#include "src/proof/translate/lkr_cut_elim/b0.h"

#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <type_traits>
#include <utility>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

DerivPtr wrap_with_duplicates(DerivPtr mult, std::size_t n) {
    // mult.conclusion = Γ ++ Γ (size 2n). The additive→multiplicative bridge
    // is the doubled context read goal-directed: the node conclusion Γ grows
    // into Γ,Γ by DUPLICATING each γ_k (CUT_ELIM_DESIGN §4 calls this the
    // |Γ| contractions; in the goal-directed IR it is RDuplicate). Build n
    // RDuplicate wrappers from innermost (src=n-1, child=mult) to outermost
    // (src=0, conclusion=Γ). Each wrapper's conclusion = child minus its
    // trailing copy of γ_src.
    DerivPtr cur = std::move(mult);
    for (std::size_t k = n; k-- > 0; ) {
        auto wrapper = std::make_unique<Deriv>();
        wrapper->conclusion = cur->conclusion;
        wrapper->conclusion.pop_back();
        wrapper->rule = RDuplicate{k, std::move(cur)};
        cur = std::move(wrapper);
    }
    return cur;
}

util::Result<DerivPtr> b0_walk(const Deriv& d) {
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;

        if constexpr (std::is_same_v<T, RAx> ||
                      std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            n->rule = r;
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RExchange{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RWeaken{r.idx, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RDuplicate>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RDuplicate{r.src, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RContract{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RAnd>) {
            TRY_ASSIGN(l, b0_walk(*r.left));
            TRY_ASSIGN(rr, b0_walk(*r.right));
            n->rule = RAnd{r.principal, r.left_partition,
                           std::move(l), std::move(rr)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = ROr{r.principal, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RForall{r.principal, r.eigen, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(c, b0_walk(*r.child));
            n->rule = RExists{r.principal, r.witness, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RCut>) {
            TRY_ASSIGN(l,  b0_walk(*r.left));
            TRY_ASSIGN(rr, b0_walk(*r.right));

            if (l->conclusion.empty() || rr->conclusion.empty())
                return MAKE_ERROR << "b0: RCut child has empty conclusion";

            const size_t gl = l->conclusion.size() - 1;
            const size_t gr = rr->conclusion.size() - 1;

            // Already multiplicative: pass through.
            if (d.conclusion.size() == gl + gr &&
                !(d.conclusion.size() == gl && gl == gr)) {
                n->rule = RCut{r.cut_formula, std::move(l), std::move(rr)};
                return util::Result<DerivPtr>(std::move(n));
            }

            // Additive: |node| = gl = gr; require Γ_L = Γ_R = node.concl.
            if (gl != gr || d.conclusion.size() != gl) {
                return MAKE_ERROR
                    << "b0: RCut shape neither additive nor multiplicative ("
                    << "node=" << d.conclusion.size() << ", |Γ_L|=" << gl
                    << ", |Γ_R|=" << gr << ")";
            }

            // Build the mult-Cut: same children, node.concl = Γ ++ Γ.
            std::vector<FormulaHandle> mult_concl;
            mult_concl.reserve(2 * d.conclusion.size());
            for (auto h : d.conclusion) mult_concl.push_back(h);
            for (auto h : d.conclusion) mult_concl.push_back(h);

            auto mult = std::make_unique<Deriv>();
            mult->conclusion = std::move(mult_concl);
            mult->rule = RCut{r.cut_formula, std::move(l), std::move(rr)};

            // Bridge the doubled context Γ,Γ back down to the additive
            // RCut's node.concl = Γ with |Γ| RDuplicate wrappers.
            return util::Result<DerivPtr>(
                wrap_with_duplicates(std::move(mult), d.conclusion.size()));
        }
        else {
            return MAKE_ERROR << "b0: unhandled rule variant";
        }
    }, d.rule);
}

}  // namespace

util::Result<DerivPtr> additive_to_multiplicative(const Deriv& root) {
    TRY_ASSIGN(out, b0_walk(root));
    TRY(validate(*out));
    return util::Result<DerivPtr>(std::move(out));
}

namespace {

// Wrap `orig` (conclusion D) with RWeaken nodes dropping the positions
// [drop_lo, drop_hi) of `target`, so the outermost node concludes `target` and
// the innermost child is `orig`. `target` must be `orig`'s conclusion with the
// [drop_lo, drop_hi) block inserted at that position.
DerivPtr weaken_up_to(DerivPtr orig, const std::vector<FormulaHandle>& target,
                      std::size_t drop_lo, std::size_t drop_hi) {
    std::vector<std::size_t> drop;                       // descending
    for (std::size_t i = drop_hi; i-- > drop_lo; ) drop.push_back(i);
    std::vector<std::vector<FormulaHandle>> concls;
    concls.push_back(target);
    for (std::size_t d : drop) {
        std::vector<FormulaHandle> next = concls.back();
        next.erase(next.begin() + d);
        concls.push_back(std::move(next));
    }
    // concls.back() == orig->conclusion.
    DerivPtr cur = std::move(orig);
    for (std::size_t k = drop.size(); k-- > 0; ) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = concls[k];
        node->rule = RWeaken{drop[k], std::move(cur)};
        cur = std::move(node);
    }
    return cur;   // conclusion == target
}

util::Result<DerivPtr> m2a_walk(const Deriv& d) {
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> || std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            n->rule = r;
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RExchange{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RWeaken{r.idx, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RDuplicate>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RDuplicate{r.src, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RContract{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = ROr{r.principal, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RForall{r.principal, r.eigen, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(c, m2a_walk(*r.child));
            n->rule = RExists{r.principal, r.witness, std::move(c)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RAnd>) {
            TRY_ASSIGN(l, m2a_walk(*r.left));
            TRY_ASSIGN(rr, m2a_walk(*r.right));
            n->rule = RAnd{r.principal, r.left_partition, std::move(l), std::move(rr)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RCut>) {
            TRY_ASSIGN(l,  m2a_walk(*r.left));
            TRY_ASSIGN(rr, m2a_walk(*r.right));
            const std::size_t gl = l->conclusion.size() - 1;
            const std::size_t gr = rr->conclusion.size() - 1;

            const bool is_mult = d.conclusion.size() == gl + gr &&
                                 !(d.conclusion.size() == gl && gl == gr);
            if (!is_mult) {
                // Already additive (or the degenerate empty-Γ coincidence).
                n->rule = RCut{r.cut_formula, std::move(l), std::move(rr)};
                return util::Result<DerivPtr>(std::move(n));
            }

            // Mult → additive on C = Γ_L ++ Γ_R = node.concl. Weaken the left
            // premise up to C ++ {φ} (insert Γ_R block at [gl, gl+gr)); the
            // right up to C ++ {dual} (insert Γ_L block at [0, gl)).
            const std::vector<FormulaHandle>& C = d.conclusion;
            const FormulaHandle phi  = l->conclusion.back();
            const FormulaHandle dual = rr->conclusion.back();

            std::vector<FormulaHandle> tgtL = C; tgtL.push_back(phi);
            DerivPtr addL = weaken_up_to(std::move(l), tgtL, gl, gl + gr);

            std::vector<FormulaHandle> tgtR = C; tgtR.push_back(dual);
            DerivPtr addR = weaken_up_to(std::move(rr), tgtR, 0, gl);

            n->rule = RCut{r.cut_formula, std::move(addL), std::move(addR)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else {
            return MAKE_ERROR << "m2a: unhandled rule variant";
        }
    }, d.rule);
}

}  // namespace

util::Result<DerivPtr> multiplicative_to_additive(const Deriv& root) {
    TRY_ASSIGN(out, m2a_walk(root));
    TRY(validate(*out));
    return util::Result<DerivPtr>(std::move(out));
}

}  // namespace logic::proof::translate::lkr_cut_elim
