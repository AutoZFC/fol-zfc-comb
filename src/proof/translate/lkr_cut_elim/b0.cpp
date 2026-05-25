#include "src/proof/translate/lkr_cut_elim/b0.h"

#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <type_traits>
#include <utility>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

DerivPtr wrap_with_weakenings_inner(DerivPtr base,
                                     const std::vector<FormulaHandle>& to_add) {
    // base.conclusion ends in to_add (pointwise). Build |to_add| RWeakens
    // from innermost to outermost; each strips one trailing entry going
    // outward, so the outermost wrapper's conclusion = base.conclusion
    // with all of to_add stripped.
    DerivPtr cur = std::move(base);
    for (auto it = to_add.rbegin(); it != to_add.rend(); ++it) {
        FormulaHandle added = *it;
        auto wrapper = std::make_unique<Deriv>();
        wrapper->conclusion = cur->conclusion;
        wrapper->conclusion.pop_back();
        wrapper->rule = RWeaken{added, std::move(cur)};
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
            n->rule = RWeaken{r.added, std::move(c)};
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

            // Wrap with |Γ| RWeakens. Each W adds one entry of Γ; outermost
            // W has conclusion = original Γ (matching the additive RCut's
            // node.concl), and the innermost W's child IS mult.
            std::vector<FormulaHandle> to_add(d.conclusion.begin(),
                                              d.conclusion.end());
            return util::Result<DerivPtr>(
                wrap_with_weakenings_inner(std::move(mult), to_add));
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

}  // namespace logic::proof::translate::lkr_cut_elim
