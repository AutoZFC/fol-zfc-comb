#include "src/proof/translate/lkr_cut_elim/reduce.h"

#include "src/core/formula.h"
#include "src/proof/lkr/literal.h"

#include <algorithm>
#include <variant>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

// ---- helpers ---------------------------------------------------------------

// Deep-clone a Deriv subtree. Required for §5.5 Contraction (duplicate the
// other premise) and for safe rewrites that need to preserve the original
// node. Used everywhere `reduce` needs to RETURN a new Deriv distinct from
// its input.
DerivPtr clone(const Deriv& d) {
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx>)        n->rule = r;
        else if constexpr (std::is_same_v<T, ROne>)  n->rule = r;
        else if constexpr (std::is_same_v<T, RLemma>) n->rule = r;
        else if constexpr (std::is_same_v<T, RExchange>) {
            n->rule = RExchange{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            n->rule = RWeaken{r.added, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            n->rule = RContract{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n->rule = RAnd{r.principal, r.left_partition,
                           clone(*r.left), clone(*r.right)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            n->rule = ROr{r.principal, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            n->rule = RForall{r.principal, r.eigen, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            n->rule = RExists{r.principal, r.witness, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            n->rule = RCut{r.cut_formula, clone(*r.left), clone(*r.right)};
        }
    }, d.rule);
    return n;
}

struct ReduceCtx {
    FormulaBuilder& builder;
};

util::Result<DerivPtr> reduce(ReduceCtx& cc, const Deriv& d);  // forward

// Substitute `old_t` with `new_t` in every formula and term within a
// Deriv subtree. Returns a fresh Deriv with updated formulas.
//
// Capture-avoidance (§6 of CUT_ELIM_DESIGN.md): the substitution is
// applied via FormulaBuilder::translate_term which performs literal
// term replacement without Gen interaction. Eigenvars are fixed
// variables; if `old_t` = Term::fixed(a) where `a` is the eigen of an
// OUTER Forall, no INNER quantifier should re-introduce `a` (by
// eigenvar freshness). Inner RForall.eigen values are kept as-is;
// inner RExists.witness terms get translated. A future rectification
// pass would harden this against pathological reuse.
DerivPtr substitute_in_deriv(ReduceCtx& cc, const Deriv& d,
                              const Term& old_t, const Term& new_t) {
    auto out = std::make_unique<Deriv>();
    out->conclusion.reserve(d.conclusion.size());
    for (auto h : d.conclusion) {
        out->conclusion.push_back(cc.builder.translate_term(h, old_t, new_t));
    }
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx>) {
            out->rule = r;
        } else if constexpr (std::is_same_v<T, ROne>) {
            out->rule = r;
        } else if constexpr (std::is_same_v<T, RLemma>) {
            out->rule = r;
        } else if constexpr (std::is_same_v<T, RExchange>) {
            out->rule = RExchange{r.i, r.j,
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            out->rule = RWeaken{
                cc.builder.translate_term(r.added, old_t, new_t),
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            out->rule = RContract{r.i, r.j,
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            out->rule = RAnd{r.principal, r.left_partition,
                substitute_in_deriv(cc, *r.left,  old_t, new_t),
                substitute_in_deriv(cc, *r.right, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            out->rule = ROr{r.principal,
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            // Inner Forall's eigen kept as-is (assumed fresh).
            out->rule = RForall{r.principal, r.eigen,
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            Term new_witness = cc.builder.translate_in_term(r.witness, old_t, new_t);
            out->rule = RExists{r.principal, new_witness,
                substitute_in_deriv(cc, *r.child, old_t, new_t)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            out->rule = RCut{
                cc.builder.translate_term(r.cut_formula, old_t, new_t),
                substitute_in_deriv(cc, *r.left,  old_t, new_t),
                substitute_in_deriv(cc, *r.right, old_t, new_t)};
        }
    }, d.rule);
    return out;
}

// ---- §4 (B0) helpers: multiplicative cut + Weakening bridge ----------------
//
// LKR's Cut is additive (shared Γ), but Gentzen's case-analysis reductions
// are naturally multiplicative — each principal case produces sub-cuts on
// SUB-FORMULAS that operate over POSSIBLY DIFFERENT contexts.
//
// We bridge between the two forms via the verifier's Weakening direction
// (W goes from smaller goal to bigger). Specifically:
//
//   1. `mcut(Dl, pl, Dr, pr)` performs a multiplicative cut on cut-free
//      sub-derivations, returning a cut-free derivation of
//      `remove(Dl.concl, pl) ++ remove(Dr.concl, pr)` (canonical order).
//
//   2. For an additive RCut at node N (conclusion Γ, left proves Γ+φ at
//      position last_L, right proves Γ+¬φ at last_R):
//      - Reduce N.left and N.right recursively (so they're cut-free).
//      - Call mcut → D_mid with conclusion Γ ++ Γ.
//      - Wrap D_mid with |Γ| RWeaken's so the outermost conclusion = Γ
//        (the cut's expected conclusion). The verifier sees the W chain
//        grow Γ → Γ ++ Γ before D_mid's ops close it.
//
// This Phase B0 commit introduces `wrap_with_weakenings` and `mcut`'s
// skeleton + the simplest case (W dead-cut) under the new framework.
// Existing B1 reductions (W dead-cut, axiom non/principal) keep their
// direct-additive form for now — they will be folded into mcut when the
// principal compound cases (B2, B3) land and need the unified path.
//
// Postcondition of `mcut`:
//   result.conclusion == remove(dl.conclusion, pl) ++ remove(dr.conclusion, pr)
// Returns nullptr (unrecognized) if no case fires — caller leaves the
// surrounding cut in place (sound: emit still produces a verifying
// program, just with a residual cut).

// Wrap `base` with `|to_add|` RWeaken layers so the resulting Deriv's
// conclusion equals `base.conclusion` with the trailing `to_add` entries
// removed. Reads `to_add` left-to-right as the order the verifier sees
// the Weakening ops (outermost RWeaken adds to_add[0], innermost adds
// to_add.back()).
//
// Precondition: base.conclusion ends in to_add (in order), i.e.,
//   base.conclusion.size() >= to_add.size()
//   for i in 0..to_add.size():
//     base.conclusion[base.conclusion.size()-to_add.size()+i] == to_add[i]
// mcut: multiplicative cut on cut-free dl (at position pl) and dr (at
// position pr). The cut formula at dl.conclusion[pl] must be the NNF
// dual of dr.conclusion[pr]. Returns a cut-free derivation whose
// conclusion equals `remove(dl.conclusion, pl) ++ remove(dr.conclusion, pr)`
// in canonical order, or nullptr if no case is implemented (caller
// preserves the surrounding cut).
//
// Subtlety: building a derivation whose conclusion is BIGGER than its
// children's via Weakening requires the verifier's W direction (parent
// smaller, child bigger). The simpler additive form (try_dead_cut_W
// in B1) sidesteps this by reusing the W's underlying child directly —
// additive cut's conclusion IS Γ_L. That's kept and still wins in
// reduce_cut.
//
// mcut is the future home of B2 (∧/∨) and B3 (∀/∃) principal cases,
// which genuinely need the multiplicative form to express sub-cuts
// over disjoint contexts. For now: skeleton + a TODO marker.
[[maybe_unused]] DerivPtr mcut(const Deriv& /*dl*/, size_t /*pl*/,
                                const Deriv& /*dr*/, size_t /*pr*/) {
    return nullptr;  // no case implemented yet — caller falls through.
}

// ---- §5.5 W (dead-cut) -----------------------------------------------------
//
// Cut(φ) where one premise's last rule is RWeaken adding the cut formula φ
// at the end of its conclusion. The Weakening contributed φ without proving
// it; the Cut is "dead". The conclusion of the cut (after dropping φ from
// the W'd premise) was already available — just weaken in the OTHER
// premise's extra formulas to reach the Cut's conclusion.
//
// Concretely (LEFT dead-cut variant):
//   Cut(φ): LEFT = ⊢ Γ, φ from RWeaken(φ) on child ⊢ Γ.
//           RIGHT = ⊢ Γ, φ̄ (additive, so same Γ).
//   Replace with: LEFT's child ⊢ Γ. (Additive cut's conclusion = Γ.)
//
// (Symmetric for RIGHT dead-cut.)
//
// Returns nullopt if the cut isn't a dead-cut shape; otherwise returns
// the replacement subtree (already reduced, since the surviving child
// was itself produced by `reduce`).
DerivPtr try_dead_cut_W(const RCut& cut) {
    // Cut(φ) semantics: cut.left ends in φ at its last position, cut.right
    // ends in NNF(¬φ). For Weakening (which appends to its conclusion),
    // an RWeaken at cut.{left,right}'s top implies the appended formula
    // IS that last entry — which IS the cut formula (or its dual). So
    // an RWeaken at either premise is automatically a dead cut.
    if (auto* wl = std::get_if<RWeaken>(&cut.left->rule)) {
        // LEFT was W(φ); discard RIGHT entirely. Return LEFT's child,
        // whose conclusion is exactly Γ (the additive cut's conclusion).
        return clone(*wl->child);
    }
    if (auto* wr = std::get_if<RWeaken>(&cut.right->rule)) {
        // RIGHT was W(φ̄); discard LEFT entirely. Return RIGHT's child.
        return clone(*wr->child);
    }
    return nullptr;
}

// ---- §5.2 axiom cases ------------------------------------------------------
//
// Cut(φ) where one premise's last rule is RAx. Two sub-cases:
//
// (a) Non-principal axiom. The Ax's two dual positions are both in Γ
//     (neither is the cut formula slot at LEFT.conclusion.size()-1).
//     The cut formula was just "weakened in" by Ax+W convention. The
//     same Ax closes Γ alone — replace Cut with Ax over Γ.
//
// (b) Principal axiom (additive form). The cut formula sits at position
//     `last`, paired with its NNF dual at some position k < last in Γ.
//     The cut's conclusion ⊢ Γ has the dual already at position k. The
//     OTHER premise proves ⊢ Γ, dual — Contract on (k, last_other) to
//     merge the duplicate. Result: ⊢ Γ.
DerivPtr try_axiom_cut_non_principal(const RCut& cut) {
    auto rewrite = [](const Deriv& d) -> DerivPtr {
        const RAx* ax = std::get_if<RAx>(&d.rule);
        if (!ax) return nullptr;
        size_t last = d.conclusion.size() - 1;
        if (ax->a == last || ax->b == last) return nullptr;
        // Ax closes within Γ. Drop the cut-formula entry.
        auto leaf = std::make_unique<Deriv>();
        leaf->conclusion = d.conclusion;
        leaf->conclusion.pop_back();
        leaf->rule = RAx{ax->a, ax->b};  // positions unchanged (both < last)
        return leaf;
    };
    if (auto out = rewrite(*cut.left))  return out;
    if (auto out = rewrite(*cut.right)) return out;
    return nullptr;
}

DerivPtr try_axiom_cut_principal(const RCut& cut) {
    // The axiom's cut formula is principal (one of its two literal
    // positions equals `last`). The standard reduction: discard the
    // axiom premise (which contributed only context), keep the OTHER
    // premise, and Weaken in any extra context to reach the cut's
    // conclusion.
    //
    // In additive form: cut.conclusion = Γ. The other premise proves
    // ⊢ Γ, NNF(¬φ). The cut's conclusion drops NNF(¬φ) — but in the
    // verifier model, Weakening grows the goal: at Γ, W(NNF(¬φ))
    // produces Γ, NNF(¬φ), and the OTHER premise's ops then close it.
    //
    // IR-side: build a RWeaken node whose conclusion = Γ (= cut's
    // conclusion) and whose child = the OTHER premise (which proves
    // Γ, NNF(¬φ)).
    auto rewrite_other = [](const Deriv& ax_side, const Deriv& other_side)
        -> DerivPtr {
        const RAx* ax = std::get_if<RAx>(&ax_side.rule);
        if (!ax) return nullptr;
        size_t last = ax_side.conclusion.size() - 1;
        if (ax->a != last && ax->b != last) return nullptr;
        // Cut formula principal in the Ax. Build Weakening over other_side.
        FormulaHandle added = other_side.conclusion.back();
        auto out = std::make_unique<Deriv>();
        out->conclusion = other_side.conclusion;
        out->conclusion.pop_back();
        out->rule = RWeaken{added, clone(other_side)};
        return out;
    };
    if (auto out = rewrite_other(*cut.left,  *cut.right)) return out;
    if (auto out = rewrite_other(*cut.right, *cut.left))  return out;
    return nullptr;
}

// ---- §5.4 permutation (cut not principal in R) -----------------------------
//
// When dl's top rule R does not act on the cut formula's position, we
// can permute the Cut above R. Most rules (Or, W, C, Forall on a non-
// last principal, …) shift Γ's contents in ways that turn the
// additive cut into a multiplicative one — those cases need `mcut` to
// handle disjoint contexts, deferred to a phase that ships mcut.
//
// The ONE clean additive case: RExchange where the swap doesn't touch
// the cut formula's slot. Permute by mirroring the swap on dr (an
// added Exchange op above dr is cheap) and wrap with the original
// Exchange.
DerivPtr try_permute_exchange(const RCut& cut) {
    auto try_side = [&](const Deriv& side_with_exchange,
                        const Deriv& other_side,
                        bool side_is_left) -> DerivPtr {
        const RExchange* ex = std::get_if<RExchange>(&side_with_exchange.rule);
        if (!ex) return nullptr;
        size_t last = side_with_exchange.conclusion.size() - 1;
        if (ex->i == last || ex->j == last) {
            // The Exchange touches the cut formula's slot — would need
            // re-indexing of the inner cut's pl. Defer.
            return nullptr;
        }
        if (ex->i >= side_with_exchange.conclusion.size() ||
            ex->j >= side_with_exchange.conclusion.size()) {
            return nullptr;
        }

        // Build dr_swapped: a Deriv whose conclusion = other_side.conclusion
        // with (ex->i, ex->j) swapped, achieved by wrapping other_side in
        // an RExchange. Per IR convention, RExchange's node.conclusion =
        // pre-Exchange (= our target swapped state); child = post-Exchange
        // (= original other_side.conclusion).
        std::vector<FormulaHandle> other_swapped = other_side.conclusion;
        std::swap(other_swapped[ex->i], other_swapped[ex->j]);
        auto other_wrapped = std::make_unique<Deriv>();
        other_wrapped->conclusion = other_swapped;
        other_wrapped->rule = RExchange{ex->i, ex->j, clone(other_side)};

        // Build the inner Cut: shared Γ_swapped at both premises.
        auto inner_cut = std::make_unique<Deriv>();
        inner_cut->conclusion.assign(
            other_swapped.begin(),
            other_swapped.end() - 1);
        DerivPtr L_inner = clone(*ex->child);
        DerivPtr R_inner = std::move(other_wrapped);
        if (side_is_left) {
            inner_cut->rule = RCut{
                cut.cut_formula, std::move(L_inner), std::move(R_inner)};
        } else {
            inner_cut->rule = RCut{
                cut.cut_formula, std::move(R_inner), std::move(L_inner)};
        }

        // Wrap with the outer Exchange to recover the original Γ.
        auto outer = std::make_unique<Deriv>();
        outer->conclusion.assign(
            side_with_exchange.conclusion.begin(),
            side_with_exchange.conclusion.end() - 1);
        outer->rule = RExchange{ex->i, ex->j, std::move(inner_cut)};
        return outer;
    };

    if (auto out = try_side(*cut.left,  *cut.right, /*side_is_left=*/true))
        return out;
    if (auto out = try_side(*cut.right, *cut.left,  /*side_is_left=*/false))
        return out;
    return nullptr;
}

// ---- §5.3 ∀/∃ principal cut ------------------------------------------------
//
// Cut(∀x.β) where LEFT ends in Forall(eigen=a) and RIGHT ends in
// Exists(witness=t), both principal on their last position. Reduce by
// substituting a:=t throughout LEFT's child subderivation, then cut on
// β[x:=t] at strictly smaller degree.
//
// Also handles the symmetric case (Cut(∃x.β) with LEFT=Exists, RIGHT=
// Forall) via the same helper with swapped sides.
//
// Returns nullptr if shape doesn't match; otherwise a NEW Cut node
// whose cut formula has strictly smaller degree. Caller (reduce_cut)
// recursively reduces the result so the new smaller cut is eliminated
// in turn — terminates by degree induction.
DerivPtr try_forall_exists_principal(ReduceCtx& cc, const RCut& cut) {
    auto try_pair = [&](const Deriv& forall_side, const Deriv& exists_side)
        -> DerivPtr {
        const RForall* fr = std::get_if<RForall>(&forall_side.rule);
        const RExists* er = std::get_if<RExists>(&exists_side.rule);
        if (!fr || !er) return nullptr;
        size_t last_F = forall_side.conclusion.size() - 1;
        size_t last_E = exists_side.conclusion.size() - 1;
        if (fr->principal != last_F || er->principal != last_E) {
            return nullptr;
        }
        Term a_term = Term::fixed(fr->eigen);
        Term t_term = er->witness;
        auto subbed = substitute_in_deriv(cc, *fr->child, a_term, t_term);
        auto new_cut_node = std::make_unique<Deriv>();
        new_cut_node->conclusion.assign(
            forall_side.conclusion.begin(),
            forall_side.conclusion.end() - 1);
        FormulaHandle new_cut_formula = subbed->conclusion.back();
        // Convention: LEFT side of an RCut ends in the cut formula
        // (positive), RIGHT ends in its NNF dual. `subbed` (from the
        // Forall side) ends in β[x:=t]; `exists_side.child` ends in
        // β̄[x:=t]. So LEFT=subbed, RIGHT=clone(exists_side.child).
        new_cut_node->rule = RCut{
            new_cut_formula,
            std::move(subbed),
            clone(*er->child)};
        return new_cut_node;
    };
    if (auto out = try_pair(*cut.left,  *cut.right)) return out;
    if (auto out = try_pair(*cut.right, *cut.left))  return out;
    return nullptr;
}

// ---- reduce_cut: case analysis ---------------------------------------------
//
// `cut.left` and `cut.right` are already reduced (recurse invariant).
// Try each case in order; first match wins. If none matches, leave the cut
// in place (sound; emit will produce an LKR Cut op which the verifier
// accepts).
util::Result<DerivPtr> reduce_cut(ReduceCtx& cc, const RCut& cut,
                                   std::vector<FormulaHandle> concl) {
    if (auto out = try_dead_cut_W(cut)) {
        return out;
    }
    if (auto out = try_axiom_cut_non_principal(cut)) {
        return out;
    }
    if (auto out = try_axiom_cut_principal(cut)) {
        return out;
    }
    if (auto out = try_forall_exists_principal(cc, cut)) {
        // The reduction produced a NEW (smaller) cut. Recursively
        // reduce it so the new cut gets eliminated too (by degree
        // induction).
        return reduce(cc, *out);
    }
    if (auto out = try_permute_exchange(cut)) {
        // Permutation moved the cut deeper; recursively reduce so
        // the new cut (possibly with a now-principal shape) lands
        // in another case.
        return reduce(cc, *out);
    }
    // No case fired — preserve the cut.
    auto n = std::make_unique<Deriv>();
    n->conclusion = std::move(concl);
    n->rule = RCut{cut.cut_formula, clone(*cut.left), clone(*cut.right)};
    return util::Result<DerivPtr>(std::move(n));
}

// ---- recursion harness -----------------------------------------------------

util::Result<DerivPtr> reduce(ReduceCtx& cc, const Deriv& d) {
    auto out = std::make_unique<Deriv>();
    out->conclusion = d.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> || std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            out->rule = r;
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = RExchange{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = RWeaken{r.added, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = RContract{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RAnd>) {
            TRY_ASSIGN(l, reduce(cc, *r.left));
            TRY_ASSIGN(rt, reduce(cc, *r.right));
            out->rule = RAnd{r.principal, r.left_partition,
                             std::move(l), std::move(rt)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = ROr{r.principal, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = RForall{r.principal, r.eigen, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(c, reduce(cc, *r.child));
            out->rule = RExists{r.principal, r.witness, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RCut>) {
            // Reduce children first, then attempt to eliminate this cut.
            TRY_ASSIGN(l, reduce(cc, *r.left));
            TRY_ASSIGN(rt, reduce(cc, *r.right));
            RCut reduced{r.cut_formula, std::move(l), std::move(rt)};
            return reduce_cut(cc, reduced, d.conclusion);
        }
        return MAKE_ERROR << "reduce: unhandled rule variant";
    }, d.rule);
}

}  // namespace

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root) {
    ReduceCtx cc{builder};
    return reduce(cc, root);
}

DerivPtr wrap_with_weakenings(
    DerivPtr base,
    const std::vector<FormulaHandle>& to_add)
{
    DerivPtr cur = std::move(base);
    // Build from innermost (closest to base) to outermost. Each wrap
    // strips one trailing entry from the conclusion.
    for (auto it = to_add.rbegin(); it != to_add.rend(); ++it) {
        FormulaHandle added = *it;
        auto wrapper = std::make_unique<Deriv>();
        wrapper->conclusion = cur->conclusion;
        wrapper->conclusion.pop_back();  // remove the entry this W added
        wrapper->rule = RWeaken{added, std::move(cur)};
        cur = std::move(wrapper);
    }
    return cur;
}

}  // namespace logic::proof::translate::lkr_cut_elim
