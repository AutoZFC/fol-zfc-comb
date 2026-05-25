#include "src/proof/translate/lkr_cut_elim/reduce.h"

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

util::Result<DerivPtr> reduce(const Deriv& d);  // forward

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

// ---- reduce_cut: case analysis ---------------------------------------------
//
// `cut.left` and `cut.right` are already reduced (recurse invariant).
// Try each case in order; first match wins. If none matches, leave the cut
// in place (sound; emit will produce an LKR Cut op which the verifier
// accepts).
util::Result<DerivPtr> reduce_cut(const RCut& cut, std::vector<FormulaHandle> concl) {
    if (auto out = try_dead_cut_W(cut)) {
        // Sanity: the W dead-cut returns the W'd child, whose conclusion
        // is exactly the cut's expected output (additive: same Γ).
        return out;
    }
    if (auto out = try_axiom_cut_non_principal(cut)) {
        return out;
    }
    if (auto out = try_axiom_cut_principal(cut)) {
        return out;
    }
    // No case fired — preserve the cut.
    auto n = std::make_unique<Deriv>();
    n->conclusion = std::move(concl);
    n->rule = RCut{cut.cut_formula, clone(*cut.left), clone(*cut.right)};
    return n;
}

// ---- recursion harness -----------------------------------------------------

util::Result<DerivPtr> reduce(const Deriv& d) {
    auto out = std::make_unique<Deriv>();
    out->conclusion = d.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> || std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            out->rule = r;
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = RExchange{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = RWeaken{r.added, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = RContract{r.i, r.j, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RAnd>) {
            TRY_ASSIGN(l, reduce(*r.left));
            TRY_ASSIGN(rt, reduce(*r.right));
            out->rule = RAnd{r.principal, r.left_partition,
                             std::move(l), std::move(rt)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = ROr{r.principal, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = RForall{r.principal, r.eigen, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(c, reduce(*r.child));
            out->rule = RExists{r.principal, r.witness, std::move(c)};
            return util::Result<DerivPtr>(std::move(out));
        } else if constexpr (std::is_same_v<T, RCut>) {
            // Reduce children first, then attempt to eliminate this cut.
            TRY_ASSIGN(l, reduce(*r.left));
            TRY_ASSIGN(rt, reduce(*r.right));
            RCut reduced{r.cut_formula, std::move(l), std::move(rt)};
            return reduce_cut(reduced, d.conclusion);
        }
        return MAKE_ERROR << "reduce: unhandled rule variant";
    }, d.rule);
}

}  // namespace

util::Result<DerivPtr> eliminate_cuts(const Deriv& root) {
    return reduce(root);
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
