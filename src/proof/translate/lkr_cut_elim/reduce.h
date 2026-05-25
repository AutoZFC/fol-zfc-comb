#pragma once

// LKR cut-elimination engine — Gentzen Hauptsatz on the sequent side.
//
// Spec: src/proof/translate/lkr_cut_elim/CUT_ELIM_DESIGN.md
//
// Operates on Deriv (the explicit sequent-carrying derivation tree).
// `eliminate_cuts(root)` returns a fresh Deriv with the same end-sequent
// but no `RCut` nodes (and, after Stage A is wired, no `RLemma` nodes
// either). The result `emit`s to a flat LKR program that re-verifies
// under LKRVerifier (the round-trip soundness gate).
//
// Phase implementation status (per CUT_ELIM_DESIGN.md §9):
//   - B1 (axiom/atomic principal, W dead-cut)         — in progress
//   - B2 (∧/∨ principal)                              — pending
//   - B3 (∀/∃ principal + capture-avoidance)          — pending
//   - B4 (permutation)                                — pending
//   - B5 (Contraction, Exchange)                      — pending
//   - B0 (additive → multiplicative + Contraction)    — pending
//   - A  (lemma inlining)                             — pending
//   - B6 (topmost-maximal-degree worklist)            — pending
//
// Until B6 lands, the driver uses a post-order strategy: recursively
// reduce children, then attempt to reduce a Cut at the current node.
// Sound but suboptimal (may miss reductions that need permutation).

#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_cut_elim {

// Eliminate Cuts (and, once Stage A lands, CloseByLemma) from the
// derivation. Returns a fresh Deriv with the same end-sequent
// (`root->conclusion`) but with no `RCut` (resp. `RLemma`) nodes in
// the implemented fragment. Out-of-fragment cuts (cases not yet
// handled) are left in place — soundness is preserved (the emit-then-
// verify gate catches bugs); only completeness narrows.
//
// `builder` must be the same FormulaBuilder used to construct `root`'s
// FormulaHandles. The B3 (∀/∃) reduction substitutes terms into
// formulas, which mints new FormulaHandles in the builder.
util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root);

// =========================================================================
// B0 helper: mcut (multiplicative cut).
//
// Performs a multiplicative cut on cut-free derivations `dl` and `dr`
// at positions `pl` (in dl.conclusion) and `pr` (in dr.conclusion).
// The cut formula at dl.conclusion[pl] must be the NNF dual of
// dr.conclusion[pr]. Returns a cut-free derivation whose conclusion =
// `remove(dl.conclusion, pl) ++ remove(dr.conclusion, pr)` in
// canonical order, or nullptr if no case is currently implemented.
//
// Implemented cases:
//   - dl.rule = RAx with pl NOT in {ax.a, ax.b} (non-principal axiom
//     on the left). The Ax closes within dl's Γ_L, ignoring the cut
//     formula at pl. Result = RAx with positions adjusted for pl's
//     removal, on the wider mcut conclusion.
//   - Symmetric: dr.rule = RAx with pr non-principal.
//
// Future cases: axiom principal (Cut against Ax pair), W dead-cut,
// permutation, ∧/∨ principal, ∀/∃ principal. Most require either
// constructing extended derivations with shifted positions or the
// Weakening bridge for additive-cut integration.
DerivPtr mcut(FormulaBuilder& builder,
              const Deriv& dl, std::size_t pl,
              const Deriv& dr, std::size_t pr);

// =========================================================================
// B0 helper: Weakening bridge.
//
// Wraps `base` with |to_add| RWeaken layers. Result's outermost node has
// `conclusion = base.conclusion` with the trailing `to_add` entries
// stripped; the verifier's W's then grow the goal from there back up to
// base.conclusion before base's ops fire.
//
// Precondition: base.conclusion ends in to_add (in the given order):
//   base.conclusion.size() >= to_add.size()
//   for i in 0..to_add.size():
//     base.conclusion[base.conclusion.size()-to_add.size()+i] == to_add[i]
//
// Used by the principal compound-cut reductions (B2 ∧/∨, B3 ∀/∃) to
// bridge from the additive cut's conclusion Γ down to the multiplicative
// intermediate Γ ++ Γ. Exposed in the header so tests can exercise it.
// =========================================================================
DerivPtr wrap_with_weakenings(
    DerivPtr base,
    const std::vector<FormulaHandle>& to_add);

}  // namespace logic::proof::translate::lkr_cut_elim
