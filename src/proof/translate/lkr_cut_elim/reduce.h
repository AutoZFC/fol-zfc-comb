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
util::Result<DerivPtr> eliminate_cuts(const Deriv& root);

}  // namespace logic::proof::translate::lkr_cut_elim
