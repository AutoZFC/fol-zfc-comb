#pragma once

// LKR Weakening-elimination engine — admissibility of (W) on the
// classical sequent side, Stage 4 of the pipeline.
//
// Spec: src/proof/translate/lkr_weak_elim/WEAKENING_ELIM_DESIGN.md
//
// Operates on Deriv (the explicit sequent-carrying derivation tree
// shared with the cut-elimination pass — see
// `src/proof/translate/lkr_cut_elim/deriv.h`). Runs AFTER Stage 3
// (`eliminate_cuts`) and BEFORE `lkr_to_comb`.
//
// `eliminate_weakenings(builder, root)` returns a fresh Deriv with the
// same end-sequent but no `RWeaken` nodes in the implemented fragment.
// Out-of-fragment Weakenings (cases not yet reduced) are left in place
// — soundness is preserved (the emit-then-verify gate catches bugs);
// only completeness narrows.
//
// Phase implementation status (per WEAKENING_ELIM_DESIGN.md §9):
//   - W1 (leaf absorption: RAx non-principal, ROne, RLemma)  — pending
//   - W2 (unary permutation: ROr/RForall/RExists/RX/RC/RW)   — pending
//   - W3 (RAnd permutation)                                  — pending
//   - W4 (driver)                                            — pending
//   - W5 (wire-up into lkr_to_comb)                          — pending
//   - W6 (decompose-then-W, §4.3 — optional)                 — pending

#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_weak_elim {

using lkr_cut_elim::Deriv;
using lkr_cut_elim::DerivPtr;

// Eliminate Weakenings from the derivation. Returns a fresh Deriv with
// the same end-sequent (`root.conclusion`). Stage 4's contract:
// `result` contains no `RWeaken` nodes in the implemented fragment;
// out-of-fragment patterns are left in place (sound but incomplete).
//
// `builder` is reserved for future cases (W2.2/W3 may rectify
// eigenvars and mint new FormulaHandles).
util::Result<DerivPtr> eliminate_weakenings(
    FormulaBuilder& builder, const Deriv& root);

}  // namespace logic::proof::translate::lkr_weak_elim
