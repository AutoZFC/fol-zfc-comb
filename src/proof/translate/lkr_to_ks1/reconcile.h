#pragma once

// ≡-reconciliation for LKR→KS1 (CUT_HANDLING_ROADMAP phase K6.1b).
//
// The LK1→KS1 translation repeatedly needs to reshape the "current formula"
// from one ∧/∨-bracketing to an ≡-equivalent one (HSW 2021 §II eq (2)): an Or
// rule appends its second disjunct to the END of the sequent, so the sequent's
// (Γ)=disjunction must be re-associated/commuted to put it in place; the And
// rule's switch sequence leaves a tail that must likewise be reconciled.
//
// `equiv_steps(fb, from, to)` returns a list of single-equation `Eqv` steps
// (CommAnd/CommOr/AssocAnd/AssocOr) that, replayed from `from`, yield exactly
// `to` — provided `from ≡ to` under the PROPOSITIONAL fragment (assoc + comm of
// ∧/∨; quantifier shifts not handled, mirroring `ks1::equiv`'s scope). It works
// by canonicalizing both to `ks1::canonicalize`'s normal form and composing the
// path to `from`'s canon with the inverse of the path to `to`'s canon. Returns
// an error if `from ≢ to` (the produced steps fail to reach `to`).

#include "src/core/formula.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_ks1 {

util::Result<std::vector<logic::proof::ks1::Step>> equiv_steps(
    FormulaBuilder& fb, FormulaHandle from, FormulaHandle to);

}  // namespace logic::proof::translate::lkr_to_ks1
