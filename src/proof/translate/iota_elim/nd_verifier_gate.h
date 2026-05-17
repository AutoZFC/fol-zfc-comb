#pragma once

// NDVerifierGate — soundness net for the iota-elimination pass.
//
// Performs two independent checks on the rewritten program:
//   I-3 (iota-free): scan the program for any nd::IotaElim instruction.
//        After the rewriter runs, none should remain. The check is on
//        the program structure, not the formula terms (which the
//        downstream NDtoLKR computes lazily).
//   I-4 (ND-verifies): run the standard NDVerifier on the rewritten
//        program against the goal formula. Catches:
//          - bad scope nesting introduced by the rewrite,
//          - inadvertent semantic change from witness substitution,
//          - any other accidental damage.
//
// Either failure is a translator bug surfaced at the boundary, not a
// soundness loss in the framework.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::iota_elim {

class NDVerifierGate {
public:
    // Run both checks. Returns Ok if the program is iota-free and verifies
    // against `goal_formula` under ND.
    static util::ResultStatus verify(
        GlobalContext&            ctx,
        FormulaHandle             goal_formula,
        const Program<nd::Instr>& rewritten);
};

}  // namespace logic::proof::translate::iota_elim
