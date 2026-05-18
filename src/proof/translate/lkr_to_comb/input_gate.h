#pragma once

// InputGate — preconditions for the LKR→Comb translator.
//
// Per LKR_TO_COMB_DESIGN.md §5, the translator accepts LKR programs that
// LKR-verify against the goal formula. Any other defect (missing
// preconditions, ill-formed ops) is an input contract violation surfaced
// before any per-rule operation runs.
//
// Additional check (per design §8 open question, chosen "yes"):
//   I-2: every CloseByLemma(L) is preceded by Cut(φ_L) such that LEFT
//        closes via CloseByLemma. This enforces Strategy B preconditions
//        structurally so the translator can rely on them.
//
// I-2 is a cheap linear scan of the instruction stream maintaining a
// goal-stack mirror sufficient to detect the pairing.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_comb {

class InputGate {
public:
    // I-1 (LKR-verifies): `LKRVerifier(ctx, goal, prog)` returns Ok.
    // I-2 (CloseByLemma pairing): not yet enforced; will be added when
    //     CloseByLemma support lands.
    static util::ResultStatus verify(
        GlobalContext&             ctx,
        FormulaHandle              goal_formula,
        const Program<lkr::Instr>& prog);
};

}  // namespace logic::proof::translate::lkr_to_comb
