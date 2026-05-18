#pragma once

// InputGate — preconditions for the LKR→Comb translator.
//
// Per LKR_TO_COMB_DESIGN.md §5, the translator accepts LKR programs that
// LKR-verify against the goal formula. Any other defect (missing
// preconditions, ill-formed ops) is an input contract violation surfaced
// before any per-rule operation runs.
//
// Checks:
//   I-1: `LKRVerifier(ctx, goal, prog)` returns Ok.
//   I-2: No load-bearing Weakening (LKR_TO_COMB_DESIGN.md §4.4 Case B).
//        For each Weakening op, track the sequent entry it introduces;
//        reject if any later non-Weakening op references such an entry
//        by position. Scaffolding Weakening (entry never referenced) is
//        allowed and handled by the walk's no-op linear branch.
//
// I-2 piggybacks on a minimal entry-tracking pass over the instruction
// stream; no need to invoke `sequent_replay`.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_comb {

class InputGate {
public:
    // I-1 (LKR-verifies): `LKRVerifier(ctx, goal, prog)` returns Ok.
    // I-2 (no load-bearing Weakening): every Weakening's entry is never
    //     referenced by subsequent ops.
    static util::ResultStatus verify(
        GlobalContext&             ctx,
        FormulaHandle              goal_formula,
        const Program<lkr::Instr>& prog);
};

}  // namespace logic::proof::translate::lkr_to_comb
