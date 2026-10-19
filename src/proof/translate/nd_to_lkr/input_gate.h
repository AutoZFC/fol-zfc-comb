#pragma once

// InputGate — preconditions for the ND→LKR translator.
//
// Per ND_TO_LKR_DESIGN.md §5, the translator accepts ND programs that:
//   I-1: contain no nd::IotaElim (Path D + EliminateIotaInProof pre-pass
//        guarantees ι-freeness; any survival is a composition error).
//   I-2: contain no nd::EqSym (the translator has no rule for it; proofs
//        derive symmetry from the eq_symmetric lemma instead).
//   I-3: ND-verify under nd::NDVerifier against the goal formula
//        (non-verifying inputs are out of scope by the soundness contract).
//
// Any failure → util::Error citing the offending instruction index.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::nd_to_lkr {

class InputGate {
public:
    // Run all three checks I-1, I-2, I-3 in order. Fails fast on the first
    // violation.
    static util::ResultStatus verify(
        GlobalContext&            ctx,
        FormulaHandle             goal_formula,
        const Program<nd::Instr>& prog);
};

}  // namespace logic::proof::translate::nd_to_lkr
