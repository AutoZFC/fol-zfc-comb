#pragma once

// NDtoLKR — translate Natural Deduction proofs to LKR (Hughes 2019 §11
// + §15 Cut + lemma-as-cut CloseByLemma).
//
// See ND_TO_LKR_DESIGN.md for the full mathematical specification. This
// header declares the Pass entry point; implementation modules under
// src/proof/translate/nd_to_lkr/ realise it.
//
// **Input contract** (enforced by InputGate):
//   - no nd::IotaElim     (run EliminateIotaInProof first if needed)
//   - no nd::EqSym         (not translated; use the eq_symmetric lemma)
//   - ND-verifies under nd::NDVerifier against the goal
//
// **Output contract** (enforced by OutputGate):
//   - Program<lkr::Instr> verifies under LKRVerifier against NNF(goal)
//
// **Composition with EliminateIotaInProof**: this Pass does NOT call
// the iota pre-pass internally. The caller composes:
//
//     auto iota_free = EliminateIotaInProof(ctx, goal).apply(in);
//     auto lkr_prog  = NDtoLKR(ctx, goal).apply(iota_free.value());
//
// matching the Pass<> discipline already established by EliminateIotaInProof.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/pass.h"
#include "src/util/error.h"

namespace logic::proof::translate::nd_to_lkr {

class NDtoLKR : public Pass<nd::Instr, lkr::Instr> {
public:
    NDtoLKR(GlobalContext& ctx, FormulaHandle goal_formula)
        : ctx_(ctx), goal_(goal_formula) {}

    util::Result<Program<lkr::Instr>> apply(
        const Program<nd::Instr>& in) override;

private:
    GlobalContext& ctx_;
    FormulaHandle  goal_;
};

}  // namespace logic::proof::translate::nd_to_lkr
