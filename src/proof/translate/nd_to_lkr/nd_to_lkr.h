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
//   - I-4, checked by ProofIndex (ELIMINATION_DEMANDS_DESIGN.md §4)
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
#include "src/proof/lkr_build/compact.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/pass.h"
#include "src/util/error.h"

namespace logic::proof::translate::nd_to_lkr {

struct Options {
    // Let-bind steps referenced at least twice (§5.2).
    bool share = false;
};

class NDtoLKR : public Pass<nd::Instr, lkr::Instr> {
public:
    NDtoLKR(GlobalContext& ctx, FormulaHandle goal_formula, Options options = {})
        : ctx_(ctx), goal_(goal_formula), options_(options) {}

    util::Result<Program<lkr::Instr>> apply(
        const Program<nd::Instr>& in) override;

private:
    GlobalContext& ctx_;
    FormulaHandle  goal_;
    Options        options_;
};

// The same translation into compact LKR (lkr_build/COMPACT_LKR_DESIGN.md).
class NDtoCompactLKR : public Pass<nd::Instr, lkr_build::CompactInstr> {
public:
    NDtoCompactLKR(GlobalContext& ctx, FormulaHandle goal_formula,
                   Options options = {})
        : ctx_(ctx), goal_(goal_formula), options_(options) {}

    util::Result<Program<lkr_build::CompactInstr>> apply(
        const Program<nd::Instr>& in) override;

private:
    GlobalContext& ctx_;
    FormulaHandle  goal_;
    Options        options_;
};

}  // namespace logic::proof::translate::nd_to_lkr
