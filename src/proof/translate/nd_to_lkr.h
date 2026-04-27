#pragma once

// NDtoLKR — translate Natural Deduction proofs into Extended LKR (Hughes
// 2019 §11 core + admissible extensions Cut, AxiomGen, UseTheorem,
// SchemaInst — see src/proof/lkr/ops.h for the layering and elimination
// theorems).
//
// Strategy ("cut spine"):
//   * NNF the claim. Outer ∀ become LKR Forall ops; outer → become Or ops
//     that unfold the NNF disjunction ¬A_1 ∨ (¬A_2 ∨ … ∨ B).
//   * For each ND body step k deriving F_k, emit Cut(F_k_nnf). LEFT
//     subgoal proves F_k_nnf using whatever is already in the goal
//     (other ¬F_j, ¬A_i, the to-prove disjunct B, and known theorems).
//     RIGHT subgoal carries ¬F_k_nnf forward as a new "premise disjunct"
//     in the goal.
//   * Final close: AxiomGen between the qed-target body step's positive
//     F_target_nnf (carried in via cut) and the original goal-disjunct
//     B in the bottom-most RIGHT subgoal.
//
// Hughes-core reduction (future work): translator output is in Extended
// LKR. To produce a pure-Hughes-core proof (required for combinatorial
// proofs per Hughes §11.1), apply the elimination passes documented in
// lkr/ops.h: cut-elimination (Hauptsatz), AxiomGen → AxiomLit structural
// reduction, UseTheorem/SchemaInst proof-inlining.
//
// Soundness: the translator is not trusted. Its output is verified by
// LKRVerifier; a buggy emission yields a verification failure on the
// output, not a soundness loss in the framework.

#include "../../core/formula.h"
#include "../../util/error.h"
#include "../proof.h"
#include "pass.h"

namespace logic::proof::translate {

class NDtoLKR final : public Pass<nd::Instr, lkr::Instr> {
public:
    NDtoLKR() : ctx_(nullptr) {}
    explicit NDtoLKR(GlobalContext& ctx) : ctx_(&ctx) {}

    util::Result<Program<lkr::Instr>> apply(const Program<nd::Instr>& in) override;

private:
    GlobalContext* ctx_;
};

// Verify-roundtrip harness: translate then verify under LKR.
util::ResultStatus translate_and_verify(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const Program<nd::Instr>& nd_prog);

}  // namespace logic::proof::translate
