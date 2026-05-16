#pragma once

// NDtoLKR — translate Natural Deduction proofs into LKR (Hughes 2019 §11)
// extended only with Cut and CloseByLemma (the lemma-as-cut realizer).
//
// Strategy ("cut spine"):
//   * NNF the claim. Outer ∀ become LKR Forall ops; outer → become Or ops
//     that unfold the NNF disjunction ¬A_1 ∨ (¬A_2 ∨ … ∨ B).
//   * For each ND body step k deriving F_k, emit Cut(F_k_nnf). LEFT
//     subgoal proves F_k_nnf using whatever is already in the goal
//     (other ¬F_j, ¬A_i, the to-prove disjunct B, and known theorems).
//     RIGHT subgoal carries ¬F_k_nnf forward as a new "premise disjunct"
//     in the goal.
//   * Final close: structural decomposition via Hughes' ∧/∨/∀/∃ rules
//     down to atomic literals, where AxiomLit closes. The decomposition
//     macro `emit_axiom_decomp` walks both NNF-dual formulas in lockstep.
//
// Lemma-as-cut: each `nd::Use(L)` is translated into `Cut(φ_L); CloseByLemma(L)`.
// The verifier resolves L against the registry; since theorems enter the
// registry only when their proofs have been verified, this is sound.
//
// Soundness: the translator is not trusted. Its output is verified by
// LKRVerifier; a buggy emission yields a verification failure on the
// output, not a soundness loss in the framework.

#include "src/core/formula.h"
#include "src/util/error.h"
#include "src/proof/proof.h"
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
