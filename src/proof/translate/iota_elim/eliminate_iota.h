#pragma once

// EliminateIotaInProof — Leisenring's constructive ε-elimination for ND
// proofs. Takes an ND program with iota_elim steps (and ι-using
// downstream ops) and produces an iota-free ND program equivalent
// modulo Leisenring's theorem.
//
// **Math**: Hilbert–Bernays 2nd ε-theorem (Leisenring variant): for
// ι-free axioms T' and ι-free goal G, T' ⊢_{with-ι} G iff T' ⊢_{without-ι} G.
// The forward construction (ProofRewriter) is the witness substitution.
//
// **Path D composition**: Path D normalises axioms at load
// (`eliminate_descriptions`) so the ι-free-axioms precondition holds
// for every input we accept. The goal is ι-free by construction
// (Path D + claim normalization). The translator is therefore in scope
// of Leisenring whenever the input proof verifies under (post-Path-D) ND.
//
// **Soundness contract**:
//   I-3: output contains no Term::description anywhere.
//   I-4: output verifies under ND against the goal.
// Enforced by NDVerifierGate.
//
// **Completeness contract**: for every input that verifies under
// (post-Path-D) ND, the rewriter produces an iota-free output that also
// verifies. Soundness gate catches any violation.
//
// **Pass composition with NDtoLKR**:
//
//     if (program contains any iota_elim) {
//         EliminateIotaInProof pass(ctx, goal);
//         program' = pass.apply(program);    // ι-free output
//         translate program' via NDtoLKR on iota-free input
//     } else {
//         translate program directly
//     }

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/pass.h"
#include "src/util/error.h"

namespace logic::proof::translate::iota_elim {

class EliminateIotaInProof : public Pass<nd::Instr, nd::Instr> {
public:
    EliminateIotaInProof(GlobalContext& ctx, FormulaHandle goal_formula)
        : ctx_(ctx), goal_(goal_formula) {}

    util::Result<Program<nd::Instr>> apply(
        const Program<nd::Instr>& in) override;

    static bool program_contains_iota(const Program<nd::Instr>& prog);

private:
    GlobalContext& ctx_;
    FormulaHandle  goal_;
};

}  // namespace logic::proof::translate::iota_elim
