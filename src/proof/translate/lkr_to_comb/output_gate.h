#pragma once

// OutputGate — soundness witness for the LKR→Comb translator.
//
// Per LKR_TO_COMB_DESIGN.md §5, every CombProof produced must be
// accepted by CombVerifier against the augmented goal (= original goal
// disjuncted with each cut formula's θ ∧ ¬θ per §15). The translator
// is not trusted; this gate is the soundness witness.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_comb {

class OutputGate {
public:
    // Run CombVerifier on the produced CombProof against
    // `augmented_goal_formula` (caller computes the augmentation —
    // typically goal ∨ ⋁ (θ_i ∧ ¬θ_i) for each LKR Cut(θ_i)).
    static util::ResultStatus verify(
        GlobalContext&         ctx,
        FormulaHandle          augmented_goal_formula,
        const comb::CombProof& cp);
};

}  // namespace logic::proof::translate::lkr_to_comb
