#pragma once

// CutAugmentation — per §15, the augmented goal is
// `goal ∨ (θ_1 ∧ ¬θ_1) ∨ ... ∨ (θ_n ∧ ¬θ_n)` where θ_i are the program's
// cut formulas in op order. The canonical target is built from this
// augmented goal so that Cut-introduced sequent entries have stable
// canonical positions in the augmented fograph.
//
// This module:
//   1. scans the program for Cut ops (extracting cut formulas);
//   2. builds the augmented-goal formula;
//   3. computes per-cut start positions in the augmented Fograph.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

struct CutAugmentation {
    // augmented_goal = goal ∨ (θ_1 ∧ ¬θ_1) ∨ … ∨ (θ_n ∧ ¬θ_n)
    FormulaHandle augmented_goal{};

    // For each cut k in program order:
    //   - theta_start[k]: canonical position where θ_k's vertices begin
    //   - theta_count[k]: number of vertices for θ_k
    //   - neg_theta_count[k]: number for ¬θ_k_nnf (= start_k + theta_count[k] is its start)
    // So θ_k positions = [theta_start[k], theta_start[k]+theta_count[k]);
    // ¬θ_k positions = [theta_start[k]+theta_count[k], theta_start[k]+theta_count[k]+neg_theta_count[k]).
    std::vector<size_t>        theta_start;
    std::vector<size_t>        theta_count;
    std::vector<size_t>        neg_theta_count;
    std::vector<FormulaHandle> theta;      // raw θ_k handles (for tests/diag)
    std::vector<FormulaHandle> neg_theta;  // NNF(¬θ_k)
};

// Build the augmentation. `goal_nnf` is the post-NNF original goal.
util::Result<CutAugmentation> build_cut_augmentation(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog);

}  // namespace logic::proof::translate::lkr_to_comb
