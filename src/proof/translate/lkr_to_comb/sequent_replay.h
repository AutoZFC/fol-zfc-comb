#pragma once

// SequentReplay — non-checking replay of an LKR program's open-goals
// stack mutations.
//
// Per LKR_TO_COMB_DESIGN.md, the §11.1 walk needs to know each op's
// *conclusion sequent* — the verifier's top-of-stack just before that
// op executes. This pre-pass computes that, mirroring LKRVerifier's
// per-op mutations but skipping the duality/freshness checks.
//
// Output:
//   - sequent_before[idx] = entries of the top open goal at the moment
//                           op idx executes.
//   - term_env[idx]       = Term bound by op idx (meaningful only for
//                           Forall, which binds Term::fixed(eigen)).
//
// Assumes the input LKR program is well-typed (LKRVerifier accepts it).
// Out-of-stack situations are reported as Errors but should not occur
// for verifier-accepted input.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstdint>
#include <optional>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

struct SequentReplay {
    // Per-op snapshot of the top open-goal's entries just before
    // exec_op runs. For branching ops (And, Cut), this is the goal
    // BEFORE the split (the children are reconstructed from this).
    std::vector<std::vector<FormulaHandle>> sequent_before;

    // Per-op snapshot of each sequent entry's *canonical positions* in
    // the goal's fograph. For each entry at sequent_before[op][i], the
    // vector entry_positions[op][i] lists the vertex indices in
    // Fograph(initial_goal_nnf) that the entry's vertices occupy, in
    // pre-order of the entry's structure.
    //
    // This is the key piece for §11.1 translation: leaves and per-rule
    // operations use these canonical positions to build fibrations
    // against the canonical target — bypassing per-step target rebuilds
    // that would permute label order (and trip the verifier's strict
    // positional comparison).
    //
    // Caveat: Weakening / Cut introduce NEW positions that aren't in
    // the initial goal. Those phases will extend the canonical target
    // (augmenting per §15 for Cut, appending for Weakening) and assign
    // fresh positions accordingly.
    std::vector<std::vector<std::vector<size_t>>> entry_positions;

    // Per-op bound Term. Populated for Forall (the eigen). Other ops
    // bind nothing — entries stay nullopt.
    std::vector<std::optional<Term>> term_env;
};

// Replay the program against an initial sequent [goal_nnf]. The
// FormulaBuilder is used for to_nnf / instantiate operations.
//
// `cut_aug` supplies per-cut start positions in the augmented target;
// Cut ops use these to populate canonical positions for the cut entries
// they introduce. Pass an empty CutAugmentation (with empty vectors) if
// the program has no Cut ops.
struct CutAugmentation;
util::Result<SequentReplay> replay_sequents(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog,
    const CutAugmentation&     cut_aug);

}  // namespace logic::proof::translate::lkr_to_comb
