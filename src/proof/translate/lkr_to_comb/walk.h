#pragma once

// §11.1 walk — recursive translation of a DerivationTree into a CombProof.
//
// Per LKR_TO_COMB_DESIGN.md §3.3, the walk visits each tree node and
// constructs the (N, G, f) state for that node's subgoal. All subgoals
// share the canonical target G(initial_goal_nnf); fibrations are built
// in those canonical coordinates throughout, using the per-entry
// canonical positions tracked by SequentReplay.
//
// **First-phase coverage** (this implementation):
//   - Leaves: AxiomLit only. One and CloseByLemma deferred.
//   - Linear: Or, Exchange (no fibration change), Weakening (target
//     unchanged at this phase; provenance limits Weakening to goals
//     whose new entries weren't subsequently referenced).
//   - Branching: And (multiplicative, both-strong + degenerate cases).
//   - Cut, Contraction, Forall, Exists, CloseByLemma deferred.

#include "sequent_replay.h"
#include "tree.h"

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <string>
#include <unordered_map>

namespace logic::proof::translate::lkr_to_comb {

// Mirror of LemmaCombProofs in lkr_to_comb.h. We can't include
// lkr_to_comb.h here (it transitively depends on us); instead we keep
// the typedef in both places — they're identical.
using LemmaCombProofs_ = std::unordered_map<std::string, comb::CombProof>;

struct WalkContext {
    FormulaBuilder&             builder;
    const Program<lkr::Instr>&  prog;
    const SequentReplay&        replay;
    // Canonical target: G(augmented_goal_nnf). All subgoal CombProofs
    // share this target; only their fonet + fibration differ.
    const comb::Fograph&        canonical_target;
    // Lemma registry for CloseByLemma (Strategy B).
    const LemmaCombProofs_&     lemmas;
};

// Translate the tree into a combinatorial proof of the canonical target.
util::Result<comb::CombProof> walk(
    WalkContext&           cc,
    const DerivationTree&  tree);

}  // namespace logic::proof::translate::lkr_to_comb
