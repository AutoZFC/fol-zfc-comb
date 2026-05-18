#pragma once

// F2 walk — recursive translation of a DerivationTree into a CombProof
// against the §15-augmented goal.
//
// Per LKR_TO_COMB_F2_DESIGN.md, each per-rule operation is defined
// against per-hypothesis targets G(H_i) = G(Γ_i) + G(ϕ_i) (Hughes
// §11.1, Lemma 11.2). Each walk_recursive call returns a
// CombProof-like triple (source, target, fibration) against the
// node's conclusion sequent's target. The root's target is the
// §15-augmented goal — built compositionally as Cut nodes accumulate
// (θ ∧ ¬θ) summands bottom-up.

#include "lemma_inliner.h"
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

// Mirror of LemmaCombProofs in lkr_to_comb.h. After Strategy A (§4.12),
// the registry holds LKR programs, not CombProofs. CloseByLemma is
// spliced out by the lemma_inliner pre-pass before walk runs, so this
// map is only consulted as a safety-net fallback (which should never
// fire for spliced programs).
using LemmaCombProofs_ = LemmaPrograms;

struct WalkContext {
    FormulaBuilder&             builder;
    const Program<lkr::Instr>&  prog;
    const SequentReplay&        replay;
    const LemmaCombProofs_&     lemmas;
    // Allocator for per-hypothesis target binder vars. Walk starts this
    // above the max LKR eigen so target binder vars never collide with
    // LKR's Forall eigens (which appear as witness terms in dualizer
    // values from rule_exists).
    var_index                   next_target_var{0};
};

// Translate the tree into a combinatorial proof of the §15-augmented
// goal. The output's target is set to a fograph that compares equal
// (structurally) to Fograph(NNF(augmented_goal)); its source_formula
// is set to `augmented_goal_formula` so the OutputGate's
// well-formedness check passes.
util::Result<comb::CombProof> walk(
    WalkContext&           cc,
    const DerivationTree&  tree,
    FormulaHandle          augmented_goal_formula);

}  // namespace logic::proof::translate::lkr_to_comb
