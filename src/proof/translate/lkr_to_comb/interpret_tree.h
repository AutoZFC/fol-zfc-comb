#pragma once

// interpret_tree — paper-exact (Hughes §11.1) LKR→Comb fold.
//
// See PAPER_EXACT_DESIGN.md. Folds the LKR DerivationTree bottom-up,
// interpreting each cut-free LKR rule as a local operation on
// combinatorial proofs (Lemma 11.2). Runs in parallel with walk.cpp
// until P8.
//
// Scope: cut-free LKR (§11's nine rules). Cut / CloseByLemma are out of
// scope and produce an error.

#include "src/proof/comb/comb_proof.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_to_comb/sequent_replay.h"
#include "src/proof/translate/lkr_to_comb/tree.h"
#include "src/util/error.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

// The combinatorial proof of a derivation-tree node's conclusion sequent.
struct NodeProof {
    comb::Fograph       target;      // G(Φ(Γ)) for this node's conclusion Γ
    comb::Fonet         source;      // the fonet N
    std::vector<size_t> fibration;   // f : V_source → V_target
};

// Fold the whole tree into a CombProof of the initial goal.
// `goal_nnf` is the NNF of the proof's goal; the root node's target must
// equal G(goal_nnf).
util::Result<comb::CombProof> interpret_tree(
    GlobalContext&                  ctx,
    FormulaHandle                   goal_nnf,
    const Program<lkr::Instr>&      prog,
    const DerivationTree&           root,
    const SequentReplay&            replay);

}  // namespace logic::proof::translate::lkr_to_comb
