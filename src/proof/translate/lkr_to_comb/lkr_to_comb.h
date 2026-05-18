#pragma once

// LKRtoComb — translate LKR proofs to combinatorial proofs (Hughes 2019
// §11.1 + §15 cut handling).
//
// See LKR_TO_COMB_DESIGN.md for the full mathematical specification.
//
// **Input contract** (enforced by InputGate):
//   - LKR-verifies under LKRVerifier against goal_formula
//
// **Output contract** (enforced by OutputGate):
//   - comb::CombProof verifies under CombVerifier against the augmented
//     goal (goal_formula disjuncted with each Cut formula's θ ∧ ¬θ)
//
// The output type is comb::CombProof (a graph-theoretic object), not
// Program<comb::Instr>. Comb is the ultimate witness layer per Hughes
// Theorem 6.4 + 15.1.

#include "lemma_inliner.h"

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <unordered_map>

namespace logic::proof::translate::lkr_to_comb {

// Registry of previously-proven lemmas, used by `CloseByLemma` via
// Strategy A (LKR-level inlining; see LKR_TO_COMB_DESIGN.md §4.12).
// Each entry's LKR program must standalone-verify under LKRVerifier
// against the lemma's formula. Caller populates this as theorems are
// translated.
using LemmaCombProofs = LemmaPrograms;

class LKRtoComb {
public:
    LKRtoComb(GlobalContext& ctx, FormulaHandle goal_formula,
              const LemmaCombProofs& lemmas)
        : ctx_(ctx), goal_(goal_formula), lemmas_(lemmas) {}

    util::Result<comb::CombProof> apply(const Program<lkr::Instr>& in);

private:
    GlobalContext&         ctx_;
    FormulaHandle          goal_;
    const LemmaCombProofs& lemmas_;
};

}  // namespace logic::proof::translate::lkr_to_comb
