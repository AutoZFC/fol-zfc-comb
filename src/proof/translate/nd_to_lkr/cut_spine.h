#pragma once

// Cut-spine driver — emits LKR ops by recursively translating the
// block tree.
//
// Per ND_TO_LKR_DESIGN.md §4, the OUTER block (the root) seeds the
// translation with sequent shadow [NNF(goal)]. Each FlatStep emits a
// Cut(F_k_nnf), proves F_k on LEFT via the per-rule close_X schema,
// and carries NNF(¬F_k) into Γ on RIGHT. Each sub-block emits its
// opener (Or for IMPLIES, Forall for FORALL, etc.), recurses on the
// body, then closes via emit_close on the block's target step.

#include "block_tree.h"
#include "sequent_shadow.h"

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <vector>

namespace logic::proof::translate::nd_to_lkr {

struct CutSpineContext {
    GlobalContext&                     ctx;
    FormulaBuilder&                    builder;
    const Program<nd::Instr>&          prog;
    // Trace state from NDVerifier::trace_full. The translator reads:
    //   - step_env[k]    — F_k for each ND step
    //   - term_env[k]    — Term for binding instrs (Fix, ExistsElim,
    //                       IotaElim though we reject iota upstream)
    //   - term_present[k] — whether term_env[k] is valid
    const nd::NDVerifier::TraceFull&  trace;
};

// Top-level: translate the OUTER block into an LKR instruction stream.
//
// PRECONDITION: `outer.kind == OUTER`. `goal_nnf` is the NNF of the
// claim's goal formula. `trace` was produced by NDVerifier::trace_formulas
// for the same program.
//
// On success, the returned vector is the body of a Program<lkr::Instr>
// that the OutputGate can hand to LKRVerifier.
util::Result<std::vector<lkr::Instr>> translate_outer(
    CutSpineContext&    cc,
    const Block&        outer,
    FormulaHandle       goal_nnf);

}  // namespace logic::proof::translate::nd_to_lkr
