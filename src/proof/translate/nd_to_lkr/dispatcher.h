#pragma once

// Stage 2 Phase 5: dispatcher — recursive descent on the ND derivation
// tree starting at Qed.derived. Per CUT_MINIMAL_DESIGN.md §1.4:
//
//   translate_step(step, shadow, target_pos, demand)
//     reads program[step] and routes to the appropriate Phase 1-4
//     emitter. For intro ops with non-trivial premise structure
//     (OnePremise / TwoPremise), recurses on the premise(s) with the
//     shadow + position the emitter produces. For ZeroPremise
//     emitters (ExcludedMiddle, Peirce), no recursion — the emitter
//     closes the goal itself.
//
// Phase 5b (this header lands): intro-op dispatch + ExcludedMiddle/
// Peirce ZeroPremise closure. Other op families (projection elims,
// combining elims, structural openers/closers, Assume leaves) return
// "not yet supported" errors. Successive sub-phases (5c-5e) wire each
// family in.

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/demand.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/util/error.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::nd_to_lkr::dispatcher {

// Dispatcher-wide context. Carries the shared resources every phase
// needs; the dispatcher itself plus per-phase emitters thread `Ctx`
// through their call graphs.
struct Ctx {
    GlobalContext&                   ctx;
    FormulaBuilder&                  builder;
    const Program<nd::Instr>&        prog;
    const nd::NDVerifier::TraceFull& trace;
};

// Recursive entry point. Translates `step`'s derivation into LKR ops
// appended to `out`, leaving the result formula NNF visible at
// `target_pos` of the resulting shadow (the result-visibility
// invariant per CUT_MINIMAL_DESIGN.md §1.3).
//
// `shadow` is consumed (by value) and the dispatcher may mutate
// internally; on success, the caller does not see `shadow` updated
// — the caller's view of the post-state lives in `out`'s LKR ops as
// interpreted by LKRVerifier.
//
// `demand`:
//   DemandNone — produce the full F_step at target_pos.
//   Demand{AndLeft/AndRight/IffLeft/IffRight} — promoted by Phase 2
//     projection elims; consumed by Phase 1 demand-aware emitters.
//   DemandInstance(t) — Phase 5c work; currently rejected upstream.
//
// Errors:
//   - op-family not yet supported at this sub-phase (5b → 5e roadmap).
//   - emitter precondition violations (shape mismatch, etc.).
util::ResultStatus translate_step(
    Ctx&                       dcc,
    SequentShadow              shadow,
    StepRef                    step,
    size_t                     target_pos,
    Demand                     demand,
    std::vector<lkr::Instr>&   out);

}  // namespace logic::proof::translate::nd_to_lkr::dispatcher
