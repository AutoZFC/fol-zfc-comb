#pragma once

// Demand variant: the cut-free projection-elim mechanism.
//
// Per CUT_MINIMAL_DESIGN.md §1.4 + §6.1, Prawitz' correspondence makes
// projection elims cut-free by "absorption into the producer's
// translation." A projection elim like `and_elim_l(h_ab)` does NOT emit
// LKR ops itself — it issues a Demand to the recursion, which then
// drives the producer's translation to expose the demanded sub-formula
// directly.
//
// Demand values are produced by Phase 2 (projection emitters) and
// consumed by Phase 5 (dispatcher) + demand-aware Phase 1 emitters.

#include "src/core/formula.h"
#include "src/proof/ir.h"

#include <variant>

namespace logic::proof::translate::nd_to_lkr {

// =========================================================================
// Demand
// =========================================================================
//
// Default behavior: NONE (produce the full F_k). Other variants
// short-circuit the producer's emission to extract just the demanded
// sub-formula.

struct DemandNone {};                               // default; full F_k.
struct DemandAndLeft {};                            // ↞ and_elim_l: F_k's ⋀-left.
struct DemandAndRight {};                           // ↞ and_elim_r: F_k's ⋀-right.
struct DemandIffLeft {};                            // ↞ iff_elim_l: forward A→B.
struct DemandIffRight {};                           // ↞ iff_elim_r: reverse B→A.
struct DemandDoubleNeg {};                          // ↞ double_neg_elim: strip ¬¬.

// INSTANCE(t, lkr_ref): ↞ forall_elim. The producer's ∀x.φ is
// instantiated at the term `t`. Phase 1's demand-aware ForallIntro
// substitutes eigen→t in the body when it sees this demand;
// shadow.lkr_term_for[fix_idx] is updated to {lkr_ref, t} so body-
// side LKR-TermRef references (e.g. nested Exists witness) resolve
// to the original LKR binding instr for t.
struct DemandInstance {
    Term    t{};
    TermRef lkr_ref{};
};

using Demand = std::variant<
    DemandNone,
    DemandAndLeft, DemandAndRight,
    DemandIffLeft, DemandIffRight,
    DemandDoubleNeg,
    DemandInstance
>;

// =========================================================================
// RecurseDescriptor — Phase 2 emitter output.
// =========================================================================
//
// A projection elim's emitter returns one of these. The dispatcher
// (Phase 5) follows the descriptor: it visits `producer_step_idx`,
// passing `demand` to the producer's emitter, with `target_pos` as
// where the result should land.
//
// Phase 2 emitters emit ZERO LKR ops; their entire contribution is the
// descriptor. The math (demand consumption) lives in Phase 5 +
// demand-aware Phase 1.

struct RecurseDescriptor {
    StepRef producer{};      // the ND step whose derivation we recurse into
    size_t  target_pos{0};   // sequent position where the result lands
    Demand  demand{DemandNone{}};
};

}  // namespace logic::proof::translate::nd_to_lkr
