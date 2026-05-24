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
#include <vector>

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
// DemandPath — ordered chain of projection demands.
// =========================================================================
//
// Projection elims compose. For a consumer chain like
//   forall_elim(h_ax: ∀x.(p∧q), t) → (p∧q)(t)
//   and_elim_l(_)                  → p(t)
// the demand at the lemma h_ax must encode BOTH projections in order:
// "INSTANCE(t) first (peels ∀), then AND_LEFT (peels ∧)."
//
// Chain semantics:
//   path[0]   = first projection to apply (= lemma's outermost shape)
//   path[N-1] = last projection (= deepest nested shape)
//
// Composition rule: each projection elim PREPENDS its demand to the
// incoming chain. The dispatcher's recursion at a projection elim
// step transforms the incoming chain into {its_demand} ++ incoming.
//
// At leaves (Use, SchemaInst, Assume, ExistsElim), the chain is
// applied in order: Cut(lemma_full) + structural decomposition (Exists
// for INSTANCE, Or for AND_LEFT/RIGHT, ...) + emit_close.
//
// Empty path == DemandNone (no projection applied).

using DemandPath = std::vector<Demand>;

// =========================================================================
// RecurseDescriptor — Phase 2 emitter output.
// =========================================================================
//
// A projection elim's emitter returns one of these. The dispatcher
// (Phase 5) follows the descriptor: it visits `producer_step_idx`,
// passing the composed chain (PREPEND descriptor's demand to incoming
// chain) to the producer's recursion, with `target_pos` as where the
// result should land.

struct RecurseDescriptor {
    StepRef producer{};                 // the ND step to recurse into
    size_t  target_pos{0};               // sequent position where result lands
    Demand  demand{DemandNone{}};        // the projection's own demand
};

}  // namespace logic::proof::translate::nd_to_lkr
