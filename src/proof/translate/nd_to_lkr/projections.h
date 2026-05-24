#pragma once

// Stage 2 Phase 2: projection elims (demand-driven, cut-free).
//
// Per CUT_MINIMAL_DESIGN.md §6.1, each emitter projects an ND
// projection-elim op into a RecurseDescriptor — naming (a) the
// producer step to recurse into, (b) the target sequent position
// where the demanded sub-formula lands, (c) the Demand variant
// promoted by the elim.
//
// **No LKR ops are emitted at this phase.** The cut-free
// semantics live in the demand-consumption logic at Phase 5
// (dispatcher) + demand-aware Phase 1 emitters.
//
// The (α) result-visibility invariant transfers through these
// descriptors: when Phase 5 follows a descriptor and the producer's
// demand-aware emission lands the demanded sub-formula at
// target_pos, the consumer's expected position is satisfied.

#include "demand.h"

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/util/error.h"

#include <cstddef>

namespace logic::proof::translate::nd_to_lkr::projections {

// Per-phase context. Same shape as Phase 1's intros::Ctx — shared
// resources (ctx, builder, prog, trace). For Phase 2's purposes,
// `prog` and `trace` are typically unused (emitters read only the op
// + shadow for forall_elim's TermRef resolution), but the structure
// is kept uniform with Phase 1.
struct Ctx {
    GlobalContext&                   ctx;
    FormulaBuilder&                  builder;
    const Program<nd::Instr>&        prog;
    const nd::NDVerifier::TraceFull& trace;
};

// =========================================================================
// Per-op emitters. Each returns a RecurseDescriptor or an Error. No
// LKR ops are emitted (no `out` parameter).
// =========================================================================

// and_elim_l(of): demand=AND_LEFT on producer `of`. target_pos is the
// consumer's expected position for F_k (the left conjunct).
util::Result<RecurseDescriptor> emit_and_elim_l(
    Ctx&                       cc,
    const nd::AndElimL&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

// and_elim_r(of): demand=AND_RIGHT on producer `of`.
util::Result<RecurseDescriptor> emit_and_elim_r(
    Ctx&                       cc,
    const nd::AndElimR&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

// iff_elim_l(iff, a): from A↔B and A, derive B. demand=IFF_LEFT
// requests "forward direction" (the A→B disjunct in NNF). The other
// premise `a` is in scope; the dispatcher's recursion may close
// against it later.
util::Result<RecurseDescriptor> emit_iff_elim_l(
    Ctx&                       cc,
    const nd::IffElimL&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

// iff_elim_r(iff, b): from A↔B and B, derive A. demand=IFF_RIGHT
// requests "reverse direction" (the B→A disjunct in NNF).
util::Result<RecurseDescriptor> emit_iff_elim_r(
    Ctx&                       cc,
    const nd::IffElimR&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

// double_neg_elim(of): from ¬¬A, derive A. demand=DOUBLE_NEG strips
// the outer double-negation, exposing the inner A in the producer's
// translation.
util::Result<RecurseDescriptor> emit_double_neg_elim(
    Ctx&                       cc,
    const nd::DoubleNegElim&   op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

// forall_elim(formula, term): from ∀x.φ and term t, derive φ[x:=t].
// demand=INSTANCE(t) carries the witness term. The emitter resolves
// the ND TermRef into a concrete Term via shadow.lkr_term_for. Failure
// to find the binding is a translator bug (preceding Fix step should
// have established it).
util::Result<RecurseDescriptor> emit_forall_elim(
    Ctx&                       cc,
    const nd::ForallElim&      op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx);

}  // namespace logic::proof::translate::nd_to_lkr::projections
