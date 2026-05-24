#pragma once

// Stage 2 Phase 3: combining elims (the Cut sites).
//
// Per CUT_MINIMAL_DESIGN.md §6.2, each combining-elim emitter projects
// an ND combining-elim op into a CombineSite descriptor naming the
// major + minor step references and the consumer's target position.
//
// **No LKR ops are emitted at this phase.** The actual Cut + structural
// emission (the And-decomposition of NNF(¬major), AxiomLit closes,
// nested Cut on minor premises for implies_elim, etc.) lives in
// Phase 5 — that's where the dispatcher integrates Phase 1's intros,
// Phase 2's projection elims, and Phase 3's combining-elim sites with
// the full recursion structure.
//
// Per α policy + the controlling design, NotElim is NOT in scope here:
// it's no-emit, with closer handling in Phase 4 (structural).

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/util/error.h"

#include <cstddef>

namespace logic::proof::translate::nd_to_lkr::combining {

// Per-phase context. Shape matches Phase 1's intros::Ctx and Phase 2's
// projections::Ctx — shared resources for uniform dispatcher wiring.
struct Ctx {
    GlobalContext&                   ctx;
    FormulaBuilder&                  builder;
    const Program<nd::Instr>&        prog;
    const nd::NDVerifier::TraceFull& trace;
};

// =========================================================================
// CombineSite descriptors — Phase 3 emitter output.
// =========================================================================
//
// Phase 5 consumes these to emit the combining-elim's full LKR
// translation. Each descriptor names: (a) the major premise step
// (Cut on its NNF formula), (b) minor premise step(s) the RIGHT
// branch's closure plan references, (c) target_pos where the
// combining-elim's result formula lands in the consumer's sequent.

// implies_elim(impl: A→B, ant: A) ⊢ B.
//   Major = impl (NNF = ¬A ∨ B; Cut emits this).
//   Minor = ant (used by RIGHT-branch closure to refute the A inside
//                NNF(¬(A→B)) = A ∧ ¬B).
struct ImpliesElimSite {
    StepRef impl_step{};
    StepRef ant_step{};
    size_t  target_pos{0};
};

// or_elim(or_formula: A∨B, ac: A→C, bc: B→C) ⊢ C.
//   Major = or_formula (NNF = A ∨ B; Cut emits this).
//   Minors = ac, bc (used by RIGHT-branch closure to derive C in each
//                    case via the two implications).
struct OrElimSite {
    StepRef or_formula_step{};
    StepRef ac_step{};
    StepRef bc_step{};
    size_t  target_pos{0};
};

// exists_elim(formula: ∃x.φ) ⊢ C, where C is the surrounding block's
// result and the eigenvariable v binds the witness within the block.
//   Major = formula (NNF = ∃x.NNF(φ); Cut emits this).
//   The block body's translation (Phase 4 + Phase 5 scope handling)
//   uses the bound eigen on the RIGHT branch where ∀x.NNF(¬φ) lives.
struct ExistsElimSite {
    StepRef formula_step{};
    size_t  target_pos{0};
};

// =========================================================================
// Phase 3 emitters.
// =========================================================================

util::Result<ImpliesElimSite> emit_implies_elim(
    Ctx&                       cc,
    const nd::ImpliesElim&     op,
    const SequentShadow&       shadow,
    size_t                     target_pos);

util::Result<OrElimSite> emit_or_elim(
    Ctx&                       cc,
    const nd::OrElim&          op,
    const SequentShadow&       shadow,
    size_t                     target_pos);

util::Result<ExistsElimSite> emit_exists_elim(
    Ctx&                       cc,
    const nd::ExistsElim&      op,
    const SequentShadow&       shadow,
    size_t                     target_pos);

}  // namespace logic::proof::translate::nd_to_lkr::combining
