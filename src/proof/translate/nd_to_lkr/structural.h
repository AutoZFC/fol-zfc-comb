#pragma once

// Stage 2 Phase 4: structural ops (Fix / Assume / ExistsElim / Qed)
// and α-policy closers (NotIntro / BottomElim / ClassicalAbsurd).
//
// Per CUT_MINIMAL_DESIGN.md §6.3, each emitter projects an ND op into
// a structural-site descriptor naming the step refs, formulas, and
// eigen identifiers the dispatcher (Phase 5) needs to:
//   - thread block-tree scope into the recursion (openers);
//   - close NOT / BottomElim / CLASSICAL_ABSURD goals via emit_close
//     on NotElim operand positions (closers; α policy);
//   - close references to assumed formulas (leaf case).
//
// **No LKR ops are emitted at this phase.** Phase 5 dispatches.
//
// NotElim itself has NO emitter (per α policy: no-emit, always). Its
// operands are extracted by the enclosing closer's emitter via the
// `bottom` step ref + program lookup.

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/util/error.h"

#include <cstddef>

namespace logic::proof::translate::nd_to_lkr::structural {

// Per-phase context. Same shape as Phases 1-3's Ctx — shared
// resources for uniform dispatcher wiring. Phase 4's closer
// emitters dereference `prog` to read the NotElim ghost behind
// `bottom`; opener emitters read `trace` for eigenvariable indices.
struct Ctx {
    GlobalContext&                   ctx;
    FormulaBuilder&                  builder;
    const Program<nd::Instr>&        prog;
    const nd::NDVerifier::TraceFull& trace;
};

// =========================================================================
// Opener descriptors (scope manipulators).
// =========================================================================

// Assume(A): assumption-scope opener. Carries the resolved formula
// (NDVerifier-validated; trace.step_env[assume_step.idx]) so Phase 5
// can compute NNF and find the dual entry placed by the enclosing
// IMPLIES/NOT/CLASSICAL_ABSURD intro emitter.
struct AssumeOpenSite {
    StepRef       assume_step{};
    FormulaHandle formula{};
};

// Fix(v): eigenvariable-scope opener. The trace's term_env[fix_step.idx]
// holds Term::fixed(eigen); Phase 5 binds shadow.lkr_term_for using it.
struct FixOpenSite {
    StepRef   fix_step{};
    var_index eigen{};
};

// ExistsElim(formula): existential-elim opener. Opens an EXISTS_ELIM
// block bound by a fresh eigen. Phase 5 emits the combining-elim Cut
// per Phase 3 (ExistsElimSite) and binds the eigen for the body.
struct ExistsElimOpenSite {
    StepRef   exists_elim_step{};
    StepRef   formula_step{};
    var_index eigen{};
};

// =========================================================================
// Closer descriptors (α-policy emit_close drivers).
// =========================================================================
//
// Each closer's `bottom` field points to a NotElim step. The emitter
// dereferences the program to extract NotElim's (negation, formula)
// operand step refs. Phase 5 closes via emit_close on those operands'
// LKR sequent positions.

struct NotIntroCloseSite {
    StepRef not_intro_step{};
    StepRef neg_step{};        // from NotElim.negation
    StepRef formula_step{};    // from NotElim.formula
};

struct BottomElimCloseSite {
    StepRef bottom_elim_step{};
    StepRef neg_step{};
    StepRef formula_step{};
    StepRef target_formula{};  // BottomElim.target_formula — the C derived
};

struct ClassicalAbsurdCloseSite {
    StepRef absurd_step{};
    StepRef neg_step{};
    StepRef formula_step{};
};

// =========================================================================
// Leaf descriptor (Assume reference in recursive descent).
// =========================================================================

// When the dispatcher recurses on an Assume step (= a reference from
// a downstream op like ImpliesElim's `ant`), the leaf handler closes
// the current LKR goal against the dual position recorded when the
// enclosing intro emitter placed NNF(¬A).
struct AssumeLeafSite {
    StepRef assume_step{};
    size_t  target_pos{0};
};

// =========================================================================
// Entry point.
// =========================================================================

// Qed: terminates the OUTER block. derived_step is the proof's
// conclusion — Phase 5's recursive-descent entry point.
struct QedSite {
    StepRef qed_step{};
    StepRef derived_step{};
};

// =========================================================================
// Phase 4 emitters.
// =========================================================================

util::Result<AssumeOpenSite> emit_assume_open(
    Ctx&                       cc,
    const nd::Assume&          op,
    StepRef                    assume_step);

util::Result<FixOpenSite> emit_fix_open(
    Ctx&                       cc,
    const nd::Fix&             op,
    StepRef                    fix_step);

util::Result<ExistsElimOpenSite> emit_exists_elim_open(
    Ctx&                       cc,
    const nd::ExistsElim&      op,
    StepRef                    exists_elim_step);

util::Result<NotIntroCloseSite> emit_not_intro_close(
    Ctx&                       cc,
    const nd::NotIntro&        op,
    StepRef                    not_intro_step);

util::Result<BottomElimCloseSite> emit_bottom_elim_close(
    Ctx&                       cc,
    const nd::BottomElim&      op,
    StepRef                    bottom_elim_step);

util::Result<ClassicalAbsurdCloseSite> emit_classical_absurd_close(
    Ctx&                       cc,
    const nd::ClassicalAbsurd& op,
    StepRef                    absurd_step);

util::Result<AssumeLeafSite> emit_assume_leaf(
    Ctx&                       cc,
    const nd::Assume&          op,
    StepRef                    assume_step,
    const SequentShadow&       shadow,
    size_t                     target_pos);

util::Result<QedSite> emit_qed_site(
    Ctx&                       cc,
    const nd::Qed&             op,
    StepRef                    qed_step);

}  // namespace logic::proof::translate::nd_to_lkr::structural
