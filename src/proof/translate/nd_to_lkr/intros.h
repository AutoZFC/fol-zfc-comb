#pragma once

// Stage 2 Phase 1: introductions (cut-free right rules).
//
// Per CUT_MINIMAL_DESIGN.md §5, each emitter handles ONE ND introduction
// op and emits the corresponding LKR right rule(s). No recursion inside
// the emitter — the dispatcher (Phase 5) owns control flow and recurses
// into the per-premise positions the emitter returns.
//
// Per-op contract:
//   PRE:    shadow.entries[f_k_idx] == NNF(F_k), where F_k is the op's
//           result formula. (Caller's responsibility; precondition
//           violation is a translator bug, not an input bug.)
//
//   ACTION: emit ≥1 LKR right-rule op(s) into `out` and return an
//           IntroResult naming the post-state shadow(s) and per-premise
//           positions the dispatcher will recurse into.
//
//   POST:   the (α) result-visibility invariant holds at each returned
//           premise_pos: the corresponding ND premise step's derived
//           formula NNF is the shadow entry at that position.
//
// Per CUT_MINIMAL_DESIGN.md §1.4, this phase emits ZERO Cut ops. Any
// emitter that cannot satisfy the contract for some input shape is a
// spec gap, not a license to emit Cut.
//
// NotIntro and BottomElim are NOT in Phase 1 — they're block closers
// and live in Phase 4 (structural.{h,cpp}). The dispatcher routes them
// past the Phase 1 emitter table.

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
#include <variant>
#include <vector>

namespace logic::proof::translate::nd_to_lkr::intros {

// Phase-1 emitter context. Minimal: enough to (a) NNF-convert formulas
// when building Weakening payloads, (b) look up TermRef bindings in
// the shadow's lkr_term_for, (c) diagnose with op headers.
struct Ctx {
    GlobalContext&                   ctx;
    FormulaBuilder&                  builder;
    const Program<nd::Instr>&        prog;
    const nd::NDVerifier::TraceFull& trace;
};

// =========================================================================
// Per-emitter return variants.
// =========================================================================

// ZeroPremise: the emitter's LKR ops close the goal entirely. The
// dispatcher must NOT recurse on the op's ND premises (they're either
// inert Let-payloads or absent). Used by ExcludedMiddle and Peirce.
struct ZeroPremise {};

// OnePremise: non-branching right rule (Or, Forall, Exists, ...) or
// a demand-aware short-circuit (AndIntro under AND_LEFT/RIGHT,
// IffIntro under IFF_LEFT/RIGHT). The post-state `shadow` has the
// decomposed structure; the dispatcher recurses on `premise_step`
// (explicit ND step ref) against (shadow, premise_pos).
struct OnePremise {
    SequentShadow shadow{};
    size_t        premise_pos{0};
    StepRef       premise_step{};
};

// TwoPremise: branching right rule (And, IffIntro under NONE). Each
// branch receives its own post-state shadow; the dispatcher recurses
// on the LEFT ND premise (left_step) against (left_shadow, left_pos)
// and on the RIGHT ND premise (right_step) against (right_shadow,
// right_pos). The two shadows reflect the multiplicative split (with
// full-context duplication per CUT_MINIMAL_DESIGN.md §5.1.1).
struct TwoPremise {
    SequentShadow left_shadow{};
    SequentShadow right_shadow{};
    size_t        left_pos{0};
    size_t        right_pos{0};
    StepRef       left_step{};
    StepRef       right_step{};
};

using IntroResult = std::variant<ZeroPremise, OnePremise, TwoPremise>;

// =========================================================================
// Phase 1 emitters.
// =========================================================================

// All Phase 1 emitters take an optional `demand` parameter (default
// DemandNone). Under non-NONE demand, demand-aware emitters
// short-circuit:
//
//   AndIntro under DemandAndLeft  → OnePremise routing to op.a, no And emitted.
//   AndIntro under DemandAndRight → OnePremise routing to op.b, no And emitted.
//   IffIntro under DemandIffLeft  → OnePremise routing to op.ab, no And emitted.
//   IffIntro under DemandIffRight → OnePremise routing to op.ba, no And emitted.
//   ForallIntro under DemandInstance(t) → reserved for Phase 5c (eigen
//     substitution requires dispatcher integration); currently returns error.
//
// All other (emitter, demand) combinations are unsupported and return
// an error — a translator bug if the dispatcher routes them here.

// AndIntro(a, b) — multiplicative ∧R with full-context duplication.
//   Under DemandNone: emits |Γ| Weakenings then And. Returns TwoPremise.
//   Under DemandAndLeft/Right: emits nothing; returns OnePremise.
util::Result<IntroResult> emit_and_intro(
    Ctx&                       cc,
    const nd::AndIntro&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// OrIntroL(a, b_formula) — ∨R; left disjunct is derived.
util::Result<IntroResult> emit_or_intro_l(
    Ctx&                       cc,
    const nd::OrIntroL&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// OrIntroR(a_formula, b) — ∨R; right disjunct is derived.
util::Result<IntroResult> emit_or_intro_r(
    Ctx&                       cc,
    const nd::OrIntroR&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// ImpliesIntro(conclusion) — NNF(A→B) = NNF(¬A) ∨ NNF(B).
util::Result<IntroResult> emit_implies_intro(
    Ctx&                       cc,
    const nd::ImpliesIntro&    op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// IffIntro(ab, ba) — NNF(A↔B) = (NNF(¬A)∨NNF(B)) ∧ (NNF(¬B)∨NNF(A)).
//   Under DemandNone: And split + Weakenings. TwoPremise.
//   Under DemandIffLeft: OnePremise routing to op.ab.
//   Under DemandIffRight: OnePremise routing to op.ba.
util::Result<IntroResult> emit_iff_intro(
    Ctx&                       cc,
    const nd::IffIntro&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// ForallIntro(body) with eigen — ∀R.
util::Result<IntroResult> emit_forall_intro(
    Ctx&                       cc,
    const nd::ForallIntro&     op,
    var_index                  eigen,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// ExistsIntro(body, witness=t) — ∃R with explicit witness.
util::Result<IntroResult> emit_exists_intro(
    Ctx&                       cc,
    const nd::ExistsIntro&     op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// ExcludedMiddle(formula_let) — fixed cut-free skeleton.
util::Result<IntroResult> emit_excluded_middle(
    Ctx&                       cc,
    const nd::ExcludedMiddle&  op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

// Peirce(a_let, b_let) — fixed cut-free skeleton for Peirce's law.
util::Result<IntroResult> emit_peirce(
    Ctx&                       cc,
    const nd::Peirce&          op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand = Demand{DemandNone{}});

}  // namespace logic::proof::translate::nd_to_lkr::intros
