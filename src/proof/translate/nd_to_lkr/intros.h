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
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
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

// OnePremise: non-branching right rule (Or, Forall, Exists, ...). The
// post-state `shadow` has the decomposed structure; the dispatcher
// recurses on the ND op's single derived premise step against
// (shadow, premise_pos). Used by OrIntroL, OrIntroR, ImpliesIntro,
// ForallIntro, ExistsIntro.
struct OnePremise {
    SequentShadow shadow{};
    size_t        premise_pos{0};
};

// TwoPremise: branching right rule (And, IffIntro). Each branch
// receives its own post-state shadow; the dispatcher recurses on the
// LEFT ND premise against (left_shadow, left_pos) and on the RIGHT ND
// premise against (right_shadow, right_pos). The two shadows reflect
// the multiplicative split (with full-context duplication per
// CUT_MINIMAL_DESIGN.md §5.1.1).
struct TwoPremise {
    SequentShadow left_shadow{};
    SequentShadow right_shadow{};
    size_t        left_pos{0};
    size_t        right_pos{0};
};

using IntroResult = std::variant<ZeroPremise, OnePremise, TwoPremise>;

// =========================================================================
// Phase 1 emitters.
// =========================================================================

// AndIntro(a, b) — multiplicative ∧R with full-context duplication.
//   Emits |Γ| Weakenings (one per non-principal entry) then
//   And{principal=f_k_idx, right_needs=[duplicate indices]}.
//   Returns TwoPremise with both branches carrying the full context.
util::Result<IntroResult> emit_and_intro(
    Ctx&                       cc,
    const nd::AndIntro&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// OrIntroL(a, b_formula) — ∨R; left disjunct is derived.
//   Emits Or{principal=f_k_idx}. After: A at f_k_idx, NNF(B) appended.
//   Returns OnePremise{shadow, premise_pos=f_k_idx}.
util::Result<IntroResult> emit_or_intro_l(
    Ctx&                       cc,
    const nd::OrIntroL&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// OrIntroR(a_formula, b) — ∨R; right disjunct is derived.
//   Emits Or{principal=f_k_idx}. After: NNF(A) at f_k_idx, B appended.
//   Returns OnePremise{shadow, premise_pos=end_idx}.
util::Result<IntroResult> emit_or_intro_r(
    Ctx&                       cc,
    const nd::OrIntroR&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// ImpliesIntro(conclusion) — NNF(A→B) = NNF(¬A) ∨ NNF(B).
//   Emits Or{principal=f_k_idx}. After: NNF(¬A) at f_k_idx,
//   NNF(B) appended. Returns OnePremise{shadow, premise_pos=end_idx}.
//   (The assumed A is brought into the sequent at f_k_idx as its dual
//   — references to the assumption close against this position.)
util::Result<IntroResult> emit_implies_intro(
    Ctx&                       cc,
    const nd::ImpliesIntro&    op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// IffIntro(ab, ba) — NNF(A↔B) = (NNF(¬A)∨NNF(B)) ∧ (NNF(¬B)∨NNF(A)).
//   Multiplicative ∧R with full-context duplication, then ∨R on each
//   branch's conjunct. Returns TwoPremise (one per direction).
util::Result<IntroResult> emit_iff_intro(
    Ctx&                       cc,
    const nd::IffIntro&        op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// ForallIntro(body) with eigen — ∀R.
//   Emits Forall{principal=f_k_idx, eigen=eigen}. The eigen is the
//   fresh variable index bound by the enclosing Fix; the dispatcher
//   resolves it via the block_tree + trace and passes it explicitly.
//   Returns OnePremise{shadow, premise_pos=f_k_idx}.
util::Result<IntroResult> emit_forall_intro(
    Ctx&                       cc,
    const nd::ForallIntro&     op,
    var_index                  eigen,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// ExistsIntro(body, witness=t) — ∃R with explicit witness.
//   No-witness form (closer of EXISTS_ELIM block) is handled by Phase 4.
//   Emits Exists{principal=f_k_idx, witness=t_lkr}. The witness's LKR
//   TermRef comes from shadow.lkr_term_for[t.idx].
//   Returns OnePremise{shadow, premise_pos=f_k_idx}.
util::Result<IntroResult> emit_exists_intro(
    Ctx&                       cc,
    const nd::ExistsIntro&     op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// ExcludedMiddle(formula_let) — fixed cut-free skeleton.
//   NNF(A ∨ ¬A) = NNF(A) ∨ NNF(¬A). Emit Or{principal=f_k_idx} then
//   emit_close on (f_k_idx, end_idx) — the two are NNF-dual.
//   Returns ZeroPremise.
util::Result<IntroResult> emit_excluded_middle(
    Ctx&                       cc,
    const nd::ExcludedMiddle&  op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

// Peirce(a_let, b_let) — fixed cut-free skeleton for Peirce's law.
//   NNF(((A→B)→A)→A) = ((NNF(¬A)∨NNF(B)) ∧ NNF(¬A)) ∨ NNF(A).
//   Skeleton: Or; Weakening{NNF(A)}; And; on each branch close via
//   the (A, NNF(¬A)) dual. Returns ZeroPremise.
util::Result<IntroResult> emit_peirce(
    Ctx&                       cc,
    const nd::Peirce&          op,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out);

}  // namespace logic::proof::translate::nd_to_lkr::intros
