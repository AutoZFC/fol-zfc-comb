#pragma once

// Stage 1 Phase 6: apply — end-to-end orchestrator.
//
// Composes the four sub-passes built in Phases 1–5:
//
//     schema_macro                 (Phases 2/3)
//       ↓ no SchemaInst ops; SchemaInst sites replaced by Use(SH(φᵢ))
//       ↓ or Use(SH(closed_φ)) + ForallElim chain
//     compute_transitive_facts     (Phase 1)
//       ↓ vector<SentenceHandle> facts(P), lex-sorted by handle id
//     emit_prelude                 (Phase 4)
//       ↓ Assume(H) + and_elim chain; fact_step_table
//     emit_body_with_remap         (Phase 5)
//       ↓ body ops with Use+Qed dropped; qed_target
//     postlude (ImpliesIntro + Qed) + output gate
//
// On success: returns the wrapped Program proving H → φ (or just φ
// when facts(P) = ∅, the identity case), the wrapped_goal as a
// SentenceHandle (typed), and the lex-sorted facts list. NDVerifier
// has accepted the output before this returns.
//
// On failure: returns an Error whose message names the sub-pass that
// rejected. Stage 1 NEVER returns a "silently-unsound" wrapped proof
// — the output gate's NDVerifier run is the soundness witness.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/theorem_facts.h"
#include "src/util/error.h"

#include <vector>

namespace logic::proof::translate::nd_internalize {

struct ApplyResult {
    // The wrapped ND program. NDVerifier accepts it against
    // wrapped_goal (enforced by the output gate before return).
    Program<nd::Instr>           proof;

    // For facts non-empty: H → φ, where H is the lex-sorted
    // left-associated conjunction of the facts' formulas and φ is the
    // caller-supplied goal. For facts empty: φ itself (identity case).
    SentenceHandle               wrapped_goal;

    // Lex-sorted by SentenceHandle.id() — the canonical facts list
    // that defines H's conjunct order. Same value the caller would
    // register into a downstream TheoremFactsMap entry for this proof.
    std::vector<SentenceHandle>  facts;
};

// Stage 1 entry point.
//
// Preconditions on `input`:
//   - NDVerifier(goal, input, ctx) accepts (caller's responsibility;
//     the output gate's accept-vs-reject is what surfaces translator
//     bugs, not input bugs).
//   - input is iota-free (upstream iota_elim ran).
//   - input is eq-translation-free (no EqSym; upstream
//     pass would translate them; absent today's pipeline because no
//     eq-translation exists, but the boundary check is here).
//   - every theorem T cited via Use(T) has its SentenceHandle in
//     `theorem_facts.map` (topological build order; Bazel `fol_proof`
//     DAG enforces).
//
// On success, the caller typically:
//   - registers ApplyResult.wrapped_goal as the theorem's new claim,
//   - persists ApplyResult.facts into TheoremFactsMap under the
//     theorem's own SentenceHandle (for use by downstream citers),
//   - hands ApplyResult.proof to Stage 2 (cut-minimal NDtoLKR).
util::Result<ApplyResult>
apply(GlobalContext&            ctx,
      const Program<nd::Instr>& input,
      FormulaHandle             goal,
      const TheoremFactsMap&    theorem_facts);

}  // namespace logic::proof::translate::nd_internalize
