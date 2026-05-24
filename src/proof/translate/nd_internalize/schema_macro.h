#pragma once

// Stage 1 schema macro — closed AND open instances.
//
// Walks a Program<nd::Instr> and replaces every SchemaInst(S, σ) op
// with operations whose net effect derives the resolved instance φᵢ at
// the same point in the program. φᵢ is itself a derived formula in
// general — it may contain free Fixed terms referring to outer
// fix-scope vars (open case). Stage 1 splits two cases:
//
//   1. Closed (φᵢ has no free Fixed): register φᵢ as a Sentence,
//      replace SchemaInst with Use(SH(φᵢ)). 1:1 op replacement.
//
//   2. Open (φᵢ has free Fixed terms {Fixed(k₁), …, Fixed(kₘ)},
//      sorted lex):
//
//        closed_φ := ∀v₁. ∀v₂. … ∀vₘ. φᵢ[Fixed(kᵢ) ↦ vᵢ]
//
//      Register closed_φ as a Sentence; the SentenceHandle goes into
//      synthetic_facts (eventually a conjunct of H, which is closed).
//      Replace SchemaInst with:
//
//        Use(SH(closed_φ))                  ⊢ closed_φ
//        ForallElim(use, Fixed(k₁))         ⊢ ∀v₂…vₘ. φᵢ[Fixed(k₁), Fixed(kᵢ)↦vᵢ, i≥2]
//        ForallElim(prev, Fixed(k₂))
//        …
//        ForallElim(prev, Fixed(kₘ))        ⊢ φᵢ
//
//      (m+1 ops replacing one SchemaInst.) Per Stage 1 v1 spec §4,
//      Q1b option α — universal closure preserves completeness on
//      scope-dependent SchemaInst inputs.
//
// Step-index threading: open-case replacement is not 1:1, so a
// step_remap is maintained during the walk and applied to every
// non-SchemaInst op's StepRef / TermRef args. prog.step_index entries
// are remapped to point at the corresponding output positions.
//
// Scope tracking: schema_macro mirrors the verifier's builder
// enter_scope / exit_scope behavior for Fix and ExistsElim (open
// scopes) and ForallIntro / ExistsIntro-without-witness (close
// scopes). This keeps var_index allocation in sync with the verifier
// and lets ForallElim's TermRef point at the correct binding op's
// instr index in the output (fix_index_by_var lookup).
//
// Soundness obligation per fact: each SentenceHandle in
// synthetic_facts is a true instance (or its universal closure over
// outer-scope vars, which is still a true sentence) of a proven
// schema — the schema's universal quantification justifies it.
// Downstream Stage 1 wraps these as antecedents of H, soundly.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <vector>

namespace logic::proof::translate::nd_internalize {

struct SchemaMacroResult {
    // Program with every SchemaInst replaced (1:1 in the closed case,
    // 1:(m+1) in the open case where m = |free_fixed|).
    Program<nd::Instr>          proof;

    // SentenceHandles of newly-registered facts. For closed instances
    // this is φᵢ; for open instances this is closed_φ (the universal
    // closure over the free Fixed vars). Each distinct fact appears
    // once (SentenceRegistry interns by structure).
    std::vector<SentenceHandle> synthetic_facts;
};

util::Result<SchemaMacroResult>
schema_macro(GlobalContext& ctx, const Program<nd::Instr>& prog);

}  // namespace logic::proof::translate::nd_internalize
