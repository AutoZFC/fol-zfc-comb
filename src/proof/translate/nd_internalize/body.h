#pragma once

// Stage 1 Phase 5: emit_body_with_remap.
//
// Takes the schema-macroed body (`schema_macro` output: no SchemaInst,
// possibly Use ops citing axiom/theorem/synthetic-instance SHs) plus
// the prelude's fact_step_table and prelude_length, and emits the body
// ops that follow the prelude in the final wrapped program.
//
// Per Stage 1 v1 spec §6/§7. The body emitter does three things:
//
//   1. DROP every `Use(F)` op. Its result-step gets aliased to
//      `fact_step_table[F.axiom.sentence]` — the prelude's extracted
//      h_F step. Any downstream op that referenced this Use's StepRef
//      now references the prelude extract directly.
//
//   2. DROP the body's `Qed` op. Stage 1's outer wrap emits a new
//      `ImpliesIntro + Qed` postlude; the original Qed's `derived`
//      step (remapped) is returned as `qed_target` so the caller knows
//      what the ImpliesIntro should discharge.
//
//   3. COPY every other op with its StepRef / TermRef args remapped:
//      - args pointing at a dropped Use → prelude extract index
//      - args pointing at another body op → its absolute output
//        index = `prelude_length` + body-local index
//
// Input contract (input gate):
//   - body has no SchemaInst ops (rejected here; Stage 1's schema
//     macro runs upstream)
//   - body has exactly one Qed op
//   - every `Use(F)` cites a SentenceHandle present in
//     fact_step_table (caller's responsibility: compute_transitive_facts
//     and emit_prelude must be fed the same facts list)
//
// Output contract:
//   - instrs has no Use ops, no Qed op, no SchemaInst ops
//   - all StepRef.idx and TermRef.idx in instrs are absolute output
//     positions (prelude indices or prelude_length + body-local)
//   - qed_target.idx is an absolute output position pointing at the
//     formula the original Qed was on
//
// instrs is ready to concat after the prelude. The caller then appends:
//     ImpliesIntro{.conclusion = qed_target}
//     Qed{.derived = StepRef{<index of the just-emitted ImpliesIntro>}}
// to complete the wrapped program.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <unordered_map>
#include <vector>

namespace logic::proof::translate::nd_internalize {

struct BodyEmitResult {
    // Body ops, ready to concat after the prelude. All StepRef and
    // TermRef args carry ABSOLUTE output indices.
    std::vector<nd::Instr> instrs;

    // Absolute output index of the formula derived by the body's
    // original Qed step. The wrap's ImpliesIntro discharges this.
    StepRef qed_target;
};

util::Result<BodyEmitResult>
emit_body_with_remap(
    const Program<nd::Instr>& body,
    const std::unordered_map<SentenceHandle, StepRef, SentenceHandleHash>& table,
    uint32_t prelude_length);

}  // namespace logic::proof::translate::nd_internalize
