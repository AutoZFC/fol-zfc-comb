#pragma once

// Stage 1 schema macro (Phase 2 / closed-instance only).
//
// Walks a Program<nd::Instr> and replaces every SchemaInst(S, σ) op
// with Use(SH(φᵢ)) where φᵢ = instantiate_schema(S.body, σ_resolved)
// is the concrete instance formula, registered as a Sentence in ctx
// (returning a typed SentenceHandle). The Use op's AxiomRef carries
// that SentenceHandle as identity.
//
// "Closed" means φᵢ contains no free Fixed term — i.e., the SchemaInst's
// bindings do not reference any outer `fix x` scope. Phase 2 handles
// only this case; SchemaInst with open instances is rejected here and
// will be handled in Phase 3 by universal-closure + ForallElim chain
// re-instantiation (per Stage 1 v1 spec §4, Q1b/α).
//
// Step-index preservation: the SchemaInst → Use replacement is 1:1
// at the same instr index, so StepRef references elsewhere in the
// program need no remapping.
//
// Dedup: two SchemaInst ops whose resolved φᵢ are structurally equal
// produce the same SentenceHandle (the FormulaRegistry interns by
// structure, and add_sentence interns by formula). Both Use ops point
// to the same handle; synthetic_facts records it only once.
//
// Soundness obligation handed to the caller: every SentenceHandle in
// synthetic_facts is a true instance of a proven schema (Stage 1's
// input gate ensures NDVerifier accepts the input, which entails the
// schemas are proven). Downstream wrapping puts these into H as true
// antecedents.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <vector>

namespace logic::proof::translate::nd_internalize {

struct SchemaMacroResult {
    // Program with every SchemaInst replaced by Use(SH(φᵢ)). All other
    // ops are copied verbatim. Step indices match the input 1:1.
    Program<nd::Instr>          proof;

    // SentenceHandles of newly-registered synthetic instance facts,
    // each distinct. Order is first-encounter (walk order); the caller
    // (compute_transitive_facts via the Use ops) is responsible for any
    // canonical sort.
    std::vector<SentenceHandle> synthetic_facts;
};

// Eliminate SchemaInst ops from `prog` via Phase 2 / closed-instance
// replacement.
//
// Errors:
//   - SchemaInst whose binding resolution fails against an empty
//     name_table (the binding references an outer fix-var, making the
//     instance scope-dependent → Phase 3 / universal-closure territory)
//   - SchemaInst whose resolved φᵢ contains a free Fixed term
//     (same scope-dependence story, caught via post-resolve check)
//   - Any error surfaced by the shared resolve_and_instantiate_schema
//     (unknown schema, unproven schema, missing/duplicate binding, etc.)
util::Result<SchemaMacroResult>
schema_macro(GlobalContext& ctx, const Program<nd::Instr>& prog);

}  // namespace logic::proof::translate::nd_internalize
