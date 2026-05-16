#pragma once

// Shared schema-instantiation resolver used by every consumer of
// SchemaInstData (the LKR verifier, the ND→LKR translator, future passes).
//
// SchemaInstData carries a SchemaRef and a list of SchemaBindings (each
// with a string var name and a deferred AST). To turn it into a
// FormulaHandle, every consumer must:
//   1. Look up the schema in GlobalContext.
//   2. Refuse if the schema is not yet proven.
//   3. Map each binding's var_name to the schema's positional index.
//   4. Reject duplicate bindings, missing bindings, unsupported arity.
//   5. Parse each binding's formula AST against the consumer's name table.
//   6. Call FormulaBuilder::instantiate_schema on the schema body.
//
// This helper centralizes that recipe. Returns the raw (non-NNF)
// instantiated formula; consumers that need the NNF form apply it
// themselves.
//
// Soundness: the helper only reads from GlobalContext (via find_schema /
// is_schema_proven) and uses the supplied FormulaBuilder for parsing and
// instantiation. It does not mutate ctx, register theorems, or construct
// LKR/ND-specific state.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/util/error.h"
#include "ir.h"

#include <string>
#include <unordered_map>

namespace logic::proof {

// Resolve a SchemaInstData payload to the concrete instantiated formula
// (raw, pre-NNF). On any validation failure returns a Result error with
// op_name as the diagnostic prefix.
//
// name_table: external scope-name → Term map for parsing each binding's
// AST. Pass an empty map for self-contained schema bindings (the typical
// case — ZFC schemas like Replacement and Separation use closed bindings).
util::Result<FormulaHandle> resolve_and_instantiate_schema(
    GlobalContext& ctx,
    FormulaBuilder& builder,
    const SchemaInstData& data,
    const std::unordered_map<std::string, Term>& name_table,
    const char* op_name);

}  // namespace logic::proof
