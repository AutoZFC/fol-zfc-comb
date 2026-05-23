#include "schema_resolve.h"

#include <string>
#include <vector>

namespace logic::proof {

util::Result<FormulaHandle> resolve_and_instantiate_schema(
    GlobalContext& ctx,
    FormulaBuilder& builder,
    const SchemaInstData& data,
    const std::unordered_map<std::string, Term>& name_table,
    const char* op_name)
{
    // SchemaRef carries the typed SchemaHandle (lowering already resolved
    // any source-level name). Deref directly; the schema's name is on
    // schema_def.name for diagnostics.
    const SchemaDefinition& schema_def = *data.schema.schema;
    if (!ctx.is_schema_proven(data.schema.schema)) {
        return MAKE_ERROR << op_name << ": schema '"
                          << schema_def.name << "' not yet proven";
    }

    // Schema-var/arity tables for parsing binding bodies. A binding body
    // may reference other schema variables from the same schema (e.g., in
    // an arity-1 lambda body that mentions another schema-var), so we
    // pre-populate these maps from the target schema before parsing each
    // binding. Mirrors the ND verifier's exec_schema_inst path.
    std::unordered_map<std::string, size_t> sv_map, ar_map;
    for (size_t j = 0; j < schema_def.var_names.size(); ++j) {
        sv_map[schema_def.var_names[j]] = j;
        if (j < schema_def.var_arities.size())
            ar_map[schema_def.var_names[j]] = schema_def.var_arities[j];
    }

    std::vector<SchemaBind> binds(schema_def.var_names.size());
    std::vector<bool>       bound(schema_def.var_names.size(), false);

    for (const auto& sb : data.bindings) {
        // Linear lookup of var_name → positional index. Schemas typically
        // have a handful of variables; an unordered_map would be overkill.
        size_t idx = schema_def.var_names.size();
        for (size_t j = 0; j < schema_def.var_names.size(); ++j) {
            if (schema_def.var_names[j] == sb.var_name) { idx = j; break; }
        }
        if (idx >= schema_def.var_names.size()) {
            return MAKE_ERROR << op_name << ": unknown schema variable '"
                              << sb.var_name << "'";
        }
        if (bound[idx]) {
            return MAKE_ERROR << op_name << ": duplicate binding for '"
                              << sb.var_name << "'";
        }
        if (!sb.formula_ast) {
            return MAKE_ERROR << op_name << ": binding for '"
                              << sb.var_name << "' has no formula AST";
        }

        size_t arity = (idx < schema_def.var_arities.size())
                        ? schema_def.var_arities[idx] : 0;

        if (arity == 0) {
            // Closed-formula binding.
            TRY_ASSIGN(body, try_parse_formula_with_vars(
                sb.formula_ast.get(), ctx, builder,
                name_table, sv_map, ar_map));
            binds[idx] = SchemaBind(body);
        } else {
            // Arity-N predicate binding: the lambda body references N
            // fresh fixed-vars (the lambda parameters), one per arg slot.
            // Algorithm mirrors nd::verifier::exec_schema_inst:
            //   1. Resolve parameter names — explicit or auto-generated.
            //   2. Allocate fresh fixed-vars via builder.enter_scope().
            //   3. Parse the body in an extended name table.
            //   4. Restore the scope counter after parsing.
            //   5. Build SchemaBind(param_indices, body); the substitution
            //      path in FormulaBuilder::instantiate_schema replaces each
            //      param-var with the corresponding arg at every SchemaVar
            //      site.
            auto lambda_param_names = sb.lambda_params;
            if (lambda_param_names.empty()) {
                for (size_t a = 0; a < arity; ++a) {
                    lambda_param_names.push_back("_lam" + std::to_string(a));
                }
            }
            if (lambda_param_names.size() != arity) {
                return MAKE_ERROR << op_name << ": schema var '"
                    << sb.var_name << "' expects " << arity
                    << " lambda params, got " << lambda_param_names.size();
            }

            auto lambda_vars = name_table;
            std::vector<var_index> param_indices;
            param_indices.reserve(arity);
            for (const auto& param : lambda_param_names) {
                var_index vi = builder.enter_scope();
                lambda_vars[param] = Term::fixed(vi);
                param_indices.push_back(vi);
            }
            auto body_r = try_parse_formula_with_vars(
                sb.formula_ast.get(), ctx, builder,
                lambda_vars, sv_map, ar_map);
            for (size_t k = 0; k < arity; ++k) builder.exit_scope();
            if (!body_r.ok()) return body_r.error();
            binds[idx] = SchemaBind(std::move(param_indices),
                                    std::move(body_r).unwrap());
        }
        bound[idx] = true;
    }

    for (size_t j = 0; j < bound.size(); ++j) {
        if (!bound[j]) {
            return MAKE_ERROR << op_name << ": missing binding for '"
                              << schema_def.var_names[j] << "'";
        }
    }

    return builder.instantiate_schema(schema_def.body, binds);
}

}  // namespace logic::proof
