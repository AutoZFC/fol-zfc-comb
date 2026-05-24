#include "src/proof/translate/nd_internalize/schema_macro.h"

#include "src/proof/schema_resolve.h"

#include <unordered_map>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::nd_internalize {

namespace {

// Structurally walk a FormulaHandle and report whether it contains any
// Fixed-var term. Used for the closed-instance check: φᵢ is closed iff
// no Fixed appears (φᵢ doesn't reference any outer fix scope).
//
// Quantified.body's bound variable is a generalized var (not a Fixed),
// so the recursion through Quantified.body correctly counts only outer
// Fixed refs as "free".
bool has_any_fixed(FormulaHandle h) {
    if (!h.valid()) return false;
    const Formula& f = h.get();
    if (f.is_predicate()) {
        for (const Term& t : f.as_predicate().args()) {
            if (t.is_fixed()) return true;
            if (t.is_description() && has_any_fixed(t.as_description().body))
                return true;
        }
        return false;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid()  && has_any_fixed(c.left))  return true;
        if (c.right.valid() && has_any_fixed(c.right)) return true;
        return false;
    }
    if (f.is_quantified()) {
        return has_any_fixed(f.as_quantified().body);
    }
    if (f.is_schema_var()) {
        // After instantiate_schema, no schema vars should remain in a
        // well-resolved φᵢ. Defensive: treat any survivor's Fixed args
        // as non-closed.
        for (const Term& t : f.as_schema_var().args) {
            if (t.is_fixed()) return true;
            if (t.is_description() && has_any_fixed(t.as_description().body))
                return true;
        }
        return false;
    }
    // Sentence wrapper is by-construction closed.
    return false;
}

}  // namespace

util::Result<SchemaMacroResult>
schema_macro(GlobalContext& ctx, const Program<nd::Instr>& prog)
{
    SchemaMacroResult result;
    result.proof.claim_name = prog.claim_name;
    result.proof.instrs.reserve(prog.instrs.size());
    result.proof.step_index = prog.step_index;

    // Builder for binding resolution. Fresh — Stage 1's scope is depth 0
    // (the prelude introduces no fix ops), so the builder needs no
    // prior scope.
    FormulaBuilder builder(ctx);
    std::unordered_set<SentenceHandle, SentenceHandleHash> seen;

    for (const auto& instr : prog.instrs) {
        const auto* si = std::get_if<nd::SchemaInst>(&instr);
        if (si == nullptr) {
            // Non-SchemaInst ops: copy verbatim. StepRef/TermRef
            // indices unchanged because the SchemaInst→Use replacement
            // preserves position.
            result.proof.instrs.push_back(instr);
            continue;
        }

        // Closed-instance test: try to resolve bindings with an empty
        // name_table. Any binding body that references a source-level
        // outer fix-var fails parse here, signaling Phase 3 territory.
        std::unordered_map<std::string, Term> empty_names;
        auto resolved = resolve_and_instantiate_schema(
            ctx, builder, si->data, empty_names, "schema_macro");
        if (!resolved.ok()) {
            return MAKE_ERROR
                << "schema_macro: SchemaInst with outer-scope-referencing "
                   "bindings (or other resolution error); Phase 3 (universal "
                   "closure) not implemented: "
                << resolved.error().to_string();
        }
        FormulaHandle phi = std::move(resolved).unwrap();
        if (has_any_fixed(phi)) {
            return MAKE_ERROR
                << "schema_macro: SchemaInst's resolved instance has a "
                   "free Fixed term; Phase 3 (universal closure per Q1b/α) "
                   "not implemented";
        }

        // Register the closed instance as a Sentence; SentenceRegistry
        // interns by structure, so equal instances collapse to the
        // same handle automatically.
        SentenceHandle sh = ctx.add_sentence(Sentence(phi));
        if (seen.insert(sh).second) {
            result.synthetic_facts.push_back(sh);
        }

        // Replace SchemaInst with Use(SH(φᵢ)). No source-cited name
        // (translator-synthesized).
        nd::Use use_op{};
        use_op.h     = si->h;             // preserve source location
        use_op.axiom = AxiomRef{sh};
        result.proof.instrs.emplace_back(nd::Instr{std::move(use_op)});
    }

    return result;
}

}  // namespace logic::proof::translate::nd_internalize
