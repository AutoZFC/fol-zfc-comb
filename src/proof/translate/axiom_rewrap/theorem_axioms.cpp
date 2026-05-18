#include "src/proof/translate/axiom_rewrap/theorem_axioms.h"

#include <algorithm>
#include <set>
#include <variant>

namespace logic::proof::translate::axiom_rewrap {

util::Result<std::vector<std::string>> compute_transitive_axioms(
    const Program<nd::Instr>& prog,
    const GlobalContext& ctx,
    const TheoremAxiomMap& theorem_axioms)
{
    std::set<std::string> closure;
    std::set<std::string> cited_theorems;

    for (const auto& instr : prog.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            const std::string& name = u->axiom.name;
            if (ctx.find_axiom(name).has_value()) {
                closure.insert(name);
            } else if (ctx.find_theorem(name).has_value()) {
                cited_theorems.insert(name);
            } else {
                return MAKE_ERROR
                    << "compute_transitive_axioms: Use('" << name
                    << "') resolves to neither an axiom nor a theorem in ctx";
            }
        } else if (std::holds_alternative<nd::SchemaInst>(instr)) {
            return MAKE_ERROR
                << "compute_transitive_axioms: SchemaInst is out of Phase 1 "
                   "scope (see AXIOM_REWRAP_DESIGN.md §1)";
        }
    }

    for (const auto& t : cited_theorems) {
        if (!theorem_axioms.contains(t)) {
            return MAKE_ERROR
                << "compute_transitive_axioms: theorem '" << t
                << "' cited but not in TheoremAxiomMap "
                   "(build-order bug — theorem must be translated before "
                   "it is cited)";
        }
        for (const auto& a : theorem_axioms.get(t)) {
            closure.insert(a);
        }
    }

    std::vector<std::string> result(closure.begin(), closure.end());
    std::sort(result.begin(), result.end());
    return result;
}

}  // namespace logic::proof::translate::axiom_rewrap
