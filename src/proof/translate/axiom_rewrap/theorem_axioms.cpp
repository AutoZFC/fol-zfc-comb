#include "src/proof/translate/axiom_rewrap/theorem_axioms.h"

#include <algorithm>
#include <set>
#include <variant>

namespace logic::proof::translate::axiom_rewrap {

util::Result<std::vector<std::string>> compute_transitive_facts(
    const Program<nd::Instr>& prog,
    const GlobalContext& ctx,
    const TheoremFactsMap& theorem_facts)
{
    std::set<std::string> closure;
    std::set<std::string> cited_theorems;

    for (const auto& instr : prog.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            // Prefer the op's source-cited name (the user-written cite)
            // for closure keying — disambiguates aliasing where two names
            // share a SentenceHandle (e.g. theorem and axiom with the
            // same body, which the registry interns to one handle). Fall
            // back to the SentenceHandle's first-registered name only
            // when the op is translator-synthesized without a source cite.
            std::string name;
            if (!u->source_name.empty()) {
                name = u->source_name;
            } else if (auto opt = ctx.name_of(u->axiom.sentence); opt.has_value()) {
                name = *opt;
            } else {
                return MAKE_ERROR
                    << "compute_transitive_facts: Use has no source_name "
                       "and its SentenceHandle has no registered name in "
                       "ctx (translator-synthesized Use without registry "
                       "entry?)";
            }
            if (ctx.find_axiom(name).has_value()) {
                closure.insert(name);
            } else if (ctx.find_theorem(name).has_value()) {
                // Theorem T is itself a fact (its formula goes into H_P);
                // we also pull in T's transitive facts so H_P is closed
                // under dependency.
                closure.insert(name);
                cited_theorems.insert(name);
            } else {
                return MAKE_ERROR
                    << "compute_transitive_facts: Use('" << name
                    << "') resolves to neither an axiom nor a theorem in ctx";
            }
        } else if (std::holds_alternative<nd::SchemaInst>(instr)) {
            return MAKE_ERROR
                << "compute_transitive_facts: SchemaInst should have been "
                   "eliminated by the upstream schema_elim pass "
                   "(see AXIOM_REWRAP_DESIGN.md §2.4)";
        }
    }

    for (const auto& t : cited_theorems) {
        if (!theorem_facts.contains(t)) {
            return MAKE_ERROR
                << "compute_transitive_facts: theorem '" << t
                << "' cited but not in TheoremFactsMap "
                   "(build-order bug — theorem must be rewrapped before "
                   "it is cited)";
        }
        for (const auto& f : theorem_facts.get(t)) {
            closure.insert(f);
        }
    }

    std::vector<std::string> result(closure.begin(), closure.end());
    std::sort(result.begin(), result.end());
    return result;
}

}  // namespace logic::proof::translate::axiom_rewrap
