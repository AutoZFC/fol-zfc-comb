#include "src/proof/translate/theorem_facts.h"

#include <algorithm>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate {

namespace {

// Compare by registry-assigned id; matches the underlying Handle's
// hash/equality semantics and gives a stable lex order across runs of
// the same build (the build re-registers in deterministic order).
struct HandleIdLess {
    bool operator()(SentenceHandle a, SentenceHandle b) const {
        return a.hash_value() < b.hash_value();
    }
};

}  // namespace

util::Result<std::vector<SentenceHandle>>
compute_transitive_facts(const Program<nd::Instr>& prog,
                         const GlobalContext& ctx,
                         const TheoremFactsMap& known)
{
    std::unordered_set<SentenceHandle, SentenceHandleHash> closure;
    std::vector<SentenceHandle> cited_theorems;

    for (const auto& instr : prog.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            SentenceHandle sh = u->axiom.sentence;
            // First-seen wins; closure dedups.
            auto [_, fresh] = closure.insert(sh);

            // Classify: theorem → schedule its facts for inclusion.
            // The classification uses the handle's registered name (when
            // available) to consult ctx — Stage 1's source-name field on
            // Use lets us prefer the user-cited name, but here we just
            // need to know whether it's a theorem. Reverse-lookup once.
            if (auto name = ctx.name_of(sh); name.has_value()) {
                if (ctx.find_theorem(*name).has_value() && fresh) {
                    cited_theorems.push_back(sh);
                }
            }
            // Translator-synthesized Use ops (no registered name) cannot
            // be theorems-with-citation-closure — they bypass the
            // TheoremFactsMap path.
            continue;
        }
        if (std::holds_alternative<nd::SchemaInst>(instr)) {
            return MAKE_ERROR
                << "compute_transitive_facts: SchemaInst present; Stage 1's "
                   "schema macro must run upstream of the facts closure";
        }
    }

    // Pull in each cited theorem's transitive facts.
    for (SentenceHandle t : cited_theorems) {
        if (!known.contains(t)) {
            return MAKE_ERROR
                << "compute_transitive_facts: cited theorem missing from "
                   "TheoremFactsMap (build-order bug — theorem must be "
                   "translated before any of its citers)";
        }
        for (SentenceHandle f : known.get(t)) {
            closure.insert(f);
        }
    }

    std::vector<SentenceHandle> result(closure.begin(), closure.end());
    std::sort(result.begin(), result.end(), HandleIdLess{});
    return result;
}

}  // namespace logic::proof::translate
