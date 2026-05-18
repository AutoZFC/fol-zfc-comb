#pragma once

// TheoremFactsMap + compute_transitive_facts.
//
// Per AXIOM_REWRAP_DESIGN.md §2.3 (revised 2026-05-18): axiom_rewrap
// treats axioms and theorems uniformly as "facts" — both get dropped
// from the body and aliased to extracted Assume(H) prelude steps. The
// wrapped goal H conjoins every cited fact's formula (axiom or
// theorem).
//
// TheoremFactsMap is the registry consulted at rewrap time:
//   name → facts(T) = transitive closure of axiom+theorem dependencies
// for each theorem T. Populated incrementally in build-topological
// order (each theorem's facts are registered after its rewrap runs).
//
// compute_transitive_facts walks a Program<nd::Instr> and returns
// facts(P), the union of direct fact uses and (for each cited theorem
// T) facts(T) ∪ {T itself}. Lex-sorted, deduplicated.
//
// Handles Use(name) only. SchemaInst is rejected as an input-gate
// error: schemas are eliminated by an upstream ND→ND inline pass
// (analogous to iota_elim); see AXIOM_REWRAP_DESIGN.md §2.4.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <string>
#include <unordered_map>
#include <vector>

namespace logic::proof::translate::axiom_rewrap {

struct TheoremFactsMap {
    // theorem name → sorted-lex list of fact names (axioms + theorems)
    // in facts(T).
    std::unordered_map<std::string, std::vector<std::string>> map;

    bool contains(const std::string& theorem_name) const {
        return map.count(theorem_name) > 0;
    }

    const std::vector<std::string>& get(const std::string& theorem_name) const {
        return map.at(theorem_name);
    }

    void put(const std::string& theorem_name, std::vector<std::string> facts) {
        map[theorem_name] = std::move(facts);
    }
};

util::Result<std::vector<std::string>> compute_transitive_facts(
    const Program<nd::Instr>& prog,
    const GlobalContext& ctx,
    const TheoremFactsMap& theorem_facts);

}  // namespace logic::proof::translate::axiom_rewrap
