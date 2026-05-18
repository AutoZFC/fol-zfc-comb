#pragma once

// TheoremAxiomMap + compute_transitive_axioms.
//
// Phase 1 deliverable for axiom_rewrap (see AXIOM_REWRAP_DESIGN.md §7.1).
//
// TheoremAxiomMap is the registry consulted at rewrap time: name → axioms(T),
// the transitive axiom closure of theorem T's wrapped proof. Populated
// incrementally by the runtime in build-topological order.
//
// compute_transitive_axioms walks a Program<nd::Instr> and returns
// axioms(P) = direct axiom uses ∪ ⋃_{T cited by P} registry[T], lex-sorted
// and deduplicated. Errors if a cited theorem is missing from the registry
// (build-order bug) or if an unresolvable Use name is encountered.
//
// Phase 1 scope: handles Use(name) only. SchemaInst is rejected with a
// clear error (the ZFC corpus uses no schemas; deferred to a later phase).

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <string>
#include <unordered_map>
#include <vector>

namespace logic::proof::translate::axiom_rewrap {

struct TheoremAxiomMap {
    // theorem name → sorted-lex list of axiom names in axioms(T)
    std::unordered_map<std::string, std::vector<std::string>> map;

    bool contains(const std::string& theorem_name) const {
        return map.count(theorem_name) > 0;
    }

    const std::vector<std::string>& get(const std::string& theorem_name) const {
        return map.at(theorem_name);
    }

    void put(const std::string& theorem_name, std::vector<std::string> axioms) {
        map[theorem_name] = std::move(axioms);
    }
};

util::Result<std::vector<std::string>> compute_transitive_axioms(
    const Program<nd::Instr>& prog,
    const GlobalContext& ctx,
    const TheoremAxiomMap& theorem_axioms);

}  // namespace logic::proof::translate::axiom_rewrap
