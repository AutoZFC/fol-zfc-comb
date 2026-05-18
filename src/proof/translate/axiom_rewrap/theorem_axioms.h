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
// Handles Use(name) only. SchemaInst is rejected as an input-gate error:
// schemas are eliminated by an upstream ND→ND inline pass (analogous to
// iota_elim), so by the time axiom_rewrap runs no SchemaInst should
// remain. See AXIOM_REWRAP_DESIGN.md §2.4.

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

// Wrapped form of each previously-rewrapped theorem.
//
// For theorem T with axioms(T) = {A_1, …, A_k} (k ≥ 1), the wrapped form
// is the FormulaHandle for (A_1 ∧ … ∧ A_k) → φ_T, lex-sorted and
// left-associated to match the canonical H_T shape used by the prelude
// extraction chain (so the unwrap macro's modus ponens type-checks).
//
// For T with axioms(T) = ∅, no entry is needed — the unwrap macro
// degenerates to a plain Use(T) which returns φ_T directly.
//
// Populated by whoever runs AxiomRewrap on T's proof (typically the
// runtime / proof_checker, in build-topological order). Consumed by
// AxiomRewrap when it sees Use(T) in a downstream proof.
struct WrappedTheoremMap {
    std::unordered_map<std::string, FormulaHandle> map;

    bool contains(const std::string& theorem_name) const {
        return map.count(theorem_name) > 0;
    }

    FormulaHandle get(const std::string& theorem_name) const {
        return map.at(theorem_name);
    }

    void put(const std::string& theorem_name, FormulaHandle wrapped) {
        map[theorem_name] = wrapped;
    }
};

util::Result<std::vector<std::string>> compute_transitive_axioms(
    const Program<nd::Instr>& prog,
    const GlobalContext& ctx,
    const TheoremAxiomMap& theorem_axioms);

}  // namespace logic::proof::translate::axiom_rewrap
