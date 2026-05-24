#pragma once

// TheoremFactsMap + compute_transitive_facts.
//
// Shared component (not tied to one pass): the typed-handle replacement
// of the old axiom_rewrap::TheoremFactsMap. Consumed by Stage 1
// (nd_internalize) and by any future pass that needs the transitive
// citation closure of a theorem's facts.
//
// A "fact" is a SentenceHandle the proof depends on — see Stage 1 spec
// §3. For a program P, facts(P) is the union of:
//   1. direct_facts(P) = { Use(F).axiom.sentence : Use(F) ∈ P }
//   2. ⋃_{T ∈ theorems_cited_in(P)} facts(T)
// where facts(T) is recovered from the TheoremFactsMap (built
// incrementally in topological order as theorems are translated).
//
// The result is lex-sorted by SentenceHandle.id() for a deterministic
// canonical order (consumed downstream as the conjunct order in H).
//
// Schema handling: SchemaInst ops in P are an input-gate error here.
// Stage 1's schema macro runs upstream of this closure call and
// converts every SchemaInst into a synthetic-instance Use, so by the
// time compute_transitive_facts sees P, no SchemaInst remains.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <unordered_map>
#include <vector>

namespace logic::proof::translate {

// SentenceHandle → its transitive facts closure.
//
// Populated by the build runner: after Stage 1 wraps theorem T, the
// runner calls `put(SH(T), facts(T))` so that subsequent translations
// citing T can pull in T's transitive dependencies via `get`. The
// build's topological order (Bazel `fol_proof` DAG) guarantees every
// cited theorem is registered before any of its citers translates.
struct TheoremFactsMap {
    std::unordered_map<SentenceHandle,
                       std::vector<SentenceHandle>,
                       SentenceHandleHash> map;

    bool contains(SentenceHandle h) const {
        return map.count(h) > 0;
    }

    const std::vector<SentenceHandle>& get(SentenceHandle h) const {
        return map.at(h);
    }

    void put(SentenceHandle h, std::vector<SentenceHandle> facts) {
        map[h] = std::move(facts);
    }
};

// Compute facts(P) = direct_facts(P) ∪ ⋃_T facts(T) where T ranges
// over Use-cited theorems in P.
//
// Determinism: handles are collected into a set (dedup), then sorted by
// SentenceHandle.id(). Two builds over equivalent input produce
// identical output.
//
// Errors (input-gate):
//   - SchemaInst present in P  → "schema macro must run upstream"
//   - Use(F) where ctx classifies F as a theorem AND `known` lacks F's
//     handle  → "cited theorem missing from TheoremFactsMap"
//     (build-order bug; theorem was cited before its own translation).
//
// Axioms and theorems are not distinguished in the output (both
// contribute a SentenceHandle to facts(P)). The axiom-vs-theorem
// distinction matters only to the closure step: theorems pull in their
// transitive facts via `known.get(T)`; axioms do not.
util::Result<std::vector<SentenceHandle>>
compute_transitive_facts(const Program<nd::Instr>& prog,
                         const GlobalContext& ctx,
                         const TheoremFactsMap& known);

}  // namespace logic::proof::translate
