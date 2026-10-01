#pragma once

// ProofRunner — the dispatcher that maps a tagged Proof to the correct
// per-system Verifier and is the single audit point for theorem
// registration.
//
// Soundness role:
//   * Resolves claim_name -> SentenceHandle / SchemaDefinition::body
//     exactly once, before invoking any verifier. The verifier receives a
//     pre-resolved FormulaHandle goal and cannot register a theorem under
//     a name it didn't itself resolve.
//   * On a successful verify, registers the new theorem against the same
//     SentenceHandle the dispatcher resolved. Verifiers must not (and the
//     base class contract forbids them to) call ctx.add_theorem directly.
//   * Marks a schema proven (mark_schema_proven) only after its proof
//     checks. It used to mark it first, whatever the outcome, so a failed
//     proof — or one citing the schema itself — left the schema citable.
//
// Threading: a ProofRunner is single-threaded with respect to its
// GlobalContext (concurrent verify() invocations would race on the
// registry). Each verify() call produces a fresh per-call private state
// inside the verifier (its Session); no state persists between calls
// beyond the verifier's own last_used_names() cache.

#include "ir.h"
#include "proof.h"
#include "verifier.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <array>
#include <memory>
#include <string>
#include <unordered_set>

namespace logic::proof {

class ProofRunner {
public:
    explicit ProofRunner(GlobalContext& ctx);

    // Install / replace the verifier for a system. Used by the constructor
    // (which installs ND by default) and by Phase 5 to plug in LKR.
    void register_verifier(std::unique_ptr<Verifier> v);

    // True iff a verifier is registered for the given system.
    bool has_verifier(System s) const {
        return verifiers_[static_cast<size_t>(s)] != nullptr;
    }

    // Verify the proof. Resolves the claim_name carried inside the
    // Program, dispatches to the matching verifier, and on success
    // registers the theorem.
    //
    // Returns Ok on success; on failure, the error message includes the
    // claim_name and the verifier's diagnostic.
    util::ResultStatus verify(const Proof& proof);

    // Names referenced by the most recent successful verify(). Empty if
    // the most recent verify failed or was never invoked.
    const std::unordered_set<std::string>& last_used_names() const {
        return last_used_;
    }

    GlobalContext& context() { return ctx_; }
    const GlobalContext& context() const { return ctx_; }

private:
    GlobalContext&                                          ctx_;
    std::array<std::unique_ptr<Verifier>, kNumSystems>      verifiers_{};
    std::unordered_set<std::string>                         last_used_{};
};

}  // namespace logic::proof
