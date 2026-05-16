#pragma once

// NDVerifier — Phase 3.
//
// Drives ClassicalProofStack against an NDProgram. Per-call private state
// (Session) holds the proof stack, the SSA env (instr-index keyed), the
// scope-name table for resolving deferred ASTs, and the used-names set for
// dependency tracking. No state persists between verify() invocations.

#include "src/proof/proof.h"
#include "src/proof/verifier.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <string>
#include <unordered_set>

namespace logic::proof::nd {

class NDVerifier final : public Verifier {
public:
    System system() const override { return System::ND; }

    util::ResultStatus verify(
        GlobalContext& ctx,
        FormulaHandle  goal_formula,
        const Proof&   proof) override;

    // Names of axioms/theorems/schemas consulted in the most recent
    // verify() call. Cleared at the start of each verify().
    const std::unordered_set<std::string>& last_used_names() const override { return last_used_; }

private:
    std::unordered_set<std::string> last_used_;
};

}  // namespace logic::proof::nd
