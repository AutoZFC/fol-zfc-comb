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
#include <vector>

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

    // Trace-execute an ND program against ctx, returning the verifier-derived
    // formula for each instruction in program order. The result vector has
    // size == prog.instrs.size(); entries for instructions that don't bind a
    // step (Fix, scope closers, Qed) are invalid FormulaHandle{}.
    //
    // No goal-match is performed (caller passes goal_formula via verify if
    // they want that). Schema parsing context is set up the same way as in
    // verify(). The pass is read-only on ctx — it does not register
    // theorems.
    //
    // Used by the iota-elimination translator (see
    // src/proof/translate/iota_elim/) to know F_k for each step before
    // synthesising T(F_k).
    util::Result<std::vector<FormulaHandle>> trace_formulas(
        GlobalContext&    ctx,
        const NDProgram&  prog);

private:
    std::unordered_set<std::string> last_used_;
};

}  // namespace logic::proof::nd
