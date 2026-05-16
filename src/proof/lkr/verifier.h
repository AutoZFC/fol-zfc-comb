#pragma once

// LKRVerifier — Hughes' one-sided multi-conclusion classical sequent calculus.
//
// Interprets an LKRProgram as a sequence of operations against an
// open-goals stack. Initial state: open_goals = [[NNF(goal_formula)]].
// Success: program terminates with open_goals empty.
//
// Each verify() call constructs its own private Session; no state spans
// invocations. Eigenvariable freshness is checked locally at the point
// of introduction (Forall).

#include "src/proof/proof.h"
#include "src/proof/verifier.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <string>
#include <unordered_set>

namespace logic::proof::lkr {

class LKRVerifier final : public Verifier {
public:
    System system() const override { return System::LKR; }

    util::ResultStatus verify(
        GlobalContext& ctx,
        FormulaHandle  goal_formula,
        const Proof&   proof) override;

    const std::unordered_set<std::string>& last_used_names() const override {
        return last_used_;
    }

private:
    std::unordered_set<std::string> last_used_;
};

}  // namespace logic::proof::lkr
