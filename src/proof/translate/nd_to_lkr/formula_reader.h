#pragma once

// ⟦s⟧σ, the only reader of trace formulas (ELIMINATION_DEMANDS_DESIGN.md
// §1.2): each binder's ND level in scope(s) becomes its LKR term under σ.

#include "proof_index.h"
#include "sequent_shadow.h"

#include "src/core/formula.h"
#include "src/proof/nd/verifier.h"
#include "src/util/error.h"

namespace logic::proof::translate::nd_to_lkr {

class FormulaReader {
public:
    FormulaReader(const ProofIndex& index,
                  const nd::NDVerifier::TraceFull& trace,
                  FormulaBuilder& builder)
        : index_(index), trace_(trace), builder_(builder) {}

    // Fails when s mentions a binder σ does not bind, which I-4 excludes.
    util::Result<FormulaHandle> read(StepRef s, const TermEnv& sigma) const;

    util::Result<FormulaHandle> read_nnf(StepRef s, const TermEnv& sigma) const;

private:
    const ProofIndex&                index_;
    const nd::NDVerifier::TraceFull& trace_;
    FormulaBuilder&                  builder_;
};

}  // namespace logic::proof::translate::nd_to_lkr
