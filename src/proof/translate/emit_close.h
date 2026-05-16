#pragma once

// emit_close — close an LKR goal by structural decomposition of two
// NNF-dual sequent entries. Replaces the old `emit_axiom_decomp`.
//
// Precondition: `pos_entry` and `neg_entry` resolve in `env` to formulas
// (a, b) such that NNF(¬a) = b structurally. Recursion preserves this
// invariant at every call.
//
// Action: emits a sequence of lkr::Instr ops into `out` that, when
// executed by LKRVerifier on the goal `env` represents, closes that
// goal. On exit, the goal has been popped from the verifier stack.
//
// On failure: returns Error with the offending positions and the
// structural mismatch reason. The Env may have been partially mutated;
// the caller must discard it.

#include "src/core/formula.h"
#include "src/util/error.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "env.h"

namespace logic::proof::translate {

util::ResultStatus emit_close(Env&            env,
                              SequentEntry    pos_entry,
                              SequentEntry    neg_entry,
                              EigenSupply&    eigens,
                              FormulaBuilder& builder,
                              Program<lkr::Instr>& out);

}  // namespace logic::proof::translate
