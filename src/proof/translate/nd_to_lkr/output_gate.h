#pragma once

// OutputGate — soundness witness for the ND→LKR translator.
//
// Per ND_TO_LKR_DESIGN.md §5, every Program<lkr::Instr> emitted by the
// translator must be accepted by LKRVerifier against the goal's NNF form.
// The translator itself is not trusted; this gate makes any translator
// bug surface as an Error at the boundary rather than as silent
// unsoundness downstream.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::nd_to_lkr {

class OutputGate {
public:
    // Run LKRVerifier on `prog` against NNF(goal_formula). Returns Ok on
    // acceptance; otherwise an Error wrapping the verifier's diagnostic.
    //
    // The caller is responsible for NNF-normalising goal_formula before
    // submission — typically by passing the same NNF handle that the
    // translator computed when constructing prog. We do not re-normalise
    // here because LKRVerifier internally NNFs at use sites already.
    static util::ResultStatus verify(
        GlobalContext&             ctx,
        FormulaHandle              goal_formula,
        const Program<lkr::Instr>& prog);
};

}  // namespace logic::proof::translate::nd_to_lkr
