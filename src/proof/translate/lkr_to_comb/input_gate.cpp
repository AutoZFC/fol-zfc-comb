#include "input_gate.h"

#include "src/proof/lkr/verifier.h"

namespace logic::proof::translate::lkr_to_comb {

util::ResultStatus InputGate::verify(
    GlobalContext&             ctx,
    FormulaHandle              goal_formula,
    const Program<lkr::Instr>& prog)
{
    lkr::LKRVerifier verifier;
    Proof p{System::LKR, prog};
    auto status = verifier.verify(ctx, goal_formula, p);
    if (!status.ok()) {
        return MAKE_ERROR
            << "LKRtoComb InputGate: I-1 violation — input does not "
            << "LKR-verify: " << status.error().to_string();
    }
    return util::Ok();
}

}  // namespace logic::proof::translate::lkr_to_comb
