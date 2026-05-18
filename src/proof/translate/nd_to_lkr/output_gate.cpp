#include "output_gate.h"

#include "src/proof/lkr/verifier.h"

namespace logic::proof::translate::nd_to_lkr {

util::ResultStatus OutputGate::verify(
    GlobalContext&             ctx,
    FormulaHandle              goal_formula,
    const Program<lkr::Instr>& prog)
{
    lkr::LKRVerifier verifier;
    Proof p{System::LKR, prog};
    auto status = verifier.verify(ctx, goal_formula, p);
    if (!status.ok()) {
        return MAKE_ERROR
            << "NDtoLKR OutputGate: translator emitted an LKR program "
            << "that does not verify (translator bug surfaced at boundary): "
            << status.error().to_string();
    }
    return util::Ok();
}

}  // namespace logic::proof::translate::nd_to_lkr
