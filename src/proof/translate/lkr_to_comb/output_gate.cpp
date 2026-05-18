#include "output_gate.h"

#include "src/proof/comb/verifier.h"

namespace logic::proof::translate::lkr_to_comb {

util::ResultStatus OutputGate::verify(
    GlobalContext&         ctx,
    FormulaHandle          augmented_goal_formula,
    const comb::CombProof& cp)
{
    comb::CombVerifier verifier;
    Proof p{System::COMB, cp};
    auto status = verifier.verify(ctx, augmented_goal_formula, p);
    if (!status.ok()) {
        return MAKE_ERROR
            << "LKRtoComb OutputGate: translator emitted a CombProof "
            << "that does not verify (translator bug surfaced at boundary): "
            << status.error().to_string();
    }
    return util::Ok();
}

}  // namespace logic::proof::translate::lkr_to_comb
