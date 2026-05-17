#include "nd_verifier_gate.h"

#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"

#include <variant>

namespace logic::proof::translate::iota_elim {

namespace {

util::ResultStatus check_iota_free(const Program<nd::Instr>& prog) {
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::IotaElim>(prog.instrs[i])) {
            return MAKE_ERROR
                << "NDVerifierGate: I-3 violation — iota_elim at instr #"
                << i << " survived the rewrite";
        }
    }
    return util::Ok();
}

util::ResultStatus check_nd_valid(GlobalContext& ctx,
                                   FormulaHandle goal_formula,
                                   const Program<nd::Instr>& prog)
{
    nd::NDVerifier verifier;
    // Construct a Proof shell around the rewritten program. The NDVerifier
    // requires a Proof with the ND tag.
    Proof p{System::ND, prog};
    auto status = verifier.verify(ctx, goal_formula, p);
    if (!status.ok()) {
        return MAKE_ERROR
            << "NDVerifierGate: I-4 violation — rewritten program fails "
            << "ND verification: " << status.error().to_string();
    }
    return util::Ok();
}

}  // namespace

util::ResultStatus NDVerifierGate::verify(
    GlobalContext&            ctx,
    FormulaHandle             goal_formula,
    const Program<nd::Instr>& rewritten)
{
    auto i3 = check_iota_free(rewritten);
    if (!i3.ok()) return i3;
    return check_nd_valid(ctx, goal_formula, rewritten);
}

}  // namespace logic::proof::translate::iota_elim
