#include "input_gate.h"

#include "src/proof/nd/verifier.h"

#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

util::ResultStatus check_iota_free(const Program<nd::Instr>& prog) {
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::IotaElim>(prog.instrs[i])) {
            return MAKE_ERROR
                << "NDtoLKR InputGate: I-1 violation — nd::IotaElim at "
                << "instr #" << i << ". The translator requires iota-free "
                << "input; run EliminateIotaInProof first.";
        }
    }
    return util::Ok();
}

util::ResultStatus check_eq_subst_free(const Program<nd::Instr>& prog) {
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::EqSubst>(prog.instrs[i])) {
            return MAKE_ERROR
                << "NDtoLKR InputGate: I-2 violation — nd::EqSubst at "
                << "instr #" << i << ". eq_subst is deprecated; see "
                << "src/proof/translate/EQ_SUBST_DEPRECATION.md.";
        }
        if (std::holds_alternative<nd::EqSym>(prog.instrs[i])) {
            return MAKE_ERROR
                << "NDtoLKR InputGate: I-2 violation — nd::EqSym at "
                << "instr #" << i << ". eq_sym is deprecated; see "
                << "src/proof/translate/EQ_SUBST_DEPRECATION.md.";
        }
    }
    return util::Ok();
}

util::ResultStatus check_nd_verifies(
    GlobalContext&            ctx,
    FormulaHandle             goal_formula,
    const Program<nd::Instr>& prog)
{
    nd::NDVerifier verifier;
    Proof p{System::ND, prog};
    auto status = verifier.verify(ctx, goal_formula, p);
    if (!status.ok()) {
        return MAKE_ERROR
            << "NDtoLKR InputGate: I-3 violation — input does not ND-verify: "
            << status.error().to_string();
    }
    return util::Ok();
}

}  // namespace

util::ResultStatus InputGate::verify(
    GlobalContext&            ctx,
    FormulaHandle             goal_formula,
    const Program<nd::Instr>& prog)
{
    TRY(check_iota_free(prog));
    TRY(check_eq_subst_free(prog));
    TRY(check_nd_verifies(ctx, goal_formula, prog));
    return util::Ok();
}

}  // namespace logic::proof::translate::nd_to_lkr
