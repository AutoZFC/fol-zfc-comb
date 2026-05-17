#include "eliminate_iota.h"

#include "elimination_plan.h"
#include "iota_inventory.h"
#include "nd_verifier_gate.h"
#include "proof_rewriter.h"

#include <variant>

namespace logic::proof::translate::iota_elim {

bool EliminateIotaInProof::program_contains_iota(
    const Program<nd::Instr>& prog)
{
    for (const auto& instr : prog.instrs) {
        if (std::holds_alternative<nd::IotaElim>(instr)) return true;
    }
    return false;
}

util::Result<Program<nd::Instr>> EliminateIotaInProof::apply(
    const Program<nd::Instr>& in)
{
    IotaInventory inv = IotaInventory::build(in);
    if (inv.empty()) return in;

    TRY_ASSIGN(plan, EliminationPlan::compute(inv, in));
    TRY_ASSIGN(out, ProofRewriter::apply(in, plan));
    TRY(NDVerifierGate::verify(ctx_, goal_, out));
    return out;
}

}  // namespace logic::proof::translate::iota_elim
