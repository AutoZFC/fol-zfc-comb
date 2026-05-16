#pragma once

// Proof — the system-tagged value submitted to a Verifier / ProofRunner.
//
// Pulling in the per-system body types gives us complete variant
// alternatives. ND and LKR are instruction-stream programs; Comb is a
// graph-object witness (no instructions to interpret) that nonetheless
// supports the same runner-side claim_name / last_used dispatch contract.

#include "comb/comb_proof.h"
#include "ir.h"
#include "lkr/ops.h"
#include "nd/ops.h"

#include <variant>

namespace logic::proof {

using NDProgram  = Program<nd::Instr>;
using LKRProgram = Program<lkr::Instr>;

struct Proof {
    System system{};
    std::variant<NDProgram, LKRProgram, comb::CombProof> body{};
};

}  // namespace logic::proof
