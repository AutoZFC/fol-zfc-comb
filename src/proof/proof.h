#pragma once

// Proof — the system-tagged value submitted to a Verifier / ProofRunner.
//
// Pulling in both per-system ops headers gives us complete Instr types,
// so std::variant<NDProgram, LKRProgram> can be instantiated.

#include "ir.h"
#include "lkr/ops.h"
#include "nd/ops.h"

#include <variant>

namespace logic::proof {

using NDProgram  = Program<nd::Instr>;
using LKRProgram = Program<lkr::Instr>;

struct Proof {
    System system{};
    std::variant<NDProgram, LKRProgram> body{};
};

}  // namespace logic::proof
