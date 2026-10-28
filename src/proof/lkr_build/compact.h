#pragma once

// Compact LKR: LKR ops plus Identity (COMPACT_LKR_DESIGN.md §2).

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"

#include <cstddef>
#include <variant>

namespace logic::proof::lkr_build {

// Expands to X on entries a, b; its k-th Forall takes first_eigen + k.
struct Identity {
    OpHeader  h{};
    size_t    a{0};
    size_t    b{0};
    var_index first_eigen{0};
};

using CompactInstr = std::variant<lkr::Instr, Identity>;

}  // namespace logic::proof::lkr_build
