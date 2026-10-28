#pragma once

// E: compact LKR to LKR (COMPACT_LKR_DESIGN.md §2). Untrusted; its output
// must verify.

#include "compact.h"

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/translate/pass.h"
#include "src/util/error.h"

namespace logic::proof::lkr_build {

class ExpandIdentities final
    : public translate::Pass<CompactInstr, lkr::Instr> {
public:
    ExpandIdentities(GlobalContext& ctx, FormulaHandle goal_formula)
        : ctx_(ctx), goal_(goal_formula) {}

    util::Result<Program<lkr::Instr>> apply(
        const Program<CompactInstr>& in) override;

private:
    GlobalContext& ctx_;
    FormulaHandle  goal_;
};

}  // namespace logic::proof::lkr_build
