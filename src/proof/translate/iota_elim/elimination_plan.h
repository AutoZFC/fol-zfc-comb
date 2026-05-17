#pragma once

// EliminationPlan — per-site scope-close planning for the iota-
// elimination rewrite.
//
// For each iota_elim site discovered by IotaInventory, the plan computes
// the enclosing block-closer instruction index — the position just before
// which the new exists_elim scope must close (in stack-LIFO order with
// respect to other scopes opened later).
//
// "Block-closer" means:
//   - The forall_intro / implies_intro / not_intro / scope-closing
//     exists_intro that closes the deepest scope opened *before* the
//     iota_elim and still open at it.
//   - If no scope is open at iota_elim's position, the program's qed
//     instruction.
//
// The plan does NOT inspect formulas. The rewrite is purely structural;
// formula-level soundness is enforced downstream by NDVerifierGate.

#include "iota_inventory.h"

#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstdint>
#include <vector>

namespace logic::proof::translate::iota_elim {

class EliminationPlan {
public:
    struct Action {
        uint32_t iota_idx;          // Index of iota_elim in old program.
        uint32_t scope_close_idx;   // Index of the block-closer (or qed)
                                    // immediately before which the new
                                    // exists_intro scope-closer must be
                                    // inserted.
    };

    static util::Result<EliminationPlan> compute(
        const IotaInventory& inv,
        const Program<nd::Instr>& prog);

    const std::vector<Action>& actions() const { return actions_; }

private:
    std::vector<Action> actions_;
};

}  // namespace logic::proof::translate::iota_elim
