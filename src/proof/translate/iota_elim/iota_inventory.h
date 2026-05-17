#pragma once

// IotaInventory — analysis pass that lists every iota_elim site in an ND
// program. Pure and structural: takes a Program<nd::Instr>, returns a
// vector of instruction indices where iota_elim appears.
//
// Per Path D, axioms/claims/assume/let formulas are ι-free at this point,
// so iota_elim instructions are the only remaining source of ι in the
// program. Each iota_elim binding will be rewritten to an exists_elim by
// the ProofRewriter.

#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"

#include <cstdint>
#include <vector>

namespace logic::proof::translate::iota_elim {

class IotaInventory {
public:
    // Walk `prog` and collect every instruction index whose op is IotaElim.
    // Order matches program order.
    static IotaInventory build(const Program<nd::Instr>& prog);

    const std::vector<uint32_t>& sites() const { return sites_; }
    bool empty() const { return sites_.empty(); }

private:
    std::vector<uint32_t> sites_;
};

}  // namespace logic::proof::translate::iota_elim
