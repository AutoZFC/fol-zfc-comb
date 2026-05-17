#include "iota_inventory.h"

#include <variant>

namespace logic::proof::translate::iota_elim {

IotaInventory IotaInventory::build(const Program<nd::Instr>& prog) {
    IotaInventory inv;
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::IotaElim>(prog.instrs[i])) {
            inv.sites_.push_back(i);
        }
    }
    return inv;
}

}  // namespace logic::proof::translate::iota_elim
