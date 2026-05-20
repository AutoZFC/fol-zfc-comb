#include "src/proof/translate/lkr_to_comb/comb_build.h"

#include "src/core/formula.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

size_t fograph_vertex_count(FormulaBuilder& /*fb*/, FormulaHandle phi) {
    // G(φ) vertex count = #atoms + #binders in φ. Layout-invariant, so
    // we build the fograph and read its size. (Building is O(|φ|).)
    comb::Fograph g(phi);
    return g.num_vertex();
}

std::vector<size_t> entry_vertex_offsets(
    FormulaBuilder&                   fb,
    const std::vector<FormulaHandle>& entries)
{
    std::vector<size_t> offsets;
    offsets.reserve(entries.size() + 1);
    size_t acc = 0;
    for (const auto& e : entries) {
        offsets.push_back(acc);
        acc += fograph_vertex_count(fb, e);
    }
    offsets.push_back(acc);  // trailing total
    return offsets;
}

comb::Fograph build_sequent_fograph(
    FormulaBuilder&                   fb,
    const std::vector<FormulaHandle>& entries)
{
    // Φ(Γ) = φ1 ∨ (φ2 ∨ … ∨ φn). Right-associated to match Hughes' §11
    // sequent-formula convention. The empty sequent is unprovable and
    // should never reach here; guard with a Bottom (0) so a caller bug
    // surfaces as a verification failure rather than UB.
    if (entries.empty()) {
        return comb::Fograph(fb.make_bottom());
    }
    FormulaHandle phi = entries.back();
    for (size_t i = entries.size() - 1; i-- > 0;) {
        phi = fb.make_or(entries[i], phi);
    }
    return comb::Fograph(phi);
}

}  // namespace logic::proof::translate::lkr_to_comb
