#include "combining.h"

namespace logic::proof::translate::nd_to_lkr::combining {

util::Result<ImpliesElimSite> emit_implies_elim(
    Ctx&                   /*cc*/,
    const nd::ImpliesElim& op,
    const SequentShadow&   shadow,
    size_t                 target_pos)
{
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_implies_elim: target_pos out of range";
    }
    return ImpliesElimSite{op.impl, op.ant, target_pos};
}

util::Result<OrElimSite> emit_or_elim(
    Ctx&                 /*cc*/,
    const nd::OrElim&    op,
    const SequentShadow& shadow,
    size_t               target_pos)
{
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_or_elim: target_pos out of range";
    }
    return OrElimSite{op.or_formula, op.ac, op.bc, target_pos};
}

util::Result<ExistsElimSite> emit_exists_elim(
    Ctx&                    /*cc*/,
    const nd::ExistsElim&   op,
    const SequentShadow&    shadow,
    size_t                  target_pos)
{
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_exists_elim: target_pos out of range";
    }
    return ExistsElimSite{op.formula, target_pos};
}

}  // namespace logic::proof::translate::nd_to_lkr::combining
