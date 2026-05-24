#include "projections.h"

namespace logic::proof::translate::nd_to_lkr::projections {

util::Result<RecurseDescriptor> emit_and_elim_l(
    Ctx&                  /*cc*/,
    const nd::AndElimL&   op,
    const SequentShadow&  shadow,
    size_t                f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_and_elim_l: f_k_idx out of range";
    }
    return RecurseDescriptor{op.of, f_k_idx, Demand{DemandAndLeft{}}};
}

util::Result<RecurseDescriptor> emit_and_elim_r(
    Ctx&                  /*cc*/,
    const nd::AndElimR&   op,
    const SequentShadow&  shadow,
    size_t                f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_and_elim_r: f_k_idx out of range";
    }
    return RecurseDescriptor{op.of, f_k_idx, Demand{DemandAndRight{}}};
}

util::Result<RecurseDescriptor> emit_iff_elim_l(
    Ctx&                  /*cc*/,
    const nd::IffElimL&   op,
    const SequentShadow&  shadow,
    size_t                f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_iff_elim_l: f_k_idx out of range";
    }
    return RecurseDescriptor{op.iff, f_k_idx, Demand{DemandIffLeft{}}};
}

util::Result<RecurseDescriptor> emit_iff_elim_r(
    Ctx&                  /*cc*/,
    const nd::IffElimR&   op,
    const SequentShadow&  shadow,
    size_t                f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_iff_elim_r: f_k_idx out of range";
    }
    return RecurseDescriptor{op.iff, f_k_idx, Demand{DemandIffRight{}}};
}

util::Result<RecurseDescriptor> emit_double_neg_elim(
    Ctx&                      /*cc*/,
    const nd::DoubleNegElim&  op,
    const SequentShadow&      shadow,
    size_t                    f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_double_neg_elim: f_k_idx out of range";
    }
    return RecurseDescriptor{op.of, f_k_idx, Demand{DemandDoubleNeg{}}};
}

util::Result<RecurseDescriptor> emit_forall_elim(
    Ctx&                  /*cc*/,
    const nd::ForallElim& op,
    const SequentShadow&  shadow,
    size_t                f_k_idx)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_forall_elim: f_k_idx out of range";
    }
    // Resolve the ND TermRef to its bound Term via the shadow's
    // lkr_term_for table (populated by Fix / ExistsElim emissions
    // upstream). Failure indicates either the witness's binding step
    // did not run or the dispatcher did not thread the table forward
    // — both translator bugs.
    auto t_it = shadow.lkr_term_for.find(op.term.idx);
    if (t_it == shadow.lkr_term_for.end()) {
        return MAKE_ERROR
            << "emit_forall_elim: ND TermRef #" << op.term.idx
            << " has no LKR binding in shadow";
    }
    return RecurseDescriptor{
        op.formula,
        f_k_idx,
        Demand{DemandInstance{t_it->second.value}}};
}

}  // namespace logic::proof::translate::nd_to_lkr::projections
