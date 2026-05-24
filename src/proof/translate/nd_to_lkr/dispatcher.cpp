#include "dispatcher.h"

#include "intros.h"
#include "projections.h"

#include <sstream>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr::dispatcher {

namespace {

// Forward — used by handle_intro_result.
util::ResultStatus translate_step_impl(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out);

intros::Ctx make_intros_ctx(Ctx& dcc) {
    return intros::Ctx{dcc.ctx, dcc.builder, dcc.prog, dcc.trace};
}

projections::Ctx make_projections_ctx(Ctx& dcc) {
    return projections::Ctx{dcc.ctx, dcc.builder, dcc.prog, dcc.trace};
}

// DemandDoubleNeg is a no-op at the NNF level — NNF(¬¬A) = A. The
// dispatcher normalizes it to DemandNone before passing to Phase 1.
Demand normalize_demand(const Demand& d) {
    if (std::holds_alternative<DemandDoubleNeg>(d)) {
        return Demand{DemandNone{}};
    }
    return d;
}

util::ResultStatus handle_intro_result(
    Ctx&                     dcc,
    intros::IntroResult      result,
    std::vector<lkr::Instr>& out)
{
    if (std::holds_alternative<intros::ZeroPremise>(result)) {
        return util::Ok();
    }
    if (auto* one = std::get_if<intros::OnePremise>(&result)) {
        return translate_step_impl(
            dcc, std::move(one->shadow), one->premise_step,
            one->premise_pos, Demand{DemandNone{}}, out);
    }
    if (auto* two = std::get_if<intros::TwoPremise>(&result)) {
        // LKR's And/Cut push LEFT on top — recurse on LEFT first so
        // its emitted ops follow the branching op in the linear stream.
        TRY(translate_step_impl(
            dcc, std::move(two->left_shadow), two->left_step,
            two->left_pos, Demand{DemandNone{}}, out));
        return translate_step_impl(
            dcc, std::move(two->right_shadow), two->right_step,
            two->right_pos, Demand{DemandNone{}}, out);
    }
    return MAKE_ERROR << "handle_intro_result: unexpected IntroResult variant";
}

util::ResultStatus translate_step_impl(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out)
{
    if (step.idx >= dcc.prog.instrs.size()) {
        return MAKE_ERROR
            << "translate_step: step #" << step.idx
            << " out of range (program size " << dcc.prog.instrs.size() << ")";
    }
    const auto& instr = dcc.prog.instrs[step.idx];
    intros::Ctx ictx = make_intros_ctx(dcc);
    projections::Ctx pctx = make_projections_ctx(dcc);
    Demand norm_demand = normalize_demand(demand);

    return std::visit(
        [&](const auto& op) -> util::ResultStatus {
            using T = std::decay_t<decltype(op)>;

            // ---- intros family (Phase 1) ---------------------------
            if constexpr (std::is_same_v<T, nd::AndIntro>) {
                TRY_ASSIGN(r, intros::emit_and_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::OrIntroL>) {
                TRY_ASSIGN(r, intros::emit_or_intro_l(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::OrIntroR>) {
                TRY_ASSIGN(r, intros::emit_or_intro_r(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::ImpliesIntro>) {
                TRY_ASSIGN(r, intros::emit_implies_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::IffIntro>) {
                TRY_ASSIGN(r, intros::emit_iff_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::ExistsIntro>) {
                if (!op.witness.has_value()) {
                    return MAKE_ERROR
                        << "translate_step: ExistsIntro no-witness form "
                           "(EXISTS_ELIM closer) requires Phase 5e";
                }
                TRY_ASSIGN(r, intros::emit_exists_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::ExcludedMiddle>) {
                TRY_ASSIGN(r, intros::emit_excluded_middle(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::Peirce>) {
                TRY_ASSIGN(r, intros::emit_peirce(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            }

            // ---- projection elims (Phase 2) ------------------------
            else if constexpr (std::is_same_v<T, nd::AndElimL>) {
                TRY_ASSIGN(desc, projections::emit_and_elim_l(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::AndElimR>) {
                TRY_ASSIGN(desc, projections::emit_and_elim_r(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::IffElimL>) {
                TRY_ASSIGN(desc, projections::emit_iff_elim_l(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::IffElimR>) {
                TRY_ASSIGN(desc, projections::emit_iff_elim_r(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::DoubleNegElim>) {
                TRY_ASSIGN(desc, projections::emit_double_neg_elim(
                    pctx, op, shadow, target_pos));
                // Demand promotes to DemandDoubleNeg, which the
                // dispatcher normalizes back to DemandNone via
                // normalize_demand() at recursion entry.
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::ForallElim>) {
                // ForallElim promotes DemandInstance(t), which requires
                // ForallIntro to substitute eigen → t. That depends on
                // block_tree fix-step lookup, deferred to 5e.
                return MAKE_ERROR
                    << "translate_step: ForallElim requires "
                       "ForallIntro/INSTANCE handling (Phase 5e)";
            }

            // ---- ForallIntro requires block_tree integration to find
            //      its enclosing Fix's eigen — Phase 5e.
            else if constexpr (std::is_same_v<T, nd::ForallIntro>) {
                return MAKE_ERROR
                    << "translate_step: ForallIntro requires block_tree "
                       "eigen lookup (Phase 5e)";
            }

            // ---- not-yet-supported families ------------------------
            else {
                std::ostringstream what;
                what << "translate_step: op family (variant "
                     << instr.index()
                     << ") not yet supported in Phase 5c "
                        "(combining/structural/closer integration lands "
                        "in 5d-5e)";
                return MAKE_ERROR << what.str();
            }
        },
        instr);
}

}  // namespace

util::ResultStatus translate_step(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out)
{
    return translate_step_impl(
        dcc, std::move(shadow), step, target_pos, demand, out);
}

}  // namespace logic::proof::translate::nd_to_lkr::dispatcher
