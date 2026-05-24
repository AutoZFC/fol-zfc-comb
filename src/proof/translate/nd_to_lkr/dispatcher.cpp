#include "dispatcher.h"

#include "block_tree.h"
#include "combining.h"
#include "emit_close.h"
#include "intros.h"
#include "projections.h"

#include "src/core/formula.h"

#include <sstream>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr::dispatcher {

// Walk the block tree and record (closer_idx → opener_idx) for every
// non-OUTER block. Used by the dispatcher to look up an Assume opener
// from an ImpliesIntro closer (and analogues).
namespace {
void walk_block(const Block& blk, CloserToOpener& out) {
    if (blk.opener_idx != kInvalidIdx && blk.closer_idx != kInvalidIdx) {
        out[blk.closer_idx] = blk.opener_idx;
    }
    for (const auto& item : blk.body) {
        if (auto* sub = std::get_if<std::unique_ptr<Block>>(&item)) {
            walk_block(**sub, out);
        }
    }
}
}  // namespace

CloserToOpener build_closer_to_opener(const Block& root) {
    CloserToOpener out;
    walk_block(root, out);
    return out;
}

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

// =========================================================================
// Combining-elim full emission (Phase 5d).
// =========================================================================
//
// implies_elim(impl: A→B, ant: A) ⊢ B. Cut-minimal LK construction:
//
//   1. Cut(NNF(impl)):  LEFT = Γ, A→B    RIGHT = Γ, NNF(¬impl)
//      LEFT closed by recursive translation of `impl` step.
//   2. (on RIGHT, with NNF(¬impl) = A ∧ ¬B at cut_impl_idx)
//      Cut(NNF(ant)):  LEFT = Γ, A      RIGHT = Γ, NNF(¬ant)
//      LEFT closed by recursive translation of `ant` step.
//   3. (on RIGHT-of-Cut(ant), with both ¬impl and ¬ant in scope)
//      And{principal=cut_impl_idx, left_partition=[cut_ant_idx]}.
//      LEFT-subgoal: [NNF(¬ant)=¬A, phi=A]. AxiomLit(0, 1).
//      RIGHT-subgoal: [Γ-complement, psi=¬B]. AxiomLit(target_pos, psi_pos).
//
// Total: 2 Cuts + 1 And + 2 AxiomLits, plus recursion on impl and ant.
// Pure cut-minimal: no other Cuts, in line with the controlling design.
util::ResultStatus emit_implies_elim_full(
    Ctx&                       dcc,
    const SequentShadow&       shadow,
    const nd::ImpliesElim&     op,
    size_t                     target_pos,
    std::vector<lkr::Instr>&   out);

// Closer family (Phase 5e.2): NOT / BottomElim / ClassicalAbsurd.
// All three discharge a contradiction via the NotElim ghost at
// `bottom`. The closer emits Cut(NNF(F_neg)) + Cut(NNF(F_formula))
// + recurses on each LEFT branch + emit_close on the duals visible
// in the final RIGHT branch. For NotIntro and ClassicalAbsurd, the
// closer also records the matching Assume opener's dual at target_pos
// so body-side references close correctly.
util::ResultStatus emit_contradiction_close(
    Ctx&                     dcc,
    SequentShadow            shadow,
    uint32_t                 closer_step_idx,
    StepRef                  notelim_bottom,
    bool                     record_assume_dual,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out);

}  // namespace

// Forward-declared above for use inside translate_step_impl's visitor.
namespace {

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
                // emit_implies_intro emits Or which places NNF(¬A) at
                // target_pos (where A→B was). The dispatcher looks up
                // the matching Assume opener and records its dual
                // position so body-side Assume leaves can close
                // against it.
                TRY_ASSIGN(r, intros::emit_implies_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                if (auto* one = std::get_if<intros::OnePremise>(&r)) {
                    auto co = dcc.closer_to_opener.find(step.idx);
                    if (co == dcc.closer_to_opener.end()) {
                        return MAKE_ERROR
                            << "translate_step: ImpliesIntro at #" << step.idx
                            << " has no matching IMPLIES block opener";
                    }
                    // After emit_implies_intro, target_pos holds NNF(¬A).
                    one->shadow.step_to_neg_idx[co->second] = target_pos;
                }
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

            // ---- combining elims (Phase 5d) ------------------------
            else if constexpr (std::is_same_v<T, nd::ImpliesElim>) {
                return emit_implies_elim_full(dcc, shadow, op, target_pos, out);
            }

            // ---- closer family (Phase 5e.2) -----------------------
            else if constexpr (std::is_same_v<T, nd::NotIntro>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/true, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::BottomElim>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/false, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::ClassicalAbsurd>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/true, target_pos, out);
            }

            // ---- Assume leaf (Phase 5e.1) -------------------------
            // Recursing on an Assume step means a downstream op
            // references the assumption's formula. The enclosing
            // IMPLIES/NOT/CLASSICAL_ABSURD intro placed NNF(¬A) at a
            // position recorded in shadow.step_to_neg_idx. emit_close
            // discharges via the dual at (target_pos, dual_pos).
            else if constexpr (std::is_same_v<T, nd::Assume>) {
                auto it = shadow.step_to_neg_idx.find(step.idx);
                if (it == shadow.step_to_neg_idx.end()) {
                    return MAKE_ERROR
                        << "translate_step: Assume #" << step.idx
                        << " has no recorded dual position — no "
                           "enclosing IMPLIES/NOT/CLASSICAL_ABSURD intro "
                           "placed it";
                }
                size_t dual_pos = it->second;
                EmitCloseContext ecc{dcc.builder};
                return emit_close(ecc, shadow, target_pos, dual_pos, out);
            }

            // ---- ForallIntro (Phase 5e.3) -------------------------
            // Look up the matching FORALL-block opener (Fix step) via
            // closer_to_opener, then pull the eigen from trace.term_env.
            // Pass to Phase 1's emit_forall_intro, then bind
            // shadow.lkr_term_for[fix_idx] so body-side TermRefs (e.g.
            // in nested Exists or recursive ForallElim) resolve to the
            // LKR Forall instr just emitted.
            else if constexpr (std::is_same_v<T, nd::ForallIntro>) {
                auto co = dcc.closer_to_opener.find(step.idx);
                if (co == dcc.closer_to_opener.end()) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro at #" << step.idx
                        << " has no matching FORALL block opener";
                }
                uint32_t fix_idx = co->second;
                if (fix_idx >= dcc.trace.term_env.size() ||
                    fix_idx >= dcc.trace.term_present.size() ||
                    !dcc.trace.term_present[fix_idx]) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro's Fix #" << fix_idx
                        << " has no eigen in trace";
                }
                const Term& fix_term = dcc.trace.term_env[fix_idx];
                if (!fix_term.is_fixed()) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro's Fix #" << fix_idx
                        << " trace term is not a fixed variable";
                }
                var_index eigen = fix_term.as_variable();

                // emit_forall_intro emits the LKR Forall op; its instr
                // index is out.size() at this point.
                size_t lkr_forall_idx = out.size();
                TRY_ASSIGN(r, intros::emit_forall_intro(
                    ictx, op, eigen, shadow, target_pos, out, norm_demand));
                if (auto* one = std::get_if<intros::OnePremise>(&r)) {
                    SequentShadow::TermBinding binding;
                    binding.lkr_ref = TermRef{static_cast<uint32_t>(lkr_forall_idx)};
                    binding.value   = fix_term;
                    one->shadow.lkr_term_for[fix_idx] = binding;
                }
                return handle_intro_result(dcc, std::move(r), out);
            }

            // ---- not-yet-supported families ------------------------
            else {
                std::ostringstream what;
                what << "translate_step: op family (variant "
                     << instr.index()
                     << ") not yet supported in Phase 5d "
                        "(or_elim, exists_elim, structural, closer "
                        "integration lands in 5d/5e)";
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

namespace {

util::ResultStatus emit_implies_elim_full(
    Ctx&                     dcc,
    const SequentShadow&     shadow,
    const nd::ImpliesElim&   op,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    if (op.impl.idx >= dcc.trace.step_env.size() ||
        op.ant.idx  >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_implies_elim_full: step refs out of trace range";
    }
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR
            << "emit_implies_elim_full: target_pos out of range";
    }

    FormulaHandle impl_f       = dcc.trace.step_env[op.impl.idx];
    FormulaHandle impl_nnf     = dcc.builder.to_nnf(impl_f);
    FormulaHandle neg_impl_nnf = dcc.builder.to_nnf_neg(impl_f);
    FormulaHandle ant_f        = dcc.trace.step_env[op.ant.idx];
    FormulaHandle ant_nnf      = dcc.builder.to_nnf(ant_f);
    FormulaHandle neg_ant_nnf  = dcc.builder.to_nnf_neg(ant_f);

    if (!neg_impl_nnf.get().is_compound() ||
        neg_impl_nnf.get().as_compound().op != Op::And) {
        return MAKE_ERROR
            << "emit_implies_elim_full: NNF(¬impl) is not And-compound";
    }

    // Step 1: Cut(NNF(impl)).
    out.emplace_back(lkr::Cut{{}, impl_nnf});

    // LEFT-of-Cut(impl): shadow + NNF(impl) appended; recurse on impl.
    SequentShadow left_impl = shadow;
    size_t left_impl_pos = left_impl.entries.size();
    left_impl.entries.push_back(impl_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_impl), op.impl,
        left_impl_pos, Demand{DemandNone{}}, out));

    // RIGHT-of-Cut(impl): NNF(¬impl) appended at cut_impl_idx.
    SequentShadow right_impl = shadow;
    size_t cut_impl_idx = right_impl.entries.size();
    right_impl.entries.push_back(neg_impl_nnf);

    // Step 2: Cut(NNF(ant)) on RIGHT-of-Cut(impl).
    out.emplace_back(lkr::Cut{{}, ant_nnf});

    SequentShadow left_ant = right_impl;
    size_t left_ant_pos = left_ant.entries.size();
    left_ant.entries.push_back(ant_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_ant), op.ant,
        left_ant_pos, Demand{DemandNone{}}, out));

    // RIGHT-of-Cut(ant): NNF(¬ant) appended at cut_ant_idx.
    SequentShadow right_ant = right_impl;
    size_t cut_ant_idx = right_ant.entries.size();
    right_ant.entries.push_back(neg_ant_nnf);

    // Step 3: And{principal=cut_impl_idx, left_partition=[cut_ant_idx]}.
    out.emplace_back(lkr::And{{}, cut_impl_idx, {cut_ant_idx}});

    // LEFT-of-And: [neg_ant_nnf=¬A, phi=NNF(A)]. Dual at (0, 1).
    out.emplace_back(lkr::AxiomLit{{}, 0, 1});

    // RIGHT-of-And: [Γ-complement, psi=NNF(¬B) at end]. Dual at
    // (target_pos, psi_pos = right_ant.size() - 2).
    // (psi_pos: complement has right_ant.size()-2 entries; psi
    // appended at index complement.size() = right_ant.size()-2.)
    size_t psi_pos = right_ant.entries.size() - 2;
    out.emplace_back(lkr::AxiomLit{{}, target_pos, psi_pos});

    return util::Ok();
}

util::ResultStatus emit_contradiction_close(
    Ctx&                     dcc,
    SequentShadow            shadow,
    uint32_t                 closer_step_idx,
    StepRef                  notelim_bottom,
    bool                     record_assume_dual,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    if (notelim_bottom.idx >= dcc.prog.instrs.size()) {
        return MAKE_ERROR
            << "emit_contradiction_close: bottom #" << notelim_bottom.idx
            << " out of program range";
    }
    const auto& bot_instr = dcc.prog.instrs[notelim_bottom.idx];
    if (!std::holds_alternative<nd::NotElim>(bot_instr)) {
        return MAKE_ERROR
            << "emit_contradiction_close: bottom #" << notelim_bottom.idx
            << " is not a NotElim";
    }
    const auto& ne = std::get<nd::NotElim>(bot_instr);

    if (record_assume_dual) {
        auto co = dcc.closer_to_opener.find(closer_step_idx);
        if (co == dcc.closer_to_opener.end()) {
            return MAKE_ERROR
                << "emit_contradiction_close: closer #" << closer_step_idx
                << " has no matching block opener";
        }
        // Record the assumption-step's dual at target_pos so body-side
        // references close against it.
        shadow.step_to_neg_idx[co->second] = target_pos;
    }

    if (ne.negation.idx >= dcc.trace.step_env.size() ||
        ne.formula.idx  >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_contradiction_close: NotElim operand out of trace range";
    }
    FormulaHandle f_neg = dcc.trace.step_env[ne.negation.idx];
    FormulaHandle f_form = dcc.trace.step_env[ne.formula.idx];
    FormulaHandle f_neg_nnf  = dcc.builder.to_nnf(f_neg);
    FormulaHandle f_form_nnf = dcc.builder.to_nnf(f_form);

    // Step 1: Cut(NNF(F_neg)).
    out.emplace_back(lkr::Cut{{}, f_neg_nnf});

    // LEFT: shadow + NNF(F_neg). Recurse on neg_step.
    SequentShadow left_neg = shadow;
    size_t left_neg_pos = left_neg.entries.size();
    left_neg.entries.push_back(f_neg_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_neg), ne.negation,
        left_neg_pos, Demand{DemandNone{}}, out));

    // RIGHT: shadow + NNF(¬F_neg) (= NNF(F_formula) in NNF semantics).
    SequentShadow right_neg = shadow;
    size_t outer_dual_pos = right_neg.entries.size();
    right_neg.entries.push_back(dcc.builder.to_nnf_neg(f_neg));

    // Step 2: Cut(NNF(F_formula)) on RIGHT-of-Cut(F_neg).
    out.emplace_back(lkr::Cut{{}, f_form_nnf});

    // LEFT: right_neg + NNF(F_formula). Recurse on formula_step.
    SequentShadow left_form = right_neg;
    size_t left_form_pos = left_form.entries.size();
    left_form.entries.push_back(f_form_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_form), ne.formula,
        left_form_pos, Demand{DemandNone{}}, out));

    // RIGHT: right_neg + NNF(¬F_formula) (= NNF(F_neg)).
    SequentShadow right_form = right_neg;
    size_t inner_dual_pos = right_form.entries.size();
    right_form.entries.push_back(dcc.builder.to_nnf_neg(f_form));

    // Step 3: emit_close on the two duals (NNF(F_formula) at
    // outer_dual_pos and NNF(F_neg) at inner_dual_pos).
    EmitCloseContext ecc{dcc.builder};
    return emit_close(ecc, right_form, outer_dual_pos, inner_dual_pos, out);
}

}  // namespace

}  // namespace logic::proof::translate::nd_to_lkr::dispatcher
