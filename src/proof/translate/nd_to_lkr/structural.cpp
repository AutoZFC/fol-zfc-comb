#include "structural.h"

#include <variant>

namespace logic::proof::translate::nd_to_lkr::structural {

namespace {

// Helper: dereference a `bottom` StepRef expected to point at a
// NotElim ghost, and extract its (negation, formula) operand step
// refs. The closers (NotIntro, BottomElim, ClassicalAbsurd) all
// follow this pattern per α policy.
struct NotElimOperands {
    StepRef neg_step;
    StepRef formula_step;
};

util::Result<NotElimOperands> deref_notelim(
    const Program<nd::Instr>& prog,
    StepRef                   bottom,
    const char*               op_label)
{
    if (bottom.idx >= prog.instrs.size()) {
        return MAKE_ERROR
            << op_label << ": `bottom` step ref #" << bottom.idx
            << " out of range (program size " << prog.instrs.size() << ")";
    }
    const auto& bot_instr = prog.instrs[bottom.idx];
    if (!std::holds_alternative<nd::NotElim>(bot_instr)) {
        return MAKE_ERROR
            << op_label << ": `bottom` at #" << bottom.idx
            << " is not a NotElim (variant " << bot_instr.index() << ")";
    }
    const auto& ne = std::get<nd::NotElim>(bot_instr);
    return NotElimOperands{ne.negation, ne.formula};
}

}  // namespace

util::Result<AssumeOpenSite> emit_assume_open(
    Ctx&              cc,
    const nd::Assume& /*op*/,
    StepRef           assume_step)
{
    // The assumed formula has been validated and parsed by NDVerifier;
    // we read it from trace.step_env.
    if (assume_step.idx >= cc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_assume_open: step #" << assume_step.idx
            << " out of trace range";
    }
    FormulaHandle f = cc.trace.step_env[assume_step.idx];
    if (!f.valid()) {
        return MAKE_ERROR
            << "emit_assume_open: step #" << assume_step.idx
            << " has no formula in trace";
    }
    return AssumeOpenSite{assume_step, f};
}

util::Result<FixOpenSite> emit_fix_open(
    Ctx&            cc,
    const nd::Fix&  /*op*/,
    StepRef         fix_step)
{
    if (fix_step.idx >= cc.trace.term_env.size()) {
        return MAKE_ERROR
            << "emit_fix_open: step #" << fix_step.idx
            << " out of trace range";
    }
    if (fix_step.idx >= cc.trace.term_present.size() ||
        !cc.trace.term_present[fix_step.idx]) {
        return MAKE_ERROR
            << "emit_fix_open: step #" << fix_step.idx
            << " has no term in trace";
    }
    const Term& t = cc.trace.term_env[fix_step.idx];
    if (!t.is_fixed()) {
        return MAKE_ERROR
            << "emit_fix_open: step #" << fix_step.idx
            << " trace term is not a fixed variable";
    }
    return FixOpenSite{fix_step, t.as_variable()};
}

util::Result<ExistsElimOpenSite> emit_exists_elim_open(
    Ctx&                  cc,
    const nd::ExistsElim& op,
    StepRef               exists_elim_step)
{
    if (exists_elim_step.idx >= cc.trace.term_env.size()) {
        return MAKE_ERROR
            << "emit_exists_elim_open: step #" << exists_elim_step.idx
            << " out of trace range";
    }
    if (exists_elim_step.idx >= cc.trace.term_present.size() ||
        !cc.trace.term_present[exists_elim_step.idx]) {
        return MAKE_ERROR
            << "emit_exists_elim_open: step #" << exists_elim_step.idx
            << " has no eigen in trace";
    }
    const Term& t = cc.trace.term_env[exists_elim_step.idx];
    if (!t.is_fixed()) {
        return MAKE_ERROR
            << "emit_exists_elim_open: step #" << exists_elim_step.idx
            << " trace term is not a fixed variable";
    }
    return ExistsElimOpenSite{exists_elim_step, op.formula, t.as_variable()};
}

util::Result<NotIntroCloseSite> emit_not_intro_close(
    Ctx&                cc,
    const nd::NotIntro& op,
    StepRef             not_intro_step)
{
    auto operands = deref_notelim(cc.prog, op.bottom, "emit_not_intro_close");
    if (!operands.ok()) return operands.error();
    return NotIntroCloseSite{
        not_intro_step,
        operands.value().neg_step,
        operands.value().formula_step};
}

util::Result<BottomElimCloseSite> emit_bottom_elim_close(
    Ctx&                  cc,
    const nd::BottomElim& op,
    StepRef               bottom_elim_step)
{
    auto operands = deref_notelim(cc.prog, op.bottom, "emit_bottom_elim_close");
    if (!operands.ok()) return operands.error();
    return BottomElimCloseSite{
        bottom_elim_step,
        operands.value().neg_step,
        operands.value().formula_step,
        op.target_formula};
}

util::Result<ClassicalAbsurdCloseSite> emit_classical_absurd_close(
    Ctx&                       cc,
    const nd::ClassicalAbsurd& op,
    StepRef                    absurd_step)
{
    auto operands = deref_notelim(cc.prog, op.bottom, "emit_classical_absurd_close");
    if (!operands.ok()) return operands.error();
    return ClassicalAbsurdCloseSite{
        absurd_step,
        operands.value().neg_step,
        operands.value().formula_step};
}

util::Result<AssumeLeafSite> emit_assume_leaf(
    Ctx&                 /*cc*/,
    const nd::Assume&    /*op*/,
    StepRef              assume_step,
    const SequentShadow& shadow,
    size_t               target_pos)
{
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_assume_leaf: target_pos out of range";
    }
    return AssumeLeafSite{assume_step, target_pos};
}

util::Result<QedSite> emit_qed_site(
    Ctx&           /*cc*/,
    const nd::Qed& op,
    StepRef        qed_step)
{
    return QedSite{qed_step, op.derived};
}

}  // namespace logic::proof::translate::nd_to_lkr::structural
