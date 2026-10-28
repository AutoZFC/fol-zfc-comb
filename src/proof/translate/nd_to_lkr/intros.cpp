// Introductions: right rules and redexes (ELIMINATION_DEMANDS_DESIGN.md §2.2).

#include "dispatcher.h"

#include "src/proof/lkr_build/nnf_shapes.h"

#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

util::ResultStatus require_target(const Target& target, StepRef step) {
    if (target.is_none()) {
        return MAKE_ERROR << "translate: introduction #" << step.idx
                          << " has no target (its result is never ⊥)";
    }
    return util::Ok();
}

}  // namespace

util::ResultStatus Dispatcher::on(const nd::AndIntro& op, Task t) {
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        std::vector<size_t> left_needs, right_needs;
        need(t.seq, op.a, left_needs);
        need(t.seq, op.b, right_needs);
        TRY_ASSIGN(split, std::move(t.seq).and_rule(
            t.target.pos(), left_needs, right_needs, sink_));
        return next(TranslateWork{Task{std::move(split.left.shadow), op.a,
                                       Target::at(split.left.added), {}}},
                    TranslateWork{Task{std::move(split.right.shadow), op.b,
                                       Target::at(split.right.added), {}}});
    }
    if (std::holds_alternative<DemandAndLeft>(t.path.head())) {
        t.step = op.a;
    } else if (std::holds_alternative<DemandAndRight>(t.path.head())) {
        t.step = op.b;
    } else {
        return impossible_head(t);
    }
    t.path.pop();
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::OrIntroL& op, Task t) {
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY(t.seq.or_rule(t.target.pos(), sink_));
        t.step = op.a;
        return next(std::move(t));
    }
    auto* cases = std::get_if<DemandCases>(&t.path.head());
    if (!cases) return impossible_head(t);
    StepRef if_left = cases->if_left;
    t.path.pop();
    t.path.push(DemandModus{Minor{op.a}});
    t.step = if_left;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::OrIntroR& op, Task t) {
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY_ASSIGN(right, t.seq.or_rule(t.target.pos(), sink_));
        t.target = Target::at(right);
        t.step = op.b;
        return next(std::move(t));
    }
    auto* cases = std::get_if<DemandCases>(&t.path.head());
    if (!cases) return impossible_head(t);
    StepRef if_right = cases->if_right;
    t.path.pop();
    t.path.push(DemandModus{Minor{op.b}});
    t.step = if_right;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::ImpliesIntro& op, Task t) {
    BlockId b = index_.closed_by(t.step);
    StepRef assumption = index_.opener(b);
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY_ASSIGN(consequent, t.seq.or_rule(t.target.pos(), sink_));
        t.seq.bind_dual(HypId::of_step(assumption), t.target.pos());
        return next(EnterWork{b, 0, TranslateWork{Task{
            std::move(t.seq), op.conclusion, Target::at(consequent), {}}}});
    }
    auto* modus = std::get_if<DemandModus>(&t.path.head());
    if (!modus) return impossible_head(t);
    Minor antecedent = modus->antecedent;
    t.path.pop();
    TRY_ASSIGN(bound, bind(std::move(t.seq), assumption, antecedent));
    return next(std::move(bound.first),
                EnterWork{b, 0, TranslateWork{Task{std::move(bound.seq),
                                                   op.conclusion, t.target,
                                                   std::move(t.path)}}});
}

util::ResultStatus Dispatcher::on(const nd::IffIntro& op, Task t) {
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        std::vector<size_t> left_needs, right_needs;
        need(t.seq, op.ab, left_needs);
        need(t.seq, op.ba, right_needs);
        TRY_ASSIGN(split, std::move(t.seq).and_rule(
            t.target.pos(), left_needs, right_needs, sink_));
        return next(TranslateWork{Task{std::move(split.left.shadow), op.ab,
                                       Target::at(split.left.added), {}}},
                    TranslateWork{Task{std::move(split.right.shadow), op.ba,
                                       Target::at(split.right.added), {}}});
    }
    auto* iff = std::get_if<DemandIffModus>(&t.path.head());
    if (!iff) return impossible_head(t);
    StepRef operand = iff->operand;
    t.step = iff->side == Side::Left ? op.ab : op.ba;
    t.path.pop();
    t.path.push(DemandModus{Minor{operand}});
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::ForallIntro& op, Task t) {
    BlockId b = index_.closed_by(t.step);
    StepRef fix = index_.opener(b);
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY_ASSIGN(eigen, t.seq.forall_rule(t.target.pos(), builder_, sink_));
        t.seq.terms().bind(fix, eigen);
    } else if (auto* inst = std::get_if<DemandInstance>(&t.path.head())) {
        t.seq.terms().bind(fix, inst->term);
        t.path.pop();
    } else {
        return impossible_head(t);
    }
    t.step = op.body;
    return next(EnterWork{b, 0, TranslateWork{std::move(t)}});
}

util::ResultStatus Dispatcher::run(ExistsIntroWork w) {
    Task& t = w.task;
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY(t.seq.exists_rule(t.target.pos(), w.witness, builder_, sink_));
        t.step = w.body;
        return next(std::move(t));
    }
    auto* elim = std::get_if<DemandWitness>(&t.path.head());
    if (!elim) return impossible_head(t);
    StepRef closer = elim->closer;
    t.path.pop();
    BlockId b = index_.closed_by(closer);
    t.seq.terms().bind(index_.opener(b), w.witness);
    TRY_ASSIGN(bound, bind(std::move(t.seq), index_.opener(b), Minor{w.body}));
    TRY_ASSIGN(body, exists_elim_body(
        Task{std::move(bound.seq), closer, t.target, std::move(t.path)}, closer));
    return next(std::move(bound.first), EnterWork{b, 0, std::move(body)});
}

util::ResultStatus Dispatcher::on(const nd::ExcludedMiddle&, Task t) {
    if (t.path.empty()) {
        TRY(require_target(t.target, t.step));
        TRY_ASSIGN(negated, t.seq.or_rule(t.target.pos(), sink_));
        return std::move(t.seq).identity(t.target.pos(), negated, builder_,
                                         sink_);
    }
    auto* cases = std::get_if<DemandCases>(&t.path.head());
    if (!cases) return impossible_head(t);
    DemandCases c = *cases;
    t.path.pop();
    TRY_ASSIGN(em, reader_.read(t.step, t.seq.terms()));
    if (!lkr_build::has_op(em, Op::Or)) {
        return MAKE_ERROR << "excluded_middle #" << t.step.idx
                          << ": result is not A ∨ ¬A";
    }
    FormulaHandle a_nnf = builder_.to_nnf(em.get().as_compound().left);
    Split split = std::move(t.seq).cut_rule(a_nnf, builder_, sink_);
    HypId not_a = fresh_local();
    split.left.shadow.bind_dual(not_a, split.left.added);
    DemandPath if_not_a = t.path;
    if_not_a.push(DemandModus{Minor{not_a}});
    HypId a = fresh_local();
    split.right.shadow.bind_dual(a, split.right.added);
    t.path.push(DemandModus{Minor{a}});
    return next(TranslateWork{Task{std::move(split.left.shadow), c.if_right,
                                   t.target, std::move(if_not_a)}},
                TranslateWork{Task{std::move(split.right.shadow), c.if_left,
                                   t.target, std::move(t.path)}});
}

util::ResultStatus Dispatcher::on(const nd::Peirce&, Task t) {
    if (!t.path.empty()) return let_cut(std::move(t));
    TRY(require_target(t.target, t.step));
    size_t goal = t.target.pos();
    TRY_ASSIGN(a1, t.seq.or_rule(goal, sink_));
    TRY_ASSIGN(a2, t.seq.duplicate(a1, sink_));
    TRY_ASSIGN(split, std::move(t.seq).and_rule(goal, {a1}, {a2}, sink_));
    size_t left_a = *split.left.moved[a1];
    TRY(split.left.shadow.or_rule(split.left.added, sink_));
    TRY(std::move(split.left.shadow).identity(left_a, split.left.added,
                                              builder_, sink_));
    return std::move(split.right.shadow).identity(
        *split.right.moved[a2], split.right.added, builder_, sink_);
}

}  // namespace logic::proof::translate::nd_to_lkr
