// Leaves and the left rules on duals (ELIMINATION_DEMANDS_DESIGN.md §2.4).

#include "dispatcher.h"

#include <algorithm>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

bool contains(const std::vector<size_t>& positions, size_t p) {
    return std::find(positions.begin(), positions.end(), p) != positions.end();
}

}  // namespace

util::ResultStatus Dispatcher::leaf(Task t, DualSlot slot) {
    if (slot.pending.empty()) {
        if (slot.pos) {
            return run(LeftRulesWork{std::move(t.seq), *slot.pos, t.target,
                                     std::move(t.path)});
        }
        if (!t.path.empty()) {
            if (auto* r = std::get_if<DemandRefute>(&t.path.head())) {
                return refute(std::move(t.seq), r->refuter, Target::none(), {});
            }
        }
        return MAKE_ERROR << "leaf #" << t.step.idx
                          << ": hypothesis with dual 0 under a demand";
    }
    Target result = slot.pos ? Target::at(*slot.pos) : Target::none();
    if (t.path.empty()) {
        if (t.target.is_none()) {
            return MAKE_ERROR << "leaf #" << t.step.idx
                              << ": pending dual without a target";
        }
        return run(LeftRulesWork{std::move(t.seq), t.target.pos(), result,
                                 std::move(slot.pending)});
    }
    if (auto* r = std::get_if<DemandRefute>(&t.path.head())) {
        return refute(std::move(t.seq), r->refuter, result,
                      std::move(slot.pending));
    }
    return MAKE_ERROR << "leaf #" << t.step.idx
                      << ": a pending dual meets a demand other than Refute "
                         "(Lemma D1)";
}

util::ResultStatus Dispatcher::run(LeftRulesWork w) {
    SequentShadow& seq = w.seq;
    DemandPath&    path = w.path;
    size_t         dual = w.dual;
    // Copy rule: peel a copy of d if the rest of the task still needs it.
    if (!path.empty()) {
        std::vector<size_t> needed;
        need(seq, path, needed);
        if (!w.target.is_none()) needed.push_back(w.target.pos());
        if (contains(needed, dual)) {
            TRY_ASSIGN(copy, seq.duplicate(dual, sink_));
            dual = copy;
        }
    }
    while (!path.empty()) {
        Demand head = path.pop();
        if (auto* inst = std::get_if<DemandInstance>(&head)) {
            TRY(seq.exists_rule(dual, inst->term, builder_, sink_));
        } else if (std::holds_alternative<DemandAndLeft>(head)) {
            TRY(seq.or_rule(dual, sink_));
        } else if (std::holds_alternative<DemandAndRight>(head)) {
            TRY_ASSIGN(right, seq.or_rule(dual, sink_));
            dual = right;
        } else if (auto* m = std::get_if<DemandModus>(&head)) {
            return modus(std::move(seq), dual, m->antecedent, w.target,
                         std::move(path));
        } else if (auto* iff = std::get_if<DemandIffModus>(&head)) {
            TRY_ASSIGN(second, seq.or_rule(dual, sink_));
            size_t clause = iff->side == Side::Left ? dual : second;
            return modus(std::move(seq), clause, Minor{iff->operand},
                         w.target, std::move(path));
        } else if (auto* r = std::get_if<DemandRefute>(&head)) {
            if (!path.empty() || !w.target.is_none()) {
                return MAKE_ERROR << "left rules: Refute must end the path "
                                     "with no target";
            }
            return refute(std::move(seq), r->refuter, Target::at(dual), {});
        } else if (auto* c = std::get_if<DemandCases>(&head)) {
            return cases(std::move(seq), dual, *c, w.target, std::move(path));
        } else if (auto* wit = std::get_if<DemandWitness>(&head)) {
            TRY_ASSIGN(eigen, seq.forall_rule(dual, builder_, sink_));
            StepRef closer = wit->closer;
            BlockId b = index_.closed_by(closer);
            seq.terms().bind(index_.opener(b), eigen);
            seq.bind_dual(HypId::of_step(index_.opener(b)), dual);
            TRY_ASSIGN(body, exists_elim_body(
                Task{std::move(seq), closer, w.target, std::move(path)}, closer));
            return next(EnterWork{b, 0, std::move(body)});
        }
    }
    if (w.target.is_none()) return seq.one(dual, sink_);
    return std::move(seq).identity(w.target.pos(), dual, builder_, sink_);
}

util::ResultStatus Dispatcher::modus(SequentShadow seq, size_t principal,
                                     const Minor& m, Target target,
                                     DemandPath rest) {
    std::vector<size_t> left_needs, right_needs;
    need(seq, m, left_needs);
    need(seq, rest, right_needs);
    if (!target.is_none()) right_needs.push_back(target.pos());
    TRY_ASSIGN(split, std::move(seq).and_rule(principal, left_needs,
                                              right_needs, sink_));
    TRY_ASSIGN(left, minor(std::move(split.left.shadow), m, split.left.added));
    return next(std::move(left),
                LeftRulesWork{std::move(split.right.shadow), split.right.added,
                              split.right.remap(target), std::move(rest)});
}

util::ResultStatus Dispatcher::cases(SequentShadow seq, size_t principal,
                                     DemandCases c, Target target,
                                     DemandPath rest) {
    std::vector<size_t> left_needs, right_needs;
    need(seq, c.if_left, left_needs);
    need(seq, c.if_right, right_needs);
    need(seq, rest, left_needs);
    need(seq, rest, right_needs);
    if (!target.is_none()) {
        left_needs.push_back(target.pos());
        right_needs.push_back(target.pos());
    }
    TRY_ASSIGN(split, std::move(seq).and_rule(principal, left_needs,
                                              right_needs, sink_));
    HypId a = fresh_local();
    split.left.shadow.bind_dual(a, split.left.added);
    DemandPath if_a = rest;
    if_a.push(DemandModus{Minor{a}});
    HypId b = fresh_local();
    split.right.shadow.bind_dual(b, split.right.added);
    rest.push(DemandModus{Minor{b}});
    return next(TranslateWork{Task{std::move(split.left.shadow), c.if_left,
                                   split.left.remap(target), std::move(if_a)}},
                TranslateWork{Task{std::move(split.right.shadow), c.if_right,
                                   split.right.remap(target), std::move(rest)}});
}

util::Result<std::optional<Dispatcher::Work>> Dispatcher::minor(
    SequentShadow seq, const Minor& m, size_t into) {
    if (auto* step = std::get_if<StepRef>(&m)) {
        return std::optional<Work>{
            TranslateWork{Task{std::move(seq), *step, Target::at(into), {}}}};
    }
    const DualSlot* slot = seq.dual(std::get<HypId>(m));
    if (!slot) return MAKE_ERROR << "minor: hypothesis has no dual";
    if (!slot->pos) {
        TRY(seq.one(into, sink_));
    } else {
        size_t hypothesis = *slot->pos;
        TRY(std::move(seq).identity(into, hypothesis, builder_, sink_));
    }
    return std::optional<Work>{};
}

util::ResultStatus Dispatcher::refute(SequentShadow seq, StepRef refuter,
                                      Target into, DemandPath path) {
    if (!into.is_none()) {
        std::vector<size_t> needed;
        need(seq, refuter, needed);
        need(seq, path, needed);
        if (contains(needed, into.pos())) {
            TRY_ASSIGN(copy, seq.duplicate(into.pos(), sink_));
            into = Target::at(copy);
        }
    }
    return next(Task{std::move(seq), refuter, into, std::move(path)});
}

}  // namespace logic::proof::translate::nd_to_lkr
