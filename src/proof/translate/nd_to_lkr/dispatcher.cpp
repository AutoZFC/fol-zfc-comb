#include "dispatcher.h"

#include "src/proof/lkr_build/nnf_shapes.h"

#include <unordered_set>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr {

util::ResultStatus Dispatcher::translate_proof(FormulaHandle goal_nnf) {
    agenda_.clear();
    TRY(next(EnterWork{index_.outer(), 0, TranslateWork{Task{
        SequentShadow(goal_nnf), index_.root(), Target::at(0), {}}}}));
    while (!agenda_.empty()) {
        Work work = std::move(agenda_.back());
        agenda_.pop_back();
        TRY(std::visit([&](auto& w) { return run(std::move(w)); }, work));
    }
    return util::Ok();
}

util::ResultStatus Dispatcher::next(Work w) {
    agenda_.push_back(std::move(w));
    return util::Ok();
}

util::ResultStatus Dispatcher::next(std::optional<Work> first, Work second) {
    agenda_.push_back(std::move(second));
    if (first) agenda_.push_back(std::move(*first));
    return util::Ok();
}

// Split B's hypothesis first (§2.8), then one share-mode cut per run (§5.2).
util::ResultStatus Dispatcher::run(EnterWork w) {
    if (!w.split) {
        w.split = true;
        TRY(split_projections(task_of(w.body).seq, w.block));
    }
    const std::vector<StepRef>& shared = index_.shared_at(w.block);
    if (w.next == shared.size()) {
        return std::visit(
            [&](auto& body) { return next(Work{std::move(body)}); }, w.body);
    }
    Task& body = task_of(w.body);
    StepRef k = shared[w.next];
    if (index_.is_bottom(k)) {
        return next(Task{std::move(body.seq), k, Target::none(), {}});
    }
    TRY_ASSIGN(formula, reader_.read_nnf(k, body.seq.terms()));
    Split split = std::move(body.seq).cut_rule(formula, builder_, sink_);
    split.right.shadow.bind_dual(HypId::of_step(k), split.right.added);
    Task left{std::move(split.left.shadow), k, Target::at(split.left.added), {}};
    body.seq = std::move(split.right.shadow);
    ++w.next;
    return next(TranslateWork{std::move(left)}, std::move(w));
}

util::ResultStatus Dispatcher::split_projections(SequentShadow& seq,
                                                 BlockId b) {
    StepRef opener = index_.opener(b);
    if (opener.idx == kInvalidIdx) return util::Ok();
    const ProofIndex::Component* root = index_.projections(opener);
    if (!root) return util::Ok();
    HypId h = HypId::of_step(opener);
    const DualSlot* slot = seq.dual(h);
    if (!slot || !slot->pos || !slot->pending.empty()) return util::Ok();
    size_t pos = *slot->pos;
    if (seq.dual_shared(pos, h)) {
        TRY_ASSIGN(copy, seq.duplicate(pos, sink_));
        pos = copy;
    }
    seq.unbind_dual(h);
    using Part = std::pair<const ProofIndex::Component*, size_t>;
    std::vector<Part> parts{{root, pos}};
    while (!parts.empty()) {
        auto [part, at] = parts.back();
        parts.pop_back();
        if (!part->split()) {
            for (StepRef s : part->steps) seq.bind_dual(HypId::of_step(s), at);
            continue;
        }
        TRY_ASSIGN(right, seq.or_rule(at, sink_));
        if (part->left) parts.push_back({part->left.get(), at});
        if (part->right) parts.push_back({part->right.get(), right});
    }
    return util::Ok();
}

util::ResultStatus Dispatcher::translate(Task t) {
    // §1.3: a target of 0 needs no position; a target of 1 is closed.
    if (!t.target.is_none()) {
        FormulaHandle demanded = t.seq.at(t.target.pos());
        if (lkr_build::is_falsum(demanded)) {
            t.target = Target::none();
        } else if (lkr_build::is_verum(demanded)) {
            return t.seq.one(t.target.pos(), sink_);
        }
    }
    if (const DualSlot* slot = t.seq.dual(HypId::of_step(t.step))) {
        DualSlot bound = *slot;
        return leaf(std::move(t), std::move(bound));
    }
    return std::visit(
        [&](const auto& op) { return on(op, std::move(t)); },
        index_.instr(t.step));
}

template <typename Op>
util::ResultStatus Dispatcher::on(const Op&, Task t) {
    return MAKE_ERROR << "translate: step #" << t.step.idx
                      << " is not a derivation step";
}

util::ResultStatus Dispatcher::impossible_head(const Task& t) const {
    return MAKE_ERROR << "translate: step #" << t.step.idx
                      << " meets an elimination its result type excludes "
                         "(translator bug)";
}

util::ResultStatus Dispatcher::on(const nd::AndElimL& op, Task t) {
    t.path.push(DemandAndLeft{});
    t.step = op.of;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::AndElimR& op, Task t) {
    t.path.push(DemandAndRight{});
    t.step = op.of;
    return next(std::move(t));
}

// NNF(¬¬A) = A': nothing to demand.
util::ResultStatus Dispatcher::on(const nd::DoubleNegElim& op, Task t) {
    t.step = op.of;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::ForallElim& op, Task t) {
    const TermBinding* term = t.seq.terms().find(StepRef{op.term.idx});
    if (!term) {
        return MAKE_ERROR << "forall_elim #" << t.step.idx << ": binder #"
                          << op.term.idx << " is unbound on this branch";
    }
    t.path.push(DemandInstance{*term});
    t.step = op.formula;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::ImpliesElim& op, Task t) {
    t.path.push(DemandModus{Minor{op.ant}});
    t.step = op.impl;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::IffElimL& op, Task t) {
    t.path.push(DemandIffModus{op.a, Side::Left});
    t.step = op.iff;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::IffElimR& op, Task t) {
    t.path.push(DemandIffModus{op.b, Side::Right});
    t.step = op.iff;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::NotElim& op, Task t) {
    t.path.push(DemandRefute{op.formula});
    t.step = op.negation;
    return next(std::move(t));
}

// Cases needs a step-free tail, which both cases receive (§2.7); else let-cut.
util::ResultStatus Dispatcher::on(const nd::OrElim& op, Task t) {
    if (!t.path.step_free()) return let_cut(std::move(t));
    t.path.push(DemandCases{op.ac, op.bc});
    t.step = op.or_formula;
    return next(std::move(t));
}

util::ResultStatus Dispatcher::on(const nd::ExistsIntro& op, Task t) {
    if (op.witness.has_value()) {
        const TermBinding* witness =
            t.seq.terms().find(StepRef{op.witness->idx});
        if (!witness) {
            return MAKE_ERROR << "exists_intro #" << t.step.idx
                              << ": witness binder #" << op.witness->idx
                              << " is unbound on this branch";
        }
        TermBinding w = *witness;
        return run(ExistsIntroWork{std::move(t), op.body, w});
    }
    // The ∃E closer: eliminate the opener's ∃x.φ with Witness.
    BlockId b = index_.closed_by(t.step);
    const auto& opener = std::get<nd::ExistsElim>(index_.instr(index_.opener(b)));
    t.path.push(DemandWitness{t.step});
    t.step = opener.formula;
    return next(std::move(t));
}

util::Result<Dispatcher::BodyWork> Dispatcher::exists_elim_body(
    Task t, StepRef closer) const {
    BlockId b = index_.closed_by(closer);
    StepRef body = index_.target(b);
    if (!index_.requantifies(closer)) {
        t.step = body;
        return BodyWork{TranslateWork{std::move(t)}};
    }
    const TermBinding* witness = t.seq.terms().find(index_.opener(b));
    if (!witness) {
        return MAKE_ERROR << "exists_elim #" << closer.idx
                          << ": the block's witness is unbound";
    }
    TermBinding w = *witness;
    t.step = closer;
    return BodyWork{ExistsIntroWork{std::move(t), body, w}};
}

util::ResultStatus Dispatcher::on(const nd::NotIntro& op, Task t) {
    return closer(std::move(t), op.bottom, /*not_intro=*/true);
}

util::ResultStatus Dispatcher::on(const nd::ClassicalAbsurd& op, Task t) {
    return closer(std::move(t), op.bottom, /*not_intro=*/false);
}

// The assumption's dual is the closer's own result (§2.3).
util::ResultStatus Dispatcher::closer(Task t, StepRef bottom, bool not_intro) {
    BlockId b = index_.closed_by(t.step);
    StepRef assumption = index_.opener(b);
    std::optional<size_t> result;
    if (!t.target.is_none()) result = t.target.pos();

    std::optional<Work> first;
    if (t.path.empty()) {
        t.seq.bind_dual(HypId::of_step(assumption), result);
    } else if (auto* r = std::get_if<DemandRefute>(&t.path.head());
               r && not_intro) {
        StepRef refuter = r->refuter;
        TRY_ASSIGN(bound, bind(std::move(t.seq), assumption, Minor{refuter}));
        t.seq = std::move(bound.seq);
        first = std::move(bound.first);
    } else if (t.path.projection_only()) {
        t.seq.bind_dual(HypId::of_step(assumption), result, std::move(t.path));
    } else {
        return let_cut(std::move(t));
    }
    return next(std::move(first),
                EnterWork{b, 0, TranslateWork{Task{std::move(t.seq), bottom,
                                                   Target::none(), {}}}});
}

util::ResultStatus Dispatcher::on(const nd::BottomElim& op, Task t) {
    return next(Task{std::move(t.seq), op.bottom, Target::none(), {}});
}

util::ResultStatus Dispatcher::on(const nd::Use& op, Task t) {
    lkr::CloseByLemma close{};
    close.target      = op.axiom;
    close.source_name = op.source_name;
    return lemma(std::move(t), std::move(close));
}

util::ResultStatus Dispatcher::on(const nd::SchemaInst& op, Task t) {
    lkr::CloseByLemma close{};
    close.target = op.data;
    return lemma(std::move(t), std::move(close));
}

util::ResultStatus Dispatcher::lemma(Task t, lkr::CloseByLemma close) {
    TRY_ASSIGN(lemma_nnf, reader_.read_nnf(t.step, t.seq.terms()));
    Split split = std::move(t.seq).cut_rule(lemma_nnf, builder_, sink_);
    split.left.shadow.close_by_lemma(std::move(close), sink_);
    return next(LeftRulesWork{std::move(split.right.shadow), split.right.added,
                              t.target, std::move(t.path)});
}

util::ResultStatus Dispatcher::on(const nd::Assume&, Task t) {
    return MAKE_ERROR << "translate: hypothesis #" << t.step.idx
                      << " has no dual in this branch";
}

util::ResultStatus Dispatcher::on(const nd::ExistsElim&, Task t) {
    return MAKE_ERROR << "translate: ∃E opener #" << t.step.idx
                      << " has no dual in this branch";
}

util::ResultStatus Dispatcher::let_cut(Task t) {
    TRY_ASSIGN(result_nnf, reader_.read_nnf(t.step, t.seq.terms()));
    Split split = std::move(t.seq).cut_rule(result_nnf, builder_, sink_);
    return next(
        TranslateWork{Task{std::move(split.left.shadow), t.step,
                           Target::at(split.left.added), {}}},
        LeftRulesWork{std::move(split.right.shadow), split.right.added,
                      t.target, std::move(t.path)});
}

util::Result<Dispatcher::Bound> Dispatcher::bind(SequentShadow seq,
                                                 StepRef hypothesis,
                                                 const Minor& m) {
    HypId h = HypId::of_step(hypothesis);
    if (auto* k = std::get_if<HypId>(&m)) {
        const DualSlot* slot = seq.dual(*k);
        if (!slot) return MAKE_ERROR << "bind: minor hypothesis has no dual";
        std::optional<size_t> pos = slot->pos;
        seq.bind_dual(h, pos);
        return Bound{std::move(seq), std::nullopt};
    }
    TRY_ASSIGN(formula, reader_.read_nnf(hypothesis, seq.terms()));
    Split split = std::move(seq).cut_rule(formula, builder_, sink_);
    split.right.shadow.bind_dual(h, split.right.added);
    Work first = TranslateWork{Task{std::move(split.left.shadow),
                                    std::get<StepRef>(m),
                                    Target::at(split.left.added), {}}};
    return Bound{std::move(split.right.shadow), std::move(first)};
}

void Dispatcher::need(const SequentShadow& seq, StepRef s,
                      std::vector<size_t>& out) const {
    if (const DualSlot* slot = seq.dual(HypId::of_step(s))) {
        if (slot->pos) out.push_back(*slot->pos);
        return;
    }
    need_free(seq, index_.free_hypotheses(s), out);
}

void Dispatcher::need(const SequentShadow& seq, const Minor& m,
                      std::vector<size_t>& out) const {
    if (auto* s = std::get_if<StepRef>(&m)) return need(seq, *s, out);
    if (const DualSlot* slot = seq.dual(std::get<HypId>(m))) {
        if (slot->pos) out.push_back(*slot->pos);
    }
}

void Dispatcher::need(const SequentShadow& seq, const DemandPath& path,
                      std::vector<size_t>& out) const {
    path.for_each([&](const Demand& d) {
        if (auto* m = std::get_if<DemandModus>(&d)) {
            need(seq, m->antecedent, out);
        } else if (auto* i = std::get_if<DemandIffModus>(&d)) {
            need(seq, i->operand, out);
        } else if (auto* r = std::get_if<DemandRefute>(&d)) {
            need(seq, r->refuter, out);
        } else if (auto* c = std::get_if<DemandCases>(&d)) {
            need(seq, c->if_left, out);
            need(seq, c->if_right, out);
        } else if (auto* w = std::get_if<DemandWitness>(&d)) {
            BlockId b = index_.closed_by(w->closer);
            need_free(seq, index_.free_in_block(b), out);
        }
    });
}

void Dispatcher::need_free(const SequentShadow& seq,
                           const std::vector<uint32_t>& free,
                           std::vector<size_t>& out) const {
    std::vector<uint32_t> work(free.begin(), free.end());
    std::unordered_set<uint32_t> seen(free.begin(), free.end());
    while (!work.empty()) {
        StepRef e{work.back()};
        work.pop_back();
        if (const DualSlot* slot = seq.dual(HypId::of_step(e))) {
            if (slot->pos) out.push_back(*slot->pos);
        } else if (index_.is_shared(e)) {
            for (uint32_t x : index_.free_hypotheses(e)) {
                if (seen.insert(x).second) work.push_back(x);
            }
        } else if (auto root = index_.view_root(e)) {
            if (seen.insert(root->idx).second) work.push_back(root->idx);
        }
    }
}

}  // namespace logic::proof::translate::nd_to_lkr
