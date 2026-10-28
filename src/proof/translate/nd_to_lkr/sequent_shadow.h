#pragma once

// The translator's mirror of the verifier's goal: an lkr_build::Sequent plus
// each hypothesis' dual slot and σ. OutputGate re-verifies what it emits.

#include "demand.h"

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr_build/op_sink.h"
#include "src/proof/lkr_build/sequent.h"
#include "src/util/error.h"

#include <cstddef>
#include <optional>
#include <unordered_map>
#include <utility>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

using lkr_build::OpSink;

// σ: the LKR term each ND binder stands for on this branch.
class TermEnv {
public:
    void bind(StepRef binder, TermBinding binding) {
        bindings_[binder] = binding;
    }
    const TermBinding* find(StepRef binder) const {
        auto it = bindings_.find(binder);
        return it == bindings_.end() ? nullptr : &it->second;
    }

private:
    std::unordered_map<StepRef, TermBinding> bindings_;
};

// Entry `pos` holds NNF(¬h) after `pending` (§1.5); no position when it is 0.
struct DualSlot {
    std::optional<size_t> pos;
    DemandPath            pending;
};

struct Split;

class SequentShadow {
public:
    explicit SequentShadow(FormulaHandle goal_nnf) : seq_(goal_nnf) {}

    size_t        size() const { return seq_.size(); }
    FormulaHandle at(size_t pos) const { return seq_.at(pos); }

    // A position holding 0 binds no position.
    void bind_dual(HypId h, std::optional<size_t> pos,
                   DemandPath pending = {});
    void unbind_dual(HypId h) { duals_.erase(h); }
    const DualSlot* dual(HypId h) const;
    bool dual_shared(size_t pos, HypId h) const;

    TermEnv&       terms() { return terms_; }
    const TermEnv& terms() const { return terms_; }

    util::Result<size_t> or_rule(size_t pos, OpSink& sink) {
        return seq_.or_rule(pos, sink);
    }

    util::Result<TermBinding> forall_rule(size_t pos, FormulaBuilder& builder,
                                          OpSink& sink) {
        return seq_.forall_rule(pos, builder.enter_scope(), builder, sink);
    }

    util::ResultStatus exists_rule(size_t pos, const TermBinding& term,
                                   FormulaBuilder& builder, OpSink& sink) {
        return seq_.exists_rule(pos, term, builder, sink);
    }

    util::Result<size_t> duplicate(size_t pos, OpSink& sink) {
        return seq_.duplicate(pos, sink);
    }

    util::ResultStatus one(size_t pos, OpSink& sink) const {
        return seq_.one(pos, sink);
    }

    void close_by_lemma(lkr::CloseByLemma op, OpSink& sink) const {
        seq_.close_by_lemma(std::move(op), sink);
    }

    // Reserves the identity's eigenvariables from `builder` (Theorem E1).
    util::ResultStatus identity(size_t a, size_t b, FormulaBuilder& builder,
                                OpSink& sink) &&;

    util::Result<Split> and_rule(size_t principal,
                                 const std::vector<size_t>& left_needs,
                                 const std::vector<size_t>& right_needs,
                                 OpSink& sink) &&;

    Split cut_rule(FormulaHandle formula_nnf, FormulaBuilder& builder,
                   OpSink& sink) &&;

private:
    explicit SequentShadow(lkr_build::Sequent seq) : seq_(std::move(seq)) {}

    // Each premise gets the slots whose entries moved to it, and σ.
    Split distribute(lkr_build::Split split) &&;

    lkr_build::Sequent                             seq_;
    std::unordered_map<HypId, DualSlot, HypIdHash> duals_;
    TermEnv                                        terms_;
};

struct Premise {
    SequentShadow shadow;
    // moved[p]: where parent entry p is here, if it came here.
    std::vector<std::optional<size_t>> moved;
    size_t added{0};

    Target remap(Target t) const {
        return t.is_none() ? t : Target::at(*moved[t.pos()]);
    }
};

struct Split {
    Premise left;
    Premise right;
};

}  // namespace logic::proof::translate::nd_to_lkr
