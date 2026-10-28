#include "expand.h"

#include "op_sink.h"
#include "sequent.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

namespace logic::proof::lkr_build {

namespace {

class Replay {
public:
    Replay(FormulaBuilder& builder, LkrSink& sink, std::vector<Sequent>& open,
           std::vector<std::optional<TermBinding>>& bound, size_t index,
           Sequent seq)
        : builder_(builder), sink_(sink), open_(open), bound_(bound),
          index_(index), seq_(std::move(seq)) {}

    util::ResultStatus operator()(const Identity& id) {
        return std::move(seq_).identity(id.a, id.b, id.first_eigen, builder_,
                                        sink_);
    }
    util::ResultStatus operator()(const lkr::Instr& op) {
        return std::visit([this](const auto& o) { return (*this)(o); }, op);
    }

    util::ResultStatus operator()(const lkr::AxiomLit& op) {
        return seq_.axiom_lit(op.lit_a, op.lit_b, sink_);
    }
    util::ResultStatus operator()(const lkr::One& op) {
        return seq_.one(op.idx, sink_);
    }
    util::ResultStatus operator()(const lkr::CloseByLemma& op) {
        seq_.close_by_lemma(op, sink_);
        return util::Ok();
    }
    util::ResultStatus operator()(const lkr::Exchange& op) {
        TRY(seq_.exchange(op.i, op.j, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::Weakening& op) {
        TRY(seq_.weakening(op.idx, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::Duplicate& op) {
        TRY(seq_.duplicate(op.src, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::Contraction& op) {
        TRY(seq_.contraction(op.i, op.j, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::Or& op) {
        TRY(seq_.or_rule(op.principal, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::Forall& op) {
        TRY_ASSIGN(term, seq_.forall_rule(op.principal, op.eigen, builder_,
                                          sink_));
        bound_[index_] = term;
        return keep();
    }
    util::ResultStatus operator()(const lkr::Exists& op) {
        uint32_t w = op.witness.idx;
        if (w >= index_ || !bound_[w]) {
            return MAKE_ERROR << "exists: witness %" << w
                              << " is not an earlier Forall";
        }
        TRY(seq_.exists_rule(op.principal, *bound_[w], builder_, sink_));
        return keep();
    }
    util::ResultStatus operator()(const lkr::And& op) {
        TRY_ASSIGN(split, std::move(seq_).and_split(op.principal,
                                                    op.left_partition, sink_));
        return branch(std::move(split));
    }
    util::ResultStatus operator()(const lkr::Cut& op) {
        const FormulaHandle* formula =
            std::get_if<FormulaHandle>(&op.cut_formula);
        if (!formula) {
            return MAKE_ERROR << "cut: the formula is a deferred AST; compact "
                                 "programs carry resolved formulas";
        }
        if (!formula->valid()) return MAKE_ERROR << "cut: empty formula";
        return branch(std::move(seq_).cut_rule(*formula, builder_, sink_));
    }

private:
    util::ResultStatus keep() {
        open_.push_back(std::move(seq_));
        return util::Ok();
    }
    util::ResultStatus branch(Split split) {
        open_.push_back(std::move(split.right.seq));
        open_.push_back(std::move(split.left.seq));
        return util::Ok();
    }

    FormulaBuilder&                          builder_;
    LkrSink&                                 sink_;
    std::vector<Sequent>&                    open_;
    std::vector<std::optional<TermBinding>>& bound_;
    size_t                                   index_;
    Sequent                                  seq_;
};

}  // namespace

util::Result<Program<lkr::Instr>> ExpandIdentities::apply(
    const Program<CompactInstr>& in)
{
    FormulaBuilder builder(ctx_);
    Program<lkr::Instr> out;
    out.claim_name = in.claim_name;
    LkrSink sink(out.instrs);
    std::vector<Sequent> open{Sequent(builder.to_nnf(goal_))};
    std::vector<std::optional<TermBinding>> bound(in.instrs.size());
    for (size_t i = 0; i < in.instrs.size(); ++i) {
        if (open.empty()) {
            return MAKE_ERROR << "expand: instr %" << i << ": no open goal";
        }
        Sequent seq = std::move(open.back());
        open.pop_back();
        Replay replay(builder, sink, open, bound, i, std::move(seq));
        auto status = std::visit(replay, in.instrs[i]);
        if (status.is_error()) {
            return MAKE_ERROR << "expand: instr %" << i << ": "
                              << status.error().to_string();
        }
    }
    if (!open.empty()) {
        return MAKE_ERROR << "expand: " << open.size()
                          << " goal(s) left open";
    }
    return out;
}

}  // namespace logic::proof::lkr_build
