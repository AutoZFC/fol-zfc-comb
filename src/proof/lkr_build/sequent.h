#pragma once

// A mirror of LKRVerifier's current goal (COMPACT_LKR_DESIGN.md §3). Each
// rule applies the verifier's transition and writes its op; a failed rule
// writes nothing. Close a split's LEFT premise before its RIGHT.

#include "op_sink.h"

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/util/error.h"

#include <cstddef>
#include <optional>
#include <vector>

namespace logic::proof::lkr_build {

// lkr_ref is the index of the Forall that bound `value`.
struct TermBinding {
    TermRef lkr_ref{};
    Term    value{};
};

struct Split;

class Sequent {
public:
    explicit Sequent(FormulaHandle goal_nnf);

    size_t        size() const { return entries_.size(); }
    FormulaHandle at(size_t pos) const { return entries_[pos]; }

    util::Result<size_t> or_rule(size_t pos, OpSink& sink);

    util::Result<TermBinding> forall_rule(size_t pos, var_index eigen,
                                          FormulaBuilder& builder,
                                          OpSink& sink);

    util::ResultStatus exists_rule(size_t pos, const TermBinding& term,
                                   FormulaBuilder& builder, OpSink& sink);

    util::Result<size_t> duplicate(size_t pos, OpSink& sink);

    util::ResultStatus contraction(size_t i, size_t j, OpSink& sink);

    util::ResultStatus exchange(size_t i, size_t j, OpSink& sink);

    util::ResultStatus weakening(size_t pos, OpSink& sink);

    util::ResultStatus axiom_lit(size_t a, size_t b, OpSink& sink) const;
    util::ResultStatus one(size_t pos, OpSink& sink) const;
    void close_by_lemma(lkr::CloseByLemma op, OpSink& sink) const;

    util::ResultStatus identity(size_t a, size_t b, var_index first_eigen,
                                FormulaBuilder& builder, OpSink& sink) &&;

    util::Result<Split> and_split(size_t principal,
                                  std::vector<size_t> left_partition,
                                  OpSink& sink) &&;

    // Duplicates the entries both sides need, the copy going RIGHT.
    util::Result<Split> and_rule(size_t principal,
                                 const std::vector<size_t>& left_needs,
                                 const std::vector<size_t>& right_needs,
                                 OpSink& sink) &&;

    Split cut_rule(FormulaHandle formula, FormulaBuilder& builder,
                   OpSink& sink) &&;

private:
    explicit Sequent(std::vector<FormulaHandle> entries)
        : entries_(std::move(entries)) {}

    util::ResultStatus require(size_t pos, const char* rule) const;

    std::vector<FormulaHandle> entries_;
};

struct Premise {
    Sequent seq;
    // moved[p]: where parent entry p is here, if it came here.
    std::vector<std::optional<size_t>> moved;
    size_t added{0};
};

struct Split {
    Premise left;
    Premise right;
};

}  // namespace logic::proof::lkr_build
