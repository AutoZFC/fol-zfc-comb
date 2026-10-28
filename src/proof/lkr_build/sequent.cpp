#include "sequent.h"

#include "nnf_shapes.h"

#include <utility>

namespace logic::proof::lkr_build {

Sequent::Sequent(FormulaHandle goal_nnf) : entries_{goal_nnf} {}

util::ResultStatus Sequent::require(size_t pos, const char* rule) const {
    if (pos >= entries_.size()) {
        return MAKE_ERROR << rule << ": entry " << pos
                          << " out of range (size " << entries_.size() << ")";
    }
    return util::Ok();
}

util::Result<size_t> Sequent::or_rule(size_t pos, OpSink& sink) {
    TRY(require(pos, "or_rule"));
    if (!has_op(entries_[pos], Op::Or)) {
        return MAKE_ERROR << "or_rule: entry " << pos << " is not φ ∨ θ";
    }
    const Compound& disj = entries_[pos].get().as_compound();
    FormulaHandle phi   = disj.left;
    FormulaHandle theta = disj.right;
    sink.emit(lkr::Or{{}, pos});
    entries_[pos] = phi;
    entries_.push_back(theta);
    return entries_.size() - 1;
}

util::Result<TermBinding> Sequent::forall_rule(
    size_t pos, var_index eigen, FormulaBuilder& builder, OpSink& sink)
{
    TRY(require(pos, "forall_rule"));
    if (!has_op(entries_[pos], Op::Forall)) {
        return MAKE_ERROR << "forall_rule: entry " << pos << " is not ∀x.φ";
    }
    FormulaHandle body = entries_[pos].get().as_quantified().body;
    TermBinding bound{sink.next_ref(), Term::fixed(eigen)};
    sink.emit(lkr::Forall{{}, pos, eigen});
    entries_[pos] = builder.instantiate_quantifier_body(body, bound.value);
    return bound;
}

util::ResultStatus Sequent::exists_rule(
    size_t pos, const TermBinding& term, FormulaBuilder& builder,
    OpSink& sink)
{
    TRY(require(pos, "exists_rule"));
    if (!has_op(entries_[pos], Op::Exists)) {
        return MAKE_ERROR << "exists_rule: entry " << pos << " is not ∃x.φ";
    }
    FormulaHandle body = entries_[pos].get().as_quantified().body;
    sink.emit(lkr::Exists{{}, pos, term.lkr_ref});
    entries_[pos] = builder.instantiate_quantifier_body(body, term.value);
    return util::Ok();
}

util::Result<size_t> Sequent::duplicate(size_t pos, OpSink& sink) {
    TRY(require(pos, "duplicate"));
    FormulaHandle copy = entries_[pos];
    sink.emit(lkr::Duplicate{{}, pos});
    entries_.push_back(copy);
    return entries_.size() - 1;
}

util::ResultStatus Sequent::contraction(size_t i, size_t j, OpSink& sink) {
    TRY(require(i, "contraction"));
    TRY(require(j, "contraction"));
    if (i == j) return MAKE_ERROR << "contraction: i and j must differ";
    if (entries_[i] != entries_[j]) {
        return MAKE_ERROR << "contraction: entries " << i << " and " << j
                          << " differ";
    }
    sink.emit(lkr::Contraction{{}, i, j});
    entries_.erase(entries_.begin() + j);
    return util::Ok();
}

// As in the verifier, exchanging an entry with itself changes nothing.
util::ResultStatus Sequent::exchange(size_t i, size_t j, OpSink& sink) {
    if (i != j) {
        TRY(require(i, "exchange"));
        TRY(require(j, "exchange"));
        std::swap(entries_[i], entries_[j]);
    }
    sink.emit(lkr::Exchange{{}, i, j});
    return util::Ok();
}

util::ResultStatus Sequent::weakening(size_t pos, OpSink& sink) {
    TRY(require(pos, "weakening"));
    sink.emit(lkr::Weakening{{}, pos});
    entries_.erase(entries_.begin() + pos);
    return util::Ok();
}

util::ResultStatus Sequent::axiom_lit(size_t a, size_t b,
                                      OpSink& sink) const {
    TRY(require(a, "axiom_lit"));
    TRY(require(b, "axiom_lit"));
    if (a == b) return MAKE_ERROR << "axiom_lit: positions coincide";
    sink.emit(lkr::AxiomLit{{}, a, b});
    return util::Ok();
}

util::ResultStatus Sequent::one(size_t pos, OpSink& sink) const {
    TRY(require(pos, "one"));
    if (!is_verum(entries_[pos])) {
        return MAKE_ERROR << "one: entry " << pos << " is not ¬⊥";
    }
    sink.emit(lkr::One{{}, pos});
    return util::Ok();
}

void Sequent::close_by_lemma(lkr::CloseByLemma op, OpSink& sink) const {
    sink.emit(std::move(op));
}

util::ResultStatus Sequent::identity(size_t a, size_t b,
                                     var_index first_eigen,
                                     FormulaBuilder& builder,
                                     OpSink& sink) && {
    TRY(require(a, "identity"));
    TRY(require(b, "identity"));
    if (a == b) return MAKE_ERROR << "identity: positions coincide";
    return sink.identity(std::move(*this), a, b, first_eigen, builder);
}

util::Result<Split> Sequent::and_split(size_t principal,
                                       std::vector<size_t> left_partition,
                                       OpSink& sink) && {
    TRY(require(principal, "and"));
    if (!has_op(entries_[principal], Op::And)) {
        return MAKE_ERROR << "and: entry " << principal << " is not φ ∧ θ";
    }
    std::vector<bool> to_left(entries_.size(), false);
    for (size_t p : left_partition) {
        TRY(require(p, "and partition"));
        if (p == principal) {
            return MAKE_ERROR << "and: the partition holds the principal "
                              << principal;
        }
        if (to_left[p]) {
            return MAKE_ERROR << "and: the partition repeats " << p;
        }
        to_left[p] = true;
    }
    const Compound& conj = entries_[principal].get().as_compound();
    FormulaHandle phi   = conj.left;
    FormulaHandle theta = conj.right;
    sink.emit(lkr::And{{}, principal, std::move(left_partition)});

    Split split{Premise{Sequent(std::vector<FormulaHandle>{}), {}, 0},
                Premise{Sequent(std::vector<FormulaHandle>{}), {}, 0}};
    split.left.moved.resize(entries_.size());
    split.right.moved.resize(entries_.size());
    for (size_t p = 0; p < entries_.size(); ++p) {
        if (p == principal) continue;
        Premise& side = to_left[p] ? split.left : split.right;
        side.moved[p] = side.seq.entries_.size();
        side.seq.entries_.push_back(entries_[p]);
    }
    split.left.added = split.left.seq.entries_.size();
    split.left.seq.entries_.push_back(phi);
    split.right.added = split.right.seq.entries_.size();
    split.right.seq.entries_.push_back(theta);
    return split;
}

util::Result<Split> Sequent::and_rule(
    size_t principal,
    const std::vector<size_t>& left_needs,
    const std::vector<size_t>& right_needs,
    OpSink& sink) &&
{
    TRY(require(principal, "and"));
    if (!has_op(entries_[principal], Op::And)) {
        return MAKE_ERROR << "and: entry " << principal << " is not φ ∧ θ";
    }
    const size_t parent_size = entries_.size();
    std::vector<bool> to_left(parent_size, false);
    std::vector<bool> to_right(parent_size, false);
    for (const auto* needs : {&left_needs, &right_needs}) {
        for (size_t p : *needs) TRY(require(p, "and needs"));
    }
    for (size_t p : left_needs) to_left[p] = true;
    for (size_t p : right_needs) to_right[p] = true;
    to_left[principal] = to_right[principal] = false;

    std::vector<std::optional<size_t>> copy_of(parent_size);
    for (size_t p = 0; p < parent_size; ++p) {
        if (!to_left[p] || !to_right[p]) continue;
        TRY_ASSIGN(copy, duplicate(p, sink));
        copy_of[p] = copy;
    }
    std::vector<size_t> left_partition;
    for (size_t p = 0; p < parent_size; ++p) {
        if (to_left[p]) left_partition.push_back(p);
    }
    TRY_ASSIGN(split, std::move(*this).and_split(
        principal, std::move(left_partition), sink));
    for (size_t p = 0; p < parent_size; ++p) {
        if (copy_of[p]) split.right.moved[p] = split.right.moved[*copy_of[p]];
    }
    split.left.moved.resize(parent_size);
    split.right.moved.resize(parent_size);
    return split;
}

Split Sequent::cut_rule(FormulaHandle formula, FormulaBuilder& builder,
                        OpSink& sink) && {
    FormulaHandle phi      = builder.to_nnf(formula);
    FormulaHandle negation = builder.to_nnf(builder.make_not(phi));
    sink.emit(lkr::Cut{{}, formula});

    const size_t n = entries_.size();
    std::vector<std::optional<size_t>> kept(n);
    for (size_t p = 0; p < n; ++p) kept[p] = p;
    Split split{Premise{Sequent(entries_), kept, n},
                Premise{Sequent(std::move(entries_)), std::move(kept), n}};
    split.left.seq.entries_.push_back(phi);
    split.right.seq.entries_.push_back(negation);
    return split;
}

}  // namespace logic::proof::lkr_build
