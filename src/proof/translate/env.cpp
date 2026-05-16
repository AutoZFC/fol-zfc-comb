#include "env.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <atomic>
#include <utility>

namespace logic::proof::translate {

Env::Env() = default;

SequentEntry Env::mint_id() {
    static std::atomic<uint64_t> g_counter{0};
    SequentEntry e;
    e.id = g_counter.fetch_add(1, std::memory_order_relaxed);
    return e;
}

void Env::rebuild_index() {
    id_to_pos_.clear();
    id_to_pos_.reserve(pos_to_id_.size());
    for (size_t i = 0; i < pos_to_id_.size(); ++i) {
        id_to_pos_[pos_to_id_[i]] = i;
    }
}

SequentEntry Env::seed(FormulaHandle f) {
    return push(f);
}

SequentEntry Env::push(FormulaHandle f) {
    SequentEntry e = mint_id();
    entries_.push_back(f);
    pos_to_id_.push_back(e);
    id_to_pos_[e] = entries_.size() - 1;
    return e;
}

util::Result<size_t> Env::position_of(SequentEntry e) const {
    auto it = id_to_pos_.find(e);
    if (it == id_to_pos_.end()) {
        return MAKE_ERROR << "Env::position_of: SequentEntry id=" << e.id
                          << " not in this Env";
    }
    return it->second;
}

util::Result<FormulaHandle> Env::formula_at(SequentEntry e) const {
    TRY_ASSIGN(pos, position_of(e));
    return entries_[pos];
}

util::Result<SequentEntry> Env::entry_at(size_t pos) const {
    if (pos >= pos_to_id_.size()) {
        return MAKE_ERROR << "Env::entry_at: position " << pos
                          << " out of range (size " << pos_to_id_.size() << ")";
    }
    return pos_to_id_[pos];
}

util::Result<SequentEntry> Env::apply_or(SequentEntry principal) {
    TRY_ASSIGN(pos, position_of(principal));
    const Formula& f = entries_[pos].get();
    if (!f.is_compound() || f.as_compound().op != Op::Or) {
        return MAKE_ERROR << "Env::apply_or: principal (id=" << principal.id
                          << ") is not (φ ∨ ψ)";
    }
    FormulaHandle phi = f.as_compound().left;
    FormulaHandle psi = f.as_compound().right;
    entries_[pos] = phi;          // principal slot now holds φ; same SequentEntry
    return push(psi);             // ψ at end with fresh SequentEntry
}

util::ResultStatus Env::apply_forall(SequentEntry principal,
                                       var_index   eigen,
                                       FormulaBuilder& builder) {
    TRY_ASSIGN(pos, position_of(principal));
    const Formula& f = entries_[pos].get();
    if (!f.is_quantified() || f.as_quantified().op != Op::Forall) {
        return MAKE_ERROR << "Env::apply_forall: principal (id=" << principal.id
                          << ") is not ∀x.φ";
    }
    FormulaHandle inst = builder.instantiate_quantifier_body(
        f.as_quantified().body, Term::fixed(eigen));
    entries_[pos] = inst;
    return util::Ok();
}

util::ResultStatus Env::apply_exists(SequentEntry principal,
                                       Term        witness,
                                       FormulaBuilder& builder) {
    TRY_ASSIGN(pos, position_of(principal));
    const Formula& f = entries_[pos].get();
    if (!f.is_quantified() || f.as_quantified().op != Op::Exists) {
        return MAKE_ERROR << "Env::apply_exists: principal (id=" << principal.id
                          << ") is not ∃x.φ";
    }
    FormulaHandle inst = builder.instantiate_quantifier_body(
        f.as_quantified().body, witness);
    entries_[pos] = inst;
    return util::Ok();
}

EnvCutResult Env::apply_cut(FormulaHandle phi_nnf,
                              FormulaBuilder& builder) const {
    Env left  = *this;   // shared id counter via shared_ptr
    Env right = *this;
    FormulaHandle neg_phi_nnf = builder.to_nnf(builder.make_not(phi_nnf));
    SequentEntry left_phi      = left.push(phi_nnf);
    SequentEntry right_neg_phi = right.push(neg_phi_nnf);
    return EnvCutResult{std::move(left), std::move(right), left_phi, right_neg_phi};
}

util::Result<EnvAndResult> Env::apply_and(
    SequentEntry                          principal,
    const std::set<SequentEntry>&         left_needs,
    const std::set<SequentEntry>&         right_needs) const
{
    TRY_ASSIGN(principal_pos, position_of(principal));
    const Formula& f = entries_[principal_pos].get();
    if (!f.is_compound() || f.as_compound().op != Op::And) {
        return MAKE_ERROR << "Env::apply_and: principal (id=" << principal.id
                          << ") is not (φ ∧ ψ)";
    }
    FormulaHandle phi = f.as_compound().left;
    FormulaHandle psi = f.as_compound().right;

    // Disjointness of left_needs and right_needs.
    for (SequentEntry e : right_needs) {
        if (left_needs.count(e)) {
            return MAKE_ERROR
                << "Env::apply_and: SequentEntry id=" << e.id
                << " appears in both left_needs and right_needs (Weaken first)";
        }
    }
    // Principal not in either set.
    if (left_needs.count(principal) || right_needs.count(principal)) {
        return MAKE_ERROR << "Env::apply_and: principal (id=" << principal.id
                          << ") is in left/right_needs";
    }
    // All declared entries are in this Env.
    for (SequentEntry e : left_needs) {
        if (!id_to_pos_.count(e)) {
            return MAKE_ERROR << "Env::apply_and: left_needs entry id="
                              << e.id << " not in Env";
        }
    }
    for (SequentEntry e : right_needs) {
        if (!id_to_pos_.count(e)) {
            return MAKE_ERROR << "Env::apply_and: right_needs entry id="
                              << e.id << " not in Env";
        }
    }

    Env left_env;
    Env right_env;
    std::vector<size_t> left_partition;

    for (size_t i = 0; i < entries_.size(); ++i) {
        if (i == principal_pos) continue;
        SequentEntry e = pos_to_id_[i];
        bool to_right = right_needs.count(e) > 0;
        if (to_right) {
            right_env.entries_.push_back(entries_[i]);
            right_env.pos_to_id_.push_back(e);
        } else {
            left_env.entries_.push_back(entries_[i]);
            left_env.pos_to_id_.push_back(e);
            left_partition.push_back(i);
        }
    }
    left_env.rebuild_index();
    right_env.rebuild_index();

    SequentEntry left_phi  = left_env.push(phi);
    SequentEntry right_psi = right_env.push(psi);

    return EnvAndResult{std::move(left_env), std::move(right_env),
                         left_phi, right_psi, std::move(left_partition)};
}

}  // namespace logic::proof::translate
