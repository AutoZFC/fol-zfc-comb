#include "build_target.h"

namespace logic::proof::translate::lkr_to_comb {

namespace {

size_t count_vertices(FormulaHandle f) {
    const Formula& fm = f.get();
    if (fm.is_predicate() || fm.is_schema_var()) return 1;
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        if (c.op == Op::Not) return 1;
        if (c.op == Op::And || c.op == Op::Or) {
            return count_vertices(c.left) + count_vertices(c.right);
        }
        return 0;
    }
    if (fm.is_quantified()) {
        return 1 + count_vertices(fm.as_quantified().body);
    }
    return 0;
}

}  // namespace

util::Result<SequentTarget> build_sequent_target(
    FormulaBuilder&                       builder,
    const std::vector<FormulaHandle>&     entries)
{
    if (entries.empty()) {
        return MAKE_ERROR
            << "build_sequent_target: empty sequent (unprovable)";
    }

    // Assemble the left-associated disjunction
    // (((e_0 ∨ e_1) ∨ e_2) ∨ …). Fograph's pre-order then visits
    // e_0, e_1, …, e_n in sequence (`∨` adds no cograph edges), so
    // vertex IDs come out as: [e_0's vertices] [e_1's] … [e_n's].
    FormulaHandle disj = entries[0];
    for (size_t k = 1; k < entries.size(); ++k) {
        disj = builder.make_or(disj, entries[k]);
    }

    SequentTarget out;
    out.target = comb::Fograph(disj);

    out.entry_positions.resize(entries.size());
    size_t cursor = 0;
    for (size_t k = 0; k < entries.size(); ++k) {
        size_t n = count_vertices(entries[k]);
        out.entry_positions[k].reserve(n);
        for (size_t i = 0; i < n; ++i) {
            out.entry_positions[k].push_back(cursor + i);
        }
        cursor += n;
    }
    if (cursor != out.target.labels.size()) {
        return MAKE_ERROR
            << "build_sequent_target: cursor (" << cursor
            << ") != target vertex count (" << out.target.labels.size()
            << "); count_vertices mismatched Fograph builder";
    }
    return out;
}

}  // namespace logic::proof::translate::lkr_to_comb
