#pragma once

// Shape predicates on NNF formulas.

#include "src/core/formula.h"

namespace logic::proof::lkr_build {

inline bool has_op(FormulaHandle h, Op op) {
    const Formula& f = h.get();
    if (f.is_compound()) return f.as_compound().op == op;
    if (f.is_quantified()) return f.as_quantified().op == op;
    return false;
}

inline bool is_falsum(FormulaHandle h) { return has_op(h, Op::Bottom); }

inline bool is_verum(FormulaHandle h) {
    return has_op(h, Op::Not) && is_falsum(h.get().as_compound().left);
}

inline bool is_atom(FormulaHandle h) {
    return h.get().is_predicate() || h.get().is_schema_var();
}

inline bool is_literal(FormulaHandle h) {
    return is_atom(h) ||
           (has_op(h, Op::Not) && is_atom(h.get().as_compound().left));
}

}  // namespace logic::proof::lkr_build
