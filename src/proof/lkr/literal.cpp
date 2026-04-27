#include "literal.h"

namespace logic::proof::lkr {

namespace {

bool is_positive_atom(FormulaHandle h) {
    if (!h.valid()) return false;
    const Formula& f = h.get();
    return f.is_predicate() || f.is_schema_var();
}

}  // namespace

bool is_atomic_literal(FormulaHandle h) {
    if (!h.valid()) return false;
    const Formula& f = h.get();
    if (is_positive_atom(h)) return true;
    if (f.is_compound() && f.as_compound().op == Op::Not) {
        return is_positive_atom(f.as_compound().left);
    }
    return false;
}

bool is_top_literal(FormulaHandle h) {
    if (!h.valid()) return false;
    const Formula& f = h.get();
    if (!f.is_compound() || f.as_compound().op != Op::Not) return false;
    FormulaHandle inner = f.as_compound().left;
    if (!inner.valid()) return false;
    const Formula& g = inner.get();
    return g.is_compound() && g.as_compound().op == Op::Bottom;
}

bool is_dual(FormulaHandle a, FormulaHandle b) {
    if (!a.valid() || !b.valid()) return false;
    const Formula& fa = a.get();
    const Formula& fb = b.get();
    // Case 1: a positive, b negative of same atom.
    if (is_positive_atom(a)) {
        if (fb.is_compound() && fb.as_compound().op == Op::Not) {
            return fb.as_compound().left == a;
        }
        return false;
    }
    // Case 2: b positive, a negative of same atom.
    if (is_positive_atom(b)) {
        if (fa.is_compound() && fa.as_compound().op == Op::Not) {
            return fa.as_compound().left == b;
        }
        return false;
    }
    return false;
}

}  // namespace logic::proof::lkr
