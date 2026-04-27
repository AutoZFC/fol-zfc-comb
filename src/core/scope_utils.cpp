#include "scope_utils.h"

namespace logic {

bool formula_contains_fixed_var(FormulaHandle const& h, var_index var_idx) {
    const Formula& f = h.get();

    if (f.is_schema_var()) return false;

    if (f.is_predicate()) {
        const PredicateInstance& p = f.as_predicate();
        for (const Term& t : p.args()) {
            if (t.is_fixed() && t.as_variable() == var_idx) {
                return true;
            }
            if (t.is_description() &&
                formula_contains_fixed_var(t.as_description().body, var_idx)) {
                return true;
            }
        }
        return false;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid() && formula_contains_fixed_var(c.left, var_idx)) {
            return true;
        }
        if (c.right.valid() && formula_contains_fixed_var(c.right, var_idx)) {
            return true;
        }
        return false;
    }
    if (f.is_quantified()) {
        return formula_contains_fixed_var(f.as_quantified().body, var_idx);
    }
    // Sentences are closed; they contain no free fixed vars.
    return false;
}

bool description_body_accessible(
    FormulaHandle const& h,
    std::function<bool(var_index)> const& is_in_scope)
{
    const Formula& f = h.get();

    if (f.is_schema_var()) return true;

    if (f.is_predicate()) {
        for (const Term& t : f.as_predicate().args()) {
            if (t.is_fixed() && !is_in_scope(t.as_variable())) return false;
            if (t.is_description() &&
                !description_body_accessible(t.as_description().body, is_in_scope)) {
                return false;
            }
            // Generalized vars are bound; skip.
        }
        return true;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid()  && !description_body_accessible(c.left,  is_in_scope)) return false;
        if (c.right.valid() && !description_body_accessible(c.right, is_in_scope)) return false;
        return true;
    }
    if (f.is_quantified()) {
        return description_body_accessible(f.as_quantified().body, is_in_scope);
    }
    // Sentences are closed.
    return true;
}

}  // namespace logic
