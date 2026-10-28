#include "formula_reader.h"

#include "src/core/scope_utils.h"

namespace logic::proof::translate::nd_to_lkr {

util::Result<FormulaHandle> FormulaReader::read(StepRef s,
                                                const TermEnv& sigma) const {
    FormulaHandle f = trace_.step_env[s.idx];
    if (!f.valid()) {
        return MAKE_ERROR << "FormulaReader: step #" << s.idx
                          << " derives no formula";
    }
    // σ's values avoid ND levels, so sequential substitution is simultaneous.
    for (StepRef binder : index_.scope(s)) {
        Term level = Term::fixed(index_.level(binder));
        if (const TermBinding* bound = sigma.find(binder)) {
            if (!(bound->value == level)) {
                f = builder_.translate_term(f, level, bound->value);
            }
        } else if (formula_contains_fixed_var(f, index_.level(binder))) {
            return MAKE_ERROR
                << "FormulaReader: step #" << s.idx << " mentions binder #"
                << binder.idx << ", which is unbound on this branch";
        }
    }
    return f;
}

util::Result<FormulaHandle> FormulaReader::read_nnf(
    StepRef s, const TermEnv& sigma) const {
    TRY_ASSIGN(f, read(s, sigma));
    return builder_.to_nnf(f);
}

}  // namespace logic::proof::translate::nd_to_lkr
