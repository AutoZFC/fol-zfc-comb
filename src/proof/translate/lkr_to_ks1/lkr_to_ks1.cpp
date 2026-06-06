#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include <variant>

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// A formula is a negative literal iff its top connective is ¬ (NNF: only atoms
// are negated). The Ai rule's parameter is the POSITIVE atom a; Ai produces
// the ordered pair a∨ā.
bool is_negative_literal(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not;
}

}  // namespace

util::Result<ks1::Derivation> lkr_to_ks1(FormulaBuilder& fb,
                                         const lce::Deriv& cutfree) {
    if (cutfree.conclusion.size() != 1)
        return MAKE_ERROR << "lkr_to_ks1: expected a single-formula (closed) goal "
                             "sequent, got " << cutfree.conclusion.size()
                          << " formulas";
    FormulaHandle goal = cutfree.conclusion[0];

    // --- K6.0 skeleton: ⊢ a∨ā only (ROr over a 2-literal RAx). ------------
    // The axiom links the two disjuncts as duals; the whole disjunction is the
    // image of a single atomic interaction. KS1: t —Ai(a)→ a∨ā.
    const auto* orr = std::get_if<lce::ROr>(&cutfree.rule);
    if (!orr)
        return MAKE_ERROR << "lkr_to_ks1: K6.0 supports only ⊢ a∨ā (ROr over an "
                             "axiom); general LK1→KS1 is K6.1+";
    const lce::Deriv* child = orr->child.get();
    const auto* ax = std::get_if<lce::RAx>(&child->rule);
    if (!ax)
        return MAKE_ERROR << "lkr_to_ks1: K6.0 supports only ⊢ a∨ā; the Or's "
                             "premise is not an axiom";
    if (child->conclusion.size() != 2)
        return MAKE_ERROR << "lkr_to_ks1: K6.0 expects a 2-literal axiom premise, "
                             "got " << child->conclusion.size();

    // The positive literal of the dual pair is Ai's parameter.
    FormulaHandle lit_a = child->conclusion[ax->a];
    FormulaHandle lit_b = child->conclusion[ax->b];
    FormulaHandle positive = is_negative_literal(lit_a) ? lit_b : lit_a;

    ks1::Step ai;
    ai.rule    = ks1::Rule::Ai;
    ai.context = {};            // whole-formula rewrite: ⊤ → a∨ā
    ai.f_param = positive;

    FormulaHandle top = fb.make_not(fb.make_bottom());   // ⊤ = ¬⊥
    return ks1::Derivation{top, goal, {ai}};
}

}  // namespace logic::proof::translate::lkr_to_ks1
