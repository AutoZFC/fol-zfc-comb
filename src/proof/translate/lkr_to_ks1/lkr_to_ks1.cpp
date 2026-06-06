#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include <variant>
#include <vector>

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// A formula is a negative literal iff its top connective is ¬ (NNF: only atoms
// are negated). Ai's parameter is the POSITIVE atom a; Ai emits the pair a∨ā.
bool is_negative_literal(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not;
}

// Prepend `d` to every step's context — composes a sub-derivation (t ⟶ X)
// inside the context S{·} = [d, …] (e.g. the Left branch of an ∧). See
// LKR_TO_KS1_DESIGN.md.
void prefix_context(std::vector<ks1::Step>& steps, ks1::Dir d) {
    for (ks1::Step& s : steps) s.context.insert(s.context.begin(), d);
}

ks1::Step ai_step(FormulaHandle positive_atom) {
    ks1::Step s;
    s.rule    = ks1::Rule::Ai;
    s.f_param = positive_atom;
    return s;
}

ks1::Step comm_or_root() {
    ks1::Step s;
    s.rule = ks1::Rule::Eqv;
    s.eq   = ks1::EqRule::CommOr;
    s.dir  = ks1::EqDir::Forward;     // A∨B → B∨A
    return s;
}

ks1::Step tu_root() {
    ks1::Step s;
    s.rule = ks1::Rule::Tu;           // A → A∧t
    return s;
}

// tr(d): KS1 steps realizing t ⟶ (d.conclusion), where (Γ) is the
// left-associated disjunction of the sequent (LKR_TO_KS1_DESIGN.md §"The
// sequent–formula correspondence"). K6.1 scope is the switch-free linear
// shapes: a 2-literal axiom, a single-formula Or wrapper, and an empty-context
// And. Everything else (switch sequence, multi-formula reconciliation,
// quantifiers, resource rules) errors with the phase that owns it.
util::Result<std::vector<ks1::Step>> tr(FormulaBuilder& fb, const lce::Deriv& d) {
    // --- RAx: pure 2-literal axiom ⊢ φ,ψ (duals). (Γ) = φ∨ψ. -------------
    if (const auto* ax = std::get_if<lce::RAx>(&d.rule)) {
        if (d.conclusion.size() != 2)
            return MAKE_ERROR << "lkr_to_ks1: K6.1 axiom must be exactly 2 literals "
                                 "(got " << d.conclusion.size()
                              << "); axiom-with-weakening is K6.3";
        FormulaHandle lit_a = d.conclusion[ax->a];
        FormulaHandle lit_b = d.conclusion[ax->b];
        FormulaHandle positive = is_negative_literal(lit_a) ? lit_b : lit_a;
        std::vector<ks1::Step> steps{ai_step(positive)};   // t → α∨ᾱ
        // (Γ) reads disjuncts in sequent order. Ai emits α∨ᾱ; if the sequent
        // lists the negative literal first, commute to ᾱ∨α.
        if (is_negative_literal(d.conclusion[0]))
            steps.push_back(comm_or_root());
        return steps;
    }

    // --- ROr: single-formula Or wrapper ⊢ φ∨ψ over child ⊢ φ,ψ. ----------
    // (child) = φ∨ψ = (node) already (the ∨ grouping is free). Multi-formula
    // Or reconciliation is K6.1b.
    if (const auto* orr = std::get_if<lce::ROr>(&d.rule)) {
        if (d.conclusion.size() != 1)
            return MAKE_ERROR << "lkr_to_ks1: K6.1 Or supports only a single-formula "
                                 "goal sequent; multi-formula reconciliation is K6.1b";
        const Formula& f = d.conclusion[0].get();
        if (!(f.is_compound() && f.as_compound().op == Op::Or))
            return MAKE_ERROR << "lkr_to_ks1: ROr goal is not a disjunction";
        // The child sequent denotes the same formula; just recurse.
        return tr(fb, *orr->child);
    }

    // --- RAnd: empty-context conjunction ⊢ φ∧ψ over ⊢ φ and ⊢ ψ. ---------
    // Γ_L = Γ_R = ∅, so no switch sequence: t —Tu→ t∧t, then the two branch
    // derivations in the Left/Right contexts. Non-empty context (the switch
    // sequence of Lemma 20) is K6.1b.
    if (const auto* andr = std::get_if<lce::RAnd>(&d.rule)) {
        if (d.conclusion.size() != 1)
            return MAKE_ERROR << "lkr_to_ks1: K6.1 And supports only the empty-context "
                                 "case (single-formula goal); the switch sequence is K6.1b";
        const lce::Deriv* L = andr->left.get();
        const lce::Deriv* R = andr->right.get();
        if (L->conclusion.size() != 1 || R->conclusion.size() != 1)
            return MAKE_ERROR << "lkr_to_ks1: K6.1 And requires empty branch contexts "
                                 "(each premise a single formula); switch sequence is K6.1b";
        TRY_ASSIGN(stepsL, tr(fb, *L));
        TRY_ASSIGN(stepsR, tr(fb, *R));
        prefix_context(stepsL, ks1::Dir::Left);
        prefix_context(stepsR, ks1::Dir::Right);
        std::vector<ks1::Step> steps{tu_root()};           // t → t∧t
        steps.insert(steps.end(), stepsL.begin(), stepsL.end());   // left t → φ
        steps.insert(steps.end(), stepsR.begin(), stepsR.end());   // right t → ψ
        return steps;
    }

    return MAKE_ERROR << "lkr_to_ks1: K6.1 does not yet handle this rule "
                         "(quantifiers = K6.2, weakening/contraction = K6.3)";
}

}  // namespace

util::Result<ks1::Derivation> lkr_to_ks1(FormulaBuilder& fb,
                                         const lce::Deriv& cutfree) {
    if (cutfree.conclusion.size() != 1)
        return MAKE_ERROR << "lkr_to_ks1: expected a single-formula (closed) goal "
                             "sequent, got " << cutfree.conclusion.size()
                          << " formulas";
    FormulaHandle goal = cutfree.conclusion[0];

    TRY_ASSIGN(steps, tr(fb, cutfree));
    FormulaHandle top = fb.make_not(fb.make_bottom());   // ⊤ = ¬⊥
    return ks1::Derivation{top, goal, std::move(steps)};
}

}  // namespace logic::proof::translate::lkr_to_ks1
