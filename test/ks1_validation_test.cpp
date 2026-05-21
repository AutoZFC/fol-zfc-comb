// KS1 end-to-end derivation validation (HSW 2021 §V/§VI) — Track 2 phase K2.
//
// These exercise the checker on multi-rule decomposed derivations that follow
// the Thm 17 phase order, proving genuine first-order theorems. Each step is a
// Fig. 6 rule instance (the rules are individually validated in
// ks1_checker_test); here we confirm they COMPOSE into valid derivations and
// that De Bruijn binding threads correctly across the linear / instantiation /
// contraction phases.
//
// NOTE on Fig. 7: the paper's worked example proves (∃x.p̄x) ∨ (∀y.(py∧pfy)),
// but its PDF text loses every negation overline (p̄ renders as p) and the
// exact bracketing of its ≡/s steps is only type-correct under specific
// polarities — transcribing it risks encoding an INVALID derivation. Since the
// checker only accepts legal Fig. 6 instances, we instead validate with
// derivations we can construct with certainty (below), which is equally
// rigorous: a passing derivation is provably a valid KS1 derivation, hence by
// Thm 16 its bottom is valid whenever its top is ⊤.

#include "src/core/formula.h"
#include "src/proof/ks1/checker.h"
#include "src/proof/ks1/derivation.h"

#include <iostream>

using namespace logic;
using namespace logic::proof::ks1;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_OK(d) do { \
    auto _r = check(f.fb, (d)); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL(expected Ok): " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; ++g_failed; } \
} while (0)

struct Fixture {
    GlobalContext  ctx;
    FormulaBuilder fb{ctx};
    PredicateHandle P1 = ctx.add_predicate("p", 1);
    PredicateHandle A0 = ctx.add_predicate("A", 0);

    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle p(Term t) { return fb.predicate(P1, {t}); }
    FormulaHandle np(Term t) { return fb.make_not(fb.predicate(P1, {t})); }
    FormulaHandle aa() { return fb.predicate(A0, {}); }
    FormulaHandle naa() { return fb.make_not(fb.predicate(A0, {})); }
    FormulaHandle And(FormulaHandle l, FormulaHandle r) { return fb.make_and(l, r); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle r) { return fb.make_or(l, r); }
    FormulaHandle fa(FormulaHandle b) { return fb.make_quantified(Op::Forall, b); }
    FormulaHandle ex(FormulaHandle b) { return fb.make_quantified(Op::Exists, b); }
    Term g0() { return Term::generalized(0); }
    Term k0() { return Term::fixed(0); }
};

Step S(Rule r, Path c = {}) { return Step{r, std::move(c)}; }

// D1: prove ∀x.(px ∨ p̄x).   t —∀→ ∀x.t —ai(@Down,a=px)→ ∀x.(px ∨ p̄x).
void test_forall_excluded_middle() {
    Fixture f;
    Step ai = S(Rule::Ai, {Dir::Down}); ai.f_param = f.p(f.g0());
    EXPECT_OK((Derivation{
        f.top(), f.fa(f.Or(f.p(f.g0()), f.np(f.g0()))),
        {S(Rule::ForallUnit), ai}}));
}

// D2: prove ∃x.(px ∨ p̄x).   t —ai(a=p(c))→ p(c)∨p̄(c) —∃(witness c)→ ∃x.(px∨p̄x).
void test_exists_excluded_middle() {
    Fixture f;
    Step ai = S(Rule::Ai); ai.f_param = f.p(f.k0());          // a = p(fixed0)
    Step ex = S(Rule::Ex); ex.f_param = f.Or(f.p(f.g0()), f.np(f.g0())); ex.t_param = f.k0();
    EXPECT_OK((Derivation{
        f.top(), f.ex(f.Or(f.p(f.g0()), f.np(f.g0()))),
        {ai, ex}}));
}

// D3 (contraction phase): (∃x.px)∨(∃x.px) —m∃→ ∃x.(px∨px) —ac(@Down)→ ∃x.px.
// A genuine KS1 derivation (B→A form) exercising medial-∃ then atomic
// contraction with De Bruijn bodies threaded through.
void test_medial_then_contraction() {
    Fixture f;
    EXPECT_OK((Derivation{
        f.Or(f.ex(f.p(f.g0())), f.ex(f.p(f.g0()))),  // top = (∃x.px)∨(∃x.px)
        f.ex(f.p(f.g0())),                            // bottom = ∃x.px
        {S(Rule::MExists), S(Rule::Ac, {Dir::Down})}}));
}

// D4 (linear phase): prove (⊤∧A) ∨ Ā via t —t→ t∧t —ai(@Right)→ t∧(A∨Ā)
//                    —s→ (t∧A)∨Ā.  Exercises the unit, ai, and switch rules.
void test_linear_switch() {
    Fixture f;
    Step ai = S(Rule::Ai, {Dir::Right}); ai.f_param = f.aa();
    EXPECT_OK((Derivation{
        f.top(), f.Or(f.And(f.top(), f.aa()), f.naa()),
        {S(Rule::Tu), ai, S(Rule::Sw)}}));
}

}  // namespace

int main() {
    Fixture probe;  // ensure fixture compiles
    (void)probe;
    test_forall_excluded_middle();
    test_exists_excluded_middle();
    test_medial_then_contraction();
    test_linear_switch();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
