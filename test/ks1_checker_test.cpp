// Tests for the KS1 derivation checker (HSW 2021 Fig. 6) — Track 2 phase K2.
// One accept + (where meaningful) one reject per rule, context navigation,
// and De Bruijn correctness for the quantifier rules and ≡ equations.

#include "src/core/formula.h"
#include "src/proof/ks1/checker.h"
#include "src/proof/ks1/derivation.h"

#include <iostream>

using namespace logic;
using namespace logic::proof::ks1;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT(...) do { \
    if (__VA_ARGS__) { ++g_passed; } else { \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_OK(d) do { \
    auto _r = check(f.fb, (d)); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL(expected Ok): " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; ++g_failed; } \
} while (0)

#define EXPECT_ERR(d) do { \
    auto _r = check(f.fb, (d)); \
    if (_r.is_error()) { ++g_passed; } else { \
        std::cerr << "FAIL(expected error) at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; } \
} while (0)

struct Fixture {
    GlobalContext  ctx;
    FormulaBuilder fb{ctx};

    PredicateHandle A = ctx.add_predicate("A", 0);
    PredicateHandle B = ctx.add_predicate("B", 0);
    PredicateHandle C = ctx.add_predicate("C", 0);
    PredicateHandle D = ctx.add_predicate("D", 0);
    PredicateHandle P1 = ctx.add_predicate("p", 1);
    PredicateHandle Q1 = ctx.add_predicate("q", 1);
    PredicateHandle R2 = ctx.add_predicate("r", 2);

    FormulaHandle a() { return fb.predicate(A, {}); }
    FormulaHandle b() { return fb.predicate(B, {}); }
    FormulaHandle c() { return fb.predicate(C, {}); }
    FormulaHandle d() { return fb.predicate(D, {}); }
    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle p(Term t) { return fb.predicate(P1, {t}); }
    FormulaHandle q(Term t) { return fb.predicate(Q1, {t}); }
    FormulaHandle r(Term s, Term t) { return fb.predicate(R2, {s, t}); }
    FormulaHandle And(FormulaHandle l, FormulaHandle rr) { return fb.make_and(l, rr); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle rr) { return fb.make_or(l, rr); }
    FormulaHandle Not(FormulaHandle x) { return fb.make_not(x); }
    FormulaHandle fa(FormulaHandle body) { return fb.make_quantified(Op::Forall, body); }
    FormulaHandle ex(FormulaHandle body) { return fb.make_quantified(Op::Exists, body); }
    Term g(var_index i) { return Term::generalized(i); }
};

Step step(Rule r, Path ctx = {}) { return Step{r, std::move(ctx)}; }

// ---- MLS1^X rules ----------------------------------------------------

void test_forall_unit() {
    Fixture f;
    EXPECT_OK((Derivation{f.top(), f.fa(f.top()), {step(Rule::ForallUnit)}}));
    // reject: redex not ⊤
    EXPECT_ERR((Derivation{f.a(), f.fa(f.top()), {step(Rule::ForallUnit)}}));
}

void test_ai() {
    Fixture f;
    Step s = step(Rule::Ai); s.f_param = f.a();          // a ∨ ¬a
    EXPECT_OK((Derivation{f.top(), f.Or(f.a(), f.Not(f.a())), {s}}));
    // reject: conclusion a∨a is not a∨ā
    EXPECT_ERR((Derivation{f.top(), f.Or(f.a(), f.a()), {s}}));
    // reject: param not atomic
    Step bad = step(Rule::Ai); bad.f_param = f.And(f.a(), f.b());
    EXPECT_ERR((Derivation{f.top(), f.Or(f.And(f.a(), f.b()), f.Not(f.And(f.a(), f.b()))), {bad}}));
}

void test_tu() {
    Fixture f;
    EXPECT_OK((Derivation{f.a(), f.And(f.a(), f.top()), {step(Rule::Tu)}}));
}

void test_switch() {
    Fixture f;
    EXPECT_OK((Derivation{f.And(f.a(), f.Or(f.b(), f.c())),
                          f.Or(f.And(f.a(), f.b()), f.c()), {step(Rule::Sw)}}));
    EXPECT_ERR((Derivation{f.And(f.a(), f.b()),  // not A∧(B∨C)
                           f.Or(f.And(f.a(), f.b()), f.c()), {step(Rule::Sw)}}));
}

void test_mix() {
    Fixture f;
    EXPECT_OK((Derivation{f.And(f.a(), f.b()), f.Or(f.a(), f.b()), {step(Rule::Mix)}}));
}

void test_exists() {
    Fixture f;
    // p(fixed0) / ∃x.p(x), witness t = fixed0, body p(Gen0).
    Step s = step(Rule::Ex); s.f_param = f.p(f.g(0)); s.t_param = Term::fixed(0);
    EXPECT_OK((Derivation{f.p(Term::fixed(0)), f.ex(f.p(f.g(0))), {s}}));
    // reject: A[x/t] ≠ redex (wrong witness)
    Step bad = step(Rule::Ex); bad.f_param = f.p(f.g(0)); bad.t_param = Term::fixed(1);
    EXPECT_ERR((Derivation{f.p(Term::fixed(0)), f.ex(f.p(f.g(0))), {bad}}));
}

// ---- ≡ equations -----------------------------------------------------

void test_eqv_comm_assoc() {
    Fixture f;
    auto eqv = [](EqRule e, EqDir dir = EqDir::Forward) {
        Step s = step(Rule::Eqv); s.eq = e; s.dir = dir; return s;
    };
    EXPECT_OK((Derivation{f.And(f.a(), f.b()), f.And(f.b(), f.a()), {eqv(EqRule::CommAnd)}}));
    EXPECT_OK((Derivation{f.Or(f.a(), f.b()), f.Or(f.b(), f.a()), {eqv(EqRule::CommOr)}}));
    // assoc∧ forward: (a∧b)∧c → a∧(b∧c)
    EXPECT_OK((Derivation{f.And(f.And(f.a(), f.b()), f.c()),
                          f.And(f.a(), f.And(f.b(), f.c())), {eqv(EqRule::AssocAnd)}}));
    // assoc∨ backward: a∨(b∨c) → (a∨b)∨c
    EXPECT_OK((Derivation{f.Or(f.a(), f.Or(f.b(), f.c())),
                          f.Or(f.Or(f.a(), f.b()), f.c()), {eqv(EqRule::AssocOr, EqDir::Backward)}}));
}

void test_eqv_swap() {
    Fixture f;
    Step s = step(Rule::Eqv); s.eq = EqRule::SwapForall;
    // ∀x.∀y.r(x,y) = ∀.∀.r(Gen1,Gen0)  →  ∀y.∀x.r(x,y) = ∀.∀.r(Gen0,Gen1)
    EXPECT_OK((Derivation{f.fa(f.fa(f.r(f.g(1), f.g(0)))),
                          f.fa(f.fa(f.r(f.g(0), f.g(1)))), {s}}));
}

void test_eqv_dist() {
    Fixture f;
    // ∀x.(p(x) ∨ b) ≡ (∀x.p(x)) ∨ b   [x ∉ b]
    Step fwd = step(Rule::Eqv); fwd.eq = EqRule::DistForall; fwd.dir = EqDir::Forward;
    EXPECT_OK((Derivation{f.fa(f.Or(f.p(f.g(0)), f.b())),
                          f.Or(f.fa(f.p(f.g(0))), f.b()), {fwd}}));
    Step bwd = step(Rule::Eqv); bwd.eq = EqRule::DistForall; bwd.dir = EqDir::Backward;
    EXPECT_OK((Derivation{f.Or(f.fa(f.p(f.g(0))), f.b()),
                          f.fa(f.Or(f.p(f.g(0)), f.b())), {bwd}}));
    // reject forward: bound var DOES occur free in B  → ∀x.(p(x) ∨ q(x))
    Step bad = step(Rule::Eqv); bad.eq = EqRule::DistForall; bad.dir = EqDir::Forward;
    EXPECT_ERR((Derivation{f.fa(f.Or(f.p(f.g(0)), f.q(f.g(0)))),
                           f.Or(f.fa(f.p(f.g(0))), f.q(f.g(0))), {bad}}));
    // ∃x.(p(x) ∧ b) ≡ (∃x.p(x)) ∧ b
    Step ex = step(Rule::Eqv); ex.eq = EqRule::DistExists; ex.dir = EqDir::Forward;
    EXPECT_OK((Derivation{f.ex(f.And(f.p(f.g(0)), f.b())),
                          f.And(f.ex(f.p(f.g(0))), f.b()), {ex}}));
}

// ---- resource rules --------------------------------------------------

void test_weakening() {
    Fixture f;
    Step s = step(Rule::W); s.f_param = f.b();
    EXPECT_OK((Derivation{f.a(), f.Or(f.a(), f.b()), {s}}));
}

void test_w_forall() {
    Fixture f;
    // a / ∀x.a  (x ∉ a; a is nullary so the binder is vacuous)
    EXPECT_OK((Derivation{f.a(), f.fa(f.a()), {step(Rule::WForall)}}));
}

void test_ac() {
    Fixture f;
    EXPECT_OK((Derivation{f.Or(f.a(), f.a()), f.a(), {step(Rule::Ac)}}));
    EXPECT_ERR((Derivation{f.Or(f.a(), f.b()), f.a(), {step(Rule::Ac)}}));  // operands differ
}

void test_c_forall() {
    Fixture f;
    // ∀y.∀x.p(x) = ∀.∀.p(Gen0)  →  ∀x.p(x) = ∀.p(Gen0)   (outer vacuous)
    EXPECT_OK((Derivation{f.fa(f.fa(f.p(f.g(0)))), f.fa(f.p(f.g(0))), {step(Rule::CForall)}}));
    EXPECT_ERR((Derivation{f.fa(f.p(f.g(0))), f.fa(f.p(f.g(0))), {step(Rule::CForall)}}));  // not ∀∀
}

void test_medial() {
    Fixture f;
    // (a∧c)∨(b∧d) → (a∨b)∧(c∨d)
    EXPECT_OK((Derivation{f.Or(f.And(f.a(), f.c()), f.And(f.b(), f.d())),
                          f.And(f.Or(f.a(), f.b()), f.Or(f.c(), f.d())), {step(Rule::M)}}));
}

void test_medial_quant() {
    Fixture f;
    // (∀x.p(x))∨(∀x.q(x)) → ∀x.(p(x)∨q(x))
    EXPECT_OK((Derivation{f.Or(f.fa(f.p(f.g(0))), f.fa(f.q(f.g(0)))),
                          f.fa(f.Or(f.p(f.g(0)), f.q(f.g(0)))), {step(Rule::MForall)}}));
    // (∃x.p(x))∨(∃x.q(x)) → ∃x.(p(x)∨q(x))
    EXPECT_OK((Derivation{f.Or(f.ex(f.p(f.g(0))), f.ex(f.q(f.g(0)))),
                          f.ex(f.Or(f.p(f.g(0)), f.q(f.g(0)))), {step(Rule::MExists)}}));
}

// ---- context navigation + multi-step ---------------------------------

void test_context_descent() {
    Fixture f;
    // Apply mix inside the right operand: a ∨ (b∧c) → a ∨ (b∨c).
    EXPECT_OK((Derivation{f.Or(f.a(), f.And(f.b(), f.c())),
                          f.Or(f.a(), f.Or(f.b(), f.c())), {step(Rule::Mix, {Dir::Right})}}));
    // Under a binder: ∀x.(p(x)∧⊤) reached by Tu at Down then... here just descend.
    // ∀x.(a∧b) → ∀x.(a∨b) via mix at Down.
    EXPECT_OK((Derivation{f.fa(f.And(f.a(), f.b())),
                          f.fa(f.Or(f.a(), f.b())), {step(Rule::Mix, {Dir::Down})}}));
    // bad path: Down into a non-quantifier
    EXPECT_ERR((Derivation{f.And(f.a(), f.b()), f.Or(f.a(), f.b()),
                           {step(Rule::Mix, {Dir::Down})}}));
}

// The context S{·} has its hole in atom position (paper §V) — in NNF that
// means at a literal slot. Descending into a Compound{Not, atom} would put
// the hole inside the literal, allowing Tu to plug a non-literal there and
// produce a non-NNF result. The navigation must reject Left/Right into Not.
void test_context_no_descent_into_not() {
    Fixture f;
    // top = ¬a;  Tu @ [Left] would land at the inner predicate. Must reject.
    EXPECT_ERR((Derivation{f.Not(f.a()), f.Not(f.And(f.a(), f.top())),
                           {step(Rule::Tu, {Dir::Left})}}));
}

// Per the paper's atom grammar `a ::= t | f | p | p̄`, units count as atoms;
// ai and ac on units are paper-permitted (a∨ā with a=⊤ is ⊤∨⊥; a∨a on ⊤).
void test_ai_on_top() {
    Fixture f;
    Step s = step(Rule::Ai); s.f_param = f.top();           // a = ⊤
    // dual of ⊤ = ¬¬⊥ ≡ ⊥? In our NNF dual_literal(¬⊥) returns the inner = ⊥.
    EXPECT_OK((Derivation{f.top(), f.Or(f.top(), f.fb.make_bottom()), {s}}));
}

void test_ai_on_bot() {
    Fixture f;
    Step s = step(Rule::Ai); s.f_param = f.fb.make_bottom();    // a = ⊥
    // dual(⊥) = ¬⊥ = ⊤ ; conclusion = ⊥ ∨ ⊤
    EXPECT_OK((Derivation{f.top(), f.Or(f.fb.make_bottom(), f.top()), {s}}));
}

void test_ac_on_top() {
    Fixture f;
    // ⊤∨⊤ → ⊤
    EXPECT_OK((Derivation{f.Or(f.top(), f.top()), f.top(), {step(Rule::Ac)}}));
}

void test_multi_step() {
    Fixture f;
    // t → ⊤∧⊤ (Tu) → (a∨ā)∧⊤ (ai at Left) → (a∨ā)∧(b∨b̄) (ai at Right)
    Step ai_l = step(Rule::Ai, {Dir::Left});  ai_l.f_param = f.a();
    Step ai_r = step(Rule::Ai, {Dir::Right}); ai_r.f_param = f.b();
    FormulaHandle bot = f.And(f.Or(f.a(), f.Not(f.a())), f.Or(f.b(), f.Not(f.b())));
    EXPECT_OK((Derivation{f.top(), bot, {step(Rule::Tu), ai_l, ai_r}}));
    // wrong bottom
    EXPECT_ERR((Derivation{f.top(), f.And(f.Or(f.a(), f.Not(f.a())), f.top()),
                           {step(Rule::Tu), ai_l, ai_r}}));
}

}  // namespace

int main() {
    test_forall_unit();
    test_ai();
    test_tu();
    test_switch();
    test_mix();
    test_exists();
    test_eqv_comm_assoc();
    test_eqv_swap();
    test_eqv_dist();
    test_weakening();
    test_w_forall();
    test_ac();
    test_c_forall();
    test_medial();
    test_medial_quant();
    test_context_descent();
    test_context_no_descent_into_not();
    test_ai_on_top();
    test_ai_on_bot();
    test_ac_on_top();
    test_multi_step();

    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
