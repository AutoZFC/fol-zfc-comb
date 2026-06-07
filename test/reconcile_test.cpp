// K6.1b — `equiv_steps` reconciliation primitive, in isolation.
//
// For a battery of ≡-equivalent (from, to) formula pairs (assoc/comm of ∧/∨),
// `equiv_steps` must emit Eqv steps that `ks1::replay` carries from `from` to
// exactly `to`; and for a NON-equivalent pair it must error. The pipeline gate
// (ks1::check / CombVerifier) sits downstream; this pins the primitive directly.

#include "src/core/formula.h"
#include "src/proof/ks1/checker.h"
#include "src/proof/translate/lkr_to_ks1/reconcile.h"

#include <iostream>

using namespace logic;
namespace l2k = logic::proof::translate::lkr_to_ks1;

namespace {

int g_passed = 0, g_failed = 0;
#define EXPECT(...) do {                                                       \
    if (__VA_ARGS__) { ++g_passed; } else {                                   \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":"          \
                  << __LINE__ << "\n"; ++g_failed; }                          \
} while (0)

struct F {
    GlobalContext ctx;
    FormulaBuilder fb{ctx};
    FormulaHandle p(const char* n) { return fb.predicate(ctx.add_predicate(n, 0), {}); }
    FormulaHandle Or(FormulaHandle a, FormulaHandle b) { return fb.make_or(a, b); }
    FormulaHandle And(FormulaHandle a, FormulaHandle b) { return fb.make_and(a, b); }
};

// equiv_steps(from,to) must reach exactly `to` from `from`.
void ok_pair(F& f, FormulaHandle from, FormulaHandle to) {
    auto s = l2k::equiv_steps(f.fb, from, to);
    EXPECT(s.ok());
    if (!s.ok()) { std::cerr << "  " << s.error().to_string() << "\n"; return; }
    auto got = proof::ks1::replay(f.fb, from, s.value());
    EXPECT(got.ok() && got.value() == to);
}

void test_identity() {
    F f; auto a = f.p("a");
    ok_pair(f, a, a);                                  // no steps
}

void test_comm_or() {
    F f; auto a = f.p("a"), b = f.p("b");
    ok_pair(f, f.Or(a, b), f.Or(b, a));               // a∨b → b∨a
}

void test_assoc_or() {
    F f; auto a = f.p("a"), b = f.p("b"), c = f.p("c");
    ok_pair(f, f.Or(f.Or(a, b), c), f.Or(a, f.Or(b, c)));   // (a∨b)∨c → a∨(b∨c)
}

void test_move_last_disjunct() {
    // The ROr shape: child appended d at the end; node wants it next to b.
    //   (((a∨b)∨c)∨d)  →  (((a∨b)∨d)∨c)
    F f; auto a=f.p("a"),b=f.p("b"),c=f.p("c"),d=f.p("d");
    auto from = f.Or(f.Or(f.Or(a,b),c),d);
    auto to   = f.Or(f.Or(f.Or(a,b),d),c);
    ok_pair(f, from, to);
}

void test_nested_and_in_or() {
    // Mixed: ((a∧b)∨c)∨d  →  d∨(c∨(b∧a))  (comm at both levels + assoc)
    F f; auto a=f.p("a"),b=f.p("b"),c=f.p("c"),d=f.p("d");
    auto from = f.Or(f.Or(f.And(a,b),c),d);
    auto to   = f.Or(d, f.Or(c, f.And(b,a)));
    ok_pair(f, from, to);
}

void test_and_chain() {
    F f; auto a=f.p("a"),b=f.p("b"),c=f.p("c");
    ok_pair(f, f.And(f.And(a,b),c), f.And(c, f.And(b,a)));
}

void test_non_equiv_errors() {
    F f; auto a=f.p("a"),b=f.p("b"),c=f.p("c");
    auto r = l2k::equiv_steps(f.fb, f.Or(a,b), f.Or(a,c));   // different atoms
    EXPECT(r.is_error());
}

// contract_steps(X): replaying from X∨X must reach exactly X.
void ok_contract(F& f, FormulaHandle x) {
    auto s = l2k::contract_steps(f.fb, x);
    EXPECT(s.ok());
    if (!s.ok()) { std::cerr << "  " << s.error().to_string() << "\n"; return; }
    auto got = proof::ks1::replay(f.fb, f.Or(x, x), s.value());
    EXPECT(got.ok() && got.value() == x);
    if (got.ok() && !(got.value() == x))
        std::cerr << "  got " << got.value().get().to_string() << "\n";
}

void test_contract_atom() { F f; ok_contract(f, f.p("a")); }                 // Ac
void test_contract_neg()  { F f; ok_contract(f, f.fb.make_not(f.p("a"))); }  // ¬a
void test_contract_or()   { F f; ok_contract(f, f.Or(f.p("a"), f.p("b"))); } // reshape+Ac×2
void test_contract_and()  { F f; ok_contract(f, f.And(f.p("a"), f.p("b"))); }// M+Ac×2
void test_contract_em()   { F f; auto a=f.p("a"); ok_contract(f, f.Or(a, f.fb.make_not(a))); }
void test_contract_nested() {
    F f; auto a=f.p("a"),b=f.p("b"),c=f.p("c");
    ok_contract(f, f.Or(f.And(a, b), c));     // ((a∧b)∨c): reshape, then M, Ac
}
void test_contract_forall() {
    F f; auto body = f.fb.predicate(f.ctx.add_predicate("p", 1), {Term::generalized(0)});
    ok_contract(f, f.fb.make_quantified(Op::Forall, body));   // MForall + Ac
}

}  // namespace

int main() {
    F init;  // (unused warning guard)
    test_identity();
    test_comm_or();
    test_assoc_or();
    test_move_last_disjunct();
    test_nested_and_in_or();
    test_and_chain();
    test_non_equiv_errors();
    test_contract_atom();
    test_contract_neg();
    test_contract_or();
    test_contract_and();
    test_contract_em();
    test_contract_nested();
    test_contract_forall();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
