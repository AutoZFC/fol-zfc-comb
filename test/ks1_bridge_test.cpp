// KS1 → Comb full bridge (HSW 2021 Thm 19) — Track 2 phase K5.
// build_comb_proof on a decomposed KS1 derivation, validated by ALL FOUR
// CombVerifier phases; plus a contraction unit test of the skew read-off.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/verifier.h"
#include "src/proof/ks1/derivation.h"
#include "src/proof/translate/ks1_to_comb/read_skew.h"

#include <iostream>

using namespace logic;
using namespace logic::proof::ks1;
using logic::proof::ks1_to_comb::build_comb_proof;
using logic::proof::ks1_to_comb::read_skew;

namespace {

int g_passed = 0, g_failed = 0;
#define EXPECT(...) do { \
    if (__VA_ARGS__) { ++g_passed; } else { \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; } \
} while (0)

struct Fixture {
    GlobalContext  ctx;
    FormulaBuilder fb{ctx};
    PredicateHandle A0 = ctx.add_predicate("A", 0);
    PredicateHandle B0 = ctx.add_predicate("B", 0);
    PredicateHandle C0 = ctx.add_predicate("C", 0);
    PredicateHandle D0 = ctx.add_predicate("D", 0);
    PredicateHandle P1 = ctx.add_predicate("p", 1);
    PredicateHandle Q1 = ctx.add_predicate("q", 1);
    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle a() { return fb.predicate(A0, {}); }
    FormulaHandle na() { return fb.make_not(fb.predicate(A0, {})); }
    FormulaHandle b() { return fb.predicate(B0, {}); }
    FormulaHandle c() { return fb.predicate(C0, {}); }
    FormulaHandle d() { return fb.predicate(D0, {}); }
    FormulaHandle p(Term t) { return fb.predicate(P1, {t}); }
    FormulaHandle q(Term t) { return fb.predicate(Q1, {t}); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle r) { return fb.make_or(l, r); }
    FormulaHandle And(FormulaHandle l, FormulaHandle r) { return fb.make_and(l, r); }
    FormulaHandle fa(FormulaHandle b) { return fb.make_quantified(Op::Forall, b); }
    FormulaHandle ex(FormulaHandle b) { return fb.make_quantified(Op::Exists, b); }
    Term g0() { return Term::generalized(0); }
};

Step S(Rule r, Path c = {}) { return Step{r, std::move(c)}; }

bool all_phases(GlobalContext& ctx, FormulaHandle goal, const proof::comb::CombProof& cp) {
    proof::comb::CombVerifier v;
    auto p0 = v.verify_well_formed(cp);
    if (p0.is_error()) { std::cerr << "  p0: " << p0.error().to_string() << "\n"; return false; }
    auto p1 = v.verify_target_is_formula_graph(ctx, goal, cp);
    if (p1.is_error()) { std::cerr << "  p1: " << p1.error().to_string() << "\n"; return false; }
    auto p2 = v.verify_fonet(cp);
    if (p2.is_error()) { std::cerr << "  p2: " << p2.error().to_string() << "\n"; return false; }
    auto p3 = v.verify_skew_bifibration(cp);
    if (p3.is_error()) { std::cerr << "  p3: " << p3.error().to_string() << "\n"; return false; }
    return true;
}

// End-to-end with a WEAKENING resource phase:
//   t —ai(a=A)→ A∨Ā            [Φ1 linear, A' = A∨Ā]
//     —w(B)→ (A∨Ā)∨B           [Φ2 resource]
// Goal (A∨Ā)∨B is valid; the fibration injects A,Ā and leaves B uncovered.
void test_weakening_end_to_end() {
    Fixture f;
    Step ai = S(Rule::Ai); ai.f_param = f.a();
    Step w = S(Rule::W); w.f_param = f.b();
    FormulaHandle goal = f.Or(f.Or(f.a(), f.na()), f.b());
    Derivation d{f.top(), goal, {ai, w}};
    auto cp = build_comb_proof(f.fb, d);
    EXPECT(cp.ok());
    if (cp.ok()) {
        EXPECT(cp.value().source.num_vertex == 2);    // A, Ā
        EXPECT(cp.value().target.num_vertex() == 3);  // A, Ā, B
        EXPECT(cp.value().fibration.size() == 2);
        EXPECT(all_phases(f.ctx, goal, cp.value()));
    }
}

// Contraction unit test: Φ2 = (A∨A) —ac→ A. The two source atoms map to the
// single target atom (many-to-one), i.e. the fibration is non-injective.
void test_ac_contraction_fibration() {
    Fixture f;
    Derivation phi2{f.Or(f.a(), f.a()), f.a(), {S(Rule::Ac)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 2);
        EXPECT(sk.value().fibration[0] == 0);
        EXPECT(sk.value().fibration[1] == 0);   // both source A's → the one target A
        EXPECT(sk.value().target.num_vertex() == 1);
    }
}

// --- per-resource-rule fibration unit tests --------------------------
//
// Each test exercises one rule's induced map on a small Φ2 and asserts the
// fibration vector matches the expected source→target vertex correspondence
// computed by hand from comb::Fograph's pre-order numbering.

// w∀: S{A}/S{∀x.A}. Premise [[A]] = [atom_A(0)]. Conclusion [[∀x.A]] =
// [binder(0), atom_A(1)]. Atom maps to itself (offset by the new binder);
// the binder is uncovered.
void test_w_forall_fibration() {
    Fixture f;
    Derivation phi2{f.a(), f.fa(f.a()), {S(Rule::WForall)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 1);
        EXPECT(sk.value().fibration[0] == 1);     // atom A → atom A (target idx 1)
        EXPECT(sk.value().target.num_vertex() == 2);
    }
}

// c∀: S{∀x.∀x.A}/S{∀x.A}. Premise vertices: outer-binder(0), inner-binder(1),
// atom(2). Conclusion vertices: binder(0), atom(1). Both binders contract to
// the kept binder; atom keeps its place.
void test_c_forall_fibration() {
    Fixture f;
    FormulaHandle bot = f.fa(f.p(f.g0()));               // ∀x.p(x)
    FormulaHandle top = f.fa(bot);                       // ∀.∀.p(Gen0)  (outer vacuous)
    Derivation phi2{top, bot, {S(Rule::CForall)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 3);
        EXPECT(sk.value().fibration[0] == 0);     // outer binder → merged binder
        EXPECT(sk.value().fibration[1] == 0);     // inner binder → merged binder
        EXPECT(sk.value().fibration[2] == 1);     // atom → atom
    }
}

// m∀: S{(∀x.A)∨(∀x.B)}/S{∀x.(A∨B)}.
//   Premise pre-order: binder_l(0), atom_p(1), binder_r(2), atom_q(3).
//   Conclusion pre-order: merged binder(0), atom_p(1), atom_q(2).
void test_m_forall_fibration() {
    Fixture f;
    Derivation phi2{f.Or(f.fa(f.p(f.g0())), f.fa(f.q(f.g0()))),
                    f.fa(f.Or(f.p(f.g0()), f.q(f.g0()))),
                    {S(Rule::MForall)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 4);
        EXPECT(sk.value().fibration[0] == 0);  // left binder → merged
        EXPECT(sk.value().fibration[1] == 1);  // atom p → atom p
        EXPECT(sk.value().fibration[2] == 0);  // right binder → merged
        EXPECT(sk.value().fibration[3] == 2);  // atom q → atom q
    }
}

// m∃: dual of m∀ on existentials.
void test_m_exists_fibration() {
    Fixture f;
    Derivation phi2{f.Or(f.ex(f.p(f.g0())), f.ex(f.q(f.g0()))),
                    f.ex(f.Or(f.p(f.g0()), f.q(f.g0()))),
                    {S(Rule::MExists)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration[0] == 0);
        EXPECT(sk.value().fibration[1] == 1);
        EXPECT(sk.value().fibration[2] == 0);
        EXPECT(sk.value().fibration[3] == 2);
    }
}

// ≡ inside Φ2 (e.g. CommOr between medials): the induced map is the identity
// on vertices, but their pre-order positions in the conclusion swap with the
// operands. Premise A∨B: A(0), B(1). Conclusion B∨A: B(0), A(1). So source
// A(0) maps to target position 1, source B(1) maps to target position 0.
void test_eqv_in_phi2_fibration() {
    Fixture f;
    Step e = S(Rule::Eqv); e.eq = EqRule::CommOr; e.dir = EqDir::Forward;
    Derivation phi2{f.Or(f.a(), f.b()), f.Or(f.b(), f.a()), {e}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 2);
        EXPECT(sk.value().fibration[0] == 1);   // A: pos 0 → pos 1
        EXPECT(sk.value().fibration[1] == 0);   // B: pos 1 → pos 0
    }
}

// m: S{(A∧C)∨(B∧D)}/S{(A∨B)∧(C∨D)}. Atoms keep identity, but pre-order
// changes:
//   Premise (A∧C)∨(B∧D): A(0), C(1), B(2), D(3).
//   Conclusion (A∨B)∧(C∨D): A(0), B(1), C(2), D(3).
//   ⟹ fibration A:0→0, C:1→2, B:2→1, D:3→3.
void test_m_fibration() {
    Fixture f;
    Derivation phi2{f.Or(f.And(f.a(), f.c()), f.And(f.b(), f.d())),
                    f.And(f.Or(f.a(), f.b()), f.Or(f.c(), f.d())),
                    {S(Rule::M)}};
    auto sk = read_skew(f.fb, phi2);
    EXPECT(sk.ok());
    if (sk.ok()) {
        EXPECT(sk.value().fibration.size() == 4);
        EXPECT(sk.value().fibration[0] == 0);  // A
        EXPECT(sk.value().fibration[1] == 2);  // C
        EXPECT(sk.value().fibration[2] == 1);  // B
        EXPECT(sk.value().fibration[3] == 3);  // D
    }
}

}  // namespace

int main() {
    test_weakening_end_to_end();
    test_ac_contraction_fibration();
    test_w_forall_fibration();
    test_c_forall_fibration();
    test_m_forall_fibration();
    test_m_exists_fibration();
    test_eqv_in_phi2_fibration();
    test_m_fibration();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
