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
    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle a() { return fb.predicate(A0, {}); }
    FormulaHandle na() { return fb.make_not(fb.predicate(A0, {})); }
    FormulaHandle b() { return fb.predicate(B0, {}); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle r) { return fb.make_or(l, r); }
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

}  // namespace

int main() {
    test_weakening_end_to_end();
    test_ac_contraction_fibration();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
