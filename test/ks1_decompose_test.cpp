// Tests for KS1 decomposition normal form + split (HSW 2021 Thm 17) — K3.

#include "src/core/formula.h"
#include "src/proof/ks1/checker.h"
#include "src/proof/ks1/decompose.h"
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
        ++g_failed; } \
} while (0)

struct Fixture {
    GlobalContext  ctx;
    FormulaBuilder fb{ctx};
    PredicateHandle P1 = ctx.add_predicate("p", 1);

    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle p(Term t) { return fb.predicate(P1, {t}); }
    FormulaHandle np(Term t) { return fb.make_not(fb.predicate(P1, {t})); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle r) { return fb.make_or(l, r); }
    FormulaHandle ex(FormulaHandle b) { return fb.make_quantified(Op::Exists, b); }
    Term g0() { return Term::generalized(0); }
    Term k0() { return Term::fixed(0); }
};

Step S(Rule r, Path c = {}) { return Step{r, std::move(c)}; }

void test_classification() {
    EXPECT(is_mls1x(Rule::ForallUnit) && is_mls1x(Rule::Ai) && is_mls1x(Rule::Ex));
    EXPECT(is_mls1x(Rule::Eqv) && is_resource(Rule::Eqv));  // ≡ in both
    EXPECT(is_resource(Rule::M) && is_resource(Rule::Ac) && is_resource(Rule::W));
    EXPECT(!is_resource(Rule::Ai) && !is_mls1x(Rule::Ac));
}

// A decomposed derivation: t —ai—→ p(c)∨p̄(c) —∃—→ ∃x.(px∨p̄x) [MLS1^X]
// then a resource ≡ (CommOr) at the end. Boundary: no resource-only step, so
// the whole thing is MLS1^X (Φ2 empty) — still decomposed.
void test_decomposed_all_linear() {
    Fixture f;
    Step ai = S(Rule::Ai); ai.f_param = f.p(f.k0());
    Step ex = S(Rule::Ex); ex.f_param = f.Or(f.p(f.g0()), f.np(f.g0())); ex.t_param = f.k0();
    Derivation d{f.top(), f.ex(f.Or(f.p(f.g0()), f.np(f.g0()))), {ai, ex}};
    EXPECT(check(f.fb, d).ok());
    EXPECT(is_decomposed(d));
    auto sp = split(f.fb, d);
    EXPECT(sp.ok());
    EXPECT(sp.value().phi1.steps.size() == 2);   // all in Φ1
    EXPECT(sp.value().phi2.steps.empty());
    EXPECT(sp.value().a_prime == d.bottom);       // A' = bottom (no resource)
    // Φ1 and Φ2 each re-check.
    EXPECT(check(f.fb, sp.value().phi1).ok());
    EXPECT(check(f.fb, sp.value().phi2).ok());
}

// Decomposed across the boundary: (∃x.px)∨(∃x.px) —m∃→ ∃x.(px∨px) —ac→ ∃x.px.
// Both steps are resource-only, so Φ1 is empty, A' = top, Φ2 = both steps.
void test_decomposed_resource() {
    Fixture f;
    Derivation d{f.Or(f.ex(f.p(f.g0())), f.ex(f.p(f.g0()))), f.ex(f.p(f.g0())),
                 {S(Rule::MExists), S(Rule::Ac, {Dir::Down})}};
    EXPECT(check(f.fb, d).ok());
    EXPECT(is_decomposed(d));
    auto sp = split(f.fb, d);
    EXPECT(sp.ok());
    EXPECT(sp.value().phi1.steps.empty());
    EXPECT(sp.value().a_prime == d.top);
    EXPECT(sp.value().phi2.steps.size() == 2);
    EXPECT(check(f.fb, sp.value().phi1).ok());
    EXPECT(check(f.fb, sp.value().phi2).ok());
}

// Out-of-order: a resource step (m∃) BEFORE an MLS1^X step (∃) is NOT
// decomposed (an ∃ instantiation cannot follow a medial in Thm 17 order).
void test_not_decomposed_out_of_order() {
    Fixture f;
    // top = (∃x.px)∨(∃x.px); m∃ → ∃x.(px∨px); then a (bogus-placement) ai.
    Step ai = S(Rule::Ai, {Dir::Down, Dir::Left});  // placement irrelevant to the order check
    ai.f_param = f.p(f.g0());
    Derivation d{f.Or(f.ex(f.p(f.g0())), f.ex(f.p(f.g0()))), f.ex(f.p(f.g0())),
                 {S(Rule::MExists), ai}};
    // m∃ is resource-only at index 0 → boundary 0 → step 1 (ai) must be
    // resource, but ai is MLS1^X-only ⇒ not decomposed.
    EXPECT(!is_decomposed(d));
    EXPECT(split(f.fb, d).is_error());
}

void test_split_halves_compose() {
    // For any decomposed d that checks, Φ1.bottom == Φ2.top == A', and
    // checking Φ1 then Φ2 reproduces d.bottom.
    Fixture f;
    Step ai = S(Rule::Ai); ai.f_param = f.p(f.k0());
    Step ex = S(Rule::Ex); ex.f_param = f.Or(f.p(f.g0()), f.np(f.g0())); ex.t_param = f.k0();
    Derivation d{f.top(), f.ex(f.Or(f.p(f.g0()), f.np(f.g0()))), {ai, ex}};
    auto sp = split(f.fb, d);
    EXPECT(sp.ok());
    EXPECT(sp.value().phi1.bottom == sp.value().a_prime);
    EXPECT(sp.value().phi2.top == sp.value().a_prime);
    EXPECT(sp.value().phi2.bottom == d.bottom);
}

}  // namespace

int main() {
    test_classification();
    test_decomposed_all_linear();
    test_decomposed_resource();
    test_not_decomposed_out_of_order();
    test_split_halves_compose();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
