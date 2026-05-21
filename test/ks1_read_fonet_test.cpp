// KS1 linear core → fonet read-off (HSW 2021 Thm 33) — Track 2 phase K4.
// Validates that the fonet read off Φ1 is a genuine fonet over [[A']], by
// running CombVerifier's well-formedness + fonet phases on a CombProof with
// the read-off fonet as source, [[A']] as target, and the identity fibration.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/verifier.h"
#include "src/proof/ks1/derivation.h"
#include "src/proof/translate/ks1_to_comb/read_fonet.h"

#include <iostream>
#include <vector>

using namespace logic;
using namespace logic::proof::ks1;
using logic::proof::ks1_to_comb::read_fonet;
using logic::proof::ks1_to_comb::FonetReadoff;

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
    PredicateHandle P1 = ctx.add_predicate("p", 1);
    FormulaHandle top() { return fb.make_not(fb.make_bottom()); }
    FormulaHandle p(Term t) { return fb.predicate(P1, {t}); }
    FormulaHandle np(Term t) { return fb.make_not(fb.predicate(P1, {t})); }
    FormulaHandle Or(FormulaHandle l, FormulaHandle r) { return fb.make_or(l, r); }
    Term g0() { return Term::generalized(0); }
    Term k0() { return Term::fixed(0); }
};

Step S(Rule r, Path c = {}) { return Step{r, std::move(c)}; }

// Run CombVerifier phases 0 + 2 on {source=readoff.fonet, target, identity}.
bool fonet_verifies(GlobalContext& ctx, const FonetReadoff& ro) {
    proof::comb::CombProof cp;
    cp.source = ro.fonet;
    cp.target = ro.target;
    cp.fibration.resize(ro.fonet.num_vertex);
    for (size_t i = 0; i < ro.fonet.num_vertex; ++i) cp.fibration[i] = i;  // identity
    proof::comb::CombVerifier v;
    auto wf = v.verify_well_formed(cp);
    if (wf.is_error()) { std::cerr << "  wf: " << wf.error().to_string() << "\n"; return false; }
    auto fn = v.verify_fonet(cp);
    if (fn.is_error()) { std::cerr << "  fonet: " << fn.error().to_string() << "\n"; return false; }
    return true;
}

// Φ1 = t —∀→ ∀x.t —ai(@Down,a=px)→ ∀x.(px ∨ p̄x). Universal binder, one link,
// empty dualizer.
void test_forall_em() {
    Fixture f;
    Step ai = S(Rule::Ai, {Dir::Down}); ai.f_param = f.p(f.g0());
    Derivation phi1{f.top(), f.fb.make_quantified(Op::Forall, f.Or(f.p(f.g0()), f.np(f.g0()))),
                    {S(Rule::ForallUnit), ai}};
    auto ro = read_fonet(f.fb, phi1);
    EXPECT(ro.ok());
    if (ro.ok()) {
        EXPECT(ro.value().fonet.links.size() == 1);
        EXPECT(ro.value().fonet.dualizer.empty());
        EXPECT(ro.value().fonet.num_vertex == 3);  // binder + 2 atoms
        EXPECT(fonet_verifies(f.ctx, ro.value()));
    }
}

// Φ1 = t —∀→ ∀y.t —ai(@Down,a=p̄y)→ ∀y.(p̄y∨py) —∃(@Down,witness y)→
//      ∀y.∃x.(p̄x ∨ py).  The ∃ is witnessed by the UNIVERSAL var y, so the
// dualizer δ(x)=y maps the existential to a universal binder — exactly the
// fonet-dualizer shape of the paper's Fig. 3 (and the only kind this
// function-symbol-free fragment's verifier accepts: image vars must be
// universal binders, so an existential witnessed by a fresh constant is not
// representable).
void test_forall_exists_drinker() {
    Fixture f;
    Step ai = S(Rule::Ai, {Dir::Down}); ai.f_param = f.np(f.g0());        // a = p̄(y)
    Step ex = S(Rule::Ex, {Dir::Down});
    ex.f_param = f.Or(f.np(f.g0()), f.p(Term::generalized(1)));           // A = p̄x ∨ py
    ex.t_param = f.g0();                                                  // witness x := y
    FormulaHandle bottom = f.fb.make_quantified(Op::Forall,
        f.fb.make_quantified(Op::Exists, f.Or(f.np(f.g0()), f.p(Term::generalized(1)))));
    Derivation phi1{f.top(), bottom, {S(Rule::ForallUnit), ai, ex}};
    auto ro = read_fonet(f.fb, phi1);
    EXPECT(ro.ok());
    if (ro.ok()) {
        EXPECT(ro.value().fonet.links.size() == 1);
        EXPECT(ro.value().fonet.dualizer.size() == 1);  // ∃ var ↦ universal var
        EXPECT(fonet_verifies(f.ctx, ro.value()));
    }
}

// Reject: a linear core not starting at ⊤.
void test_reject_non_top_start() {
    Fixture f;
    Derivation phi1{f.p(f.k0()), f.p(f.k0()), {}};
    EXPECT(read_fonet(f.fb, phi1).is_error());
}

}  // namespace

int main() {
    test_forall_em();
    test_forall_exists_drinker();
    test_reject_non_top_start();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
