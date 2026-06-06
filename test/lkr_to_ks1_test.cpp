// K6.0 — LKR → KS1 front-end skeleton, end-to-end through the comb verifier.
//
// Builds the simplest cut-free LKR proof (⊢ A∨¬A: an axiom under one Or) as a
// `lkr_cut_elim::Deriv`, translates it to a KS1 derivation via `lkr_to_ks1`,
// runs it through the existing KS1→comb bridge (`build_comb_proof`), and checks
// the resulting combinatorial proof against ALL FOUR `CombVerifier` phases.
// This validates the full Deriv → Derivation → comb → verify integration path
// (the K6.0 obligation flip) before any of the general §VII machinery (K6.1+).

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/verifier.h"
#include "src/proof/ks1/checker.h"
#include "src/proof/translate/ks1_to_comb/read_skew.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include <iostream>
#include <memory>
#include <utility>

using namespace logic;
namespace lce = logic::proof::translate::lkr_cut_elim;
namespace l2k = logic::proof::translate::lkr_to_ks1;
using logic::proof::ks1_to_comb::build_comb_proof;

namespace {

int g_passed = 0, g_failed = 0;
#define EXPECT(...) do {                                                       \
    if (__VA_ARGS__) { ++g_passed; } else {                                   \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":"          \
                  << __LINE__ << "\n"; ++g_failed; }                          \
} while (0)

// Run all four CombVerifier phases against `goal`. Returns true iff all pass.
bool all_phases(GlobalContext& ctx, FormulaHandle goal,
                const proof::comb::CombProof& cp) {
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

// ⊢ A∨¬A : ROr{0} over RAx{0,1} on the premise [A, ¬A].
void test_excluded_middle_end_to_end() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle A = ctx.add_predicate("A", 0);   // 0-ary ⇒ a closed atom
    FormulaHandle a    = fb.predicate(A, {});
    FormulaHandle na   = fb.make_not(a);
    FormulaHandle goal = fb.make_or(a, na);          // A ∨ ¬A

    auto axd = std::make_unique<lce::Deriv>();
    axd->conclusion = {a, na};
    axd->rule = lce::RAx{0, 1};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(axd)};

    auto d = l2k::lkr_to_ks1(fb, root);
    EXPECT(d.ok());
    if (!d.ok()) { std::cerr << "  " << d.error().to_string() << "\n"; return; }

    // Intermediate gate: the produced derivation is a valid KS1 derivation.
    auto chk = proof::ks1::check(fb, d.value());
    EXPECT(chk.ok());
    if (chk.is_error()) std::cerr << "  ks1::check: " << chk.error().to_string() << "\n";

    // End-to-end: bridge to a comb proof and run the independent verifier.
    auto cp = build_comb_proof(fb, d.value());
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  build_comb_proof: " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ (A∨¬A) ∧ (B∨¬B) : RAnd{0, ∅} over two ROr-over-RAx branches. A genuine
// 2-axiom fonet — empty branch contexts, so no switch sequence:
//   t —Tu→ t∧t —Ai(A)@Left→ (A∨¬A)∧t —Ai(B)@Right→ (A∨¬A)∧(B∨¬B).
void test_conjunction_of_em_end_to_end() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle PA = ctx.add_predicate("A", 0);
    PredicateHandle PB = ctx.add_predicate("B", 0);
    FormulaHandle a = fb.predicate(PA, {}), na = fb.make_not(a);
    FormulaHandle b = fb.predicate(PB, {}), nb = fb.make_not(b);
    FormulaHandle aOr = fb.make_or(a, na);     // A∨¬A
    FormulaHandle bOr = fb.make_or(b, nb);     // B∨¬B
    FormulaHandle goal = fb.make_and(aOr, bOr);

    auto branch = [&](FormulaHandle lit, FormulaHandle nlit, FormulaHandle orF) {
        auto ax = std::make_unique<lce::Deriv>();
        ax->conclusion = {lit, nlit};
        ax->rule = lce::RAx{0, 1};
        auto orr = std::make_unique<lce::Deriv>();
        orr->conclusion = {orF};
        orr->rule = lce::ROr{0, std::move(ax)};
        return orr;
    };

    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::RAnd{/*principal=*/0, /*left_partition=*/{},
                          branch(a, na, aOr), branch(b, nb, bOr)};

    auto d = l2k::lkr_to_ks1(fb, root);
    EXPECT(d.ok());
    if (!d.ok()) { std::cerr << "  " << d.error().to_string() << "\n"; return; }
    auto chk = proof::ks1::check(fb, d.value());
    EXPECT(chk.ok());
    if (chk.is_error()) std::cerr << "  ks1::check: " << chk.error().to_string() << "\n";
    auto cp = build_comb_proof(fb, d.value());
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  build_comb_proof: " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

}  // namespace

int main() {
    test_excluded_middle_end_to_end();
    test_conjunction_of_em_end_to_end();
    std::cerr << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
