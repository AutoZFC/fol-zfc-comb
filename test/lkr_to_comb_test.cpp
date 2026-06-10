// Direct LKR → comb fold (Hughes §11.1) — the second, parallel back-end track.
//
// Phase 1: the switch-free propositional fragment (RAx, ROr, RExchange). Builds
// cut-free `lkr_cut_elim::Deriv` trees by hand, folds them to a `comb::CombProof`
// via `lkr_to_comb`, and checks the result against ALL FOUR `CombVerifier`
// phases — the same oracle the LKR→KS1→comb track uses. Mirrors the K6.0
// skeleton test for the KS1 track (lkr_to_ks1_test.cpp).

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/verifier.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_to_comb/lkr_to_comb.h"

#include <iostream>
#include <memory>
#include <utility>

using namespace logic;
namespace lce = logic::proof::translate::lkr_cut_elim;
namespace l2c = logic::proof::translate::lkr_to_comb;

namespace {

int g_passed = 0, g_failed = 0;
#define EXPECT(...) do {                                                       \
    if (__VA_ARGS__) { ++g_passed; } else {                                   \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":"          \
                  << __LINE__ << "\n"; ++g_failed; }                          \
} while (0)

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
void test_excluded_middle() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle A = ctx.add_predicate("A", 0);
    FormulaHandle a    = fb.predicate(A, {});
    FormulaHandle na   = fb.make_not(a);
    FormulaHandle goal = fb.make_or(a, na);

    auto axd = std::make_unique<lce::Deriv>();
    axd->conclusion = {a, na};
    axd->rule = lce::RAx{0, 1};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(axd)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ ¬A∨A : same, but the dual pair is in the other order, and an RExchange
// reorders the axiom's two entries before the Or groups them. Exercises the
// RExchange entry-swap + fibration remap and the θ-vertex offset shift.
void test_excluded_middle_swapped() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle A = ctx.add_predicate("A", 0);
    FormulaHandle a    = fb.predicate(A, {});
    FormulaHandle na   = fb.make_not(a);
    FormulaHandle goal = fb.make_or(na, a);   // ¬A ∨ A

    auto axd = std::make_unique<lce::Deriv>();
    axd->conclusion = {a, na};
    axd->rule = lce::RAx{0, 1};
    auto exd = std::make_unique<lce::Deriv>();
    exd->conclusion = {na, a};                // swapped
    exd->rule = lce::RExchange{0, 1, std::move(axd)};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(exd)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// Helper: ROr{0} over RAx{0,1} on [p, ¬p] — a closed EM proof of p∨¬p.
std::unique_ptr<lce::Deriv> em_proof(FormulaBuilder& fb, FormulaHandle p) {
    FormulaHandle np = fb.make_not(p);
    auto ax = std::make_unique<lce::Deriv>();
    ax->conclusion = {p, np};
    ax->rule = lce::RAx{0, 1};
    auto orr = std::make_unique<lce::Deriv>();
    orr->conclusion = {fb.make_or(p, np)};
    orr->rule = lce::ROr{0, std::move(ax)};
    return orr;
}

// ⊢ (A∨¬A) ∧ (B∨¬B) : RAnd{0, ∅} over two EM branches. Empty branch contexts,
// both strong — fonet fusion with the full P_L×P_R cross-join (matches the ∧).
void test_conjunction_of_em() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    FormulaHandle a = fb.predicate(ctx.add_predicate("A", 0), {});
    FormulaHandle b = fb.predicate(ctx.add_predicate("B", 0), {});
    FormulaHandle goal = fb.make_and(fb.make_or(a, fb.make_not(a)),
                                     fb.make_or(b, fb.make_not(b)));
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::RAnd{0, {}, em_proof(fb, a), em_proof(fb, b)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ (A∨¬A) ∨ C : the EM proof, then C weakened in and folded by a second Or.
// C is uncovered in the fibration (Hughes §11.1 W, Case A scaffolding).
void test_weakening_scaffolding() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    FormulaHandle a = fb.predicate(ctx.add_predicate("A", 0), {});
    FormulaHandle c = fb.predicate(ctx.add_predicate("C", 0), {});
    FormulaHandle em = fb.make_or(a, fb.make_not(a));
    FormulaHandle goal = fb.make_or(em, c);

    auto wk = std::make_unique<lce::Deriv>();        // [em, c] — c weakened in at idx 1
    wk->conclusion = {em, c};
    wk->rule = lce::RWeaken{1, em_proof(fb, a)};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(wk)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ ∀y.(p(y)∨¬p(y)) : RForall over the EM proof of the instantiated body.
// Exercises the universal binder vertex (Case B, +-attached, no cograph edge)
// and the root binding-edge derivation (binder var 0 → both p atoms).
void test_forall_em() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle P = ctx.add_predicate("p", 1);
    const var_index Y = 0;                              // eigenvar for ∀y
    FormulaHandle pY  = fb.predicate(P, {Term::fixed(Y)});
    FormulaHandle body_inst = fb.make_or(pY, fb.make_not(pY));   // p(Y)∨¬p(Y)
    FormulaHandle pg  = fb.predicate(P, {Term::generalized(0)});
    FormulaHandle goal = fb.make_quantified(Op::Forall, fb.make_or(pg, fb.make_not(pg)));

    auto ax = std::make_unique<lce::Deriv>();
    ax->conclusion = {pY, fb.make_not(pY)};
    ax->rule = lce::RAx{0, 1};
    auto orr = std::make_unique<lce::Deriv>();
    orr->conclusion = {body_inst};
    orr->rule = lce::ROr{0, std::move(ax)};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::RForall{0, Y, std::move(orr)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ ∀y.∃x.(¬p(x)∨p(y)) — the DRINKER. RForall over RExists (witness x:=y) over
// the EM proof of ¬p(y)∨p(y). Exercises the ∃ binder vertex (×-attached to the
// body) + the dualizer δ(x)=y, canonicalized at the root. First comb-verified ∃
// for the direct track.
void test_drinker() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle P = ctx.add_predicate("p", 1);
    const var_index Y = 0;                              // eigenvar for ∀y (witness for ∃x)
    FormulaHandle pY   = fb.predicate(P, {Term::fixed(Y)});
    FormulaHandle npY  = fb.make_not(pY);
    FormulaHandle pg0  = fb.predicate(P, {Term::generalized(0)});  // p(x) inside ∃
    FormulaHandle pg1  = fb.predicate(P, {Term::generalized(1)});  // p(y) inside ∃

    // goal = ∀y.∃x.(¬p(x)∨p(y))
    FormulaHandle ex_body = fb.make_or(fb.make_not(pg0), pg1);
    FormulaHandle goal = fb.make_quantified(Op::Forall,
                            fb.make_quantified(Op::Exists, ex_body));
    // exists-node principal = ∃x.(¬p(x)∨p(Y))  (∀ instantiated; ∃ body keeps gen0 = x)
    FormulaHandle ex_principal = fb.make_quantified(
        Op::Exists, fb.make_or(fb.make_not(pg0), pY));

    auto ax = std::make_unique<lce::Deriv>();
    ax->conclusion = {npY, pY};
    ax->rule = lce::RAx{0, 1};
    auto orr = std::make_unique<lce::Deriv>();
    orr->conclusion = {fb.make_or(npY, pY)};           // ¬p(Y)∨p(Y)
    orr->rule = lce::ROr{0, std::move(ax)};
    auto exd = std::make_unique<lce::Deriv>();
    exd->conclusion = {ex_principal};
    exd->rule = lce::RExists{0, Term::fixed(Y), std::move(orr)};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::RForall{0, Y, std::move(exd)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ ¬A ∨ (A∧A) : the A∧A needs ¬A on BOTH And branches, so ¬A is duplicated.
// Exercises RDuplicate — the contraction folds the duplicate ¬A onto the kept
// copy, giving a NON-INJECTIVE fibration (two source ¬A vertices → one target
// position). First contraction for the direct track.
void test_contraction() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    FormulaHandle a  = fb.predicate(ctx.add_predicate("A", 0), {});
    FormulaHandle na = fb.make_not(a);
    FormulaHandle aa = fb.make_and(a, a);
    FormulaHandle goal = fb.make_or(na, aa);            // ¬A ∨ (A∧A)

    // left/right And branches: each ⊢ [¬A, A] (an axiom).
    auto mk_ax = [&]() {
        auto ax = std::make_unique<lce::Deriv>();
        ax->conclusion = {na, a};
        ax->rule = lce::RAx{0, 1};
        return ax;
    };
    auto andd = std::make_unique<lce::Deriv>();         // ⊢ [¬A, A∧A, ¬A]
    andd->conclusion = {na, aa, na};
    andd->rule = lce::RAnd{1, {0}, mk_ax(), mk_ax()};
    auto dupd = std::make_unique<lce::Deriv>();          // ⊢ [¬A, A∧A] (contract)
    dupd->conclusion = {na, aa};
    dupd->rule = lce::RDuplicate{0, std::move(andd)};
    lce::Deriv root;
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(dupd)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

// ⊢ (∀y.∃x.(¬p(x)∨p(y))) ∨ C : the drinker, with C weakened in ABOVE the
// quantifier subtree and folded by an Or. REGRESSION for the binder-record-drop
// bug class: RWeaken and ROr (both written before WalkResult carried the binder
// records) must propagate forall_binders/ex_witness up past them — otherwise the
// ∃'s dualizer entry is lost and verify_fonet rejects ("missing ∃-binder var").
void test_weakening_above_quantifier() {
    GlobalContext ctx;
    FormulaBuilder fb(ctx);
    PredicateHandle P = ctx.add_predicate("p", 1);
    const var_index Y = 0;
    FormulaHandle pY   = fb.predicate(P, {Term::fixed(Y)});
    FormulaHandle npY  = fb.make_not(pY);
    FormulaHandle pg0  = fb.predicate(P, {Term::generalized(0)});
    FormulaHandle pg1  = fb.predicate(P, {Term::generalized(1)});
    FormulaHandle drinker = fb.make_quantified(Op::Forall,
                              fb.make_quantified(Op::Exists,
                                fb.make_or(fb.make_not(pg0), pg1)));
    FormulaHandle c    = fb.predicate(ctx.add_predicate("C", 0), {});
    FormulaHandle goal = fb.make_or(drinker, c);
    FormulaHandle ex_principal = fb.make_quantified(
        Op::Exists, fb.make_or(fb.make_not(pg0), pY));

    auto ax = std::make_unique<lce::Deriv>();
    ax->conclusion = {npY, pY};
    ax->rule = lce::RAx{0, 1};
    auto orr = std::make_unique<lce::Deriv>();
    orr->conclusion = {fb.make_or(npY, pY)};
    orr->rule = lce::ROr{0, std::move(ax)};
    auto exd = std::make_unique<lce::Deriv>();
    exd->conclusion = {ex_principal};
    exd->rule = lce::RExists{0, Term::fixed(Y), std::move(orr)};
    auto fard = std::make_unique<lce::Deriv>();
    fard->conclusion = {drinker};
    fard->rule = lce::RForall{0, Y, std::move(exd)};
    auto wk = std::make_unique<lce::Deriv>();           // weaken C in at idx 1
    wk->conclusion = {drinker, c};
    wk->rule = lce::RWeaken{1, std::move(fard)};
    lce::Deriv root;                                     // fold (drinker)∨C
    root.conclusion = {goal};
    root.rule = lce::ROr{0, std::move(wk)};

    auto cp = l2c::lkr_to_comb(fb, root);
    EXPECT(cp.ok());
    if (cp.is_error()) { std::cerr << "  " << cp.error().to_string() << "\n"; return; }
    EXPECT(all_phases(ctx, goal, cp.value()));
}

}  // namespace

int main() {
    test_excluded_middle();
    test_excluded_middle_swapped();
    test_conjunction_of_em();
    test_weakening_scaffolding();
    test_forall_em();
    test_drinker();
    test_contraction();
    test_weakening_above_quantifier();
    std::cerr << "lkr_to_comb_test: " << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
