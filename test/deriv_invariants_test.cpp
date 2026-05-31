// deriv_invariants_test — Step 1 of STAGE3_RESET_PLAN: typed Deriv conventions.
//
// validate() enforces the per-rule positional invariants spelled out in
// STAGE3_RESET_PLAN.md §4. The load-bearing case is RWeaken (the
// convention bug from the 05-27 audit): child must be POST-W = bigger
// than node by exactly one. validate is wired into build(), so any
// build-produced Deriv that violates an invariant fails early; this
// test also constructs hand-built Derivs in both the canonical and the
// inverted convention to confirm validate catches the latter.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>
#include <string>

using namespace logic;
using namespace logic::proof;
using namespace logic::proof::translate::lkr_cut_elim;

namespace {

int g_passed = 0;
int g_failed = 0;

#define CHECK(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define CHECK_OK(expr) do { \
    auto _r = (expr); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Ok, got: " \
                  << _r.error().to_string() << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define CHECK_ERR(expr) do { \
    auto _r = (expr); \
    if (!_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Err, got Ok at " \
                  __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

// =========================================================================
// Positive — round-trip via build() exercises validate() automatically.
// If build returns Ok, the resulting Deriv satisfies every invariant.
// =========================================================================
void build_round_trip(const char* label, const char* src, const char* claim_name) {
    Runtime rt;
    auto parsed = rt.load_with_proofs(src);
    if (!parsed.ok()) {
        std::cerr << "FAIL[" << label << "]: load: "
                  << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = nd::lower(parsed.value().proofs[0], rt.context());
    if (!nd_prog.ok()) {
        std::cerr << "FAIL[" << label << "]: nd lower: "
                  << nd_prog.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto claim = rt.context().find_claim(claim_name);
    if (!claim.has_value()) {
        std::cerr << "FAIL[" << label << "]: claim not found\n";
        ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();
    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto lkr_prog = pass.apply(nd_prog.value());
    if (!lkr_prog.ok()) {
        std::cerr << "FAIL[" << label << "]: nd_to_lkr: "
                  << lkr_prog.error().to_string() << "\n";
        ++g_failed; return;
    }
    FormulaBuilder builder(rt.context());
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    auto deriv = build(builder, goal_nnf, lkr_prog.value());
    if (!deriv.ok()) {
        std::cerr << "FAIL[" << label << "]: build (which calls validate): "
                  << deriv.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
    std::cout << "  ok[" << label << "]: build∘validate ok\n";
}

void test_build_round_trip_smoke() {
    build_round_trip("p_implies_p", R"(
        axiom dummy: forall x. P(x)
        claim p_implies_p: forall x. (P(x) -> P(x))
        proof p_implies_p:
            fix x
            h = assume P(x)
            h_impl = implies_intro h
            h_fa = forall_intro h_impl
            qed h_fa
    )", "p_implies_p");

    build_round_trip("syllogism", R"(
        axiom all_p: forall x. P(x)
        axiom all_p_q: forall x. (P(x) -> Q(x))
        claim all_q: forall x. Q(x)
        proof all_q:
            fix x
            h_pax = use all_p
            h_p = forall_elim h_pax, x
            h_pqax = use all_p_q
            h_pq = forall_elim h_pqax, x
            h_q = implies_elim h_pq, h_p
            h_fa = forall_intro h_q
            qed h_fa
    )", "all_q");

    build_round_trip("and_intro", R"(
        axiom all_p: forall x. P(x)
        axiom all_q: forall x. Q(x)
        claim all_pq: forall x. (P(x) & Q(x))
        proof all_pq:
            fix x
            h_pax = use all_p
            h_p = forall_elim h_pax, x
            h_qax = use all_q
            h_q = forall_elim h_qax, x
            h_pq = and_intro h_p, h_q
            h_fa = forall_intro h_pq
            qed h_fa
    )", "all_pq");
}

// =========================================================================
// Positive — hand-built minimal Derivs in the canonical convention.
// =========================================================================
void test_hand_built_canonical_RAx_and_ROr() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder b(ctx);
    FormulaHandle goal_nnf = b.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P};
    leaf->rule = RAx{0, 1};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(leaf)};
    CHECK_OK(validate(*root));
}

void test_hand_built_canonical_RWeaken() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle Qnnf = b.to_nnf(Qimp);
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle P    = Pnnf.get().as_compound().right;
    FormulaHandle Q    = Qnnf.get().as_compound().right;

    // Canonical (goal-directed W = drop): node = [notP, P, Q] (has the entry
    // to drop), child = [notP, P] (smaller, Q at idx 2 dropped).
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P};
    leaf->rule = RAx{0, 1};
    auto w = std::make_unique<Deriv>();
    w->conclusion = {notP, P, Q};
    w->rule = RWeaken{2, std::move(leaf)};
    CHECK_OK(validate(*w));
}

void test_hand_built_canonical_RDuplicate() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle P    = Pnnf.get().as_compound().right;

    // Canonical Duplicate: node = [notP, P] (smaller), child = [notP, P, P]
    // (bigger, a copy of idx 1 appended).
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P, P};
    leaf->rule = RAx{0, 1};
    auto d = std::make_unique<Deriv>();
    d->conclusion = {notP, P};
    d->rule = RDuplicate{1, std::move(leaf)};
    CHECK_OK(validate(*d));
}

void test_hand_built_canonical_RCut_additive() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle P    = Pnnf.get().as_compound().right;

    // Cut on P. Additive: left.conclusion = [notP] ++ [P], right.conclusion = [notP] ++ [¬P].
    // node.conclusion = [notP].
    FormulaHandle dual = b.to_nnf(b.make_not(P));  // = notP (in NNF).
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {notP, P};
    lefty->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {notP, dual};
    righty->rule = RAx{0, 1};  // notP at 0 dual to dual = notP? Actually we need real duals.
    // Skip the dual semantics check — validate doesn't check NNF duality.
    // We're only exercising the structural shape.
    auto root = std::make_unique<Deriv>();
    root->conclusion = {notP};
    root->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*root));
}

// =========================================================================
// Negative — the 05-27 bug shape: inverted RWeaken convention.
//
// If a future case-author writes child smaller than node (the old test-
// suite convention), validate must catch it. This is the canary.
// =========================================================================
void test_inverted_RWeaken_convention_caught() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle Qnnf = b.to_nnf(Qimp);
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle P    = Pnnf.get().as_compound().right;
    FormulaHandle Q    = Qnnf.get().as_compound().right;

    // INVERTED for the goal-directed W: child BIGGER than node (that is a
    // Duplicate shape, not a Weakening). validate must reject — RWeaken
    // requires child = node − {idx} (child smaller).
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P, Q};
    leaf->rule = RAx{0, 1};
    auto w = std::make_unique<Deriv>();
    w->conclusion = {notP, P};
    w->rule = RWeaken{0, std::move(leaf)};
    CHECK_ERR(validate(*w));
}

// =========================================================================
// Negative — RAnd partition violations.
// =========================================================================
void test_RAnd_partition_violations() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle pq   = parse_root(ctx, "P & Q");
    FormulaBuilder b(ctx);
    FormulaHandle pq_nnf = b.to_nnf(pq);  // P ∧ Q
    FormulaHandle phi  = pq_nnf.get().as_compound().left;
    FormulaHandle psi  = pq_nnf.get().as_compound().right;
    (void)Pimp;  // kept for symmetry with other tests; not used here.

    // Build a Deriv for ⊢ R, P∧Q where R is some atom.
    FormulaHandle Rimp = parse_root(ctx, "R -> R");
    FormulaHandle Rnnf = b.to_nnf(Rimp);
    FormulaHandle Rlit = Rnnf.get().as_compound().right;

    // Correct shape first to confirm baseline.
    auto leftL = std::make_unique<Deriv>(); leftL->conclusion = {Rlit, phi};
        leftL->rule = RAx{0, 1};  // structural shape only; ignore dual semantics.
    auto rightL = std::make_unique<Deriv>(); rightL->conclusion = {psi};
        rightL->rule = RAx{0, 0};  // intentionally a=b -> will fail validate.

    // Top-level: principal=1 (the ∧), left_partition={0} (Rlit goes left).
    // Expected: left.conclusion = [Rlit, phi]; right.conclusion = [psi].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Rlit, pq_nnf};
    root->rule = RAnd{1, {0}, std::move(leftL), std::move(rightL)};
    // RAnd shape ok at top, but right child has RAx{0,0} which is invalid.
    CHECK_ERR(validate(*root));

    // Now build a clean root with a partition that contains the principal.
    auto cleanL = std::make_unique<Deriv>(); cleanL->conclusion = {Rlit, phi};
        cleanL->rule = RAx{0, 1};
    auto cleanR = std::make_unique<Deriv>(); cleanR->conclusion = {psi};
        cleanR->rule = RAx{0, 0};  // doesn't matter — fail will be at root.
    auto bad_root = std::make_unique<Deriv>();
    bad_root->conclusion = {Rlit, pq_nnf};
    bad_root->rule = RAnd{1, {1}, std::move(cleanL), std::move(cleanR)};  // partition contains principal
    CHECK_ERR(validate(*bad_root));
}

// =========================================================================
// Negative — RCut child not extended by cut_formula.
// =========================================================================
void test_RCut_child_shape_caught() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle P    = Pnnf.get().as_compound().right;

    // node.conclusion = [notP]; but left.conclusion is just [notP] (no +cut).
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {notP};  // WRONG — should be [notP, P]
    lefty->rule = RAx{0, 0};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {notP, notP};
    righty->rule = RAx{0, 1};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {notP};
    root->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_ERR(validate(*root));
}

// =========================================================================
// Negative — RContract requires concl[i] == concl[j].
// =========================================================================
void test_RContract_duplicate_required() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle Qnnf = b.to_nnf(Qimp);
    FormulaHandle P = Pnnf.get().as_compound().right;
    FormulaHandle Q = Qnnf.get().as_compound().right;

    // node.conclusion = [P, Q] (not duplicates). Trying to contract i=0 j=1.
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {P};
    leaf->rule = RAx{0, 0};  // shape only
    auto root = std::make_unique<Deriv>();
    root->conclusion = {P, Q};
    root->rule = RContract{0, 1, std::move(leaf)};
    CHECK_ERR(validate(*root));
}

// =========================================================================
// Negative — RExchange must actually swap.
// =========================================================================
void test_RExchange_must_swap() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle Qnnf = b.to_nnf(Qimp);
    FormulaHandle P = Pnnf.get().as_compound().right;
    FormulaHandle Q = Qnnf.get().as_compound().right;

    // node = [P, Q]; child should be [Q, P] for Exchange{0, 1}; but we give [P, Q].
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {P, Q};  // WRONG — should be {Q, P}
    leaf->rule = RAx{0, 1};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {P, Q};
    root->rule = RExchange{0, 1, std::move(leaf)};
    CHECK_ERR(validate(*root));
}

}  // namespace

int main() {
    test_build_round_trip_smoke();
    test_hand_built_canonical_RAx_and_ROr();
    test_hand_built_canonical_RWeaken();
    test_hand_built_canonical_RDuplicate();
    test_hand_built_canonical_RCut_additive();
    test_inverted_RWeaken_convention_caught();
    test_RAnd_partition_violations();
    test_RCut_child_shape_caught();
    test_RContract_duplicate_required();
    test_RExchange_must_swap();

    std::cout << "deriv_invariants_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
