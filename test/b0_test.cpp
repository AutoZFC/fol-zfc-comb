// b0_test — Step 2 of STAGE3_RESET_PLAN.
//
// additive_to_multiplicative walks a Deriv once and rewrites every
// additive RCut to (|Γ| RWeakens) + (multiplicative RCut), preserving
// the outer node.concl. Tests:
//
//   - Smoke: a cut-free program passes through unchanged.
//   - Build round-trip on a real proof that contains cuts: count of
//     RCut nodes preserved; every cut in the output is multiplicative;
//     the WHOLE tree validates.
//   - Hand-built additive RCut: confirm the wrapped structure has the
//     expected shape (|Γ| RWeakens above the mult-Cut, in order).
//   - Already-multiplicative input passes through unchanged.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>

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

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

size_t count_cuts(const Deriv& d) {
    size_t n = 0;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            n = 1 + count_cuts(*r.left) + count_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n = count_cuts(*r.left) + count_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            n = count_cuts(*r.child);
        }
    }, d.rule);
    return n;
}

// Counts RCuts that are STRICTLY multiplicative (node.concl size = |Γ_L| + |Γ_R|
// and not coinciding with additive shape).
size_t count_strict_mult_cuts(const Deriv& d) {
    size_t n = 0;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            size_t gl = r.left->conclusion.size() - 1;
            size_t gr = r.right->conclusion.size() - 1;
            bool is_strict_mult = (d.conclusion.size() == gl + gr) &&
                                  !(d.conclusion.size() == gl && gl == gr);
            n = (is_strict_mult ? 1 : 0)
              + count_strict_mult_cuts(*r.left)
              + count_strict_mult_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n = count_strict_mult_cuts(*r.left)
              + count_strict_mult_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            n = count_strict_mult_cuts(*r.child);
        }
    }, d.rule);
    return n;
}

// =========================================================================
// Smoke: cut-free Deriv passes through unchanged.
// =========================================================================
void test_smoke_cut_free() {
    Runtime rt;
    auto loaded = rt.load_with_proofs(R"(
        axiom dummy: forall x. P(x)
        claim p_implies_p: forall x. (P(x) -> P(x))
        proof p_implies_p:
            fix x
            h = assume P(x)
            h_impl = implies_intro h
            h_fa = forall_intro h_impl
            qed h_fa
    )");
    assert(loaded.ok());
    auto nd_prog = nd::lower(loaded.value().proofs[0], rt.context());
    assert(nd_prog.ok());
    auto claim = rt.context().find_claim("p_implies_p");
    FormulaHandle goal = claim.value().get().root();
    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto lkr_prog = pass.apply(nd_prog.value());
    assert(lkr_prog.ok());
    FormulaBuilder builder(rt.context());
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    auto deriv = build(builder, goal_nnf, lkr_prog.value());
    assert(deriv.ok());

    CHECK(count_cuts(*deriv.value()) == 0);

    auto out = additive_to_multiplicative(*deriv.value());
    if (!out.ok()) {
        std::cerr << "FAIL: b0: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
}

// =========================================================================
// Real proof with implies_elim (NDtoLKR emits cuts): every additive cut
// becomes multiplicative, count preserved, full tree validates.
// =========================================================================
void test_syllogism_cuts_become_mult() {
    Runtime rt;
    auto loaded = rt.load_with_proofs(R"(
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
    )");
    assert(loaded.ok());
    auto nd_prog = nd::lower(loaded.value().proofs[0], rt.context());
    assert(nd_prog.ok());
    auto claim = rt.context().find_claim("all_q");
    FormulaHandle goal = claim.value().get().root();
    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto lkr_prog = pass.apply(nd_prog.value());
    assert(lkr_prog.ok());
    FormulaBuilder builder(rt.context());
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    auto deriv = build(builder, goal_nnf, lkr_prog.value());
    assert(deriv.ok());

    size_t cuts_before = count_cuts(*deriv.value());
    size_t mult_before = count_strict_mult_cuts(*deriv.value());
    CHECK(cuts_before > 0);
    CHECK(mult_before == 0);  // build() emits additive cuts only.

    auto out = additive_to_multiplicative(*deriv.value());
    if (!out.ok()) {
        std::cerr << "FAIL: b0: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }

    CHECK(count_cuts(*out.value()) == cuts_before);
    // Every cut after B0 is multiplicative (assuming non-empty Γ at each cut;
    // for empty-Γ cuts the additive and mult shapes coincide).
    size_t mult_after = count_strict_mult_cuts(*out.value());
    CHECK(mult_after == cuts_before);
    CHECK_OK(validate(*out.value()));

    // The top-level node.concl is unchanged.
    CHECK(out.value()->conclusion == deriv.value()->conclusion);
}

// =========================================================================
// Hand-built additive RCut: confirm the wrapped structure has the expected
// shape (|Γ| RWeakens above a mult-Cut, with W's added formulas = Γ in order).
// =========================================================================
void test_hand_built_additive_RCut_becomes_wrapped_mult() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaHandle Rimp = parse_root(ctx, "R -> R");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(Pimp);
    FormulaHandle Qnnf = b.to_nnf(Qimp);
    FormulaHandle Rnnf = b.to_nnf(Rimp);
    FormulaHandle P  = Pnnf.get().as_compound().right;
    FormulaHandle Q  = Qnnf.get().as_compound().right;
    FormulaHandle R  = Rnnf.get().as_compound().right;

    // Additive RCut on cut formula Q, with Γ = [P, R].
    //   left.concl  = [P, R, Q]    (Γ ++ {Q})
    //   right.concl = [P, R, ¬Q-shaped] — validate doesn't check the dual
    //                                     semantically, so use any sentinel.
    //   node.concl  = [P, R]
    // Children are RAx structurally (positions distinct, in range).
    FormulaHandle dual_marker = R;  // arbitrary distinct handle; validate ignores duality.

    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {P, R, Q};
    lefty->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {P, R, dual_marker};
    righty->rule = RAx{0, 1};
    auto add_cut = std::make_unique<Deriv>();
    add_cut->conclusion = {P, R};
    add_cut->rule = RCut{Q, std::move(lefty), std::move(righty)};

    CHECK_OK(validate(*add_cut));

    auto out = additive_to_multiplicative(*add_cut);
    if (!out.ok()) {
        std::cerr << "FAIL: b0: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Expect structure: RDuplicate{0} → RDuplicate{1} → RCut (mult, node =
    // [P,R,P,R]). The doubled context Γ,Γ is reached from Γ goal-directed by
    // DUPLICATING each entry (CUT_ELIM_DESIGN §4; see WEAKENING_FIX_DESIGN.md).
    //
    // wrap_with_duplicates builds k = n-1 .. 0 from the inside out:
    //   - innermost RDuplicate{1} copies node[1]=R, child = mult [P,R,P,R];
    //   - outermost RDuplicate{0} copies node[0]=P, concl [P,R].

    const Deriv* cur = out.value().get();
    CHECK(cur->conclusion == std::vector<FormulaHandle>({P, R}));

    auto* w1 = std::get_if<RDuplicate>(&cur->rule);
    if (!w1) { std::cerr << "FAIL: top is not RDuplicate\n"; ++g_failed; return; }
    CHECK(w1->src == 0);
    cur = w1->child.get();
    CHECK(cur->conclusion == std::vector<FormulaHandle>({P, R, P}));

    auto* w2 = std::get_if<RDuplicate>(&cur->rule);
    if (!w2) { std::cerr << "FAIL: second is not RDuplicate\n"; ++g_failed; return; }
    CHECK(w2->src == 1);
    cur = w2->child.get();
    CHECK(cur->conclusion == std::vector<FormulaHandle>({P, R, P, R}));

    auto* cut = std::get_if<RCut>(&cur->rule);
    if (!cut) { std::cerr << "FAIL: deepest is not RCut\n"; ++g_failed; return; }
    CHECK(cut->cut_formula == Q);
    CHECK(cut->left->conclusion  == std::vector<FormulaHandle>({P, R, Q}));
    CHECK(cut->right->conclusion == std::vector<FormulaHandle>({P, R, dual_marker}));

    // The cut at this depth has node.concl = [P,R,P,R] (|node|=4), |Γ_L|=2,
    // |Γ_R|=2 → mult shape.
    CHECK_OK(validate(*out.value()));
}

// =========================================================================
// Already-multiplicative RCut passes through unchanged.
// =========================================================================
void test_already_mult_passes_through() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle Pimp = parse_root(ctx, "P -> P");
    FormulaHandle Qimp = parse_root(ctx, "Q -> Q");
    FormulaBuilder b(ctx);
    FormulaHandle P = b.to_nnf(Pimp).get().as_compound().right;
    FormulaHandle Q = b.to_nnf(Qimp).get().as_compound().right;

    // Hand-build a mult-Cut directly: Γ_L = [P], Γ_R = [P]; cut formula Q;
    // node.concl = [P, P] (mult); left.concl = [P, Q]; right.concl = [P, Q-dual-marker].
    FormulaHandle dual_marker = P;  // validate ignores dual; reuse P.
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {P, Q};
    lefty->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {P, dual_marker};
    righty->rule = RAx{0, 1};
    auto mult_cut = std::make_unique<Deriv>();
    mult_cut->conclusion = {P, P};  // strict multiplicative shape (gl + gr = 1+1 = 2)
    mult_cut->rule = RCut{Q, std::move(lefty), std::move(righty)};

    CHECK_OK(validate(*mult_cut));

    auto out = additive_to_multiplicative(*mult_cut);
    if (!out.ok()) {
        std::cerr << "FAIL: b0 on mult: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    // Top-level should still be the cut (no W's added).
    auto* cut = std::get_if<RCut>(&out.value()->rule);
    if (!cut) { std::cerr << "FAIL: mult cut not preserved at top\n"; ++g_failed; return; }
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({P, P}));
    CHECK(cut->cut_formula == Q);
}

}  // namespace

int main() {
    test_smoke_cut_free();
    test_syllogism_cuts_become_mult();
    test_hand_built_additive_RCut_becomes_wrapped_mult();
    test_already_mult_passes_through();

    std::cout << "b0_test: " << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
