// reduce_test — Step 3 of STAGE3_RESET_PLAN: cut-elim driver scaffold.
//
// Tests:
//   - degree() correctness on various formulas.
//   - find_topmost_max_deg_cut picks the right cut (max degree, topmost).
//   - eliminate_cuts on cut-free trees: returns unchanged.
//   - eliminate_cuts on trees with cuts: returns unchanged (all §5 case
//     stubs return "not implemented" in Step 3; driver gives up).
//
// Step 4 will fill in cases and add reduction-progress tests.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/reduce.h"
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

#define CHECK_EQ(a, b) do { \
    auto _a = (a); auto _b = (b); \
    if (_a == _b) { ++g_passed; } else { \
        std::cerr << "FAIL: " #a " == " #b ": " << _a << " != " << _b \
                  << " at " __FILE__ ":" << __LINE__ << "\n"; \
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
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            n = count_cuts(*r.child);
        }
    }, d.rule);
    return n;
}

// =========================================================================
// degree() on various formulas.
// =========================================================================
void test_degree() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();

    // P alone: degree 0 (atomic predicate).
    {
        FormulaHandle f = parse_root(ctx, "P -> P");  // ¬P ∨ P in NNF
        FormulaBuilder b(ctx);
        FormulaHandle nnf = b.to_nnf(f);
        FormulaHandle P = nnf.get().as_compound().right;
        CHECK_EQ(degree(P), 0u);
    }
    // ¬P (Compound{Not, P}): NNF would push not down to atomic literal,
    // but raw ¬P (in non-NNF) has degree 1.
    // ∧ of two atoms: degree 1.
    {
        FormulaHandle f = parse_root(ctx, "P & Q");
        FormulaBuilder b(ctx);
        FormulaHandle nnf = b.to_nnf(f);  // P ∧ Q (already in NNF)
        CHECK_EQ(degree(nnf), 1u);
    }
    // (P ∧ Q) ∨ R: degree 2.
    {
        FormulaHandle f = parse_root(ctx, "(P & Q) | R");
        FormulaBuilder b(ctx);
        FormulaHandle nnf = b.to_nnf(f);
        CHECK_EQ(degree(nnf), 2u);
    }
    // ∀x.P(x): degree 1 (quantified, body is atom).
    {
        FormulaHandle f = parse_root(ctx, "forall x. P(x)");
        FormulaBuilder b(ctx);
        FormulaHandle nnf = b.to_nnf(f);
        CHECK_EQ(degree(nnf), 1u);
    }
    // ∀x.∃y.(P(x) ∧ Q(y)): degree 3 (∀ over ∃ over ∧).
    {
        FormulaHandle f = parse_root(ctx, "forall x. exists y. (P(x) & Q(y))");
        FormulaBuilder b(ctx);
        FormulaHandle nnf = b.to_nnf(f);
        CHECK_EQ(degree(nnf), 3u);
    }
}

// =========================================================================
// find_topmost_max_deg_cut on hand-built trees.
// =========================================================================

// Helper: hand-build an additive RCut at conclusion Γ with cut formula φ.
// Children are RAx leaves on extended Γ ++ {φ} / Γ ++ {dual_marker}.
DerivPtr make_additive_cut(const std::vector<FormulaHandle>& Γ,
                            FormulaHandle phi,
                            FormulaHandle dual_marker) {
    auto leftc  = Γ; leftc.push_back(phi);
    auto rightc = Γ; rightc.push_back(dual_marker);
    auto l = std::make_unique<Deriv>(); l->conclusion = leftc;  l->rule = RAx{0, 0 == leftc.size()-1 ? 0 : (leftc.size()-1)};
    // Avoid invalid RAx (a == b). Use {0, last}.
    l->rule = RAx{0, leftc.size() - 1};
    auto r = std::make_unique<Deriv>(); r->conclusion = rightc; r->rule = RAx{0, rightc.size() - 1};
    auto n = std::make_unique<Deriv>(); n->conclusion = Γ;
    n->rule = RCut{phi, std::move(l), std::move(r)};
    return n;
}

void test_find_topmost_single_cut() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle P  = parse_root(ctx, "P -> P");
    FormulaHandle pq = parse_root(ctx, "P & Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf  = b.to_nnf(P);
    FormulaHandle Q     = Pnnf.get().as_compound().right;     // atom P; dummy
    FormulaHandle PandQ = b.to_nnf(pq);                       // P ∧ Q, degree 1

    auto cut = make_additive_cut({Q}, PandQ, Q);
    CHECK_OK(validate(*cut));

    auto cand = find_topmost_max_deg_cut(*cut);
    CHECK(cand.has_value());
    CHECK_EQ(cand->cut_degree, 1u);
    CHECK_EQ(cand->path.size(), 0u);  // the root IS the cut.
}

void test_find_topmost_picks_max_degree() {
    // Tree: outer cut on P (deg 0) above inner cut on (P∧Q) (deg 1).
    // Topmost MAX-DEG cut should be the inner one, not the outer.
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle P_dom = parse_root(ctx, "P -> P");
    FormulaHandle pq    = parse_root(ctx, "P & Q");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf  = b.to_nnf(P_dom);
    FormulaHandle P     = Pnnf.get().as_compound().right;
    FormulaHandle PandQ = b.to_nnf(pq);

    // Inner cut: Γ = [P]; cut formula PandQ (deg 1).
    auto inner = make_additive_cut({P}, PandQ, P);

    // Outer cut: Γ = []; cut formula P (deg 0); LEFT child is inner cut
    // (whose conclusion is [P]); RIGHT child is a simple Ax leaf.
    auto outer_left  = std::move(inner);
    outer_left->conclusion.push_back(P);  // turn it into a cut whose CONCLUSION is [P], which becomes the LEFT side of the outer cut (= [P, P_outer_cut_formula])
    // Actually this hand-build is fiddly. Let me restructure.

    // Forget the awkward composition. Build directly:
    //   outer: cut formula P; node.concl = []; left.concl = [P]; right.concl = [P_dual].
    //   inner (= outer.left): cut formula PandQ; node.concl = [P]; left.concl = [P, PandQ];
    //                         right.concl = [P, marker].
    auto inner2 = make_additive_cut({P}, PandQ, P);  // node.concl = [P]
    auto right_leaf = std::make_unique<Deriv>();
    right_leaf->conclusion = {P};
    right_leaf->rule = RAx{0, 0};  // invalid (a==b); change.
    // Hmm need a structurally-valid leaf. Use ROne with idx 0 (we don't care if it's
    // semantically truth-shaped; validate only checks idx in range).
    right_leaf->rule = ROne{0};

    auto outer = std::make_unique<Deriv>();
    outer->conclusion = {};
    outer->rule = RCut{P, std::move(inner2), std::move(right_leaf)};
    // Wait — outer's left child must have conclusion = outer.concl ++ {cut_formula}
    // = [] ++ [P] = [P]. The inner cut's node.concl is [P]. ✓
    // outer's right child must have conclusion = outer.concl ++ {dual} = [P_dual].
    // We set right_leaf.conclusion = [P]; we're claiming P is its own dual for
    // validate purposes (validate doesn't check duality).

    // The above is getting confused. Let me simplify by checking what validate
    // actually expects and writing it cleanly.

    // For a clean two-cut test, just ensure validate passes — that means the
    // additive shape is correct.

    CHECK_OK(validate(*outer));

    auto cand = find_topmost_max_deg_cut(*outer);
    CHECK(cand.has_value());
    CHECK_EQ(cand->cut_degree, 1u);  // PandQ has higher degree than P (the outer cut formula).
    CHECK_EQ(cand->path.size(), 1u);  // outer → left = inner.
    CHECK_EQ(cand->path[0], 0);

    (void)outer_left;  // unused (kept variable around to silence warnings).
}

void test_find_topmost_no_cuts() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle P_dom = parse_root(ctx, "P -> P");
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(P_dom);

    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {Pnnf.get().as_compound().left, Pnnf.get().as_compound().right};
    leaf->rule = RAx{0, 1};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Pnnf};
    root->rule = ROr{0, std::move(leaf)};

    auto cand = find_topmost_max_deg_cut(*root);
    CHECK(!cand.has_value());
}

// =========================================================================
// eliminate_cuts: cut-free input passes through.
// =========================================================================
void test_eliminate_cut_free_passes_through() {
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

    auto out = eliminate_cuts(builder, *deriv.value());
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts cut-free: "
                  << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
}

// =========================================================================
// eliminate_cuts: input with cuts, Step 3 stubs return not_implemented.
// Driver gives up; output equals input (modulo deep-clone).
// =========================================================================
void test_eliminate_with_cuts_returns_unchanged_in_step3() {
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

    // Convert to multiplicative form first (eliminate_cuts's precondition).
    auto mult = additive_to_multiplicative(*deriv.value());
    assert(mult.ok());
    size_t cuts_before = count_cuts(*mult.value());
    CHECK(cuts_before > 0);

    // With all §5 cases stubbed, eliminate_cuts gives up on the first cut.
    auto out = eliminate_cuts(builder, *mult.value());
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts on mult: "
                  << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == cuts_before);  // no reduction yet.
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == mult.value()->conclusion);
}

}  // namespace

int main() {
    test_degree();
    test_find_topmost_single_cut();
    test_find_topmost_picks_max_degree();
    test_find_topmost_no_cuts();
    test_eliminate_cut_free_passes_through();
    test_eliminate_with_cuts_returns_unchanged_in_step3();

    std::cout << "reduce_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
