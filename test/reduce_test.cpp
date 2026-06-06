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

// =========================================================================
// Step 4 — B1 axiom non-principal: cut against an RAx where neither
// axiom literal is the cut formula. The OTHER premise is discarded;
// reduction is RAx on the multiplicative conclusion (with shifted
// positions when the axiom is on the right).
// =========================================================================
void test_b1_ax_nonprincipal_on_left() {
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
    FormulaHandle P    = Pnnf.get().as_compound().right;  // positive atom P
    FormulaHandle notP = Pnnf.get().as_compound().left;   // ¬P
    FormulaHandle Q    = Qnnf.get().as_compound().right;
    FormulaHandle R    = Rnnf.get().as_compound().right;

    // Hand-build a multiplicative RCut:
    //   Γ_L = [P, ¬P, Q]            (axiom positions 0, 1; structural shape only)
    //   cut formula = R             at left.concl[3]
    //   Γ_R = [Q]
    //   right.concl  = [Q, marker]  (marker = stand-in for ¬R; validate doesn't check duality)
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {P, notP, Q, R};
    lefty->rule = RAx{0, 1};  // non-principal (cut slot is at 3)
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {Q, P};
    righty->rule = RAx{0, 1};  // shape only
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {P, notP, Q, Q};  // Γ_L ++ Γ_R: |node| = 3+1 = 4 = gl+gr
    cut->rule = RCut{R, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;  // share registry
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({P, notP, Q, Q}));

    auto* ax = std::get_if<RAx>(&out.value()->rule);
    if (!ax) { std::cerr << "FAIL: reduced root is not RAx\n"; ++g_failed; return; }
    CHECK_EQ(ax->a, 0u);
    CHECK_EQ(ax->b, 1u);
}

void test_b1_ax_nonprincipal_on_right() {
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
    FormulaHandle P    = Pnnf.get().as_compound().right;
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle Q    = Qnnf.get().as_compound().right;
    FormulaHandle R    = Rnnf.get().as_compound().right;

    // Mult-Cut:
    //   Γ_L = [Q]; cut formula = R    at left.concl[1]
    //   left.concl = [Q, R]
    //   Γ_R = [P, ¬P, Q]              (axiom at 0, 1; cut slot at 3)
    //   right.concl = [P, ¬P, Q, marker]
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {Q, R};
    lefty->rule = RAx{0, 1};  // shape only
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {P, notP, Q, R};  // marker = R (validate doesn't check duality)
    righty->rule = RAx{0, 1};  // non-principal (cut slot at 3)
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {Q, P, notP, Q};  // Γ_L ++ Γ_R
    cut->rule = RCut{R, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({Q, P, notP, Q}));

    auto* ax = std::get_if<RAx>(&out.value()->rule);
    if (!ax) { std::cerr << "FAIL: reduced root is not RAx\n"; ++g_failed; return; }
    // Right's positions 0, 1 shift by |Γ_L| = 1 → expected {1, 2}.
    CHECK_EQ(ax->a, 1u);
    CHECK_EQ(ax->b, 2u);
}

// =========================================================================
// Step 4 — B1 axiom PRINCIPAL: the cut formula IS one of the axiom literals,
// so the axiom side closes on φ and its dual φ̄ ∈ its Γ. The cut is redundant:
// graft the OTHER premise after dropping the axiom side down to the shared
// dual (drop-weakening) and reordering. Exercises drops + rotation.
// =========================================================================
void test_b1_ax_principal_on_left() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(parse_root(ctx, "P -> P"));
    FormulaHandle P    = Pnnf.get().as_compound().right;   // P
    FormulaHandle notP = Pnnf.get().as_compound().left;    // ¬P
    FormulaHandle A    = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().right;
    FormulaHandle B    = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;

    // Mult-Cut on P: Γ_L = [¬P, A], Γ_R = [P, B], node = [¬P, A, P, B].
    //   left.concl  = [¬P, A, P]   RAx{0,2}  (¬P dual to P=cut slot 2; principal)
    //   right.concl = [P, B, ¬P]   RAx{0,2}  (the discarded-from-left side)
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {notP, A, P};
    lefty->rule = RAx{0, 2};                 // principal: cut slot 2 is a literal
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {P, B, notP};
    righty->rule = RAx{0, 2};
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {notP, A, P, B};       // Γ_L ++ Γ_R
    cut->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({notP, A, P, B}));
    CHECK(std::holds_alternative<RWeaken>(out.value()->rule));  // dropped the spare A
}

void test_b1_ax_principal_on_right() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    FormulaHandle Pnnf = b.to_nnf(parse_root(ctx, "P -> P"));
    FormulaHandle P    = Pnnf.get().as_compound().right;
    FormulaHandle notP = Pnnf.get().as_compound().left;
    FormulaHandle Q    = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle B    = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;

    // Mult-Cut on P: Γ_L = [Q], Γ_R = [P, B], node = [Q, P, B].
    //   left  = a NON-axiom (RLemma) so dispatch falls through to RIGHT.
    //   left.concl  = [Q, P]   (Γ_L ++ {P}).
    //   right.concl = [P, B, ¬P]   RAx{0,2}  (¬P=cut slot 2 dual to P at 0; principal)
    SentenceHandle sh = ctx.find_known("dummy").value();
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {Q, P};
    lefty->rule = RLemma{AxiomRef{sh}, "dummy"};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {P, B, notP};
    righty->rule = RAx{0, 2};                // principal on the right
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {Q, P, B};             // Γ_L ++ Γ_R
    cut->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({Q, P, B}));
    CHECK(std::holds_alternative<RWeaken>(out.value()->rule));  // dropped the spare B
}

// =========================================================================
// Step 4 — B2 ∧/∨ principal (§5.3). A cut on β∧γ where one premise ends in
// (∧) and the other in (∨) splits into two lower-degree cuts on β then γ.
// With β,γ atomic the residual cuts are axiom-principal, so the whole thing
// drives to Cut == 0 (B2 then B1). Both orientations tested.
// =========================================================================
namespace {
struct B2Atoms {
    FormulaHandle P, nP, Q, nQ, PandQ, dual;  // dual = ¬P ∨ ¬Q
};
B2Atoms b2_atoms(GlobalContext& ctx, FormulaBuilder& b) {
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle Q  = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle PandQ = b.to_nnf(b.make_and(P, Q));
    FormulaHandle dual  = b.to_nnf(b.make_not(PandQ));   // ¬P ∨ ¬Q
    FormulaHandle nP = dual.get().as_compound().left;
    FormulaHandle nQ = dual.get().as_compound().right;
    return {P, nP, Q, nQ, PandQ, dual};
}
}  // namespace

void test_b2_and_on_left() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    auto a = b2_atoms(ctx, b);

    // left = RAnd ⊢ [¬P, ¬Q, P∧Q]; right = ROr ⊢ [P, Q, ¬P∨¬Q].
    auto Lb = std::make_unique<Deriv>();
    Lb->conclusion = {a.nP, a.P}; Lb->rule = RAx{0, 1};
    auto Lg = std::make_unique<Deriv>();
    Lg->conclusion = {a.nQ, a.Q}; Lg->rule = RAx{0, 1};
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {a.nP, a.nQ, a.PandQ};
    lefty->rule = RAnd{2, {0}, std::move(Lb), std::move(Lg)};

    auto Oc = std::make_unique<Deriv>();
    Oc->conclusion = {a.P, a.Q, a.nP, a.nQ}; Oc->rule = RAx{0, 2};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {a.P, a.Q, a.dual};
    righty->rule = ROr{2, std::move(Oc)};

    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {a.nP, a.nQ, a.P, a.Q};
    cut->rule = RCut{a.PandQ, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.nP, a.nQ, a.P, a.Q}));
}

void test_b2_or_on_left() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    auto a = b2_atoms(ctx, b);

    // φ = ¬P∨¬Q: left = ROr ⊢ [P, Q, ¬P∨¬Q]; right = RAnd ⊢ [¬P, ¬Q, P∧Q].
    auto Oc = std::make_unique<Deriv>();
    Oc->conclusion = {a.P, a.Q, a.nP, a.nQ}; Oc->rule = RAx{0, 2};
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {a.P, a.Q, a.dual};
    lefty->rule = ROr{2, std::move(Oc)};

    auto Lb = std::make_unique<Deriv>();
    Lb->conclusion = {a.nP, a.P}; Lb->rule = RAx{0, 1};
    auto Lg = std::make_unique<Deriv>();
    Lg->conclusion = {a.nQ, a.Q}; Lg->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {a.nP, a.nQ, a.PandQ};
    righty->rule = RAnd{2, {0}, std::move(Lb), std::move(Lg)};

    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {a.P, a.Q, a.nP, a.nQ};
    cut->rule = RCut{a.dual, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.P, a.Q, a.nP, a.nQ}));
}

// =========================================================================
// Step 4 — B3 ∀/∃ principal (§5.3 + §6). A cut on ∀x.P(x) (left ends in ∀
// with eigenvar a; right ends in ∃ with witness t) substitutes a:=t through
// the ∀ subderivation and cuts on the lower-degree P(t). With the leaves as
// (shape-only) axioms the residual P(t) cut is axiom-principal → Cut == 0.
// =========================================================================
void test_b3_forall_on_left() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    FormulaHandle faF = b.to_nnf(parse_root(ctx, "forall x. P(x)"));   // ∀x.P(x)
    FormulaHandle exF = b.to_nnf(b.make_not(faF));                     // ∃x.¬P(x)
    FormulaHandle Pa    = b.instantiate_quantifier_body(faF.get().as_quantified().body, Term::fixed(5));  // P(a)
    FormulaHandle Pt    = b.instantiate_quantifier_body(faF.get().as_quantified().body, Term::fixed(7));  // P(t)
    FormulaHandle notPt = b.instantiate_quantifier_body(exF.get().as_quantified().body, Term::fixed(7));  // ¬P(t)

    // Γ_fa = [¬P(t)], Γ_ex = [P(t)] — chosen so that after a:=t the ∀-child's
    // RAx becomes a REAL axiom (¬P(t) dual to P(t)), letting the residual
    // P(t) cut close via B1. a=5 ∉ FV(Γ_fa)={7} (eigenvar condition).
    auto Lc = std::make_unique<Deriv>();
    Lc->conclusion = {notPt, Pa}; Lc->rule = RAx{0, 1};   // real after a:=t
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {notPt, faF};
    lefty->rule = RForall{1, 5, std::move(Lc)};
    auto Rc = std::make_unique<Deriv>();
    Rc->conclusion = {Pt, notPt}; Rc->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {Pt, exF};
    righty->rule = RExists{1, Term::fixed(7), std::move(Rc)};

    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {notPt, Pt};
    cut->rule = RCut{faF, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({notPt, Pt}));
}

// =========================================================================
// Step 4 — B4 permutation (§5.4). The cut formula is a SIDE formula of the
// left premise's ROr (the ∨ is non-principal). The cut permutes ABOVE the
// ROr: the result is ROr-at-root with the (same-degree) cut moved into its
// premise. Leaves are RLemma so the permutation is the only transformation;
// we check the tree stays valid, the conclusion is preserved, and the cut
// count is unchanged (permutation, not elimination).
// =========================================================================
void test_b4_permute_or_left() {
    Runtime rt;
    rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    SentenceHandle sh = ctx.find_known("dummy").value();

    FormulaHandle A    = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().right;
    FormulaHandle notA = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().left;
    FormulaHandle B    = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;
    FormulaHandle notB = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().left;
    FormulaHandle P    = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle notP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle AorB = b.to_nnf(b.make_or(A, B));

    // left = ROr{0, Lc} ⊢ [A∨B, P]; Lc = [A, P, B] (RLemma). cut slot = 1.
    auto Lc = std::make_unique<Deriv>();
    Lc->conclusion = {A, P, B}; Lc->rule = RLemma{AxiomRef{sh}, "dummy"};
    auto lefty = std::make_unique<Deriv>();
    lefty->conclusion = {AorB, P};
    lefty->rule = ROr{0, std::move(Lc)};
    auto righty = std::make_unique<Deriv>();
    righty->conclusion = {notA, notB, notP};
    righty->rule = RLemma{AxiomRef{sh}, "dummy"};

    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {AorB, notA, notB};       // Γ_L ++ Γ_R
    cut->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));

    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({AorB, notA, notB}));
    CHECK(count_cuts(*out.value()) == 1);                       // permuted, not eliminated
    CHECK(std::holds_alternative<ROr>(out.value()->rule));     // ROr now at the root
}

// B4 left-side unary rules that leave φ at the premise's last position
// (RExchange/RWeaken/RExists/RForall): a real axiom under the rule means that
// after the cut permutes above it, B1 closes → Cut == 0.
namespace {
struct B4Atoms { FormulaHandle P, nP, A, B; };
B4Atoms b4_atoms(GlobalContext& ctx, FormulaBuilder& b) {
    return {b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right,
            b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left,
            b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().right,
            b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right};
}
RLemma lemma(GlobalContext& ctx) { return RLemma{AxiomRef{ctx.find_known("dummy").value()}, "dummy"}; }
}  // namespace

void test_b4_exchange_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left = RExchange{0,1} ⊢ [¬P, A, P]; child [A, ¬P, P] (RAx{1,2}).
    auto Lc = std::make_unique<Deriv>(); Lc->conclusion = {a.A, a.nP, a.P}; Lc->rule = RAx{1, 2};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.nP, a.A, a.P};
    lefty->rule = RExchange{0, 1, std::move(Lc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.nP, a.A, a.B};
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.nP, a.A, a.B}));
}

void test_b4_weaken_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left = RWeaken{0} ⊢ [A, ¬P, P]; child [¬P, P] (RAx{0,1}).
    auto Lc = std::make_unique<Deriv>(); Lc->conclusion = {a.nP, a.P}; Lc->rule = RAx{0, 1};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.A, a.nP, a.P};
    lefty->rule = RWeaken{0, std::move(Lc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.A, a.nP, a.B};
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.A, a.nP, a.B}));
}

void test_b4_exists_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    FormulaHandle exQ = b.to_nnf(parse_root(ctx, "exists x. Q(x)"));
    FormulaHandle Qw  = b.instantiate_quantifier_body(exQ.get().as_quantified().body, Term::fixed(9));
    // left = RExists{0,fixed(9)} ⊢ [∃x.Q(x), ¬P, P]; child [Q(w), ¬P, P] (RAx{1,2}).
    auto Lc = std::make_unique<Deriv>(); Lc->conclusion = {Qw, a.nP, a.P}; Lc->rule = RAx{1, 2};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {exQ, a.nP, a.P};
    lefty->rule = RExists{0, Term::fixed(9), std::move(Lc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {exQ, a.nP, a.B};
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({exQ, a.nP, a.B}));
}

void test_b4_forall_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    FormulaHandle faQ = b.to_nnf(parse_root(ctx, "forall x. Q(x)"));
    FormulaHandle Qe  = b.instantiate_quantifier_body(faQ.get().as_quantified().body, Term::fixed(5));
    // left = RForall{0,eigen 5} ⊢ [∀x.Q(x), ¬P, P]; child [Q(e), ¬P, P] (RAx{1,2}).
    auto Lc = std::make_unique<Deriv>(); Lc->conclusion = {Qe, a.nP, a.P}; Lc->rule = RAx{1, 2};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {faQ, a.nP, a.P};
    lefty->rule = RForall{0, 5, std::move(Lc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {faQ, a.nP, a.B};
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({faQ, a.nP, a.B}));
}

// Right-side permutation (base = |Γ_L| offset): the RWeaken is on the RIGHT
// premise; left is an opaque RLemma so dispatch reaches the right side.
void test_b4_weaken_right() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    FormulaHandle C = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    // left = RLemma ⊢ [C, P]; right = RWeaken{0} ⊢ [A, P, ¬P], child [P, ¬P] (RAx{0,1}).
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {C, a.P}; lefty->rule = lemma(ctx);
    auto Rc = std::make_unique<Deriv>(); Rc->conclusion = {a.P, a.nP}; Rc->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.A, a.P, a.nP};
    righty->rule = RWeaken{0, std::move(Rc)};
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {C, a.A, a.P};   // Γ_L=[C] ++ Γ_R=[A,P]
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({C, a.A, a.P}));
}

// Appending-rule chain: ROr over a REAL axiom. B4 permutes the cut above the
// ROr (inserting a φ-to-last exchange); B1 then sees through that exchange to
// the axiom and closes → Cut == 0.
void test_b4_or_chain_to_zero() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle B  = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;
    FormulaHandle C  = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    FormulaHandle nPorB = b.to_nnf(b.make_or(nP, B));
    // left = ROr{0} ⊢ [¬P∨B, P]; child [¬P, P, B] (RAx{0,1}, real duals ¬P/P).
    auto Rc = std::make_unique<Deriv>(); Rc->conclusion = {nP, P, B}; Rc->rule = RAx{0, 1};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {nPorB, P};
    lefty->rule = ROr{0, std::move(Rc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {C, nP};
    righty->rule = RLemma{AxiomRef{ctx.find_known("dummy").value()}, "dummy"};
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {nPorB, C};
    cut->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({nPorB, C}));
    CHECK(std::holds_alternative<ROr>(out.value()->rule));   // ROr permuted to root
}

// B4 binary RAnd: the cut formula sits in one ∧-sub-premise. The cut routes
// into that premise (a real axiom), the other ∧-premise is untouched, and ∧
// is re-applied below. effective_axiom then closes → Cut == 0.
void test_b4_and_to_zero() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle B  = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;
    FormulaHandle C  = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    FormulaHandle nPandB = b.to_nnf(b.make_and(nP, B));
    RLemma lem{AxiomRef{ctx.find_known("dummy").value()}, "dummy"};
    // left = RAnd{ap=0, lp={1}} ⊢ [(¬P)∧B, P]; Lchild [P, ¬P] (RAx{0,1}); Rchild [B].
    auto Lchild = std::make_unique<Deriv>(); Lchild->conclusion = {P, nP}; Lchild->rule = RAx{0, 1};
    auto Rchild = std::make_unique<Deriv>(); Rchild->conclusion = {B}; Rchild->rule = lem;
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {nPandB, P};
    lefty->rule = RAnd{0, {1}, std::move(Lchild), std::move(Rchild)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {C, nP}; righty->rule = lem;
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {nPandB, C};
    cut->rule = RCut{P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({nPandB, C}));
    CHECK(std::holds_alternative<RAnd>(out.value()->rule));   // ∧ permuted to root
}

// B4 DEEP chain: an appending rule (ROr) over a NON-axiom rule (another ROr)
// over the axiom. The cut must permute past BOTH ROr's — seeing through the
// φ-to-last exchange the first permutation inserts — before B1 closes at the
// bottom axiom. P rides as non-principal context all the way down.
void test_b4_or_over_or_to_zero() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle Q  = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle nQ = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().left;
    FormulaHandle R  = b.to_nnf(parse_root(ctx, "R -> R")).get().as_compound().right;
    FormulaHandle C  = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    FormulaHandle DQ = b.to_nnf(b.make_or(nQ, Q));   // ¬Q ∨ Q
    FormulaHandle DD = b.to_nnf(b.make_or(DQ, R));    // (¬Q∨Q) ∨ R
    // bottom axiom [¬Q, P, R, Q] RAx{0,3}; inner ROr{0}⊢[DQ,P,R]; outer ROr{0}⊢[DD,P].
    auto bottom = std::make_unique<Deriv>(); bottom->conclusion = {nQ, P, R, Q}; bottom->rule = RAx{0, 3};
    auto inner = std::make_unique<Deriv>(); inner->conclusion = {DQ, P, R};
    inner->rule = ROr{0, std::move(bottom)};
    auto outer = std::make_unique<Deriv>(); outer->conclusion = {DD, P};
    outer->rule = ROr{0, std::move(inner)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {C, b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left};
    righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {DD, C};
    cut->rule = RCut{P, std::move(outer), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({DD, C}));
}

// B4 DEEP chain: ROr over RForall over axiom. Exercises the eigenvariable
// rectification path under the see-through-exchange permutation.
void test_b4_or_over_forall_to_zero() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle R  = b.to_nnf(parse_root(ctx, "R -> R")).get().as_compound().right;
    FormulaHandle C  = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    FormulaHandle faQ = b.to_nnf(parse_root(ctx, "forall y. Q(y)"));
    FormulaHandle Qe  = b.instantiate_quantifier_body(faQ.get().as_quantified().body, Term::fixed(7));
    FormulaHandle DD = b.to_nnf(b.make_or(faQ, R));   // (∀y.Q(y)) ∨ R
    // bottom axiom [Q(e), ¬P, P, R] RAx{1,2}; forall ⊢[∀y.Q,¬P,P,R] eigen 7;
    // outer ROr{0} ⊢ [DD, ¬P, P] — wait, keep P at cut slot. Build bottom→forall→ROr.
    auto bottom = std::make_unique<Deriv>(); bottom->conclusion = {Qe, nP, P, R}; bottom->rule = RAx{1, 2};
    auto fa = std::make_unique<Deriv>(); fa->conclusion = {faQ, nP, P, R};
    fa->rule = RForall{0, 7, std::move(bottom)};
    auto outer = std::make_unique<Deriv>(); outer->conclusion = {DD, nP, P};
    outer->rule = ROr{0, std::move(fa)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {C, nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {DD, nP, C};   // Γ_L=[DD,¬P] ++ Γ_R=[C]
    cut->rule = RCut{P, std::move(outer), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({DD, nP, C}));
}

// B4 DEEP chain through a BINARY rule: the cut routes into an ∧-branch that
// itself ends in a non-axiom rule (ROr). After try_b4_and the cut permutes
// into the branch, then must see through the φ-to-last exchange to the branch's
// ROr and continue down to the axiom. Exercises try_b4_and + peel together.
void test_b4_and_over_or_to_zero() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle Z  = b.to_nnf(parse_root(ctx, "Z -> Z")).get().as_compound().right;
    FormulaHandle nZ = b.to_nnf(parse_root(ctx, "Z -> Z")).get().as_compound().left;
    FormulaHandle Y  = b.to_nnf(parse_root(ctx, "Y -> Y")).get().as_compound().right;
    FormulaHandle nY = b.to_nnf(parse_root(ctx, "Y -> Y")).get().as_compound().left;
    FormulaHandle U  = b.to_nnf(parse_root(ctx, "U -> U")).get().as_compound().right;
    FormulaHandle V  = b.to_nnf(parse_root(ctx, "V -> V")).get().as_compound().right;
    FormulaHandle C  = b.to_nnf(parse_root(ctx, "C -> C")).get().as_compound().right;
    FormulaHandle DR = b.to_nnf(b.make_or(nZ, Z));     // ¬Z ∨ Z
    FormulaHandle AC = b.to_nnf(b.make_and(U, V));     // U ∧ V
    // left ∧-branch `into` = ROr{0} ⊢ [DR, P, U]; child [¬Z, P, U, Z] RAx{0,3}.
    auto orChild = std::make_unique<Deriv>(); orChild->conclusion = {nZ, P, U, Z}; orChild->rule = RAx{0, 3};
    auto into = std::make_unique<Deriv>(); into->conclusion = {DR, P, U};
    into->rule = ROr{0, std::move(orChild)};
    // right ∧-branch ⊢ [¬Y, Y, V] RAx{0,1}.
    auto andR = std::make_unique<Deriv>(); andR->conclusion = {nY, Y, V}; andR->rule = RAx{0, 1};
    // andNode ⊢ [DR, ¬Y, Y, AC, P]: principal=3 (AC), left_partition={0,4} (DR,P).
    auto andNode = std::make_unique<Deriv>(); andNode->conclusion = {DR, nY, Y, AC, P};
    andNode->rule = RAnd{3, {0, 4}, std::move(into), std::move(andR)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {C, nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {DR, nY, Y, AC, C};  // Γ_L ++ Γ_R=[C]
    cut->rule = RCut{P, std::move(andNode), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({DR, nY, Y, AC, C}));
}

// =========================================================================
// Step 4 — B5 structural (§5.5).
// =========================================================================

// B5-W dead cut, left premise: the cut formula P was WEAKENED into the left
// premise (RWeaken at the cut slot). The cut is dead — discard the right
// premise and weaken Γ_R into the W-premise's child. Cut → 0.
void test_b5_weaken_dead_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left = RWeaken{1} ⊢ [A, P]; child [A] (opaque RLemma). P at cut slot 1.
    auto Lc = std::make_unique<Deriv>(); Lc->conclusion = {a.A}; Lc->rule = lemma(ctx);
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.A, a.P};
    lefty->rule = RWeaken{1, std::move(Lc)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP};
    righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.A, a.B};  // Γ_L=[A] ++ Γ_R=[B]
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.A, a.B}));
    CHECK(std::holds_alternative<RWeaken>(out.value()->rule));   // weakened Γ_R back in
}

// B5-W dead cut, right premise (base offset). The cut formula ¬P was weakened
// into the right premise; discard the left and weaken Γ_L into the child.
void test_b5_weaken_dead_right() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left opaque ⊢ [A, P]; right = RWeaken{1} ⊢ [B, ¬P], child [B]. ¬P at cut slot 1.
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.A, a.P}; lefty->rule = lemma(ctx);
    auto Rc = std::make_unique<Deriv>(); Rc->conclusion = {a.B}; Rc->rule = lemma(ctx);
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP};
    righty->rule = RWeaken{1, std::move(Rc)};
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.A, a.B};
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.A, a.B}));
    CHECK(std::holds_alternative<RWeaken>(out.value()->rule));
}

// B5-C contraction on the RIGHT premise: ¬P was produced by a contraction
// (RDuplicate{src=cut slot}). The reduction duplicates the left premise and
// cuts twice against the contraction premise [P, ¬P, ¬P]; the residual cuts
// are axiom-(non)principal, so the whole thing drives to Cut == 0.
void test_b5_contraction_right() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left = O opaque ⊢ [A, P] (Γ_L=[A]). right = RDuplicate{1} ⊢ [P, ¬P];
    //   child C2 = [P, ¬P, ¬P] RAx{0,1} (Γ_R=[P], two ¬P contracted).
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.A, a.P}; lefty->rule = lemma(ctx);
    auto C2 = std::make_unique<Deriv>(); C2->conclusion = {a.P, a.nP, a.nP}; C2->rule = RAx{0, 1};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.P, a.nP};
    righty->rule = RDuplicate{1, std::move(C2)};
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.A, a.P};  // Γ_L=[A] ++ Γ_R=[P]
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.A, a.P}));
}

// B5-C contraction on the LEFT premise: P was produced by a contraction.
// Symmetric to the right case but the residual cut formula ends up mid-
// sequence, exercising the rotate-to-back path. Drives to Cut == 0.
void test_b5_contraction_left() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    auto a = b4_atoms(ctx, b);
    // left = RDuplicate{1} ⊢ [¬P, P]; child C2 = [¬P, P, P] RAx{0,1} (Γ_L=[¬P]).
    // right = O opaque ⊢ [B, ¬P] (Γ_R=[B]).
    auto C2 = std::make_unique<Deriv>(); C2->conclusion = {a.nP, a.P, a.P}; C2->rule = RAx{0, 1};
    auto lefty = std::make_unique<Deriv>(); lefty->conclusion = {a.nP, a.P};
    lefty->rule = RDuplicate{1, std::move(C2)};
    auto righty = std::make_unique<Deriv>(); righty->conclusion = {a.B, a.nP}; righty->rule = lemma(ctx);
    auto cut = std::make_unique<Deriv>(); cut->conclusion = {a.nP, a.B};  // Γ_L=[¬P] ++ Γ_R=[B]
    cut->rule = RCut{a.P, std::move(lefty), std::move(righty)};
    CHECK_OK(validate(*cut));
    FormulaBuilder builder = b;
    auto out = eliminate_cuts(builder, *cut);
    if (!out.ok()) { std::cerr << "FAIL: " << out.error().to_string() << "\n"; ++g_failed; return; }
    CHECK(count_cuts(*out.value()) == 0);
    CHECK_OK(validate(*out.value()));
    CHECK(out.value()->conclusion == std::vector<FormulaHandle>({a.nP, a.B}));
}

}  // namespace

int main() {
    test_degree();
    test_find_topmost_single_cut();
    test_find_topmost_picks_max_degree();
    test_find_topmost_no_cuts();
    test_eliminate_cut_free_passes_through();
    test_eliminate_with_cuts_returns_unchanged_in_step3();
    test_b1_ax_nonprincipal_on_left();
    test_b1_ax_nonprincipal_on_right();
    test_b1_ax_principal_on_left();
    test_b1_ax_principal_on_right();
    test_b2_and_on_left();
    test_b2_or_on_left();
    test_b3_forall_on_left();
    test_b4_permute_or_left();
    test_b4_exchange_left();
    test_b4_weaken_left();
    test_b4_exists_left();
    test_b4_forall_left();
    test_b4_weaken_right();
    test_b4_or_chain_to_zero();
    test_b4_and_to_zero();
    test_b4_or_over_or_to_zero();
    test_b4_or_over_forall_to_zero();
    test_b4_and_over_or_to_zero();
    test_b5_weaken_dead_left();
    test_b5_weaken_dead_right();
    test_b5_contraction_right();
    test_b5_contraction_left();

    std::cout << "reduce_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
