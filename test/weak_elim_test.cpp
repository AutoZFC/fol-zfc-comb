// weak_elim_test — Stage 4 Weakening-elimination engine.
//
// Spec: src/proof/translate/lkr_weak_elim/WEAKENING_ELIM_DESIGN.md
//
// Each test follows the round-trip discipline: construct a Deriv with
// RWeaken nodes, eliminate_weakenings, emit to flat LKR, re-verify
// under LKRVerifier against the same goal. The re-verify gate is the
// soundness net — a bad reduction produces a RED test, never an
// unsound proof.
//
// Phase coverage:
//   - W1.1 (smoke):   W-free Deriv passes through unchanged.
//   - W1.2 (§4.1):    RWeaken above RAx (non-principal) — absorb.
//   - W1.3 (§4.1):    RWeaken above ROne (idx < |Γ|)    — absorb.
//   - W1.4 (§4.1):    RWeaken above RLemma (NNF ≠ φ)    — absorb.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_weak_elim/reduce.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <type_traits>
#include <variant>

using namespace logic;
using namespace logic::proof;
using namespace logic::proof::translate::lkr_cut_elim;
namespace we = logic::proof::translate::lkr_weak_elim;

namespace {

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

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
                  << _r.error().to_string() \
                  << " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

// Count RWeaken nodes in a Deriv tree.
size_t count_weakenings(const Deriv& d) {
    size_t n = 0;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RWeaken>) {
            n = 1 + count_weakenings(*r.child);
        } else if constexpr (std::is_same_v<T, RCut> ||
                             std::is_same_v<T, RAnd>) {
            n = count_weakenings(*r.left) + count_weakenings(*r.right);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            n = count_weakenings(*r.child);
        }
    }, d.rule);
    return n;
}

util::ResultStatus emit_and_verify(GlobalContext& ctx, FormulaHandle goal,
                                    const Deriv& root) {
    auto p = emit(root);
    if (!p.ok()) return p.error();
    Proof pf{System::LKR, std::move(p).unwrap()};
    lkr::LKRVerifier v;
    return v.verify(ctx, goal, pf);
}

// =========================================================================
// W1.1 — Smoke: W-free Deriv passes through eliminate_weakenings unchanged.
//
// Goal: P → P (NNF: ¬P ∨ P). Derivation: Or(0) → AxiomLit(0, 1).
// =========================================================================
void test_smoke_weakening_free() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P};
    leaf->rule = RAx{0, 1};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(leaf)};

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_weakenings: "
                  << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W1.2 — §4.1 W above RAx (non-principal).
//
// Construct: a W'd entry φ atop a leaf RAx{a, b} where a, b both
// reference positions in Γ (not the W'd slot). The W is absorbed by
// dropping it — the RAx is sound on the smaller Γ directly.
//
// Concretely: sequent ⊢ ¬P, P. RAx{0, 1} closes it. Weaken in φ = Q,
// producing ⊢ ¬P, P, Q with the W at the outer node (conclusion =
// ⊢ ¬P, P). W1.2 should yield just the RAx{0, 1} leaf with conclusion
// ⊢ ¬P, P.
// =========================================================================
void test_W_absorb_at_ax_nonprincipal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal_pp = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal_pp);  // ¬P ∨ P
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    // Fresh atom Q for the W'd formula.
    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;

    // Leaf: RAx{0, 1} on sequent [¬P, P, Q]. Both literal slots < 2,
    // so they're non-principal in the W'd Q at slot 2.
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P, Q};
    leaf->rule = RAx{0, 1};

    // W'd node: conclusion = [¬P, P] (smaller); child = [¬P, P, Q] (bigger).
    auto wn = std::make_unique<Deriv>();
    wn->conclusion = {notP, P};
    wn->rule = RWeaken{Q, std::move(leaf)};

    // Outer Or(0) on the W'd node: makes [¬P ∨ P] (the goal).
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(wn)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_weakenings: "
                  << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal_pp, *reduced.value()));
}

// =========================================================================
// W1.3 — §4.1 W above ROne (idx < |Γ|).
//
// Sequent ⊢ ¬⊥. Close via ROne{0}. Weaken in φ = Q at slot 1.
// The W'd node has conclusion ⊢ ¬⊥; child has ⊢ ¬⊥, Q. Absorb yields
// just ROne{0} on ⊢ ¬⊥.
// =========================================================================
void test_W_absorb_at_one() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder builder(ctx);
    // ¬⊥ as goal: parse "~false" then NNF.
    FormulaHandle goal = parse_root(ctx, "~false");
    FormulaHandle goal_nnf = builder.to_nnf(goal);

    // Fresh atom Q for the W'd formula.
    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;

    // Leaf: ROne{0} on sequent [¬⊥, Q].
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {goal_nnf, Q};
    leaf->rule = ROne{0};

    // W'd node: conclusion = [¬⊥]; child = [¬⊥, Q].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = RWeaken{Q, std::move(leaf)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_weakenings: "
                  << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W2.6 — §4.2.6 W stacked over W, bottom child is a leaf.
//
// Driver post-order already handles this for free: the inner W absorbs
// at the leaf first (W1), then the outer W's child becomes a leaf and
// absorbs too.
//
// Build: RWeaken{φ_outer, RWeaken{φ_inner, RAx{0,1}}}
// Reduce: both W's gone, RAx{0,1} on the outer conclusion.
// =========================================================================
void test_W_over_W_stacked() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    FormulaHandle Q  = builder.to_nnf(parse_root(ctx, "Q -> Q"))
                              .get().as_compound().right;
    FormulaHandle R  = builder.to_nnf(parse_root(ctx, "R -> R"))
                              .get().as_compound().right;

    // RAx{0,1} on [¬P, P, Q, R]: positions 0,1 non-principal in Q@2 and R@3.
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P, Q, R};
    leaf->rule = RAx{0, 1};

    // Inner W (R) over leaf: conclusion = [¬P, P, Q], child = [¬P, P, Q, R].
    auto w_inner = std::make_unique<Deriv>();
    w_inner->conclusion = {notP, P, Q};
    w_inner->rule = RWeaken{R, std::move(leaf)};

    // Outer W (Q) over inner: conclusion = [¬P, P], child = [¬P, P, Q].
    auto w_outer = std::make_unique<Deriv>();
    w_outer->conclusion = {notP, P};
    w_outer->rule = RWeaken{Q, std::move(w_inner)};

    // Or on outer: conclusion = [¬P∨P].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(w_outer)};

    CHECK(count_weakenings(*root) == 2);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W2.4 — §4.2.4 W above RExchange (i, j < |Γ|).
//
// Permute W past Exchange when the swap doesn't involve the W'd slot.
// Build:
//   Outer:  conclusion [¬P∨P]
//   Or(0): conclusion [¬P, P]
//   W(Q):   conclusion [¬P, P, Q] — but wait, RExchange child has to
//   make sense. Let's structure differently.
//
// Use:
//   leaf:  RAx{1, 0} on [P, ¬P, Q]   — atomic dual pair at 1,0; Q@2.
//   exch:  RExchange{0, 1, leaf} on [¬P, P, Q] → swap to [P, ¬P, Q].
//   W:     RWeaken{Q, exch} on [¬P, P] → after W: [¬P, P, Q].
//   Or:    ROr{0, W} on [¬P∨P].
//
// Reduce: permute W past Exchange, then absorb at leaf.
// =========================================================================
void test_W_over_Exchange() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;
    FormulaHandle Q    = builder.to_nnf(parse_root(ctx, "Q -> Q"))
                                .get().as_compound().right;

    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {P, notP, Q};      // post-Exchange
    leaf->rule = RAx{1, 0};

    auto exch = std::make_unique<Deriv>();
    exch->conclusion = {notP, P, Q};      // pre-Exchange
    exch->rule = RExchange{0, 1, std::move(leaf)};

    auto w = std::make_unique<Deriv>();
    w->conclusion = {notP, P};            // pre-W
    w->rule = RWeaken{Q, std::move(exch)};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(w)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W2.5 — §4.2.5 W above RContract (i, j < |Γ|).
//
// Permute W past Contraction when the merge doesn't involve the W'd slot.
//
// Goal: P | (~P | ~P). NNF: P ∨ (¬P ∨ ¬P).
// Verifier sequence:
//   1. Or(0) on [P∨(¬P∨¬P)]            → [P, ¬P∨¬P]
//   2. Or(1) on [P, ¬P∨¬P]             → [P, ¬P, ¬P]
//   3. W(Q):                            → [P, ¬P, ¬P, Q]
//   4. Contract(1, 2):                  → [P, ¬P, Q]    (erase entry 2)
//   5. Ax(0, 1):                        ✓ (P / ¬P dual)
//
// W is above Contract; Contract's i=1, j=2 are both < |Γ|=3 (the W's
// outer node has Γ = [P, ¬P, ¬P] of size 3). Non-W-involving.
// =========================================================================
void test_W_over_Contract() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder builder(ctx);

    FormulaHandle goal = parse_root(ctx, "P | (~P | ~P)");
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    // goal_nnf = P ∨ (¬P ∨ ¬P). Extract pieces.
    const auto& g_cmp = goal_nnf.get().as_compound();
    FormulaHandle P = g_cmp.left;
    FormulaHandle inner_or = g_cmp.right;   // (¬P ∨ ¬P)
    const auto& in_cmp = inner_or.get().as_compound();
    FormulaHandle nP = in_cmp.left;
    // inner_or.right is also ¬P; by interning should equal nP.
    assert(in_cmp.right == nP);

    FormulaHandle Q  = builder.to_nnf(parse_root(ctx, "Q -> Q"))
                              .get().as_compound().right;

    // Leaf: [P, ¬P, Q] (post-Contract). Ax{0, 1}: P / ¬P dual pair.
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {P, nP, Q};
    leaf->rule = RAx{0, 1};

    // Contract{1, 2} on [P, ¬P, ¬P, Q] → erase entry 2 → [P, ¬P, Q].
    auto ctr = std::make_unique<Deriv>();
    ctr->conclusion = {P, nP, nP, Q};
    ctr->rule = RContract{1, 2, std::move(leaf)};

    // W(Q) on [P, ¬P, ¬P] → [P, ¬P, ¬P, Q]. i=1,j=2 < |Γ|=3.
    auto w = std::make_unique<Deriv>();
    w->conclusion = {P, nP, nP};
    w->rule = RWeaken{Q, std::move(ctr)};

    // Or(1) on [P, ¬P∨¬P] → [P, ¬P, ¬P].
    auto or_inner = std::make_unique<Deriv>();
    or_inner->conclusion = {P, inner_or};
    or_inner->rule = ROr{1, std::move(w)};

    // Or(0) on [goal_nnf] → [P, ¬P∨¬P].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(or_inner)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W2.2 — §4.2.2 W above RForall (p < |Γ|, principal in Γ not in φ).
//
// Goal: forall x. (P(x) -> P(x)).  NNF: forall x. (¬P(x) ∨ P(x)).
//
// Direct derivation:
//   Forall(0, eigen=v0): instantiate. Sequent: [¬P(v0) ∨ P(v0)].
//   Or(0): expand. Sequent: [¬P(v0), P(v0)].
//   Ax(0,1): close.
//
// Add a W(Q) somewhere above the Forall:
//   Original:  Outer Forall on Γ then ... NO, we want W ABOVE Forall
//   in the LK sense = the W's child IS the Forall.
//   In IR: W's node.conclusion = Γ, W's child is the Forall whose
//   conclusion = Γ+φ. So we need a Forall at sequent [..., ∀x.body, φ].
//
// Concretely:
//   leaf: Ax{0,1} on [¬P(v0), P(v0), Q]
//   Or(0): conclusion [¬P(v0) ∨ P(v0), Q]
//   Forall(0, v0): conclusion [forall x. (...), Q]
//   W(Q): conclusion [forall x. (...)] (= goal_nnf)
//
// This DOESN'T have W above Forall in the spec-rewrite sense — W is the
// outermost rule here. To exercise the spec's permutation case, we need
// W somewhere INSIDE a tree above a Forall. Restructure: put the W
// INSIDE the Forall's child.
// =========================================================================
void test_W_over_Forall() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder builder(ctx);

    // Goal: forall x. P(x) -> P(x).  NNF: ∀x. (¬P(x) ∨ P(x)).
    FormulaHandle goal = parse_root(ctx, "forall x. (P(x) -> P(x))");
    FormulaHandle goal_nnf = builder.to_nnf(goal);

    // Extract substructure.
    const auto& fall = goal_nnf.get().as_quantified();
    var_index v = 100;    // any fresh fixed-var index
    FormulaHandle body_inst =
        builder.instantiate_quantifier_body(fall.body, Term::fixed(v));
    // body_inst = ¬P(v) ∨ P(v)
    FormulaHandle nPv = body_inst.get().as_compound().left;
    FormulaHandle Pv  = body_inst.get().as_compound().right;
    FormulaHandle Q   = builder.to_nnf(parse_root(ctx, "Q -> Q"))
                                .get().as_compound().right;

    // Verifier semantics: Or(p) replaces entries[p] with phi, appends psi.
    // Pre-Or: [body_inst, Q] (size 2). Or(0): [¬P(v), Q, P(v)] (size 3).
    // Q ends up at the middle, P(v) at the tail.
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {nPv, Q, Pv};
    leaf->rule = RAx{0, 2};

    // Or(0): conclusion = [body_inst, Q]; child = [nPv, Q, Pv].
    auto orn = std::make_unique<Deriv>();
    orn->conclusion = {body_inst, Q};
    orn->rule = ROr{0, std::move(leaf)};

    // Forall(p=0, v): conclusion = [forall x. body, Q]; child = [body_inst, Q].
    auto forall_n = std::make_unique<Deriv>();
    forall_n->conclusion = {goal_nnf, Q};
    forall_n->rule = RForall{0, v, std::move(orn)};

    // W(Q): conclusion = [forall x. body]; child = [forall x. body, Q].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = RWeaken{Q, std::move(forall_n)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

// =========================================================================
// W2.1 — §4.2.1 W above ROr (p < |Γ|, principal in Γ not in φ).
//
// Goal: (P → P) ∨ Q. NNF: (¬P ∨ P) ∨ Q.
//
// Structure:
//   leaf: Ax{0, 1} on [¬P, P, Q]
//   Or(0): conclusion = [¬P∨P, Q]; child = [¬P, P, Q]
//   W(Q): conclusion = [¬P∨P]; child = [¬P∨P, Q]
//
// W is over Or — but Or has already fired below the W (the Or's
// conclusion contains Q, which the W introduces). Wait — Or fires on
// the W'd sequent (post-W). The W's child IS the Or; Or's conclusion =
// W's child.conclusion = [¬P∨P, Q]. The Or's p=0 references ¬P∨P (in
// the W'd sequent, position 0). That's < |Γ| = 1 (W's outer node has
// Γ = [¬P∨P] of size 1, φ = Q at position 1). So p=0 < |Γ|. ✓
//
// After permute: Or fires on [¬P∨P] → [¬P, P]. Then W(Q) on [¬P, P]
// → [¬P, P, Q]. Note: the original child of Or was [¬P, P, Q] (= same
// as post-W in permuted). But the ORDER of the tail: original had
// [¬P, P, Q] (Q was already there pre-Or, then Or appended P → Q ended
// up at the MIDDLE: [¬P, Q, P]?). Hmm let me re-trace.
//
// Verifier semantics: Or(p) replaces entries[p] with φ, then APPENDS ψ.
// Original sequence:
//   1. W(Q): [¬P∨P] → [¬P∨P, Q].
//   2. Or(0): replace entry 0 with ¬P, append P → [¬P, Q, P].
//   ∴ original Or-child.conclusion = [¬P, Q, P], not [¬P, P, Q]!
//
// Need to rebuild the test accordingly.
// =========================================================================
void test_W_over_Or() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder builder(ctx);

    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;
    FormulaHandle Q    = builder.to_nnf(parse_root(ctx, "Q -> Q"))
                                .get().as_compound().right;

    // Or's principal entry at position 0 is goal_nnf. After Or(0):
    // [¬P, Q, P] (Q at position 1 because it was in [¬P∨P, Q] before Or).
    // Leaf: Ax{0, 2} on [¬P, Q, P].
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, Q, P};
    leaf->rule = RAx{0, 2};

    auto orn = std::make_unique<Deriv>();
    orn->conclusion = {goal_nnf, Q};
    orn->rule = ROr{0, std::move(leaf)};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = RWeaken{Q, std::move(orn)};

    CHECK(count_weakenings(*root) == 1);

    auto reduced = we::eliminate_weakenings(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_weakenings(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value()));
}

}  // namespace

int main() {
    test_smoke_weakening_free();
    test_W_absorb_at_ax_nonprincipal();
    test_W_absorb_at_one();
    test_W_over_W_stacked();
    test_W_over_Exchange();
    test_W_over_Contract();
    test_W_over_Forall();
    test_W_over_Or();
    std::cout << "weak_elim_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
