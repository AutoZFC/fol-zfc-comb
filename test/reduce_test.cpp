// reduce_test — Stage 3 cut-elimination engine.
//
// Spec: src/proof/translate/lkr_cut_elim/CUT_ELIM_DESIGN.md
//
// Each test follows the round-trip discipline: construct a Deriv with
// cuts, eliminate_cuts, emit to flat LKR, re-verify under LKRVerifier
// against the same goal. The re-verify gate is the soundness net —
// a bad reduction produces a RED test, never an unsound proof.
//
// Phase coverage:
//   - P1 (smoke): cut-free Deriv passes through unchanged.
//   - P2 (§5.5 W dead-cut, LEFT variant): Cut(φ) where LEFT = W(φ) on
//     a cut-free derivation. Engine drops both the W and the Cut.
//
// Additional cases (§5.2 axiom, §5.3 ∧/∨, ∀/∃, §5.4 permutation,
// §5.5 contraction) land in subsequent commits per math-first
// discipline.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/reduce.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <variant>

using namespace logic;
using namespace logic::proof;
using namespace logic::proof::translate::lkr_cut_elim;

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

// Count Cut nodes in a Deriv tree.
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

util::ResultStatus emit_and_verify(GlobalContext& ctx, FormulaHandle goal,
                                    const Deriv& root,
                                    const std::string& /*claim_name*/) {
    auto p = emit(root);
    if (!p.ok()) return p.error();
    Proof pf{System::LKR, std::move(p).unwrap()};
    lkr::LKRVerifier v;
    return v.verify(ctx, goal, pf);
}

// =========================================================================
// P1 — Smoke: cut-free Deriv passes through eliminate_cuts unchanged.
//
// Goal: P → P (NNF: ¬P ∨ P). Derivation: Or(0) → AxiomLit(0, 1).
// =========================================================================
void test_smoke_cut_free() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);  // = ¬P ∨ P
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    // Leaf: AxiomLit(0, 1) on sequent [¬P, P].
    auto leaf = std::make_unique<Deriv>();
    leaf->conclusion = {notP, P};
    leaf->rule = RAx{0, 1};

    // Root: Or(0) on sequent [¬P ∨ P].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(leaf)};

    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "smoke"));
}

// =========================================================================
// P2 — §5.5 W dead-cut (LEFT variant).
//
// Construct a Deriv with one cut where LEFT = Weakening(φ) on a cut-
// free sub-derivation of ⊢ Γ. eliminate_cuts should drop both the W
// and the Cut, returning the original ⊢ Γ derivation.
//
// Goal: ⊢ ¬P ∨ P. Cut formula: a SchemaVar Q (any closed formula
// not appearing in goal).
// Construction:
//   Cut(Q):
//     LEFT  = Weakening(Q) over a cut-free proof of ⊢ ¬P∨P     (= Γ, Q)
//     RIGHT = Weakening(¬Q) over a cut-free proof of ⊢ ¬P∨P    (= Γ, ¬Q)
// After dead-cut: just the LEFT's child (cut-free proof of Γ).
// =========================================================================
void test_dead_cut_W_left() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    // Extract a fresh atomic Q distinct from P. Use a separate parse.
    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");  // NNF: ¬Q ∨ Q
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;
    FormulaHandle notQ   = builder.to_nnf(builder.make_not(Q));

    // Helper: build a cut-free Or(0)+AxiomLit proof of ⊢ ¬P∨P with the
    // sequent having an extra trailing entry (for W-stacked context).
    auto build_em_proof = [&](FormulaHandle extra) -> DerivPtr {
        // Sequent before Or: [¬P∨P, extra]. Or(0) yields [¬P, extra, P].
        // AxiomLit(0, 2) closes (¬P at 0, P at 2).
        auto leaf = std::make_unique<Deriv>();
        leaf->conclusion = {notP, extra, P};
        leaf->rule = RAx{0, 2};

        auto orn = std::make_unique<Deriv>();
        orn->conclusion = {goal_nnf, extra};
        orn->rule = ROr{0, std::move(leaf)};
        return orn;
    };

    // LEFT premise of Cut: W(Q) on ⊢ ¬P∨P → ⊢ ¬P∨P, Q.
    auto inner_left = std::make_unique<Deriv>();
    inner_left->conclusion = {goal_nnf};
    {
        auto em = std::make_unique<Deriv>();
        em->conclusion = {notP, P};
        em->rule = RAx{0, 1};
        inner_left->rule = ROr{0, std::move(em)};
    }
    auto w_left = std::make_unique<Deriv>();
    w_left->conclusion = {goal_nnf, Q};
    w_left->rule = RWeaken{Q, std::move(inner_left)};

    // RIGHT premise of Cut: any proof of ⊢ ¬P∨P, ¬Q. Use W(¬Q) over EM.
    auto inner_right = build_em_proof(notQ);  // builds ⊢ ¬P∨P, ¬Q via Or+Ax.
    // But we want W(¬Q) on top of a proof of ⊢ ¬P∨P alone, not embedded.
    // Reuse the same approach as inner_left.
    auto inner_right_clean = std::make_unique<Deriv>();
    inner_right_clean->conclusion = {goal_nnf};
    {
        auto em = std::make_unique<Deriv>();
        em->conclusion = {notP, P};
        em->rule = RAx{0, 1};
        inner_right_clean->rule = ROr{0, std::move(em)};
    }
    auto w_right = std::make_unique<Deriv>();
    w_right->conclusion = {goal_nnf, notQ};
    w_right->rule = RWeaken{notQ, std::move(inner_right_clean)};
    (void)inner_right;

    // Cut(Q): LEFT ⊢ Γ,Q  RIGHT ⊢ Γ,¬Q  →  ⊢ Γ.
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = RCut{Q, std::move(w_left), std::move(w_right)};

    CHECK(count_cuts(*root) == 1);

    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);  // dead-cut removed
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "dead_cut_W"));
}

// =========================================================================
// P3 — §5.5 W dead-cut (RIGHT variant).
//
// Cut(φ) where RIGHT = W(NNF(¬φ)) on a cut-free derivation of ⊢ Γ.
// eliminate_cuts should drop both the W and the Cut, returning the
// original ⊢ Γ from RIGHT's child.
// =========================================================================
void test_dead_cut_W_right() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;
    FormulaHandle notQ   = builder.to_nnf(builder.make_not(Q));

    auto make_em_proof = [&]() -> DerivPtr {
        auto leaf = std::make_unique<Deriv>();
        leaf->conclusion = {notP, P};
        leaf->rule = RAx{0, 1};
        auto orn = std::make_unique<Deriv>();
        orn->conclusion = {goal_nnf};
        orn->rule = ROr{0, std::move(leaf)};
        return orn;
    };

    // LEFT premise of Cut: a proof of ⊢ ¬P∨P, Q. Use W(Q) over EM.
    auto inner_left = make_em_proof();
    auto w_left = std::make_unique<Deriv>();
    w_left->conclusion = {goal_nnf, Q};
    w_left->rule = RWeaken{Q, std::move(inner_left)};

    // RIGHT premise of Cut: W(¬Q) over a proof of ⊢ ¬P∨P.
    auto inner_right = make_em_proof();
    auto w_right = std::make_unique<Deriv>();
    w_right->conclusion = {goal_nnf, notQ};
    w_right->rule = RWeaken{notQ, std::move(inner_right)};

    // Cut(Q): LEFT ⊢ Γ,Q  RIGHT ⊢ Γ,¬Q  →  ⊢ Γ.
    // (Both premises are W'd, so dead-cut fires on EITHER; the LEFT
    // variant happens to fire first in our scan. To exercise the RIGHT
    // variant in isolation, make LEFT a non-W proof of ⊢ Γ, Q.)
    //
    // Better: use a NON-W LEFT. Build LEFT as a non-W proof of ⊢ ¬P∨P, Q
    // — e.g., Or(0) on ¬P∨P then AxiomLit. The 3-entry sequent [¬P, Q, P]
    // doesn't close with AxiomLit on a non-adjacent dual; Q in the middle
    // is fine. AxiomLit(0, 2) closes (¬P, P).
    auto leaf_l = std::make_unique<Deriv>();
    leaf_l->conclusion = {notP, Q, P};
    leaf_l->rule = RAx{0, 2};
    auto non_w_left = std::make_unique<Deriv>();
    non_w_left->conclusion = {goal_nnf, Q};
    non_w_left->rule = ROr{0, std::move(leaf_l)};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = RCut{Q, std::move(non_w_left), std::move(w_right)};

    CHECK(count_cuts(*root) == 1);
    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "dead_cut_W_right"));
    (void)w_left;
}

// =========================================================================
// P4 — §5.2 axiom cut, non-principal case.
//
// Γ contains a dual pair (P, ¬P). LEFT and RIGHT both close via that
// pair, with the cut formula α weakened into the Ax conclusion but not
// principal. After cut-elim: same Ax over Γ alone.
//
// Concretely:
//   Goal proves ⊢ ¬P ∨ P. Decompose with Or(0) → [¬P, P].
//   Insert a cut on a fresh atom Q in front:
//     Cut(Q): LEFT = Ax(0,1) on [¬P, P, Q]
//             RIGHT = Ax(0,1) on [¬P, P, ¬Q]
//   The Ax in both closes (¬P, P) — Q / ¬Q is irrelevant.
//   After cut-elim: Ax(0, 1) on [¬P, P]. Same proof.
// =========================================================================
void test_axiom_cut_non_principal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;
    FormulaHandle notQ   = builder.to_nnf(builder.make_not(Q));

    // LEFT: Ax(0, 1) on [¬P, P, Q]. ¬P and P are duals at 0, 1.
    auto ax_left = std::make_unique<Deriv>();
    ax_left->conclusion = {notP, P, Q};
    ax_left->rule = RAx{0, 1};

    // RIGHT: Ax(0, 1) on [¬P, P, ¬Q].
    auto ax_right = std::make_unique<Deriv>();
    ax_right->conclusion = {notP, P, notQ};
    ax_right->rule = RAx{0, 1};

    // We need to wrap these so the WHOLE program verifies. The cut sits
    // above the Or that decomposes ¬P ∨ P. Build the full Deriv:
    //   Root: Or(0) on [¬P∨P]
    //   Child: Cut(Q) on [¬P, P]
    //     LEFT  = Ax(0,1) on [¬P, P, Q]
    //     RIGHT = Ax(0,1) on [¬P, P, ¬Q]
    auto cut_node = std::make_unique<Deriv>();
    cut_node->conclusion = {notP, P};
    cut_node->rule = RCut{Q, std::move(ax_left), std::move(ax_right)};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(cut_node)};

    CHECK(count_cuts(*root) == 1);
    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "ax_cut_nonprincipal"));
}

// =========================================================================
// P5 — §5.2 axiom cut, principal case (additive form).
//
// LEFT = Ax with cut formula α principal: positions are (last, k) where
// conclusion[k] = NNF(¬α) (in Γ). After cut-elim, RIGHT gets Contracted
// on (k, last_R) to merge the duplicate dual.
//
// Goal: ⊢ ¬P ∨ P. Build a cut where:
//   Γ (shared) = [¬P, P]  (= post-Or sequent before cut adds α).
//   Cut formula α = P.
//   LEFT = Ax(1, last=2) on [¬P, P, P] — but wait, last is P (the cut
//     formula), and position 1 is also P. Two P's aren't duals.
//
// Try Cut(¬P) instead: LEFT = ⊢ ¬P, P, ¬P. Ax(0, last=2)... 0 = ¬P,
// 2 = ¬P. Same, not duals.
//
// We need α and ᾱ both present. So Cut(α): LEFT.conclusion = Γ, α =
// [Γ..., α]. For LEFT = Ax(k, last) to close, conclusion[k] = ᾱ.
// So Γ must contain ᾱ. For Γ = [¬P, P], pick α=P (so ᾱ=¬P at position 0):
//   LEFT.conclusion = [¬P, P, P]. Ax(0, 2)? conclusion[0]=¬P,
//   conclusion[2]=P. Dual! ✓ This is principal.
//   k = 0 (the dual position in Γ).
//
// RIGHT.conclusion = [¬P, P, ¬P]. Position 1 (P) and 2 (¬P) dual.
// So RIGHT = Ax(1, 2). ✓
//
// After cut-elim: Contract(k=0, last_R=2) on RIGHT[¬P, P, ¬P] → [¬P, P].
// =========================================================================
void test_axiom_cut_principal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    // LEFT: Ax(0, 2) on [¬P, P, P]. Cut formula P principal at last=2.
    auto ax_left = std::make_unique<Deriv>();
    ax_left->conclusion = {notP, P, P};
    ax_left->rule = RAx{0, 2};

    // RIGHT: Ax(1, 2) on [¬P, P, ¬P]. Cut formula's dual ¬P at last=2;
    // positions 1=P, 2=¬P are duals — but here the Ax is on (1, 2), so
    // ¬P at last is paired with P at position 1. Whether the Ax pair
    // includes `last` is the test for principal axiom on RIGHT — yes,
    // axR.b == last = 2, k = axR.a = 1.
    //
    // For the test, we want the LEFT-principal path to fire FIRST (since
    // our `try_` order checks LEFT first). The LEFT Ax (0, 2) has
    // axL.b == last = 2, k = 0. So LEFT principal fires.
    auto ax_right = std::make_unique<Deriv>();
    ax_right->conclusion = {notP, P, notP};
    ax_right->rule = RAx{1, 2};

    auto cut_node = std::make_unique<Deriv>();
    cut_node->conclusion = {notP, P};
    cut_node->rule = RCut{P, std::move(ax_left), std::move(ax_right)};

    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(cut_node)};

    CHECK(count_cuts(*root) == 1);
    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "ax_cut_principal"));
}

// =========================================================================
// P9 — mcut, axiom non-principal case (B0 expansion).
//
// Direct unit test of the `mcut` helper (not yet wired into reduce_cut
// for additive cuts — that requires the W-bridge for context doubling).
//
// Setup:
//   dl = RAx{0, 1} on [¬R, R, U]      (Ax closes (¬R, R), U is side)
//   dr = some derivation of [¬Q, Q, ¬U]
//   pl = 2 (cut formula = U), pr = 2 (dual = ¬U).
//
// Expected mcut result conclusion = (dl - 2) ++ (dr - 2) = [¬R, R] ++ [¬Q, Q]
//                                  = [¬R, R, ¬Q, Q].
// Result rule = RAx on the new positions of the (¬R, R) pair, which
// are still (0, 1) since pl=2 is past them.
//
// To verify the result, embed it in a goal and check LKRVerifier
// accepts the emitted program. Goal = ⊢ (¬R ∨ R) — but we need a goal
// whose NNF matches the mcut result's "main statement". For test
// purposes, we wrap with Or(0) on a goal whose NNF starts the same
// way; the unused entries (¬Q, Q) are weakened-in context that the
// AxiomLit ignores.
// =========================================================================
void test_mcut_ax_nonprincipal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder builder(ctx);

    FormulaHandle r_sent = parse_root(ctx, "R -> R");
    FormulaHandle r_nnf  = builder.to_nnf(r_sent);  // ¬R ∨ R
    FormulaHandle notR   = r_nnf.get().as_compound().left;
    FormulaHandle R      = r_nnf.get().as_compound().right;

    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle notQ   = q_nnf.get().as_compound().left;
    FormulaHandle Q      = q_nnf.get().as_compound().right;

    FormulaHandle u_sent = parse_root(ctx, "U -> U");
    FormulaHandle u_nnf  = builder.to_nnf(u_sent);
    FormulaHandle U      = u_nnf.get().as_compound().right;
    FormulaHandle notU   = builder.to_nnf(builder.make_not(U));

    // dl = Ax(0, 1) on [¬R, R, U].
    Deriv dl;
    dl.conclusion = {notR, R, U};
    dl.rule = RAx{0, 1};

    // dr = Ax(0, 1) on [¬Q, Q, ¬U].
    Deriv dr;
    dr.conclusion = {notQ, Q, notU};
    dr.rule = RAx{0, 1};

    // Call mcut directly.
    DerivPtr result = mcut(builder, dl, /*pl=*/2, dr, /*pr=*/2);
    if (!result) {
        std::cerr << "FAIL: mcut returned nullptr\n"; ++g_failed; return;
    }
    // Check conclusion.
    CHECK(result->conclusion.size() == 4);
    CHECK(result->conclusion[0] == notR);
    CHECK(result->conclusion[1] == R);
    CHECK(result->conclusion[2] == notQ);
    CHECK(result->conclusion[3] == Q);

    // Check rule is RAx with positions adjusted (dl's (0,1) stay at (0,1)
    // since pl=2 was past them).
    auto* ax = std::get_if<RAx>(&result->rule);
    if (!ax) { std::cerr << "FAIL: mcut result rule is not RAx\n"; ++g_failed; return; }
    CHECK(ax->a == 0);
    CHECK(ax->b == 1);

    // Round-trip: emit the result as a stand-alone proof of ⊢ ¬R ∨ R
    // by wrapping with Or(0). The (¬Q, Q) entries become a wider goal
    // context — we'd need the Or'd ¬R ∨ R as the goal, with ¬Q, Q as
    // "extra context" entries already present at start. For test, we
    // wrap the result with Or(0) targeting ¬R ∨ R, but the verifier
    // starts at a 1-entry goal — so we need a richer scaffold. Skip
    // the emit-round-trip for this unit test; just check structural
    // properties.
}

// =========================================================================
// P7 — §5.3 ∀/∃ principal cut.
//
// Cut(∀x.P(x)) where:
//   LEFT  = Forall(eigen=a) at the cut-formula position. LEFT's child
//           closes via a Γ-internal AxiomLit (non-principal w.r.t. cut).
//   RIGHT = Exists(witness=Term::fixed(a)) at the dual position.
//           RIGHT's child closes via the same Γ-internal AxiomLit.
//
// After reduction:
//   substitute a := a (no-op since witness uses the same eigen);
//   new Cut(P(a)) which then reduces via B1 axiom non-principal to a
//   plain RAx over Γ. Result: cut-free.
//
// Γ = [¬R, R] provides the dual pair for the inner Ax. The goal is
// just ⊢ Γ = ⊢ ¬R ∨ R wrapped via Or. The Cut on ∀x.P(x) is a
// gratuitous detour that B3 collapses.
// =========================================================================
void test_forall_exists_principal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "R -> R");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);  // ¬R ∨ R
    FormulaHandle notR = goal_nnf.get().as_compound().left;
    FormulaHandle R    = goal_nnf.get().as_compound().right;

    // Build ∀x.P(x) and ∃x.¬P(x) via parsing.
    FormulaHandle fa_P = parse_root(ctx, "forall x. P(x)");
    FormulaHandle fa_P_nnf = builder.to_nnf(fa_P);
    FormulaHandle ex_negP_nnf = builder.to_nnf(builder.make_not(fa_P));

    // Instantiate the body at eigen=0 to get P(0) and ¬P(0).
    var_index a = 0;
    FormulaHandle P_body = fa_P_nnf.get().as_quantified().body;
    FormulaHandle P_at_a = builder.instantiate_quantifier_body(P_body, Term::fixed(a));
    FormulaHandle neg_P_body = ex_negP_nnf.get().as_quantified().body;
    FormulaHandle negP_at_a = builder.instantiate_quantifier_body(neg_P_body, Term::fixed(a));

    // LEFT: RForall{principal=2, eigen=0, child=Ax(0,1) on [¬R, R, P(a)]}.
    auto leaf_L = std::make_unique<Deriv>();
    leaf_L->conclusion = {notR, R, P_at_a};
    leaf_L->rule = RAx{0, 1};
    auto forall_L = std::make_unique<Deriv>();
    forall_L->conclusion = {notR, R, fa_P_nnf};
    forall_L->rule = RForall{2, a, std::move(leaf_L)};

    // RIGHT: RExists{principal=2, witness=Term::fixed(0), child=Ax(0,1)
    //   on [¬R, R, ¬P(a)]}.
    auto leaf_R = std::make_unique<Deriv>();
    leaf_R->conclusion = {notR, R, negP_at_a};
    leaf_R->rule = RAx{0, 1};
    auto exists_R = std::make_unique<Deriv>();
    exists_R->conclusion = {notR, R, ex_negP_nnf};
    exists_R->rule = RExists{2, Term::fixed(a), std::move(leaf_R)};

    // Cut(∀x.P(x)) on [¬R, R].
    auto cut_node = std::make_unique<Deriv>();
    cut_node->conclusion = {notR, R};
    cut_node->rule = RCut{fa_P_nnf, std::move(forall_L), std::move(exists_R)};

    // Wrap with Or(0) at the goal level.
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(cut_node)};

    CHECK(count_cuts(*root) == 1);
    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);  // ∀/∃ principal + axiom non-principal
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "forall_exists_principal"));
}

// =========================================================================
// P8 — §5.4 Exchange permutation.
//
// Build a Cut(α) where LEFT's top rule is RExchange that swaps two
// Γ-internal positions (not touching the cut formula's slot at last).
// eliminate_cuts should permute: outer Exchange wrapping an inner cut
// on the swapped premises. The inner cut then triggers a B1 reduction
// (axiom non-principal) and disappears.
//
// Construction:
//   Goal: ⊢ R → R (NNF ¬R ∨ R), reach [¬R, R] via Or(0).
//   Then Cut(Q):
//     LEFT  = RExchange{0, 1, child=RAx(0,1) on [R, ¬R, Q]}.
//           LEFT.conclusion = [¬R, R, Q] (Exchange's pre-op = swapped
//           back). RAx on [R, ¬R, Q] closes via (R, ¬R) duality.
//     RIGHT = RAx(0, 1) on [¬R, R, ¬Q]. Closes via (¬R, R) duality.
//
//   Permutation: outer = RExchange{0, 1, inner_cut} where inner_cut =
//     Cut(Q, LEFT.child = RAx on [R, ¬R, Q],
//             RIGHT_wrapped = RExchange{0, 1, RIGHT} so its conclusion
//             = [R, ¬R, ¬Q]).
//   Inner cut is then non-principal axiom (RAx on [R, ¬R, Q] closes on
//   positions 0, 1 < last=2). B1 reduces to RAx(0, 1) on [R, ¬R].
//   Outer Exchange wraps it: conclusion = [¬R, R].
// =========================================================================
void test_exchange_permutation() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "R -> R");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);  // ¬R ∨ R
    FormulaHandle notR = goal_nnf.get().as_compound().left;
    FormulaHandle R    = goal_nnf.get().as_compound().right;

    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;
    FormulaHandle notQ   = builder.to_nnf(builder.make_not(Q));

    // LEFT side: RExchange{0, 1} over an Ax. Pre-Exchange conclusion =
    // [¬R, R, Q]. Post-Exchange (child) conclusion = [R, ¬R, Q]. The
    // Ax closes (R, ¬R) at positions 0, 1.
    auto ax_L_inner = std::make_unique<Deriv>();
    ax_L_inner->conclusion = {R, notR, Q};
    ax_L_inner->rule = RAx{0, 1};

    auto exchange_L = std::make_unique<Deriv>();
    exchange_L->conclusion = {notR, R, Q};
    exchange_L->rule = RExchange{0, 1, std::move(ax_L_inner)};

    // RIGHT: plain Ax(0, 1) on [¬R, R, ¬Q].
    auto ax_R = std::make_unique<Deriv>();
    ax_R->conclusion = {notR, R, notQ};
    ax_R->rule = RAx{0, 1};

    // Cut(Q) on [¬R, R].
    auto cut_node = std::make_unique<Deriv>();
    cut_node->conclusion = {notR, R};
    cut_node->rule = RCut{Q, std::move(exchange_L), std::move(ax_R)};

    // Wrap with Or to reach the goal.
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(cut_node)};

    CHECK(count_cuts(*root) == 1);
    auto reduced = eliminate_cuts(builder, *root);
    if (!reduced.ok()) {
        std::cerr << "FAIL: eliminate_cuts: " << reduced.error().to_string() << "\n";
        ++g_failed; return;
    }
    CHECK(count_cuts(*reduced.value()) == 0);  // Exchange permutation + B1
    CHECK_OK(emit_and_verify(ctx, goal, *reduced.value(), "exchange_permutation"));
}

// =========================================================================
// P6 — B0 framework: wrap_with_weakenings helper.
//
// Build a Deriv that proves [¬P, P, Q] via AxiomLit(0, 1). Wrap with
// weakenings({Q}) → outer node has conclusion [¬P, P]. The verifier's
// W grows [¬P, P] to [¬P, P, Q] before AxiomLit fires.
// =========================================================================
void test_wrap_with_weakenings() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaBuilder builder(ctx);
    FormulaHandle goal_nnf = builder.to_nnf(goal);
    FormulaHandle notP = goal_nnf.get().as_compound().left;
    FormulaHandle P    = goal_nnf.get().as_compound().right;

    FormulaHandle q_sent = parse_root(ctx, "Q -> Q");
    FormulaHandle q_nnf  = builder.to_nnf(q_sent);
    FormulaHandle Q      = q_nnf.get().as_compound().right;

    // base: AxiomLit(0, 1) on [¬P, P, Q].
    auto base = std::make_unique<Deriv>();
    base->conclusion = {notP, P, Q};
    base->rule = RAx{0, 1};

    // Wrap with Q → outer's conclusion = [¬P, P].
    auto wrapped = wrap_with_weakenings(std::move(base), {Q});
    CHECK(wrapped->conclusion.size() == 2);
    CHECK(wrapped->conclusion[0] == notP);
    CHECK(wrapped->conclusion[1] == P);
    CHECK(std::holds_alternative<RWeaken>(wrapped->rule));

    // Top-level Or to reach the goal [¬P ∨ P].
    auto root = std::make_unique<Deriv>();
    root->conclusion = {goal_nnf};
    root->rule = ROr{0, std::move(wrapped)};

    CHECK_OK(emit_and_verify(ctx, goal, *root, "wrap_w"));
}

}  // namespace

int main() {
    test_smoke_cut_free();
    test_dead_cut_W_left();
    test_dead_cut_W_right();
    test_axiom_cut_non_principal();
    test_axiom_cut_principal();
    test_wrap_with_weakenings();
    test_forall_exists_principal();
    test_exchange_permutation();
    test_mcut_ax_nonprincipal();
    std::cout << "reduce_test: " << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
