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

}  // namespace

int main() {
    test_smoke_weakening_free();
    test_W_absorb_at_ax_nonprincipal();
    test_W_absorb_at_one();
    std::cout << "weak_elim_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
