// axiom_rewrap Phase 1 tests — compute_transitive_facts.
//
// Per AXIOM_REWRAP_DESIGN.md §7.1, this phase delivers:
//   compute_transitive_facts(prog, ctx, theorem_axioms) → vector<string>
//
// The function returns axiom names (lex-sorted, deduplicated) for:
//   - direct Use(A) where ctx resolves A as an axiom
//   - transitive Use(T) where ctx resolves T as a theorem, via
//     theorem_axioms[T]
//
// SchemaInst is out of Phase 1 scope (errors clearly if encountered).

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/axiom_rewrap/axiom_rewrap.h"
#include "src/proof/translate/axiom_rewrap/theorem_axioms.h"
#include "src/proof/translate/lkr_to_comb/lkr_to_comb.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <string>
#include <variant>
#include <vector>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::axiom_rewrap::AxiomRewrap;
using logic::proof::translate::axiom_rewrap::RewrapResult;
using logic::proof::translate::axiom_rewrap::TheoremFactsMap;
using logic::proof::translate::axiom_rewrap::compute_transitive_facts;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_TRUE(expr) do { \
    if (expr) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_EQ(a, b) do { \
    auto _a = (a); auto _b = (b); \
    if (_a == _b) { ++g_passed; } else { \
        std::cerr << "FAIL: " #a " == " #b " at " __FILE__ ":" << __LINE__ \
                  << " (lhs/rhs differ)\n"; \
        ++g_failed; \
    } \
} while (0)

Program<nd::Instr> lower_or_die(const ParsedProof& parsed, const GlobalContext& ctx) {
    auto r = nd::lower(parsed, ctx);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

// =========================================================================
// Test 1: empty axiom set
// A proof of `p -> p` via assume/qed uses no axioms.
// =========================================================================
void test_empty_axiom_set() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap registry;

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        EXPECT_EQ(r.value().size(), size_t{0});
    }
}

// =========================================================================
// Test 2: single axiom used once
// =========================================================================
void test_single_axiom_used_once() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_true: forall x. p(x)
        claim p_y: forall y. p(y)
        proof p_y:
            fix y
            h = use a_true
            h2 = forall_elim h, y
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap registry;

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_true"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 3: same axiom used multiple times → dedup
// =========================================================================
void test_same_axiom_used_many_times() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_holds: p
        claim p_and_p: p & p
        proof p_and_p:
            h1 = use p_holds
            h2 = use p_holds
            h3 = and_intro h1, h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap registry;

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"p_holds"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 4: multiple axioms in non-lex source order, output is lex-sorted
// =========================================================================
void test_multiple_axioms_lex_sort() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom c_ax: c_pred
        axiom a_ax: a_pred
        axiom b_ax: b_pred
        claim abc: a_pred & b_pred & c_pred
        proof abc:
            hc = use c_ax
            ha = use a_ax
            hb = use b_ax
            hab = and_intro ha, hb
            habc = and_intro hab, hc
            qed habc
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap registry;

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax", "b_ax", "c_ax"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 5: one-theorem transitive dep
// Proof uses theorem T, which itself uses axiom A.
// Closure = {A, t_thm} (under uniform fact treatment, T contributes
// itself AND its transitive facts).
// =========================================================================
void test_one_theorem_dep() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim t_thm: a_pred
        proof t_thm:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Simulate that t_thm has been translated and its closure is recorded.
    TheoremFactsMap registry;
    registry.put("t_thm", std::vector<std::string>{"a_ax"});

    // Now a proof that uses t_thm.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t: a_pred
        proof use_t:
            h = use t_thm
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Register t_thm as a theorem in ctx BEFORE lowering — lowering now
    // eagerly resolves Use names to SentenceHandles, so the cited theorem
    // must be visible. (Previously this happened lazily at verify time.)
    auto t_thm_sentence = rt.context().find_claim("t_thm");
    if (!t_thm_sentence.has_value()) {
        std::cerr << "FAIL: t_thm claim not found\n"; ++g_failed; return;
    }
    rt.context().add_theorem("t_thm", t_thm_sentence.value());

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax", "t_thm"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 6: chained theorem deps (T2 uses T1 uses A)
// =========================================================================
void test_chained_theorem_deps() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim t1: a_pred
        proof t1:
            h = use a_ax
            qed h
        claim t2: a_pred
        proof t2:
            h = use t1
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremFactsMap registry;
    registry.put("t1", std::vector<std::string>{"a_ax"});
    // Under uniform fact treatment, t2's facts include t1 itself + t1's facts.
    registry.put("t2", std::vector<std::string>{"a_ax", "t1"});

    // Outer proof using t2.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t2: a_pred
        proof use_t2:
            h = use t2
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Register t1, t2 as theorems BEFORE lowering — eager resolution.
    auto t1_s = rt.context().find_claim("t1");
    auto t2_s = rt.context().find_claim("t2");
    if (!t1_s || !t2_s) {
        std::cerr << "FAIL: t1/t2 not found\n"; ++g_failed; return;
    }
    rt.context().add_theorem("t1", t1_s.value());
    rt.context().add_theorem("t2", t2_s.value());

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax", "t1", "t2"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 7: theorem cited but not in registry → error (caller bug)
// =========================================================================
void test_theorem_not_in_registry_errors() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim t_missing: p
        proof t_missing:
            h = assume p
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Outer proof citing the unregistered theorem.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_missing: p
        proof use_missing:
            h = use t_missing
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Promote t_missing as a theorem in ctx but DO NOT add to registry.
    // (Must be done before lowering so the Use's name resolves at
    // lowering time — see lowering.cpp.)
    auto t_s = rt.context().find_claim("t_missing");
    if (!t_s) { std::cerr << "FAIL: claim missing\n"; ++g_failed; return; }
    rt.context().add_theorem("t_missing", t_s.value());

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    TheoremFactsMap registry;  // empty: t_missing not registered

    auto r = compute_transitive_facts(prog, rt.context(), registry);
    EXPECT_TRUE(r.is_error());
}

// =========================================================================
// Phase 2: AxiomRewrap::apply — boundary wrap mechanism.
// =========================================================================

// Helper: count Assume ops in a program (excluding ones with AST formulas).
int count_synthetic_assume(const Program<nd::Instr>& prog) {
    int n = 0;
    for (const auto& instr : prog.instrs) {
        if (const auto* a = std::get_if<nd::Assume>(&instr)) {
            if (a->resolved.has_value() && !a->formula) ++n;
        }
    }
    return n;
}

// Helper: count Use ops in `prog` that resolve to axioms in `ctx`.
// Phase 4's contract is that this returns 0 in the rewrap output.
int count_axiom_uses(const Program<nd::Instr>& prog, const GlobalContext& ctx) {
    int n = 0;
    for (const auto& instr : prog.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            if (auto name = ctx.name_of(u->axiom.sentence); name.has_value()
                && ctx.find_axiom(*name).has_value()) ++n;
        }
    }
    return n;
}

// =========================================================================
// Phase 2 Test 1: apply on a proof with no axiom uses → identity
// =========================================================================
void test_apply_no_axioms_identity() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    size_t input_size = prog.instrs.size();
    auto claim = rt.context().find_claim("p_self");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << r.error().to_string() << "\n"; return; }

    const auto& res = r.value();
    EXPECT_EQ(res.facts.size(), size_t{0});
    EXPECT_EQ(res.wrapped_goal, goal);
    EXPECT_EQ(res.proof.instrs.size(), input_size);
    EXPECT_EQ(count_synthetic_assume(res.proof), 0);
}

// =========================================================================
// Phase 2 Test 2: apply on a proof using one axiom → wrapped
// Boundary scaffold only — Phase 2 does NOT drop the body's Use(A).
// The wrap produces a verifiable H → φ proof regardless.
// =========================================================================
void test_apply_single_axiom_wrap() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_true: forall x. p(x)
        claim p_y: forall y. p(y)
        proof p_y:
            fix y
            h = use a_true
            h2 = forall_elim h, y
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    size_t input_size = prog.instrs.size();
    auto claim = rt.context().find_claim("p_y");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "apply fail: " << r.error().to_string() << "\n";
        return;
    }

    const auto& res = r.value();
    EXPECT_EQ(res.facts.size(), size_t{1});
    if (res.facts.size() == 1) {
        EXPECT_EQ(res.facts[0], std::string("a_true"));
    }
    // Wrapped goal != original goal (now H → φ).
    EXPECT_TRUE(res.wrapped_goal != goal);
    // Layout (Phase 4): +1 Assume, -1 Qed, -1 Use(a_true), +2 (ImpliesIntro+Qed).
    EXPECT_EQ(res.proof.instrs.size(), input_size + 1);
    EXPECT_EQ(count_synthetic_assume(res.proof), 1);
    // Phase 4 contract: no axiom Use ops survive.
    EXPECT_EQ(count_axiom_uses(res.proof, rt.context()), 0);

    // Output gate already ran NDVerifier inside apply(); also re-verify
    // explicitly to make the contract visible at the test layer.
    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = res.proof;
    auto vr = verifier.verify(rt.context(), res.wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify fail: " << vr.error().to_string() << "\n";
    }
}

// =========================================================================
// Phase 2 Test 3: apply on a proof using two axioms → conjunction H
// =========================================================================
void test_apply_two_axioms_wrap() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom b_ax: q2
        axiom a_ax: q1
        claim q1_and_q2: q1 & q2
        proof q1_and_q2:
            ha = use a_ax
            hb = use b_ax
            hab = and_intro ha, hb
            qed hab
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("q1_and_q2");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "apply fail: " << r.error().to_string() << "\n";
        return;
    }

    const auto& res = r.value();
    // Two axioms, lex-sorted: a_ax, b_ax.
    EXPECT_EQ(res.facts.size(), size_t{2});
    if (res.facts.size() == 2) {
        EXPECT_EQ(res.facts[0], std::string("a_ax"));
        EXPECT_EQ(res.facts[1], std::string("b_ax"));
    }
    // Phase 4: axiom Uses dropped from body.
    EXPECT_EQ(count_axiom_uses(res.proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = res.proof;
    auto vr = verifier.verify(rt.context(), res.wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify fail: " << vr.error().to_string() << "\n";
    }
}

// =========================================================================
// Phase 3: structural-copy coverage across ND op kinds.
//
// shift_refs is compile-time exhaustive over nd::Instr (all 30+ variants
// have arms). Phase 3 runtime tests sample representative op families to
// confirm the shifted output remains verifier-accepted. Each test:
//   1. Includes at least one Use(A) to trigger n ≥ 1 wrap.
//   2. Body exercises a target op family.
//   3. NDVerifier accepts the wrapped output (post-shift).
// A miswired StepRef field in shift_refs would surface as a dangling-ref
// or formula-mismatch verifier error.
// =========================================================================

// Shared helper: parse + lower + apply + verify wrapped output.
void verify_wrap(Runtime& rt, const char* source, const char* claim_name) {
    auto parsed = rt.load_with_proofs(source);
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    // Find the proof for the requested claim (there may be others in source).
    const ParsedProof* target = nullptr;
    for (const auto& p : parsed.value().proofs) {
        if (p.claim_name == claim_name) { target = &p; break; }
    }
    if (!target) {
        std::cerr << "claim '" << claim_name << "' has no proof\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(*target, rt.context());
    auto claim = rt.context().find_claim(claim_name);
    if (!claim) {
        std::cerr << "claim '" << claim_name << "' missing\n";
        ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    if (!r.ok()) {
        std::cerr << "apply fail for '" << claim_name << "': "
                  << r.error().to_string() << "\n";
        ++g_failed; return;
    }

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    if (!vr.ok()) {
        std::cerr << "verify fail for '" << claim_name << "': "
                  << vr.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// =========================================================================
// Phase 3 Test A: Or family + Let
// Covers: use, assume, let, or_intro_l, or_intro_r, or_elim, implies_intro
// =========================================================================
void test_apply_body_or_family() {
    Runtime rt;
    verify_wrap(rt, R"(
        axiom p_or_q: p | q
        claim q_or_p: q | p
        proof q_or_p:
            h_pq = use p_or_q
            h1 = assume p
            h_q_let = let q
            h2 = or_intro_r h_q_let, h1
            h3 = implies_intro h2
            h4 = assume q
            h_p_let = let p
            h5 = or_intro_l h4, h_p_let
            h6 = implies_intro h5
            h7 = or_elim h_pq, h3, h6
            qed h7
    )", "q_or_p");
}

// =========================================================================
// Phase 3 Test B: Iff family + ImpliesIntro mixed
// Covers: use, assume, iff_elim_l, iff_elim_r, iff_intro, implies_intro
// =========================================================================
void test_apply_body_iff_family() {
    Runtime rt;
    verify_wrap(rt, R"(
        axiom a_iff_b: a <-> b
        claim a_iff_b_again: a <-> b
        proof a_iff_b_again:
            h = use a_iff_b
            h_a = assume a
            h_b1 = iff_elim_l h, h_a
            h_ab = implies_intro h_b1
            h_b = assume b
            h_a1 = iff_elim_r h, h_b
            h_ba = implies_intro h_a1
            h_iff = iff_intro h_ab, h_ba
            qed h_iff
    )", "a_iff_b_again");
}

// =========================================================================
// Phase 3 Test C: And-elim + Negation + Bottom-elim + Let
// Covers: use, and_elim_l, and_elim_r, not_elim, let, bottom_elim
// =========================================================================
void test_apply_body_negation_and_bottom() {
    Runtime rt;
    verify_wrap(rt, R"(
        axiom p_and_not_p: p & ~p
        claim derive_q: exists x. q(x)
        proof derive_q:
            h_pnp = use p_and_not_p
            h_p = and_elim_l h_pnp
            h_np = and_elim_r h_pnp
            h_bot = not_elim h_np, h_p
            h_target = let exists x. q(x)
            h_q = bottom_elim h_bot, h_target
            qed h_q
    )", "derive_q");
}

// =========================================================================
// Phase 3 Test D: Exists family
// Covers: use, exists_elim (binding witness), exists_intro (scope-closing).
// The scope-closing form is required here so the assume(H) scope is what
// the trailing implies_intro discharges.
// =========================================================================
void test_apply_body_exists_family() {
    Runtime rt;
    verify_wrap(rt, R"(
        axiom exists_p: exists x. p(x)
        claim exists_p_again: exists y. p(y)
        proof exists_p_again:
            h = use exists_p
            h_w = exists_elim h, w
            h_intro = exists_intro h_w
            qed h_intro
    )", "exists_p_again");
}

// =========================================================================
// Phase 3 Test E: Classical (DoubleNegElim)
// Covers: use, double_neg_elim. Adds n=1 wrap via the use(not_not_p) axiom.
// ExcludedMiddle, ClassicalAbsurd, Peirce are covered by compile-time
// exhaustiveness in shift_refs; their interaction with NDVerifier under
// shift is identical to the simpler ops tested here.
// =========================================================================
void test_apply_body_classical_double_neg() {
    Runtime rt;
    verify_wrap(rt, R"(
        axiom not_not_p: ~~p
        claim p_holds: p
        proof p_holds:
            h = use not_not_p
            h2 = double_neg_elim h
            qed h2
    )", "p_holds");
}

// =========================================================================
// Phase 4: Use(A) axiom drop + extraction chain.
//
// Output's axiom_step_table caches A_i once at the prelude; every body
// Use(A_i) is dropped and downstream refs alias the cached extract. The
// output has zero Use ops resolving to axioms. NDVerifier accepts H → φ.
// =========================================================================

// Phase 4 Test 1: single axiom used once → dropped; cached at prelude.
void test_apply_axiom_dropped_no_other_uses() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_true: a_pred
        claim a_again: a_pred
        proof a_again:
            h = use a_true
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("a_again");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);
    EXPECT_EQ(count_synthetic_assume(r.value().proof), 1);
}

// Phase 4 Test 2: single axiom used MANY times → cached once, all aliased.
void test_apply_axiom_cached_across_multi_use() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_holds: p
        claim p_and_p_and_p: p & p & p
        proof p_and_p_and_p:
            h1 = use p_holds
            h2 = use p_holds
            h3 = use p_holds
            h12 = and_intro h1, h2
            h123 = and_intro h12, h3
            qed h123
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("p_and_p_and_p");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify fail: " << vr.error().to_string() << "\n";
    }
}

// Phase 4 Test 3: two axioms, mixed uses → extraction chain (n=2),
// 2 AndElim ops, both Uses dropped.
void test_apply_two_axioms_dropped_with_extracts() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        axiom b_ax: b_pred
        claim a_and_b: a_pred & b_pred
        proof a_and_b:
            ha = use a_ax
            hb = use b_ax
            hab = and_intro ha, hb
            qed hab
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("a_and_b");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << r.error().to_string() << "\n"; return; }
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify fail: " << vr.error().to_string() << "\n";
    }
}

// Phase 4 Test 4: three axioms → extraction chain has depth-2 left peel
// (h_3 = and_elim_l h, h_2 = and_elim_l h_3 = and_elim_l h_3) plus
// AndElimR's at h and h_3. Verifies the nested-extract algorithm.
void test_apply_three_axioms_dropped_with_extracts() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom c_ax: c_pred
        axiom a_ax: a_pred
        axiom b_ax: b_pred
        claim abc: a_pred & b_pred & c_pred
        proof abc:
            ha = use a_ax
            hb = use b_ax
            hc = use c_ax
            hab = and_intro ha, hb
            habc = and_intro hab, hc
            qed habc
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("abc");
    if (!claim) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap registry;
    AxiomRewrap pass(rt.context(), goal, registry);
    auto r = pass.apply(prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << r.error().to_string() << "\n"; return; }

    const auto& res = r.value();
    // Lex order: a_ax, b_ax, c_ax. H = ((a ∧ b) ∧ c).
    EXPECT_EQ(res.facts.size(), size_t{3});
    EXPECT_EQ(count_axiom_uses(res.proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = res.proof;
    auto vr = verifier.verify(rt.context(), res.wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify fail: " << vr.error().to_string() << "\n";
    }
}

// =========================================================================
// Phase 5: Use(T) theorem unwrap macro.
//
// For Use(T) where axioms(T) ≠ ∅, emit:
//   [k₀]  Use{resolved: H_T → φ_T}        ← bind the wrapped form
//   [k₁]  and_intro chain over            ← rebuild H_T from axiom_step_table
//          axiom_step_table[A_i]           (lex order matches H_T's shape)
//   [k₂]  ImpliesElim([k₀], [k₁])         ← modus ponens, binds φ_T
//
// Downstream refs to the original Use(T) are aliased to [k₂].
// For axioms(T) = ∅: no unwrap; emit Use(T) as-is (it binds φ_T directly).
// =========================================================================

// Helper: run axiom_rewrap on theorem T's proof, register T as a theorem
// in ctx, and populate the registries. Returns the rewrap result for the
// caller to inspect (e.g., to confirm the wrapped form). The caller
// supplies the input registries so chained theorems compose correctly
// (T_2 needs T_1's entries already populated).
RewrapResult setup_wrapped_theorem(
    Runtime& rt,
    const ParseResult& parsed,
    const std::string& T_name,
    TheoremFactsMap& thm_facts)
{
    const ParsedProof* p = nullptr;
    for (const auto& pp : parsed.proofs) {
        if (pp.claim_name == T_name) { p = &pp; break; }
    }
    if (!p) {
        std::cerr << "setup_wrapped_theorem: no proof for '" << T_name << "'\n";
        std::abort();
    }
    Program<nd::Instr> prog = lower_or_die(*p, rt.context());
    auto claim = rt.context().find_claim(T_name);
    if (!claim) {
        std::cerr << "setup_wrapped_theorem: no claim for '" << T_name << "'\n";
        std::abort();
    }
    FormulaHandle T_goal = claim.value().get().root();

    AxiomRewrap pass(rt.context(), T_goal, thm_facts);
    auto r = pass.apply(prog);
    if (!r.ok()) {
        std::cerr << "setup_wrapped_theorem(" << T_name << "): "
                  << r.error().to_string() << "\n";
        std::abort();
    }

    rt.context().add_theorem(T_name, claim.value());
    thm_facts.put(T_name, r.value().facts);
    return std::move(r).unwrap();
}

// Phase 5 Test 1: theorem T uses one axiom A; outer proof uses T.
void test_apply_theorem_use_one_axiom() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: a
        claim t1: a
        proof t1:
            h = use a_holds
            qed h
        claim outer: a
        proof outer:
            h = use t1
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremFactsMap thm_axioms;
    setup_wrapped_theorem(rt, parsed.value(), "t1", thm_axioms);

    // Outer rewrap.
    Program<nd::Instr> outer_prog =
        lower_or_die(*[&]() -> const ParsedProof* {
            for (const auto& p : parsed.value().proofs)
                if (p.claim_name == "outer") return &p;
            return nullptr;
        }(), rt.context());
    auto outer_claim = rt.context().find_claim("outer");
    FormulaHandle outer_goal = outer_claim.value().get().root();

    AxiomRewrap pass(rt.context(), outer_goal, thm_axioms);
    auto r = pass.apply(outer_prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    // Outer's facts = {a_holds, t1} — direct axiom plus the cited theorem
    // itself under uniform fact treatment.
    EXPECT_EQ(r.value().facts.size(), size_t{2});
    if (r.value().facts.size() == 2) {
        EXPECT_EQ(r.value().facts[0], std::string("a_holds"));
        EXPECT_EQ(r.value().facts[1], std::string("t1"));
    }
    // Phase 4 contract still holds: no axiom Use ops.
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    // Output gate already ran NDVerifier; re-verify for visibility.
    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << vr.error().to_string() << "\n";
}

// Phase 5 Test 2: theorem T uses two axioms; outer uses T.
// Exercises the and_intro chain in the unwrap macro.
void test_apply_theorem_use_two_axioms() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: a
        axiom b_holds: b
        claim t: a & b
        proof t:
            h_a = use a_holds
            h_b = use b_holds
            h_ab = and_intro h_a, h_b
            qed h_ab
        claim outer: a & b
        proof outer:
            h = use t
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremFactsMap thm_axioms;
    setup_wrapped_theorem(rt, parsed.value(), "t", thm_axioms);

    Program<nd::Instr> outer_prog =
        lower_or_die(*[&]() -> const ParsedProof* {
            for (const auto& p : parsed.value().proofs)
                if (p.claim_name == "outer") return &p;
            return nullptr;
        }(), rt.context());
    auto outer_claim = rt.context().find_claim("outer");
    FormulaHandle outer_goal = outer_claim.value().get().root();

    AxiomRewrap pass(rt.context(), outer_goal, thm_axioms);
    auto r = pass.apply(outer_prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    // outer cites t which uses {a_holds, b_holds}. facts(outer) =
    // {a_holds, b_holds, t} (t plus its transitive facts).
    EXPECT_EQ(r.value().facts.size(), size_t{3});
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << vr.error().to_string() << "\n";
}

// Phase 5 Test 3: theorem chain T_2 → T_1 → A. Verifies the
// transitive-closure threading: facts(outer) includes t1, t2, a_holds.
void test_apply_theorem_chain() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: a
        claim t1: a
        proof t1:
            h = use a_holds
            qed h
        claim t2: a
        proof t2:
            h = use t1
            qed h
        claim outer: a
        proof outer:
            h = use t2
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremFactsMap thm_axioms;
    setup_wrapped_theorem(rt, parsed.value(), "t1", thm_axioms);
    setup_wrapped_theorem(rt, parsed.value(), "t2", thm_axioms);

    Program<nd::Instr> outer_prog =
        lower_or_die(*[&]() -> const ParsedProof* {
            for (const auto& p : parsed.value().proofs)
                if (p.claim_name == "outer") return &p;
            return nullptr;
        }(), rt.context());
    auto outer_claim = rt.context().find_claim("outer");
    FormulaHandle outer_goal = outer_claim.value().get().root();

    AxiomRewrap pass(rt.context(), outer_goal, thm_axioms);
    auto r = pass.apply(outer_prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    // outer uses t2 → t1 → a_holds. facts(outer) = {a_holds, t1, t2}.
    EXPECT_EQ(r.value().facts.size(), size_t{3});
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << vr.error().to_string() << "\n";
}

// Phase 5 Test 4: theorem with no facts of its own; Use(T) is dropped
// and aliased to the extracted h_taut (taut's formula sits in H_outer).
void test_apply_theorem_no_axioms_no_unwrap() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: a
        claim taut: p -> p
        proof taut:
            h = assume p
            h2 = implies_intro h
            qed h2
        claim outer: a & (p -> p)
        proof outer:
            h_a = use a_holds
            h_taut = use taut
            h = and_intro h_a, h_taut
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremFactsMap thm_axioms;
    auto taut_result =
        setup_wrapped_theorem(rt, parsed.value(), "taut", thm_axioms);
    EXPECT_EQ(taut_result.facts.size(), size_t{0});

    Program<nd::Instr> outer_prog =
        lower_or_die(*[&]() -> const ParsedProof* {
            for (const auto& p : parsed.value().proofs)
                if (p.claim_name == "outer") return &p;
            return nullptr;
        }(), rt.context());
    auto outer_claim = rt.context().find_claim("outer");
    FormulaHandle outer_goal = outer_claim.value().get().root();

    AxiomRewrap pass(rt.context(), outer_goal, thm_axioms);
    auto r = pass.apply(outer_prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << r.error().to_string() << "\n"; return;
    }
    // Outer uses a_holds (direct axiom) + taut (theorem).
    // Under uniform design, facts(outer) = {a_holds, taut} (both go in H_outer).
    EXPECT_EQ(r.value().facts.size(), size_t{2});
    EXPECT_EQ(count_axiom_uses(r.value().proof, rt.context()), 0);

    // No Use(taut) op should survive — drop-and-alias treats theorems
    // exactly like axioms.
    int use_taut_count = 0;
    for (const auto& instr : r.value().proof.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            if (auto name = rt.context().name_of(u->axiom.sentence);
                name.has_value() && *name == "taut") ++use_taut_count;
        }
    }
    EXPECT_EQ(use_taut_count, 0);

    nd::NDVerifier verifier;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = verifier.verify(rt.context(), r.value().wrapped_goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << vr.error().to_string() << "\n";
}

// (Former Phase 5 Test 5: tested missing WrappedTheoremMap entry — no
// longer applicable under the uniform fact treatment, where there is
// no WrappedTheoremMap to be missing from. Deleted 2026-05-18.)

// =========================================================================
// Phase 6: End-to-end pipeline integration.
//
// Wires axiom_rewrap into the existing ND → NDtoLKR → LKRtoComb chain and
// confirms the result is a CombVerifier-accepted CombProof of the WRAPPED
// goal H → φ. This is the obligation that closes COMPLETENESS.md §4.3.
//
// The pipeline (per AXIOM_REWRAP_DESIGN.md §3.1):
//   ND  →  axiom_rewrap  →  NDtoLKR  →  LKRtoComb  →  CombProof of H → φ
//
// (iota_elim is omitted here — the proofs below have no iota terms;
// adding it would only matter for ZFC fixtures containing `iota_elim`
// ops, which can be incorporated later.)
// =========================================================================

namespace lc = logic::proof::translate::lkr_to_comb;
namespace ntl = logic::proof::translate::nd_to_lkr;

// Phase 6 Test 1: minimal end-to-end. Single axiom, trivial proof.
// Goal: confirm the synthetic Assume(resolved=H) emitted by axiom_rewrap
// survives NDtoLKR's trace-based pipeline + LKRtoComb's machinery.
void test_integration_simple_axiom_to_comb() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: p
        claim derive_p: p
        proof derive_p:
            h = use a_holds
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("derive_p");
    FormulaHandle goal = claim.value().get().root();

    // Stage 1: axiom_rewrap. Output: ND proof of p → p (axiom-free).
    TheoremFactsMap thm_axioms;
    AxiomRewrap rewrap(rt.context(), goal, thm_axioms);
    auto rwr = rewrap.apply(prog);
    if (!rwr.ok()) {
        std::cerr << "axiom_rewrap fail: " << rwr.error().to_string() << "\n";
        ++g_failed; return;
    }
    FormulaHandle wrapped_goal = rwr.value().wrapped_goal;

    // Stage 2: NDtoLKR. Translate the wrapped ND proof to LKR.
    ntl::NDtoLKR ndl(rt.context(), wrapped_goal);
    auto lkr_r = ndl.apply(rwr.value().proof);
    if (!lkr_r.ok()) {
        std::cerr << "nd_to_lkr fail: " << lkr_r.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Stage 3: LKRtoComb. Translate LKR to a CombProof of H → φ.
    lc::LemmaCombProofs no_lemmas;
    lc::LKRtoComb comb(rt.context(), wrapped_goal, no_lemmas);
    auto comb_r = comb.apply(lkr_r.value());
    EXPECT_TRUE(comb_r.ok());
    if (!comb_r.ok()) {
        std::cerr << "lkr_to_comb fail: " << comb_r.error().to_string() << "\n";
    }
}

// Phase 6 Test 2: two-axiom integration. Exercises the extraction chain
// (n=2 prelude with AndElimL + AndElimR) in axiom_rewrap, followed by
// the downstream translators on a slightly richer proof.
void test_integration_two_axioms_to_comb() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_holds: a
        axiom b_holds: b
        claim derive_ab: a & b
        proof derive_ab:
            ha = use a_holds
            hb = use b_holds
            hab = and_intro ha, hb
            qed hab
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("derive_ab");
    FormulaHandle goal = claim.value().get().root();

    TheoremFactsMap thm_axioms;
    AxiomRewrap rewrap(rt.context(), goal, thm_axioms);
    auto rwr = rewrap.apply(prog);
    if (!rwr.ok()) {
        std::cerr << "axiom_rewrap fail: " << rwr.error().to_string() << "\n";
        ++g_failed; return;
    }
    FormulaHandle wrapped_goal = rwr.value().wrapped_goal;

    ntl::NDtoLKR ndl(rt.context(), wrapped_goal);
    auto lkr_r = ndl.apply(rwr.value().proof);
    if (!lkr_r.ok()) {
        std::cerr << "nd_to_lkr fail: " << lkr_r.error().to_string() << "\n";
        ++g_failed; return;
    }

    lc::LemmaCombProofs no_lemmas;
    lc::LKRtoComb comb(rt.context(), wrapped_goal, no_lemmas);
    auto comb_r = comb.apply(lkr_r.value());
    EXPECT_TRUE(comb_r.ok());
    if (!comb_r.ok()) {
        std::cerr << "lkr_to_comb fail: " << comb_r.error().to_string() << "\n";
    }
}


}  // namespace

int main() {
    // Phase 1 — compute_transitive_facts
    test_empty_axiom_set();
    test_single_axiom_used_once();
    test_same_axiom_used_many_times();
    test_multiple_axioms_lex_sort();
    test_one_theorem_dep();
    test_chained_theorem_deps();
    test_theorem_not_in_registry_errors();

    // Phase 2 — AxiomRewrap::apply boundary wrap
    test_apply_no_axioms_identity();
    test_apply_single_axiom_wrap();
    test_apply_two_axioms_wrap();

    // Phase 3 — structural-copy coverage across ND op kinds
    test_apply_body_or_family();
    test_apply_body_iff_family();
    test_apply_body_negation_and_bottom();
    test_apply_body_exists_family();
    test_apply_body_classical_double_neg();

    // Phase 4 — Use(A) axiom drop + extraction chain
    test_apply_axiom_dropped_no_other_uses();
    test_apply_axiom_cached_across_multi_use();
    test_apply_two_axioms_dropped_with_extracts();
    test_apply_three_axioms_dropped_with_extracts();

    // Phase 5 — Use(T) theorem unwrap macro
    test_apply_theorem_use_one_axiom();
    test_apply_theorem_use_two_axioms();
    test_apply_theorem_chain();
    test_apply_theorem_no_axioms_no_unwrap();

    // Phase 6 — end-to-end integration (axiom_rewrap → NDtoLKR → LKRtoComb)
    test_integration_simple_axiom_to_comb();
    test_integration_two_axioms_to_comb();

    std::cerr << "axiom_rewrap_test: passed " << g_passed
              << ", failed " << g_failed << "\n";
    return g_failed == 0 ? 0 : 1;
}
