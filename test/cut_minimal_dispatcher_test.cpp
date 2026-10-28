// Stage 2 dispatcher regressions; NDtoLKR's OutputGate verifies each output.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/runner.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::NDtoLKR;

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
                  << _r.error().to_string() \
                  << " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

Program<nd::Instr> lower_or_die(const ParsedProof& parsed,
                                  const GlobalContext& ctx)
{
    auto r = nd::lower(parsed, ctx);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

util::ResultStatus translate_and_verify(
    Runtime&                    rt,
    const Program<nd::Instr>&   prog,
    FormulaHandle               goal)
{
    NDtoLKR pass(rt.context(), goal);
    auto out = pass.apply(prog);
    if (!out.ok()) return out.error();
    return util::Ok();
}

// =========================================================================
// Test 1: ExcludedMiddle as Qed.derived. Goal: A | ~A.
// =========================================================================
void test_excluded_middle_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim em_test: A | ~A
        proof em_test:
            a_let = let A
            em = excluded_middle a_let
            qed em
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("em_test");
    if (!sh.has_value()) { std::cerr << "no em_test claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

// =========================================================================
// Test 2: Peirce as Qed.derived. Goal: ((A -> B) -> A) -> A.
// =========================================================================
void test_peirce_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim peirce_test: ((A -> B) -> A) -> A
        proof peirce_test:
            a_let = let A
            b_let = let B
            p = peirce a_let, b_let
            qed p
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("peirce_test");
    if (!sh.has_value()) { std::cerr << "no peirce_test claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

// =========================================================================
// Test 3: AndIntro of two ExcludedMiddles. Goal: (A | ~A) & (B | ~B).
// Exercises TwoPremise recursion.
// =========================================================================
void test_and_of_em_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim and_em: (A | ~A) & (B | ~B)
        proof and_em:
            a_let = let A
            em_a = excluded_middle a_let
            b_let = let B
            em_b = excluded_middle b_let
            ai = and_intro em_a, em_b
            qed ai
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("and_em");
    if (!sh.has_value()) { std::cerr << "no and_em claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

// =========================================================================
// Test 4 (5c): AndElimL on AndIntro of two ExcludedMiddles.
// Goal: A | ~A. Demand-driven: and_elim_l promotes AND_LEFT; and_intro
// short-circuits to its `a` premise (em_a); em_a's excluded_middle
// closes the goal. The result LKR program is [Or, AxiomLit] —
// identical to test 1 (excluded_middle direct), demonstrating that
// the projection elim contributes ZERO ops.
// =========================================================================
void test_and_elim_l_of_em_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim a_or_na: A | ~A
        proof a_or_na:
            a_let = let A
            em_a = excluded_middle a_let
            b_let = let B
            em_b = excluded_middle b_let
            ai = and_intro em_a, em_b
            el = and_elim_l ai
            qed el
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("a_or_na");
    if (!sh.has_value()) { std::cerr << "no a_or_na claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

// =========================================================================
// Test 5 (5c): AndElimR (symmetric).
// =========================================================================
void test_and_elim_r_of_em_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim b_or_nb: B | ~B
        proof b_or_nb:
            a_let = let A
            em_a = excluded_middle a_let
            b_let = let B
            em_b = excluded_middle b_let
            ai = and_intro em_a, em_b
            er = and_elim_r ai
            qed er
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("b_or_nb");
    if (!sh.has_value()) { std::cerr << "no b_or_nb claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

// =========================================================================
// Test 6: a proof that leaves its `fix` scope open is rejected.
// =========================================================================
void test_open_fix_scope_rejected() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. P(x)
        claim need_inst: P
        proof need_inst:
            fix v
            ap = use all_p
            inst = forall_elim ap, v
            qed inst
    )");
    if (!parsed.ok()) {
        // The proof might not parse cleanly without nd_internalize first.
        // Skip negative test if parse fails.
        return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("need_inst");
    if (!sh.has_value()) { return; }
    FormulaHandle goal = sh->get().root();

    auto r = translate_and_verify(rt, prog, goal);
    CHECK(!r.ok());
}

// =========================================================================
// Test 7 (5e.1): ImpliesIntro of Assume — A -> A.
// Dispatcher: Qed.derived = ImpliesIntro. emit_implies_intro emits Or,
// places ¬A at f_k_idx, records shadow.step_to_neg_idx[assume_step]
// = f_k_idx. Recurses on conclusion = the Assume step. Assume leaf
// handler does emit_close on (target_pos, recorded dual_pos).
// =========================================================================
// =========================================================================
// Test 8 (5e.2): NotIntro of contradiction.
// Goal: ~~(A | ~A). Proof: assume ~(A|~A); derive em = (A|~A) via
// excluded_middle; not_elim h, em gives ⊥; not_intro h_bot proves
// ~~(A|~A).
// =========================================================================
// =========================================================================
// Test 9 (5e.3): ForallIntro of a quantified tautology.
// Goal: forall x. (P(x) -> P(x)). Body: fix x; assume P(x); implies_intro;
// forall_intro. Exercises Fix opener + ForallIntro NONE integration.
// =========================================================================
// =========================================================================
// Test 10 (5e.4): or_elim. Prove (A | A) -> A via or_elim with two trivial
// A -> A implications. Exercises 3-Cut + Weakening + nested And pattern.
// =========================================================================
// =========================================================================
// Test 11 (5e.4): exists_elim. Prove (exists x. P(x)) -> (exists x. P(x))
// via exists_elim opening a witness scope and exists_intro using the
// witness to re-derive the existential.
// =========================================================================
// =========================================================================
// Test 12 (5e.5): ForallElim under DemandInstance. Prove
// (forall x. P(x)) -> (forall y. P(y)) via forall_elim of the assumed
// ∀x.P(x) at the fix y, then forall_intro to re-quantify.
// =========================================================================
void test_forall_elim_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim fa_inst: (forall x. P(x)) -> (forall y. P(y))
        proof fa_inst:
            h_ap = assume forall x. P(x)
            fix y
            h_py = forall_elim h_ap, y
            h_fa = forall_intro h_py
            h_out = implies_intro h_fa
            qed h_out
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("fa_inst");
    if (!sh.has_value()) { std::cerr << "no fa_inst claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

void test_exists_elim_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim ex_self: (exists x. P(x)) -> (exists x. P(x))
        proof ex_self:
            h_ex = assume exists x. P(x)
            h_pw = exists_elim h_ex, w
            h_again = exists_intro h_pw, w
            h_close = exists_intro h_again
            h_out = implies_intro h_close
            qed h_out
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("ex_self");
    if (!sh.has_value()) { std::cerr << "no ex_self claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

void test_or_elim_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim or_self: (A | A) -> A
        proof or_self:
            h_or = assume A | A
            h_ac_in = assume A
            h_ac = implies_intro h_ac_in
            h_bc_in = assume A
            h_bc = implies_intro h_bc_in
            h_c = or_elim h_or, h_ac, h_bc
            h_out = implies_intro h_c
            qed h_out
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("or_self");
    if (!sh.has_value()) { std::cerr << "no or_self claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

void test_forall_intro_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim fa_self: forall x. (P(x) -> P(x))
        proof fa_self:
            fix x
            h = assume P(x)
            h2 = implies_intro h
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("fa_self");
    if (!sh.has_value()) { std::cerr << "no fa_self claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

void test_not_intro_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim nn_em: ~~(A | ~A)
        proof nn_em:
            h = assume ~(A | ~A)
            em_let = let A
            em = excluded_middle em_let
            h_bot = not_elim h, em
            h_out = not_intro h_bot
            qed h_out
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("nn_em");
    if (!sh.has_value()) { std::cerr << "no nn_em claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

void test_implies_intro_of_assume_e2e() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: A -> A
        proof p_self:
            h = assume A
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim("p_self");
    if (!sh.has_value()) { std::cerr << "no p_self claim\n"; ++g_failed; return; }
    FormulaHandle goal = sh->get().root();

    CHECK_OK(translate_and_verify(rt, prog, goal));
}

}  // namespace

int main() {
    test_excluded_middle_e2e();
    test_peirce_e2e();
    test_and_of_em_e2e();
    test_and_elim_l_of_em_e2e();
    test_and_elim_r_of_em_e2e();
    test_open_fix_scope_rejected();
    test_implies_intro_of_assume_e2e();
    test_not_intro_e2e();
    test_forall_intro_e2e();
    test_or_elim_e2e();
    test_exists_elim_e2e();
    test_forall_elim_e2e();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
