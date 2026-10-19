// NDtoLKR tests — translator phases brought up one at a time.
//
// Phase 1 (skeleton + gates): exercises the InputGate's three rejection
// modes (I-1 iota, I-2 eq_sym, I-3 non-ND-verify) plus the
// gate-passes-then-stub-error path that confirms the body's call point.
//
// Phase 2 (block tree): exercises decompose_blocks on each block kind and
// on nested structures.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/iota_elim/eliminate_iota.h"
#include "src/proof/translate/nd_to_lkr/block_tree.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <string>
#include <variant>

using namespace logic;
using namespace logic::proof;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_ERROR_CONTAINING(expr, substr) do {                          \
    auto _r = (expr);                                                        \
    if (_r.ok()) {                                                           \
        std::cerr << "FAIL: " #expr " expected Error, got Ok at "             \
                  << __FILE__ << ":" << __LINE__ << "\n";                    \
        ++g_failed;                                                          \
    } else if (_r.error().to_string().find(substr) == std::string::npos) {   \
        std::cerr << "FAIL: " #expr " error didn't contain '" << substr      \
                  << "': " << _r.error().to_string()                         \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n";          \
        ++g_failed;                                                          \
    } else {                                                                 \
        ++g_passed;                                                          \
    }                                                                        \
} while (0)

Program<nd::Instr> lower_or_die(const ParsedProof& parsed, const GlobalContext& ctx) {
    auto r = nd::lower(parsed, ctx);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

// -------------------------------------------------------------------------
// I-1: iota_elim in input is rejected with a pointer to EliminateIotaInProof.
// -------------------------------------------------------------------------
void test_gate_rejects_iota() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_exists: forall a. exists r. p(a, r)
        claim p_exists_again: forall a. exists r. p(a, r)

        proof p_exists_again:
            fix a
            h_axiom = use p_exists
            h1 = forall_elim h_axiom, a
            h2 = iota_elim h1, h2
            h3 = exists_intro h2, h2
            h4 = forall_intro h3
            qed h4
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("p_exists_again");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    EXPECT_ERROR_CONTAINING(pass.apply(nd_prog), "I-1 violation");
}

// -------------------------------------------------------------------------
// I-2: eq_sym in input is rejected.
// -------------------------------------------------------------------------
void test_gate_rejects_eq_sym() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim eq_app: forall a. forall b. (eq(a, b) -> eq(b, a))

        proof eq_app:
            fix a
            fix b
            h_eq = assume eq(a, b)
            h_ba = eq_sym h_eq
            h_impl = implies_intro h_ba
            h1 = forall_intro h_impl
            h2 = forall_intro h1
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("eq_app");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    EXPECT_ERROR_CONTAINING(pass.apply(nd_prog), "I-2 violation");
}

// -------------------------------------------------------------------------
// I-3: non-ND-verifying input is rejected.
//
// We construct a syntactically valid but semantically broken ND program:
// a Qed pointing to a step whose derived formula is NOT the claim. The
// lowerer accepts it (no static check); the verifier rejects.
// -------------------------------------------------------------------------
void test_gate_rejects_non_verifying() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom px: forall x. p(x)
        axiom qx: forall x. q(x)
        claim qx_claim: forall x. q(x)

        proof qx_claim:
            h = use px
            qed h
    )");
    // Lowering and parsing succeed; ND verification fails because
    // p(x) is not the claim's formula q(x).
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("qx_claim");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    EXPECT_ERROR_CONTAINING(pass.apply(nd_prog), "I-3 violation");
}

// -------------------------------------------------------------------------
// End-to-end: prove a claim by Use of the matching axiom. Smallest
// non-trivial flat-step rule. Exercises: input gate → trace → block tree
// → cut-spine driver → close_use → emit_close (Forall+Exists+AxiomLit) →
// output gate. The OutputGate runs LKRVerifier on the emitted program;
// success means LKR accepts the proof, which is the soundness witness.
// -------------------------------------------------------------------------
#define EXPECT_OK(expr) do {                                                 \
    auto _r = (expr);                                                         \
    if (!_r.ok()) {                                                           \
        std::cerr << "FAIL: " #expr " expected Ok, got: "                     \
                  << _r.error().to_string()                                   \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n";           \
        ++g_failed;                                                           \
    } else { ++g_passed; }                                                    \
} while (0)

// Helper: load + translate + assert OK.
void run_e2e(const char* src, const char* claim_name) {
    Runtime rt;
    auto parsed = rt.load_with_proofs(src);
    if (!parsed.ok()) {
        std::cerr << "load (" << claim_name << "): "
                  << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim(claim_name);
    if (!claim.has_value()) {
        std::cerr << "claim not found: " << claim_name << "\n";
        ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();
    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "translator (" << claim_name << "): "
                  << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

void test_e2e_and_intro() {
    run_e2e(R"(
        axiom all_p: forall x. p(x)
        axiom all_q: forall x. q(x)
        claim all_pq: forall x. (p(x) & q(x))

        proof all_pq:
            fix x
            h_p_ax = use all_p
            h_p = forall_elim h_p_ax, x
            h_q_ax = use all_q
            h_q = forall_elim h_q_ax, x
            h_pq = and_intro h_p, h_q
            h_fa = forall_intro h_pq
            qed h_fa
    )", "all_pq");
}

void test_e2e_and_elim_l() {
    run_e2e(R"(
        axiom all_pq: forall x. (p(x) & q(x))
        claim all_p: forall x. p(x)

        proof all_p:
            fix x
            h_ax = use all_pq
            h_pq = forall_elim h_ax, x
            h_p = and_elim_l h_pq
            h_fa = forall_intro h_p
            qed h_fa
    )", "all_p");
}

void test_e2e_and_elim_r() {
    run_e2e(R"(
        axiom all_pq: forall x. (p(x) & q(x))
        claim all_q: forall x. q(x)

        proof all_q:
            fix x
            h_ax = use all_pq
            h_pq = forall_elim h_ax, x
            h_q = and_elim_r h_pq
            h_fa = forall_intro h_q
            qed h_fa
    )", "all_q");
}

void test_e2e_or_intro_l() {
    run_e2e(R"(
        axiom all_p: forall x. p(x)
        claim all_p_or_q: forall x. (p(x) | q(x))

        proof all_p_or_q:
            fix x
            h_ax = use all_p
            h_p = forall_elim h_ax, x
            h_qf = let q(x)
            h_disj = or_intro_l h_p, h_qf
            h_fa = forall_intro h_disj
            qed h_fa
    )", "all_p_or_q");
}

// IffIntro: prove ∀x. (p(x) ↔ q(x)) from two implication axioms.
void test_e2e_iff_intro() {
    run_e2e(R"(
        axiom all_p_q: forall x. (p(x) -> q(x))
        axiom all_q_p: forall x. (q(x) -> p(x))
        claim all_iff: forall x. (p(x) <-> q(x))

        proof all_iff:
            fix x
            h_pq_ax = use all_p_q
            h_pq = forall_elim h_pq_ax, x
            h_qp_ax = use all_q_p
            h_qp = forall_elim h_qp_ax, x
            h_iff = iff_intro h_pq, h_qp
            h_fa = forall_intro h_iff
            qed h_fa
    )", "all_iff");
}

// IffElim_l: from A↔B and A, derive B.
void test_e2e_iff_elim_l() {
    run_e2e(R"(
        axiom all_iff: forall x. (p(x) <-> q(x))
        axiom all_p: forall x. p(x)
        claim all_q: forall x. q(x)

        proof all_q:
            fix x
            h_iff_ax = use all_iff
            h_iff = forall_elim h_iff_ax, x
            h_p_ax = use all_p
            h_p = forall_elim h_p_ax, x
            h_q = iff_elim_l h_iff, h_p
            h_fa = forall_intro h_q
            qed h_fa
    )", "all_q");
}

// IffElim_r: from A↔B and B, derive A. (Uses the SECOND clause of NNF(¬iff).)
// Integration: iota_elim → nd_to_lkr → LKRVerifier. Demonstrates the
// composition Q1=(i): the caller pipes EliminateIotaInProof's output into
// NDtoLKR. The iota_elim pass rewrites the iota into an exists_elim
// scope; NDtoLKR then handles the iota-free output normally.
void test_integration_iota_pipeline() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_exists: forall a. exists r. p(a, r)
        claim p_exists_again: forall a. exists r. p(a, r)

        proof p_exists_again:
            fix a
            h_axiom = use p_exists
            h1 = forall_elim h_axiom, a
            h2 = iota_elim h1, h2
            h3 = exists_intro h2, h2
            h4 = forall_intro h3
            qed h4
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("p_exists_again");
    if (!claim.has_value()) {
        std::cerr << "claim not found\n"; ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    // Step 1: iota_elim pre-pass.
    translate::iota_elim::EliminateIotaInProof iota_pass(rt.context(), goal);
    auto iota_free = iota_pass.apply(nd_prog);
    if (!iota_free.ok()) {
        std::cerr << "iota_elim: " << iota_free.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Step 2: NDtoLKR on the iota-free output.
    translate::nd_to_lkr::NDtoLKR nd_to_lkr_pass(rt.context(), goal);
    auto lkr_out = nd_to_lkr_pass.apply(iota_free.value());
    if (!lkr_out.ok()) {
        std::cerr << "nd_to_lkr: " << lkr_out.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// EXISTS_ELIM block: derive ∃x.p(x) from ∃x.p(x) trivially through
// exists_elim + exists_intro (witness from elim) + scope-closing exists_intro.
void test_e2e_exists_elim_block() {
    run_e2e(R"(
        axiom ex_p: exists x. p(x)
        claim ex_p_again: exists x. p(x)

        proof ex_p_again:
            h_ax = use ex_p
            h_ee = exists_elim h_ax, w
            h_pw = exists_intro h_ee, w
            h_close = exists_intro h_pw
            qed h_close
    )", "ex_p_again");
}

// ClassicalAbsurd: classical reductio ad absurdum.
// Goal: ¬¬p → p. ND proof: assume p's double-negation; assume ¬p; derive ⊥;
// classical_absurd closes the assumption-of-¬p scope, deriving p; then
// implies_intro discharges the ¬¬p assumption.
void test_e2e_classical_absurd() {
    run_e2e(R"(
        claim dne_via_ca: ~~p -> p

        proof dne_via_ca:
            hnnp = assume ~~p
            hnp = assume ~p
            hbot = not_elim hnnp, hnp
            hp = classical_absurd hbot
            himpl = implies_intro hp
            qed himpl
    )", "dne_via_ca");
}

// Peirce: classical ((A → B) → A) → A as a built-in ND rule.
// Uses two let-defined formulas for A and B. Tests close_peirce
// (ND_TO_LKR_DESIGN.md §4.7): Cut(A) + Or + And + emit_close pattern.
void test_e2e_peirce() {
    run_e2e(R"(
        claim peirce_law: ((p -> q) -> p) -> p

        proof peirce_law:
            ha = let p
            hb = let q
            hpe = peirce ha, hb
            qed hpe
    )", "peirce_law");
}

// ExcludedMiddle: classical p ∨ ¬p as a built-in axiom.
void test_e2e_excluded_middle() {
    run_e2e(R"(
        claim em: forall x. (p(x) | ~p(x))

        proof em:
            fix x
            h_let = let p(x)
            h_em = excluded_middle h_let
            h_fa = forall_intro h_em
            qed h_fa
    )", "em");
}

// OrElim: case analysis. If we have A ∨ B and both A → C and B → C, conclude C.
void test_e2e_or_elim() {
    run_e2e(R"(
        axiom all_or: forall x. (p(x) | q(x))
        axiom all_p_r: forall x. (p(x) -> r(x))
        axiom all_q_r: forall x. (q(x) -> r(x))
        claim all_r: forall x. r(x)

        proof all_r:
            fix x
            h_or_ax = use all_or
            h_or = forall_elim h_or_ax, x
            h_pr_ax = use all_p_r
            h_pr = forall_elim h_pr_ax, x
            h_qr_ax = use all_q_r
            h_qr = forall_elim h_qr_ax, x
            h_r = or_elim h_or, h_pr, h_qr
            h_fa = forall_intro h_r
            qed h_fa
    )", "all_r");
}

// NOT block: prove ¬¬p(x) by contradicting ¬p(x) with the all_p axiom.
void test_e2e_not_block() {
    run_e2e(R"(
        axiom all_p: forall x. p(x)
        claim not_not_p: forall x. ~~p(x)

        proof not_not_p:
            fix x
            h_neg = assume ~p(x)
            h_ax = use all_p
            h_p = forall_elim h_ax, x
            h_bot = not_elim h_neg, h_p
            h_nn = not_intro h_bot
            h_fa = forall_intro h_nn
            qed h_fa
    )", "not_not_p");
}

// BottomElim: ex falso quodlibet — from ⊥, derive anything.
void test_e2e_bottom_elim() {
    run_e2e(R"(
        axiom all_p: forall x. p(x)
        claim explosion: forall x. (~p(x) -> q(x))

        proof explosion:
            fix x
            h_neg = assume ~p(x)
            h_ax = use all_p
            h_p = forall_elim h_ax, x
            h_bot = not_elim h_neg, h_p
            h_qf = let q(x)
            h_q = bottom_elim h_bot, h_qf
            h_impl = implies_intro h_q
            h_fa = forall_intro h_impl
            qed h_fa
    )", "explosion");
}

void test_e2e_iff_elim_r() {
    run_e2e(R"(
        axiom all_iff: forall x. (p(x) <-> q(x))
        axiom all_q: forall x. q(x)
        claim all_p: forall x. p(x)

        proof all_p:
            fix x
            h_iff_ax = use all_iff
            h_iff = forall_elim h_iff_ax, x
            h_q_ax = use all_q
            h_q = forall_elim h_q_ax, x
            h_p = iff_elim_r h_iff, h_q
            h_fa = forall_intro h_p
            qed h_fa
    )", "all_p");
}

void test_e2e_implies_elim() {
    run_e2e(R"(
        axiom all_p: forall x. p(x)
        axiom all_p_q: forall x. (p(x) -> q(x))
        claim all_q: forall x. q(x)

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
}

// End-to-end: FORALL block via fix + forall_elim + forall_intro.
// Exercises the cut-spine treatment of a sub-block + var alignment between
// trace and emit.
void test_e2e_forall_block() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim all_p_again: forall x. p(x)

        proof all_p_again:
            fix x
            h_ax = use all_p
            h_px = forall_elim h_ax, x
            h_fa = forall_intro h_px
            qed h_fa
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("all_p_again");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "translator: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// End-to-end: IMPLIES block via assume + implies_intro.
void test_e2e_implies_block() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim impl_self: forall x. (p(x) -> p(x))

        proof impl_self:
            fix x
            h_ass = assume p(x)
            h_impl = implies_intro h_ass
            h_fa = forall_intro h_impl
            qed h_fa
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("impl_self");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "translator: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

void test_e2e_use_axiom() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim all_p_claim: forall x. p(x)

        proof all_p_claim:
            h = use all_p
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("all_p_claim");
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    EXPECT_OK(pass.apply(nd_prog));
}

// =========================================================================
// Phase 2: block tree
// =========================================================================

using namespace logic::proof::translate::nd_to_lkr;

#define EXPECT_TRUE(cond) do {                                               \
    if (!(cond)) {                                                            \
        std::cerr << "FAIL: " #cond " at " << __FILE__ << ":" << __LINE__     \
                  << "\n";                                                    \
        ++g_failed;                                                           \
    } else { ++g_passed; }                                                    \
} while (0)

#define EXPECT_EQ(a, b) do {                                                  \
    auto _av = (a); auto _bv = (b);                                           \
    if (_av != _bv) {                                                         \
        std::cerr << "FAIL: " #a " (" << _av << ") != " #b " (" << _bv        \
                  << ") at " << __FILE__ << ":" << __LINE__ << "\n";          \
        ++g_failed;                                                           \
    } else { ++g_passed; }                                                    \
} while (0)

const Block* as_block(const BodyItem& item) {
    auto* p = std::get_if<std::unique_ptr<Block>>(&item);
    return p ? p->get() : nullptr;
}

const FlatStep* as_flat(const BodyItem& item) {
    return std::get_if<FlatStep>(&item);
}

// Build the simplest valid OUTER block: a single Use + Qed.
void test_block_outer_only() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim all_p_claim: forall x. p(x)

        proof all_p_claim:
            h = use all_p
            qed h
    )");
    EXPECT_TRUE(parsed.ok());
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.ok());
    if (!root_r.ok()) return;
    auto& root = *root_r.value();

    EXPECT_TRUE(root.kind == BlockKind::OUTER);
    EXPECT_EQ(root.opener_idx, kInvalidIdx);
    // body has one item: the FlatStep for `h = use all_p`. Qed is the closer,
    // not a body item.
    EXPECT_EQ(static_cast<int>(root.body.size()), 1);
    EXPECT_TRUE(as_flat(root.body[0]) != nullptr);
}

// FORALL block: fix + use + forall_intro + qed.
void test_block_forall() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim all_p_claim: forall x. p(x)

        proof all_p_claim:
            fix x
            h_axiom = use all_p
            h = forall_elim h_axiom, x
            h2 = forall_intro h
            qed h2
    )");
    EXPECT_TRUE(parsed.ok());
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.ok());
    if (!root_r.ok()) return;
    auto& root = *root_r.value();

    EXPECT_TRUE(root.kind == BlockKind::OUTER);
    // body has one sub-block (the FORALL) — the inner FlatSteps belong to it.
    EXPECT_EQ(static_cast<int>(root.body.size()), 1);
    auto* inner = as_block(root.body[0]);
    EXPECT_TRUE(inner != nullptr);
    if (!inner) return;
    EXPECT_TRUE(inner->kind == BlockKind::FORALL);
    // Inner body: h_axiom and h (the forall_elim). forall_intro is the closer.
    EXPECT_EQ(static_cast<int>(inner->body.size()), 2);
    EXPECT_TRUE(as_flat(inner->body[0]) != nullptr);
    EXPECT_TRUE(as_flat(inner->body[1]) != nullptr);
}

// IMPLIES block: assume + ... + implies_intro.
void test_block_implies() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim impl_self: forall x. (p(x) -> p(x))

        proof impl_self:
            fix x
            h_assume = assume p(x)
            h_impl = implies_intro h_assume
            h_fa = forall_intro h_impl
            qed h_fa
    )");
    EXPECT_TRUE(parsed.ok());
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.ok());
    if (!root_r.ok()) return;
    auto& root = *root_r.value();

    EXPECT_EQ(static_cast<int>(root.body.size()), 1);
    auto* forall_blk = as_block(root.body[0]);
    EXPECT_TRUE(forall_blk != nullptr);
    if (!forall_blk) return;
    EXPECT_TRUE(forall_blk->kind == BlockKind::FORALL);
    EXPECT_EQ(static_cast<int>(forall_blk->body.size()), 1);
    auto* impl_blk = as_block(forall_blk->body[0]);
    EXPECT_TRUE(impl_blk != nullptr);
    if (!impl_blk) return;
    EXPECT_TRUE(impl_blk->kind == BlockKind::IMPLIES);
    // body inside IMPLIES is empty — assume IS the opener (not in body).
    EXPECT_EQ(static_cast<int>(impl_blk->body.size()), 0);
}

// NOT block: assume + not_elim + not_intro.
void test_block_not() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim not_not_p: forall x. ~~p(x)

        proof not_not_p:
            fix x
            h_neg = assume ~p(x)
            h_axiom = use all_p
            h_px = forall_elim h_axiom, x
            h_bot = not_elim h_neg, h_px
            h_not_not = not_intro h_bot
            h_fa = forall_intro h_not_not
            qed h_fa
    )");
    EXPECT_TRUE(parsed.ok());
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.ok());
    if (!root_r.ok()) return;
    auto& root = *root_r.value();

    auto* fa = as_block(root.body[0]);
    EXPECT_TRUE(fa && fa->kind == BlockKind::FORALL);
    if (!fa) return;
    auto* nb = as_block(fa->body[0]);
    EXPECT_TRUE(nb && nb->kind == BlockKind::NOT_);
    if (!nb) return;
    // body: h_axiom, h_px, h_bot (3 flat steps); not_intro is closer.
    EXPECT_EQ(static_cast<int>(nb->body.size()), 3);
}

// EXISTS_ELIM block: exists_elim + body + exists_intro (no witness).
void test_block_exists_elim() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom ex_p: exists x. p(x)
        claim ex_p_claim: exists x. p(x)

        proof ex_p_claim:
            h_ax = use ex_p
            h_ee = exists_elim h_ax, w
            h_pw = exists_intro h_ee, w
            h_close = exists_intro h_pw
            qed h_close
    )");
    EXPECT_TRUE(parsed.ok());
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.ok());
    if (!root_r.ok()) return;
    auto& root = *root_r.value();

    // body: h_ax (FlatStep), then EXISTS_ELIM block. Closing exists_intro
    // is the closer of that block.
    EXPECT_EQ(static_cast<int>(root.body.size()), 2);
    EXPECT_TRUE(as_flat(root.body[0]) != nullptr);
    auto* ee = as_block(root.body[1]);
    EXPECT_TRUE(ee != nullptr);
    if (!ee) return;
    EXPECT_TRUE(ee->kind == BlockKind::EXISTS_ELIM);
    // body inside: h_pw (FlatStep). exists_elim opens, exists_intro closes.
    EXPECT_EQ(static_cast<int>(ee->body.size()), 1);
}

// Missing Qed.
void test_block_rejects_no_qed() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim all_p_claim: forall x. p(x)

        proof all_p_claim:
            h = use all_p
            qed h
    )");
    auto nd_prog = lower_or_die(parsed.value().proofs[0], rt.context());
    // Strip the qed.
    nd_prog.instrs.pop_back();
    auto root_r = decompose_blocks(nd_prog);
    EXPECT_TRUE(root_r.is_error());
    if (root_r.is_error()) {
        EXPECT_TRUE(root_r.error().to_string().find("no Qed") != std::string::npos);
    }
}

}  // namespace

int main() {
    test_gate_rejects_iota();
    test_gate_rejects_eq_sym();
    test_gate_rejects_non_verifying();
    test_e2e_use_axiom();
    test_e2e_forall_block();
    test_e2e_implies_block();
    test_e2e_and_intro();
    test_e2e_and_elim_l();
    test_e2e_and_elim_r();
    test_e2e_or_intro_l();
    test_e2e_implies_elim();
    test_e2e_iff_intro();
    test_e2e_iff_elim_l();
    test_e2e_iff_elim_r();
    test_e2e_not_block();
    test_e2e_bottom_elim();
    test_e2e_classical_absurd();
    test_e2e_peirce();
    test_e2e_excluded_middle();
    test_e2e_or_elim();
    test_e2e_exists_elim_block();
    test_integration_iota_pipeline();

    test_block_outer_only();
    test_block_forall();
    test_block_implies();
    test_block_not();
    test_block_exists_elim();
    test_block_rejects_no_qed();

    std::cout << "nd_to_lkr_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
