// NDtoLKR translator tests.
//
// Each test:
//   1. Constructs an ND program (in source form, lowered through the
//      runtime's existing ND pipeline)
//   2. Runs NDtoLKR::apply
//   3. Verifies the resulting LKR program against the same goal under
//      LKRVerifier
//
// This is the verify-roundtrip harness from the Phase 6 design: a bug
// in the translator surfaces as a verification failure on the output.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <iostream>
#include <string>

using namespace logic;
using namespace logic::proof;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_OK(expr) do { \
    auto _r = (expr); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Ok, got: " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_ERR(expr) do { \
    auto _r = (expr); \
    if (_r.is_error()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected error, got Ok at " \
                  << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

// =========================================================================
// Lower a ParsedProof to an NDProgram. Wrap the ND pipeline's lowering
// helper for tests.
// =========================================================================
Program<nd::Instr> lower_or_die(const ParsedProof& parsed) {
    auto r = nd::lower(parsed);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

// =========================================================================
// Use+Qed pattern: ND proof imports an axiom whose formula equals the
// claim. NDtoLKR translates to [UseTheorem(axiom)]. LKR verifies.
// =========================================================================
void test_use_qed_translates_and_verifies() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom self_impl_axiom: forall x. (P(x) -> P(x))
        claim self_impl_claim: forall x. (P(x) -> P(x))

        proof self_impl_claim:
            h = use self_impl_axiom
            qed h
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }

    // Lower the parsed proof to an ND IR program.
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { std::cerr << "no proofs parsed\n"; ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    // Resolve the claim.
    auto& ctx = rt.context();
    auto claim = ctx.find_claim("self_impl_claim");
    if (!claim.has_value()) { std::cerr << "claim not found\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    // Translate + verify under LKR.
    EXPECT_OK(translate::translate_and_verify(ctx, goal, nd_prog));
}

// =========================================================================
// Translator without a GlobalContext is rejected (Hughes' LKR translator
// always requires GlobalContext for axiom resolution + NNF state).
// =========================================================================
void test_no_ctx_rejected() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. P(x)
        claim p_at_eigen: forall x. P(x)

        proof p_at_eigen:
            fix x
            h = use all_p
            h2 = forall_elim h, x
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    translate::NDtoLKR translator_noctx;
    EXPECT_ERR(translator_noctx.apply(nd_prog));
}

// =========================================================================
// v2 SHOWCASE: full ND→LKR rewrite of a non-trivial proof.
//
// ND proof:
//   axiom all_p: forall x. P(x)
//   claim p_at_eigen: forall x. P(x)
//   proof p_at_eigen:
//     fix x
//     h  = use all_p              // F_h = ∀x. P(x)
//     h2 = forall_elim h, x       // F_h2 = P(x)         <-- target of qed-chain
//     h3 = forall_intro h2        // F_h3 = ∀x. P(x)
//     qed h3
//
// Expected LKR translation (Cut-based, with x → ForallR-introduced eigen):
//   ForallR(0)              # ⊢ ∀x. P(x)  →  ⊢ P(eigen)
//   Cut(∀x. P(x))           # left:  ⊢ ∀x. P(x)        right: ∀x. P(x) ⊢ P(eigen)
//     UseTheorem(all_p)     #   close left
//   Cut(P(eigen))           # left:  ∀x. P(x) ⊢ P(eigen)
//                           # right: ∀x. P(x), P(eigen) ⊢ P(eigen)
//     ForallL(0, eigen)     #   left becomes P(eigen) ⊢ P(eigen)
//     Axiom(0, 0)           #   close left
//   Axiom(1, 0)             # close right via the cut-in P(eigen)
// =========================================================================
void test_v2_full_translation_of_real_proof() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. P(x)
        claim p_at_eigen: forall x. P(x)

        proof p_at_eigen:
            fix x
            h = use all_p
            h2 = forall_elim h, x
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    auto& ctx = rt.context();
    auto claim = ctx.find_claim("p_at_eigen");
    if (!claim.has_value()) { std::cerr << "claim missing\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    // Translate (v2) and verify under LKR — full roundtrip.
    EXPECT_OK(translate::translate_and_verify(ctx, goal, nd_prog));
}

// =========================================================================
// v2: a slightly bigger proof exercising ImpliesElim too.
//
//   axiom all_p:  forall x. P(x)
//   axiom all_pq: forall x. (P(x) -> Q(x))
//   claim q_at_eigen: forall x. Q(x)
//   proof q_at_eigen:
//     fix x
//     h_p     = use all_p
//     h_p_x   = forall_elim h_p, x      // P(x)
//     h_pq    = use all_pq
//     h_pq_x  = forall_elim h_pq, x     // P(x) -> Q(x)
//     h_q_x   = implies_elim h_pq_x, h_p_x   // Q(x)
//     h_q     = forall_intro h_q_x      // ∀x. Q(x)
//     qed h_q
// =========================================================================
void test_v2_modus_ponens_chain() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p:  forall x. P(x)
        axiom all_pq: forall x. (P(x) -> Q(x))
        claim q_at_eigen: forall x. Q(x)

        proof q_at_eigen:
            fix x
            h_p    = use all_p
            h_p_x  = forall_elim h_p, x
            h_pq   = use all_pq
            h_pq_x = forall_elim h_pq, x
            h_q_x  = implies_elim h_pq_x, h_p_x
            h_q    = forall_intro h_q_x
            qed h_q
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    auto& ctx = rt.context();
    auto claim = ctx.find_claim("q_at_eigen");
    if (!claim.has_value()) { ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    EXPECT_OK(translate::translate_and_verify(ctx, goal, nd_prog));
}

// =========================================================================
// Translator produces a valid LKR program shape for use+qed: cut spine
// emits Cut + UseTheorem + AxiomGen for a 0-Fix, 0-Assume claim.
// =========================================================================
void test_translator_output_shape() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom my_ax: forall x. (P(x) | ~P(x))
        claim my_claim: forall x. (P(x) | ~P(x))

        proof my_claim:
            h = use my_ax
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    translate::NDtoLKR translator(rt.context());
    auto out = translator.apply(nd_prog);
    if (!out.ok()) { std::cerr << out.error().to_string() << "\n"; ++g_failed; return; }
    auto& lkr_prog = out.value();

    if (lkr_prog.claim_name != "my_claim") {
        std::cerr << "claim_name mismatch\n"; ++g_failed; return;
    }
    // Expected: Cut(my_ax_nnf), UseTheorem(my_ax), AxiomGen(0,1).
    if (lkr_prog.instrs.size() != 3) {
        std::cerr << "expected 3 LKR instrs, got " << lkr_prog.instrs.size() << "\n";
        ++g_failed; return;
    }
    if (!std::holds_alternative<lkr::Cut>(lkr_prog.instrs[0])) {
        std::cerr << "instr 0 not Cut\n"; ++g_failed; return;
    }
    const auto* ut = std::get_if<lkr::UseTheorem>(&lkr_prog.instrs[1]);
    if (!ut || ut->axiom.name != "my_ax") {
        std::cerr << "instr 1 not UseTheorem(my_ax)\n"; ++g_failed; return;
    }
    if (!std::holds_alternative<lkr::AxiomGen>(lkr_prog.instrs[2])) {
        std::cerr << "instr 2 not AxiomGen\n"; ++g_failed; return;
    }
    ++g_passed;
}

}  // namespace

// =========================================================================
// v2 SHOWCASE 3: outer assume pattern — a transitive-implication proof.
//
//   axiom all_pq: forall x. (P(x) -> Q(x))
//   axiom all_qr: forall x. (Q(x) -> R(x))
//   claim chain:  forall x. (P(x) -> R(x))
//
//   proof chain:
//     fix x                                 // outer Fix
//     h_assume = assume P(x)                // outer Assume
//     h_pq    = use all_pq                  // body: Use
//     h_pq_x  = forall_elim h_pq, x         // body: ForallElim → P(x) → Q(x)
//     h_q     = implies_elim h_pq_x, h_assume  // body: ImpliesElim → Q(x)
//     h_qr    = use all_qr                  // body: Use
//     h_qr_x  = forall_elim h_qr, x         // body: ForallElim → Q(x) → R(x)
//     h_r     = implies_elim h_qr_x, h_q    // body: ImpliesElim → R(x)
//     h_impl  = implies_intro h_r           // outer ImpliesIntro: P(x) → R(x)
//     h_all   = forall_intro h_impl         // outer ForallIntro
//     qed h_all
//
// This exercises the full outer pattern Fix*/Assume*/body/ImpliesIntro*/
// ForallIntro*/Qed and a non-trivial body chain (modus-ponens twice).
// =========================================================================
void test_v2_transitive_implication() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_pq: forall x. (P(x) -> Q(x))
        axiom all_qr: forall x. (Q(x) -> R(x))
        claim chain: forall x. (P(x) -> R(x))

        proof chain:
            fix x
            h_assume = assume P(x)
            h_pq = use all_pq
            h_pq_x = forall_elim h_pq, x
            h_q = implies_elim h_pq_x, h_assume
            h_qr = use all_qr
            h_qr_x = forall_elim h_qr, x
            h_r = implies_elim h_qr_x, h_q
            h_impl = implies_intro h_r
            h_all = forall_intro h_impl
            qed h_all
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }
    auto& proofs = parsed.value().proofs;
    if (proofs.empty()) { ++g_failed; return; }
    Program<nd::Instr> nd_prog = lower_or_die(proofs[0]);

    auto& ctx = rt.context();
    auto claim = ctx.find_claim("chain");
    if (!claim.has_value()) { ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    // Full ND→LKR roundtrip.
    EXPECT_OK(translate::translate_and_verify(ctx, goal, nd_prog));
}

int main() {
    test_use_qed_translates_and_verifies();
    test_no_ctx_rejected();
    test_translator_output_shape();
    test_v2_full_translation_of_real_proof();
    test_v2_modus_ponens_chain();
    test_v2_transitive_implication();
    std::cout << "nd_to_lkr_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
