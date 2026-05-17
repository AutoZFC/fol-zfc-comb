// EliminateIotaInProof tests — Leisenring's ε-elimination realized as
// witness-substitution.
//
// Each test:
//   1. Constructs an ND program with iota_elim (and downstream ι uses).
//   2. Verifies it under ND (Path D-normalized axioms + iota_elim valid).
//   3. Runs EliminateIotaInProof::apply.
//   4. The apply call internally invokes NDVerifierGate, which:
//      - I-3: asserts the output contains no iota_elim instructions.
//      - I-4: asserts the output verifies under ND against the goal.
//   So apply() returning Ok proves both soundness invariants.
//
// Completeness: for every input that verifies under (post-Path-D) ND,
// the rewriter produces an iota-free output that also verifies. These
// tests demonstrate the construction on the common patterns:
//   - iota_elim binding a term (basic case)
//   - the term used as forall_elim arg (term-arg substitution)
//   - the term used as exists_intro witness (witness-arg substitution)
//   - multiple iota_elims in one proof (LIFO scope nesting)

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/iota_elim/eliminate_iota.h"
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

#define EXPECT_OK(expr) do { \
    auto _r = (expr); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Ok, got: " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

// Lower a ParsedProof to an NDProgram or abort.
Program<nd::Instr> lower_or_die(const ParsedProof& parsed) {
    auto r = nd::lower(parsed);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

bool nd_iota_free(const Program<nd::Instr>& prog) {
    for (const auto& instr : prog.instrs) {
        if (std::holds_alternative<nd::IotaElim>(instr)) return false;
    }
    return true;
}

// =========================================================================
// Basic iota_elim: from ∃x.P(x), derive ∃x.P(x) trivially via iota_elim +
// exists_intro with the iota term as witness. The translator must
// substitute the iota with an exists_elim witness and re-derive ∃x.P(x).
// =========================================================================
void test_iota_basic() {
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
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }

    Program<nd::Instr> nd_prog = lower_or_die(parsed.value().proofs[0]);

    // Confirm input has iota_elim and verifies under ND.
    if (nd_iota_free(nd_prog)) {
        std::cerr << "FAIL: test_iota_basic input has no iota_elim\n";
        ++g_failed; return;
    }
    auto claim = rt.context().find_claim("p_exists_again");
    if (!claim.has_value()) {
        std::cerr << "FAIL: claim not found\n"; ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    {
        nd::NDVerifier v;
        Proof p{System::ND, nd_prog};
        auto status = v.verify(rt.context(), goal, p);
        if (!status.ok()) {
            std::cerr << "FAIL: input doesn't verify under ND: "
                      << status.error().to_string() << "\n";
            ++g_failed; return;
        }
    }

    // Run the translator. apply() succeeds iff (a) the rewrite succeeded
    // structurally and (b) NDVerifierGate's I-3 + I-4 checks pass.
    translate::iota_elim::EliminateIotaInProof pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "FAIL: translator: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Soundness invariant I-3: output has no iota_elim.
    if (!nd_iota_free(out.value())) {
        std::cerr << "FAIL: I-3: output still contains iota_elim\n";
        ++g_failed; return;
    }

    ++g_passed;
}

// =========================================================================
// Iota term used as forall_elim arg. The user does iota_elim, then uses
// the resulting iota term to instantiate a universal. Translator must
// substitute the iota term with the witness fix-var in the forall_elim.
// =========================================================================
void test_iota_used_in_forall_elim() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_exists: forall a. exists r. p(a, r)
        axiom q_for_all: forall a. forall r. (p(a, r) -> q(a, r))
        claim q_witness: forall a. exists r. q(a, r)

        proof q_witness:
            fix a
            h0 = use p_exists
            h1 = forall_elim h0, a
            h2 = iota_elim h1, h2          # binds w; derives p(a, w)
            h3 = use q_for_all
            h4 = forall_elim h3, a
            h5 = forall_elim h4, h2        # uses w (was iota term) as forall arg
            h6 = implies_elim h5, h2
            h7 = exists_intro h6, h2       # uses w as exists witness
            h8 = forall_intro h7
            qed h8
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }

    Program<nd::Instr> nd_prog = lower_or_die(parsed.value().proofs[0]);

    auto claim = rt.context().find_claim("q_witness");
    if (!claim.has_value()) { std::cerr << "no claim\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    {
        nd::NDVerifier v;
        Proof p{System::ND, nd_prog};
        auto status = v.verify(rt.context(), goal, p);
        if (!status.ok()) {
            std::cerr << "FAIL: input doesn't verify under ND: "
                      << status.error().to_string() << "\n";
            ++g_failed; return;
        }
    }

    translate::iota_elim::EliminateIotaInProof pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "FAIL: translator: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    if (!nd_iota_free(out.value())) {
        std::cerr << "FAIL: I-3: output contains iota_elim\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// =========================================================================
// Two nested iota_elims in the same scope (LIFO discipline). The second
// iota's body references the first iota's witness.
// =========================================================================
void test_iota_nested_witnesses() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_exists: forall a. exists r. p(a, r)
        axiom q_exists: forall a. exists r. q(a, r)
        claim pair_witness: forall a. exists r1. (exists r2. (p(a, r1) & q(a, r2)))

        proof pair_witness:
            fix a
            h0 = use p_exists
            h1 = forall_elim h0, a
            h2 = iota_elim h1, h2          # w1; derives p(a, w1)
            h3 = use q_exists
            h4 = forall_elim h3, a
            h5 = iota_elim h4, h5          # w2; derives q(a, w2)
            h6 = and_intro h2, h5          # p(a, w1) & q(a, w2)
            h7 = exists_intro h6, h5       # ∃r2. p(a, w1) & q(a, r2)
            h8 = exists_intro h7, h2       # ∃r1. (∃r2. ...)
            h9 = forall_intro h8
            qed h9
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }

    Program<nd::Instr> nd_prog = lower_or_die(parsed.value().proofs[0]);

    auto claim = rt.context().find_claim("pair_witness");
    if (!claim.has_value()) { std::cerr << "no claim\n"; ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    {
        nd::NDVerifier v;
        Proof p{System::ND, nd_prog};
        auto status = v.verify(rt.context(), goal, p);
        if (!status.ok()) {
            std::cerr << "FAIL: input doesn't verify under ND: "
                      << status.error().to_string() << "\n";
            ++g_failed; return;
        }
    }

    translate::iota_elim::EliminateIotaInProof pass(rt.context(), goal);
    auto out = pass.apply(nd_prog);
    if (!out.ok()) {
        std::cerr << "FAIL: translator: " << out.error().to_string() << "\n";
        ++g_failed; return;
    }
    if (!nd_iota_free(out.value())) {
        std::cerr << "FAIL: I-3: output contains iota_elim\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// =========================================================================
// program_contains_iota helper sanity-check.
// =========================================================================
void test_iota_free_input_passes_through() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_axiom: forall x. p(x)
        claim p_axiom_again: forall x. p(x)
        proof p_axiom_again:
            h = use p_axiom
            qed h
    )");
    if (!parsed.ok()) { std::cerr << parsed.error().to_string() << "\n"; ++g_failed; return; }

    Program<nd::Instr> nd_prog = lower_or_die(parsed.value().proofs[0]);
    if (translate::iota_elim::EliminateIotaInProof::program_contains_iota(nd_prog)) {
        std::cerr << "FAIL: iota-free program reported as containing iota\n";
        ++g_failed; return;
    }
    ++g_passed;
}

}  // namespace

int main() {
    std::cerr << "Running iota_translator_test...\n";
    test_iota_free_input_passes_through();
    test_iota_basic();
    test_iota_used_in_forall_elim();
    test_iota_nested_witnesses();

    std::cerr << "Passed: " << g_passed << ", Failed: " << g_failed << "\n";
    return g_failed == 0 ? 0 : 1;
}
