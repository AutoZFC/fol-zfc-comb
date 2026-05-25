// Stage 2 Phase 6 tests: demand propagation through combining elims.
//
// Spec: src/proof/translate/nd_to_lkr/DEMAND_THROUGH_COMBINING.md
//
// Each test exercises a combining-elim (implies_elim, iff_elim_l/r,
// or_elim) under a non-trivial DemandPath promoted by a downstream
// projection elim (forall_elim → DemandInstance, and_elim_l/r →
// DemandAnd{Left,Right}).
//
// Construction pattern (for INSTANCE cases):
//
//   forall z. ⟨wrap⟩         (outer forall_intro pre-substitutes target_pos)
//     → assume premises
//     → COMBINING_ELIM ⊢ ∀y. φ(y, z)
//     → forall_elim z          (promotes DemandInstance(z))
//     → implies_intro chain
//     → forall_intro
//
// At ImpliesElim/IffElim/OrElim dispatch, target_pos's content is
// NNF(φ(?, z)) (atomic after pre-substitution by the outer Forall);
// the emitter's psi-side carries the un-instantiated NNF(¬∀y.φ) =
// ∃y.¬φ. The fix (apply_path_and_close on psi-vs-target with
// norm_path) closes the gap.
//
// LKRVerifier acceptance is the soundness witness. All tests should
// be RED before the fix lands and GREEN after.

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
#include "src/proof/translate/nd_to_lkr/block_tree.h"
#include "src/proof/translate/nd_to_lkr/demand.h"
#include "src/proof/translate/nd_to_lkr/dispatcher.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::DemandPath;
using logic::proof::translate::nd_to_lkr::SequentShadow;
using logic::proof::translate::nd_to_lkr::decompose_blocks;
using logic::proof::translate::nd_to_lkr::dispatcher::CloserToOpener;
using logic::proof::translate::nd_to_lkr::dispatcher::Ctx;
using logic::proof::translate::nd_to_lkr::dispatcher::build_closer_to_opener;
using logic::proof::translate::nd_to_lkr::dispatcher::translate_step;

namespace {

int g_passed = 0;
int g_failed = 0;

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

StepRef find_qed_derived(const Program<nd::Instr>& prog) {
    for (const auto& instr : prog.instrs) {
        if (auto* qed = std::get_if<nd::Qed>(&instr)) {
            return qed->derived;
        }
    }
    std::cerr << "no Qed found\n";
    std::abort();
}

util::ResultStatus translate_and_verify(
    Runtime&                    rt,
    const Program<nd::Instr>&   prog,
    FormulaHandle               goal,
    const std::string&          claim_name)
{
    nd::NDVerifier verifier;
    auto trace_r = verifier.trace_full(rt.context(), prog);
    if (!trace_r.ok()) return trace_r.error();
    auto trace = std::move(trace_r).unwrap();

    FormulaBuilder builder(rt.context());
    // Seed builder depth above the ND trace's eigen high-water mark so
    // emit_close's enter_scope() returns indices disjoint from trace-
    // side eigens. (Mirrors nd_to_lkr.cpp:46 — the production path
    // already does this; without it, an inner emit_close Forall can
    // collide with an outer fix-var eigen.)
    while (builder.depth() < trace.next_free_var) builder.enter_scope();
    FormulaHandle goal_nnf = builder.to_nnf(goal);

    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    auto blocks_r = decompose_blocks(prog);
    if (!blocks_r.ok()) return blocks_r.error();
    CloserToOpener c2o = build_closer_to_opener(*blocks_r.value());

    Ctx dcc{rt.context(), builder, prog, trace, c2o};
    StepRef qed_derived = find_qed_derived(prog);

    std::vector<lkr::Instr> emitted;
    auto disp_r = translate_step(
        dcc, std::move(shadow), qed_derived,
        /*target_pos=*/0, DemandPath{}, emitted);
    if (!disp_r.ok()) return disp_r.error();

    LKRProgram lkr_prog;
    lkr_prog.claim_name = claim_name;
    lkr_prog.instrs = std::move(emitted);

    Proof p{System::LKR, std::move(lkr_prog)};
    lkr::LKRVerifier v;
    return v.verify(rt.context(), goal, p);
}

void run_proof_test(const char* claim_name,
                    const char* source) {
    Runtime rt;
    auto parsed = rt.load_with_proofs(source);
    if (!parsed.ok()) {
        std::cerr << "FAIL [" << claim_name << "]: parse: "
                  << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto prog = lower_or_die(parsed.value().proofs[0], rt.context());
    auto sh = rt.context().find_claim(claim_name);
    if (!sh.has_value()) {
        std::cerr << "FAIL [" << claim_name << "]: claim not found\n";
        ++g_failed; return;
    }
    FormulaHandle goal = sh->get().root();
    CHECK_OK(translate_and_verify(rt, prog, goal, claim_name));
}

// =========================================================================
// T-IE-I: implies_elim under DemandInstance.
//
// Currently fails with `axiom_lit: indices do not point to atomic literals`
// because emit_implies_elim_full's psi=∃y.¬Q(y) is non-atomic but raw
// AxiomLit{target_pos, psi_pos} assumes both atomic.
// =========================================================================
void test_implies_elim_under_instance() {
    run_proof_test("ie_inst", R"(
        claim ie_inst: forall z. ((P -> (forall y. Q(y))) -> (P -> Q(z)))
        proof ie_inst:
            fix z
            h_impl = assume P -> (forall y. Q(y))
            h_p = assume P
            h_fa = implies_elim h_impl, h_p
            h_qz = forall_elim h_fa, z
            h_o1 = implies_intro h_qz
            h_o2 = implies_intro h_o1
            h_out = forall_intro h_o2
            qed h_out
    )");
}

// =========================================================================
// T-IL-I: iff_elim_l under DemandInstance — eq_symmetric-shaped.
//
// Currently fails with `emit_close: a is exists, b is and`.
// =========================================================================
void test_iff_elim_l_under_instance() {
    run_proof_test("il_inst", R"(
        claim il_inst: forall z. ((P <-> (forall y. Q(y))) -> (P -> Q(z)))
        proof il_inst:
            fix z
            h_iff = assume P <-> (forall y. Q(y))
            h_p = assume P
            h_fa = iff_elim_l h_iff, h_p
            h_qz = forall_elim h_fa, z
            h_o1 = implies_intro h_qz
            h_o2 = implies_intro h_o1
            h_out = forall_intro h_o2
            qed h_out
    )");
}

// =========================================================================
// T-IR-I: iff_elim_r under DemandInstance.
//
// iff_elim_r: from A↔B and B, derive A. Here A=(forall y.Q(y)), B=P.
// =========================================================================
void test_iff_elim_r_under_instance() {
    run_proof_test("ir_inst", R"(
        claim ir_inst: forall z. (((forall y. Q(y)) <-> P) -> (P -> Q(z)))
        proof ir_inst:
            fix z
            h_iff = assume (forall y. Q(y)) <-> P
            h_p = assume P
            h_fa = iff_elim_r h_iff, h_p
            h_qz = forall_elim h_fa, z
            h_o1 = implies_intro h_qz
            h_o2 = implies_intro h_o1
            h_out = forall_intro h_o2
            qed h_out
    )");
}

// =========================================================================
// T-OE-I: or_elim under DemandInstance.
//
// or_elim produces forall y. Q(y) from both branches; the downstream
// forall_elim demands an instance.
// =========================================================================
void test_or_elim_under_instance() {
    run_proof_test("oe_inst", R"(
        claim oe_inst: forall z. ((P | P) -> ((P -> (forall y. Q(y))) -> Q(z)))
        proof oe_inst:
            fix z
            h_or = assume P | P
            h_pi = assume P -> (forall y. Q(y))
            h_ac_in = assume P
            h_ac_fa = implies_elim h_pi, h_ac_in
            h_ac = implies_intro h_ac_fa
            h_bc_in = assume P
            h_bc_fa = implies_elim h_pi, h_bc_in
            h_bc = implies_intro h_bc_fa
            h_fa = or_elim h_or, h_ac, h_bc
            h_qz = forall_elim h_fa, z
            h_o1 = implies_intro h_qz
            h_o2 = implies_intro h_o1
            h_out = forall_intro h_o2
            qed h_out
    )");
}

// =========================================================================
// T-IE-AL: implies_elim under DemandAndLeft.
//
// and_elim_l of an implies_elim whose conclusion is A ∧ B → wants A.
// Exercises the Or-on-neg-pos peel rather than the Exists peel.
// =========================================================================
void test_implies_elim_under_and_left() {
    run_proof_test("ie_al", R"(
        claim ie_al: (P -> (A & B)) -> (P -> A)
        proof ie_al:
            h_impl = assume P -> (A & B)
            h_p = assume P
            h_ab = implies_elim h_impl, h_p
            h_a = and_elim_l h_ab
            h_o1 = implies_intro h_a
            h_o2 = implies_intro h_o1
            qed h_o2
    )");
}

// =========================================================================
// T-IL-AL: iff_elim_l under DemandAndLeft.
// =========================================================================
void test_iff_elim_l_under_and_left() {
    run_proof_test("il_al", R"(
        claim il_al: (P <-> (A & B)) -> (P -> A)
        proof il_al:
            h_iff = assume P <-> (A & B)
            h_p = assume P
            h_ab = iff_elim_l h_iff, h_p
            h_a = and_elim_l h_ab
            h_o1 = implies_intro h_a
            h_o2 = implies_intro h_o1
            qed h_o2
    )");
}

// =========================================================================
// T-IFF-SWAP: iff_intro of two implies_intros, each wrapping an
// iff_elim of the assumed iff — the exact body-shape of eq_symmetric's
// inner construction (h_swap = iff_intro of LR-direction and RL-
// direction implies-intros). Tests that iff_intro+iff_elim_l+iff_elim_r
// compose correctly with the Weakening that iff_intro emits to share
// the assumed iff between branches.
// =========================================================================
void test_iff_swap_via_intro() {
    run_proof_test("iff_swap", R"(
        claim iff_swap: forall x. ((P(x) <-> Q(x)) -> (Q(x) <-> P(x)))
        proof iff_swap:
            fix x
            h_iff = assume P(x) <-> Q(x)
            h_lr_in = assume Q(x)
            h_lr_p = iff_elim_r h_iff, h_lr_in
            h_lr = implies_intro h_lr_p
            h_rl_in = assume P(x)
            h_rl_q = iff_elim_l h_iff, h_rl_in
            h_rl = implies_intro h_rl_q
            h_swap = iff_intro h_lr, h_rl
            h_o = implies_intro h_swap
            h_full = forall_intro h_o
            qed h_full
    )");
}

// =========================================================================
// T-IL-I-USE: iff_elim_l under DemandInstance where the iff comes from
// a USE+forall_elim chain (matching eq_symmetric's `iff_elim_l ext2, h_eq`
// where ext2 is the doubly-instantiated extensionality axiom).
//
// Exercises Use's apply_path_and_close with a multi-INSTANCE chain, then
// iff_elim_l's emit_iff_elim_full with a single-INSTANCE demand on
// top of the resulting iff.
// =========================================================================
void test_iff_elim_l_via_use_chain() {
    run_proof_test("il_use", R"(
        axiom ext_lite: forall x. forall y. (P(x, y) <-> (forall z. (Q(z, x) <-> Q(z, y))))
        claim il_use:
            forall x. forall y. forall z.
                (P(x, y) -> (Q(z, x) <-> Q(z, y)))
        proof il_use:
            fix x
            fix y
            fix z
            h_p = assume P(x, y)
            ax = use ext_lite
            ax1 = forall_elim ax, x
            ax2 = forall_elim ax1, y
            h_iff = iff_elim_l ax2, h_p
            h_zif = forall_elim h_iff, z
            h_out = implies_intro h_zif
            h_a = forall_intro h_out
            h_b = forall_intro h_a
            h_c = forall_intro h_b
            qed h_c
    )");
}

// =========================================================================
// T-IL-I-DEEP: iff_elim_l under DemandInstance where the iff's RHS body
// is itself an iff (matching eq_symmetric's structural depth — the iff
// of extensionality has a ∀z. (... ↔ ...) body, so after demand peel
// the close descends through (And, Or) → (Or, And) → atomic).
//
// If T-IL-I passes but this fails, the gap is in emit_close's deep-
// decomposition, not in demand propagation.
// =========================================================================
void test_iff_elim_l_under_instance_deep() {
    run_proof_test("il_inst_deep", R"(
        claim il_inst_deep:
            forall z. ((P <-> (forall y. (Q(y) <-> R(y)))) -> (P -> (Q(z) <-> R(z))))
        proof il_inst_deep:
            fix z
            h_iff = assume P <-> (forall y. (Q(y) <-> R(y)))
            h_p = assume P
            h_fa = iff_elim_l h_iff, h_p
            h_qz = forall_elim h_fa, z
            h_o1 = implies_intro h_qz
            h_o2 = implies_intro h_o1
            h_out = forall_intro h_o2
            qed h_out
    )");
}

}  // namespace

int main() {
    test_implies_elim_under_instance();
    test_iff_elim_l_under_instance();
    test_iff_elim_r_under_instance();
    test_or_elim_under_instance();
    test_implies_elim_under_and_left();
    test_iff_elim_l_under_and_left();
    test_iff_elim_l_under_instance_deep();
    test_iff_elim_l_via_use_chain();
    test_iff_swap_via_intro();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
