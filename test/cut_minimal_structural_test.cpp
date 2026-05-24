// Stage 2 Phase 4 tests: structural.{h,cpp} emitters.
//
// Per CUT_MINIMAL_DESIGN.md §6.3: Phase 4 emitters return scope-opener,
// closer, leaf, and entry-point descriptors. No LKR ops are emitted at
// this phase; full Cut + emit_close + scope binding lives in Phase 5.
//
// These tests verify descriptor field-mapping per op variant, plus
// the NotElim-operand extraction for closers (NotIntro/BottomElim/
// ClassicalAbsurd dereference their `bottom` to read the NotElim's
// negation + formula step refs).

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/proof/translate/nd_to_lkr/structural.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::SequentShadow;
using logic::proof::translate::nd_to_lkr::structural::Ctx;
using logic::proof::translate::nd_to_lkr::structural::emit_assume_leaf;
using logic::proof::translate::nd_to_lkr::structural::emit_assume_open;
using logic::proof::translate::nd_to_lkr::structural::emit_bottom_elim_close;
using logic::proof::translate::nd_to_lkr::structural::emit_classical_absurd_close;
using logic::proof::translate::nd_to_lkr::structural::emit_exists_elim_open;
using logic::proof::translate::nd_to_lkr::structural::emit_fix_open;
using logic::proof::translate::nd_to_lkr::structural::emit_not_intro_close;
using logic::proof::translate::nd_to_lkr::structural::emit_qed_site;

namespace {

int g_passed = 0;
int g_failed = 0;

#define CHECK(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

struct TestFixture {
    Runtime                         rt;
    std::unique_ptr<FormulaBuilder> builder_;
    Program<nd::Instr>              prog{};
    nd::NDVerifier::TraceFull       trace{};

    Ctx make_ctx() {
        return Ctx{rt.context(), *builder_, prog, trace};
    }
    GlobalContext&  ctx()     { return rt.context(); }
    FormulaBuilder& builder() { return *builder_; }

    TestFixture() {
        auto loaded = rt.load(
            "axiom dummy_p: forall x. P(x)\n"
            "axiom dummy_a: A\n"
            "axiom dummy_b: B\n");
        assert(loaded.ok());
        builder_ = std::make_unique<FormulaBuilder>(rt.context());
    }
};

void test_assume_open() {
    TestFixture f;
    // Synthesize trace.step_env[0] = formula(A) for the Assume step.
    FormulaHandle a = parse_sentence("A", f.ctx()).get().root();
    f.trace.step_env.resize(1);
    f.trace.step_env[0] = a;

    Ctx cc = f.make_ctx();
    nd::Assume op{};
    auto r = emit_assume_open(cc, op, StepRef{0});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().assume_step.idx == 0);
    CHECK(r.value().formula == a);
}

void test_fix_open() {
    TestFixture f;
    const var_index eigen{42};
    f.trace.term_env.resize(3);
    f.trace.term_present.resize(3, 0);
    f.trace.term_env[1] = Term::fixed(eigen);
    f.trace.term_present[1] = 1;

    Ctx cc = f.make_ctx();
    nd::Fix op{};
    auto r = emit_fix_open(cc, op, StepRef{1});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().fix_step.idx == 1);
    CHECK(r.value().eigen == eigen);
}

void test_fix_open_no_term() {
    TestFixture f;
    f.trace.term_env.resize(2);
    f.trace.term_present.resize(2, 0);
    // step 0's term_present remains false.

    Ctx cc = f.make_ctx();
    nd::Fix op{};
    auto r = emit_fix_open(cc, op, StepRef{0});
    CHECK(!r.ok());   // no term recorded → translator-bug error.
}

void test_exists_elim_open() {
    TestFixture f;
    const var_index eigen{77};
    f.trace.term_env.resize(2);
    f.trace.term_present.resize(2, 0);
    f.trace.term_env[1] = Term::fixed(eigen);
    f.trace.term_present[1] = 1;

    Ctx cc = f.make_ctx();
    nd::ExistsElim op{};
    op.formula = StepRef{55};
    auto r = emit_exists_elim_open(cc, op, StepRef{1});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().exists_elim_step.idx == 1);
    CHECK(r.value().formula_step.idx     == 55);
    CHECK(r.value().eigen                == eigen);
}

void test_not_intro_close() {
    TestFixture f;
    // Build a Program with a NotElim at index 0.
    nd::NotElim ne{};
    ne.negation = StepRef{7};
    ne.formula  = StepRef{8};
    f.prog.instrs.push_back(ne);

    Ctx cc = f.make_ctx();
    nd::NotIntro op{};
    op.bottom = StepRef{0};
    auto r = emit_not_intro_close(cc, op, StepRef{99});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().not_intro_step.idx == 99);
    CHECK(r.value().neg_step.idx       == 7);
    CHECK(r.value().formula_step.idx   == 8);
}

void test_not_intro_close_bad_bottom() {
    TestFixture f;
    // bottom points to a non-NotElim (e.g., a Let).
    nd::Let lop{};
    f.prog.instrs.push_back(lop);

    Ctx cc = f.make_ctx();
    nd::NotIntro op{};
    op.bottom = StepRef{0};
    auto r = emit_not_intro_close(cc, op, StepRef{99});
    CHECK(!r.ok());
}

void test_bottom_elim_close() {
    TestFixture f;
    nd::NotElim ne{};
    ne.negation = StepRef{10};
    ne.formula  = StepRef{11};
    f.prog.instrs.push_back(ne);

    Ctx cc = f.make_ctx();
    nd::BottomElim op{};
    op.bottom         = StepRef{0};
    op.target_formula = StepRef{12};
    auto r = emit_bottom_elim_close(cc, op, StepRef{77});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().bottom_elim_step.idx == 77);
    CHECK(r.value().neg_step.idx         == 10);
    CHECK(r.value().formula_step.idx     == 11);
    CHECK(r.value().target_formula.idx   == 12);
}

void test_classical_absurd_close() {
    TestFixture f;
    nd::NotElim ne{};
    ne.negation = StepRef{20};
    ne.formula  = StepRef{21};
    f.prog.instrs.push_back(ne);

    Ctx cc = f.make_ctx();
    nd::ClassicalAbsurd op{};
    op.bottom = StepRef{0};
    auto r = emit_classical_absurd_close(cc, op, StepRef{88});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().absurd_step.idx   == 88);
    CHECK(r.value().neg_step.idx      == 20);
    CHECK(r.value().formula_step.idx  == 21);
}

void test_assume_leaf() {
    TestFixture f;
    SequentShadow shadow;
    shadow.entries.push_back(parse_sentence("A", f.ctx()).get().root());
    shadow.entries.push_back(parse_sentence("B", f.ctx()).get().root());

    Ctx cc = f.make_ctx();
    nd::Assume op{};
    auto r = emit_assume_leaf(cc, op, StepRef{42}, shadow, /*target_pos=*/1);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().assume_step.idx == 42);
    CHECK(r.value().target_pos      == 1);
}

void test_assume_leaf_out_of_range() {
    TestFixture f;
    SequentShadow shadow;
    shadow.entries.push_back(parse_sentence("A", f.ctx()).get().root());
    Ctx cc = f.make_ctx();
    nd::Assume op{};
    auto r = emit_assume_leaf(cc, op, StepRef{0}, shadow, /*target_pos=*/9);
    CHECK(!r.ok());
}

void test_qed_site() {
    TestFixture f;
    Ctx cc = f.make_ctx();
    nd::Qed op{};
    op.derived = StepRef{15};
    auto r = emit_qed_site(cc, op, StepRef{16});
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().qed_step.idx     == 16);
    CHECK(r.value().derived_step.idx == 15);
}

}  // namespace

int main() {
    test_assume_open();
    test_fix_open();
    test_fix_open_no_term();
    test_exists_elim_open();
    test_not_intro_close();
    test_not_intro_close_bad_bottom();
    test_bottom_elim_close();
    test_classical_absurd_close();
    test_assume_leaf();
    test_assume_leaf_out_of_range();
    test_qed_site();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
