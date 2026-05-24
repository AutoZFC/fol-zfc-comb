// Stage 2 Phase 2 tests: projections.{h,cpp} emitters.
//
// Per CUT_MINIMAL_DESIGN.md §6.1: Phase 2 emitters return a
// RecurseDescriptor naming (producer step, target_pos, demand). No
// LKR ops are emitted at this phase; semantic correctness is exercised
// at Phase 5 (dispatcher + demand-aware Phase 1).
//
// These tests verify the descriptor field-mapping: each op variant
// projects to its expected Demand value, the producer field is routed
// from the op's StepRef, and target_pos is preserved.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/demand.h"
#include "src/proof/translate/nd_to_lkr/projections.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>
#include <variant>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::Demand;
using logic::proof::translate::nd_to_lkr::DemandAndLeft;
using logic::proof::translate::nd_to_lkr::DemandAndRight;
using logic::proof::translate::nd_to_lkr::DemandDoubleNeg;
using logic::proof::translate::nd_to_lkr::DemandIffLeft;
using logic::proof::translate::nd_to_lkr::DemandIffRight;
using logic::proof::translate::nd_to_lkr::DemandInstance;
using logic::proof::translate::nd_to_lkr::DemandNone;
using logic::proof::translate::nd_to_lkr::RecurseDescriptor;
using logic::proof::translate::nd_to_lkr::SequentShadow;
using logic::proof::translate::nd_to_lkr::projections::Ctx;
using logic::proof::translate::nd_to_lkr::projections::emit_and_elim_l;
using logic::proof::translate::nd_to_lkr::projections::emit_and_elim_r;
using logic::proof::translate::nd_to_lkr::projections::emit_double_neg_elim;
using logic::proof::translate::nd_to_lkr::projections::emit_forall_elim;
using logic::proof::translate::nd_to_lkr::projections::emit_iff_elim_l;
using logic::proof::translate::nd_to_lkr::projections::emit_iff_elim_r;

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
    Program<nd::Instr>              empty_prog{};
    nd::NDVerifier::TraceFull       empty_trace{};

    Ctx make_ctx() {
        return Ctx{rt.context(), *builder_, empty_prog, empty_trace};
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

// Build a minimal shadow with a single dummy formula at index 0. The
// Phase 2 emitters only check `f_k_idx in range`; the formula content
// is not inspected.
SequentShadow make_shadow_size1(FormulaBuilder& b, GlobalContext& ctx) {
    SequentShadow s;
    // Use any formula handle; content doesn't matter for descriptor tests.
    SentenceHandle dummy = parse_sentence("A", ctx);
    s.entries.push_back(dummy.get().root());
    (void)b;
    return s;
}

void test_and_elim_l() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    nd::AndElimL op{};
    op.of = StepRef{42};

    auto r = emit_and_elim_l(cc, op, shadow, /*f_k_idx=*/0);
    CHECK(r.ok());
    if (!r.ok()) return;

    const RecurseDescriptor& d = r.value();
    CHECK(d.producer.idx == 42);
    CHECK(d.target_pos == 0);
    CHECK(std::holds_alternative<DemandAndLeft>(d.demand));
}

void test_and_elim_r() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    nd::AndElimR op{};
    op.of = StepRef{7};

    auto r = emit_and_elim_r(cc, op, shadow, 0);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().producer.idx == 7);
    CHECK(std::holds_alternative<DemandAndRight>(r.value().demand));
}

void test_iff_elim_l() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    nd::IffElimL op{};
    op.iff = StepRef{11};
    op.a   = StepRef{12};

    auto r = emit_iff_elim_l(cc, op, shadow, 0);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().producer.idx == 11);
    CHECK(std::holds_alternative<DemandIffLeft>(r.value().demand));
}

void test_iff_elim_r() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    nd::IffElimR op{};
    op.iff = StepRef{13};
    op.b   = StepRef{14};

    auto r = emit_iff_elim_r(cc, op, shadow, 0);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().producer.idx == 13);
    CHECK(std::holds_alternative<DemandIffRight>(r.value().demand));
}

void test_double_neg_elim() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    nd::DoubleNegElim op{};
    op.of = StepRef{99};

    auto r = emit_double_neg_elim(cc, op, shadow, 0);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().producer.idx == 99);
    CHECK(std::holds_alternative<DemandDoubleNeg>(r.value().demand));
}

void test_forall_elim_with_binding() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    Ctx cc = f.make_ctx();

    // Set up a synthetic TermRef binding in shadow.lkr_term_for, as a
    // Fix step upstream would have done.
    const uint32_t nd_term_ref_idx = 5;
    const var_index eigen{42};
    SequentShadow::TermBinding binding;
    binding.lkr_ref = TermRef{nd_term_ref_idx};
    binding.value   = Term::fixed(eigen);
    shadow.lkr_term_for[nd_term_ref_idx] = binding;

    nd::ForallElim op{};
    op.formula = StepRef{20};
    op.term    = TermRef{nd_term_ref_idx};

    auto r = emit_forall_elim(cc, op, shadow, 0);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(r.value().producer.idx == 20);
    CHECK(std::holds_alternative<DemandInstance>(r.value().demand));
    if (std::holds_alternative<DemandInstance>(r.value().demand)) {
        const auto& di = std::get<DemandInstance>(r.value().demand);
        CHECK(di.t.is_fixed());
        CHECK(di.t.as_variable() == eigen);
    }
}

// Missing TermRef binding for forall_elim → translator-bug error.
void test_forall_elim_missing_binding() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());
    // Deliberately do NOT add the binding.
    Ctx cc = f.make_ctx();

    nd::ForallElim op{};
    op.formula = StepRef{20};
    op.term    = TermRef{999};   // not in shadow.lkr_term_for

    auto r = emit_forall_elim(cc, op, shadow, 0);
    CHECK(!r.ok());
}

void test_target_pos_routed() {
    // f_k_idx is passed through unchanged in the descriptor.
    TestFixture f;
    SequentShadow shadow;
    shadow.entries.push_back(parse_sentence("A", f.ctx()).get().root());
    shadow.entries.push_back(parse_sentence("B", f.ctx()).get().root());
    shadow.entries.push_back(parse_sentence("A", f.ctx()).get().root());
    Ctx cc = f.make_ctx();

    nd::AndElimL op{};
    op.of = StepRef{1};
    auto r = emit_and_elim_l(cc, op, shadow, /*f_k_idx=*/2);
    CHECK(r.ok());
    if (r.ok()) CHECK(r.value().target_pos == 2);
}

void test_out_of_range_rejected() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.builder(), f.ctx());   // size 1
    Ctx cc = f.make_ctx();

    nd::AndElimL op{};
    op.of = StepRef{1};
    auto r = emit_and_elim_l(cc, op, shadow, /*f_k_idx=*/5);
    CHECK(!r.ok());
}

}  // namespace

int main() {
    test_and_elim_l();
    test_and_elim_r();
    test_iff_elim_l();
    test_iff_elim_r();
    test_double_neg_elim();
    test_forall_elim_with_binding();
    test_forall_elim_missing_binding();
    test_target_pos_routed();
    test_out_of_range_rejected();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
