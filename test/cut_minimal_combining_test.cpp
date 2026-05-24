// Stage 2 Phase 3 tests: combining.{h,cpp} emitters.
//
// Per CUT_MINIMAL_DESIGN.md §6.2: Phase 3 emitters return a CombineSite
// descriptor naming the major + minor step references and target_pos.
// No LKR ops are emitted at this phase; full Cut + structural emission
// lives in Phase 5.
//
// These tests verify the descriptor field-mapping per op variant and
// that out-of-range target_pos is rejected.

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/combining.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::SequentShadow;
using logic::proof::translate::nd_to_lkr::combining::Ctx;
using logic::proof::translate::nd_to_lkr::combining::emit_exists_elim;
using logic::proof::translate::nd_to_lkr::combining::emit_implies_elim;
using logic::proof::translate::nd_to_lkr::combining::emit_or_elim;

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
            "axiom dummy_b: B\n"
            "axiom dummy_c: C\n");
        assert(loaded.ok());
        builder_ = std::make_unique<FormulaBuilder>(rt.context());
    }
};

SequentShadow make_shadow_size1(GlobalContext& ctx) {
    SequentShadow s;
    s.entries.push_back(parse_sentence("A", ctx).get().root());
    return s;
}

void test_implies_elim() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.ctx());
    Ctx cc = f.make_ctx();

    nd::ImpliesElim op{};
    op.impl = StepRef{10};
    op.ant  = StepRef{11};

    auto r = emit_implies_elim(cc, op, shadow, /*target_pos=*/0);
    CHECK(r.ok());
    if (!r.ok()) return;

    const auto& site = r.value();
    CHECK(site.impl_step.idx == 10);
    CHECK(site.ant_step.idx  == 11);
    CHECK(site.target_pos    == 0);
}

void test_or_elim() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.ctx());
    Ctx cc = f.make_ctx();

    nd::OrElim op{};
    op.or_formula = StepRef{20};
    op.ac         = StepRef{21};
    op.bc         = StepRef{22};

    auto r = emit_or_elim(cc, op, shadow, /*target_pos=*/0);
    CHECK(r.ok());
    if (!r.ok()) return;

    const auto& site = r.value();
    CHECK(site.or_formula_step.idx == 20);
    CHECK(site.ac_step.idx         == 21);
    CHECK(site.bc_step.idx         == 22);
    CHECK(site.target_pos          == 0);
}

void test_exists_elim() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.ctx());
    Ctx cc = f.make_ctx();

    nd::ExistsElim op{};
    op.formula = StepRef{30};

    auto r = emit_exists_elim(cc, op, shadow, /*target_pos=*/0);
    CHECK(r.ok());
    if (!r.ok()) return;

    const auto& site = r.value();
    CHECK(site.formula_step.idx == 30);
    CHECK(site.target_pos       == 0);
}

void test_target_pos_routed() {
    // target_pos is passed through unchanged.
    TestFixture f;
    SequentShadow shadow;
    shadow.entries.push_back(parse_sentence("A", f.ctx()).get().root());
    shadow.entries.push_back(parse_sentence("B", f.ctx()).get().root());
    shadow.entries.push_back(parse_sentence("C", f.ctx()).get().root());
    Ctx cc = f.make_ctx();

    nd::ImpliesElim op{};
    op.impl = StepRef{1};
    op.ant  = StepRef{2};
    auto r = emit_implies_elim(cc, op, shadow, /*target_pos=*/2);
    CHECK(r.ok());
    if (r.ok()) CHECK(r.value().target_pos == 2);
}

void test_out_of_range_rejected() {
    TestFixture f;
    auto shadow = make_shadow_size1(f.ctx());   // size 1
    Ctx cc = f.make_ctx();

    nd::OrElim op{};
    op.or_formula = StepRef{1};
    op.ac         = StepRef{2};
    op.bc         = StepRef{3};
    auto r = emit_or_elim(cc, op, shadow, /*target_pos=*/9);
    CHECK(!r.ok());
}

}  // namespace

int main() {
    test_implies_elim();
    test_or_elim();
    test_exists_elim();
    test_target_pos_routed();
    test_out_of_range_rejected();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
