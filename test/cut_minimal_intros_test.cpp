// Stage 2 Phase 1 tests: intros.{h,cpp} emitters.
//
// Per CUT_MINIMAL_DESIGN.md §5.2: each emitter is exercised against a
// hand-built shadow representing the dispatcher's state at that point.
// The emitter's output is wrapped in an LKR program that includes the
// caller-side setup (outer right rules) and the recursion-side close
// ops, then LKRVerifier checks the result against the original goal.
//
// Acceptance by LKRVerifier is the soundness witness for each emitter.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/runner.h"
#include "src/proof/translate/nd_to_lkr/intros.h"
#include "src/proof/translate/nd_to_lkr/sequent_shadow.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <variant>
#include <vector>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::nd_to_lkr::SequentShadow;
using logic::proof::translate::nd_to_lkr::intros::Ctx;
using logic::proof::translate::nd_to_lkr::intros::IntroResult;
using logic::proof::translate::nd_to_lkr::intros::OnePremise;
using logic::proof::translate::nd_to_lkr::intros::TwoPremise;
using logic::proof::translate::nd_to_lkr::intros::ZeroPremise;

namespace {

int g_passed = 0;
int g_failed = 0;

#define CHECK(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define CHECK_OK(expr) do { \
    auto _r = (expr); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Ok, got: " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

// Convenience: a Runtime + ctx + builder + empty prog/trace package.
struct TestFixture {
    Runtime                     rt;
    std::unique_ptr<FormulaBuilder> builder_;
    Program<nd::Instr>          empty_prog{};
    nd::NDVerifier::TraceFull   empty_trace{};

    Ctx make_ctx() {
        return Ctx{rt.context(), *builder_, empty_prog, empty_trace};
    }
    GlobalContext& ctx() { return rt.context(); }
    FormulaBuilder& builder() { return *builder_; }

    TestFixture() {
        // Load a dummy axiom so the runtime has a populated context with
        // the predicates we'll parse against. P, Q, R are atomic.
        auto loaded = rt.load(
            "axiom dummy_p: forall x. P(x)\n"
            "axiom dummy_q: forall x. Q(x)\n"
            "axiom dummy_r: forall x. R(x)\n"
            "axiom dummy_atom_a: A\n"
            "axiom dummy_atom_b: B\n"
        );
        assert(loaded.ok());
        builder_ = std::make_unique<FormulaBuilder>(rt.context());
    }
};

// =========================================================================
// emit_or_intro_l
//
// Goal: A → (A | B). NNF: ¬A ∨ (A ∨ B). Caller-side setup: outer Or
// (decomposes the implication). Then emit_or_intro_l fires on (A∨B) at
// index 1. Recursion-side close: AxiomLit on (¬A, A) duals.
// =========================================================================
void test_or_intro_l() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "A -> (A | B)");

    // Manually build the shadow state at the point emit_or_intro_l fires:
    // sequent = [¬A_nnf, NNF(A∨B)].
    FormulaHandle a_nnf      = f.builder().to_nnf(parse_root(f.ctx(), "A"));
    FormulaHandle neg_a_nnf  = f.builder().to_nnf_neg(parse_root(f.ctx(), "A"));
    FormulaHandle a_or_b     = f.builder().to_nnf(parse_root(f.ctx(), "A | B"));
    (void)a_nnf;

    SequentShadow shadow;
    shadow.entries.push_back(neg_a_nnf);
    shadow.entries.push_back(a_or_b);

    Ctx cc = f.make_ctx();
    nd::OrIntroL op{};
    op.a         = StepRef{0};
    op.b_formula = StepRef{1};

    std::vector<lkr::Instr> emitted;
    auto r = emit_or_intro_l(cc, op, shadow, /*f_k_idx=*/1, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    // Assert IntroResult shape: OnePremise with premise_pos at the
    // left-disjunct's position (= f_k_idx = 1).
    CHECK(std::holds_alternative<OnePremise>(r.value()));
    const auto& one = std::get<OnePremise>(r.value());
    CHECK(one.premise_pos == 1);
    CHECK(one.shadow.entries.size() == 3);   // [¬A, A, B] after Or

    // Assert emitted op: a single Or with principal=1.
    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::Or>(emitted[0]));
    CHECK(std::get<lkr::Or>(emitted[0]).principal == 1);

    // Wrap in a full LKR program and verify.
    LKRProgram prog;
    prog.claim_name = "or_intro_l_test";
    prog.instrs.push_back(lkr::Or{{}, 0});             // outer setup
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});    // close ¬A vs A

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_or_intro_r
//
// Symmetric: goal B → (A | B). NNF: ¬B ∨ (A ∨ B). After outer Or, sequent
// is [¬B, A∨B]. emit_or_intro_r fires on (A∨B); premise_pos = B's end position.
// =========================================================================
void test_or_intro_r() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "B -> (A | B)");

    FormulaHandle neg_b_nnf = f.builder().to_nnf_neg(parse_root(f.ctx(), "B"));
    FormulaHandle a_or_b    = f.builder().to_nnf(parse_root(f.ctx(), "A | B"));

    SequentShadow shadow;
    shadow.entries.push_back(neg_b_nnf);
    shadow.entries.push_back(a_or_b);

    Ctx cc = f.make_ctx();
    nd::OrIntroR op{};
    std::vector<lkr::Instr> emitted;
    auto r = emit_or_intro_r(cc, op, shadow, /*f_k_idx=*/1, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<OnePremise>(r.value()));
    const auto& one = std::get<OnePremise>(r.value());
    CHECK(one.premise_pos == 2);             // B at end position
    CHECK(one.shadow.entries.size() == 3);   // [¬B, A, B]

    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::Or>(emitted[0]));

    LKRProgram prog;
    prog.claim_name = "or_intro_r_test";
    prog.instrs.push_back(lkr::Or{{}, 0});
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});   // close ¬B vs B

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_implies_intro
//
// Goal: A → A. NNF: ¬A ∨ A. emit_implies_intro fires directly on the
// principal. After Or, sequent is [¬A, A]; premise_pos = 1 (the conclusion A).
// =========================================================================
void test_implies_intro() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "A -> A");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::ImpliesIntro op{};
    std::vector<lkr::Instr> emitted;
    auto r = emit_implies_intro(cc, op, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<OnePremise>(r.value()));
    const auto& one = std::get<OnePremise>(r.value());
    CHECK(one.premise_pos == 1);             // conclusion A position
    CHECK(one.shadow.entries.size() == 2);   // [¬A, A]

    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::Or>(emitted[0]));

    LKRProgram prog;
    prog.claim_name = "implies_intro_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_forall_intro
//
// Goal: ∀x. (P(x) → P(x)). NNF: ∀x. (¬P(x) ∨ P(x)).
// emit_forall_intro fires on the principal with an explicit eigen.
// After Forall, sequent is [¬P(eigen) ∨ P(eigen)]; premise_pos = 0.
// Then the dispatcher's recursion would emit Or + AxiomLit.
// =========================================================================
void test_forall_intro() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "forall x. (P(x) -> P(x))");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::ForallIntro op{};

    // Pick a fresh eigen (just any var_index — verifier checks freshness
    // against the sequent, which has no fixed vars yet).
    var_index eigen{99};

    std::vector<lkr::Instr> emitted;
    auto r = emit_forall_intro(cc, op, eigen, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<OnePremise>(r.value()));
    const auto& one = std::get<OnePremise>(r.value());
    CHECK(one.premise_pos == 0);

    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::Forall>(emitted[0]));
    CHECK(std::get<lkr::Forall>(emitted[0]).eigen == eigen);

    // Complete the proof: after Forall, sequent is [¬P(eigen) ∨ P(eigen)].
    // Or to expose duals, AxiomLit to close.
    LKRProgram prog;
    prog.claim_name = "forall_intro_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_and_intro
//
// Goal: (A | ~A) & (B | ~B). NNF: same (both conjuncts are taut). The
// emitter fires on the principal with empty surrounding context, so no
// Weakenings are emitted (right_needs is empty). And{0, []} splits to
// LEFT = [A|¬A] and RIGHT = [B|¬B]. Each branch's recursion would emit
// Or + AxiomLit.
// =========================================================================
void test_and_intro() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "(A | ~A) & (B | ~B)");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::AndIntro op{};

    std::vector<lkr::Instr> emitted;
    auto r = emit_and_intro(cc, op, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<TwoPremise>(r.value()));
    const auto& two = std::get<TwoPremise>(r.value());
    CHECK(two.left_shadow.entries.size() == 1);    // [A|¬A]
    CHECK(two.right_shadow.entries.size() == 1);   // [B|¬B]
    CHECK(two.left_pos == 0);
    CHECK(two.right_pos == 0);

    // emitted = [And{0, []}] (no Weakenings since no surrounding context).
    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::And>(emitted[0]));
    CHECK(std::get<lkr::And>(emitted[0]).principal == 0);
    CHECK(std::get<lkr::And>(emitted[0]).left_partition.empty());

    // Build full LKR program: And + (Or, AxiomLit) on each branch.
    LKRProgram prog;
    prog.claim_name = "and_intro_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    // LKR's branching pushes RIGHT then LEFT on top of the open-goals
    // stack (LEFT operates first). For our test both branches have the
    // same Or+AxiomLit shape, so the order doesn't change the program.
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_iff_intro
//
// Goal: A <-> A. NNF: (¬A ∨ A) ∧ (¬A ∨ A). The emitter does And + Or
// per branch. Each branch ends at [¬A, A] which closes via AxiomLit.
// =========================================================================
void test_iff_intro() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "A <-> A");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::IffIntro op{};
    std::vector<lkr::Instr> emitted;
    auto r = emit_iff_intro(cc, op, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<TwoPremise>(r.value()));

    // emitter emits And only. Each branch's recursion (= the dispatcher
    // calling the IMPLIES_INTRO emitter on each ab/ba) would emit Or on
    // the conjunct. For this unit test we manually emit Or + AxiomLit
    // per branch to close.
    CHECK(emitted.size() == 1);
    CHECK(std::holds_alternative<lkr::And>(emitted[0]));

    LKRProgram prog;
    prog.claim_name = "iff_intro_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);
    // LEFT subgoal: [¬A ∨ A]. Or → [¬A, A]. AxiomLit closes.
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    // RIGHT subgoal: [A ∨ ¬A]. Or → [A, ¬A]. AxiomLit closes.
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_excluded_middle
//
// Goal: A | ~A. The emitter emits Or + emit_close. The whole goal
// closes via the emitter — ZeroPremise.
// =========================================================================
void test_excluded_middle() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "A | ~A");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::ExcludedMiddle op{};
    std::vector<lkr::Instr> emitted;
    auto r = emit_excluded_middle(cc, op, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) return;

    CHECK(std::holds_alternative<ZeroPremise>(r.value()));

    LKRProgram prog;
    prog.claim_name = "excluded_middle_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

// =========================================================================
// emit_peirce
//
// Goal: ((A -> B) -> A) -> A. The emitter emits the full cut-free
// skeleton; ZeroPremise.
// =========================================================================
void test_peirce() {
    TestFixture f;
    FormulaHandle goal = parse_root(f.ctx(), "((A -> B) -> A) -> A");

    FormulaHandle goal_nnf = f.builder().to_nnf(goal);
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);

    Ctx cc = f.make_ctx();
    nd::Peirce op{};
    std::vector<lkr::Instr> emitted;
    auto r = emit_peirce(cc, op, shadow, /*f_k_idx=*/0, emitted);
    CHECK(r.ok());
    if (!r.ok()) {
        std::cerr << "  peirce error: " << r.error().to_string() << "\n";
        return;
    }

    CHECK(std::holds_alternative<ZeroPremise>(r.value()));

    LKRProgram prog;
    prog.claim_name = "peirce_test";
    for (const auto& op_i : emitted) prog.instrs.push_back(op_i);

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    CHECK_OK(v.verify(f.ctx(), goal, p));
}

}  // namespace

int main() {
    test_or_intro_l();
    test_or_intro_r();
    test_implies_intro();
    test_forall_intro();
    test_and_intro();
    test_iff_intro();
    test_excluded_middle();
    test_peirce();

    std::cerr << "\nResults: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
