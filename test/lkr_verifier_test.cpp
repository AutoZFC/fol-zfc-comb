// LKRVerifier tests for Hughes' one-sided multi-conclusion sequent calculus.
//
// These exercise each LKR op via C++-built lkr::Program values. The
// programs operate on NNF formulas — the verifier NNF-normalizes the
// goal at entry, so test programs should expect the post-NNF form.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/runner.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace logic;
using namespace logic::proof;

namespace {

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

int g_passed = 0;
int g_failed = 0;

#define CHECK(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

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
// AxiomLit: prove ⊢ P → P. NNF: ¬P ∨ P. Apply Or(0) → [¬P, P]; close
// via AxiomLit on the dual pair.
// =========================================================================
void test_axiom_self_implication() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "lkr_self_impl";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// And rule: prove ⊢ (P ∧ Q) → (Q ∧ P).
// NNF: (¬P ∨ ¬Q) ∨ (Q ∧ P).
// Or(0) → [(¬P ∨ ¬Q), (Q ∧ P)].
// Or(0) on (¬P ∨ ¬Q) replaces idx 0 with ¬P and appends ¬Q at the end:
//   → [¬P, (Q ∧ P), ¬Q].
// And(1) splits on (Q ∧ P):
//   LEFT  [¬P, Q, ¬Q]  — AxiomLit(1, 2) on (Q, ¬Q).
//   RIGHT [¬P, P, ¬Q]  — AxiomLit(0, 1) on (¬P, P).
// =========================================================================
void test_and_commute() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "(P & Q) -> (Q & P)");

    LKRProgram prog;
    prog.claim_name = "and_commute";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::And{{}, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 1, 2});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Modus ponens packed: ⊢ ((P → Q) ∧ P) → Q.
// NNF builds `Or(Or(And(P, ¬Q), ¬P), Q)` (left-associated by the NNF
// implementation's bottom-up assembly).
// Initial: [Or(Or(And(P, ¬Q), ¬P), Q)].
// Or(0): replaces idx 0 with phi=`Or(And(P, ¬Q), ¬P)`; appends psi=`Q`.
//        → [Or(And(P, ¬Q), ¬P), Q].
// Or(0): replaces idx 0 with phi=`And(P, ¬Q)`; appends psi=`¬P`.
//        → [And(P, ¬Q), Q, ¬P].
// And(0) splits And(P, ¬Q):
//   LEFT  [P, Q, ¬P]   — AxiomLit(0, 2) on (P, ¬P).
//   RIGHT [¬Q, Q, ¬P]  — AxiomLit(0, 1) on (¬Q, Q).
// =========================================================================
void test_implies_packed() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "((P -> Q) & P) -> Q");

    LKRProgram prog;
    prog.claim_name = "modus_ponens_packed";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::And{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Forall + Exists: ⊢ (∀x. P(x)) → (∀y. P(y)).
// NNF: (∃x. ¬P(x)) ∨ (∀y. P(y)).
// Or(0) → [∃x.¬P(x), ∀y.P(y)]. Forall(1) → introduces eigen e (TermRef
// at instr 1); replaces entry 1 with P(e).  ts.entries = [∃x.¬P(x), P(e)].
// Exists(0, witness=e) → replaces entry 0 with ¬P(e). [¬P(e), P(e)].
// AxiomLit(0,1).
// =========================================================================
void test_forall_round_trip() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "(forall x. P(x)) -> (forall y. P(y))");

    LKRProgram prog;
    prog.claim_name = "forall_round_trip";
    prog.instrs.push_back(lkr::Or{{}, 0});                 // instr 0
    prog.instrs.push_back(lkr::Forall{{}, 1});             // instr 1: binds TermRef{1}
    prog.instrs.push_back(lkr::Exists{{}, 0, TermRef{1}}); // instr 2
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});        // instr 3

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// AxiomLit rejection: indices that don't point to dual literals fail.
// =========================================================================
void test_axiom_lit_rejects_non_duals() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "axiom_lit_reject";
    prog.instrs.push_back(lkr::Or{{}, 0});            // [¬P, P]
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 0});   // same index; should error

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Cross-system theorem reuse: prove a theorem in ND, then UseTheorem from
// LKR. UseTheorem closes if some entry equals NNF(theorem).
// =========================================================================
void test_cross_system_use_theorem() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom self_impl_axiom: forall x. (P(x) -> P(x))
        claim my_thm: forall x. (P(x) -> P(x))

        proof my_thm:
            h = use self_impl_axiom
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse failed: " << parsed.error().to_string() << "\n";
        ++g_failed;
        return;
    }
    EXPECT_OK(rt.execute_all_proofs(parsed.value()));
    auto& ctx = rt.context();
    auto thm = ctx.find_theorem("my_thm");
    CHECK(thm.has_value());
    if (!thm.has_value()) return;

    FormulaHandle goal = thm.value().get().root();
    LKRProgram prog;
    prog.claim_name = "lkr_uses_my_thm";
    prog.instrs.push_back(lkr::UseTheorem{{}, AxiomRef{"my_thm"}});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));

    const auto& used = v.last_used_names();
    CHECK(used.count("my_thm") == 1);
}

// =========================================================================
// Cut: prove ⊢ P → P via additive Cut on P.
// NNF of goal: ¬P ∨ P. Cut(P): LEFT = [¬P ∨ P, P]; RIGHT = [¬P ∨ P, ¬P].
// LEFT close: Or(0) → [¬P, P, P]; AxiomLit(0, 1).
// RIGHT close: Or(0) → [¬P, P, ¬P]; AxiomLit(0, 1).
// =========================================================================
void test_cut() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();

    // Need a FormulaHandle for "P" to pass to Cut. Build via parse of a
    // larger sentence and extract.
    FormulaHandle goal = parse_root(ctx, "P -> P");
    // Goal NNF = ¬P ∨ P; the right disjunct is P (positive atom).
    FormulaHandle goal_nnf;
    {
        FormulaBuilder b(ctx);
        goal_nnf = b.to_nnf(goal);
    }
    FormulaHandle P_handle = goal_nnf.get().as_compound().right;

    LKRProgram prog;
    prog.claim_name = "cut_taut";
    prog.instrs.push_back(lkr::Cut{{}, P_handle});  // instr 0
    // LEFT  = [(¬P ∨ P), P]. Or(0) → [¬P, P, P]. AxiomLit(0, 1).
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    // RIGHT = [(¬P ∨ P), ¬P]. Or(0) → [¬P, ¬P, P]. AxiomLit(0, 2).
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Reject-on-no-progress.
// =========================================================================
void test_unfinished_proof_rejected() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "unfinished";
    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Dispatcher routing.
// =========================================================================
void test_dispatcher_routes_lkr() {
    Runtime rt;
    auto loaded = rt.load(R"(
        axiom dummy: forall x. P(x)
        claim self_impl: P -> P
    )");
    assert(loaded.ok());

    LKRProgram prog;
    prog.claim_name = "self_impl";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};

    proof::ProofRunner runner(rt.context());
    EXPECT_OK(runner.verify(p));

    CHECK(rt.context().find_theorem("self_impl").has_value());
}

}  // namespace

int main() {
    test_axiom_self_implication();
    test_and_commute();
    test_implies_packed();
    test_forall_round_trip();
    test_axiom_lit_rejects_non_duals();
    test_cross_system_use_theorem();
    test_cut();
    test_unfinished_proof_rejected();
    test_dispatcher_routes_lkr();

    std::cout << "lkr_verifier_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
