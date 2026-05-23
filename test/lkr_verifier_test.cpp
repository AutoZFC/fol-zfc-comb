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
// And rule (multiplicative): prove ⊢ (P ∧ Q) → (Q ∧ P).
// NNF: (¬P ∨ ¬Q) ∨ (Q ∧ P).
// Or(0) → [(¬P ∨ ¬Q), (Q ∧ P)].
// Or(0) on (¬P ∨ ¬Q) replaces idx 0 with ¬P and appends ¬Q at the end:
//   → [¬P, (Q ∧ P), ¬Q].
// And(principal=1, left_partition={2}) splits on (Q ∧ P):
//   LEFT  = entries[2] then φ=Q   = [¬Q, Q]   — AxiomLit(0, 1).
//   RIGHT = entries[0] then θ=P   = [¬P, P]   — AxiomLit(0, 1).
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
    prog.instrs.push_back(lkr::And{{}, 1, {2}});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Modus ponens packed (multiplicative): ⊢ ((P → Q) ∧ P) → Q.
// NNF builds `Or(Or(And(P, ¬Q), ¬P), Q)` (left-associated by the NNF
// implementation's bottom-up assembly).
// Initial: [Or(Or(And(P, ¬Q), ¬P), Q)].
// Or(0): → [Or(And(P, ¬Q), ¬P), Q].
// Or(0): → [And(P, ¬Q), Q, ¬P].
// And(principal=0, left_partition={2}) splits And(P, ¬Q):
//   LEFT  = entries[2] then P  = [¬P, P]  — AxiomLit(0, 1).
//   RIGHT = entries[1] then ¬Q = [Q, ¬Q]  — AxiomLit(0, 1).
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
    prog.instrs.push_back(lkr::And{{}, 0, {2}});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
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
    prog.instrs.push_back(lkr::Or{{}, 0});                    // instr 0
    prog.instrs.push_back(lkr::Forall{{}, 1, /*eigen=*/0});   // instr 1: binds TermRef{1} → f_0
    prog.instrs.push_back(lkr::Exists{{}, 0, TermRef{1}});    // instr 2
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});           // instr 3

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
// Cross-system theorem reuse: prove a theorem in ND, then close from LKR
// via CloseByLemma. The op closes if some entry equals NNF(theorem).
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
    prog.instrs.push_back(lkr::CloseByLemma{{}, AxiomRef{thm.value()}, "my_thm"});

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
// One: ⊢ ¬⊥ closes via the truth-constant rule. Build the goal directly
// from the builder so it's exactly ¬⊥ (parsing keywords for ⊤/⊥ aren't
// part of the surface syntax).
// =========================================================================
void test_one_closes_truth_literal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaBuilder b(ctx);
    FormulaHandle bot     = b.make_bottom();
    FormulaHandle not_bot = b.make_not(bot);

    LKRProgram prog;
    prog.claim_name = "one_closes";
    prog.instrs.push_back(lkr::One{{}, /*idx=*/0});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, not_bot, p));
}

// =========================================================================
// One rejection: a non-truth-literal entry must not close.
// Goal P → P (NNF: ¬P ∨ P) — applying One(0) on the disjunction is bogus.
// =========================================================================
void test_one_rejects_non_truth_literal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "one_reject";
    prog.instrs.push_back(lkr::One{{}, 0});  // entry is ¬P ∨ P, not ¬⊥

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Exchange: swap entries before AxiomLit. Goal P → P (NNF ¬P ∨ P).
// Or(0) → [¬P, P]. Exchange(0,1) → [P, ¬P]. AxiomLit(0,1) closes.
// =========================================================================
void test_exchange_swaps_entries() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "exchange_swap";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Exchange{{}, 0, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Exchange with i==j is a no-op (must not error and must not change state).
// =========================================================================
void test_exchange_self_is_noop() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "exchange_noop";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Exchange{{}, 1, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Exchange OOB rejection.
// =========================================================================
void test_exchange_rejects_oob() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "exchange_oob";
    prog.instrs.push_back(lkr::Or{{}, 0});            // [¬P, P]
    prog.instrs.push_back(lkr::Exchange{{}, 0, 5});   // 5 is OOB

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Weakening appends a new formula to the sequent. Goal P → P (NNF ¬P ∨ P).
// Or(0) → [¬P, P]. Weakening(Q) → [¬P, P, Q]. AxiomLit(0,1) still closes.
// =========================================================================
void test_weakening_appends() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaHandle Q    = parse_root(ctx, "Q");

    LKRProgram prog;
    prog.claim_name = "weakening";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Weakening{{}, Q});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Contraction merges two equal entries. Goal P → P (NNF ¬P ∨ P).
// Or(0) → [¬P, P]. Weakening(P) → [¬P, P, P]. Contraction(1,2) → [¬P, P].
// AxiomLit(0,1) closes.
// =========================================================================
void test_contraction_merges_duplicates() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");
    FormulaHandle P    = parse_root(ctx, "P");

    LKRProgram prog;
    prog.claim_name = "contraction_merge";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Weakening{{}, P});
    prog.instrs.push_back(lkr::Contraction{{}, 1, 2});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_OK(v.verify(ctx, goal, p));
}

// =========================================================================
// Contraction rejects when the two entries differ. After Or(0) the sequent
// is [¬P, P]; entries[0] != entries[1], so Contraction(0,1) must fail.
// =========================================================================
void test_contraction_rejects_unequal() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "contraction_reject";
    prog.instrs.push_back(lkr::Or{{}, 0});             // [¬P, P]
    prog.instrs.push_back(lkr::Contraction{{}, 0, 1}); // unequal

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Contraction rejects when i == j (the rule requires two distinct indices).
// =========================================================================
void test_contraction_rejects_same_index() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "P -> P");

    LKRProgram prog;
    prog.claim_name = "contraction_same_index";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Contraction{{}, 0, 0});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// Forall freshness rejection: if the eigenvariable already occurs free in
// another entry, the rule must fail. We can't construct that scenario from
// the surface syntax cleanly, but we can exercise the order-of-validation
// fix by binding eigen=0 twice in a row over the same goal — the second
// Forall sees an entry containing f_0 (the body instantiated by the first
// Forall) and must reject.
//
// Goal: (∀x. P(x)) ∨ (∀y. Q(y))  (already a positive disjunction; no NNF
// flip needed because all subformulas are positive).
//
// Initial: [(∀x.P) ∨ (∀y.Q)].
// Or(0) → [∀x.P, ∀y.Q].
// Forall(0, eigen=0) → [P(f_0), ∀y.Q].
// Forall(1, eigen=0) → tries to use f_0 again, but f_0 is free in entry 0
// (P(f_0)), so freshness fails.
// =========================================================================
void test_forall_eigen_freshness_rejection() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. P(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "(forall x. P(x)) | (forall y. Q(y))");

    LKRProgram prog;
    prog.claim_name = "forall_freshness";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Forall{{}, 0, /*eigen=*/0});
    prog.instrs.push_back(lkr::Forall{{}, 1, /*eigen=*/0});

    Proof p{System::LKR, std::move(prog)};
    lkr::LKRVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =========================================================================
// CloseByLemma with arity-N schema bindings: prove an arity-1 schema in
// ND, then close an LKR goal via CloseByLemma supplying a lambda binding.
// schema_resolve must substitute P(x) → eq(x, x) at every site in the
// schema body before the close-formula is matched against the goal.
// =========================================================================
void test_close_by_lemma_arity_n_schema() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        schema unary_self_impl [P(1)]: forall x. (P(x) -> P(x))

        proof unary_self_impl:
            fix x
            h_assume = assume P(x)
            h_impl = implies_intro h_assume
            h_all = forall_intro h_impl
            qed h_all
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    EXPECT_OK(rt.execute_all_proofs(parsed.value()));

    auto& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "forall x. (eq(x, x) -> eq(x, x))");

    // Build a SchemaBinding payload manually: bind P to \y. eq(y, y).
    // We can't easily construct an AST without going through the parser,
    // so we parse a helper sentence and steal its formula AST.
    auto helper = parse_with_proofs(
        R"(claim _h: forall x. (P -> P)
           proof _h:
               h = schema_inst unary_self_impl { P: \y. eq(y, y) }
               qed h
        )",
        ctx);
    if (helper.proofs.empty() || helper.proofs[0].steps.empty()) {
        ++g_failed; return;
    }
    const auto& step0 = helper.proofs[0].steps[0];
    if (step0.kind != ParsedProofStep::Kind::SchemaInst ||
        step0.schema_bindings.size() != 1) {
        ++g_failed; return;
    }

    LKRProgram prog;
    prog.claim_name = "lkr_arity_n_close";
    SchemaInstData inst_data;
    inst_data.schema   = SchemaRef{"unary_self_impl"};
    inst_data.bindings = step0.schema_bindings;
    prog.instrs.push_back(lkr::CloseByLemma{{}, std::move(inst_data)});

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
    test_one_closes_truth_literal();
    test_one_rejects_non_truth_literal();
    test_exchange_swaps_entries();
    test_exchange_self_is_noop();
    test_exchange_rejects_oob();
    test_weakening_appends();
    test_contraction_merges_duplicates();
    test_contraction_rejects_unequal();
    test_contraction_rejects_same_index();
    test_forall_eigen_freshness_rejection();
    test_close_by_lemma_arity_n_schema();
    test_unfinished_proof_rejected();
    test_dispatcher_routes_lkr();

    std::cout << "lkr_verifier_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
