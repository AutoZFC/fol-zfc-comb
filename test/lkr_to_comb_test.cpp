// LKRtoComb tests — translator phases brought up one at a time.
//
// Phase 4 partial: AxiomLit leaf + Or/Exchange/Weakening linear ops.
// And/Cut/Forall/Exists/Contraction/CloseByLemma deferred to later phases.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_to_comb/lkr_to_comb.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>

using namespace logic;
using namespace logic::proof;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_OK(expr) do {                                                  \
    auto _r = (expr);                                                          \
    if (_r.ok()) { ++g_passed; } else {                                        \
        std::cerr << "FAIL: " #expr " expected Ok, got: "                      \
                  << _r.error().to_string() << " at "                          \
                  << __FILE__ << ":" << __LINE__ << "\n";                      \
        ++g_failed;                                                            \
    }                                                                          \
} while (0)

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    SentenceHandle sh = parse_sentence(s, ctx);
    return sh.get().root();
}

// Simplest case: excluded middle `p → p` (NNF: ¬p ∨ p).
// LKR program: Or(0); AxiomLit(0, 1).
// Combinatorial proof:
//   target = G(¬p ∨ p) = {•¬p, •p} no edges
//   source.fonet = {u_0, u_1} with link {0, 1}, no edges, empty dualizer
//   fibration = [0, 1]
void test_lkr_to_comb_self_implication() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. p(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "p -> p");

    LKRProgram prog;
    prog.claim_name = "self_impl";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// One leaf (LKR_TO_COMB_DESIGN.md §4.2): close a goal whose entry is
// the truth literal ¬⊥ via the One(idx) closing op.
//
// Smallest case: goal = ¬⊥. LKR = [One(0)]. CombProof: source = one
// vertex (kind=One, unlinked), target = G(¬⊥) = single One vertex,
// fibration [0]. No links, no edges, empty dualizer.
void test_lkr_to_comb_one_minimal() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "~_|_");

    LKRProgram prog;
    prog.claim_name = "one_minimal";
    prog.instrs.push_back(lkr::One{{}, 0});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// One with sibling disjunct: goal = p | ¬⊥. The ¬⊥ entry alone closes
// the goal regardless of p (Weakening-style; p stays uncovered in
// source). LKR = [Or(0); One(1)] — Or splits the goal into [p, ¬⊥],
// then One(1) closes via the truth literal at idx 1.
void test_lkr_to_comb_one_with_sibling() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "p | ~_|_");

    LKRProgram prog;
    prog.claim_name = "one_with_sibling";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::One{{}, 1});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// And rule (worked example B from WALKTHROUGH.md): prove (p ∧ q) ⇒ (q ∧ p).
// NNF: (¬p ∨ ¬q) ∨ (q ∧ p). LKR:
//   Or(0)            → [(¬p ∨ ¬q), (q ∧ p)]
//   Or(0)            → [¬p, (q ∧ p), ¬q]
//   And(1, [2])      → LEFT=[¬q, q]; RIGHT=[¬p, p]
//   AxiomLit(0, 1)   → close LEFT
//   AxiomLit(0, 1)   → close RIGHT
// Combinatorial proof: fonet with 4 vertices, 2 links, 1 cross-edge
// between u_q (in LEFT portion) and u_p (in RIGHT portion).
void test_lkr_to_comb_and_commute() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. p(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "(p & q) -> (q & p)");

    LKRProgram prog;
    prog.claim_name = "and_commute";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::And{{}, 1, {2}});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// Forall: prove ∀x. (p(x) ∨ ¬p(x)). LKR program:
//   Forall(0, eigen=0)   → [p(f_0) ∨ ¬p(f_0)]
//   Or(0)                → [p(f_0), ¬p(f_0)]
//   AxiomLit(0, 1)       → close
// Combinatorial proof: 3 source vertices (u_p, u_¬p, b_x), link {0,1},
// binding edges {b_x → u_p, b_x → u_¬p}.
void test_lkr_to_comb_forall_em() {
    Runtime rt;
    auto loaded = rt.load("axiom dummy: forall x. p(x)");
    assert(loaded.ok());
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "forall x. (p(x) | ~p(x))");

    LKRProgram prog;
    prog.claim_name = "forall_em";
    prog.instrs.push_back(lkr::Forall{{}, 0, /*eigen=*/0});
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// Cut with both sides closed via the original sequent (cut formula
// "weakened in", so the cut block is uncovered in the source fonet).
// Goal: p → p. Cut(p ∨ ¬p) as a no-op-style cut. Both LEFT and RIGHT
// close via Or + AxiomLit on the original ¬p ∨ p disjunction.
//
// Augmented goal: (¬p ∨ p) ∨ ((p ∨ ¬p) ∧ (¬p ∧ p)).
// The cut block is uncovered in the source (P_L = P_R = ∅, both weak).
void test_lkr_to_comb_cut_no_use() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "p -> p");
    FormulaHandle cut_formula = parse_root(ctx, "p | ~p");

    LKRProgram prog;
    prog.claim_name = "cut_no_use";
    {
        lkr::Cut c{};
        c.cut_formula = cut_formula;
        prog.instrs.emplace_back(std::move(c));
    }
    // LEFT after Cut: [¬p ∨ p, p ∨ ¬p].
    // Or(0): [¬p, p ∨ ¬p, p]. AxiomLit pairs ¬p (idx 0) with p (idx 2).
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});
    // RIGHT after Cut: [¬p ∨ p, ¬p ∧ p].
    // Or(0): [¬p, ¬p ∧ p, p]. AxiomLit pairs ¬p (idx 0) with p (idx 2).
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb pass(ctx, goal, lemmas);
    EXPECT_OK(pass.apply(prog));
}

// Cut + CloseByLemma round-trip. The lemma is `p → p` (= the same
// formula as the outer goal); its CombProof is built first via the
// trivial Or+AxiomLit program. The outer proof cuts on the lemma's
// formula and closes LEFT via CloseByLemma, then closes RIGHT via
// standard structural decomposition.
void test_lkr_to_comb_cut_with_lemma() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    rt.load("axiom lemma_pp: p -> p");  // register so LKR can lookup
    GlobalContext& ctx = rt.context();
    FormulaHandle goal = parse_root(ctx, "p -> p");

    // ---- Step 1: build the lemma's CombProof.
    LKRProgram lemma_prog;
    lemma_prog.claim_name = "lemma_pp_proof";
    lemma_prog.instrs.push_back(lkr::Or{{}, 0});
    lemma_prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LemmaCombProofs empty;
    translate::lkr_to_comb::LKRtoComb lemma_pass(ctx, goal, empty);
    auto lemma_cp_r = lemma_pass.apply(lemma_prog);
    if (!lemma_cp_r.ok()) {
        std::cerr << "FAIL: lemma translation: "
                  << lemma_cp_r.error().to_string() << "\n";
        ++g_failed; return;
    }

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    lemmas["lemma_pp"] = lemma_cp_r.value();

    // ---- Step 2: outer proof uses Cut(p → p) + CloseByLemma + RIGHT closer.
    // LKR:
    //   Cut(p → p)             LEFT [¬p ∨ p, ¬p ∨ p], RIGHT [¬p ∨ p, ¬(¬p ∨ p)=p ∧ ¬p]
    //   CloseByLemma(lemma_pp) close LEFT
    //   Or(0)                  RIGHT becomes [¬p, p ∧ ¬p, p]
    //   And(1, [0])            principal=(p ∧ ¬p); partition [0] sends ¬p to LEFT.
    //                          LEFT [¬p, p], RIGHT [p, ¬p]
    //   AxiomLit(0, 1)         close LEFT
    //   AxiomLit(0, 1)         close RIGHT
    LKRProgram outer;
    outer.claim_name = "cut_with_lemma";
    {
        lkr::Cut c{};
        c.cut_formula = goal;  // p → p
        outer.instrs.emplace_back(std::move(c));
    }
    {
        lkr::CloseByLemma cbl{};
        cbl.axiom = AxiomRef{"lemma_pp"};
        outer.instrs.emplace_back(std::move(cbl));
    }
    outer.instrs.push_back(lkr::Or{{}, 0});
    outer.instrs.push_back(lkr::And{{}, 1, {0}});
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LKRtoComb outer_pass(ctx, goal, lemmas);
    EXPECT_OK(outer_pass.apply(outer));
}

// CloseByLemma dualizer remap (LKR_TO_COMB_DESIGN.md §4.11):
// regression test for empty dualizer. The existing
// test_lkr_to_comb_cut_with_lemma already covers this; this is the
// row that previously took the empty-dualizer early-return path.
// Kept passing means the σ remap implementation doesn't regress.
//
// (Already exercised by test_lkr_to_comb_cut_with_lemma above; no new
// test needed for this row — the regression is implicit.)

// CloseByLemma with a forall lemma (LKR_TO_COMB_DESIGN.md §4.11
// test 2). Exercises the σ build: lemma's universal binder vertex
// must pair with an outer-target universal binder at the
// position-remapped vertex. Dualizer is empty (lemma has no ∃), so
// σ_T isn't exercised here — only the binder-kind precondition check.
//
// Strategy: build the lemma's CombProof via the existing ND→Comb
// pipeline (test_end_to_end_nd_to_comb_forall_self_impl proves
// `∀x.(p(x) → p(x))`). Register it. Then an outer ND proof of the
// same formula via `use lemma_fa_pp` translates through NDtoLKR to
// a Cut + CloseByLemma + emit_close pattern.
void test_lkr_to_comb_cut_with_forall_lemma() {
    // The lemma's CombProof must target G(lemma_formula_nnf) exactly,
    // not the §15-augmented form. Lemmas built via the full ND→Comb
    // pipeline target their augmented goal (extra positions from any
    // internal Cuts), which doesn't match the outer cut formula's
    // slice — that's an open obligation tracked separately. For now,
    // use a Cut-free hand-crafted LKR program so augmented == original.
    //
    // Lemma: forall x. (p(x) | ~p(x)) — same NNF shape as forall x.
    // (p(x) -> p(x)) but expressed positively. Hand-crafted LKR:
    //   Forall(0, eigen=0)   [body becomes (p(0) | ~p(0))]
    //   Or(0)                [split: p(0), ~p(0)]
    //   AxiomLit(0, 1)       [close]
    // Empty dualizer (no ∃). Source has one ∀ binder vertex.
    Runtime rt;
    rt.load("axiom lemma_fa_em: forall x. (p(x) | ~p(x))");
    GlobalContext& ctx = rt.context();

    FormulaHandle lemma_goal = parse_root(ctx, "forall x. (p(x) | ~p(x))");
    comb::CombProof lemma_cp_value;
    {
        LKRProgram lemma_prog;
        lemma_prog.claim_name = "lemma_fa_em_proof";
        lemma_prog.instrs.push_back(lkr::Forall{{}, 0, /*eigen=*/0});
        lemma_prog.instrs.push_back(lkr::Or{{}, 0});
        lemma_prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

        translate::lkr_to_comb::LemmaCombProofs empty;
        translate::lkr_to_comb::LKRtoComb lemma_lc(ctx, lemma_goal, empty);
        auto cp = lemma_lc.apply(lemma_prog);
        if (!cp.ok()) {
            std::cerr << "lemma lkr_to_comb: " << cp.error().to_string() << "\n";
            ++g_failed; return;
        }
        lemma_cp_value = cp.value();
    }

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    lemmas["lemma_fa_em"] = lemma_cp_value;

    // ---- Outer proof: cut on the lemma's formula, close LEFT via
    // CloseByLemma, decompose RIGHT structurally.
    //
    // Goal = `forall x. (p(x) | ~p(x))`. Initial sequent [goal_nnf].
    //   Cut(lemma_formula)  → LEFT [goal, lemma], RIGHT [goal, ¬lemma]
    //   CloseByLemma        → closes LEFT
    //   On RIGHT [forall x.(p∨¬p), exists x.(¬p∧p)]:
    //   Forall(p=0, eigen=v1)              → [(p(v1) | ¬p(v1)), exists x.(¬p∧p)]
    //   Exists(p=1, witness=Forall ref)     → [(p(v1) | ¬p(v1)), (¬p(v1) ∧ p(v1))]
    //   Or(0)                               → [p(v1), (¬p(v1) ∧ p(v1)), ¬p(v1)]
    //   And(p=1, L=[0])                     → LEFT [p(v1), ¬p(v1)], RIGHT [¬p(v1), p(v1)]
    //   AxiomLit(0, 1)                      close LEFT
    //   AxiomLit(0, 1)                      close RIGHT
    FormulaHandle goal = parse_root(ctx, "forall x. (p(x) | ~p(x))");
    LKRProgram outer;
    outer.claim_name = "cut_with_forall_lemma";
    {
        lkr::Cut c{};
        c.cut_formula = lemma_goal;
        outer.instrs.emplace_back(std::move(c));
    }
    {
        lkr::CloseByLemma cbl{};
        cbl.axiom = AxiomRef{"lemma_fa_em"};
        outer.instrs.emplace_back(std::move(cbl));
    }
    outer.instrs.push_back(lkr::Forall{{}, /*principal=*/0, /*eigen=*/1});
    {
        lkr::Exists e{};
        e.principal = 1;
        e.witness = TermRef{2};  // the Forall above is at op index 2
        outer.instrs.emplace_back(std::move(e));
    }
    outer.instrs.push_back(lkr::Or{{}, /*principal=*/0});
    outer.instrs.push_back(lkr::And{{}, /*principal=*/1, /*left_partition=*/{0}});
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LKRtoComb outer_lc(ctx, goal, lemmas);
    EXPECT_OK(outer_lc.apply(outer));
}

// CloseByLemma with an exists-containing lemma (LKR_TO_COMB_DESIGN.md
// §4.11 test 3). The lemma has BOTH ∀ and ∃ binders, so its
// CombProof's dualizer is non-empty. This is the test that exercises
// the full σ + σ_T remap path: both dualizer keys (lemma ∃ var →
// outer ∃ var) and image terms (Fixed(lemma_∀_var) → Fixed(outer_∀_var))
// must be renamed.
//
// Lemma: forall y. (¬p(y) ∨ exists x. p(x)) — i.e., the trivial
// `∀y. (p(y) → ∃x. p(x))` after NNF.
// Hand-crafted LKR for the lemma (Cut-free so target = G(formula)):
//   Forall(0, eigen=0)              [∀y, body = ¬p(0) ∨ ∃x.p(x)]
//   Or(0)                            [split: ¬p(0), ∃x.p(x)]
//   Exists(1, witness=TermRef{0})    [body = p(Fixed(0))]
//   AxiomLit(0, 1)                   [close ¬p(0) and p(0)]
// CombProof.source has 4 vertices, link {0,1}, cograph (2,1) from
// the ∃ Case B, dualizer {∃-var: Fixed(∀-eigen)} — non-empty.
void test_lkr_to_comb_cut_with_exists_lemma() {
    Runtime rt;
    rt.load("axiom lemma_fa_ex: forall y. (~p(y) | exists x. p(x))");
    GlobalContext& ctx = rt.context();

    FormulaHandle lemma_goal =
        parse_root(ctx, "forall y. (~p(y) | exists x. p(x))");
    comb::CombProof lemma_cp_value;
    {
        LKRProgram lemma_prog;
        lemma_prog.claim_name = "lemma_fa_ex_proof";
        lemma_prog.instrs.push_back(lkr::Forall{{}, /*p=*/0, /*eigen=*/0});
        lemma_prog.instrs.push_back(lkr::Or{{}, /*p=*/0});
        {
            lkr::Exists e{};
            e.principal = 1;
            e.witness   = TermRef{0};  // the Forall is op #0
            lemma_prog.instrs.emplace_back(std::move(e));
        }
        lemma_prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

        translate::lkr_to_comb::LemmaCombProofs empty;
        translate::lkr_to_comb::LKRtoComb lemma_lc(ctx, lemma_goal, empty);
        auto cp = lemma_lc.apply(lemma_prog);
        if (!cp.ok()) {
            std::cerr << "lemma lkr_to_comb: " << cp.error().to_string() << "\n";
            ++g_failed; return;
        }
        lemma_cp_value = cp.value();
    }

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    lemmas["lemma_fa_ex"] = lemma_cp_value;

    // Outer goal = same lemma formula. Outer LKR cuts on the lemma,
    // CloseByLemma closes LEFT, RIGHT decomposes the negation
    // structurally (∀y on goal entry, ∃y on neg-goal entry, Or, And
    // split, then nested Forall+Exists+AxiomLit for the inner pair).
    //
    // NNF(¬lemma) = exists y. (p(y) ∧ forall x. ¬p(x)).
    //
    // op#0: Cut(lemma_formula)
    // op#1: CloseByLemma(lemma_fa_ex)              — closes LEFT
    // op#2: Forall(p=0, eigen=10)                   on RIGHT, principal = goal
    // op#3: Exists(p=1, witness=TermRef{2})         on RIGHT, principal = ¬goal
    // op#4: Or(p=0)                                 split (¬p(y) ∨ ∃x.p(x))
    // op#5: And(p=1, L=[0])                         split (p(y) ∧ ∀x.¬p(x))
    // op#6: AxiomLit(0, 1)                          close And's LEFT: [¬p(y), p(y)]
    // op#7: Forall(p=1, eigen=11)                   And's RIGHT: ∀x.¬p(x)
    // op#8: Exists(p=0, witness=TermRef{7})         And's RIGHT: ∃x.p(x)
    // op#9: AxiomLit(0, 1)                          close
    FormulaHandle goal = parse_root(ctx, "forall y. (~p(y) | exists x. p(x))");
    LKRProgram outer;
    outer.claim_name = "cut_with_exists_lemma";
    {
        lkr::Cut c{};
        c.cut_formula = lemma_goal;
        outer.instrs.emplace_back(std::move(c));
    }
    {
        lkr::CloseByLemma cbl{};
        cbl.axiom = AxiomRef{"lemma_fa_ex"};
        outer.instrs.emplace_back(std::move(cbl));
    }
    outer.instrs.push_back(lkr::Forall{{}, /*p=*/0, /*eigen=*/10});
    {
        lkr::Exists e{};
        e.principal = 1;
        e.witness   = TermRef{2};
        outer.instrs.emplace_back(std::move(e));
    }
    outer.instrs.push_back(lkr::Or{{}, /*p=*/0});
    outer.instrs.push_back(lkr::And{{}, /*p=*/1, /*L=*/{0}});
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});
    outer.instrs.push_back(lkr::Forall{{}, /*p=*/1, /*eigen=*/11});
    {
        lkr::Exists e{};
        e.principal = 0;
        e.witness   = TermRef{7};
        outer.instrs.emplace_back(std::move(e));
    }
    outer.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    translate::lkr_to_comb::LKRtoComb outer_lc(ctx, goal, lemmas);
    EXPECT_OK(outer_lc.apply(outer));
}

// End-to-end pipeline: ND → ND(iota-free) → LKR → CombProof. The ND
// proof uses no axioms (only built-in rules), so no lemma registry
// entries are needed. Goal: prove `p → p` via assume + implies_intro.
//
// Steps:
//   1. Lower the ND text to NDProgram (parser/lowerer).
//   2. ND verifies → InputGate of NDtoLKR passes.
//   3. NDtoLKR emits an LKRProgram (Cut for the IMPLIES block + emit_close
//      pattern). LKRVerifier accepts via the OutputGate.
//   4. LKRtoComb consumes the LKRProgram, builds a CombProof, CombVerifier
//      accepts via the OutputGate.
void test_end_to_end_nd_to_comb_self_impl() {
    // Quantifier-free goal — avoids the open issue of LKR-eigen vs
    // Fograph-canonical var divergence for cut formulas with binders.
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim pp: p -> p

        proof pp:
            h_a = assume p
            h_i = implies_intro h_a
            qed h_i
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_r = nd::lower(parsed.value().proofs[0]);
    if (!nd_r.ok()) {
        std::cerr << "lower: " << nd_r.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = std::move(nd_r).unwrap();
    auto claim = rt.context().find_claim("pp");
    if (!claim.has_value()) {
        std::cerr << "claim not found\n"; ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    // Step 1: ND → LKR.
    translate::nd_to_lkr::NDtoLKR ndl(rt.context(), goal);
    auto lkr_r = ndl.apply(nd_prog);
    if (!lkr_r.ok()) {
        std::cerr << "nd_to_lkr: " << lkr_r.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Step 2: LKR → Comb. No lemmas referenced (no Use ops in the ND
    // proof → no CloseByLemma in the LKR output).
    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb lc(rt.context(), goal, lemmas);
    auto cp_r = lc.apply(lkr_r.value());
    if (!cp_r.ok()) {
        std::cerr << "lkr_to_comb: " << cp_r.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

// Quantified end-to-end. Goal: forall x. (p(x) → p(x)). Exercises the
// alpha-rename pre-pass: NDtoLKR emits Forall(eigen=K) where K is ND's
// trace fix-var; LKRtoComb's canonical target allocates a different
// fresh var for the cut formula's binder. The pre-pass renames K to
// the canonical var so the fibration's atom args match the canonical
// target's labels (LKR_TO_COMB_DESIGN.md §7.5 fix).
void test_end_to_end_nd_to_comb_forall_self_impl() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim pp_q: forall x. (p(x) -> p(x))

        proof pp_q:
            fix x
            h_a = assume p(x)
            h_i = implies_intro h_a
            h_f = forall_intro h_i
            qed h_f
    )");
    if (!parsed.ok()) {
        std::cerr << "load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_r = nd::lower(parsed.value().proofs[0]);
    if (!nd_r.ok()) {
        std::cerr << "lower: " << nd_r.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = std::move(nd_r).unwrap();
    auto claim = rt.context().find_claim("pp_q");
    if (!claim.has_value()) {
        std::cerr << "claim not found\n"; ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR ndl(rt.context(), goal);
    auto lkr_r = ndl.apply(nd_prog);
    if (!lkr_r.ok()) {
        std::cerr << "nd_to_lkr: " << lkr_r.error().to_string() << "\n";
        ++g_failed; return;
    }

    translate::lkr_to_comb::LemmaCombProofs lemmas;
    translate::lkr_to_comb::LKRtoComb lc(rt.context(), goal, lemmas);
    auto cp_r = lc.apply(lkr_r.value());
    if (!cp_r.ok()) {
        std::cerr << "lkr_to_comb: " << cp_r.error().to_string() << "\n";
        ++g_failed; return;
    }
    ++g_passed;
}

}  // namespace

int main() {
    test_lkr_to_comb_self_implication();
    test_lkr_to_comb_one_minimal();
    test_lkr_to_comb_one_with_sibling();
    test_lkr_to_comb_and_commute();
    test_lkr_to_comb_forall_em();
    test_lkr_to_comb_cut_no_use();
    test_lkr_to_comb_cut_with_lemma();
    test_lkr_to_comb_cut_with_forall_lemma();
    test_lkr_to_comb_cut_with_exists_lemma();
    test_end_to_end_nd_to_comb_self_impl();
    test_end_to_end_nd_to_comb_forall_self_impl();

    std::cout << "lkr_to_comb_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
