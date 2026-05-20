// Tests for the paper-exact (Hughes §11.1) LKR→Comb fold, interpret_tree.
//
// Brought up one phase at a time alongside walk.cpp:
//   P1: leaf rules (One; AxiomLit exercised once Or lands at P2).

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/comb/verifier.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_to_comb/cut_augment.h"
#include "src/proof/translate/lkr_to_comb/interpret_tree.h"
#include "src/proof/translate/lkr_to_comb/sequent_replay.h"
#include "src/proof/translate/lkr_to_comb/tree.h"
#include "src/runtime/runtime.h"

#include <iostream>
#include <string>

using namespace logic;
using namespace logic::proof;
namespace l2c = logic::proof::translate::lkr_to_comb;

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

// Drive interpret_tree end-to-end and verify the resulting CombProof
// against `goal` with the real CombVerifier.
util::ResultStatus run(GlobalContext& ctx, FormulaHandle goal,
                       const LKRProgram& prog) {
    FormulaBuilder fb(ctx);
    FormulaHandle  goal_nnf = fb.to_nnf(goal);

    auto tree = l2c::rebuild_tree(prog);
    if (tree.is_error()) return tree.error();

    l2c::CutAugmentation cut_aug;  // empty: cut-free programs only
    auto replay = l2c::replay_sequents(fb, goal_nnf, prog, cut_aug);
    if (replay.is_error()) return replay.error();

    auto cp = l2c::interpret_tree(ctx, goal_nnf, prog, *tree.value(),
                                  replay.value());
    if (cp.is_error()) return cp.error();

    comb::CombVerifier v;
    Proof p{System::COMB, cp.value()};
    return v.verify(ctx, goal, p);
}

// P1: One leaf. goal = ¬⊥; LKR = [One(0)] closes the single-entry
// initial sequent directly. The CombProof is the minimal fonet •1
// mapped onto the single One vertex of G(¬⊥).
void test_p1_one_minimal() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle  goal = parse_root(ctx, "~_|_");

    LKRProgram prog;
    prog.claim_name = "one_minimal";
    prog.instrs.push_back(lkr::One{{}, 0});

    EXPECT_OK(run(ctx, goal, prog));
}

// P2: Or + AxiomLit. goal = p → p (NNF: ¬p ∨ p). LKR = [Or(0),
// AxiomLit(0,1)]. Or splits the goal into [¬p, p]; AxiomLit closes the
// dual pair. Exercises both the Or remap and the (P1) AxiomLit leaf
// end-to-end.
void test_p2_self_implication() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle  goal = parse_root(ctx, "p -> p");

    LKRProgram prog;
    prog.claim_name = "self_impl";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    EXPECT_OK(run(ctx, goal, prog));
}

// P2: Or with a middle entry, exercising the non-identity Or remap
// (θ moves to the end of H, jumping over a middle entry). goal =
// (p → p) ∨ q  =  (¬p ∨ p) ∨ q. NNF flattens to ¬p ∨ p ∨ q.
// LKR: Or(0) on the outer ∨ → [¬p ∨ p, q]; Or(0) on ¬p∨p →
// [¬p, q, p] (p appended past the middle entry q); AxiomLit(0, 2).
void test_p2_or_with_middle_entry() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle  goal = parse_root(ctx, "(p -> p) | q");

    LKRProgram prog;
    prog.claim_name = "or_middle";
    prog.instrs.push_back(lkr::Or{{}, 0});   // [¬p ∨ p, q]
    prog.instrs.push_back(lkr::Or{{}, 0});   // [¬p, q, p]
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 2});

    EXPECT_OK(run(ctx, goal, prog));
}

// P2: Exchange. goal = p → p (¬p ∨ p). LKR: Or(0) → [¬p, p];
// Exchange(0,1) → [p, ¬p]; AxiomLit(0,1) closes the swapped pair.
void test_p2_exchange() {
    Runtime rt;
    rt.load("axiom dummy: forall x. p(x)");
    GlobalContext& ctx = rt.context();
    FormulaHandle  goal = parse_root(ctx, "p -> p");

    LKRProgram prog;
    prog.claim_name = "exchange";
    prog.instrs.push_back(lkr::Or{{}, 0});
    prog.instrs.push_back(lkr::Exchange{{}, 0, 1});
    prog.instrs.push_back(lkr::AxiomLit{{}, 0, 1});

    EXPECT_OK(run(ctx, goal, prog));
}

}  // namespace

int main() {
    test_p1_one_minimal();
    test_p2_self_implication();
    test_p2_or_with_middle_entry();
    test_p2_exchange();

    std::cerr << "interpret_tree_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
