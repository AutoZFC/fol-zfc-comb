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

}  // namespace

int main() {
    test_p1_one_minimal();

    std::cerr << "interpret_tree_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
