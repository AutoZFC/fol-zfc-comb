#pragma once

// ProofRewriter — Leisenring's constructive ε-elimination, realised as
// a structural witness substitution.
//
// **Math content**: Leisenring's 2nd ε-theorem states that for ε-free
// axioms T' and ε-free goal G:
//
//     T' ⊢_{ND-with-ε} G    iff    T' ⊢_{ND-without-ε} G
//
// The forward construction (which this module implements): given an
// ND-with-ε proof π of G from T', produce an ND-without-ε proof π' of G
// from T'. The construction replaces each ε-introduction (`iota_elim`
// here) with the ε-axiom's underlying ∃-elimination, substituting the
// fresh witness fix-var for the ε-term throughout the scope.
//
// **Path D composition**: this module assumes axioms are already
// ε-free (Path D normalises them at load via `eliminate_descriptions`).
// The translator's scope is then exactly the proofs whose iota usage
// fits Leisenring's construction — those that verify under post-Path-D
// ND. Proofs that pattern-match the pre-Path-D iota-bearing axiom shape
// won't verify under post-Path-D ND and are outside Leisenring's scope
// (they require uniqueness assumptions Path D explicitly rejects).
//
// **Algorithm**:
//   1. Each `iota_elim ∃x.B(x)` is replaced by `exists_elim ∃x.B(x), w`
//      where `w` is a fresh fix-var bound at this instruction.
//   2. Subsequent TermRef references to the iota_elim's instruction
//      naturally resolve to `w` (the IR uses instr-index TermRefs;
//      changing the bound term changes all references).
//   3. The new exists_elim scope must close LIFO before the enclosing
//      block. A scope-closing `exists_intro` is inserted just before the
//      enclosing block's closer; the closer's `body` StepRef is
//      overridden to point at the inserted closer's result.
//   4. All StepRef / TermRef fields are remapped through `old_to_new`
//      (the inserted closers shift subsequent indices by 1 each).
//   5. `Program::step_index` (name → idx map) is rewritten accordingly.
//
// **Soundness**: the output verifies under ND iff the construction is
// correct. NDVerifierGate runs the ND verifier on the output and
// surfaces any incorrectness as an I-4 error.
//
// **Completeness**: for any input that verifies under (post-Path-D) ND
// and uses iota only via `iota_elim` + `forall_elim` / `exists_intro`
// (the standard ε-elimination pattern), the rewrite produces a valid
// ND-without-ε proof. This is Leisenring's theorem, constructively
// realised.

#include "elimination_plan.h"
#include "iota_inventory.h"

#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

namespace logic::proof::translate::iota_elim {

class ProofRewriter {
public:
    static util::Result<Program<nd::Instr>> apply(
        const Program<nd::Instr>& in,
        const EliminationPlan&    plan);
};

}  // namespace logic::proof::translate::iota_elim
