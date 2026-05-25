#pragma once

// Deriv structural invariants — the convention enforcer.
//
// Spec: STAGE3_RESET_PLAN.md §4 (Step 1). Validates every node's
// rule-specific positional invariants. Called from build() to guarantee
// that build-produced Derivs satisfy the invariants, and from cut-elim
// tests at top-of-test to guarantee hand-built Derivs don't silently
// pick an inverted convention (the 05-27 try_dead_cut_W class of bug).
//
// Conventions that are load-bearing for cut-elim and explicitly checked
// here:
//
//   - RWeaken{added, child}: child.conclusion = node.conclusion ++ {added}.
//     Child is bigger (post-W); node is smaller (pre-W).
//
//   - RContract{i, j, child}: child.conclusion = node.conclusion with
//     position j removed; child is smaller; node has the duplicate.
//     Requires concl[i] == concl[j].
//
//   - RExchange{i, j, child}: child.conclusion = node.conclusion with
//     positions i and j swapped; sizes equal.
//
//   - RCut{cut_formula, left, right} (ADDITIVE convention, per deriv.h
//     line 67–69): left.conclusion = node.conclusion ++ {cut_formula};
//     right.conclusion = node.conclusion ++ {NNF dual}. Both children
//     bigger by one.
//
//   - RAnd{principal, left_partition, left, right}: principal indexes a
//     compound ∧ formula in node.conclusion; left_partition is a subset
//     of [0..|Γ|) \ {principal} with no duplicates; left.conclusion =
//     (partition picks from node.conclusion) ++ {φ}; right.conclusion =
//     (complement picks) ++ {ψ}.
//
//   - ROr{principal, child}: principal indexes a compound ∨; child =
//     node.conclusion with [principal] replaced by φ, ++ {ψ}.
//
//   - RForall / RExists{principal, eigen|witness, child}: principal
//     indexes a quantified formula of the matching kind; child has the
//     same shape as node EXCEPT at [principal] (the body instantiation
//     is NOT re-derived here — checked by LKRVerifier on emit).
//
//   - RAx{a, b}: positions in range, distinct. NNF duality of the
//     literals is deferred to LKRVerifier (avoids carrying a
//     FormulaBuilder through validate).
//
//   - ROne{idx}: position in range. Truth-literal identity deferred.
//
//   - RLemma{target, source_name}: non-empty Γ. Goal/target match
//     deferred to LKRVerifier.
//
// Semantic invariants NOT checked here (deferred to LKRVerifier on the
// emitted program): NNF duality of axiom literals, exact body of ∀/∃
// instantiation, eigenvariable freshness, and lemma target conclusion
// match. Validate's job is the *convention* layer that no test can
// silently subvert.

#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_cut_elim {

util::ResultStatus validate(const Deriv& root);

}  // namespace logic::proof::translate::lkr_cut_elim
