#pragma once

// LemmaInliner — pre-pass that splices lemma LKR programs into the
// outer LKR program at each CloseByLemma point (Strategy A; see
// LKR_TO_COMB_DESIGN.md §4.12).
//
// Rationale: Hughes §15 "keeps cuts" by augmenting the goal. The same
// principle scales to lemma composition: inline the lemma's LKR ops
// at the CloseByLemma site, and the lemma's cuts propagate naturally
// into the combined LKR program. The outer's augmented goal then
// includes the lemma's cut blocks; the lemma's source fibrates into
// that combined target without any CombProof-level composition.
//
// This dissolves the Cut-free-lemma restriction of Strategy B (§4.11).
//
// Splicing rewrites each lemma op:
//   - position references (principal, lit_a, lit_b, idx, i, j,
//     left_partition[]) shift by an offset that tracks the lemma's
//     position in the outer sequent;
//   - Forall.eigen renames to a fresh var (preserves LKR freshness);
//   - Cut.cut_formula / Weakening.formula has free Fixed terms
//     substituted per the eigen rename;
//   - Exists.witness (a TermRef) shifts by the spliced Forall's
//     combined-program op index;
//   - Nested CloseByLemma in lemmas recursively splices.
//
// Branching ops (And, Cut) require per-subgoal offset tracking. For
// And: LEFT subgoal's offset resets to 0 (the partition contains only
// lemma indices, so outer-stuff goes to RIGHT); RIGHT inherits parent.
// For Cut: both subgoals inherit parent. Linear ops: offset unchanged.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <string>
#include <unordered_map>

namespace logic::proof::translate::lkr_to_comb {

// Lemma registry: lemma name → LKR program proving the lemma formula.
// Each program must standalone-verify under LKRVerifier against its
// formula (the caller is responsible for this precondition).
using LemmaPrograms = std::unordered_map<std::string, Program<lkr::Instr>>;

// Splice every CloseByLemma in `outer` with the corresponding lemma's
// LKR ops. On success, the returned program has no CloseByLemma ops
// (assuming all lemmas are in the registry; missing lemmas surface as
// errors).
//
// `initial_goal_nnf` is the outer's goal in NNF (needed for computing
// the initial sequent size for offset tracking).
util::Result<Program<lkr::Instr>> inline_lemmas(
    FormulaBuilder&             builder,
    FormulaHandle               initial_goal_nnf,
    const Program<lkr::Instr>&  outer,
    const LemmaPrograms&        lemmas);

}  // namespace logic::proof::translate::lkr_to_comb
