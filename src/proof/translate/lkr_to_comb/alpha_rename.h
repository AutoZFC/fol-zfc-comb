#pragma once

// AlphaRename — pre-pass that rewrites an LKR program's Forall eigens
// (and any fix-var references baked into Weakening/Cut formula handles)
// so they match the canonical binder vars that Fograph will allocate
// when building the §15-augmented goal.
//
// Background (LKR_TO_COMB_DESIGN.md §7.5, Option B):
//   NDtoLKR emits Forall(eigen=K) where K is ND's trace fix-var.
//   Fograph(augmented_goal) allocates a fresh var per binder occurrence
//   in pre-order. The two var allocators are independent, so they
//   diverge whenever a cut formula introduces a new binder whose
//   trace-allocated index differs from Fograph's pre-order index. The
//   resulting CombProof fails CombVerifier's link check because the
//   linked atoms' args carry different fix-var indices.
//
//   This pre-pass closes the gap by reading the canonical binder var
//   for each Forall (from Fograph(augmented_goal) at the binder's
//   canonical position) and rewriting the program to match.
//
// Substitution scope:
//   - Forall.eigen                  → canonical_var
//   - Cut.cut_formula (FormulaHandle): walk and substitute every
//                                       Term::fixed(old) → Term::fixed(new)
//                                       for each (old, new) in the map.
//   - Weakening.formula             → same substitution.
//   - Other ops (Exists, AxiomLit, CloseByLemma, And, Or, Exchange,
//     Contraction, One) carry no free fix-vars to rewrite. Exists's
//     witness TermRef resolves through term_env, which automatically
//     picks up the renamed Forall eigen.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <unordered_map>

namespace logic::proof::translate::lkr_to_comb {

// Compute the rename map and the renamed program in a single call. The
// caller already has the original program; on success this returns a
// new program ready to feed into the remainder of the pipeline.
//
// Pre-pass uses cut_augment + sequent_replay + Fograph against the
// *original* program to determine, per Forall op, what canonical var
// Fograph allocates for that op's principal binder. This works because
// Fograph's allocation order depends only on the augmented goal's
// structure, not on its atom args' fix-vars.
util::Result<Program<lkr::Instr>> alpha_rename_to_canonical(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& in);

}  // namespace logic::proof::translate::lkr_to_comb
