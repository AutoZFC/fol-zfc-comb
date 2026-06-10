#pragma once

// Direct LKR → combinatorial proof fold (Hughes 2019 §11.1).
//
// The SECOND, parallel back-end track (alongside LKR→KS1→comb). Consumes the
// SAME cut-free, lemma-free `lkr_cut_elim::Deriv` tree that `lkr_to_ks1` walks,
// but folds it directly into a `comb::CombProof` — building the fonet (linear
// core) and skew bifibration (resource map) as ONE object per node, per the
// §11.1 per-rule table. Because the input is cut-free + lemma-free (Stage-3
// cut-elim and lemma internalization ran upstream), the §15 cut-augmentation,
// summand tracking, and `CloseByLemma` machinery of the old flat-program walk
// all VANISH: this is a clean bottom-up `std::visit` fold returning a
// (fonet, fibration, entries) triple per node, mirroring `lkr_to_ks1.cpp`.
//
// The fibration is carried SYMBOLICALLY as (entry-index, offset-within-entry)
// and materialized to absolute G(goal) vertex indices only at the root — the
// "localize at root" analogue of the KS1 env-threading. Block offsets are
// trivial prefix sums because (Γ) = a left-associated ∨ is a disjoint vertex-
// block concatenation in Fograph's pre-order layout (no cograph edges across ∨).
//
// Trust boundary: the translator is UNTRUSTED. The output is checked by
// `comb::CombVerifier`'s four phases against `cutfree`'s goal. A translator bug
// surfaces as an output-gate rejection, never as silent unsoundness.
//
// SCOPE (phased): Phase 1 covers the switch-free propositional fragment
// (RAx, ROr, RExchange). RAnd/RWeaken, quantifiers, and contraction each return
// an explicit "not yet implemented" error. See LKR_TO_COMB_DESIGN.md (§11.1
// per-rule table) for the full construction.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_comb {

// Translate a cut-free, lemma-free Deriv with a single-formula (closed) goal
// sequent directly into a combinatorial proof of that goal. Precondition:
// `cutfree` contains no RCut and no RLemma. Errors on any shape outside the
// current phase's scope.
util::Result<logic::proof::comb::CombProof> lkr_to_comb(
    FormulaBuilder& fb, const lkr_cut_elim::Deriv& cutfree);

}  // namespace logic::proof::translate::lkr_to_comb
