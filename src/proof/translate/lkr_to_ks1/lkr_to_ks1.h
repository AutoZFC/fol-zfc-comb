#pragma once

// K6 — cut-free LKR (Deriv tree) → KS1 derivation.
//
// The last missing link of the LKR→KS1→comb pipeline (CUT_HANDLING_ROADMAP
// phase K6). Takes a CUT-FREE, LEMMA-FREE `lkr_cut_elim::Deriv` (the structured
// sequent-proof tree produced by `eliminate_cuts`) and produces a *decomposed*
// `ks1::Derivation` (t ⟶ goal) that the existing KS1→comb bridge
// (`ks1_to_comb::build_comb_proof`) consumes to emit a combinatorial proof for
// `CombVerifier`.
//
// An LKR sequent ⊢ Γ corresponds to a KS1 derivation t ⟶ ⋁Γ. The translation
// emits the linear (MLS1^X) steps Φ1 first, then the resource steps Φ2, so the
// result is already in Thm-17 decomposed form (no reorganizer needed).
//
// SCOPE (K6.0 skeleton): only the simplest cut-free proof — ⊢ a∨ā via an
// axiom under a single Or — is translated, to validate the end-to-end
// integration (Deriv → Derivation → build_comb_proof → CombVerifier). The
// general LK1→KS1 construction (HSW 2021 §VII) lands in K6.1+; every shape not
// yet handled returns an explicit "not yet implemented" error.

#include "src/core/formula.h"
#include "src/proof/ks1/derivation.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_ks1 {

// Translate a cut-free, lemma-free Deriv with a single-formula (closed) goal
// sequent into a decomposed KS1 derivation t ⟶ goal. Precondition: `cutfree`
// contains no RCut and no RLemma (guaranteed post-eliminate_cuts for tractable
// theorems). Errors on any shape outside the current phase's scope.
util::Result<logic::proof::ks1::Derivation> lkr_to_ks1(
    FormulaBuilder& fb, const lkr_cut_elim::Deriv& cutfree);

}  // namespace logic::proof::translate::lkr_to_ks1
