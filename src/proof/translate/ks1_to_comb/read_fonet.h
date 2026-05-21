#pragma once

// KS1 linear core Φ1  →  comb fonet  (HSW 2021 Thm 33) — Track 2 phase K4.
//
// Given an MLS1^X derivation Φ1 from t (⊤) to A' (the linear core produced by
// decompose::split), build the fonet [[Φ1]] = ⟨[[A']], ∼Φ1⟩ with its dualizer
// (paper §VIII-A, Thm 33):
//   - underlying fograph  = comb::Fograph(A');
//   - links ∼Φ1           = the atom pairs that meet in the ai-rule instances
//                           of Φ1 (Thm 19 obs. (i): each `ai : t / a∨ā` makes
//                           one link {a, ā});
//   - dualizer δΦ1        = the substitution collected from the ∃-rule
//                           instances (`∃ : A[x/t] / ∃x.A` records x ↦ t).
//
// Provenance problem: core::FormulaHandle is interned, so two structurally
// equal atoms share a handle and occurrence identity is lost. We therefore
// REPLAY Φ1 on a tagged mirror tree (starting from a single ⊤ node, since the
// linear core always starts at t), tracking atom-occurrence tags, binder tags,
// the ai link pairs, and ∃ witnesses. We then reconstruct A' from the mirror
// in fograph pre-order — cross-checking it equals the real replay of Φ1 — and
// map tags to the pre-order vertex indices / binder var_indices that
// comb::Fograph assigns. This makes the read-off provably consistent with the
// derivation.
//
// SCOPE (K4): supports the MLS1^X rules that occur in linear cores —
// ForallUnit, ai, t(unit), mix, s, ∃, and the ≡ equations. PRECONDITION:
// Φ1.top is ⊤ and every step is an MLS1^X rule (as produced by split).

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

namespace logic::proof::ks1_to_comb {

// The fonet read off Φ1, together with the fograph it lives over. `target` is
// [[A']] (comb::Fograph(A')); `fonet` is the source, defined over the SAME
// vertex set (so the identity fibration maps it onto `target`). A CombProof
// {source=fonet, target, fibration=identity} should pass CombVerifier's
// well-formedness + fonet phases.
struct FonetReadoff {
    comb::Fonet   fonet{};
    comb::Fograph target{};   // [[A']]
    FormulaHandle a_prime{};  // A'
};

// Read the fonet off the MLS1^X linear core `phi1` (t ⟶ A'). Error if a
// precondition fails or an unsupported rule is encountered.
util::Result<FonetReadoff> read_fonet(FormulaBuilder& fb,
                                      const logic::proof::ks1::Derivation& phi1);

}  // namespace logic::proof::ks1_to_comb
