#pragma once

// KS1 decomposition normal form (HSW 2021 Thm 17) — Track 2 phase K3.
//
// Thm 17: every KS1 derivation t ⟶ A can be reorganized into the fixed phase
// order (top = t, bottom = A):
//
//     {∀, ai, t}   ── axioms / units      ⎫
//     {s, mix, ≡}  ── linear              ⎬  MLS1^X "linear core" Φ1 (t ⟶ A')
//     {∃}          ── instantiation       ⎭
//     {m, m∀, m∃, ≡} ── medial            ⎫
//     {ac, c∀}     ── contraction         ⎬  resource phase Φ2 (A' ⟶ A)
//     {w, w∀, ≡}   ── weakening           ⎭
//
// The split point A' = A3 (after the whole MLS1^X part). The bridge (Thm 19)
// reads the fonet off Φ1 (K4) and the skew bifibration off Φ2 (K5).
//
// `≡` lives in the linear, medial, AND weakening phases — so it is admissible
// in either half and never forces a particular phase. The MLS1^X/resource
// boundary is therefore located at the first *resource-only* step (a non-≡
// rule from {m, m∀, m∃, ac, c∀, w, w∀}). This module does NOT reorganize an
// arbitrary derivation into decomposed form (the constructive Thm 17 via
// rule-permutation is deferred); it CHECKS decomposed form and SPLITS a
// derivation already in it.

#include "src/core/formula.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

namespace logic::proof::ks1 {

// Thm 17 phases, numbered top→bottom (≡ is flexible: it may sit in 2, 4 or 6).
enum class Phase { Axioms = 1, Linear = 2, Inst = 3, Medial = 4,
                   Contraction = 5, Weakening = 6 };

// Rule classification. Eqv (≡) is in BOTH fragments.
bool is_mls1x(Rule r);     // {∀, ai, t, s, mix, ∃, ≡}
bool is_resource(Rule r);  // {w, w∀, ac, c∀, m, m∀, m∃, ≡}

// True iff the derivation's steps are in Thm 17 decomposed order: every MLS1^X
// step precedes every resource-only step, and the non-≡ phase numbers are
// non-decreasing within each half.
bool is_decomposed(const Derivation& d);

// Constructive Thm 17: reorganize `d` into decomposed form by phase-sorting its
// steps via replay-verified adjacent transpositions (DECOMPOSE_DESIGN.md). Each
// swap exactly preserves the derivation's effect; any pair that does not commute
// cleanly (binder crossing, weakening-absorption cases, AC-chain merges) is left
// in place — so the result may be only PARTIALLY decomposed and `split` still
// gates on `is_decomposed`. Returns a derivation with the same top/bottom.
util::Result<Derivation> decompose(FormulaBuilder& fb, const Derivation& d);

// The MLS1^X linear core Φ1 (t ⟶ A'), the split formula A', and the resource
// phase Φ2 (A' ⟶ A), of a decomposed derivation.
struct Split {
    Derivation    phi1{};    // top ⟶ A'   (MLS1^X)
    FormulaHandle a_prime{}; // A'
    Derivation    phi2{};    // A' ⟶ bottom (resource)
};

// Split a decomposed derivation at the MLS1^X/resource boundary, computing A'
// by replaying Φ1. Error if `d` is not in decomposed form or fails to replay.
util::Result<Split> split(FormulaBuilder& fb, const Derivation& d);

}  // namespace logic::proof::ks1
