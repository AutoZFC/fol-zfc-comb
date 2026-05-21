#pragma once

// KS1 resource phase Φ2  →  skew bifibration  (HSW 2021 Lemma 41) — K5.
//
// Given a resource derivation Φ2 in {w, w∀, ac, c∀, m, m∀, m∃, ≡} from A'
// (the linear-core conclusion) to B (the goal), the induced vertex map
// ⌊Φ2⌋ : [[A']] → [[B]] is a skew bifibration (Lemma 41). It is the
// composition of the per-step induced maps:
//   - m, ≡            : identity (same vertices, restructured);
//   - w, w∀           : injection — the weakened-in vertices of the conclusion
//                       are NOT in the image (uncovered, paper §11.1 W);
//   - ac, c∀, m∀, m∃  : many-to-one — the two contracted atoms / binders of the
//                       premise map to the single one of the conclusion
//                       (contraction = the fibration being non-injective).
//
// We compute it by replaying Φ2 on a tagged mirror of A' whose vertices carry
// their [[A']] pre-order index; contraction rules union the source-index sets,
// weakening adds empty-set vertices. Reconstructing B in fograph pre-order
// (cross-checked == the real replay of Φ2) assigns each B vertex its index and
// yields fibration[s] = the B-vertex carrying source vertex s.
//
// Combined with read_fonet (K4), build_comb_proof assembles the full
// CombProof {source = fonet over [[A']], target = [[B]], fibration = ⌊Φ2⌋}
// for a decomposed KS1 derivation — the Thm 19 image.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

#include <vector>

namespace logic::proof::ks1_to_comb {

// The induced map ⌊Φ2⌋ : V_{[[A']]} → V_{[[B]]} (total on the source), the
// goal fograph [[B]], and B itself.
struct SkewReadoff {
    std::vector<size_t> fibration{};  // source A'-vertex → target B-vertex
    comb::Fograph       target{};     // [[B]]
    FormulaHandle       b{};          // B (the goal)
};

// Read the skew bifibration off the resource phase `phi2` (A' ⟶ B). `a_prime`
// must equal phi2.top. Error on a precondition failure or unsupported rule.
util::Result<SkewReadoff> read_skew(FormulaBuilder& fb,
                                    const logic::proof::ks1::Derivation& phi2);

// Full bridge (Thm 19): decompose a KS1 derivation t ⟶ A into (Φ1, A', Φ2),
// read the fonet off Φ1 and the skew bifibration off Φ2, and assemble the
// CombProof. The result should pass all CombVerifier phases against d.bottom.
util::Result<comb::CombProof>
build_comb_proof(FormulaBuilder& fb, const logic::proof::ks1::Derivation& d);

}  // namespace logic::proof::ks1_to_comb
