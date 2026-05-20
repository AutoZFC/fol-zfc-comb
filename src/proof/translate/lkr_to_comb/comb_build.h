#pragma once

// comb_build — CombProof builder helpers for the paper-exact §11.1 fold.
//
// See PAPER_EXACT_DESIGN.md. These construct the per-node target fograph
// G(Φ(Γ)) and provide the index arithmetic the canonical homomorphisms
// need.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

// G(Φ(Γ)) for a sequent Γ = φ1,…,φn.  Φ(Γ) = φ1 ∨ (φ2 ∨ … ∨ φn), and
// since ∨ = + the result is the disjoint union of the per-entry
// fographs laid out in sequent order (Hughes §11 intro + Def. 3.1).
//
// PRECONDITION: every entry is in NNF (LKR sequents are NNF).
comb::Fograph build_sequent_fograph(FormulaBuilder&                   fb,
                                    const std::vector<FormulaHandle>& entries);

// Start vertex index of each entry's contiguous vertex block within
// build_sequent_fograph(entries). offsets.size() == entries.size();
// offsets[0] == 0; offsets[i] == sum of vertex counts of entries < i.
// A trailing total-count is appended (offsets.size() == n+1) so the
// block of entry i is [offsets[i], offsets[i+1]).
std::vector<size_t> entry_vertex_offsets(
    FormulaBuilder&                   fb,
    const std::vector<FormulaHandle>& entries);

// Number of fograph vertices in G(φ) (atoms + binders), layout-invariant.
size_t fograph_vertex_count(FormulaBuilder& fb, FormulaHandle phi);

}  // namespace logic::proof::translate::lkr_to_comb
