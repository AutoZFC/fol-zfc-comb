#pragma once

// build_target — per-hypothesis target construction for the F2 walk.
//
// Hughes §11.1 defines each per-rule operation against a hypothesis
// target G(H_i) = G(ψ_1) + G(ψ_2) + … where the ψ_k are the entries of
// the hypothesis sequent. This is just parallel composition of each
// entry's fograph — and since cograph_edges of `∨` are empty, it
// coincides structurally with Fograph(ψ_1 ∨ ψ_2 ∨ … ∨ ψ_n).
//
// The translator needs both the fograph itself AND per-entry vertex
// position vectors (needed by per-rule operations to embed child
// targets into parent targets and to identify the V_{G(ψ_principal)}
// witness portion).

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/util/error.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

struct SequentTarget {
    // Fograph of the parallel composition G(entries[0]) + … + G(entries[n-1]).
    // source_formula is set to the left-associated disjunction
    // (entries[0] ∨ entries[1] ∨ … ∨ entries[n-1]) so it is a valid
    // FormulaHandle; callers that need the root's target to compare
    // structurally against an externally-given augmented goal can swap
    // this field at the root.
    comb::Fograph target;

    // entry_positions[k] = vertex indices in `target` for the k-th
    // entry, in the order Fograph allocates them (pre-order of that
    // entry's structure).
    std::vector<std::vector<size_t>> entry_positions;
};

// Build the per-hypothesis target for a sequent. `entries` must be
// non-empty (the empty sequent is unprovable so cannot arise as a
// conclusion sequent). Each entry must be in NNF.
util::Result<SequentTarget> build_sequent_target(
    FormulaBuilder&                       builder,
    const std::vector<FormulaHandle>&     entries);

}  // namespace logic::proof::translate::lkr_to_comb
