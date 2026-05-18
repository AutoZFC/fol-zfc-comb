#pragma once

// SequentShadow — translator-side mirror of the verifier's current open
// goal, used to compute LKR op operands (positions, witnesses, eigens).
//
// Per ND_TO_LKR_DESIGN.md §3.3, each recursive frame in the cut-spine
// driver owns its own SequentShadow. Branching ops (Cut, multiplicative
// And) DO NOT mutate the parent's shadow — they construct child shadows
// by cloning + selecting + remapping. This makes the "stale index after
// multiplicative-And" failure mode (old bug class #4) structurally
// impossible.
//
// The shadow is metadata; it carries no soundness obligation by itself.
// Soundness comes from the OutputGate running LKRVerifier on the emitted
// program. The shadow only has to be self-consistent enough that the
// emitted ops are accepted.

#include "src/core/formula.h"
#include "src/proof/ir.h"

#include <cstdint>
#include <unordered_map>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

struct SequentShadow {
    // Current sequent entries, in verifier-order. Stable within a single
    // recursive call frame (the only ops that mutate are: Or replaces
    // principal in place then appends; Forall/Exists replace principal in
    // place; Weakening / Cut append; Exchange swaps two entries).
    std::vector<FormulaHandle> entries;

    // Position of NNF(¬F_k) in `entries`, for each ND step k whose Cut
    // is in scope at this frame. Cleared by branching ops on the child
    // side that doesn't keep them.
    std::unordered_map<uint32_t, size_t> step_to_neg_idx;

    // For each ND step k that BINDS a TermRef (Fix, ExistsElim), the
    // corresponding LKR TermRef + the concrete Term it resolves to.
    //
    // - TermRef: the instr index of the LKR Forall op that bound the
    //   eigen, used as the `witness` field of LKR Exists ops.
    // - Term: the same Term::fixed(eigen) value, used to compute formula
    //   substitutions in the shadow (since the shadow tracks formulas,
    //   not the verifier's term_env).
    struct TermBinding {
        TermRef lkr_ref;
        Term    value;
    };
    std::unordered_map<uint32_t, TermBinding> lkr_term_for;

    // Convenience accessors.
    size_t size() const { return entries.size(); }
    size_t append(FormulaHandle f) {
        entries.push_back(f);
        return entries.size() - 1;
    }
};

}  // namespace logic::proof::translate::nd_to_lkr
