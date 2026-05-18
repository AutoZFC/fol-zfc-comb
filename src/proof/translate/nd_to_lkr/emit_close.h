#pragma once

// emit_close — close the current LKR open goal by structural dual
// decomposition of two NNF-dual sequent entries.
//
// Per ND_TO_LKR_DESIGN.md §3.5, this is the ONE place the translator
// closes a goal. Per-rule schemas may emit structural moves (Or, And,
// Cut, Forall, Exists, Weakening, Contraction, Exchange) to re-shape
// the sequent into a form where two entries are NNF-dual; then they
// hand off to emit_close.
//
// **Precondition:** `shadow.entries[pos_a]` and `shadow.entries[pos_b]`
// are NNF formulas with `a ⊥ b`  (i.e., NNF(¬a) ≡ b structurally).
// Precondition violation is a translator bug; emit_close returns Error.
//
// **Action:** appends LKR ops to `out` that, when the verifier executes
// them on the goal `shadow` represents, close that goal (popping it
// from the verifier's open-goals stack). The shadow is mutated to
// match the verifier's intermediate state during the recursion, but
// since the goal is closed at the end, the caller discards the shadow.
//
// **Generic over rule provenance.** emit_close walks NNF structure
// only. It never pattern-matches rule-specific shapes (no "this is an
// Iff expansion" branches). This makes the deleted translator's bug
// class #1 (close_iff_intro RIGHT-branch swap) structurally impossible.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/util/error.h"

#include "sequent_shadow.h"

#include <cstddef>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

// Context carried through emit_close's recursion: builder for formula
// operations and a counter to allocate fresh eigenvariables that don't
// correspond to any ND-side fix.
struct EmitCloseContext {
    FormulaBuilder& builder;
};

util::ResultStatus emit_close(
    EmitCloseContext&         cc,
    SequentShadow&            shadow,
    size_t                    pos_a,
    size_t                    pos_b,
    std::vector<lkr::Instr>&  out);

}  // namespace logic::proof::translate::nd_to_lkr
