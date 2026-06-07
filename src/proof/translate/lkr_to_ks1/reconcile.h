#pragma once

// ≡-reconciliation for LKR→KS1 (CUT_HANDLING_ROADMAP phase K6.1b).
//
// The LK1→KS1 translation repeatedly needs to reshape the "current formula"
// from one ∧/∨-bracketing to an ≡-equivalent one (HSW 2021 §II eq (2)): an Or
// rule appends its second disjunct to the END of the sequent, so the sequent's
// (Γ)=disjunction must be re-associated/commuted to put it in place; the And
// rule's switch sequence leaves a tail that must likewise be reconciled.
//
// `equiv_steps(fb, from, to)` returns a list of single-equation `Eqv` steps
// (CommAnd/CommOr/AssocAnd/AssocOr) that, replayed from `from`, yield exactly
// `to` — provided `from ≡ to` under the PROPOSITIONAL fragment (assoc + comm of
// ∧/∨; quantifier shifts not handled, mirroring `ks1::equiv`'s scope). It works
// by canonicalizing both to `ks1::canonicalize`'s normal form and composing the
// path to `from`'s canon with the inverse of the path to `to`'s canon. Returns
// an error if `from ≢ to` (the produced steps fail to reach `to`).

#include "src/core/formula.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_to_ks1 {

util::Result<std::vector<logic::proof::ks1::Step>> equiv_steps(
    FormulaBuilder& fb, FormulaHandle from, FormulaHandle to);

// Reorder the LEFT-associated ∨-chain of `from` (the sequent entries) into the
// order `to`, where `to` is a permutation of `from` BY HANDLE (same multiset of
// entries, different positions). Emits a minimal adjacent-transposition bubble
// (one CommOr, or an AssocOr/CommOr/AssocOr triple, per swap) — O(inversions)
// steps, vs. `equiv_steps`'s full canonicalize-and-invert (O(n²)). This is the
// fast path for `RExchange`/`RWeaken`, whose reconciliation is a pure entry
// permutation. Replaying the result from denote(from) yields denote(to).
// Precondition (checked): `to` is a permutation of `from` by handle.
util::Result<std::vector<logic::proof::ks1::Step>> reorder_steps(
    FormulaBuilder& fb, const std::vector<FormulaHandle>& from,
    const std::vector<FormulaHandle>& to);

// Contraction (CUT_HANDLING_ROADMAP K6.3b). Emit the KS1 resource steps that
// rewrite `X ∨ X` into `X` — medials (M/MForall/MExists) pushing the ∨ down
// through X's ∧/∀/∃ structure, then atomic contraction Ac at each literal pair
// (with ≡-reshaping to pair the matching atoms). Replaying the result from
// `make_or(X, X)` yields `X`. This is the core of the resource phase Φ2's
// contraction (HSW §IX); `tr(RDuplicate)` reshapes the doubled sequent so the
// two copies are adjacent, then applies this.
util::Result<std::vector<logic::proof::ks1::Step>> contract_steps(
    FormulaBuilder& fb, FormulaHandle x);

// Re-bracket `cur` — a ∨-tree whose opaque leaves (stopping at any handle in
// `entries`) are exactly `entries` left-to-right — into the fully LEFT-associated
// denote(entries), via AssocOr right-rotations. Entries are OPAQUE: a ∨-valued
// entry is never descended into, so this is O(#entries) structural rotations, not
// a leaf canonicalization (the cheap alternative to `equiv_steps` when the caller
// already knows the entry boundaries, e.g. RAnd's switch tail (…∨P)∨Q with P,Q
// grouped). Self-checks by replay; errors if it cannot reach denote(entries)
// (e.g. a spine ∨-node aliases an entry handle) so the caller can fall back.
util::Result<std::vector<logic::proof::ks1::Step>> reassoc_left_steps(
    FormulaBuilder& fb, FormulaHandle cur,
    const std::vector<FormulaHandle>& entries);

}  // namespace logic::proof::translate::lkr_to_ks1
