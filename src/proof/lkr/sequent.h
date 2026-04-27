#pragma once

// Sequent representation for LKR (Hughes 2019, "First-order proofs without
// syntax", §11). One-sided, multi-conclusion, classical.
//
// A sequent is a finite sequence ϕ₁, …, ϕₙ of formulas (n ≥ 0). All formulas
// are in negation normal form (NNF): only PredicateInstance, Compound{Not,
// PredicateInstance, _}, Compound{And/Or, …, …}, Quantified{Forall/Exists,
// …}, Bottom, and SchemaVar (positive or negated) appear as subterms.
// Implies, Iff, and double-negation are eliminated by the NNF pass at
// translation time.
//
// Soundness reading: a sequent ϕ₁, …, ϕₙ is provable iff its disjunction
// ϕ₁ ∨ … ∨ ϕₙ is classically valid. The empty sequent is unprovable.
//
// Memory: a SequentRecord holds a vector of FormulaHandles. Most rules
// transform the sequent O(width); width is bounded by the proof's
// instruction count, which is small in practice.

#include "../../core/formula.h"

#include <vector>

namespace logic::proof::lkr {

struct SequentRecord {
    std::vector<FormulaHandle> entries;

    bool empty() const { return entries.empty(); }
    size_t size() const { return entries.size(); }
};

}  // namespace logic::proof::lkr
