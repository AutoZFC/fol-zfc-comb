#pragma once

// Literal helpers for LKR.
//
// In NNF, an "atomic literal" is either a positive atom (PredicateInstance
// or SchemaVar) or its negation (Compound{Not, atom, _}). This header
// exposes:
//
//   * is_atomic_literal — predicate.
//   * is_dual           — true iff two formulas are dual literals (one is
//                          +L, the other is −L for the same atom L).
//   * is_top_literal    — true iff a formula is the syntactic top
//                          ¬⊥ used as a placeholder for ⊤ (NNF leaves
//                          it as Compound{Not, Bottom, _}).
//
// Soundness contract: these functions inspect formula structure only;
// they allocate nothing and mutate nothing.

#include "../../core/formula.h"

namespace logic::proof::lkr {

bool is_atomic_literal(FormulaHandle h);
bool is_dual(FormulaHandle a, FormulaHandle b);
bool is_top_literal(FormulaHandle h);

}  // namespace logic::proof::lkr
