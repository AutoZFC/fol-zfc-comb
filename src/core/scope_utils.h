#pragma once

// Free-function utilities for inspecting fixed-variable usage and
// description-body accessibility within a formula.
//
// These are extracted from ProofStack so that proof systems other than
// natural deduction (e.g. LKR) can perform eigenvariable side-condition
// checks without depending on ND's scope-stack machinery.
//
// Soundness contract: these are pure inspection functions over the formula
// term language (PredicateInstance / Compound / Quantified / SentenceHandle
// / SchemaVar). They mutate nothing; they allocate nothing; they perform
// the same recursive walk that ProofStack used to perform internally. The
// only change versus the original implementation is that
// description_body_accessible now takes its scope predicate as a parameter
// instead of consulting ProofStack::find_scope_for_term directly — making
// it usable from any verifier that can answer "is this fixed var live?".

#include "formula.h"

#include <functional>

namespace logic {

// True iff the formula tree rooted at `h` contains a free occurrence of
// the fixed variable Term::fixed(var_idx). Used by:
//   * ND ExistsIntro mode B (witness-occurrence check)
//   * LKR ForallR / ExistsL eigenvariable freshness check (Phase 5)
//
// Schema variables and sentences (closed formulas) are treated as
// containing no free fixed vars — matching the existing ND semantics.
bool formula_contains_fixed_var(FormulaHandle const& h, var_index var_idx);

// True iff every fixed variable appearing free in `h` satisfies the caller-
// supplied `is_in_scope` predicate. Used by:
//   * ND iota_elim: every fixed var in the description body must be live
//   * Future verifiers that need an analogous well-formedness check
//
// is_in_scope: callback returning true if the given fixed-var index is
// considered "in scope" by the calling verifier. Generalised over what
// "in scope" means (ND's open FixVarScopes, LKR's currently-bound
// eigenvariables, etc.) so this utility is verifier-agnostic.
bool description_body_accessible(
    FormulaHandle const& h,
    std::function<bool(var_index)> const& is_in_scope);

}  // namespace logic
