#pragma once

// KS1 derivation checker (HSW 2021 Fig. 6) — Track 2 phase K2.
//
// `check` replays a Derivation top-down: starting from `top`, it applies each
// Step (verifying the redex at the step's context matches the rule's premise
// schema, then rewriting to the conclusion). On success the final formula must
// equal `bottom`. Every accepted derivation is a valid KS1 derivation, so by
// Thm 16 (soundness) `bottom` is valid whenever `top` is ⊤.
//
// The checker is independent of the comb layer (paper §V/§VI). It uses a
// FormulaBuilder for De Bruijn surgery and formula (re)construction.

#include "src/core/formula.h"
#include "src/proof/ks1/derivation.h"
#include "src/util/error.h"

namespace logic::proof::ks1 {

// Replay `steps` (applied top-down) starting from `top`, verifying each is a
// valid Fig. 6 rule instance at its context. Returns the resulting formula.
// `check` is replay + the final-equals-bottom test; `split` (decompose.h)
// reuses this to compute the linear-core conclusion A'.
util::Result<FormulaHandle> replay(FormulaBuilder& fb, FormulaHandle top,
                                   const std::vector<Step>& steps);

// Verify `d` is a valid KS1 derivation from d.top to d.bottom. Ok() on success.
util::ResultStatus check(FormulaBuilder& fb, const Derivation& d);

}  // namespace logic::proof::ks1
