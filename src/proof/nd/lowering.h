#pragma once

// Lowering: ParsedProof (parser output) -> NDProgram (typed IR).
//
// This is the only place where the parser's string-keyed proof step
// representation is converted into the typed ND instruction variant.
// Failure modes:
//   * unknown rule name (Kind::Rule with rule_name not matching any op)
//   * argument arity mismatch
//   * step-name reference to an unbound name
//   * Qed not present
//
// Lowering does NOT consult GlobalContext beyond what is needed to validate
// the proof's structural well-formedness (e.g. no axiom/theorem lookup;
// that's deferred to the verifier).

#include "../../parser/parser.h"
#include "../../util/error.h"
#include "../proof.h"

namespace logic::proof::nd {

util::Result<NDProgram> lower(const ParsedProof& parsed);

}  // namespace logic::proof::nd
