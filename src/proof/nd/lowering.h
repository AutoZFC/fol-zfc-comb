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
//   * Use(name) where name resolves to neither an axiom nor a theorem in ctx
//     (axiom/theorem name resolution to SentenceHandle happens here per the
//     "no string hacks in IR" rule — IR Use ops carry SentenceHandle, not
//     names; see src/proof/ir.h::AxiomRef).

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/util/error.h"
#include "src/proof/proof.h"

namespace logic::proof::nd {

util::Result<NDProgram> lower(const ParsedProof& parsed, const GlobalContext& ctx);

}  // namespace logic::proof::nd
