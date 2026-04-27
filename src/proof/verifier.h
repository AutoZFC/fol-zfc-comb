#pragma once

// Verifier — abstract interface for per-system proof checkers.
//
// Each concrete verifier (NDVerifier in Phase 3, LKRVerifier in Phase 5)
// is an interpreter of a typed instruction stream. It owns no state across
// invocations: every verify() call constructs its own private Session.
//
// Soundness contract:
//   * The verifier must not register theorems or modify GlobalContext's
//     named registries. The dispatcher (ProofRunner, Phase 4) is the only
//     site of theorem registration and uses the dispatcher-resolved
//     SentenceHandle for the claim_name.
//   * verify() returns Ok if and only if the proof's instructions, executed
//     in order, derive the goal_formula under the system's success
//     predicate Φ. On failure, returns an Error with diagnostic context.

#include "ir.h"
#include "proof.h"

#include "../core/formula.h"
#include "../util/error.h"

#include <string>
#include <unordered_set>

namespace logic::proof {

class Verifier {
public:
    virtual ~Verifier() = default;

    // Which system this verifier handles. Used by ProofRunner to route.
    virtual System system() const = 0;

    // Verify the proof against the given goal formula. The goal_formula is
    // pre-resolved by the dispatcher: for a regular claim, it is the claim
    // sentence's root; for a schema, it is the schema body. The verifier
    // does not need to distinguish — it only confirms a derivation of
    // goal_formula exists under the proof's instructions.
    //
    // ctx is used read-mostly: axiom/theorem/schema lookups via find_known
    // and find_schema. The verifier must not call ctx.add_theorem,
    // ctx.add_axiom, ctx.mark_schema_proven, or any other registry mutator.
    virtual util::ResultStatus verify(
        GlobalContext& ctx,
        FormulaHandle  goal_formula,
        const Proof&   proof) = 0;

    // The set of axiom/theorem/schema names consulted during the most
    // recent verify() call (e.g. via Use / UseTheorem / SchemaInst). The
    // dispatcher reads this after a successful verify to populate the
    // proof-dependency graph. Must be cleared at the start of each verify.
    virtual const std::unordered_set<std::string>& last_used_names() const = 0;
};

}  // namespace logic::proof
