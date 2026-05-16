#pragma once

// Verifier — abstract interface for per-system proof checkers.
//
// Each concrete verifier consumes a Proof artefact and reports a polynomial-
// time verdict on whether it witnesses validity of `goal_formula`. The
// artefact's presentation is system-dependent:
//   * NDVerifier and LKRVerifier interpret typed instruction streams.
//   * CombVerifier checks structural conditions on a graph object
//     (a fonet + fograph + skew bifibration) — no instructions to interpret.
// The interface is agnostic to that choice: a proof is information that
// the verifier validates in polynomial time.
//
// State: each verify() call constructs its own private state; verifiers own
// nothing across invocations beyond the last_used_names cache.
//
// Soundness contract:
//   * The verifier must not register theorems or modify GlobalContext's
//     named registries. The dispatcher (ProofRunner) is the only site of
//     theorem registration and uses the dispatcher-resolved SentenceHandle
//     for the claim_name.
//   * verify() returns Ok if and only if the proof's data witnesses validity
//     of goal_formula under the system's success predicate Φ. On failure,
//     returns an Error with diagnostic context.

#include "ir.h"
#include "proof.h"

#include "src/core/formula.h"
#include "src/util/error.h"

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
