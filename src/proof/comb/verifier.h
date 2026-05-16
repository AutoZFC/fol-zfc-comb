#pragma once

// CombVerifier — Hughes' combinatorial-proof checker.
//
// Verifies that a CombProof artefact `(N, G, f)` witnesses validity of
// `goal_formula`, by checking the polynomial-time conditions of paper §3-§6:
//
//   Phase 0 — well-formedness: shapes and indices are in range.
//   Phase 1 — target == G(goal_formula): the target fograph is the
//             canonical graph of the goal formula (paper Def. 3.1).
//   Phase 2 — fonet validity (paper Def. 5.3):
//               - linked fograph well-formedness (Def. 5.1)
//               - dualizer is well-defined and unifies all links (Def. 5.2)
//               - leap graph admits no induced bimatching
//   Phase 3 — skew bifibration (paper Def. 4.1):
//               - label-preserving and existential-preserving
//               - skew fibration on the underlying cograph
//               - ordinary (unique-lift) fibration on the binding graph
//
// Each phase is exposed as a public method so tests can pinpoint failures.
//
// State: each verify() call constructs its own private check state and
// resets last_used_. No state spans invocations.

#include "src/proof/comb/comb_proof.h"
#include "src/proof/proof.h"
#include "src/proof/verifier.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <string>
#include <unordered_set>

namespace logic::proof::comb {

class CombVerifier final : public Verifier {
public:
    System system() const override { return System::COMB; }

    // Top-level verifier (ProofRunner entrypoint). Unwraps proof.body to a
    // CombProof, confirms `target.source_formula` matches `goal_formula`
    // (NNF-equivalent), then runs phases 0-3.
    util::ResultStatus verify(
        GlobalContext& ctx,
        FormulaHandle  goal_formula,
        const Proof&   proof) override;

    const std::unordered_set<std::string>& last_used_names() const override {
        return last_used_;
    }

    // ---------------------------------------------------------------------
    // Per-phase entrypoints. Each is independently testable; verify()
    // composes them in order.
    // ---------------------------------------------------------------------

    // Phase 0. Sizes match: fibration.size() == source.num_vertex; every
    // fibration entry indexes into target.labels; vertex indices in edges
    // and links are in range; target.labels.size() matches target's edges.
    util::ResultStatus verify_well_formed(const CombProof& cp) const;

    // Phase 1. Recomputes G(goal_formula) and checks structural equality
    // with cp.target. The verifier does not trust the translator's stored
    // target; it rebuilds and compares.
    util::ResultStatus verify_target_is_formula_graph(
        GlobalContext& ctx,
        FormulaHandle  goal_formula,
        const CombProof& cp) const;

    // Phase 2. Fonet validity per paper Def. 5.3.
    util::ResultStatus verify_fonet(const CombProof& cp) const;

    // Phase 3. Skew bifibration per paper Def. 4.1.
    util::ResultStatus verify_skew_bifibration(const CombProof& cp) const;

private:
    std::unordered_set<std::string> last_used_;
};

}  // namespace logic::proof::comb
