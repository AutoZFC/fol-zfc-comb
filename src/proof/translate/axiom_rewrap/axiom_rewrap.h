#pragma once

// AxiomRewrap — the ND→ND boundary-wrap pass (Phase 2).
//
// Per AXIOM_REWRAP_DESIGN.md, takes an iota-free ND proof P of φ that
// references axioms A_1..A_n (transitively, through cited theorems) and
// emits an ND proof P' of (A_1 ∧ … ∧ A_n) → φ — the deduction theorem,
// realized as a syntactic transformation.
//
// Phase 2 scope: boundary mechanism only.
//   - n = 0 (no axiom references): identity. Output = input.
//   - n ≥ 1: emit synthetic Assume(H) at the start, copy the body
//     verbatim (with StepRef/TermRef shifted by prelude size), drop the
//     input's Qed, emit synthetic ImpliesIntro + Qed at the end. The
//     output verifies as a proof of H → φ.
//
// Phase 2 does NOT drop axiom-Use ops from the body, expand SchemaInst,
// or emit theorem unwrap macros — those are later phases (§7.4–§7.6).
// The body still references axioms via Use(A); the wrap nevertheless
// produces a verifiable H → φ proof because the body's derivation of φ
// is independent of whether the synthetic h: H is used.
//
// Output gate: the pass invokes NDVerifier on the output against the
// wrapped goal before returning Ok. Translator bugs surface as a
// boundary Error.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/axiom_rewrap/theorem_axioms.h"
#include "src/util/error.h"

#include <string>
#include <vector>

namespace logic::proof::translate::axiom_rewrap {

struct RewrapResult {
    // ND proof of `wrapped_goal`. For n = 0, equals the input verbatim.
    Program<nd::Instr>       proof;
    // The new goal handed to downstream stages.
    // For n ≥ 1: H → φ where H is the lex-sorted conjunction of `axioms`.
    // For n = 0: equals the original goal.
    FormulaHandle            wrapped_goal;
    // axioms(P), lex-sorted (defines H's component order).
    std::vector<std::string> axioms;
};

class AxiomRewrap {
public:
    AxiomRewrap(GlobalContext& ctx,
                FormulaHandle goal_formula,
                const TheoremAxiomMap& theorem_axioms,
                const WrappedTheoremMap& wrapped_theorems)
        : ctx_(ctx), goal_(goal_formula),
          theorem_axioms_(theorem_axioms),
          wrapped_theorems_(wrapped_theorems) {}

    util::Result<RewrapResult> apply(const Program<nd::Instr>& in);

private:
    GlobalContext&           ctx_;
    FormulaHandle            goal_;
    const TheoremAxiomMap&   theorem_axioms_;
    const WrappedTheoremMap& wrapped_theorems_;
};

}  // namespace logic::proof::translate::axiom_rewrap
