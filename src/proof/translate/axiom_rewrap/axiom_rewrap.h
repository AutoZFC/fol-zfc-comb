#pragma once

// AxiomRewrap — the ND→ND boundary-wrap pass.
//
// Per AXIOM_REWRAP_DESIGN.md (revised 2026-05-18), takes an iota-free
// ND proof P of φ that references facts F_1..F_n (axioms or theorems,
// transitively closed) and emits an ND proof P' of (φ_F_1 ∧ … ∧ φ_F_n) → φ
// — the deduction theorem realized as a syntactic transformation.
//
// Both axioms and theorems are treated uniformly as "facts":
//   - n = 0 (no Use ops anywhere transitively): identity. Output = input.
//   - n ≥ 1: emit synthetic Assume(H) at the start, copy the body
//     verbatim (with StepRef/TermRef shifted by prelude size), but
//     replace every Use(F) (axiom OR theorem) with a step-ref to the
//     extracted h_F. Drop the input's Qed, emit synthetic ImpliesIntro
//     + Qed at the end. The output verifies as a proof of H → φ.
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
    // For n ≥ 1: H → φ where H is the lex-sorted conjunction of `facts`'
    // formulas (axioms by axiom-body, theorems by theorem-formula).
    // For n = 0: equals the original goal.
    FormulaHandle            wrapped_goal;
    // facts(P), lex-sorted (defines H's component order).
    std::vector<std::string> facts;
};

class AxiomRewrap {
public:
    AxiomRewrap(GlobalContext& ctx,
                FormulaHandle goal_formula,
                const TheoremFactsMap& theorem_facts)
        : ctx_(ctx), goal_(goal_formula),
          theorem_facts_(theorem_facts) {}

    util::Result<RewrapResult> apply(const Program<nd::Instr>& in);

private:
    GlobalContext&         ctx_;
    FormulaHandle          goal_;
    const TheoremFactsMap& theorem_facts_;
};

}  // namespace logic::proof::translate::axiom_rewrap
