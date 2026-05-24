#pragma once

// Stage 1 Phase 4: emit_prelude.
//
// Builds the `Assume(H) + and_elim chain` prelude that opens Stage 1's
// wrapped proof. Given sorted_facts = [F₁, F₂, …, Fₙ] (lex-sorted by
// SentenceHandle.id() — output of compute_transitive_facts):
//
//   H = (((φ_{F₁} ∧ φ_{F₂}) ∧ φ_{F₃}) ∧ … ∧ φ_{Fₙ})   left-associated
//
// and the output ops are:
//
//   [0]              Assume(H)                       binds h = H
//   [1 .. n-1]       AndElimL chain on h             builds h_{n-1}, …, h_1
//                                                    (each h_k = the prefix
//                                                     (((φ_1 ∧ φ_2) … ∧ φ_k)))
//   [n .. 2n-2]      AndElimR's                      binds h_{F_k} for k = 2..n
//                                                    (h_{F_n} comes from h_n,
//                                                     h_{F_{n-1}} from h_{n-1},
//                                                     …)
//
// Total prelude length is 2n-1 ops for n ≥ 1; the n=1 special case is
// just `Assume(H)` with H = φ_{F₁} and h_{F₁} = StepRef{0}. The n=0
// case is identity: empty ops, default-constructed (invalid) H.
//
// Per Stage 1 v1 spec §6. fact_step_table maps each fact's
// SentenceHandle to the StepRef of the prelude op whose result is that
// fact's extracted formula — the alias target that the body emitter
// (Phase 5) uses when dropping `Use(F)` ops.

#include "src/core/formula.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <unordered_map>
#include <vector>

namespace logic::proof::translate::nd_internalize {

struct PreludeResult {
    // The prelude's ops (no claim_name, no step_index — caller composes
    // with the body to form the final Program).
    std::vector<nd::Instr> instrs;

    // The conjunction sentence H; default-constructed (invalid handle)
    // when facts is empty (n=0 identity case).
    SentenceHandle H;

    // Fact identity → its extracted-step StepRef in the prelude. Empty
    // when n=0. The body emitter consults this table to drop each
    // `Use(F)` and alias to the matching prelude extract.
    std::unordered_map<SentenceHandle, StepRef, SentenceHandleHash>
        fact_step_table;
};

util::Result<PreludeResult>
emit_prelude(GlobalContext& ctx,
             const std::vector<SentenceHandle>& sorted_facts);

}  // namespace logic::proof::translate::nd_internalize
