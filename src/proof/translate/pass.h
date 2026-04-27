#pragma once

// Pass<FromInstr, ToInstr> — the IR-to-IR transformation interface.
//
// A pass is a pure function on Programs: it takes a Program<FromInstr>
// and produces a Program<ToInstr>, optionally over the same Instr type
// (an "optimization pass") or over a different one (a "translation pass").
//
// Soundness contract: a pass produces a Program; correctness of that
// Program is established by submitting it to the destination verifier.
// Passes are not trusted — their output must verify. This is the
// empirical correctness check that makes IR-to-IR transformations
// safe to compose without proving each pass formally correct.
//
// Design:
//   * Stateless: a Pass instance carries no state across apply() calls.
//   * Pure: apply() must not mutate any GlobalContext or registries.
//   * Total over the input shape: missing op-arms in a translator's
//     std::visit dispatch are compile-time errors when the overloaded
//     pattern is used (see overloaded utility below).
//
// Memory: each pass produces a new Program; the input is read-only.
// At our proof scale, copying instr lists is cheap.

#include "../../util/error.h"
#include "../ir.h"

#include <utility>

namespace logic::proof::translate {

template <typename FromInstr, typename ToInstr>
class Pass {
public:
    virtual ~Pass() = default;

    // Apply the pass. Returns the transformed program on success, or an
    // Error on failure (e.g. an op the pass doesn't know how to handle,
    // a structural well-formedness violation in the input, etc.).
    virtual util::Result<Program<ToInstr>> apply(const Program<FromInstr>& in) = 0;
};

// overloaded — visitor combinator that produces a callable from a list
// of lambdas, one per std::variant arm. If a lambda is missing for some
// arm, std::visit fails to compile — the type system enforces totality
// of the dispatch. This is the canonical pattern translators use.
template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

}  // namespace logic::proof::translate
