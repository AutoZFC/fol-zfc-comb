#pragma once

// BlockTree — nested decomposition of the flat ND op stream.
//
// Per ND_TO_LKR_DESIGN.md §3.1, the ND op stream is reorganised into a
// tree of *blocks*:
//
//   OUTER             — root; opens at instr 0, closes at Qed.
//   FORALL[v]         — Fix          → ForallIntro
//   IMPLIES[A]        — Assume       → ImpliesIntro
//   NOT[A]            — Assume       → NotIntro
//   CLASSICAL_ABSURD  — Assume(¬A)   → ClassicalAbsurd (derives A)
//   EXISTS_ELIM       — ExistsElim   → ExistsIntro (no witness)
//
// A block carries:
//   - kind        — which of the five kinds above
//   - opener_idx  — the instr index of the opener (kInvalidIdx for OUTER)
//   - closer_idx  — the instr index of the closer (= Qed for OUTER)
//   - target_idx  — the instr index whose derived formula is the block's
//                   *result*: for OUTER it's Qed.derived; for FORALL it's
//                   ForallIntro.body; for IMPLIES it's ImpliesIntro.conclusion;
//                   for NOT it's NotIntro.bottom; for EXISTS_ELIM it's
//                   ExistsIntro.body.
//   - body        — ordered list of FlatStep | sub-Block items.
//
// The eigenvariable for FORALL/EXISTS_ELIM and the assumption formula for
// IMPLIES/NOT are not stored in BlockTree itself — they are recovered at
// emission time by looking at the opener's nd::Instr (Fix.var_name,
// Assume.formula, ExistsElim.bind_witness).
//
// The decomposition is purely structural (matches openers to closers by
// stack discipline) and produces an error if the program has unmatched
// scopes or no Qed.

#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstdint>
#include <memory>
#include <variant>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

enum class BlockKind {
    OUTER,
    FORALL,
    IMPLIES,
    NOT_,        // NOT is a Win32 macro; trailing underscore avoids the clash
    CLASSICAL_ABSURD,  // assume ¬A; ... derive ⊥; classical_absurd → A
    EXISTS_ELIM,
};

struct Block;

struct FlatStep {
    uint32_t nd_idx;
};

using BodyItem = std::variant<FlatStep, std::unique_ptr<Block>>;

inline constexpr uint32_t kInvalidIdx = static_cast<uint32_t>(-1);

struct Block {
    BlockKind             kind{};
    uint32_t              opener_idx{kInvalidIdx};  // kInvalidIdx for OUTER
    uint32_t              closer_idx{kInvalidIdx};
    uint32_t              target_idx{kInvalidIdx};  // see header doc
    std::vector<BodyItem> body{};
};

// Decompose the flat ND program into a tree of blocks. Returns the root
// OUTER block on success.
//
// Failure modes:
//   - Closer without a matching opener (program structure broken).
//   - Unclosed openers at end of program.
//   - No Qed instruction.
//   - Qed not at top-level (would mean an open scope wraps it).
util::Result<std::unique_ptr<Block>> decompose_blocks(
    const Program<nd::Instr>& prog);

}  // namespace logic::proof::translate::nd_to_lkr
