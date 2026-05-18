#pragma once

// DerivationTree — branching tree reconstructed from a flat LKR op stream.
//
// Per LKR_TO_COMB_DESIGN.md §3.2. LKR is a linear instruction stream
// consumed by a stack-based verifier. Each closing op pops the top open
// goal; each branching op (And, Cut) pushes two new goals (deeper RIGHT,
// then LEFT on top). The §11.1 translation is naturally tree-shaped, so
// before walking we rebuild the tree from the stream.
//
// Algorithm: recursive descent. Each closing op terminates a subtree;
// each linear op wraps a child subtree; each branching op consumes the
// next two subtrees as LEFT then RIGHT (matching the verifier's
// push-RIGHT-then-LEFT convention, so the immediate next subtree is
// LEFT).
//
// Failure modes:
//   - Stream ends mid-tree (some open subtree never closes).
//   - Closing op at top level with nothing to close.
//   - Op count mismatch.

#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstdint>
#include <memory>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

struct DerivationTree;

// Three node kinds, matching the three op categories.
struct LeafNode {
    uint32_t op_idx;       // index in prog.instrs; the closing op
};

struct LinearNode {
    uint32_t                       op_idx;
    std::unique_ptr<DerivationTree> child;
};

struct BranchingNode {
    uint32_t                       op_idx;
    std::unique_ptr<DerivationTree> left;
    std::unique_ptr<DerivationTree> right;
};

struct DerivationTree {
    std::variant<LeafNode, LinearNode, BranchingNode> node;
};

// Rebuild the tree. Returns the root on success. The tree's leaf nodes
// pin closing ops; linear nodes pin one-child ops; branching nodes pin
// two-child ops. The instruction count is preserved (each op appears in
// exactly one node).
util::Result<std::unique_ptr<DerivationTree>> rebuild_tree(
    const Program<lkr::Instr>& prog);

}  // namespace logic::proof::translate::lkr_to_comb
