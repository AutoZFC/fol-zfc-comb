#include "tree.h"

#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

enum class OpKind { Closing, Linear, Branching };

OpKind classify(const lkr::Instr& op) {
    if (std::holds_alternative<lkr::AxiomLit>(op) ||
        std::holds_alternative<lkr::One>(op) ||
        std::holds_alternative<lkr::CloseByLemma>(op)) {
        return OpKind::Closing;
    }
    if (std::holds_alternative<lkr::And>(op) ||
        std::holds_alternative<lkr::Cut>(op)) {
        return OpKind::Branching;
    }
    return OpKind::Linear;
}

util::Result<std::unique_ptr<DerivationTree>> parse_subtree(
    const Program<lkr::Instr>& prog,
    uint32_t&                  pos)
{
    if (pos >= prog.instrs.size()) {
        return MAKE_ERROR
            << "rebuild_tree: stream ended mid-tree at pos " << pos;
    }
    uint32_t my_idx = pos;
    OpKind k = classify(prog.instrs[my_idx]);
    ++pos;

    auto tree = std::make_unique<DerivationTree>();
    switch (k) {
        case OpKind::Closing: {
            tree->node = LeafNode{my_idx};
            return tree;
        }
        case OpKind::Linear: {
            TRY_ASSIGN(child, parse_subtree(prog, pos));
            tree->node = LinearNode{my_idx, std::move(child)};
            return tree;
        }
        case OpKind::Branching: {
            // LKR Cut/And verifier pushes RIGHT first (deeper), then LEFT.
            // So the next op operates on LEFT; LEFT closes; then RIGHT
            // becomes top. Parse LEFT first, then RIGHT.
            TRY_ASSIGN(left,  parse_subtree(prog, pos));
            TRY_ASSIGN(right, parse_subtree(prog, pos));
            tree->node = BranchingNode{my_idx, std::move(left), std::move(right)};
            return tree;
        }
    }
    return MAKE_ERROR << "rebuild_tree: unreachable op kind";
}

}  // namespace

util::Result<std::unique_ptr<DerivationTree>> rebuild_tree(
    const Program<lkr::Instr>& prog)
{
    if (prog.instrs.empty()) {
        return MAKE_ERROR << "rebuild_tree: empty program";
    }
    uint32_t pos = 0;
    TRY_ASSIGN(root, parse_subtree(prog, pos));
    if (pos != prog.instrs.size()) {
        return MAKE_ERROR
            << "rebuild_tree: " << (prog.instrs.size() - pos)
            << " op(s) remained unconsumed after root subtree";
    }
    return root;
}

}  // namespace logic::proof::translate::lkr_to_comb
