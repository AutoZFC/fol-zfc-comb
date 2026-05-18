#include "block_tree.h"

#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

// Open-block frame: holds the in-progress Block for the current scope
// plus the opener's nd::Instr role so we can decide kind at close time.
struct OpenFrame {
    std::unique_ptr<Block> block;
};

// Classify a closer instruction → which BlockKind it produces, and which
// ND step is the block's `target` (the derived step the body must reach
// to make the closer well-typed).
struct CloserInfo {
    BlockKind kind;
    uint32_t  target_idx;
};

util::Result<CloserInfo> classify_closer(const nd::Instr& instr,
                                          uint32_t          instr_idx)
{
    if (auto* fi = std::get_if<nd::ForallIntro>(&instr)) {
        return CloserInfo{BlockKind::FORALL, fi->body.idx};
    }
    if (auto* ii = std::get_if<nd::ImpliesIntro>(&instr)) {
        return CloserInfo{BlockKind::IMPLIES, ii->conclusion.idx};
    }
    if (auto* ni = std::get_if<nd::NotIntro>(&instr)) {
        return CloserInfo{BlockKind::NOT_, ni->bottom.idx};
    }
    if (auto* ei = std::get_if<nd::ExistsIntro>(&instr); ei && !ei->witness.has_value()) {
        return CloserInfo{BlockKind::EXISTS_ELIM, ei->body.idx};
    }
    return MAKE_ERROR
        << "decompose_blocks: instr #" << instr_idx
        << " is not a scope closer";
}

// Validate that opener instr type matches the block kind chosen by the
// closer. Catches malformed programs early: a Fix followed by ImpliesIntro
// would mean an IMPLIES block opened by Fix, which is structurally invalid.
util::ResultStatus check_opener_matches(const nd::Instr& opener_instr,
                                         BlockKind        kind,
                                         uint32_t         opener_idx,
                                         uint32_t         closer_idx)
{
    auto kind_ok = [&]() -> bool {
        switch (kind) {
            case BlockKind::FORALL:
                return std::holds_alternative<nd::Fix>(opener_instr);
            case BlockKind::IMPLIES:
            case BlockKind::NOT_:
                return std::holds_alternative<nd::Assume>(opener_instr);
            case BlockKind::EXISTS_ELIM:
                return std::holds_alternative<nd::ExistsElim>(opener_instr);
            case BlockKind::OUTER:
                return false;  // OUTER has no real opener instr
        }
        return false;
    }();
    if (!kind_ok) {
        return MAKE_ERROR
            << "decompose_blocks: opener at #" << opener_idx
            << " does not match the block kind chosen by closer at #"
            << closer_idx;
    }
    return util::Ok();
}

bool is_opener(const nd::Instr& instr) {
    return std::holds_alternative<nd::Fix>(instr) ||
           std::holds_alternative<nd::Assume>(instr) ||
           std::holds_alternative<nd::ExistsElim>(instr);
}

bool is_closer(const nd::Instr& instr) {
    if (std::holds_alternative<nd::ForallIntro>(instr)) return true;
    if (std::holds_alternative<nd::ImpliesIntro>(instr)) return true;
    if (std::holds_alternative<nd::NotIntro>(instr)) return true;
    if (auto* ei = std::get_if<nd::ExistsIntro>(&instr)) {
        return !ei->witness.has_value();
    }
    return false;
}

}  // namespace

util::Result<std::unique_ptr<Block>> decompose_blocks(
    const Program<nd::Instr>& prog)
{
    // Initialise the OUTER frame.
    std::vector<OpenFrame> stack;
    {
        OpenFrame f;
        f.block             = std::make_unique<Block>();
        f.block->kind       = BlockKind::OUTER;
        f.block->opener_idx = kInvalidIdx;
        stack.push_back(std::move(f));
    }

    // Will be filled when Qed is found.
    bool seen_qed = false;

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        const auto& instr = prog.instrs[i];

        if (std::holds_alternative<nd::Qed>(instr)) {
            if (stack.size() != 1) {
                return MAKE_ERROR
                    << "decompose_blocks: Qed at #" << i
                    << " inside an open scope (depth=" << stack.size() << ")";
            }
            auto& outer       = *stack.back().block;
            outer.closer_idx  = i;
            // Qed.derived is the target step the outer body must reach.
            outer.target_idx  = std::get<nd::Qed>(instr).derived.idx;
            seen_qed          = true;
            // Note: Qed is the closer for OUTER; we don't append it as a
            // body item.
            continue;
        }

        if (is_opener(instr)) {
            OpenFrame f;
            f.block             = std::make_unique<Block>();
            f.block->opener_idx = i;
            stack.push_back(std::move(f));
            continue;
        }

        if (is_closer(instr)) {
            if (stack.size() < 2) {
                return MAKE_ERROR
                    << "decompose_blocks: closer at #" << i
                    << " has no matching opener";
            }
            TRY_ASSIGN(ci, classify_closer(instr, i));
            auto& top = *stack.back().block;
            TRY(check_opener_matches(prog.instrs[top.opener_idx],
                                      ci.kind, top.opener_idx, i));
            top.kind       = ci.kind;
            top.closer_idx = i;
            top.target_idx = ci.target_idx;
            // Move this completed block as a body item of the parent.
            auto completed = std::move(stack.back().block);
            stack.pop_back();
            stack.back().block->body.push_back(std::move(completed));
            continue;
        }

        // Flat step: add to the current block's body.
        stack.back().block->body.push_back(FlatStep{i});
    }

    if (!seen_qed) {
        return MAKE_ERROR << "decompose_blocks: program has no Qed";
    }
    if (stack.size() != 1) {
        return MAKE_ERROR
            << "decompose_blocks: " << (stack.size() - 1)
            << " unclosed scope(s) at end of program";
    }

    return std::move(stack.back().block);
}

}  // namespace logic::proof::translate::nd_to_lkr
