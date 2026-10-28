#pragma once

// Static facts about an ND program for Stage 2: blocks, binders, FH(s),
// projections and share mode; checks I-4 (ELIMINATION_DEMANDS_DESIGN.md).

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/block_tree.h"
#include "src/util/error.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

struct BlockId {
    uint32_t idx;
    bool operator==(const BlockId&) const = default;
};

class ProofIndex {
public:
    // A part of a hypothesis' dual (§2.8), with its halves when only projected.
    struct Component {
        std::vector<StepRef>       steps;
        std::unique_ptr<Component> left;
        std::unique_ptr<Component> right;

        bool split() const { return left || right; }
    };

    static util::Result<ProofIndex> build(
        const Program<nd::Instr>&         prog,
        const nd::NDVerifier::TraceFull&  trace,
        bool                              share);

    const nd::Instr& instr(StepRef s) const { return prog_->instrs[s.idx]; }

    StepRef root() const { return root_; }
    BlockId outer() const { return BlockId{0}; }

    BlockId closed_by(StepRef closer) const;
    StepRef opener(BlockId b) const { return blocks_[b.idx].opener; }
    StepRef target(BlockId b) const { return blocks_[b.idx].target; }

    var_index level(StepRef binder) const { return levels_[binder.idx]; }

    // scope(s): the binder steps enclosing s, outermost first.
    const std::vector<StepRef>& scope(StepRef s) const {
        return blocks_[block_of_[s.idx].idx].binders;
    }

    // FH(s): the hypotheses, binders and shared steps s leaves free.
    const std::vector<uint32_t>& free_hypotheses(StepRef s) const {
        return free_hypotheses_[s.idx];
    }
    const std::vector<uint32_t>& free_in_block(BlockId b) const {
        return blocks_[b.idx].free;
    }

    // nullptr unless h is used only through and_elim projections.
    const Component* projections(StepRef hypothesis) const {
        auto it = projections_.find(hypothesis);
        return it == projections_.end() ? nullptr : it->second.get();
    }
    std::optional<StepRef> view_root(StepRef s) const {
        if (view_root_[s.idx] == kInvalidIdx) return std::nullopt;
        return StepRef{view_root_[s.idx]};
    }

    bool is_shared(StepRef s) const { return shared_[s.idx]; }
    const std::vector<StepRef>& shared_at(BlockId b) const {
        return blocks_[b.idx].shared;
    }

    bool is_bottom(StepRef s) const { return bottom_[s.idx]; }
    // An ∃E closer whose body mentions the witness (G5).
    bool requantifies(StepRef closer) const { return requantifies_[closer.idx]; }

private:
    struct BlockInfo {
        BlockKind            kind{};
        StepRef              opener{kInvalidIdx};
        StepRef              closer{kInvalidIdx};
        StepRef              target{kInvalidIdx};
        uint32_t             parent{0};
        uint32_t             depth{0};
        std::vector<StepRef> binders;
        std::vector<StepRef> shared;
        std::vector<uint32_t> free;
    };

    ProofIndex() = default;

    const Program<nd::Instr>*          prog_{nullptr};
    StepRef                            root_{0};
    std::vector<BlockInfo>             blocks_;
    std::vector<BlockId>               block_of_;
    std::vector<uint32_t>              closed_by_;
    std::vector<var_index>             levels_;
    std::vector<std::vector<uint32_t>> free_hypotheses_;
    std::vector<uint32_t>              view_root_;
    std::unordered_map<StepRef, std::unique_ptr<Component>> projections_;
    std::vector<bool>                  shared_;
    std::vector<bool>                  bottom_;
    std::vector<bool>                  requantifies_;

    friend class ProofIndexBuilder;
};

}  // namespace logic::proof::translate::nd_to_lkr
