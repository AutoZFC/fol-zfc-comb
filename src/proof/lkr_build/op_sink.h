#pragma once

// Where Sequent rules write: LkrSink expands identities, CompactSink keeps
// them as Identity (COMPACT_LKR_DESIGN.md §3).

#include "compact.h"

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/util/error.h"

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

namespace logic::proof::lkr_build {

class Sequent;

class OpSink {
public:
    virtual ~OpSink() = default;

    virtual TermRef next_ref() const = 0;
    virtual void emit(lkr::Instr op) = 0;

    virtual util::ResultStatus identity(Sequent seq, size_t a, size_t b,
                                        var_index first_eigen,
                                        FormulaBuilder& builder) = 0;
};

class LkrSink final : public OpSink {
public:
    explicit LkrSink(std::vector<lkr::Instr>& ops) : ops_(ops) {}

    TermRef next_ref() const override {
        return TermRef{static_cast<uint32_t>(ops_.size())};
    }
    void emit(lkr::Instr op) override { ops_.push_back(std::move(op)); }
    util::ResultStatus identity(Sequent seq, size_t a, size_t b,
                                var_index first_eigen,
                                FormulaBuilder& builder) override;

private:
    std::vector<lkr::Instr>& ops_;
};

class CompactSink final : public OpSink {
public:
    explicit CompactSink(std::vector<CompactInstr>& ops) : ops_(ops) {}

    TermRef next_ref() const override {
        return TermRef{static_cast<uint32_t>(ops_.size())};
    }
    void emit(lkr::Instr op) override { ops_.push_back(std::move(op)); }
    util::ResultStatus identity(Sequent seq, size_t a, size_t b,
                                var_index first_eigen,
                                FormulaBuilder& builder) override;

private:
    std::vector<CompactInstr>& ops_;
};

}  // namespace logic::proof::lkr_build
