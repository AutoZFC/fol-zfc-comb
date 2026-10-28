#pragma once

// Demands, targets, hypothesis ids (ELIMINATION_DEMANDS_DESIGN.md §1.3–§1.5).

#include "src/core/formula.h"
#include "src/proof/ir.h"
#include "src/proof/lkr_build/sequent.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <variant>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

using lkr_build::TermBinding;

// An ND step's hypothesis, or a local one the translator introduces.
class HypId {
public:
    static HypId of_step(StepRef s) { return HypId(Kind::Step, s.idx); }
    static HypId local(uint32_t n) { return HypId(Kind::Local, n); }

    bool operator==(const HypId&) const = default;

    size_t hash_value() const {
        return std::hash<uint64_t>{}(
            (static_cast<uint64_t>(kind_) << 32) | index_);
    }

private:
    enum class Kind : uint8_t { Step, Local };
    HypId(Kind kind, uint32_t index) : kind_(kind), index_(index) {}

    Kind     kind_;
    uint32_t index_;
};

struct HypIdHash {
    size_t operator()(const HypId& h) const { return h.hash_value(); }
};

using Minor = std::variant<StepRef, HypId>;

enum class Side : uint8_t { Left, Right };

struct DemandInstance { TermBinding term; };
struct DemandAndLeft {};
struct DemandAndRight {};
struct DemandModus { Minor antecedent; };
struct DemandIffModus { StepRef operand; Side side; };
struct DemandRefute { StepRef refuter; };
struct DemandCases { StepRef if_left; StepRef if_right; };
struct DemandWitness { StepRef closer; };

using Demand = std::variant<
    DemandInstance,
    DemandAndLeft, DemandAndRight,
    DemandModus, DemandIffModus, DemandRefute,
    DemandCases, DemandWitness>;

// The eliminations still to apply to a step's result, head first.
class DemandPath {
public:
    bool   empty() const { return reversed_.empty(); }
    size_t size() const { return reversed_.size(); }

    const Demand& head() const { return reversed_.back(); }

    void push(Demand d) { reversed_.push_back(std::move(d)); }

    Demand pop() {
        Demand d = std::move(reversed_.back());
        reversed_.pop_back();
        return d;
    }

    template <typename F>
    void for_each(F&& f) const {
        for (auto it = reversed_.rbegin(); it != reversed_.rend(); ++it) f(*it);
    }

    // No Step minor, Cases or Witness, so copying it copies no translation.
    bool step_free() const;

    bool projection_only() const;

private:
    std::vector<Demand> reversed_;
};

inline bool DemandPath::step_free() const {
    bool free = true;
    for_each([&](const Demand& d) {
        if (auto* m = std::get_if<DemandModus>(&d)) {
            if (std::holds_alternative<StepRef>(m->antecedent)) free = false;
        } else if (!std::holds_alternative<DemandInstance>(d) &&
                   !std::holds_alternative<DemandAndLeft>(d) &&
                   !std::holds_alternative<DemandAndRight>(d)) {
            free = false;
        }
    });
    return free;
}

inline bool DemandPath::projection_only() const {
    bool only = true;
    for_each([&](const Demand& d) {
        if (!std::holds_alternative<DemandInstance>(d) &&
            !std::holds_alternative<DemandAndLeft>(d) &&
            !std::holds_alternative<DemandAndRight>(d)) {
            only = false;
        }
    });
    return only;
}

// A sequent position, or none when the demanded result is ⊥ (§1.3).
class Target {
public:
    static Target at(size_t pos) { return Target(pos); }
    static Target none() { return Target(std::nullopt); }

    bool   is_none() const { return !pos_.has_value(); }
    size_t pos() const { return *pos_; }

private:
    explicit Target(std::optional<size_t> pos) : pos_(pos) {}
    std::optional<size_t> pos_;
};

}  // namespace logic::proof::translate::nd_to_lkr
