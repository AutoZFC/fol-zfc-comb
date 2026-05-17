#include "elimination_plan.h"

#include <variant>

namespace logic::proof::translate::iota_elim {

namespace {

// Classify an instruction's structural role for block bookkeeping.
enum class Role { Opener, Closer, ScopeClosingExistsIntro, Qed, Other };

Role classify(const nd::Instr& instr) {
    if (std::holds_alternative<nd::Fix>(instr) ||
        std::holds_alternative<nd::Assume>(instr) ||
        std::holds_alternative<nd::ExistsElim>(instr)) {
        return Role::Opener;
    }
    if (std::holds_alternative<nd::ForallIntro>(instr) ||
        std::holds_alternative<nd::ImpliesIntro>(instr) ||
        std::holds_alternative<nd::NotIntro>(instr)) {
        return Role::Closer;
    }
    if (auto* ei = std::get_if<nd::ExistsIntro>(&instr)) {
        if (!ei->witness.has_value()) return Role::ScopeClosingExistsIntro;
    }
    if (std::holds_alternative<nd::Qed>(instr)) return Role::Qed;
    return Role::Other;
}

}  // namespace

util::Result<EliminationPlan> EliminationPlan::compute(
    const IotaInventory& inv,
    const Program<nd::Instr>& prog)
{
    EliminationPlan plan;
    if (inv.empty()) return plan;

    // Find qed index (fallback target for outer-level iota sites).
    uint32_t qed_idx = static_cast<uint32_t>(prog.instrs.size());
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::Qed>(prog.instrs[i])) {
            qed_idx = i;
            break;
        }
    }
    if (qed_idx == prog.instrs.size()) {
        return MAKE_ERROR << "EliminationPlan: program has no qed";
    }

    // Pass 1: pair openers to closers (stack discipline).
    std::vector<uint32_t> stack;
    std::vector<uint32_t> closer_of(prog.instrs.size(),
                                     static_cast<uint32_t>(-1));
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        Role r = classify(prog.instrs[i]);
        switch (r) {
            case Role::Opener:
                stack.push_back(i);
                break;
            case Role::Closer:
            case Role::ScopeClosingExistsIntro:
                if (stack.empty()) {
                    return MAKE_ERROR
                        << "EliminationPlan: closer at #" << i
                        << " has no matching opener";
                }
                closer_of[stack.back()] = i;
                stack.pop_back();
                break;
            case Role::Qed:
            case Role::Other:
                break;
        }
    }
    if (!stack.empty()) {
        return MAKE_ERROR
            << "EliminationPlan: " << stack.size()
            << " unclosed scope(s) at end of program";
    }

    // Pass 2: for each iota_elim site, find the deepest open block at its
    // position; the iota's new exists_elim scope must close before that
    // block's closer.
    stack.clear();
    size_t next_site = 0;
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        while (next_site < inv.sites().size() &&
               inv.sites()[next_site] == i) {
            Action a;
            a.iota_idx = i;
            a.scope_close_idx = stack.empty() ? qed_idx : closer_of[stack.back()];
            plan.actions_.push_back(a);
            ++next_site;
        }
        Role r = classify(prog.instrs[i]);
        switch (r) {
            case Role::Opener:
                stack.push_back(i);
                break;
            case Role::Closer:
            case Role::ScopeClosingExistsIntro:
                stack.pop_back();
                break;
            case Role::Qed:
            case Role::Other:
                break;
        }
    }

    return plan;
}

}  // namespace logic::proof::translate::iota_elim
