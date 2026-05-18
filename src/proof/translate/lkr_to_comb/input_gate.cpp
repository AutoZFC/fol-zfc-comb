#include "input_gate.h"

#include "src/proof/lkr/verifier.h"

#include <algorithm>
#include <sstream>
#include <string>
#include <unordered_set>
#include <variant>
#include <vector>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// =========================================================================
// I-2 check: no load-bearing Weakening (LKR_TO_COMB_DESIGN.md §4.4).
//
// Track a parallel open-goals stack where each entry is a `bool` flag:
// true = weakening-derived (the entry originated from a Weakening op or
// from a structural decomposition of a weakening-derived entry).
//
// For each op, before applying its effect on the stack, check that no
// position-field reference targets a flagged entry. If any does, the
// Weakening is load-bearing and the program is rejected.
//
// Mark propagation rules:
//   Weakening      → append `true` at end.
//   Or(p)          → entries[p] becomes phi (mark inherited);
//                    psi appended at end (mark inherited).
//   And(p, L)      → split; LEFT gets entries at sorted(L) + LEFT_phi
//                    (false); RIGHT gets complement + RIGHT_theta (false).
//                    Inherited marks routed to LEFT/RIGHT entries.
//   Cut(θ)         → push 2 subgoals (parent + cut formula, mark false).
//   Forall/Exists  → entries[p] replaced by instantiated body
//                    (mark inherited).
//   Exchange       → swap marks at i and j.
//   Contraction    → erase entry at j (its mark dies with it).
//   AxiomLit/One/CloseByLemma → closing; pop top goal.
// =========================================================================

struct GoalMarks {
    std::vector<bool> marks;  // per-entry: true ⇒ weakening-derived
};

bool is_marked(const GoalMarks& g, size_t i) {
    return i < g.marks.size() && g.marks[i];
}

util::ResultStatus reject_load_bearing(
    uint32_t op_idx, const char* op_name, const char* field, size_t pos)
{
    std::ostringstream os;
    os << "LKRtoComb InputGate: I-2 violation — load-bearing Weakening at "
       << "op #" << op_idx << " (" << op_name << "): "
       << field << "=" << pos << " references a weakening-derived entry. "
       << "Scaffolding Weakening is supported (entry never referenced); "
       << "load-bearing Weakening would prove a weaker statement (see "
       << "LKR_TO_COMB_DESIGN.md §4.4 Case B).";
    return MAKE_ERROR << os.str();
}

util::ResultStatus check_no_load_bearing_weakening(
    const Program<lkr::Instr>& prog)
{
    std::vector<GoalMarks> stack;
    stack.push_back(GoalMarks{std::vector<bool>{false}});  // initial: 1 entry, not marked

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (stack.empty()) {
            return MAKE_ERROR
                << "InputGate I-2 check: stack underflow at op #" << i;
        }
        const auto& op = prog.instrs[i];
        GoalMarks& g = stack.back();

        // Closing ops: check + pop.
        if (auto* o = std::get_if<lkr::AxiomLit>(&op)) {
            if (is_marked(g, o->lit_a))
                return reject_load_bearing(i, "AxiomLit", "lit_a", o->lit_a);
            if (is_marked(g, o->lit_b))
                return reject_load_bearing(i, "AxiomLit", "lit_b", o->lit_b);
            stack.pop_back();
            continue;
        }
        if (auto* o = std::get_if<lkr::One>(&op)) {
            if (is_marked(g, o->idx))
                return reject_load_bearing(i, "One", "idx", o->idx);
            stack.pop_back();
            continue;
        }
        if (std::holds_alternative<lkr::CloseByLemma>(op)) {
            // CloseByLemma doesn't reference an existing entry by position
            // (it consumes the whole goal via lemma application).
            stack.pop_back();
            continue;
        }

        // Weakening: no check; mark new entry.
        if (std::holds_alternative<lkr::Weakening>(op)) {
            g.marks.push_back(true);
            continue;
        }

        // Linear ops: check, then apply mark propagation.
        if (auto* o = std::get_if<lkr::Exchange>(&op)) {
            if (is_marked(g, o->i))
                return reject_load_bearing(i, "Exchange", "i", o->i);
            if (is_marked(g, o->j))
                return reject_load_bearing(i, "Exchange", "j", o->j);
            bool tmp_i = g.marks[o->i];
            g.marks[o->i] = g.marks[o->j];
            g.marks[o->j] = tmp_i;
            continue;
        }
        if (auto* o = std::get_if<lkr::Contraction>(&op)) {
            if (is_marked(g, o->i))
                return reject_load_bearing(i, "Contraction", "i", o->i);
            if (is_marked(g, o->j))
                return reject_load_bearing(i, "Contraction", "j", o->j);
            g.marks.erase(g.marks.begin() + o->j);
            continue;
        }
        if (auto* o = std::get_if<lkr::Or>(&op)) {
            if (is_marked(g, o->principal))
                return reject_load_bearing(i, "Or", "principal", o->principal);
            // entries[principal] → phi (mark unchanged); append psi (same mark).
            g.marks.push_back(g.marks[o->principal]);
            continue;
        }
        if (auto* o = std::get_if<lkr::Forall>(&op)) {
            if (is_marked(g, o->principal))
                return reject_load_bearing(i, "Forall", "principal", o->principal);
            // entries[principal] replaced by instantiated body (mark unchanged).
            continue;
        }
        if (auto* o = std::get_if<lkr::Exists>(&op)) {
            if (is_marked(g, o->principal))
                return reject_load_bearing(i, "Exists", "principal", o->principal);
            // entries[principal] replaced by instantiated body (mark unchanged).
            continue;
        }
        if (auto* o = std::get_if<lkr::And>(&op)) {
            if (is_marked(g, o->principal))
                return reject_load_bearing(i, "And", "principal", o->principal);
            for (size_t k : o->left_partition) {
                if (is_marked(g, k))
                    return reject_load_bearing(i, "And", "left_partition[k]", k);
            }
            // Split: LEFT = sorted_partition + LEFT_phi (new, unmarked);
            //        RIGHT = complement (excluding principal) + RIGHT_theta (new, unmarked).
            std::unordered_set<size_t> in_left(
                o->left_partition.begin(), o->left_partition.end());
            std::vector<size_t> sorted_left(
                o->left_partition.begin(), o->left_partition.end());
            std::sort(sorted_left.begin(), sorted_left.end());

            GoalMarks left, right;
            for (size_t k : sorted_left) {
                left.marks.push_back(g.marks[k]);
            }
            left.marks.push_back(false);  // LEFT_phi
            for (size_t k = 0; k < g.marks.size(); ++k) {
                if (k == o->principal) continue;
                if (in_left.count(k))    continue;
                right.marks.push_back(g.marks[k]);
            }
            right.marks.push_back(false);  // RIGHT_theta
            stack.pop_back();
            stack.push_back(std::move(right));  // RIGHT deeper
            stack.push_back(std::move(left));   // LEFT on top
            continue;
        }
        if (std::holds_alternative<lkr::Cut>(op)) {
            // Cut doesn't reference existing entries; both subgoals inherit
            // parent's marks + a new (unmarked) cut formula entry.
            GoalMarks left  = g;
            GoalMarks right = std::move(g);
            left.marks.push_back(false);   // cut formula on LEFT
            right.marks.push_back(false);  // ¬cut formula on RIGHT
            stack.pop_back();
            stack.push_back(std::move(right));
            stack.push_back(std::move(left));
            continue;
        }

        return MAKE_ERROR
            << "InputGate I-2 check: unknown op variant at op #" << i;
    }

    return util::Ok();
}

}  // namespace

util::ResultStatus InputGate::verify(
    GlobalContext&             ctx,
    FormulaHandle              goal_formula,
    const Program<lkr::Instr>& prog)
{
    // I-1: LKR-verifies.
    {
        lkr::LKRVerifier verifier;
        Proof p{System::LKR, prog};
        auto status = verifier.verify(ctx, goal_formula, p);
        if (!status.ok()) {
            return MAKE_ERROR
                << "LKRtoComb InputGate: I-1 violation — input does not "
                << "LKR-verify: " << status.error().to_string();
        }
    }

    // I-2: no load-bearing Weakening.
    TRY(check_no_load_bearing_weakening(prog));

    return util::Ok();
}

}  // namespace logic::proof::translate::lkr_to_comb
