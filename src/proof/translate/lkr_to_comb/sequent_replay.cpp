#include "sequent_replay.h"

#include "cut_augment.h"

#include <algorithm>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// Number of vertices Fograph would allocate for `f`. Mirrors
// count_fograph_vertices in walk.cpp; duplicated here to keep replay
// independent of walk.
size_t count_vertices(FormulaHandle f) {
    const Formula& fm = f.get();
    if (fm.is_predicate() || fm.is_schema_var()) return 1;
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        if (c.op == Op::Not) return 1;
        if (c.op == Op::And || c.op == Op::Or) {
            return count_vertices(c.left) + count_vertices(c.right);
        }
        return 0;
    }
    if (fm.is_quantified()) {
        return 1 + count_vertices(fm.as_quantified().body);
    }
    return 0;
}

util::Result<FormulaHandle> resolve_source(const lkr::FormulaSource& src) {
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        if (!h->valid()) {
            return MAKE_ERROR
                << "sequent_replay: FormulaSource holds invalid FormulaHandle";
        }
        return *h;
    }
    return MAKE_ERROR
        << "sequent_replay: deferred-AST FormulaSource not supported";
}

util::Result<Term> resolve_term(
    const std::vector<std::optional<Term>>& term_env,
    TermRef                                  ref)
{
    if (ref.idx >= term_env.size() || !term_env[ref.idx].has_value()) {
        return MAKE_ERROR
            << "sequent_replay: unresolved TermRef #" << ref.idx;
    }
    return *term_env[ref.idx];
}

}  // namespace

util::Result<SequentReplay> replay_sequents(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog,
    const CutAugmentation&     cut_aug)
{
    SequentReplay r;
    r.sequent_before.resize(prog.instrs.size());
    r.entry_positions.resize(prog.instrs.size());
    r.term_env.resize(prog.instrs.size());
    size_t cut_count = 0;  // tracks which θ_k we're at when seeing Cut

    // Two parallel stacks: formula entries and their canonical-position
    // tracking. Always pushed/popped together.
    std::vector<std::vector<FormulaHandle>>             entry_stack;
    std::vector<std::vector<std::vector<size_t>>>       pos_stack;

    // Initial: one entry (goal_nnf) whose positions are 0..N-1 (all
    // vertices of Fograph(goal_nnf), in pre-order).
    size_t goal_count = count_vertices(goal_nnf);
    std::vector<size_t> initial_positions;
    initial_positions.reserve(goal_count);
    for (size_t i = 0; i < goal_count; ++i) initial_positions.push_back(i);
    entry_stack.push_back({goal_nnf});
    pos_stack.push_back({std::move(initial_positions)});

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (entry_stack.empty()) {
            return MAKE_ERROR
                << "sequent_replay: empty open-goals stack at op #" << i;
        }
        r.sequent_before[i]   = entry_stack.back();
        r.entry_positions[i]  = pos_stack.back();

        const auto& instr = prog.instrs[i];

        // ===================================================================
        // Closing ops: pop the top goal.
        // ===================================================================
        if (std::holds_alternative<lkr::AxiomLit>(instr) ||
            std::holds_alternative<lkr::One>(instr) ||
            std::holds_alternative<lkr::CloseByLemma>(instr)) {
            entry_stack.pop_back();
            pos_stack.pop_back();
            continue;
        }

        // ===================================================================
        // Linear ops.
        // ===================================================================
        if (auto* op = std::get_if<lkr::Exchange>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->i >= g.size() || op->j >= g.size()) {
                return MAKE_ERROR << "sequent_replay: Exchange OOR at op #" << i;
            }
            std::swap(g[op->i], g[op->j]);
            std::swap(p[op->i], p[op->j]);
            continue;
        }

        if (auto* op = std::get_if<lkr::Weakening>(&instr)) {
            TRY_ASSIGN(f, resolve_source(op->formula));
            entry_stack.back().push_back(f);
            // Weakened-in vertices get NEW positions beyond the goal's
            // canonical range. Placeholder for now (Weakening support
            // requires extending the target — phase 7+ work).
            pos_stack.back().push_back({});
            (void)f;
            continue;
        }

        if (auto* op = std::get_if<lkr::Contraction>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->j >= g.size()) {
                return MAKE_ERROR << "sequent_replay: Contraction OOR at op #" << i;
            }
            g.erase(g.begin() + op->j);
            p.erase(p.begin() + op->j);
            (void)op->i;
            continue;
        }

        if (auto* op = std::get_if<lkr::Or>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->principal >= g.size()) {
                return MAKE_ERROR << "sequent_replay: Or OOR at op #" << i;
            }
            const Formula& f = g[op->principal].get();
            if (!f.is_compound() || f.as_compound().op != Op::Or) {
                return MAKE_ERROR
                    << "sequent_replay: Or principal at op #" << i
                    << " is not ϕ ∨ θ";
            }
            FormulaHandle phi = f.as_compound().left;
            FormulaHandle psi = f.as_compound().right;
            // Split positions: phi takes first count_vertices(phi); psi
            // takes the rest.
            size_t left_count = count_vertices(phi);
            std::vector<size_t> phi_pos(p[op->principal].begin(),
                                         p[op->principal].begin() + left_count);
            std::vector<size_t> psi_pos(p[op->principal].begin() + left_count,
                                         p[op->principal].end());
            g[op->principal] = phi;
            p[op->principal] = std::move(phi_pos);
            g.push_back(psi);
            p.push_back(std::move(psi_pos));
            continue;
        }

        if (auto* op = std::get_if<lkr::Forall>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->principal >= g.size()) {
                return MAKE_ERROR << "sequent_replay: Forall OOR at op #" << i;
            }
            const Formula& f = g[op->principal].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Forall) {
                return MAKE_ERROR
                    << "sequent_replay: Forall principal at op #" << i
                    << " is not ∀x.ϕ";
            }
            Term eigen = Term::fixed(op->eigen);
            r.term_env[i] = eigen;
            g[op->principal] = builder.instantiate_quantifier_body(
                f.as_quantified().body, eigen);
            // Positions: the binder vertex (first of principal's
            // positions) is consumed; body vertices keep the rest. The
            // binder remains in the canonical fograph but is no longer
            // a sequent entry's responsibility (handled by per-rule
            // Forall in §11.1, which adds a binder vertex to source N).
            if (!p[op->principal].empty()) {
                p[op->principal].erase(p[op->principal].begin());
            }
            continue;
        }

        if (auto* op = std::get_if<lkr::Exists>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->principal >= g.size()) {
                return MAKE_ERROR << "sequent_replay: Exists OOR at op #" << i;
            }
            const Formula& f = g[op->principal].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Exists) {
                return MAKE_ERROR
                    << "sequent_replay: Exists principal at op #" << i
                    << " is not ∃x.ϕ";
            }
            TRY_ASSIGN(t, resolve_term(r.term_env, op->witness));
            g[op->principal] = builder.instantiate_quantifier_body(
                f.as_quantified().body, t);
            if (!p[op->principal].empty()) {
                p[op->principal].erase(p[op->principal].begin());
            }
            continue;
        }

        // ===================================================================
        // Branching ops.
        // ===================================================================
        if (auto* op = std::get_if<lkr::And>(&instr)) {
            auto& g = entry_stack.back();
            auto& p = pos_stack.back();
            if (op->principal >= g.size()) {
                return MAKE_ERROR << "sequent_replay: And OOR at op #" << i;
            }
            const Formula& f = g[op->principal].get();
            if (!f.is_compound() || f.as_compound().op != Op::And) {
                return MAKE_ERROR
                    << "sequent_replay: And principal at op #" << i
                    << " is not ϕ ∧ θ";
            }
            FormulaHandle phi   = f.as_compound().left;
            FormulaHandle theta = f.as_compound().right;
            std::unordered_set<size_t> left_set(
                op->left_partition.begin(), op->left_partition.end());
            if (left_set.count(op->principal)) {
                return MAKE_ERROR
                    << "sequent_replay: And partition includes principal";
            }
            for (size_t k : op->left_partition) {
                if (k >= g.size()) {
                    return MAKE_ERROR << "sequent_replay: And partition OOR";
                }
            }

            // Split principal's positions: phi gets first count_vertices(phi);
            // theta gets the rest.
            size_t phi_count = count_vertices(phi);
            std::vector<size_t> phi_pos(p[op->principal].begin(),
                                         p[op->principal].begin() + phi_count);
            std::vector<size_t> theta_pos(p[op->principal].begin() + phi_count,
                                           p[op->principal].end());

            std::vector<size_t> sorted_left(op->left_partition.begin(),
                                             op->left_partition.end());
            std::sort(sorted_left.begin(), sorted_left.end());

            std::vector<FormulaHandle> g_left;
            std::vector<std::vector<size_t>> p_left;
            for (size_t k : sorted_left) {
                g_left.push_back(g[k]);
                p_left.push_back(p[k]);
            }
            g_left.push_back(phi);
            p_left.push_back(std::move(phi_pos));

            std::vector<FormulaHandle> g_right;
            std::vector<std::vector<size_t>> p_right;
            for (size_t k = 0; k < g.size(); ++k) {
                if (k == op->principal) continue;
                if (left_set.count(k)) continue;
                g_right.push_back(g[k]);
                p_right.push_back(p[k]);
            }
            g_right.push_back(theta);
            p_right.push_back(std::move(theta_pos));

            entry_stack.pop_back();
            pos_stack.pop_back();
            entry_stack.push_back(std::move(g_right));
            pos_stack.push_back(std::move(p_right));
            entry_stack.push_back(std::move(g_left));
            pos_stack.push_back(std::move(p_left));
            continue;
        }

        if (auto* op = std::get_if<lkr::Cut>(&instr)) {
            TRY_ASSIGN(phi, resolve_source(op->cut_formula));
            FormulaHandle phi_nnf     = builder.to_nnf(phi);
            FormulaHandle not_phi_nnf = builder.to_nnf_neg(phi);
            (void)op;

            if (cut_count >= cut_aug.theta_start.size()) {
                return MAKE_ERROR
                    << "sequent_replay: cut op #" << i
                    << " exceeds CutAugmentation's cut count ("
                    << cut_aug.theta_start.size() << ")";
            }
            size_t theta_start     = cut_aug.theta_start[cut_count];
            size_t theta_count_k   = cut_aug.theta_count[cut_count];
            size_t neg_theta_count_k = cut_aug.neg_theta_count[cut_count];

            std::vector<size_t> theta_positions;
            theta_positions.reserve(theta_count_k);
            for (size_t k = 0; k < theta_count_k; ++k) {
                theta_positions.push_back(theta_start + k);
            }
            std::vector<size_t> neg_theta_positions;
            neg_theta_positions.reserve(neg_theta_count_k);
            for (size_t k = 0; k < neg_theta_count_k; ++k) {
                neg_theta_positions.push_back(
                    theta_start + theta_count_k + k);
            }

            auto g = entry_stack.back();
            auto p = pos_stack.back();
            auto g_left  = g;
            auto g_right = std::move(g);
            auto p_left  = p;
            auto p_right = std::move(p);
            // LEFT gets θ_nnf; RIGHT gets ¬θ_nnf. Important: we use the
            // NNF form on LEFT too, so positions match Fograph's pre-order.
            g_left.push_back(phi_nnf);
            g_right.push_back(not_phi_nnf);
            p_left.push_back(std::move(theta_positions));
            p_right.push_back(std::move(neg_theta_positions));

            entry_stack.pop_back();
            pos_stack.pop_back();
            entry_stack.push_back(std::move(g_right));
            pos_stack.push_back(std::move(p_right));
            entry_stack.push_back(std::move(g_left));
            pos_stack.push_back(std::move(p_left));
            ++cut_count;
            continue;
        }

        return MAKE_ERROR
            << "sequent_replay: unknown op variant at op #" << i;
    }

    if (!entry_stack.empty()) {
        return MAKE_ERROR
            << "sequent_replay: " << entry_stack.size()
            << " open goal(s) left after last op";
    }
    return r;
}

}  // namespace logic::proof::translate::lkr_to_comb
