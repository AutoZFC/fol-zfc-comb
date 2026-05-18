#include "lemma_inliner.h"

#include "src/proof/ir.h"

#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// =========================================================================
// Sequent-size helpers (mirror Fograph's structural vertex count for ops
// that don't change size; just need raw entry counts for offset tracking).
// =========================================================================

size_t count_fograph_vertices(FormulaHandle f) {
    const Formula& fm = f.get();
    if (fm.is_predicate() || fm.is_schema_var()) return 1;
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        if (c.op == Op::Not) return 1;
        if (c.op == Op::Bottom) return 0;
        if (c.op == Op::And || c.op == Op::Or) {
            return count_fograph_vertices(c.left) +
                   count_fograph_vertices(c.right);
        }
        return 0;
    }
    if (fm.is_quantified()) {
        return 1 + count_fograph_vertices(fm.as_quantified().body);
    }
    return 0;
}

// =========================================================================
// Eigen rename helpers.
// =========================================================================

// Walk all formulas reachable from `prog` to find the maximum Fixed-var
// index ever used. Used to seed the fresh-eigen counter.
//
// We scan: every Forall.eigen, every FormulaHandle in Cut/Weakening
// FormulaSources (recursively into the formula tree).
var_index max_var_in_term(const Term& t) {
    if (t.is_fixed()) return t.as_variable() + 1;
    return 0;
}

var_index max_var_in_formula(FormulaHandle f) {
    if (!f.valid()) return 0;
    const Formula& fm = f.get();
    if (fm.is_predicate()) {
        var_index m = 0;
        for (const Term& t : fm.as_predicate().args()) {
            m = std::max(m, max_var_in_term(t));
        }
        return m;
    }
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        var_index l = c.left.valid()  ? max_var_in_formula(c.left)  : 0;
        var_index r = c.right.valid() ? max_var_in_formula(c.right) : 0;
        return std::max(l, r);
    }
    if (fm.is_quantified()) {
        return max_var_in_formula(fm.as_quantified().body);
    }
    return 0;
}

var_index max_var_in_source(const lkr::FormulaSource& src) {
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        return max_var_in_formula(*h);
    }
    return 0;
}

var_index max_var_in_program(const Program<lkr::Instr>& p) {
    var_index m = 0;
    for (const auto& op : p.instrs) {
        if (auto* f = std::get_if<lkr::Forall>(&op)) {
            m = std::max<var_index>(m, f->eigen + 1);
        } else if (auto* c = std::get_if<lkr::Cut>(&op)) {
            m = std::max(m, max_var_in_source(c->cut_formula));
        } else if (auto* w = std::get_if<lkr::Weakening>(&op)) {
            m = std::max(m, max_var_in_source(w->formula));
        }
    }
    return m;
}

// Simultaneous substitution: Fixed(v) → Fixed(rename[v]) for every
// v in the rename map. Mirrors alpha_rename.cpp's recipe; one-pass to
// avoid clobbering when the map is a permutation.
Term rewrite_term_simultaneous(
    const Term&                                      t,
    const std::unordered_map<var_index, var_index>&  rename)
{
    if (t.is_fixed()) {
        auto it = rename.find(t.as_variable());
        if (it != rename.end()) return Term::fixed(it->second);
    }
    return t;
}

FormulaHandle rewrite_formula_simultaneous(
    FormulaBuilder&                                  builder,
    FormulaHandle                                    h,
    const std::unordered_map<var_index, var_index>&  rename)
{
    if (rename.empty() || !h.valid()) return h;
    const Formula& f = h.get();
    if (f.is_predicate()) {
        const auto& p = f.as_predicate();
        std::vector<Term> new_args;
        new_args.reserve(p.args().size());
        bool changed = false;
        for (const auto& a : p.args()) {
            Term na = rewrite_term_simultaneous(a, rename);
            if (!(na == a)) changed = true;
            new_args.push_back(na);
        }
        if (!changed) return h;
        return builder.predicate(p.predicate(), std::move(new_args));
    }
    if (f.is_compound()) {
        const auto& c = f.as_compound();
        if (c.op == Op::Bottom) return h;
        auto nl = c.left.valid()
            ? rewrite_formula_simultaneous(builder, c.left, rename) : c.left;
        auto nr = c.right.valid()
            ? rewrite_formula_simultaneous(builder, c.right, rename) : c.right;
        if (nl == c.left && nr == c.right) return h;
        switch (c.op) {
            case Op::And:     return builder.make_and(nl, nr);
            case Op::Or:      return builder.make_or(nl, nr);
            case Op::Implies: return builder.make_implies(nl, nr);
            case Op::Iff:     return builder.make_iff(nl, nr);
            case Op::Not:     return builder.make_not(nl);
            default: return h;
        }
    }
    if (f.is_quantified()) {
        const auto& q = f.as_quantified();
        auto nb = rewrite_formula_simultaneous(builder, q.body, rename);
        if (nb == q.body) return h;
        return builder.make_quantified(q.op, nb);
    }
    return h;
}

lkr::FormulaSource rewrite_source_simultaneous(
    FormulaBuilder&                                  builder,
    const lkr::FormulaSource&                        src,
    const std::unordered_map<var_index, var_index>&  rename)
{
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        return lkr::FormulaSource{rewrite_formula_simultaneous(builder, *h, rename)};
    }
    return src;
}

// =========================================================================
// Pre-computed per-op offset map for a lemma program.
//
// LKR sequent operations are local to the current open goal. When the
// lemma is spliced into an outer context where outer-stuff precedes
// φ_L, lemma positions need to shift by an offset. The offset is
// per-open-goal (changes only at branching ops):
//   - And: LEFT subgoal resets offset to 0 (partition contains only
//     lemma indices; outer-stuff goes to RIGHT); RIGHT keeps parent's.
//   - Cut: both LEFT and RIGHT keep parent's offset.
//   - Linear ops: offset unchanged.
//   - Closing ops: pop the offset stack.
// =========================================================================

bool is_closing_op(const lkr::Instr& op) {
    return std::holds_alternative<lkr::AxiomLit>(op) ||
           std::holds_alternative<lkr::One>(op) ||
           std::holds_alternative<lkr::CloseByLemma>(op);
}

util::Result<std::vector<size_t>> compute_lemma_offsets(
    const Program<lkr::Instr>& L,
    size_t                     base_offset)
{
    std::vector<size_t> offsets(L.instrs.size(), 0);
    std::vector<size_t> stack;
    stack.push_back(base_offset);

    for (size_t i = 0; i < L.instrs.size(); ++i) {
        if (stack.empty()) {
            return MAKE_ERROR
                << "compute_lemma_offsets: empty stack at lemma op #" << i;
        }
        offsets[i] = stack.back();
        const auto& op = L.instrs[i];

        if (is_closing_op(op)) {
            stack.pop_back();
        } else if (std::holds_alternative<lkr::And>(op)) {
            size_t parent = stack.back();
            stack.pop_back();
            // LKR branching: push RIGHT first, then LEFT (LEFT on top).
            stack.push_back(parent);  // RIGHT keeps parent's offset
            stack.push_back(0);       // LEFT resets — outer-stuff went to RIGHT
        } else if (std::holds_alternative<lkr::Cut>(op)) {
            size_t parent = stack.back();
            stack.pop_back();
            stack.push_back(parent);  // RIGHT
            stack.push_back(parent);  // LEFT
        }
        // Linear ops: stack unchanged.
    }

    if (!stack.empty()) {
        return MAKE_ERROR
            << "compute_lemma_offsets: " << stack.size()
            << " open goal(s) left after last op (lemma malformed)";
    }
    return offsets;
}

// =========================================================================
// Op rewriter: apply position shift, eigen rename, TermRef shift, formula
// substitution to a single lemma op.
//
// `position_offset` is added to position fields.
// `eigen_rename` maps lemma's Forall eigens to fresh outer-context vars.
// `op_index_map` (lemma op-index → combined-program op-index) is used
//   for TermRef rewrites (Exists.witness etc.). Built incrementally as
//   ops are spliced.
// =========================================================================

util::Result<lkr::Instr> rewrite_lemma_op(
    FormulaBuilder&                                  builder,
    const lkr::Instr&                                op,
    size_t                                           pos_offset,
    const std::unordered_map<var_index, var_index>&  eigen_rename,
    const std::vector<uint32_t>&                     op_index_map)
{
    if (auto* o = std::get_if<lkr::AxiomLit>(&op)) {
        lkr::AxiomLit c = *o;
        c.lit_a += pos_offset;
        c.lit_b += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::One>(&op)) {
        lkr::One c = *o;
        c.idx += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Exchange>(&op)) {
        lkr::Exchange c = *o;
        c.i += pos_offset;
        c.j += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Contraction>(&op)) {
        lkr::Contraction c = *o;
        c.i += pos_offset;
        c.j += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Or>(&op)) {
        lkr::Or c = *o;
        c.principal += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::And>(&op)) {
        lkr::And c = *o;
        c.principal += pos_offset;
        for (auto& p : c.left_partition) p += pos_offset;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Forall>(&op)) {
        lkr::Forall c = *o;
        c.principal += pos_offset;
        auto it = eigen_rename.find(c.eigen);
        if (it != eigen_rename.end()) c.eigen = it->second;
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Exists>(&op)) {
        lkr::Exists c = *o;
        c.principal += pos_offset;
        // Witness TermRef: shift to combined op-index of the spliced
        // op that bound the term (originally an L-index, now an
        // outer-combined-index).
        if (c.witness.idx >= op_index_map.size()) {
            return MAKE_ERROR
                << "rewrite_lemma_op(Exists): witness TermRef #"
                << c.witness.idx << " out of L-index range";
        }
        c.witness.idx = op_index_map[c.witness.idx];
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Weakening>(&op)) {
        lkr::Weakening c = *o;
        c.formula = rewrite_source_simultaneous(builder, c.formula, eigen_rename);
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::Cut>(&op)) {
        lkr::Cut c = *o;
        c.cut_formula =
            rewrite_source_simultaneous(builder, c.cut_formula, eigen_rename);
        return lkr::Instr{c};
    }
    if (auto* o = std::get_if<lkr::CloseByLemma>(&op)) {
        // Nested CloseByLemma: not rewritten here. The outer splice
        // loop handles recursive splicing by re-entering the dispatch
        // on the original lemma name (no rewrite needed for CloseByLemma's
        // payload — axiom name + bindings — none of which carry positions
        // or eigens to shift).
        return lkr::Instr{*o};
    }
    return MAKE_ERROR << "rewrite_lemma_op: unknown op variant";
}

// =========================================================================
// Apply an outer op's effect to the goal-size stack (used to track the
// outer's sequent size at each CloseByLemma point).
//
// Mirrors LKRVerifier's exec_op size effects without doing any
// correctness checks (the input gate already verified the program).
// =========================================================================

void apply_outer_op_effect(
    std::vector<size_t>&     goal_sizes,
    const lkr::Instr&        op,
    const LemmaPrograms&     lemmas)
{
    if (is_closing_op(op)) {
        // CloseByLemma also closes the top goal (after splicing in
        // lemma's ops, the lemma's closer pops; net effect = one pop).
        if (!goal_sizes.empty()) goal_sizes.pop_back();
        return;
    }
    if (auto* o = std::get_if<lkr::Or>(&op)) {
        (void)o;
        if (!goal_sizes.empty()) goal_sizes.back() += 1;  // appends psi
        return;
    }
    if (std::holds_alternative<lkr::Exchange>(op) ||
        std::holds_alternative<lkr::Forall>(op) ||
        std::holds_alternative<lkr::Exists>(op)) {
        // Linear ops with no size change.
        return;
    }
    if (std::holds_alternative<lkr::Weakening>(op)) {
        if (!goal_sizes.empty()) goal_sizes.back() += 1;
        return;
    }
    if (std::holds_alternative<lkr::Contraction>(op)) {
        if (!goal_sizes.empty()) goal_sizes.back() -= 1;
        return;
    }
    if (auto* o = std::get_if<lkr::And>(&op)) {
        if (goal_sizes.empty()) return;
        size_t parent = goal_sizes.back();
        goal_sizes.pop_back();
        size_t partition_size = o->left_partition.size();
        size_t left_size  = partition_size + 1;
        size_t right_size = parent - 1 - partition_size + 1;  // - principal - partition + theta
        goal_sizes.push_back(right_size);  // RIGHT first
        goal_sizes.push_back(left_size);   // LEFT on top
        return;
    }
    if (std::holds_alternative<lkr::Cut>(op)) {
        if (goal_sizes.empty()) return;
        size_t parent = goal_sizes.back();
        goal_sizes.pop_back();
        goal_sizes.push_back(parent + 1);  // RIGHT
        goal_sizes.push_back(parent + 1);  // LEFT
        return;
    }
    (void)lemmas;
}

}  // namespace

// =========================================================================
// Main entry point.
// =========================================================================

util::Result<Program<lkr::Instr>> inline_lemmas(
    FormulaBuilder&             builder,
    FormulaHandle               initial_goal_nnf,
    const Program<lkr::Instr>&  outer,
    const LemmaPrograms&        lemmas)
{
    Program<lkr::Instr> out;
    out.claim_name = outer.claim_name;
    out.step_index = outer.step_index;

    // Track outer's open-goals stack (just sizes — we don't need the
    // formulas themselves for offset computation). Initial sequent
    // always has 1 entry (the goal).
    std::vector<size_t> goal_sizes;
    goal_sizes.push_back(1);
    (void)initial_goal_nnf;

    // Map outer op-index → combined op-index. Outer ops can carry
    // TermRefs (Exists.witness) that point to earlier outer ops; after
    // splicing lemma ops in between, those targets shift. Rewrite as
    // we go.
    std::vector<uint32_t> outer_index_map(outer.instrs.size(), 0);

    // Allocate fresh-eigen pool above any var used in outer or any lemma.
    var_index next_fresh_eigen = max_var_in_program(outer);
    for (const auto& [name, prog] : lemmas) {
        (void)name;
        next_fresh_eigen = std::max(next_fresh_eigen, max_var_in_program(prog));
    }

    for (uint32_t i = 0; i < outer.instrs.size(); ++i) {
        outer_index_map[i] = static_cast<uint32_t>(out.instrs.size());
        const auto& op = outer.instrs[i];

        if (auto* cbl = std::get_if<lkr::CloseByLemma>(&op)) {
            auto it = lemmas.find(cbl->axiom.name);
            if (it == lemmas.end()) {
                return MAKE_ERROR
                    << "inline_lemmas: unknown lemma '"
                    << cbl->axiom.name << "' (not in registry)";
            }
            const Program<lkr::Instr>& L = it->second;
            if (goal_sizes.empty()) {
                return MAKE_ERROR
                    << "inline_lemmas: CloseByLemma at op #" << i
                    << " has no open goal";
            }
            size_t base_offset = goal_sizes.back() - 1;

            // Recursive splice: if L itself contains CloseByLemma,
            // resolve those first by recursively inlining L against
            // the registry. The result has no CloseByLemma ops.
            //
            // Note: the recursive call passes L's first entry size
            // (which is 1 — L starts from [φ_L] in standalone view).
            TRY_ASSIGN(L_resolved,
                inline_lemmas(builder, /*initial_goal_nnf=*/L.instrs.empty()
                                  ? initial_goal_nnf
                                  : initial_goal_nnf,  // dummy; only size matters
                              L, lemmas));
            // (initial_goal_nnf passed to recursive call is not used
            // meaningfully — the recursive call starts with size=1
            // unconditionally via the override above.)

            // Allocate eigen rename for this splice.
            std::unordered_map<var_index, var_index> eigen_rename;
            for (const auto& l_op : L_resolved.instrs) {
                if (auto* f = std::get_if<lkr::Forall>(&l_op)) {
                    auto [iter, inserted] =
                        eigen_rename.try_emplace(f->eigen, next_fresh_eigen);
                    if (inserted) ++next_fresh_eigen;
                }
            }

            // Compute per-op offsets within L.
            TRY_ASSIGN(L_offsets, compute_lemma_offsets(L_resolved, base_offset));

            // Splice L's ops, building op_index_map as we go.
            std::vector<uint32_t> op_index_map(L_resolved.instrs.size());
            for (size_t j = 0; j < L_resolved.instrs.size(); ++j) {
                op_index_map[j] = static_cast<uint32_t>(out.instrs.size());
                TRY_ASSIGN(rewritten,
                    rewrite_lemma_op(builder, L_resolved.instrs[j],
                                     L_offsets[j], eigen_rename, op_index_map));
                out.instrs.push_back(std::move(rewritten));
            }

            // Net effect of CloseByLemma on outer's goal stack: pop top.
            apply_outer_op_effect(goal_sizes, op, lemmas);
        } else {
            // Outer's own ops: position fields are correct (outer's
            // indexing). But TermRefs (Exists.witness) target outer op
            // indices that may have shifted. Rewrite through
            // outer_index_map.
            if (auto* e = std::get_if<lkr::Exists>(&op)) {
                lkr::Exists copy = *e;
                if (copy.witness.idx >= outer_index_map.size()) {
                    return MAKE_ERROR
                        << "inline_lemmas: Exists at op #" << i
                        << " witness TermRef #" << copy.witness.idx
                        << " out of outer-index range";
                }
                copy.witness.idx = outer_index_map[copy.witness.idx];
                out.instrs.emplace_back(std::move(copy));
            } else {
                out.instrs.push_back(op);
            }
            apply_outer_op_effect(goal_sizes, op, lemmas);
        }
    }

    return out;
}

}  // namespace logic::proof::translate::lkr_to_comb
