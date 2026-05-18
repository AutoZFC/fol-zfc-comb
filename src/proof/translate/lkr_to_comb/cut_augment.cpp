#include "cut_augment.h"

#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

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

}  // namespace

util::Result<CutAugmentation> build_cut_augmentation(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog)
{
    CutAugmentation r;
    // Pass 1: collect cut formulas in op order, computing NNF(¬θ_k) and
    // accumulated start positions.
    FormulaHandle augmented = goal_nnf;
    size_t pos = count_vertices(goal_nnf);
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        auto* cut = std::get_if<lkr::Cut>(&prog.instrs[i]);
        if (!cut) continue;
        auto* h = std::get_if<FormulaHandle>(&cut->cut_formula);
        if (!h || !h->valid()) {
            return MAKE_ERROR
                << "cut_augmentation: Cut at op #" << i
                << " uses deferred-AST FormulaSource (unsupported)";
        }
        FormulaHandle theta = *h;
        FormulaHandle theta_nnf = builder.to_nnf(theta);
        FormulaHandle neg_theta_nnf = builder.to_nnf_neg(theta);

        size_t t_count   = count_vertices(theta_nnf);
        size_t neg_count = count_vertices(neg_theta_nnf);

        r.theta_start.push_back(pos);
        r.theta_count.push_back(t_count);
        r.neg_theta_count.push_back(neg_count);
        r.theta.push_back(theta_nnf);
        r.neg_theta.push_back(neg_theta_nnf);

        // Build the (θ ∧ ¬θ) block and append as a disjunct.
        FormulaHandle block = builder.make_and(theta_nnf, neg_theta_nnf);
        augmented = builder.make_or(augmented, block);

        pos += t_count + neg_count;
    }
    r.augmented_goal = augmented;
    return r;
}

}  // namespace logic::proof::translate::lkr_to_comb
