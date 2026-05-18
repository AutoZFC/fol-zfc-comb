#include "alpha_rename.h"

#include "cut_augment.h"
#include "sequent_replay.h"

#include "src/proof/comb/comb_proof.h"

#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// Simultaneous substitution: walk the formula tree once, mapping every
// Fixed(v) with v in `rename` to Fixed(rename[v]). One-pass is essential
// because sequential single-substitution chains clobber themselves when
// the map is a permutation (e.g. {0→1, 1→0}).
//
// Gen indices, schema vars (other than via their args), and the
// compound/quantified shape are preserved.
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

FormulaHandle rewrite_formula(
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
        if (c.op == Op::Bottom) return h;  // no children, no fix-vars
        auto nl = c.left.valid()  ? rewrite_formula(builder, c.left,  rename) : c.left;
        auto nr = c.right.valid() ? rewrite_formula(builder, c.right, rename) : c.right;
        if (nl == c.left && nr == c.right) return h;
        switch (c.op) {
            case Op::And:     return builder.make_and(nl, nr);
            case Op::Or:      return builder.make_or(nl, nr);
            case Op::Implies: return builder.make_implies(nl, nr);
            case Op::Iff:     return builder.make_iff(nl, nr);
            case Op::Not:     return builder.make_not(nl);
            default: return h;  // unreachable for well-formed NNF formulas
        }
    }
    if (f.is_quantified()) {
        const auto& q = f.as_quantified();
        auto nb = rewrite_formula(builder, q.body, rename);
        if (nb == q.body) return h;
        return builder.make_quantified(q.op, nb);
    }
    // SchemaVar and other shapes: assume no fix-vars buried inside (the
    // LKR pipeline operates post-iota-elim on schema-free formulas).
    return h;
}

// Apply rename to a FormulaSource. Deferred-AST variants are passed
// through (they only arise from hand-crafted programs and contain no
// trace fix-vars from a translator).
lkr::FormulaSource rewrite_source(
    FormulaBuilder&                                  builder,
    const lkr::FormulaSource&                        src,
    const std::unordered_map<var_index, var_index>&  rename)
{
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        return lkr::FormulaSource{rewrite_formula(builder, *h, rename)};
    }
    return src;
}

}  // namespace

util::Result<Program<lkr::Instr>> alpha_rename_to_canonical(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& in)
{
    // === Phase A: compute the rename map against the un-renamed program. ===
    TRY_ASSIGN(cut_aug_orig, build_cut_augmentation(builder, goal_nnf, in));
    comb::Fograph canonical_target_orig(cut_aug_orig.augmented_goal);
    TRY_ASSIGN(replay_orig,
        replay_sequents(builder, goal_nnf, in, cut_aug_orig));

    std::unordered_map<var_index, var_index> rename;
    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        auto* op = std::get_if<lkr::Forall>(&in.instrs[i]);
        if (!op) continue;
        if (op->principal >= replay_orig.entry_positions[i].size()) {
            return MAKE_ERROR
                << "alpha_rename: Forall at op #" << i
                << " principal " << op->principal
                << " out of range in replay";
        }
        const auto& positions = replay_orig.entry_positions[i][op->principal];
        if (positions.empty()) {
            return MAKE_ERROR
                << "alpha_rename: Forall at op #" << i
                << " has empty principal positions";
        }
        size_t binder_pos = positions[0];
        if (binder_pos >= canonical_target_orig.labels.size()) {
            return MAKE_ERROR
                << "alpha_rename: Forall at op #" << i
                << " binder_pos " << binder_pos
                << " out of canonical target range";
        }
        const auto& lbl = canonical_target_orig.labels[binder_pos];
        if (lbl.kind != comb::VertexKind::Binder) {
            return MAKE_ERROR
                << "alpha_rename: canonical position " << binder_pos
                << " for Forall #" << i << " is not a binder";
        }
        var_index canonical = lbl.var;
        if (op->eigen == canonical) continue;
        auto [it, inserted] = rename.emplace(op->eigen, canonical);
        if (!inserted && it->second != canonical) {
            return MAKE_ERROR
                << "alpha_rename: Forall at op #" << i
                << " eigen " << op->eigen
                << " maps to canonical " << canonical
                << " but was already mapped to " << it->second
                << " (LKR program reuses an eigen for distinct binders)";
        }
    }

    // === Phase B: apply the rename map to produce the renamed program. ===
    Program<lkr::Instr> out;
    out.claim_name  = in.claim_name;
    out.step_index  = in.step_index;
    out.instrs.reserve(in.instrs.size());

    for (const auto& instr : in.instrs) {
        if (auto* op = std::get_if<lkr::Forall>(&instr)) {
            lkr::Forall copy = *op;
            auto it = rename.find(copy.eigen);
            if (it != rename.end()) copy.eigen = it->second;
            out.instrs.emplace_back(std::move(copy));
            continue;
        }
        if (auto* op = std::get_if<lkr::Cut>(&instr)) {
            lkr::Cut copy = *op;
            copy.cut_formula = rewrite_source(builder, copy.cut_formula, rename);
            out.instrs.emplace_back(std::move(copy));
            continue;
        }
        if (auto* op = std::get_if<lkr::Weakening>(&instr)) {
            lkr::Weakening copy = *op;
            copy.formula = rewrite_source(builder, copy.formula, rename);
            out.instrs.emplace_back(std::move(copy));
            continue;
        }
        out.instrs.emplace_back(instr);
    }

    return out;
}

}  // namespace logic::proof::translate::lkr_to_comb
