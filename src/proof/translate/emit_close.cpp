#include "emit_close.h"

#include "src/proof/lkr/literal.h"
#include "src/proof/lkr/ops.h"

#include <cstdint>
#include <utility>

namespace logic::proof::translate {

util::ResultStatus emit_close(Env&            env,
                              SequentEntry    pos_entry,
                              SequentEntry    neg_entry,
                              EigenSupply&    eigens,
                              FormulaBuilder& builder,
                              Program<lkr::Instr>& out)
{
    TRY_ASSIGN(a,        env.formula_at(pos_entry));
    TRY_ASSIGN(b,        env.formula_at(neg_entry));
    TRY_ASSIGN(pos_pos,  env.position_of(pos_entry));
    TRY_ASSIGN(neg_pos,  env.position_of(neg_entry));

    // Atomic literal pair — close via AxiomLit.
    if (lkr::is_atomic_literal(a) && lkr::is_atomic_literal(b)) {
        if (!lkr::is_dual(a, b)) {
            return MAKE_ERROR
                << "emit_close: atomic literals at positions "
                << pos_pos << " and " << neg_pos << " are not dual";
        }
        lkr::AxiomLit ax{}; ax.lit_a = pos_pos; ax.lit_b = neg_pos;
        out.instrs.emplace_back(std::move(ax));
        return util::Ok();
    }

    // Truth literal (¬⊥) on either side — close via One.
    if (lkr::is_top_literal(a)) {
        lkr::One one{}; one.idx = pos_pos;
        out.instrs.emplace_back(std::move(one));
        return util::Ok();
    }
    if (lkr::is_top_literal(b)) {
        lkr::One one{}; one.idx = neg_pos;
        out.instrs.emplace_back(std::move(one));
        return util::Ok();
    }

    const Formula& fa = a.get();
    const Formula& fb = b.get();

    // pos = (φ ∨ ψ), neg = NNF(¬φ) ∧ NNF(¬ψ).
    //
    // Conjunction child order in NNF is not canonical: NNF(¬(A → B)) is
    // (NNF(A) ∧ NNF(¬B)), but NNF(¬(B → A)) is (NNF(B) ∧ NNF(¬A)) — both
    // semantic duals of (NNF(¬A) ∨ NNF(B)) and (NNF(A) ∨ NNF(¬B))
    // respectively, but the surface child orders differ. We accept both
    // orderings explicitly.
    if (fa.is_compound() && fa.as_compound().op == Op::Or) {
        if (!(fb.is_compound() && fb.as_compound().op == Op::And)) {
            return MAKE_ERROR
                << "emit_close: pos is ∨ but neg is not ∧ dual (positions "
                << pos_pos << " / " << neg_pos << ")";
        }
        FormulaHandle phi     = fa.as_compound().left;
        FormulaHandle psi     = fa.as_compound().right;
        FormulaHandle b_left  = fb.as_compound().left;
        FormulaHandle b_right = fb.as_compound().right;
        FormulaHandle neg_phi = builder.to_nnf(builder.make_not(phi));
        FormulaHandle neg_psi = builder.to_nnf(builder.make_not(psi));

        bool order_normal  = (b_left == neg_phi && b_right == neg_psi);
        bool order_swapped = (b_left == neg_psi && b_right == neg_phi);
        if (!order_normal && !order_swapped) {
            return MAKE_ERROR
                << "emit_close: Or/And dual children do not match in either order "
                   "(positions " << pos_pos << " / " << neg_pos << ")";
        }

        // Or on pos: pos slot becomes φ, ψ appended at end.
        lkr::Or orop{}; orop.principal = pos_pos;
        out.instrs.emplace_back(std::move(orop));
        TRY_ASSIGN(psi_entry, env.apply_or(pos_entry));

        // Route the Or's children so each pairs with the matching dual on
        // its destination side of the multiplicative-And split.
        SequentEntry to_left, to_right;
        if (order_normal) {
            to_left  = pos_entry;   // (= φ) paired with neg's left_phi (= NNF(¬φ))
            to_right = psi_entry;   // (= ψ) paired with neg's right_psi (= NNF(¬ψ))
        } else {
            to_left  = psi_entry;   // (= ψ) paired with neg's left_phi (= NNF(¬ψ))
            to_right = pos_entry;   // (= φ) paired with neg's right_psi (= NNF(¬φ))
        }

        TRY_ASSIGN(split, env.apply_and(neg_entry, {to_left}, {to_right}));
        lkr::And andop{};
        andop.principal      = neg_pos;        // pre-And position of neg
        andop.left_partition = split.left_partition;
        out.instrs.emplace_back(std::move(andop));

        TRY(emit_close(split.left,  to_left,  split.left_phi,
                       eigens, builder, out));
        return emit_close(split.right, to_right, split.right_psi,
                           eigens, builder, out);
    }

    // pos = (φ ∧ ψ), neg = NNF(¬φ) ∨ NNF(¬ψ) — swap roles.
    if (fa.is_compound() && fa.as_compound().op == Op::And) {
        if (!(fb.is_compound() && fb.as_compound().op == Op::Or)) {
            return MAKE_ERROR
                << "emit_close: pos is ∧ but neg is not ∨ dual (positions "
                << pos_pos << " / " << neg_pos << ")";
        }
        return emit_close(env, neg_entry, pos_entry, eigens, builder, out);
    }

    // pos = ∀x.φ, neg = ∃x.NNF(¬φ).
    if (fa.is_quantified() && fa.as_quantified().op == Op::Forall) {
        if (!(fb.is_quantified() && fb.as_quantified().op == Op::Exists)) {
            return MAKE_ERROR
                << "emit_close: pos is ∀ but neg is not ∃ dual (positions "
                << pos_pos << " / " << neg_pos << ")";
        }
        var_index v = eigens.fresh();
        uint32_t forall_idx = static_cast<uint32_t>(out.instrs.size());
        lkr::Forall fop{}; fop.principal = pos_pos; fop.eigen = v;
        out.instrs.emplace_back(std::move(fop));
        TRY(env.apply_forall(pos_entry, v, builder));

        // neg has not moved; re-resolve its position (apply_forall mutates
        // contents, not order, but we re-resolve defensively).
        TRY_ASSIGN(neg_pos2, env.position_of(neg_entry));
        lkr::Exists ex{}; ex.principal = neg_pos2;
        ex.witness = TermRef{forall_idx};
        out.instrs.emplace_back(std::move(ex));
        TRY(env.apply_exists(neg_entry, Term::fixed(v), builder));

        return emit_close(env, pos_entry, neg_entry, eigens, builder, out);
    }

    // pos = ∃x.φ, neg = ∀x.NNF(¬φ) — swap roles.
    if (fa.is_quantified() && fa.as_quantified().op == Op::Exists) {
        if (!(fb.is_quantified() && fb.as_quantified().op == Op::Forall)) {
            return MAKE_ERROR
                << "emit_close: pos is ∃ but neg is not ∀ dual (positions "
                << pos_pos << " / " << neg_pos << ")";
        }
        return emit_close(env, neg_entry, pos_entry, eigens, builder, out);
    }

    return MAKE_ERROR
        << "emit_close: unhandled NNF dual pair at positions "
        << pos_pos << " and " << neg_pos;
}

}  // namespace logic::proof::translate
