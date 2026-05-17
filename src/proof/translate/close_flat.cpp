// close_flat — LEFT-branch realizer for one ND flat step.
//
// Each translate_flat_step in the ND→LKR translator emits Cut(F_k_nnf)
// and recurses into close_flat to close the LEFT subgoal (where F_k_nnf
// is now an additional hypothesis). This file is the per-op dispatch
// table: one lambda per nd::Instr variant, each emitting the LKR ops
// that realize that ND rule.
//
// The dispatcher calls emit_close once it has reduced the goal to a pair
// of NNF-dual entries; emit_close handles the rest (structural recursion
// into And/Or/∀/∃ duals).
//
// Lives in its own translation unit so nd_to_lkr.cpp can stay focused on
// Phase A (decompose, compute formulas, deps planning) and Phase B's
// orchestration (translate_block, translate_flat_step). All shared
// internal types are declared in nd_to_lkr_internal.h.

#include "nd_to_lkr_internal.h"

#include "emit_close.h"
#include "env.h"
#include "pass.h"

#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <utility>
#include <variant>

namespace logic::proof::translate::detail {

util::ResultStatus close_flat(LowerCtx&                 lc,
                              Env&                      env,
                              uint32_t                  k,
                              const Program<nd::Instr>& in,
                              SequentEntry              F_k_entry,
                              const StepNegMap&         step_to_neg)
{
    const auto& instr = in.instrs[k];

    auto require_neg = [&](StepRef r, const char* op) -> util::Result<SequentEntry> {
        auto it2 = step_to_neg.find(r.idx);
        if (it2 == step_to_neg.end()) {
            return MAKE_ERROR << op << ": step %" << r.idx
                              << " not cut-in (op %" << k << ")";
        }
        return it2->second;
    };
    auto require_term = [&](TermRef r, const char* op) -> util::Result<Term> {
        auto it2 = lc.term_for_idx.find(r.idx);
        if (it2 == lc.term_for_idx.end()) {
            return MAKE_ERROR << op << ": ND term %" << r.idx << " unbound";
        }
        return it2->second;
    };
    auto require_lkr_termref = [&](TermRef r, const char* op) -> util::Result<TermRef> {
        auto it2 = lc.nd_to_lkr_termref.find(r.idx);
        if (it2 == lc.nd_to_lkr_termref.end()) {
            return MAKE_ERROR << op << ": ND term %" << r.idx
                              << " has no LKR-side binding";
        }
        return TermRef{it2->second};
    };

    return std::visit(overloaded{

        [&](const nd::Use& op) -> util::ResultStatus {
            lkr::CloseByLemma cb{}; cb.axiom = AxiomRef{op.axiom.name};
            lc.out.instrs.emplace_back(std::move(cb));
            return util::Ok();
        },

        [&](const nd::SchemaInst& op) -> util::ResultStatus {
            lkr::CloseByLemma cb{};
            cb.axiom    = AxiomRef{op.data.schema.name};
            cb.bindings = op.data.bindings;
            lc.out.instrs.emplace_back(std::move(cb));
            return util::Ok();
        },

        [&](const nd::ForallElim& op) -> util::ResultStatus {
            TRY_ASSIGN(neg_F_h,    require_neg(op.formula,    "forall_elim"));
            TRY_ASSIGN(witness_t,  require_term(op.term,      "forall_elim"));
            TRY_ASSIGN(witness_lkr, require_lkr_termref(op.term, "forall_elim"));

            TRY_ASSIGN(neg_pos, env.position_of(neg_F_h));
            lkr::Exists ex{}; ex.principal = neg_pos; ex.witness = witness_lkr;
            lc.out.instrs.emplace_back(std::move(ex));
            TRY(env.apply_exists(neg_F_h, witness_t, lc.builder));

            return emit_close(env, F_k_entry, neg_F_h,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::ImpliesElim& op) -> util::ResultStatus {
            // ¬F_impl = NNF(A) ∧ NNF(¬B); ¬F_ant = NNF(¬A); F_k = NNF(B).
            TRY_ASSIGN(neg_impl, require_neg(op.impl, "implies_elim"));
            TRY_ASSIGN(neg_ant,  require_neg(op.ant,  "implies_elim"));

            TRY_ASSIGN(neg_impl_pos, env.position_of(neg_impl));
            TRY_ASSIGN(split,
                env.apply_and(neg_impl, {neg_ant}, {F_k_entry}));
            lkr::And andop{};
            andop.principal      = neg_impl_pos;
            andop.left_partition = split.left_partition;
            lc.out.instrs.emplace_back(std::move(andop));

            TRY(emit_close(split.left, neg_ant, split.left_phi,
                           lc.eigens, lc.builder, lc.out));
            return emit_close(split.right, F_k_entry, split.right_psi,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::AndIntro& op) -> util::ResultStatus {
            TRY_ASSIGN(neg_a, require_neg(op.a, "and_intro"));
            TRY_ASSIGN(neg_b, require_neg(op.b, "and_intro"));

            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            TRY_ASSIGN(split, env.apply_and(F_k_entry, {neg_a}, {neg_b}));
            lkr::And andop{};
            andop.principal      = F_k_pos;
            andop.left_partition = split.left_partition;
            lc.out.instrs.emplace_back(std::move(andop));

            TRY(emit_close(split.left, split.left_phi, neg_a,
                           lc.eigens, lc.builder, lc.out));
            return emit_close(split.right, split.right_psi, neg_b,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::AndElimL& op) -> util::ResultStatus {
            // ¬F_of = NNF(¬A) ∨ NNF(¬B). Or on it; close F_k vs the new ¬A.
            TRY_ASSIGN(neg_of, require_neg(op.of, "and_elim_l"));
            TRY_ASSIGN(neg_of_pos, env.position_of(neg_of));
            lkr::Or orop{}; orop.principal = neg_of_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY(env.apply_or(neg_of));    // discard appended ¬B (unused)

            return emit_close(env, F_k_entry, neg_of,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::AndElimR& op) -> util::ResultStatus {
            TRY_ASSIGN(neg_of, require_neg(op.of, "and_elim_r"));
            TRY_ASSIGN(neg_of_pos, env.position_of(neg_of));
            lkr::Or orop{}; orop.principal = neg_of_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY_ASSIGN(neg_b, env.apply_or(neg_of));    // ¬B at end

            return emit_close(env, F_k_entry, neg_b,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::OrIntroL& op) -> util::ResultStatus {
            // F_k = A ∨ B. Or on F_k; close F_k (= A) vs ¬F_a (= ¬A).
            TRY_ASSIGN(neg_a, require_neg(op.a, "or_intro_l"));
            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            lkr::Or orop{}; orop.principal = F_k_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY(env.apply_or(F_k_entry));

            return emit_close(env, F_k_entry, neg_a,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::OrIntroR& op) -> util::ResultStatus {
            TRY_ASSIGN(neg_b, require_neg(op.b, "or_intro_r"));
            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            lkr::Or orop{}; orop.principal = F_k_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY_ASSIGN(B_entry, env.apply_or(F_k_entry));

            return emit_close(env, B_entry, neg_b,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::OrElim& op) -> util::ResultStatus {
            // F_k = C; ¬F_or = NNF(¬A) ∧ NNF(¬B); ¬F_ac = NNF(A) ∧ NNF(¬C);
            // ¬F_bc = NNF(B) ∧ NNF(¬C). The two case-eliminators each need
            // F_k (= C) on their own subgoal — duplicate it via Weakening.
            //
            // If both case-eliminators reference the *same* derived step
            // (e.g., `or_elim h, hf, hf` in a proof where both branches
            // share an implication), neg_ac == neg_bc and we must also
            // weaken to duplicate that entry so the partition is disjoint.
            TRY_ASSIGN(neg_or, require_neg(op.or_formula, "or_elim"));
            TRY_ASSIGN(neg_ac, require_neg(op.ac,         "or_elim"));
            TRY_ASSIGN(neg_bc, require_neg(op.bc,         "or_elim"));

            TRY_ASSIGN(F_k_nnf, env.formula_at(F_k_entry));
            lkr::Weakening w_fk{}; w_fk.formula = F_k_nnf;
            lc.out.instrs.emplace_back(std::move(w_fk));
            SequentEntry F_k_dup = env.push(F_k_nnf);

            if (neg_ac == neg_bc) {
                TRY_ASSIGN(neg_bc_fml, env.formula_at(neg_bc));
                lkr::Weakening w_nbc{}; w_nbc.formula = neg_bc_fml;
                lc.out.instrs.emplace_back(std::move(w_nbc));
                neg_bc = env.push(neg_bc_fml);
            }

            TRY_ASSIGN(neg_or_pos, env.position_of(neg_or));
            TRY_ASSIGN(outer,
                env.apply_and(neg_or, {neg_ac, F_k_entry},
                                       {neg_bc, F_k_dup}));
            lkr::And outer_and{};
            outer_and.principal      = neg_or_pos;
            outer_and.left_partition = outer.left_partition;
            lc.out.instrs.emplace_back(std::move(outer_and));

            // ---- LEFT branch: outer And's left_phi = NNF(¬A); ----
            // need to close ¬A vs A from neg_ac, plus ¬C from neg_ac vs F_k.
            {
                Env& le = outer.left;
                TRY_ASSIGN(neg_ac_pos, le.position_of(neg_ac));
                TRY_ASSIGN(inner,
                    le.apply_and(neg_ac, {outer.left_phi}, {F_k_entry}));
                lkr::And inner_and{};
                inner_and.principal      = neg_ac_pos;
                inner_and.left_partition = inner.left_partition;
                lc.out.instrs.emplace_back(std::move(inner_and));

                // inner.left_phi = NNF(A); pair with NNF(¬A) at outer.left_phi.
                TRY(emit_close(inner.left, inner.left_phi, outer.left_phi,
                               lc.eigens, lc.builder, lc.out));
                // inner.right_psi = NNF(¬C); pair with NNF(C) at F_k_entry.
                TRY(emit_close(inner.right, F_k_entry, inner.right_psi,
                               lc.eigens, lc.builder, lc.out));
            }

            // ---- RIGHT branch: outer And's right_psi = NNF(¬B); ----
            {
                Env& re = outer.right;
                TRY_ASSIGN(neg_bc_pos, re.position_of(neg_bc));
                TRY_ASSIGN(inner,
                    re.apply_and(neg_bc, {outer.right_psi}, {F_k_dup}));
                lkr::And inner_and{};
                inner_and.principal      = neg_bc_pos;
                inner_and.left_partition = inner.left_partition;
                lc.out.instrs.emplace_back(std::move(inner_and));

                TRY(emit_close(inner.left, inner.left_phi, outer.right_psi,
                               lc.eigens, lc.builder, lc.out));
                TRY(emit_close(inner.right, F_k_dup, inner.right_psi,
                               lc.eigens, lc.builder, lc.out));
            }
            return util::Ok();
        },

        [&](const nd::IffIntro& op) -> util::ResultStatus {
            // F_k_nnf = And(L_phi, L_psi) where L_phi, L_psi are the iff's
            // two implication NNFs (Or shapes). ¬F_ab and ¬F_ba are their
            // structural duals (in NNF). Outer multiplicative-And on F_k:
            // route ¬F_ab to LEFT, ¬F_ba to RIGHT. Then emit_close on each
            // pair (or_child, ¬_child) handles the rest — including any
            // commutativity reordering between the iff conjunct shapes.
            TRY_ASSIGN(neg_ab, require_neg(op.ab, "iff_intro"));
            TRY_ASSIGN(neg_ba, require_neg(op.ba, "iff_intro"));

            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            TRY_ASSIGN(split, env.apply_and(F_k_entry, {neg_ab}, {neg_ba}));
            lkr::And andop{};
            andop.principal      = F_k_pos;
            andop.left_partition = split.left_partition;
            lc.out.instrs.emplace_back(std::move(andop));

            TRY(emit_close(split.left, split.left_phi, neg_ab,
                           lc.eigens, lc.builder, lc.out));
            return emit_close(split.right, split.right_psi, neg_ba,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::IffElimL& op) -> util::ResultStatus {
            // F_k = NNF(B); ¬F_iff = (NNF(A) ∧ NNF(¬B)) ∨ (NNF(¬A) ∧ NNF(B));
            // ¬F_a = NNF(¬A). Or on ¬F_iff: original slot becomes left
            // disjunct (A ∧ ¬B); right disjunct (¬A ∧ B) appended.
            // Multiplicative And on (A ∧ ¬B): LEFT pairs left_phi (= A) with
            // ¬F_a (= ¬A); RIGHT pairs right_psi (= ¬B) with F_k (= B).
            TRY_ASSIGN(neg_iff, require_neg(op.iff, "iff_elim_l"));
            TRY_ASSIGN(neg_a,   require_neg(op.a,   "iff_elim_l"));
            TRY_ASSIGN(neg_iff_pos, env.position_of(neg_iff));
            lkr::Or orop{}; orop.principal = neg_iff_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY(env.apply_or(neg_iff));   // appended (¬A ∧ B) is unused

            TRY_ASSIGN(neg_iff_pos2, env.position_of(neg_iff));
            TRY_ASSIGN(split,
                env.apply_and(neg_iff, {neg_a}, {F_k_entry}));
            lkr::And andop{};
            andop.principal      = neg_iff_pos2;
            andop.left_partition = split.left_partition;
            lc.out.instrs.emplace_back(std::move(andop));

            TRY(emit_close(split.left, split.left_phi, neg_a,
                           lc.eigens, lc.builder, lc.out));
            return emit_close(split.right, F_k_entry, split.right_psi,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::IffElimR& op) -> util::ResultStatus {
            // F_k = NNF(A); ¬F_iff = (NNF(A) ∧ NNF(¬B)) ∨ (NNF(¬A) ∧ NNF(B));
            // ¬F_b = NNF(¬B). Or on ¬F_iff: original slot becomes left
            // disjunct (A ∧ ¬B); right disjunct (¬A ∧ B) appended.
            // Multiplicative And on the appended (¬A ∧ B): LEFT pairs
            // left_phi (= ¬A) with F_k (= A); RIGHT pairs right_psi (= B)
            // with ¬F_b (= ¬B).
            TRY_ASSIGN(neg_iff, require_neg(op.iff, "iff_elim_r"));
            TRY_ASSIGN(neg_b,   require_neg(op.b,   "iff_elim_r"));
            TRY_ASSIGN(neg_iff_pos, env.position_of(neg_iff));
            lkr::Or orop{}; orop.principal = neg_iff_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY_ASSIGN(appended, env.apply_or(neg_iff));

            TRY_ASSIGN(appended_pos, env.position_of(appended));
            TRY_ASSIGN(split,
                env.apply_and(appended, {F_k_entry}, {neg_b}));
            lkr::And andop{};
            andop.principal      = appended_pos;
            andop.left_partition = split.left_partition;
            lc.out.instrs.emplace_back(std::move(andop));

            TRY(emit_close(split.left, F_k_entry, split.left_phi,
                           lc.eigens, lc.builder, lc.out));
            return emit_close(split.right, split.right_psi, neg_b,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::ExistsIntro& op) -> util::ResultStatus {
            if (!op.witness.has_value()) {
                return MAKE_ERROR
                    << "exists_intro: scope-closing form must be a block closer";
            }
            TRY_ASSIGN(neg_body, require_neg(op.body, "exists_intro"));
            TRY_ASSIGN(witness_lkr,
                require_lkr_termref(*op.witness, "exists_intro"));
            TRY_ASSIGN(witness_t,
                require_term(*op.witness, "exists_intro"));

            // F_k_nnf = ∃x.NNF(body). Emit Exists with the supplied witness;
            // F_k_entry now contains body[witness], which pairs with neg_body.
            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            lkr::Exists ex{}; ex.principal = F_k_pos; ex.witness = witness_lkr;
            lc.out.instrs.emplace_back(std::move(ex));
            TRY(env.apply_exists(F_k_entry, witness_t, lc.builder));

            return emit_close(env, F_k_entry, neg_body,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::ExcludedMiddle& op) -> util::ResultStatus {
            // F_k = A ∨ ¬A. Or on F_k; pair both halves.
            (void)op;
            TRY_ASSIGN(F_k_pos, env.position_of(F_k_entry));
            lkr::Or orop{}; orop.principal = F_k_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY_ASSIGN(neg_A_entry, env.apply_or(F_k_entry));
            return emit_close(env, F_k_entry, neg_A_entry,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const nd::BottomElim& op) -> util::ResultStatus {
            // F_k = target; we close by classical absurdity. Find the
            // not_elim that produced ⊥ and pair its operands' negations.
            const auto& bot_instr = in.instrs[op.bottom.idx];
            const nd::NotElim* ne = std::get_if<nd::NotElim>(&bot_instr);
            if (!ne) {
                return MAKE_ERROR
                    << "bottom_elim: bot step %" << op.bottom.idx
                    << " is not a not_elim";
            }
            TRY_ASSIGN(neg_neg, require_neg(ne->negation, "bottom_elim"));
            TRY_ASSIGN(neg_pos, require_neg(ne->formula,  "bottom_elim"));
            return emit_close(env, neg_neg, neg_pos,
                              lc.eigens, lc.builder, lc.out);
        },

        [&](const auto& op) -> util::ResultStatus {
            (void)op;
            return MAKE_ERROR
                << "close_flat: ND op variant index "
                << instr.index() << " not yet supported";
        },

    }, instr);
}

}  // namespace logic::proof::translate::detail
