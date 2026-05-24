#include "dispatcher.h"

#include "block_tree.h"
#include "combining.h"
#include "emit_close.h"
#include "intros.h"
#include "projections.h"

#include "src/core/formula.h"

#include <algorithm>
#include <sstream>
#include <unordered_set>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr::dispatcher {

// Walk the block tree and record (closer_idx → opener_idx) for every
// non-OUTER block. Used by the dispatcher to look up an Assume opener
// from an ImpliesIntro closer (and analogues).
namespace {
void walk_block(const Block& blk, CloserToOpener& out) {
    if (blk.opener_idx != kInvalidIdx && blk.closer_idx != kInvalidIdx) {
        out[blk.closer_idx] = blk.opener_idx;
    }
    for (const auto& item : blk.body) {
        if (auto* sub = std::get_if<std::unique_ptr<Block>>(&item)) {
            walk_block(**sub, out);
        }
    }
}
}  // namespace

CloserToOpener build_closer_to_opener(const Block& root) {
    CloserToOpener out;
    walk_block(root, out);
    return out;
}

namespace {

// Forward — used by handle_intro_result.
util::ResultStatus translate_step_impl(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out);

intros::Ctx make_intros_ctx(Ctx& dcc) {
    return intros::Ctx{dcc.ctx, dcc.builder, dcc.prog, dcc.trace};
}

projections::Ctx make_projections_ctx(Ctx& dcc) {
    return projections::Ctx{dcc.ctx, dcc.builder, dcc.prog, dcc.trace};
}

// DemandDoubleNeg is a no-op at the NNF level — NNF(¬¬A) = A. The
// dispatcher normalizes it to DemandNone before passing to Phase 1.
Demand normalize_demand(const Demand& d) {
    if (std::holds_alternative<DemandDoubleNeg>(d)) {
        return Demand{DemandNone{}};
    }
    return d;
}

// =========================================================================
// Combining-elim full emission (Phase 5d).
// =========================================================================
//
// implies_elim(impl: A→B, ant: A) ⊢ B. Cut-minimal LK construction:
//
//   1. Cut(NNF(impl)):  LEFT = Γ, A→B    RIGHT = Γ, NNF(¬impl)
//      LEFT closed by recursive translation of `impl` step.
//   2. (on RIGHT, with NNF(¬impl) = A ∧ ¬B at cut_impl_idx)
//      Cut(NNF(ant)):  LEFT = Γ, A      RIGHT = Γ, NNF(¬ant)
//      LEFT closed by recursive translation of `ant` step.
//   3. (on RIGHT-of-Cut(ant), with both ¬impl and ¬ant in scope)
//      And{principal=cut_impl_idx, left_partition=[cut_ant_idx]}.
//      LEFT-subgoal: [NNF(¬ant)=¬A, phi=A]. AxiomLit(0, 1).
//      RIGHT-subgoal: [Γ-complement, psi=¬B]. AxiomLit(target_pos, psi_pos).
//
// Total: 2 Cuts + 1 And + 2 AxiomLits, plus recursion on impl and ant.
// Pure cut-minimal: no other Cuts, in line with the controlling design.
util::ResultStatus emit_implies_elim_full(
    Ctx&                       dcc,
    const SequentShadow&       shadow,
    const nd::ImpliesElim&     op,
    size_t                     target_pos,
    std::vector<lkr::Instr>&   out);

// Multiplicative And-split helper. Mirrors cut_spine's emit_and_split:
// emits And{principal, left_partition} with left_partition computed as
// (parent indices) - {principal} - right_needs. Returns LEFT and RIGHT
// post-state shadows plus remaps from parent indices to child indices.
struct AndSplitResult {
    SequentShadow                        left;
    SequentShadow                        right;
    size_t                               left_phi_idx{0};
    size_t                               right_theta_idx{0};
    std::unordered_map<size_t, size_t>   left_remap;   // parent → LEFT child
    std::unordered_map<size_t, size_t>   right_remap;  // parent → RIGHT child
};

util::Result<AndSplitResult> emit_and_split_local(
    const SequentShadow&        parent,
    size_t                      principal,
    const std::vector<size_t>&  right_needs,
    FormulaHandle               phi,
    FormulaHandle               theta,
    std::vector<lkr::Instr>&    out)
{
    std::unordered_set<size_t> right_set(
        right_needs.begin(), right_needs.end());
    if (right_set.count(principal)) {
        return MAKE_ERROR
            << "emit_and_split_local: principal #" << principal
            << " appears in right_needs";
    }

    std::vector<size_t> left_partition;
    left_partition.reserve(parent.entries.size());
    for (size_t k = 0; k < parent.entries.size(); ++k) {
        if (k == principal) continue;
        if (right_set.count(k)) continue;
        left_partition.push_back(k);
    }

    out.emplace_back(lkr::And{{}, principal, left_partition});

    AndSplitResult s;
    s.left.lkr_term_for     = parent.lkr_term_for;
    s.left.step_to_neg_idx  = parent.step_to_neg_idx;
    s.right.lkr_term_for    = parent.lkr_term_for;
    s.right.step_to_neg_idx = parent.step_to_neg_idx;

    std::vector<size_t> sorted_left = left_partition;
    std::sort(sorted_left.begin(), sorted_left.end());
    for (size_t i : sorted_left) {
        s.left_remap[i] = s.left.entries.size();
        s.left.entries.push_back(parent.entries[i]);
    }
    s.left_phi_idx = s.left.entries.size();
    s.left.entries.push_back(phi);

    for (size_t i = 0; i < parent.entries.size(); ++i) {
        if (i == principal) continue;
        if (!right_set.count(i)) continue;
        s.right_remap[i] = s.right.entries.size();
        s.right.entries.push_back(parent.entries[i]);
    }
    s.right_theta_idx = s.right.entries.size();
    s.right.entries.push_back(theta);

    return s;
}

// Closer family (Phase 5e.2): NOT / BottomElim / ClassicalAbsurd.
// All three discharge a contradiction via the NotElim ghost at
// `bottom`. The closer emits Cut(NNF(F_neg)) + Cut(NNF(F_formula))
// + recurses on each LEFT branch + emit_close on the duals visible
// in the final RIGHT branch. For NotIntro and ClassicalAbsurd, the
// closer also records the matching Assume opener's dual at target_pos
// so body-side references close correctly.
util::ResultStatus emit_contradiction_close(
    Ctx&                     dcc,
    SequentShadow            shadow,
    uint32_t                 closer_step_idx,
    StepRef                  notelim_bottom,
    bool                     record_assume_dual,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out);

// or_elim full emission (Phase 5e.4). 3 Cuts + Weakening{C} + outer
// And on ¬or + two nested Ands on ¬ac and ¬bc + 4 AxiomLits.
util::ResultStatus emit_or_elim_full(
    Ctx&                     dcc,
    SequentShadow            shadow,
    const nd::OrElim&        op,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out);

// exists_elim full emission (Phase 5e.4). 1 Cut(∃x.φ) on the existential
// formula step + Forall on the dualized ∀x.¬φ with eigen v + recurse on
// the body's last step (the block's C-deriving step).
util::ResultStatus emit_exists_elim_full(
    Ctx&                     dcc,
    SequentShadow            shadow,
    const nd::ExistsIntro&   op,
    uint32_t                 closer_step_idx,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out);

}  // namespace

// Forward-declared above for use inside translate_step_impl's visitor.
namespace {

util::ResultStatus handle_intro_result(
    Ctx&                     dcc,
    intros::IntroResult      result,
    std::vector<lkr::Instr>& out)
{
    if (std::holds_alternative<intros::ZeroPremise>(result)) {
        return util::Ok();
    }
    if (auto* one = std::get_if<intros::OnePremise>(&result)) {
        return translate_step_impl(
            dcc, std::move(one->shadow), one->premise_step,
            one->premise_pos, Demand{DemandNone{}}, out);
    }
    if (auto* two = std::get_if<intros::TwoPremise>(&result)) {
        // LKR's And/Cut push LEFT on top — recurse on LEFT first so
        // its emitted ops follow the branching op in the linear stream.
        TRY(translate_step_impl(
            dcc, std::move(two->left_shadow), two->left_step,
            two->left_pos, Demand{DemandNone{}}, out));
        return translate_step_impl(
            dcc, std::move(two->right_shadow), two->right_step,
            two->right_pos, Demand{DemandNone{}}, out);
    }
    return MAKE_ERROR << "handle_intro_result: unexpected IntroResult variant";
}

util::ResultStatus translate_step_impl(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out)
{
    if (step.idx >= dcc.prog.instrs.size()) {
        return MAKE_ERROR
            << "translate_step: step #" << step.idx
            << " out of range (program size " << dcc.prog.instrs.size() << ")";
    }
    const auto& instr = dcc.prog.instrs[step.idx];
    intros::Ctx ictx = make_intros_ctx(dcc);
    projections::Ctx pctx = make_projections_ctx(dcc);
    Demand norm_demand = normalize_demand(demand);

    return std::visit(
        [&](const auto& op) -> util::ResultStatus {
            using T = std::decay_t<decltype(op)>;

            // ---- intros family (Phase 1) ---------------------------
            if constexpr (std::is_same_v<T, nd::AndIntro>) {
                TRY_ASSIGN(r, intros::emit_and_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::OrIntroL>) {
                TRY_ASSIGN(r, intros::emit_or_intro_l(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::OrIntroR>) {
                TRY_ASSIGN(r, intros::emit_or_intro_r(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::ImpliesIntro>) {
                // emit_implies_intro emits Or which places NNF(¬A) at
                // target_pos (where A→B was). The dispatcher looks up
                // the matching Assume opener and records its dual
                // position so body-side Assume leaves can close
                // against it.
                TRY_ASSIGN(r, intros::emit_implies_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                if (auto* one = std::get_if<intros::OnePremise>(&r)) {
                    auto co = dcc.closer_to_opener.find(step.idx);
                    if (co == dcc.closer_to_opener.end()) {
                        return MAKE_ERROR
                            << "translate_step: ImpliesIntro at #" << step.idx
                            << " has no matching IMPLIES block opener";
                    }
                    // After emit_implies_intro, target_pos holds NNF(¬A).
                    one->shadow.step_to_neg_idx[co->second] = target_pos;
                }
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::IffIntro>) {
                TRY_ASSIGN(r, intros::emit_iff_intro(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::ExistsIntro>) {
                if (op.witness.has_value()) {
                    TRY_ASSIGN(r, intros::emit_exists_intro(
                        ictx, op, shadow, target_pos, out, norm_demand));
                    return handle_intro_result(dcc, std::move(r), out);
                }
                // No-witness form = EXISTS_ELIM block closer (Phase 5e.4).
                return emit_exists_elim_full(
                    dcc, std::move(shadow), op, step.idx, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::ExcludedMiddle>) {
                TRY_ASSIGN(r, intros::emit_excluded_middle(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            } else if constexpr (std::is_same_v<T, nd::Peirce>) {
                TRY_ASSIGN(r, intros::emit_peirce(
                    ictx, op, shadow, target_pos, out, norm_demand));
                return handle_intro_result(dcc, std::move(r), out);
            }

            // ---- projection elims (Phase 2) ------------------------
            else if constexpr (std::is_same_v<T, nd::AndElimL>) {
                TRY_ASSIGN(desc, projections::emit_and_elim_l(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::AndElimR>) {
                TRY_ASSIGN(desc, projections::emit_and_elim_r(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::IffElimL>) {
                TRY_ASSIGN(desc, projections::emit_iff_elim_l(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::IffElimR>) {
                TRY_ASSIGN(desc, projections::emit_iff_elim_r(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::DoubleNegElim>) {
                TRY_ASSIGN(desc, projections::emit_double_neg_elim(
                    pctx, op, shadow, target_pos));
                // Demand promotes to DemandDoubleNeg, which the
                // dispatcher normalizes back to DemandNone via
                // normalize_demand() at recursion entry.
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            } else if constexpr (std::is_same_v<T, nd::ForallElim>) {
                TRY_ASSIGN(desc, projections::emit_forall_elim(
                    pctx, op, shadow, target_pos));
                return translate_step_impl(
                    dcc, std::move(shadow), desc.producer,
                    desc.target_pos, desc.demand, out);
            }

            // ---- combining elims (Phase 5d, 5e.4) ------------------
            else if constexpr (std::is_same_v<T, nd::ImpliesElim>) {
                return emit_implies_elim_full(dcc, shadow, op, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::OrElim>) {
                return emit_or_elim_full(dcc, std::move(shadow), op, target_pos, out);
            }

            // ---- closer family (Phase 5e.2) -----------------------
            else if constexpr (std::is_same_v<T, nd::NotIntro>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/true, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::BottomElim>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/false, target_pos, out);
            } else if constexpr (std::is_same_v<T, nd::ClassicalAbsurd>) {
                return emit_contradiction_close(
                    dcc, std::move(shadow), step.idx, op.bottom,
                    /*record_assume_dual=*/true, target_pos, out);
            }

            // ---- Use / SchemaInst (deprecated leaf; Stage 1 normally
            // eliminates them, but kept for tests bypassing Stage 1).
            // Cut-minimal: emit Cut(NNF(lemma)) so the lemma's NNF
            // lands on LEFT (where CloseByLemma can match it), then
            // close RIGHT via emit_close or demand-aware Exists.
            else if constexpr (std::is_same_v<T, nd::Use> ||
                               std::is_same_v<T, nd::SchemaInst>) {
                FormulaHandle lemma_f       = dcc.trace.step_env[step.idx];
                FormulaHandle lemma_nnf     = dcc.builder.to_nnf(lemma_f);
                FormulaHandle neg_lemma_nnf = dcc.builder.to_nnf_neg(lemma_f);

                out.emplace_back(lkr::Cut{{}, lemma_nnf});

                // LEFT: lemma's NNF at end; CloseByLemma matches.
                {
                    lkr::CloseByLemma cb{};
                    if constexpr (std::is_same_v<T, nd::Use>) {
                        cb.target      = op.axiom;
                        cb.source_name = op.source_name;
                    } else {
                        cb.target = op.data;
                    }
                    out.emplace_back(std::move(cb));
                }

                // RIGHT: ¬lemma's NNF appended. Demand-aware close.
                size_t neg_pos = shadow.entries.size();
                shadow.entries.push_back(neg_lemma_nnf);

                if (auto* di = std::get_if<DemandInstance>(&norm_demand)) {
                    if (!neg_lemma_nnf.get().is_quantified() ||
                        neg_lemma_nnf.get().as_quantified().op != Op::Exists) {
                        return MAKE_ERROR
                            << "translate_step: Use/INSTANCE: NNF(¬lemma) "
                               "is not Exists";
                    }
                    out.emplace_back(lkr::Exists{{}, neg_pos, di->lkr_ref});
                    shadow.entries[neg_pos] =
                        dcc.builder.instantiate_quantifier_body(
                            neg_lemma_nnf.get().as_quantified().body, di->t);
                }

                EmitCloseContext ecc{dcc.builder};
                return emit_close(ecc, shadow, target_pos, neg_pos, out);
            }

            // ---- Let — inert formula handle; never a recursion target
            // in a well-formed proof, but if reached, emit nothing.
            else if constexpr (std::is_same_v<T, nd::Let>) {
                return util::Ok();
            }

            // ---- Assume / ExistsElim leaf (Phase 5e.1, 5e.4, 5e.5) -
            // Recursing on an Assume step (or ExistsElim opener) means
            // a downstream op references the assumption / witness body.
            // The enclosing intro / EXISTS_ELIM emission placed the
            // dual at shadow.step_to_neg_idx[step.idx].
            //
            // Under DemandNone: emit_close on (target_pos, dual_pos).
            // Under DemandInstance(t, lkr_ref): the assumed formula is
            //   ∀x.φ. Its dual at dual_pos is NNF(¬∀x.φ) = ∃x.NNF(¬φ).
            //   Emit Exists{principal=dual_pos, witness=lkr_ref} to
            //   instantiate the existential at t, leaving NNF(¬φ)[x:=t]
            //   at dual_pos — the NNF-dual of target_pos's NNF(φ[x:=t]).
            //   Then emit_close.
            else if constexpr (std::is_same_v<T, nd::Assume> ||
                               std::is_same_v<T, nd::ExistsElim>) {
                auto it = shadow.step_to_neg_idx.find(step.idx);
                if (it == shadow.step_to_neg_idx.end()) {
                    return MAKE_ERROR
                        << "translate_step: leaf step #" << step.idx
                        << " has no recorded dual position";
                }
                size_t dual_pos = it->second;

                if (auto* di = std::get_if<DemandInstance>(&norm_demand)) {
                    if (dual_pos >= shadow.entries.size()) {
                        return MAKE_ERROR
                            << "translate_step: leaf INSTANCE: dual_pos out of range";
                    }
                    FormulaHandle dual = shadow.entries[dual_pos];
                    if (!dual.get().is_quantified() ||
                        dual.get().as_quantified().op != Op::Exists) {
                        return MAKE_ERROR
                            << "translate_step: leaf INSTANCE: dual is not ∃-shaped";
                    }
                    out.emplace_back(lkr::Exists{{}, dual_pos, di->lkr_ref});
                    shadow.entries[dual_pos] =
                        dcc.builder.instantiate_quantifier_body(
                            dual.get().as_quantified().body, di->t);
                }

                EmitCloseContext ecc{dcc.builder};
                return emit_close(ecc, shadow, target_pos, dual_pos, out);
            }

            // ---- ForallIntro (Phase 5e.3 + 5e.5) ------------------
            // Look up the matching FORALL-block opener (Fix step) via
            // closer_to_opener, then pull the eigen from trace.term_env.
            //
            // Under demand=NONE: pass eigen to Phase 1, emit LKR Forall,
            // bind shadow.lkr_term_for[fix_idx] to the new Forall instr.
            //
            // Under demand=INSTANCE(t): Phase 1 short-circuits (no
            // Forall emitted). Bind shadow.lkr_term_for[fix_idx] to
            // demand.lkr_ref (the consumer's term binding) and set
            // shadow.entries[target_pos] to NNF(φ[x:=t]) so the body's
            // translation sees the instantiated formula.
            else if constexpr (std::is_same_v<T, nd::ForallIntro>) {
                auto co = dcc.closer_to_opener.find(step.idx);
                if (co == dcc.closer_to_opener.end()) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro at #" << step.idx
                        << " has no matching FORALL block opener";
                }
                uint32_t fix_idx = co->second;
                if (fix_idx >= dcc.trace.term_env.size() ||
                    fix_idx >= dcc.trace.term_present.size() ||
                    !dcc.trace.term_present[fix_idx]) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro's Fix #" << fix_idx
                        << " has no eigen in trace";
                }
                const Term& fix_term = dcc.trace.term_env[fix_idx];
                if (!fix_term.is_fixed()) {
                    return MAKE_ERROR
                        << "translate_step: ForallIntro's Fix #" << fix_idx
                        << " trace term is not a fixed variable";
                }
                var_index eigen = fix_term.as_variable();

                bool is_instance = std::holds_alternative<DemandInstance>(norm_demand);
                Term inst_t;
                TermRef inst_lkr_ref{};
                if (is_instance) {
                    const auto& di = std::get<DemandInstance>(norm_demand);
                    inst_t       = di.t;
                    inst_lkr_ref = di.lkr_ref;
                    // Pre-substitute shadow.entries[target_pos] from
                    // NNF(∀x.φ)[x:=v] (what NONE would produce) to the
                    // demanded NNF(φ[x:=t]). We compute it from the
                    // current shadow.entries[target_pos] which has
                    // NNF(∀x.φ); instantiate its body at t.
                    if (target_pos >= shadow.entries.size()) {
                        return MAKE_ERROR
                            << "translate_step: ForallIntro INSTANCE: "
                               "target_pos out of range";
                    }
                    FormulaHandle outer = shadow.entries[target_pos];
                    if (!outer.get().is_quantified() ||
                        outer.get().as_quantified().op != Op::Forall) {
                        return MAKE_ERROR
                            << "translate_step: ForallIntro INSTANCE: "
                               "target_pos entry is not Forall";
                    }
                    FormulaHandle body_f = outer.get().as_quantified().body;
                    shadow.entries[target_pos] =
                        dcc.builder.instantiate_quantifier_body(body_f, inst_t);
                }

                // emit_forall_intro emits the LKR Forall op (only under
                // NONE); its instr index is out.size() at this point.
                size_t lkr_forall_idx = out.size();
                TRY_ASSIGN(r, intros::emit_forall_intro(
                    ictx, op, eigen, shadow, target_pos, out, norm_demand));
                if (auto* one = std::get_if<intros::OnePremise>(&r)) {
                    SequentShadow::TermBinding binding;
                    if (is_instance) {
                        binding.lkr_ref = inst_lkr_ref;
                        binding.value   = inst_t;
                    } else {
                        binding.lkr_ref = TermRef{static_cast<uint32_t>(lkr_forall_idx)};
                        binding.value   = fix_term;
                    }
                    one->shadow.lkr_term_for[fix_idx] = binding;
                }
                return handle_intro_result(dcc, std::move(r), out);
            }

            // ---- not-yet-supported families ------------------------
            else {
                std::ostringstream what;
                what << "translate_step: op family (variant "
                     << instr.index()
                     << ") not yet supported in Phase 5d "
                        "(or_elim, exists_elim, structural, closer "
                        "integration lands in 5d/5e)";
                return MAKE_ERROR << what.str();
            }
        },
        instr);
}

}  // namespace

util::ResultStatus translate_step(
    Ctx&                     dcc,
    SequentShadow            shadow,
    StepRef                  step,
    size_t                   target_pos,
    Demand                   demand,
    std::vector<lkr::Instr>& out)
{
    return translate_step_impl(
        dcc, std::move(shadow), step, target_pos, demand, out);
}

namespace {

util::ResultStatus emit_implies_elim_full(
    Ctx&                     dcc,
    const SequentShadow&     shadow,
    const nd::ImpliesElim&   op,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    if (op.impl.idx >= dcc.trace.step_env.size() ||
        op.ant.idx  >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_implies_elim_full: step refs out of trace range";
    }
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR
            << "emit_implies_elim_full: target_pos out of range";
    }

    FormulaHandle impl_f       = dcc.trace.step_env[op.impl.idx];
    FormulaHandle impl_nnf     = dcc.builder.to_nnf(impl_f);
    FormulaHandle neg_impl_nnf = dcc.builder.to_nnf_neg(impl_f);
    FormulaHandle ant_f        = dcc.trace.step_env[op.ant.idx];
    FormulaHandle ant_nnf      = dcc.builder.to_nnf(ant_f);
    FormulaHandle neg_ant_nnf  = dcc.builder.to_nnf_neg(ant_f);

    if (!neg_impl_nnf.get().is_compound() ||
        neg_impl_nnf.get().as_compound().op != Op::And) {
        return MAKE_ERROR
            << "emit_implies_elim_full: NNF(¬impl) is not And-compound";
    }

    // Step 1: Cut(NNF(impl)).
    out.emplace_back(lkr::Cut{{}, impl_nnf});

    // LEFT-of-Cut(impl): shadow + NNF(impl) appended; recurse on impl.
    SequentShadow left_impl = shadow;
    size_t left_impl_pos = left_impl.entries.size();
    left_impl.entries.push_back(impl_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_impl), op.impl,
        left_impl_pos, Demand{DemandNone{}}, out));

    // RIGHT-of-Cut(impl): NNF(¬impl) appended at cut_impl_idx.
    SequentShadow right_impl = shadow;
    size_t cut_impl_idx = right_impl.entries.size();
    right_impl.entries.push_back(neg_impl_nnf);

    // Step 2: Cut(NNF(ant)) on RIGHT-of-Cut(impl).
    out.emplace_back(lkr::Cut{{}, ant_nnf});

    SequentShadow left_ant = right_impl;
    size_t left_ant_pos = left_ant.entries.size();
    left_ant.entries.push_back(ant_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_ant), op.ant,
        left_ant_pos, Demand{DemandNone{}}, out));

    // RIGHT-of-Cut(ant): NNF(¬ant) appended at cut_ant_idx.
    SequentShadow right_ant = right_impl;
    size_t cut_ant_idx = right_ant.entries.size();
    right_ant.entries.push_back(neg_ant_nnf);

    // Step 3: And{principal=cut_impl_idx, left_partition=[cut_ant_idx]}.
    out.emplace_back(lkr::And{{}, cut_impl_idx, {cut_ant_idx}});

    // LEFT-of-And: [neg_ant_nnf=¬A, phi=NNF(A)]. Dual at (0, 1).
    out.emplace_back(lkr::AxiomLit{{}, 0, 1});

    // RIGHT-of-And: [Γ-complement, psi=NNF(¬B) at end]. Dual at
    // (target_pos, psi_pos = right_ant.size() - 2).
    // (psi_pos: complement has right_ant.size()-2 entries; psi
    // appended at index complement.size() = right_ant.size()-2.)
    size_t psi_pos = right_ant.entries.size() - 2;
    out.emplace_back(lkr::AxiomLit{{}, target_pos, psi_pos});

    return util::Ok();
}

util::ResultStatus emit_contradiction_close(
    Ctx&                     dcc,
    SequentShadow            shadow,
    uint32_t                 closer_step_idx,
    StepRef                  notelim_bottom,
    bool                     record_assume_dual,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    if (notelim_bottom.idx >= dcc.prog.instrs.size()) {
        return MAKE_ERROR
            << "emit_contradiction_close: bottom #" << notelim_bottom.idx
            << " out of program range";
    }
    const auto& bot_instr = dcc.prog.instrs[notelim_bottom.idx];
    if (!std::holds_alternative<nd::NotElim>(bot_instr)) {
        return MAKE_ERROR
            << "emit_contradiction_close: bottom #" << notelim_bottom.idx
            << " is not a NotElim";
    }
    const auto& ne = std::get<nd::NotElim>(bot_instr);

    if (record_assume_dual) {
        auto co = dcc.closer_to_opener.find(closer_step_idx);
        if (co == dcc.closer_to_opener.end()) {
            return MAKE_ERROR
                << "emit_contradiction_close: closer #" << closer_step_idx
                << " has no matching block opener";
        }
        // Record the assumption-step's dual at target_pos so body-side
        // references close against it.
        shadow.step_to_neg_idx[co->second] = target_pos;
    }

    if (ne.negation.idx >= dcc.trace.step_env.size() ||
        ne.formula.idx  >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_contradiction_close: NotElim operand out of trace range";
    }
    FormulaHandle f_neg = dcc.trace.step_env[ne.negation.idx];
    FormulaHandle f_form = dcc.trace.step_env[ne.formula.idx];
    FormulaHandle f_neg_nnf  = dcc.builder.to_nnf(f_neg);
    FormulaHandle f_form_nnf = dcc.builder.to_nnf(f_form);

    // Step 1: Cut(NNF(F_neg)).
    out.emplace_back(lkr::Cut{{}, f_neg_nnf});

    // LEFT: shadow + NNF(F_neg). Recurse on neg_step.
    SequentShadow left_neg = shadow;
    size_t left_neg_pos = left_neg.entries.size();
    left_neg.entries.push_back(f_neg_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_neg), ne.negation,
        left_neg_pos, Demand{DemandNone{}}, out));

    // RIGHT: shadow + NNF(¬F_neg) (= NNF(F_formula) in NNF semantics).
    SequentShadow right_neg = shadow;
    size_t outer_dual_pos = right_neg.entries.size();
    right_neg.entries.push_back(dcc.builder.to_nnf_neg(f_neg));

    // Step 2: Cut(NNF(F_formula)) on RIGHT-of-Cut(F_neg).
    out.emplace_back(lkr::Cut{{}, f_form_nnf});

    // LEFT: right_neg + NNF(F_formula). Recurse on formula_step.
    SequentShadow left_form = right_neg;
    size_t left_form_pos = left_form.entries.size();
    left_form.entries.push_back(f_form_nnf);
    TRY(translate_step_impl(
        dcc, std::move(left_form), ne.formula,
        left_form_pos, Demand{DemandNone{}}, out));

    // RIGHT: right_neg + NNF(¬F_formula) (= NNF(F_neg)).
    SequentShadow right_form = right_neg;
    size_t inner_dual_pos = right_form.entries.size();
    right_form.entries.push_back(dcc.builder.to_nnf_neg(f_form));

    // Step 3: emit_close on the two duals (NNF(F_formula) at
    // outer_dual_pos and NNF(F_neg) at inner_dual_pos).
    EmitCloseContext ecc{dcc.builder};
    return emit_close(ecc, right_form, outer_dual_pos, inner_dual_pos, out);
}

// or_elim(or_formula: A∨B, ac: A→C, bc: B→C) ⊢ C.
//
// LK construction (cut-minimal):
//   1. Cut(NNF(or_formula)): LEFT proves A∨B; RIGHT carries
//      NNF(¬or) = ¬A ∧ ¬B.
//   2. Cut(NNF(ac)): LEFT proves A→C; RIGHT carries NNF(¬ac) = A ∧ ¬C.
//   3. Cut(NNF(bc)): LEFT proves B→C; RIGHT carries NNF(¬bc) = B ∧ ¬C.
//   4. Weakening{NNF(C)} to duplicate the target (both outer And sides
//      need a copy of C for the ¬C dual).
//   5. Outer And on ¬or = ¬A ∧ ¬B:
//        LEFT  inherits {¬ac, C(orig)}; phi = ¬A.
//        RIGHT inherits {¬bc, C(dup)}; psi = ¬B.
//   6a. LEFT outer: And on ¬ac = A ∧ ¬C:
//        LEFT inner = [¬A, A]      — emit_close on the dual pair.
//        RIGHT inner = [C, ¬C]     — emit_close on the dual pair.
//   6b. RIGHT outer: And on ¬bc = B ∧ ¬C:
//        LEFT inner = [¬B, B]      — emit_close.
//        RIGHT inner = [C, ¬C]     — emit_close.
//
// Total: 3 Cuts + 1 Weakening + 3 Ands + 4 emit_closes, plus the
// recursion on or_formula, ac, bc.
util::ResultStatus emit_or_elim_full(
    Ctx&                     dcc,
    SequentShadow            shadow,
    const nd::OrElim&        op,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    if (op.or_formula.idx >= dcc.trace.step_env.size() ||
        op.ac.idx         >= dcc.trace.step_env.size() ||
        op.bc.idx         >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_or_elim_full: step refs out of trace range";
    }
    if (target_pos >= shadow.entries.size()) {
        return MAKE_ERROR
            << "emit_or_elim_full: target_pos out of range";
    }

    FormulaHandle or_f       = dcc.trace.step_env[op.or_formula.idx];
    FormulaHandle ac_f       = dcc.trace.step_env[op.ac.idx];
    FormulaHandle bc_f       = dcc.trace.step_env[op.bc.idx];
    FormulaHandle or_nnf     = dcc.builder.to_nnf(or_f);
    FormulaHandle ac_nnf     = dcc.builder.to_nnf(ac_f);
    FormulaHandle bc_nnf     = dcc.builder.to_nnf(bc_f);
    FormulaHandle neg_or_nnf = dcc.builder.to_nnf_neg(or_f);
    FormulaHandle neg_ac_nnf = dcc.builder.to_nnf_neg(ac_f);
    FormulaHandle neg_bc_nnf = dcc.builder.to_nnf_neg(bc_f);
    FormulaHandle nnf_c      = shadow.entries[target_pos];

    // Cut 1: or_formula.
    out.emplace_back(lkr::Cut{{}, or_nnf});
    {
        SequentShadow left = shadow;
        size_t pos = left.entries.size();
        left.entries.push_back(or_nnf);
        TRY(translate_step_impl(
            dcc, std::move(left), op.or_formula, pos,
            Demand{DemandNone{}}, out));
    }
    size_t i_or = shadow.entries.size();
    shadow.entries.push_back(neg_or_nnf);

    // Cut 2: ac.
    out.emplace_back(lkr::Cut{{}, ac_nnf});
    {
        SequentShadow left = shadow;
        size_t pos = left.entries.size();
        left.entries.push_back(ac_nnf);
        TRY(translate_step_impl(
            dcc, std::move(left), op.ac, pos,
            Demand{DemandNone{}}, out));
    }
    size_t i_ac = shadow.entries.size();
    shadow.entries.push_back(neg_ac_nnf);

    // Cut 3: bc.
    out.emplace_back(lkr::Cut{{}, bc_nnf});
    {
        SequentShadow left = shadow;
        size_t pos = left.entries.size();
        left.entries.push_back(bc_nnf);
        TRY(translate_step_impl(
            dcc, std::move(left), op.bc, pos,
            Demand{DemandNone{}}, out));
    }
    size_t i_bc = shadow.entries.size();
    shadow.entries.push_back(neg_bc_nnf);

    // Weakening: duplicate C.
    out.emplace_back(lkr::Weakening{{}, nnf_c});
    size_t i_c_dup = shadow.entries.size();
    shadow.entries.push_back(nnf_c);

    // Sanity: neg_or = ¬A ∧ ¬B (And-shaped).
    if (!neg_or_nnf.get().is_compound() ||
        neg_or_nnf.get().as_compound().op != Op::And) {
        return MAKE_ERROR
            << "emit_or_elim_full: NNF(¬or) is not And-compound";
    }
    FormulaHandle neg_a = neg_or_nnf.get().as_compound().left;
    FormulaHandle neg_b = neg_or_nnf.get().as_compound().right;

    // Outer And on i_or. RIGHT_needs = {i_bc, i_c_dup} (so RIGHT gets
    // ¬bc and the duplicated C). LEFT gets {i_ac, target_pos (C)}.
    TRY_ASSIGN(outer, emit_and_split_local(
        shadow, i_or, {i_bc, i_c_dup}, neg_a, neg_b, out));

    // LEFT outer subgoal: handles A-case via ¬ac.
    {
        FormulaHandle ac_entry =
            outer.left.entries[outer.left_remap.at(i_ac)];
        if (!ac_entry.get().is_compound() ||
            ac_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR
                << "emit_or_elim_full: NNF(¬ac) is not And-compound";
        }
        FormulaHandle nnf_a   = ac_entry.get().as_compound().left;
        FormulaHandle neg_c_l = ac_entry.get().as_compound().right;
        size_t l_i_ac  = outer.left_remap.at(i_ac);
        size_t l_neg_a = outer.left_phi_idx;
        size_t l_c     = outer.left_remap.at(target_pos);

        TRY_ASSIGN(inner, emit_and_split_local(
            outer.left, l_i_ac, {l_c}, nnf_a, neg_c_l, out));
        size_t in_l_neg_a = inner.left_remap.at(l_neg_a);
        EmitCloseContext ecc{dcc.builder};
        TRY(emit_close(ecc, inner.left, inner.left_phi_idx, in_l_neg_a, out));
        size_t in_r_c = inner.right_remap.at(l_c);
        TRY(emit_close(ecc, inner.right, inner.right_theta_idx, in_r_c, out));
    }

    // RIGHT outer subgoal: handles B-case via ¬bc (symmetric).
    {
        FormulaHandle bc_entry =
            outer.right.entries[outer.right_remap.at(i_bc)];
        if (!bc_entry.get().is_compound() ||
            bc_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR
                << "emit_or_elim_full: NNF(¬bc) is not And-compound";
        }
        FormulaHandle nnf_b   = bc_entry.get().as_compound().left;
        FormulaHandle neg_c_r = bc_entry.get().as_compound().right;
        size_t r_i_bc    = outer.right_remap.at(i_bc);
        size_t r_neg_b   = outer.right_theta_idx;
        size_t r_c_dup   = outer.right_remap.at(i_c_dup);

        TRY_ASSIGN(inner, emit_and_split_local(
            outer.right, r_i_bc, {r_c_dup}, nnf_b, neg_c_r, out));
        size_t in_l_neg_b = inner.left_remap.at(r_neg_b);
        EmitCloseContext ecc{dcc.builder};
        TRY(emit_close(ecc, inner.left, inner.left_phi_idx, in_l_neg_b, out));
        size_t in_r_c_dup = inner.right_remap.at(r_c_dup);
        return emit_close(ecc, inner.right, inner.right_theta_idx, in_r_c_dup, out);
    }
}

// exists_elim translation (closer of EXISTS_ELIM block).
//
// LK construction:
//   1. Find the EXISTS_ELIM opener (an `nd::ExistsElim` step) via
//      closer_to_opener. Read its eigen from trace.term_env and its
//      `formula` field (the ∃-deriving step).
//   2. Cut(NNF(∃x.φ)): LEFT proves ∃x.φ via recursion on `formula`;
//      RIGHT carries NNF(¬∃x.φ) = ∀x.NNF(¬φ) at cut_ex_idx.
//   3. Forall{principal=cut_ex_idx, eigen=v}: replaces ∀x.¬φ with
//      NNF(¬φ)[x:=v]. Now NNF(¬φ)[x:=v] is in scope at cut_ex_idx.
//   4. Bind shadow.lkr_term_for[exists_elim_idx] = {lkr_ref=lkr_forall_idx,
//      value=Term::fixed(v)} so body-side TermRef references to the
//      witness resolve correctly. Also record
//      step_to_neg_idx[exists_elim_idx] = cut_ex_idx for any body-
//      side step-ref references.
//   5. Recurse on the body's last step (op.body) with target_pos
//      unchanged — body translates its proof of C, eventually closing
//      via dualizations against ¬φ[x:=v] (if needed) and other
//      in-scope assumptions.
util::ResultStatus emit_exists_elim_full(
    Ctx&                     dcc,
    SequentShadow            shadow,
    const nd::ExistsIntro&   op,
    uint32_t                 closer_step_idx,
    size_t                   target_pos,
    std::vector<lkr::Instr>& out)
{
    auto co = dcc.closer_to_opener.find(closer_step_idx);
    if (co == dcc.closer_to_opener.end()) {
        return MAKE_ERROR
            << "emit_exists_elim_full: closer #" << closer_step_idx
            << " has no matching EXISTS_ELIM opener";
    }
    uint32_t exists_elim_idx = co->second;
    if (exists_elim_idx >= dcc.prog.instrs.size()) {
        return MAKE_ERROR
            << "emit_exists_elim_full: opener #" << exists_elim_idx
            << " out of program range";
    }
    const auto& opener_instr = dcc.prog.instrs[exists_elim_idx];
    if (!std::holds_alternative<nd::ExistsElim>(opener_instr)) {
        return MAKE_ERROR
            << "emit_exists_elim_full: opener #" << exists_elim_idx
            << " is not an ExistsElim";
    }
    const auto& opener = std::get<nd::ExistsElim>(opener_instr);

    // Eigen from trace.term_env.
    if (exists_elim_idx >= dcc.trace.term_env.size() ||
        exists_elim_idx >= dcc.trace.term_present.size() ||
        !dcc.trace.term_present[exists_elim_idx]) {
        return MAKE_ERROR
            << "emit_exists_elim_full: ExistsElim #" << exists_elim_idx
            << " has no eigen in trace";
    }
    const Term& eigen_term = dcc.trace.term_env[exists_elim_idx];
    if (!eigen_term.is_fixed()) {
        return MAKE_ERROR
            << "emit_exists_elim_full: ExistsElim's eigen is not a "
               "fixed variable";
    }
    var_index eigen = eigen_term.as_variable();

    // ∃x.φ formula from opener.formula.
    if (opener.formula.idx >= dcc.trace.step_env.size()) {
        return MAKE_ERROR
            << "emit_exists_elim_full: ExistsElim.formula #"
            << opener.formula.idx << " out of trace range";
    }
    FormulaHandle ex_f       = dcc.trace.step_env[opener.formula.idx];
    FormulaHandle ex_nnf     = dcc.builder.to_nnf(ex_f);
    FormulaHandle neg_ex_nnf = dcc.builder.to_nnf_neg(ex_f);

    // Step 1: Cut(NNF(∃x.φ)).
    out.emplace_back(lkr::Cut{{}, ex_nnf});

    // LEFT: shadow + NNF(∃x.φ) at end. Recurse on opener.formula.
    {
        SequentShadow left = shadow;
        size_t pos = left.entries.size();
        left.entries.push_back(ex_nnf);
        TRY(translate_step_impl(
            dcc, std::move(left), opener.formula, pos,
            Demand{DemandNone{}}, out));
    }

    // RIGHT: shadow + NNF(¬∃x.φ) = ∀x.NNF(¬φ) at cut_ex_idx.
    size_t cut_ex_idx = shadow.entries.size();
    shadow.entries.push_back(neg_ex_nnf);

    // Step 2: Forall on cut_ex_idx with eigen.
    size_t lkr_forall_idx = out.size();
    out.emplace_back(lkr::Forall{{}, cut_ex_idx, eigen});

    // Update shadow.entries[cut_ex_idx] to NNF(¬φ)[x:=v].
    if (!neg_ex_nnf.get().is_quantified() ||
        neg_ex_nnf.get().as_quantified().op != Op::Forall) {
        return MAKE_ERROR
            << "emit_exists_elim_full: NNF(¬∃x.φ) is not Forall";
    }
    FormulaHandle neg_body = neg_ex_nnf.get().as_quantified().body;
    Term v = Term::fixed(eigen);
    shadow.entries[cut_ex_idx] =
        dcc.builder.instantiate_quantifier_body(neg_body, v);

    // Step 3: bind shadow's term-mapping for the eigen.
    SequentShadow::TermBinding binding;
    binding.lkr_ref = TermRef{static_cast<uint32_t>(lkr_forall_idx)};
    binding.value   = v;
    shadow.lkr_term_for[exists_elim_idx] = binding;
    shadow.step_to_neg_idx[exists_elim_idx] = cut_ex_idx;

    // Step 4: recurse on body's last step.
    return translate_step_impl(
        dcc, std::move(shadow), op.body, target_pos,
        Demand{DemandNone{}}, out);
}

}  // namespace

}  // namespace logic::proof::translate::nd_to_lkr::dispatcher
