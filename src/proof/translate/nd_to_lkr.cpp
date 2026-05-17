#include "nd_to_lkr.h"

#include "emit_close.h"
#include "env.h"
#include "nd_to_lkr_internal.h"

#include "src/proof/lkr/literal.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/schema_resolve.h"

#include "src/core/formula.h"
#include "src/core/scope_utils.h"
#include "src/parser/parser.h"
#include "src/util/error.h"

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace logic::proof::translate {

// Bring detail-namespace types into this TU's scope. close_flat lives in
// detail (defined in close_flat.cpp) and is called from translate_flat_step
// below; the shared types (Block, LowerCtx, StepNegMap, …) come from
// nd_to_lkr_internal.h.
using detail::BlockKind;
using detail::Block;
using detail::FlatStep;
using detail::BodyItem;
using detail::StepFormulaMap;
using detail::FlatEvent;
using detail::SubBlockEvent;
using detail::EmissionEvent;
using detail::DepsPlan;
using detail::LowerCtx;
using detail::StepNegMap;
using detail::ScopeDeps;
using detail::discharge;
using detail::close_flat;

namespace {

util::Result<std::unique_ptr<Block>> decompose_blocks(
    const Program<nd::Instr>& in,
    GlobalContext& ctx,
    FormulaBuilder& builder,
    std::unordered_map<std::string, Term>& name_table,
    std::unordered_map<uint32_t, Term>& term_for_idx,
    std::unordered_map<var_index, int>&  var_to_depth)
{
    if (in.instrs.empty()) {
        return MAKE_ERROR << "NDtoLKR: empty program";
    }

    auto outer = std::make_unique<Block>();
    outer->kind  = BlockKind::OUTER;
    outer->depth = 0;

    std::vector<Block*> stack{outer.get()};
    std::unordered_map<std::string, size_t> empty_sv, empty_ar;

    auto push_block = [&](std::unique_ptr<Block> b) -> util::Result<Block*> {
        int new_depth = static_cast<int>(stack.size());   // = parent.depth + 1
        if (ScopeDeps::overflows(new_depth)) {
            return MAKE_ERROR
                << "decompose: scope nesting depth " << new_depth
                << " exceeds ScopeDeps capacity ("
                << ScopeDeps::kMaxDepth << ")";
        }
        Block* raw = b.get();
        raw->depth = new_depth;
        stack.back()->body.push_back(BodyItem{std::move(b)});
        stack.push_back(raw);
        return raw;
    };

    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        const auto& instr = in.instrs[i];

        if (auto* fix = std::get_if<nd::Fix>(&instr)) {
            auto blk = std::make_unique<Block>();
            blk->kind = BlockKind::FORALL;
            blk->opener_idx = i;
            var_index v = builder.enter_scope();
            blk->eigen_term = Term::fixed(v);
            term_for_idx[i] = blk->eigen_term;
            if (!fix->var_name.name.empty()) {
                name_table[fix->var_name.name] = blk->eigen_term;
            }
            TRY_ASSIGN(raw, push_block(std::move(blk)));
            var_to_depth[v] = raw->depth;
            continue;
        }
        if (auto* assume = std::get_if<nd::Assume>(&instr)) {
            if (!assume->formula) {
                return MAKE_ERROR << "decompose: assume #" << i << " missing formula AST";
            }
            auto blk = std::make_unique<Block>();
            blk->kind = BlockKind::IMPLIES;
            blk->opener_idx = i;
            TRY_ASSIGN(assumption_raw, try_parse_formula_with_vars(
                assume->formula.get(), ctx, builder,
                name_table, empty_sv, empty_ar));
            blk->assumption_raw = assumption_raw;
            TRY(push_block(std::move(blk)));
            continue;
        }
        if (auto* ee = std::get_if<nd::ExistsElim>(&instr)) {
            auto blk = std::make_unique<Block>();
            blk->kind = BlockKind::EXISTS_ELIM;
            blk->opener_idx = i;
            blk->exists_formula_step = ee->formula;
            var_index v = builder.enter_scope();
            blk->eigen_term = Term::fixed(v);
            term_for_idx[i] = blk->eigen_term;
            if (ee->bind_witness.has_value() && !ee->bind_witness->name.empty()) {
                name_table[ee->bind_witness->name] = blk->eigen_term;
            }
            TRY_ASSIGN(raw, push_block(std::move(blk)));
            var_to_depth[v] = raw->depth;
            continue;
        }

        if (auto* fi = std::get_if<nd::ForallIntro>(&instr)) {
            if (stack.back() == outer.get() || stack.back()->kind != BlockKind::FORALL) {
                return MAKE_ERROR << "decompose: forall_intro at #" << i
                                  << " has no matching FORALL scope";
            }
            stack.back()->closer_idx = i;
            stack.back()->close_target_idx = fi->body.idx;
            stack.pop_back();
            continue;
        }
        if (auto* ii = std::get_if<nd::ImpliesIntro>(&instr)) {
            if (stack.back() == outer.get() || stack.back()->kind != BlockKind::IMPLIES) {
                return MAKE_ERROR << "decompose: implies_intro at #" << i
                                  << " has no matching IMPLIES scope";
            }
            stack.back()->closer_idx = i;
            stack.back()->close_target_idx = ii->conclusion.idx;
            stack.pop_back();
            continue;
        }
        if (auto* ni = std::get_if<nd::NotIntro>(&instr)) {
            if (stack.back() == outer.get() || stack.back()->kind != BlockKind::IMPLIES) {
                return MAKE_ERROR << "decompose: not_intro at #" << i
                                  << " has no matching IMPLIES scope";
            }
            stack.back()->kind = BlockKind::NOT;
            stack.back()->closer_idx = i;
            stack.back()->close_target_idx = ni->bottom.idx;
            stack.pop_back();
            continue;
        }
        if (auto* ei = std::get_if<nd::ExistsIntro>(&instr)) {
            if (!ei->witness.has_value()) {
                if (stack.back() == outer.get() || stack.back()->kind != BlockKind::EXISTS_ELIM) {
                    return MAKE_ERROR << "decompose: exists_intro (scope-closing) at #" << i
                                      << " has no matching EXISTS_ELIM scope";
                }
                stack.back()->closer_idx = i;
                stack.back()->close_target_idx = ei->body.idx;
                stack.pop_back();
                continue;
            }
        }
        if (auto* qed = std::get_if<nd::Qed>(&instr)) {
            if (stack.back() != outer.get()) {
                return MAKE_ERROR << "decompose: qed at #" << i
                                  << " not at outermost depth (" << (stack.size() - 1)
                                  << " unclosed scopes)";
            }
            outer->closer_idx = i;
            outer->close_target_idx = qed->derived.idx;
            continue;
        }

        stack.back()->body.push_back(BodyItem{FlatStep{i}});
    }

    if (stack.size() != 1) {
        return MAKE_ERROR << "decompose: " << (stack.size() - 1)
                          << " unclosed scope(s) at end of program";
    }

    return std::unique_ptr<Block>(std::move(outer));
}

// =========================================================================
// Pass 2 — compute_block_formulas
// =========================================================================
// (StepFormulaMap is declared in nd_to_lkr_internal.h.)

util::Result<FormulaHandle> compute_flat_formula(
    const Program<nd::Instr>& in,
    uint32_t idx,
    FormulaBuilder& builder,
    GlobalContext& ctx,
    const StepFormulaMap& step_formula,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    std::unordered_map<std::string, Term>& name_table);

util::ResultStatus compute_block_formulas(
    const Program<nd::Instr>& in,
    const Block& blk,
    FormulaBuilder& builder,
    GlobalContext& ctx,
    StepFormulaMap& step_formula,
    StepFormulaMap& step_formula_nnf,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    std::unordered_map<std::string, Term>& name_table)
{
    auto record = [&](uint32_t idx, FormulaHandle f) {
        step_formula[idx] = f;
        step_formula_nnf[idx] = builder.to_nnf(f);
    };

    if ((blk.kind == BlockKind::IMPLIES || blk.kind == BlockKind::NOT) &&
        blk.assumption_raw.valid()) {
        record(blk.opener_idx, blk.assumption_raw);
    }

    if (blk.kind == BlockKind::EXISTS_ELIM) {
        auto it = step_formula.find(blk.exists_formula_step.idx);
        if (it == step_formula.end()) {
            return MAKE_ERROR << "compute_block_formulas: exists_elim at #"
                              << blk.opener_idx << " references unknown step %"
                              << blk.exists_formula_step.idx;
        }
        const Formula& f = it->second.get();
        if (!f.is_quantified() || f.as_quantified().op != Op::Exists) {
            return MAKE_ERROR << "compute_block_formulas: exists_elim at #"
                              << blk.opener_idx << " step is not ∃x.φ";
        }
        FormulaHandle inst = builder.instantiate_quantifier_body(
            f.as_quantified().body, blk.eigen_term);
        record(blk.opener_idx, inst);
    }

    for (const auto& item : blk.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            TRY_ASSIGN(f, compute_flat_formula(
                in, flat->nd_idx, builder, ctx, step_formula,
                term_for_idx, name_table));
            record(flat->nd_idx, f);
        } else {
            const Block& sub = *std::get<std::unique_ptr<Block>>(item);
            TRY(compute_block_formulas(
                in, sub, builder, ctx, step_formula, step_formula_nnf,
                term_for_idx, name_table));
            FormulaHandle target_f;
            if (auto it = step_formula.find(sub.close_target_idx);
                it != step_formula.end()) {
                target_f = it->second;
            } else {
                return MAKE_ERROR << "compute_block_formulas: sub-block at #"
                                  << sub.opener_idx
                                  << " close_target step %" << sub.close_target_idx
                                  << " has no formula";
            }
            FormulaHandle result;
            switch (sub.kind) {
                case BlockKind::FORALL: {
                    FormulaHandle abstracted = builder.abstract_var(
                        target_f, sub.eigen_term.as_variable());
                    result = builder.make_quantified(Op::Forall, abstracted);
                    break;
                }
                case BlockKind::IMPLIES: {
                    result = builder.make_implies(sub.assumption_raw, target_f);
                    break;
                }
                case BlockKind::NOT: {
                    result = builder.make_not(sub.assumption_raw);
                    break;
                }
                case BlockKind::EXISTS_ELIM: {
                    // Mirror ND scope-closing exists_intro semantics: if
                    // target_f mentions the witness eigenvariable, abstract
                    // it back into ∃x.target_f[v↦x]; otherwise keep target_f
                    // unchanged (witness escaped trivially).
                    var_index v = sub.eigen_term.as_variable();
                    if (formula_contains_fixed_var(target_f, v)) {
                        FormulaHandle abstracted =
                            builder.abstract_var(target_f, v);
                        result = builder.make_quantified(Op::Exists, abstracted);
                    } else {
                        result = target_f;
                    }
                    break;
                }
                case BlockKind::OUTER:
                    return MAKE_ERROR << "compute_block_formulas: nested OUTER block (impossible)";
            }
            record(sub.closer_idx, result);
        }
    }
    return util::Ok();
}

util::Result<FormulaHandle> compute_flat_formula(
    const Program<nd::Instr>& in,
    uint32_t idx,
    FormulaBuilder& builder,
    GlobalContext& ctx,
    const StepFormulaMap& step_formula,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    std::unordered_map<std::string, Term>& name_table)
{
    const auto& instr = in.instrs[idx];

    auto require_step = [&](StepRef r, const char* op) -> util::Result<FormulaHandle> {
        auto it = step_formula.find(r.idx);
        if (it == step_formula.end()) {
            return MAKE_ERROR << op << ": step %" << r.idx << " formula unknown";
        }
        return it->second;
    };
    auto require_term = [&](TermRef r, const char* op) -> util::Result<Term> {
        auto it = term_for_idx.find(r.idx);
        if (it == term_for_idx.end()) {
            return MAKE_ERROR << op << ": term %" << r.idx << " not bound";
        }
        return it->second;
    };

    return std::visit(overloaded{
        [&](const nd::Use& op) -> util::Result<FormulaHandle> {
            auto found = ctx.find_known(op.axiom.name);
            if (!found.has_value()) {
                return MAKE_ERROR << "use: unknown axiom/theorem '"
                                  << op.axiom.name << "'";
            }
            return found.value().get().root();
        },
        [&](const nd::Let& op) -> util::Result<FormulaHandle> {
            if (!op.formula) return MAKE_ERROR << "let: missing formula AST";
            std::unordered_map<std::string, size_t> empty_sv, empty_ar;
            return try_parse_formula_with_vars(op.formula.get(), ctx, builder,
                                                name_table, empty_sv, empty_ar);
        },
        [&](const nd::SchemaInst& op) -> util::Result<FormulaHandle> {
            std::unordered_map<std::string, Term> empty_vars;
            return resolve_and_instantiate_schema(
                ctx, builder, op.data, empty_vars, "schema_inst");
        },
        [&](const nd::ForallElim& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(f, require_step(op.formula, "forall_elim"));
            const Formula& g = f.get();
            if (!g.is_quantified() || g.as_quantified().op != Op::Forall) {
                return MAKE_ERROR << "forall_elim: step %" << op.formula.idx
                                  << " is not ∀x.φ";
            }
            TRY_ASSIGN(t, require_term(op.term, "forall_elim"));
            return builder.instantiate_quantifier_body(g.as_quantified().body, t);
        },
        [&](const nd::ImpliesElim& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(impl, require_step(op.impl, "implies_elim"));
            TRY_ASSIGN(ant,  require_step(op.ant,  "implies_elim"));
            const Formula& f = impl.get();
            if (!f.is_compound() || f.as_compound().op != Op::Implies) {
                return MAKE_ERROR << "implies_elim: step %" << op.impl.idx
                                  << " is not A → B";
            }
            if (f.as_compound().left != ant) {
                return MAKE_ERROR << "implies_elim: antecedent doesn't match A";
            }
            return f.as_compound().right;
        },
        [&](const nd::AndIntro& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(a, require_step(op.a, "and_intro"));
            TRY_ASSIGN(b, require_step(op.b, "and_intro"));
            return builder.make_and(a, b);
        },
        [&](const nd::AndElimL& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(of, require_step(op.of, "and_elim_l"));
            const Formula& f = of.get();
            if (!f.is_compound() || f.as_compound().op != Op::And)
                return MAKE_ERROR << "and_elim_l: not A ∧ B";
            return f.as_compound().left;
        },
        [&](const nd::AndElimR& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(of, require_step(op.of, "and_elim_r"));
            const Formula& f = of.get();
            if (!f.is_compound() || f.as_compound().op != Op::And)
                return MAKE_ERROR << "and_elim_r: not A ∧ B";
            return f.as_compound().right;
        },
        [&](const nd::OrElim& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(or_f, require_step(op.or_formula, "or_elim"));
            TRY_ASSIGN(ac,   require_step(op.ac,         "or_elim"));
            TRY_ASSIGN(bc,   require_step(op.bc,         "or_elim"));
            const Formula& fo = or_f.get();
            const Formula& fac = ac.get();
            const Formula& fbc = bc.get();
            if (!fo.is_compound() || fo.as_compound().op != Op::Or)
                return MAKE_ERROR << "or_elim: or_formula not A ∨ B";
            if (!fac.is_compound() || fac.as_compound().op != Op::Implies)
                return MAKE_ERROR << "or_elim: ac not A → C";
            if (!fbc.is_compound() || fbc.as_compound().op != Op::Implies)
                return MAKE_ERROR << "or_elim: bc not B → C";
            if (fo.as_compound().left  != fac.as_compound().left)
                return MAKE_ERROR << "or_elim: ac's antecedent doesn't match A";
            if (fo.as_compound().right != fbc.as_compound().left)
                return MAKE_ERROR << "or_elim: bc's antecedent doesn't match B";
            if (fac.as_compound().right != fbc.as_compound().right)
                return MAKE_ERROR << "or_elim: ac and bc have different conclusions";
            return fac.as_compound().right;
        },
        [&](const nd::IffIntro& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(ab, require_step(op.ab, "iff_intro"));
            TRY_ASSIGN(ba, require_step(op.ba, "iff_intro"));
            const Formula& fab = ab.get();
            const Formula& fba = ba.get();
            if (!fab.is_compound() || fab.as_compound().op != Op::Implies)
                return MAKE_ERROR << "iff_intro: ab is not A → B";
            if (!fba.is_compound() || fba.as_compound().op != Op::Implies)
                return MAKE_ERROR << "iff_intro: ba is not B → A";
            if (fab.as_compound().left != fba.as_compound().right ||
                fab.as_compound().right != fba.as_compound().left)
                return MAKE_ERROR << "iff_intro: ab and ba do not pair as A→B / B→A";
            return builder.make_iff(fab.as_compound().left, fab.as_compound().right);
        },
        [&](const nd::IffElimL& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(iff, require_step(op.iff, "iff_elim_l"));
            TRY_ASSIGN(a,   require_step(op.a,   "iff_elim_l"));
            const Formula& f = iff.get();
            if (!f.is_compound() || f.as_compound().op != Op::Iff)
                return MAKE_ERROR << "iff_elim_l: not A ↔ B";
            if (f.as_compound().left != a)
                return MAKE_ERROR << "iff_elim_l: a doesn't match lhs";
            return f.as_compound().right;
        },
        [&](const nd::IffElimR& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(iff, require_step(op.iff, "iff_elim_r"));
            TRY_ASSIGN(b,   require_step(op.b,   "iff_elim_r"));
            const Formula& f = iff.get();
            if (!f.is_compound() || f.as_compound().op != Op::Iff)
                return MAKE_ERROR << "iff_elim_r: not A ↔ B";
            if (f.as_compound().right != b)
                return MAKE_ERROR << "iff_elim_r: b doesn't match rhs";
            return f.as_compound().left;
        },
        [&](const nd::OrIntroL& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(a, require_step(op.a,         "or_intro_l"));
            TRY_ASSIGN(b, require_step(op.b_formula, "or_intro_l"));
            return builder.make_or(a, b);
        },
        [&](const nd::OrIntroR& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(a, require_step(op.a_formula, "or_intro_r"));
            TRY_ASSIGN(b, require_step(op.b,         "or_intro_r"));
            return builder.make_or(a, b);
        },
        [&](const nd::ExistsIntro& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(body, require_step(op.body, "exists_intro"));
            if (!op.witness.has_value()) {
                return MAKE_ERROR << "exists_intro (scope-closing) reached in flat dispatch";
            }
            TRY_ASSIGN(t, require_term(*op.witness, "exists_intro"));
            if (!t.is_fixed())
                return MAKE_ERROR << "exists_intro: witness must be a fixed-var term";
            FormulaHandle abstracted = builder.abstract_var(body, t.as_variable());
            return builder.make_quantified(Op::Exists, abstracted);
        },
        [&](const nd::ExcludedMiddle& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(a, require_step(op.formula_let, "excluded_middle"));
            return builder.make_or(a, builder.make_not(a));
        },
        [&](const nd::NotElim& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(neg, require_step(op.negation, "not_elim"));
            TRY_ASSIGN(pos, require_step(op.formula,  "not_elim"));
            const Formula& nf = neg.get();
            if (!nf.is_compound() || nf.as_compound().op != Op::Not)
                return MAKE_ERROR << "not_elim: negation step is not ¬φ";
            if (nf.as_compound().left != pos)
                return MAKE_ERROR << "not_elim: ¬φ and φ don't match";
            return builder.make_bottom();
        },
        [&](const nd::BottomElim& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(target, require_step(op.target_formula, "bottom_elim"));
            return target;
        },
        [&](const nd::EqSubst& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(eq, require_step(op.eq_formula, "eq_subst"));
            TRY_ASSIGN(target, require_step(op.target, "eq_subst"));
            const Formula& f = eq.get();
            if (!f.is_predicate()
                || f.as_predicate().predicate().get().get_name() != "eq"
                || f.as_predicate().args().size() != 2) {
                return MAKE_ERROR << "eq_subst: expected eq(a, b), got: "
                                  << f.to_string();
            }
            Term a = f.as_predicate().args()[0];
            Term b = f.as_predicate().args()[1];
            return builder.translate_term(target, a, b);
        },
        [&](const nd::EqSym& op) -> util::Result<FormulaHandle> {
            TRY_ASSIGN(eq, require_step(op.eq_formula, "eq_sym"));
            const Formula& f = eq.get();
            if (!f.is_predicate()
                || f.as_predicate().predicate().get().get_name() != "eq"
                || f.as_predicate().args().size() != 2) {
                return MAKE_ERROR << "eq_sym: expected eq(a, b), got: "
                                  << f.to_string();
            }
            Term a = f.as_predicate().args()[0];
            Term b = f.as_predicate().args()[1];
            return builder.predicate(f.as_predicate().predicate(), {b, a});
        },
        [&](const auto& op) -> util::Result<FormulaHandle> {
            (void)op;
            return MAKE_ERROR
                << "compute_flat_formula: ND op variant index "
                << instr.index() << " not yet supported";
        },
    }, instr);
}

// =========================================================================
// DepsPlan — scope-aware cut hoisting (mirrors ND ScopeDeps semantics).
//
// For every step k that produces a formula, compute step_deps[k] — the
// bitset of block-depths whose scope k transitively depends on. The
// recurrence matches src/proof/nd/stack.cpp's derive_with_deps exactly:
//   total = proof_deps_from_operands | compute_var_deps(step_formula[k])
// with discharge applied at sub-block closers.
//
// host_block[k] = the deepest live block whose depth equals
// step_deps[k].deepest() (OUTER if deps are empty).
//
// `events` schedules per-block emission: each block B has a sequence of
// EmissionEvents in the order they should be emitted. Each event is
// either a B-hosted flat step's cut, or one of B's top-level sub-blocks.
// The scheduler enforces that any B-hosted flat whose program position
// lies INSIDE a top-level sub-block S of B is emitted BEFORE S's
// SubBlock event — keeping the cut on B's RIGHT continuation (inherited
// by S via apply_cut) rather than localized to S's LEFT subgoal.
// =========================================================================

// (FlatEvent, SubBlockEvent, EmissionEvent, DepsPlan are in
// nd_to_lkr_internal.h.)

// Walk a formula collecting fix-var deps. Mirrors ND's compute_var_deps.
ScopeDeps compute_var_deps_fml(
    FormulaHandle h,
    const std::unordered_map<var_index, int>& var_to_depth);

ScopeDeps compute_var_deps_term(
    Term t,
    const std::unordered_map<var_index, int>& var_to_depth)
{
    if (t.is_fixed()) {
        auto it = var_to_depth.find(t.as_variable());
        if (it != var_to_depth.end()) return ScopeDeps::from_bit(it->second);
        return {};
    }
    if (t.is_description()) {
        return compute_var_deps_fml(t.as_description().body, var_to_depth);
    }
    return {};
}

ScopeDeps compute_var_deps_fml(
    FormulaHandle h,
    const std::unordered_map<var_index, int>& var_to_depth)
{
    if (!h.valid()) return {};
    const Formula& f = h.get();
    if (f.is_predicate()) {
        ScopeDeps d;
        for (const Term& t : f.as_predicate().args()) {
            d |= compute_var_deps_term(t, var_to_depth);
        }
        return d;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        ScopeDeps d;
        if (c.left.valid())  d |= compute_var_deps_fml(c.left,  var_to_depth);
        if (c.right.valid()) d |= compute_var_deps_fml(c.right, var_to_depth);
        return d;
    }
    if (f.is_quantified()) {
        return compute_var_deps_fml(f.as_quantified().body, var_to_depth);
    }
    if (f.is_schema_var()) {
        return {};
    }
    if (f.is_sentence()) {
        return {};
    }
    return {};
}

// Per-flat-step proof_deps (operand union + witness-term scope). The
// compute_var_deps(step_formula[k]) component is added uniformly by
// record_step (mirroring ND's derive_with_deps), so this function does
// NOT include it. Block-opener/closer/Fix ops are handled separately in
// the block recursion and should never be passed here.
util::Result<ScopeDeps> compute_flat_step_proof_deps(
    const Program<nd::Instr>& in,
    uint32_t k,
    const std::unordered_map<uint32_t, ScopeDeps>& step_deps_so_far,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    const std::unordered_map<var_index, int>& var_to_depth)
{
    auto deps_of = [&](StepRef r) -> ScopeDeps {
        auto it = step_deps_so_far.find(r.idx);
        return it != step_deps_so_far.end() ? it->second : ScopeDeps{};
    };
    auto deps_of_termref = [&](TermRef r) -> ScopeDeps {
        auto it = term_for_idx.find(r.idx);
        if (it == term_for_idx.end()) return {};
        return compute_var_deps_term(it->second, var_to_depth);
    };

    const auto& instr = in.instrs[k];
    return std::visit(overloaded{
        [&](const nd::Use&)        -> util::Result<ScopeDeps> { return ScopeDeps{}; },
        [&](const nd::SchemaInst&) -> util::Result<ScopeDeps> { return ScopeDeps{}; },
        [&](const nd::Let&)        -> util::Result<ScopeDeps> { return ScopeDeps{}; },
        [&](const nd::ForallElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.formula) | deps_of_termref(op.term);
        },
        [&](const nd::ImpliesElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.impl) | deps_of(op.ant);
        },
        [&](const nd::AndIntro& op) -> util::Result<ScopeDeps> {
            return deps_of(op.a) | deps_of(op.b);
        },
        [&](const nd::AndElimL& op) -> util::Result<ScopeDeps> { return deps_of(op.of); },
        [&](const nd::AndElimR& op) -> util::Result<ScopeDeps> { return deps_of(op.of); },
        [&](const nd::OrIntroL& op) -> util::Result<ScopeDeps> {
            return deps_of(op.a) | deps_of(op.b_formula);
        },
        [&](const nd::OrIntroR& op) -> util::Result<ScopeDeps> {
            return deps_of(op.a_formula) | deps_of(op.b);
        },
        [&](const nd::OrElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.or_formula) | deps_of(op.ac) | deps_of(op.bc);
        },
        [&](const nd::IffIntro& op) -> util::Result<ScopeDeps> {
            return deps_of(op.ab) | deps_of(op.ba);
        },
        [&](const nd::IffElimL& op) -> util::Result<ScopeDeps> {
            return deps_of(op.iff) | deps_of(op.a);
        },
        [&](const nd::IffElimR& op) -> util::Result<ScopeDeps> {
            return deps_of(op.iff) | deps_of(op.b);
        },
        [&](const nd::ExistsIntro& op) -> util::Result<ScopeDeps> {
            ScopeDeps d = deps_of(op.body);
            if (op.witness.has_value()) d |= deps_of_termref(*op.witness);
            return d;
        },
        [&](const nd::NotElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.negation) | deps_of(op.formula);
        },
        [&](const nd::BottomElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.bottom) | deps_of(op.target_formula);
        },
        [&](const nd::EqSubst& op) -> util::Result<ScopeDeps> {
            return deps_of(op.eq_formula) | deps_of(op.target);
        },
        [&](const nd::EqSym& op) -> util::Result<ScopeDeps> { return deps_of(op.eq_formula); },
        [&](const nd::DoubleNegElim& op) -> util::Result<ScopeDeps> { return deps_of(op.of); },
        [&](const nd::ExcludedMiddle& op) -> util::Result<ScopeDeps> {
            return deps_of(op.formula_let);
        },
        [&](const nd::IotaElim& op) -> util::Result<ScopeDeps> {
            return deps_of(op.exists_formula);
        },
        [&](const nd::ClassicalAbsurd& op) -> util::Result<ScopeDeps> { return deps_of(op.bottom); },
        [&](const nd::Peirce& op) -> util::Result<ScopeDeps> {
            return deps_of(op.a_let) | deps_of(op.b_let);
        },
        // Block-structural ops should never be passed to this function.
        [&](const nd::Fix&)          -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: Fix is a block opener (#" << k << ")";
        },
        [&](const nd::Assume&)       -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: Assume is a block opener (#" << k << ")";
        },
        [&](const nd::ExistsElim&)   -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: ExistsElim is a block opener (#" << k << ")";
        },
        [&](const nd::ForallIntro&)  -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: ForallIntro is a block closer (#" << k << ")";
        },
        [&](const nd::ImpliesIntro&) -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: ImpliesIntro is a block closer (#" << k << ")";
        },
        [&](const nd::NotIntro&)     -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: NotIntro is a block closer (#" << k << ")";
        },
        [&](const nd::Qed&)          -> util::Result<ScopeDeps> {
            return MAKE_ERROR << "compute_flat_step_proof_deps: Qed is a block closer (#" << k << ")";
        },
    }, instr);
}

// Recursive deps-plan computation. live_blocks[d] is the block at depth
// d currently in scope; live_blocks.back() is the innermost. Block opener
// is responsible for pushing itself onto live_blocks before recursing,
// and popping after.
util::ResultStatus compute_deps_block(
    const Program<nd::Instr>& in,
    const Block& blk,
    const StepFormulaMap& step_formula,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    const std::unordered_map<var_index, int>& var_to_depth,
    std::vector<const Block*>& live_blocks,
    DepsPlan& plan)
{
    // Mirror ND's derive_with_deps: total = proof_deps | compute_var_deps(f).
    // The compute_var_deps(f) component picks up free fix-vars present in
    // the result formula — crucial for sub-block closers, whose result
    // formula may mention vars from outer FORALL/EXISTS_ELIM scopes that
    // the discharge of the sub-block's own bit doesn't cover.
    auto record_step = [&](uint32_t k, ScopeDeps proof_deps) {
        ScopeDeps total = proof_deps;
        auto sf_it = step_formula.find(k);
        if (sf_it != step_formula.end()) {
            total |= compute_var_deps_fml(sf_it->second, var_to_depth);
        }
        plan.step_deps[k] = total;
        int dd = total.deepest();
        const Block* host = (dd < 0) ? live_blocks[0] : live_blocks[dd];
        plan.host_block[k] = host;
    };

    // Record opener-step deps for IMPLIES/NOT/EXISTS_ELIM. (FORALL openers
    // are Fix ops, which don't bind a step formula in step_formula and so
    // don't need step_deps.)
    if (blk.kind == BlockKind::IMPLIES || blk.kind == BlockKind::NOT) {
        // Assume's step is the assumption formula itself; it depends on
        // its own scope's bit.
        record_step(blk.opener_idx, ScopeDeps::from_bit(blk.depth));
    } else if (blk.kind == BlockKind::EXISTS_ELIM) {
        ScopeDeps src;
        auto it = plan.step_deps.find(blk.exists_formula_step.idx);
        if (it != plan.step_deps.end()) src = it->second;
        record_step(blk.opener_idx, src | ScopeDeps::from_bit(blk.depth));
    }

    for (const auto& item : blk.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            uint32_t k = flat->nd_idx;
            TRY_ASSIGN(d, compute_flat_step_proof_deps(
                in, k, plan.step_deps, term_for_idx, var_to_depth));
            record_step(k, d);
        } else {
            const Block& sub = *std::get<std::unique_ptr<Block>>(item);
            live_blocks.push_back(&sub);
            TRY(compute_deps_block(in, sub, step_formula, term_for_idx,
                                    var_to_depth, live_blocks, plan));
            live_blocks.pop_back();

            // Sub-block closer: proof_deps = discharge(target.deps, sub.depth).
            // record_step ORs in compute_var_deps(closer_formula) uniformly,
            // which restores any outer-scope fix-vars the discharge cleared
            // (essential for IMPLIES closers whose result mentions vars from
            // surrounding FORALL/EXISTS_ELIM scopes).
            ScopeDeps target_deps;
            auto t_it = plan.step_deps.find(sub.close_target_idx);
            if (t_it != plan.step_deps.end()) target_deps = t_it->second;
            record_step(sub.closer_idx,
                        discharge(target_deps, sub.depth));
        }
    }
    return util::Ok();
}

util::ResultStatus compute_deps_plan(
    const Program<nd::Instr>& in,
    const Block& root,
    const StepFormulaMap& step_formula,
    const std::unordered_map<uint32_t, Term>& term_for_idx,
    const std::unordered_map<var_index, int>& var_to_depth,
    DepsPlan& plan)
{
    std::vector<const Block*> live_blocks{&root};
    return compute_deps_block(in, root, step_formula, term_for_idx,
                                var_to_depth, live_blocks, plan);
}

// Walk `search` recursively gathering every flat-step k hosted at
// `host_target` and not Let/NotElim (which emit no LKR ops). Pushed in
// program order via the body iteration order.
void gather_hosted_inside(const Program<nd::Instr>& in,
                          const Block& search,
                          const Block* host_target,
                          const DepsPlan& plan,
                          std::vector<uint32_t>& out)
{
    for (const auto& item : search.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            uint32_t k = flat->nd_idx;
            const auto& instr = in.instrs[k];
            if (std::holds_alternative<nd::Let>(instr) ||
                std::holds_alternative<nd::NotElim>(instr)) {
                continue;
            }
            auto it = plan.host_block.find(k);
            if (it != plan.host_block.end() && it->second == host_target) {
                out.push_back(k);
            }
        } else {
            const Block& sub = *std::get<std::unique_ptr<Block>>(item);
            gather_hosted_inside(in, sub, host_target, plan, out);
        }
    }
}

// Build the emission event list for block B (and recursively for its
// sub-blocks). See DepsPlan / EmissionEvent comments for the ordering
// invariant: any B-hosted flat defined inside a top-level sub-block S of
// B precedes S's SubBlockEvent so the flat lands on B's RIGHT continuation.
void build_events(const Program<nd::Instr>& in,
                   const Block& B,
                   DepsPlan& plan)
{
    std::vector<EmissionEvent> events;
    for (const auto& item : B.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            uint32_t k = flat->nd_idx;
            const auto& instr = in.instrs[k];
            if (std::holds_alternative<nd::Let>(instr) ||
                std::holds_alternative<nd::NotElim>(instr)) {
                continue;   // no LKR op; nothing to schedule
            }
            auto it = plan.host_block.find(k);
            if (it != plan.host_block.end() && it->second == &B) {
                events.emplace_back(FlatEvent{k});
            }
            // host elsewhere: skip; handled by the host's event list.
        } else {
            const Block& sub = *std::get<std::unique_ptr<Block>>(item);
            std::vector<uint32_t> pre;
            gather_hosted_inside(in, sub, &B, plan, pre);
            for (uint32_t k : pre) {
                events.emplace_back(FlatEvent{k});
            }
            events.emplace_back(SubBlockEvent{&sub});
            build_events(in, sub, plan);   // recurse
        }
    }
    plan.events[&B] = std::move(events);
}

// =========================================================================
// Phase B — emission. See SPEC.md.
//
// All sequent positions are addressed by SequentEntry (an opaque handle);
// Env owns the entry→position map and is the only place position
// arithmetic lives. Multiplicative-And partitions are computed from
// per-rule declared `left_needs` / `right_needs` (see Env::apply_and).
// Generic structural closure (emit_close) handles all Or/And/∀/∃ duals
// — including iff-derived NNFs — without per-iff special-case code.
// =========================================================================

// (LowerCtx and StepNegMap are declared in nd_to_lkr_internal.h.
// close_flat is defined in close_flat.cpp.)

util::ResultStatus translate_block(LowerCtx& lc, Env& env,
                                    SequentEntry result_entry,
                                    const Block& block,
                                    const Program<nd::Instr>& in,
                                    StepNegMap& step_to_neg);

// emit_block_opener: mutate env so the body sees the right scope.
// Returns the qed_entry — the SequentEntry the closer will pair against
// the close_target's negation via emit_close. Also updates step_to_neg
// for opener-introduced bindings (IMPLIES/NOT assumption-neg, EXISTS_ELIM
// witness-neg).
util::Result<SequentEntry> emit_block_opener(LowerCtx& lc, Env& env,
                                              SequentEntry result_entry,
                                              const Block& block,
                                              StepNegMap& step_to_neg)
{
    switch (block.kind) {
        case BlockKind::OUTER:
            return result_entry;

        case BlockKind::FORALL: {
            TRY_ASSIGN(result_pos, env.position_of(result_entry));
            TRY_ASSIGN(f, env.formula_at(result_entry));
            const Formula& fg = f.get();
            if (!fg.is_quantified() || fg.as_quantified().op != Op::Forall) {
                return MAKE_ERROR
                    << "emit_block_opener(FORALL): result is not ∀x.φ";
            }
            var_index v = block.eigen_term.as_variable();
            uint32_t lkr_idx = static_cast<uint32_t>(lc.out.instrs.size());
            lkr::Forall fop{}; fop.principal = result_pos; fop.eigen = v;
            lc.out.instrs.emplace_back(std::move(fop));
            TRY(env.apply_forall(result_entry, v, lc.builder));
            lc.nd_to_lkr_termref[block.opener_idx] = lkr_idx;
            return result_entry;
        }

        case BlockKind::IMPLIES: {
            TRY_ASSIGN(result_pos, env.position_of(result_entry));
            TRY_ASSIGN(f, env.formula_at(result_entry));
            const Formula& fg = f.get();
            if (!fg.is_compound() || fg.as_compound().op != Op::Or) {
                return MAKE_ERROR
                    << "emit_block_opener(IMPLIES): result is not (NNF(¬A) ∨ body)";
            }
            lkr::Or orop{}; orop.principal = result_pos;
            lc.out.instrs.emplace_back(std::move(orop));
            TRY_ASSIGN(body_entry, env.apply_or(result_entry));
            // result_entry now points at NNF(¬A) — the assumption's negation
            // visible to the body via step_to_neg[opener].
            step_to_neg[block.opener_idx] = result_entry;
            return body_entry;
        }

        case BlockKind::NOT: {
            // result_entry already holds NNF(¬A). The closer is custom
            // (uses the not_elim's two operands). No LKR op emitted at open.
            step_to_neg[block.opener_idx] = result_entry;
            return result_entry;
        }

        case BlockKind::EXISTS_ELIM: {
            // The block depends on the cut-in negation of its source ∃ step,
            // which lives at step_to_neg[block.exists_formula_step.idx] and
            // currently holds NNF(¬∃x.φ) = ∀x.NNF(¬φ).
            auto it = step_to_neg.find(block.exists_formula_step.idx);
            if (it == step_to_neg.end()) {
                return MAKE_ERROR
                    << "emit_block_opener(EXISTS_ELIM): exists step %"
                    << block.exists_formula_step.idx << " not cut-in";
            }
            SequentEntry neg_exists = it->second;
            TRY_ASSIGN(neg_pos, env.position_of(neg_exists));
            TRY_ASSIGN(f, env.formula_at(neg_exists));
            const Formula& fg = f.get();
            if (!fg.is_quantified() || fg.as_quantified().op != Op::Forall) {
                return MAKE_ERROR
                    << "emit_block_opener(EXISTS_ELIM): cut-in is not ∀x.¬φ";
            }
            var_index v = block.eigen_term.as_variable();
            uint32_t lkr_idx = static_cast<uint32_t>(lc.out.instrs.size());
            lkr::Forall fop{}; fop.principal = neg_pos; fop.eigen = v;
            lc.out.instrs.emplace_back(std::move(fop));
            TRY(env.apply_forall(neg_exists, v, lc.builder));
            lc.nd_to_lkr_termref[block.opener_idx] = lkr_idx;
            step_to_neg[block.opener_idx] = neg_exists;

            // If compute_block_formulas wrapped the close_target in ∃x. …
            // (because the target mentioned the witness eigen), the
            // sub-block cut formula is one quantifier deeper than the
            // close_target's negation. Reduce it back to body[w] by
            // applying Exists with witness=w, so emit_block_closer's
            // emit_close can pair structurally with NNF(¬body[w]).
            //
            // We detect "was abstracted" by checking whether the
            // close_target itself mentions the witness eigen — exactly
            // the predicate compute_block_formulas used.
            auto target_it = lc.step_formula.find(block.close_target_idx);
            if (target_it == lc.step_formula.end()) {
                return MAKE_ERROR
                    << "emit_block_opener(EXISTS_ELIM): close_target step %"
                    << block.close_target_idx << " has no formula";
            }
            if (formula_contains_fixed_var(target_it->second, v)) {
                TRY_ASSIGN(result_pos, env.position_of(result_entry));
                lkr::Exists ex{};
                ex.principal = result_pos;
                ex.witness   = TermRef{lkr_idx};
                lc.out.instrs.emplace_back(std::move(ex));
                TRY(env.apply_exists(result_entry, Term::fixed(v), lc.builder));
            }

            return result_entry;
        }
    }
    return MAKE_ERROR << "emit_block_opener: unhandled block kind";
}

util::ResultStatus emit_block_closer(LowerCtx& lc, Env& env,
                                      SequentEntry qed_entry,
                                      const Block& block,
                                      const Program<nd::Instr>& in,
                                      const StepNegMap& step_to_neg)
{
    if (block.kind == BlockKind::NOT) {
        // close_target is a not_elim deriving ⊥. Pair the negs of its two
        // operands (which are duals of each other).
        const auto& closer_instr = in.instrs[block.close_target_idx];
        const nd::NotElim* ne = std::get_if<nd::NotElim>(&closer_instr);
        if (!ne) {
            return MAKE_ERROR
                << "emit_block_closer(NOT): close_target #"
                << block.close_target_idx << " is not a not_elim";
        }
        auto neg_it = step_to_neg.find(ne->negation.idx);
        auto pos_it = step_to_neg.find(ne->formula.idx);
        if (neg_it == step_to_neg.end() || pos_it == step_to_neg.end()) {
            return MAKE_ERROR
                << "emit_block_closer(NOT): not_elim's operands not cut-in";
        }
        return emit_close(env, neg_it->second, pos_it->second,
                          lc.eigens, lc.builder, lc.out);
    }

    auto neg_it = step_to_neg.find(block.close_target_idx);
    if (neg_it == step_to_neg.end()) {
        return MAKE_ERROR
            << "emit_block_closer: close_target step %"
            << block.close_target_idx << " not cut-in";
    }
    return emit_close(env, qed_entry, neg_it->second,
                      lc.eigens, lc.builder, lc.out);
}

// Cut-spine for one flat step. Mutates env to reflect the post-cut RIGHT
// subgoal and registers step_to_neg[k] = ¬F_k entry.
util::ResultStatus translate_flat_step(LowerCtx& lc, Env& env, uint32_t k,
                                        const Program<nd::Instr>& in,
                                        StepNegMap& step_to_neg)
{
    const auto& instr = in.instrs[k];

    // Let / NotElim emit no LKR ops; their formulas are recorded in
    // step_formula_nnf at compute_block_formulas time and are consumed by
    // downstream ops (or_intro, bottom_elim, NOT-block closer).
    if (std::holds_alternative<nd::Let>(instr) ||
        std::holds_alternative<nd::NotElim>(instr)) {
        return util::Ok();
    }

    auto it = lc.step_formula_nnf.find(k);
    if (it == lc.step_formula_nnf.end()) {
        return MAKE_ERROR
            << "translate_flat_step: step %" << k << " has no NNF formula";
    }
    FormulaHandle F_k_nnf = it->second;

    auto cut = env.apply_cut(F_k_nnf, lc.builder);
    lkr::Cut cut_op{}; cut_op.cut_formula = F_k_nnf;
    lc.out.instrs.emplace_back(std::move(cut_op));

    // Close LEFT.
    Env left_env = std::move(cut.left);
    TRY(close_flat(lc, left_env, k, in, cut.left_phi, step_to_neg));

    // Continue on RIGHT; ¬F_k is now visible to subsequent steps.
    env = std::move(cut.right);
    step_to_neg[k] = cut.right_neg_phi;
    return util::Ok();
}

util::ResultStatus translate_block(LowerCtx& lc, Env& env,
                                    SequentEntry result_entry,
                                    const Block& block,
                                    const Program<nd::Instr>& in,
                                    StepNegMap& step_to_neg)
{
    TRY_ASSIGN(qed_entry,
        emit_block_opener(lc, env, result_entry, block, step_to_neg));

    // Drive emission off the per-block event list. Events are ordered so
    // that B-hosted flats whose definition lives inside a top-level sub-
    // block S of B precede S's SubBlock event — putting their cut on B's
    // RIGHT continuation, where every nested context can see it. Flats
    // hosted at ancestors of B are already cut (via the ancestor's events)
    // and do not appear here; flats hosted at descendants of B appear in
    // those descendants' event lists.
    auto ev_it = lc.plan.events.find(&block);
    if (ev_it == lc.plan.events.end()) {
        return MAKE_ERROR
            << "translate_block: no event list for block at depth "
            << block.depth;
    }
    for (const EmissionEvent& ev : ev_it->second) {
        TRY(std::visit(overloaded{
            [&](const FlatEvent& fe) -> util::ResultStatus {
                return translate_flat_step(lc, env, fe.flat_idx, in, step_to_neg);
            },
            [&](const SubBlockEvent& se) -> util::ResultStatus {
                const Block& sub = *se.sub_block;
                auto sf_it = lc.step_formula.find(sub.closer_idx);
                if (sf_it == lc.step_formula.end()) {
                    return MAKE_ERROR
                        << "translate_block: sub-block closer #"
                        << sub.closer_idx << " has no formula";
                }
                FormulaHandle sub_result_nnf = lc.builder.to_nnf(sf_it->second);
                lc.step_formula_nnf[sub.closer_idx] = sub_result_nnf;

                auto cut = env.apply_cut(sub_result_nnf, lc.builder);
                lkr::Cut cut_op{}; cut_op.cut_formula = sub_result_nnf;
                lc.out.instrs.emplace_back(std::move(cut_op));

                StepNegMap sub_step_to_neg = step_to_neg;
                Env left_env = std::move(cut.left);
                TRY(translate_block(lc, left_env, cut.left_phi, sub, in,
                                    sub_step_to_neg));

                env = std::move(cut.right);
                step_to_neg[sub.closer_idx] = cut.right_neg_phi;
                return util::Ok();
            },
        }, ev));
    }

    return emit_block_closer(lc, env, qed_entry, block, in, step_to_neg);
}

}  // namespace

// =========================================================================
// Public entry points
// =========================================================================

util::Result<Program<lkr::Instr>> NDtoLKR::apply(const Program<nd::Instr>& in) {
    if (!ctx_) {
        return MAKE_ERROR << "NDtoLKR: GlobalContext required";
    }

    Program<lkr::Instr> out;
    out.claim_name = in.claim_name;

    FormulaBuilder                        builder(*ctx_);
    EigenSupply                           eigens(builder);
    StepFormulaMap                        step_formula;
    StepFormulaMap                        step_formula_nnf;
    std::unordered_map<uint32_t, Term>    term_for_idx;
    std::unordered_map<uint32_t, uint32_t> nd_to_lkr_termref;
    std::unordered_map<std::string, Term> name_table;
    std::unordered_map<var_index, int>    var_to_depth;

    auto outer_r = decompose_blocks(in, *ctx_, builder, name_table,
                                     term_for_idx, var_to_depth);
    if (!outer_r.ok()) return outer_r.error();
    std::unique_ptr<Block> outer = std::move(outer_r).unwrap();

    TRY(compute_block_formulas(in, *outer, builder, *ctx_,
                                step_formula, step_formula_nnf,
                                term_for_idx, name_table));

    // Pre-pass: compute scope-deps for every step and determine each
    // flat step's host block (the deepest ancestor whose depth equals
    // step_deps.deepest(); OUTER if deps empty). The lowerer emits each
    // hosted flat's Cut at the start of its host block's body, so the
    // step is in scope for every descendant — even after sub-blocks close.
    DepsPlan plan;
    TRY(compute_deps_plan(in, *outer, step_formula, term_for_idx,
                           var_to_depth, plan));
    build_events(in, *outer, plan);

    // Resolve the claim formula and seed the initial sequent.
    SentenceHandle claim_sentence{};
    if (auto cl = ctx_->find_claim(in.claim_name)) {
        claim_sentence = cl.value();
    } else if (auto kn = ctx_->find_known(in.claim_name)) {
        claim_sentence = kn.value();
    } else {
        return MAKE_ERROR << "NDtoLKR: claim '" << in.claim_name
                          << "' not found in context";
    }
    FormulaHandle nnf_claim = builder.to_nnf(claim_sentence.get().root());

    Env env;
    SequentEntry result_entry = env.seed(nnf_claim);

    LowerCtx lc{*ctx_, builder, eigens, step_formula, step_formula_nnf,
                 term_for_idx, nd_to_lkr_termref, plan, out};
    StepNegMap step_to_neg;
    TRY(translate_block(lc, env, result_entry, *outer, in, step_to_neg));

    return out;
}

util::ResultStatus translate_and_verify(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const Program<nd::Instr>& nd_prog)
{
    NDtoLKR translator(ctx);
    auto translated = translator.apply(nd_prog);
    if (!translated.ok()) return translated.error();

    Proof p{System::LKR, std::move(translated).unwrap()};
    lkr::LKRVerifier v;
    return v.verify(ctx, goal_formula, p);
}

}  // namespace logic::proof::translate
