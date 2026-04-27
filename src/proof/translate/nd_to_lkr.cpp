#include "nd_to_lkr.h"

#include "../lkr/literal.h"
#include "../lkr/ops.h"
#include "../lkr/verifier.h"
#include "../nd/ops.h"
#include "../proof.h"

#include "../../core/formula.h"
#include "../../parser/parser.h"
#include "../../util/error.h"

#include <cstdint>
#include <functional>
#include <memory>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace logic::proof::translate {

namespace {

// =========================================================================
// Block tree (translator-internal scratch state)
// =========================================================================
//
// An ND derivation is a tree of nested scopes. Each scope opens with one
// of {Fix, Assume, ExistsElim} and closes with one of {ForallIntro,
// ImpliesIntro, NotIntro, ExistsIntro-no-witness, Qed}. Inside a scope,
// the body is a sequence of steps — each step is either a flat ND rule
// or a sub-scope.
//
// The flat ND IR (vector<nd::Instr>) is correct for execution; the
// translator reifies the implicit scope tree as private scratch state to
// match the natural shape of structural translation. The Block tree is
// not an IR — it does not cross any pass boundary, has no serialization
// format, and exists only for the lifetime of NDtoLKR::apply().

enum class BlockKind {
    OUTER,         // root; closer is Qed; result is the bare claim conclusion
    FORALL,        // Fix x ... ForallIntro h
    IMPLIES,       // Assume A ... ImpliesIntro h
    NOT,           // Assume A ... NotIntro h_bot
    EXISTS_ELIM,   // ExistsElim h ... ExistsIntro h_inner (no witness)
};

struct Block;

// A body item is either a flat ND step (referenced by its instr index)
// or a nested sub-block.
struct FlatStep { uint32_t nd_idx; };
using BodyItem = std::variant<FlatStep, std::unique_ptr<Block>>;

struct Block {
    BlockKind kind{BlockKind::OUTER};

    uint32_t opener_idx{0};   // ND instr index of opener (N/A for OUTER)
    uint32_t closer_idx{0};   // ND instr index of closer
    uint32_t close_target_idx{0};  // body step the closer references

    // FORALL / EXISTS_ELIM: eigenvariable as Term::fixed.
    Term eigen_term{};

    // IMPLIES / NOT: the assumption formula (raw, parsed from AST).
    FormulaHandle assumption_raw{};

    // For EXISTS_ELIM: the ND step ref to the ∃-formula being eliminated.
    StepRef exists_formula_step{};

    // Body in source order.
    std::vector<BodyItem> body;
};

// =========================================================================
// Pass 1 — decompose_blocks: nd::Program -> Block tree.
// =========================================================================
//
// Stack-walks the flat ND instruction list. Open-ops push a new block
// onto the topmost block's body and onto the parsing stack. Close-ops
// pop. All other ops are flat steps appended to the topmost block's body.
//
// Eigenvariables are allocated here via the translator's FormulaBuilder
// in lockstep with what the LKR verifier will allocate when it processes
// the emitted Forall ops in DFS order. Both builders start fresh and
// allocate sequentially, so the var_index values match.

util::Result<std::unique_ptr<Block>> decompose_blocks(
    const Program<nd::Instr>& in,
    GlobalContext& ctx,
    FormulaBuilder& builder,
    std::unordered_map<std::string, Term>& name_table,
    std::unordered_map<uint32_t, Term>& term_for_idx)
{
    if (in.instrs.empty()) {
        return MAKE_ERROR << "NDtoLKR: empty program";
    }

    auto outer = std::make_unique<Block>();
    outer->kind = BlockKind::OUTER;

    std::vector<Block*> stack{outer.get()};
    std::unordered_map<std::string, size_t> empty_sv, empty_ar;

    auto push_block = [&](std::unique_ptr<Block> b) -> Block* {
        Block* raw = b.get();
        stack.back()->body.push_back(BodyItem{std::move(b)});
        stack.push_back(raw);
        return raw;
    };

    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        const auto& instr = in.instrs[i];

        // ---- Open-ops ----
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
            push_block(std::move(blk));
            continue;
        }
        if (auto* assume = std::get_if<nd::Assume>(&instr)) {
            if (!assume->formula) {
                return MAKE_ERROR << "decompose: assume #" << i << " missing formula AST";
            }
            auto blk = std::make_unique<Block>();
            blk->kind = BlockKind::IMPLIES;  // tentative; reclassified by NotIntro
            blk->opener_idx = i;
            blk->assumption_raw = parse_formula_with_vars(
                assume->formula.get(), ctx, builder,
                name_table, empty_sv, empty_ar);
            push_block(std::move(blk));
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
            push_block(std::move(blk));
            continue;
        }

        // ---- Close-ops ----
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
            stack.back()->kind = BlockKind::NOT;  // reclassify
            stack.back()->closer_idx = i;
            stack.back()->close_target_idx = ni->bottom.idx;
            stack.pop_back();
            continue;
        }
        if (auto* ei = std::get_if<nd::ExistsIntro>(&instr)) {
            if (!ei->witness.has_value()) {
                // Scope-closing form: must close an EXISTS_ELIM block.
                if (stack.back() == outer.get() || stack.back()->kind != BlockKind::EXISTS_ELIM) {
                    return MAKE_ERROR << "decompose: exists_intro (scope-closing) at #" << i
                                      << " has no matching EXISTS_ELIM scope";
                }
                stack.back()->closer_idx = i;
                stack.back()->close_target_idx = ei->body.idx;
                stack.pop_back();
                continue;
            }
            // With explicit witness: a regular flat step (∃-introduction
            // logical rule), not a scope-closer. Falls through.
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

        // All other ops are flat steps appended to the topmost block.
        stack.back()->body.push_back(BodyItem{FlatStep{i}});
    }

    if (stack.size() != 1) {
        return MAKE_ERROR << "decompose: " << (stack.size() - 1)
                          << " unclosed scope(s) at end of program";
    }

    return std::unique_ptr<Block>(std::move(outer));
}

// =========================================================================
// Pass 2 — compute_step_formulas: walk the Block tree, fill in each ND
// step's derived raw FormulaHandle.
// =========================================================================
//
// For each flat step, the raw formula is determined by the rule kind
// and its operand step formulas. For each scope-closing step (the
// closer instr of a sub-block), the formula is the block's "result":
//   FORALL(close_target=h, eigen=e):       ∀x. abstract_at_e(step_formula[h])
//   IMPLIES(close_target=h, assumption=A): A → step_formula[h]
//   NOT(close_target=h_bot, assumption=A): ¬A
//   EXISTS_ELIM(close_target=h):            step_formula[h]  (lifted out)

using StepFormulaMap = std::unordered_map<uint32_t, FormulaHandle>;

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

    // For IMPLIES / NOT blocks: assumption is the assume's "step formula"
    // — register it before walking the body so flat steps that reference
    // op.idx == assume_step_idx via implies_elim et al. resolve correctly.
    if ((blk.kind == BlockKind::IMPLIES || blk.kind == BlockKind::NOT) &&
        blk.assumption_raw.valid()) {
        record(blk.opener_idx, blk.assumption_raw);
    }

    // For EXISTS_ELIM: the eigen-instantiated body of the ∃-formula is
    // the "available" formula inside the scope. Treat it as the step
    // formula of the opener (so body steps that reference the
    // ExistsElim's ND idx via implies_elim, eq_subst, etc., see the
    // instantiated form).
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
            // Compute the sub-block's result formula.
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
                    // The lifted-out formula must not reference the eigen.
                    // We don't enforce here; the LKR verifier's eigen
                    // freshness check (or downstream AxiomGen) will catch
                    // any leak as a verification failure.
                    result = target_f;
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
            return parse_formula_with_vars(op.formula.get(), ctx, builder,
                                            name_table, empty_sv, empty_ar);
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
            return fac.as_compound().right;  // = C
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
                // Scope-closing form is handled at the Block level (closer
                // is recorded as the block's close_target). This arm only
                // fires for explicit-witness ExistsIntro, which is a flat
                // step.
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
            // NotElim produces ⊥. Validate that the operands are dual.
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
            // BottomElim takes ⊥ and a target formula step; result is the
            // target's formula.
            TRY_ASSIGN(target, require_step(op.target_formula, "bottom_elim"));
            return target;
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
// Translator state (TS) and emit/close helpers
// =========================================================================
//
// TS shadows the LKR verifier's runtime sequent state. Each emitted op
// updates ts.seq in lockstep with what the verifier will compute. The
// `step_to_neg_idx` map records, for each ND step whose ¬F_step_nnf has
// been cut into the goal, the index in ts.seq of that cut-in entry.

struct TS {
    GlobalContext&        ctx;
    FormulaBuilder        builder;
    Program<lkr::Instr>&  out;

    std::vector<FormulaHandle> seq;
    std::unordered_map<uint32_t, FormulaHandle>      step_formula;
    std::unordered_map<uint32_t, FormulaHandle>      step_formula_nnf;
    std::unordered_map<uint32_t, size_t>             step_to_neg_idx;
    std::unordered_map<uint32_t, Term>               term_for_idx;
    std::unordered_map<std::string, Term>            name_table;

    // ND TermRef.idx → LKR instr index of the corresponding Forall op
    // that allocated this eigenvariable. Populated by emit_opener for
    // FORALL and EXISTS_ELIM blocks (since both bind term-refs via
    // lkr::Forall on either the result-side or the dual-side respectively).
    std::unordered_map<uint32_t, uint32_t>           nd_to_lkr_termref;

    TS(GlobalContext& c, Program<lkr::Instr>& o)
        : ctx(c), builder(c), out(o) {}

    void emit(lkr::Instr i) { out.instrs.push_back(std::move(i)); }

    // Resolve an ND TermRef (referring to an ND Fix or ExistsElim instr)
    // to an LKR TermRef (referring to the LKR Forall instr that bound
    // the matching eigenvariable).
    util::Result<TermRef> resolve_lkr_termref(TermRef nd_ref, const char* op) const {
        auto it = nd_to_lkr_termref.find(nd_ref.idx);
        if (it == nd_to_lkr_termref.end()) {
            return MAKE_ERROR << op << ": ND term %" << nd_ref.idx
                              << " has no LKR-side binding";
        }
        return TermRef{it->second};
    }
};

FormulaHandle nnf_of(TS& ts, FormulaHandle h)     { return ts.builder.to_nnf(h); }
FormulaHandle nnf_neg_of(TS& ts, FormulaHandle h) {
    return ts.builder.to_nnf(ts.builder.make_not(h));
}

// emit_cut: emit Cut(phi_nnf) and update ts.seq to LEFT subgoal.
// Returns a snapshot of pre-cut ts.seq for the caller to use when
// transitioning to RIGHT.
std::vector<FormulaHandle> emit_cut(TS& ts, FormulaHandle phi_raw) {
    auto snapshot = ts.seq;
    FormulaHandle phi_nnf = nnf_of(ts, phi_raw);
    lkr::Cut cut{};
    cut.cut_formula = phi_nnf;
    ts.emit(std::move(cut));
    ts.seq.push_back(phi_nnf);
    return snapshot;
}

void enter_right(TS& ts, std::vector<FormulaHandle> snapshot,
                  FormulaHandle neg_phi_nnf) {
    snapshot.push_back(neg_phi_nnf);
    ts.seq = std::move(snapshot);
}

// =========================================================================
// Per-rule LEFT-subgoal closure helpers
// =========================================================================
//
// Each helper assumes ts.seq mirrors the LEFT subgoal of a Cut(F_k) —
// pre-cut Γ + F_k_nnf at the end. After the helper, the verifier closes
// LEFT and pops to RIGHT.

util::ResultStatus close_use(TS& ts, const std::string& axiom_name) {
    lkr::UseTheorem ut{}; ut.axiom = AxiomRef{axiom_name};
    ts.emit(std::move(ut));
    return util::Ok();
}

util::ResultStatus close_forall_elim(TS& ts, size_t neg_F_h_idx,
                                       TermRef witness, size_t F_k_idx) {
    lkr::Exists ex{}; ex.principal = neg_F_h_idx; ex.witness = witness;
    ts.emit(std::move(ex));
    lkr::AxiomGen ax{}; ax.a = neg_F_h_idx; ax.b = F_k_idx;
    ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus close_implies_elim(TS& ts, size_t neg_F_impl_idx,
                                        size_t neg_F_ant_idx, size_t F_k_idx) {
    auto pre_and = ts.seq;
    if (neg_F_impl_idx >= pre_and.size())
        return MAKE_ERROR << "close_implies_elim: neg_F_impl_idx OOB";
    const Formula& fn = pre_and[neg_F_impl_idx].get();
    if (!fn.is_compound() || fn.as_compound().op != Op::And)
        return MAKE_ERROR << "close_implies_elim: ¬F_impl not A ∧ ¬B";
    FormulaHandle A_nnf = fn.as_compound().left;
    FormulaHandle negB  = fn.as_compound().right;

    lkr::And andop{}; andop.principal = neg_F_impl_idx;
    ts.emit(std::move(andop));
    ts.seq = pre_and;
    ts.seq[neg_F_impl_idx] = A_nnf;
    {
        lkr::AxiomGen ax{}; ax.a = neg_F_ant_idx; ax.b = neg_F_impl_idx;
        ts.emit(std::move(ax));
    }
    ts.seq = pre_and;
    ts.seq[neg_F_impl_idx] = negB;
    {
        lkr::AxiomGen ax{}; ax.a = neg_F_impl_idx; ax.b = F_k_idx;
        ts.emit(std::move(ax));
    }
    return util::Ok();
}

util::ResultStatus close_and_intro(TS& ts, size_t F_k_idx,
                                     size_t neg_F_a_idx, size_t neg_F_b_idx) {
    auto pre_and = ts.seq;
    if (F_k_idx >= pre_and.size())
        return MAKE_ERROR << "close_and_intro: F_k_idx OOB";
    const Formula& f = pre_and[F_k_idx].get();
    if (!f.is_compound() || f.as_compound().op != Op::And)
        return MAKE_ERROR << "close_and_intro: F_k not A ∧ B";
    FormulaHandle A = f.as_compound().left;
    FormulaHandle B = f.as_compound().right;

    lkr::And andop{}; andop.principal = F_k_idx;
    ts.emit(std::move(andop));
    ts.seq = pre_and; ts.seq[F_k_idx] = A;
    { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_F_a_idx; ts.emit(std::move(ax)); }
    ts.seq = pre_and; ts.seq[F_k_idx] = B;
    { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_F_b_idx; ts.emit(std::move(ax)); }
    return util::Ok();
}

util::ResultStatus close_and_elim_l(TS& ts, size_t neg_F_of_idx, size_t F_k_idx) {
    auto pre_or = ts.seq;
    if (neg_F_of_idx >= pre_or.size())
        return MAKE_ERROR << "close_and_elim_l: neg_F_of_idx OOB";
    const Formula& nf = pre_or[neg_F_of_idx].get();
    if (!nf.is_compound() || nf.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_and_elim_l: ¬F_of not (¬A ∨ ¬B)";
    lkr::Or orop{}; orop.principal = neg_F_of_idx; ts.emit(std::move(orop));
    FormulaHandle negA = nf.as_compound().left;
    FormulaHandle negB = nf.as_compound().right;
    ts.seq[neg_F_of_idx] = negA;
    ts.seq.push_back(negB);
    lkr::AxiomGen ax{}; ax.a = neg_F_of_idx; ax.b = F_k_idx; ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus close_and_elim_r(TS& ts, size_t neg_F_of_idx, size_t F_k_idx) {
    auto pre_or = ts.seq;
    if (neg_F_of_idx >= pre_or.size())
        return MAKE_ERROR << "close_and_elim_r: neg_F_of_idx OOB";
    const Formula& nf = pre_or[neg_F_of_idx].get();
    if (!nf.is_compound() || nf.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_and_elim_r: ¬F_of not (¬A ∨ ¬B)";
    lkr::Or orop{}; orop.principal = neg_F_of_idx; ts.emit(std::move(orop));
    FormulaHandle negA = nf.as_compound().left;
    FormulaHandle negB = nf.as_compound().right;
    ts.seq[neg_F_of_idx] = negA;
    ts.seq.push_back(negB);
    size_t negB_idx = ts.seq.size() - 1;
    lkr::AxiomGen ax{}; ax.a = negB_idx; ax.b = F_k_idx; ts.emit(std::move(ax));
    return util::Ok();
}

// close_iff_intro: F_k = A ↔ B given F_ab (= A→B) and F_ba (= B→A).
// LEFT after Cut(A↔B) holds:
//   F_k_nnf at F_k_idx = (¬A ∨ B) ∧ (A ∨ ¬B)
//   ¬F_ab_nnf at neg_ab_idx = A ∧ ¬B
//   ¬F_ba_nnf at neg_ba_idx = B ∧ ¬A
// Strategy:
//   Outer And on F_k → two subgoals (additive):
//     LEFT-A:  F_k_idx becomes (¬A ∨ B). Or-unfold → ¬A, B.
//              And on ¬F_ab (A ∧ ¬B) → two sub-subgoals:
//                ¬F_ab=A: AxiomGen(F_k_idx=¬A, neg_ab_idx=A).
//                ¬F_ab=¬B: AxiomGen(neg_ab_idx=¬B, B's idx).
//     LEFT-B:  F_k_idx becomes (A ∨ ¬B). Or-unfold → A, ¬B.
//              And on ¬F_ba (B ∧ ¬A) → two sub-subgoals:
//                ¬F_ba=B: AxiomGen(neg_ba_idx=B, ¬B's idx).
//                ¬F_ba=¬A: AxiomGen(F_k_idx=A, neg_ba_idx=¬A).
util::ResultStatus close_iff_intro(TS& ts, size_t F_k_idx,
                                     size_t neg_ab_idx, size_t neg_ba_idx) {
    if (F_k_idx >= ts.seq.size())
        return MAKE_ERROR << "close_iff_intro: F_k_idx OOB";
    const Formula& f = ts.seq[F_k_idx].get();
    if (!f.is_compound() || f.as_compound().op != Op::And)
        return MAKE_ERROR << "close_iff_intro: F_k_nnf not a conjunction";
    FormulaHandle phi = f.as_compound().left;   // ¬A ∨ B
    FormulaHandle psi = f.as_compound().right;  // A ∨ ¬B

    auto pre_outer = ts.seq;
    lkr::And outer_and{}; outer_and.principal = F_k_idx;
    ts.emit(std::move(outer_and));

    // ---- LEFT-A subgoal: F_k_idx = (¬A ∨ B). ----
    ts.seq = pre_outer;
    ts.seq[F_k_idx] = phi;
    if (!phi.get().is_compound() || phi.get().as_compound().op != Op::Or)
        return MAKE_ERROR << "close_iff_intro: phi not (¬A ∨ B)";
    FormulaHandle negA  = phi.get().as_compound().left;
    FormulaHandle B_nnf = phi.get().as_compound().right;
    {
        lkr::Or orop{}; orop.principal = F_k_idx; ts.emit(std::move(orop));
    }
    ts.seq[F_k_idx] = negA;
    ts.seq.push_back(B_nnf);
    size_t B_idx = ts.seq.size() - 1;
    if (neg_ab_idx >= ts.seq.size())
        return MAKE_ERROR << "close_iff_intro: neg_ab_idx OOB";
    const Formula& ab_neg = ts.seq[neg_ab_idx].get();
    if (!ab_neg.is_compound() || ab_neg.as_compound().op != Op::And)
        return MAKE_ERROR << "close_iff_intro: ¬F_ab not (A ∧ ¬B)";
    FormulaHandle A_nnf = ab_neg.as_compound().left;
    FormulaHandle negB  = ab_neg.as_compound().right;
    {
        auto pre_inner = ts.seq;
        lkr::And inner_and{}; inner_and.principal = neg_ab_idx;
        ts.emit(std::move(inner_and));
        // ¬F_ab = A
        ts.seq = pre_inner; ts.seq[neg_ab_idx] = A_nnf;
        { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_ab_idx; ts.emit(std::move(ax)); }
        // ¬F_ab = ¬B
        ts.seq = pre_inner; ts.seq[neg_ab_idx] = negB;
        { lkr::AxiomGen ax{}; ax.a = neg_ab_idx; ax.b = B_idx; ts.emit(std::move(ax)); }
    }

    // ---- LEFT-B subgoal: F_k_idx = (A ∨ ¬B). ----
    ts.seq = pre_outer;
    ts.seq[F_k_idx] = psi;
    if (!psi.get().is_compound() || psi.get().as_compound().op != Op::Or)
        return MAKE_ERROR << "close_iff_intro: psi not (A ∨ ¬B)";
    FormulaHandle A2     = psi.get().as_compound().left;
    FormulaHandle negB2  = psi.get().as_compound().right;
    {
        lkr::Or orop{}; orop.principal = F_k_idx; ts.emit(std::move(orop));
    }
    ts.seq[F_k_idx] = A2;
    ts.seq.push_back(negB2);
    size_t negB_idx = ts.seq.size() - 1;
    if (neg_ba_idx >= ts.seq.size())
        return MAKE_ERROR << "close_iff_intro: neg_ba_idx OOB";
    const Formula& ba_neg = ts.seq[neg_ba_idx].get();
    if (!ba_neg.is_compound() || ba_neg.as_compound().op != Op::And)
        return MAKE_ERROR << "close_iff_intro: ¬F_ba not (B ∧ ¬A)";
    FormulaHandle B2     = ba_neg.as_compound().left;
    FormulaHandle negA2  = ba_neg.as_compound().right;
    {
        auto pre_inner = ts.seq;
        lkr::And inner_and{}; inner_and.principal = neg_ba_idx;
        ts.emit(std::move(inner_and));
        // ¬F_ba = B
        ts.seq = pre_inner; ts.seq[neg_ba_idx] = B2;
        { lkr::AxiomGen ax{}; ax.a = neg_ba_idx; ax.b = negB_idx; ts.emit(std::move(ax)); }
        // ¬F_ba = ¬A
        ts.seq = pre_inner; ts.seq[neg_ba_idx] = negA2;
        { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_ba_idx; ts.emit(std::move(ax)); }
    }
    return util::Ok();
}

// close_or_elim: F_k = C given F_or (A∨B), F_ac (A→C), F_bc (B→C).
// LEFT after Cut(C) holds C_nnf at F_k_idx, ¬F_or_nnf=(¬A∧¬B), ¬F_ac_nnf=(A∧¬C),
// ¬F_bc_nnf=(B∧¬C). Outer And on ¬F_or splits into ¬A / ¬B branches; in
// each branch, And on the matching ¬F_ac/¬F_bc splits to (A,¬C) / (B,¬C),
// closing via AxiomGen on (¬A,A)/(C,¬C) and (¬B,B)/(C,¬C) respectively.
util::ResultStatus close_or_elim(TS& ts, size_t F_k_idx,
                                   size_t neg_or_idx, size_t neg_ac_idx,
                                   size_t neg_bc_idx) {
    if (neg_or_idx >= ts.seq.size())
        return MAKE_ERROR << "close_or_elim: neg_or_idx OOB";
    const Formula& orf = ts.seq[neg_or_idx].get();
    if (!orf.is_compound() || orf.as_compound().op != Op::And)
        return MAKE_ERROR << "close_or_elim: ¬F_or not (¬A ∧ ¬B)";
    FormulaHandle negA = orf.as_compound().left;
    FormulaHandle negB = orf.as_compound().right;

    auto pre_outer = ts.seq;
    lkr::And outer{}; outer.principal = neg_or_idx;
    ts.emit(std::move(outer));

    // ---- LEFT-¬A branch: ¬F_or = ¬A. And on ¬F_ac. ----
    ts.seq = pre_outer;
    ts.seq[neg_or_idx] = negA;
    if (neg_ac_idx >= ts.seq.size())
        return MAKE_ERROR << "close_or_elim: neg_ac_idx OOB";
    const Formula& acf = ts.seq[neg_ac_idx].get();
    if (!acf.is_compound() || acf.as_compound().op != Op::And)
        return MAKE_ERROR << "close_or_elim: ¬F_ac not (A ∧ ¬C)";
    FormulaHandle A_ac  = acf.as_compound().left;
    FormulaHandle negC1 = acf.as_compound().right;
    {
        auto pre_inner = ts.seq;
        lkr::And inner{}; inner.principal = neg_ac_idx;
        ts.emit(std::move(inner));
        ts.seq = pre_inner; ts.seq[neg_ac_idx] = A_ac;
        { lkr::AxiomGen ax{}; ax.a = neg_or_idx; ax.b = neg_ac_idx; ts.emit(std::move(ax)); }
        ts.seq = pre_inner; ts.seq[neg_ac_idx] = negC1;
        { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_ac_idx; ts.emit(std::move(ax)); }
    }

    // ---- LEFT-¬B branch: ¬F_or = ¬B. And on ¬F_bc. ----
    ts.seq = pre_outer;
    ts.seq[neg_or_idx] = negB;
    if (neg_bc_idx >= ts.seq.size())
        return MAKE_ERROR << "close_or_elim: neg_bc_idx OOB";
    const Formula& bcf = ts.seq[neg_bc_idx].get();
    if (!bcf.is_compound() || bcf.as_compound().op != Op::And)
        return MAKE_ERROR << "close_or_elim: ¬F_bc not (B ∧ ¬C)";
    FormulaHandle B_bc  = bcf.as_compound().left;
    FormulaHandle negC2 = bcf.as_compound().right;
    {
        auto pre_inner = ts.seq;
        lkr::And inner{}; inner.principal = neg_bc_idx;
        ts.emit(std::move(inner));
        ts.seq = pre_inner; ts.seq[neg_bc_idx] = B_bc;
        { lkr::AxiomGen ax{}; ax.a = neg_or_idx; ax.b = neg_bc_idx; ts.emit(std::move(ax)); }
        ts.seq = pre_inner; ts.seq[neg_bc_idx] = negC2;
        { lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_bc_idx; ts.emit(std::move(ax)); }
    }
    return util::Ok();
}

util::ResultStatus close_iff_elim_l(TS& ts, size_t neg_F_iff_idx,
                                      size_t neg_F_a_idx, size_t F_k_idx) {
    if (neg_F_iff_idx >= ts.seq.size())
        return MAKE_ERROR << "close_iff_elim_l: neg_F_iff_idx OOB";
    const Formula& nf = ts.seq[neg_F_iff_idx].get();
    if (!nf.is_compound() || nf.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_iff_elim_l: ¬F_iff not (X ∨ Y)";
    FormulaHandle and_a_negb = nf.as_compound().left;
    FormulaHandle nega_and_b = nf.as_compound().right;
    if (!and_a_negb.get().is_compound() || and_a_negb.get().as_compound().op != Op::And)
        return MAKE_ERROR << "close_iff_elim_l: left disjunct not A ∧ ¬B";
    FormulaHandle A_nnf = and_a_negb.get().as_compound().left;
    FormulaHandle negB  = and_a_negb.get().as_compound().right;

    lkr::Or orop{}; orop.principal = neg_F_iff_idx; ts.emit(std::move(orop));
    ts.seq[neg_F_iff_idx] = and_a_negb;
    ts.seq.push_back(nega_and_b);

    auto pre_and = ts.seq;
    lkr::And andop{}; andop.principal = neg_F_iff_idx; ts.emit(std::move(andop));
    ts.seq = pre_and; ts.seq[neg_F_iff_idx] = A_nnf;
    { lkr::AxiomGen ax{}; ax.a = neg_F_iff_idx; ax.b = neg_F_a_idx; ts.emit(std::move(ax)); }
    ts.seq = pre_and; ts.seq[neg_F_iff_idx] = negB;
    { lkr::AxiomGen ax{}; ax.a = neg_F_iff_idx; ax.b = F_k_idx; ts.emit(std::move(ax)); }
    return util::Ok();
}

util::ResultStatus close_iff_elim_r(TS& ts, size_t neg_F_iff_idx,
                                      size_t neg_F_b_idx, size_t F_k_idx) {
    if (neg_F_iff_idx >= ts.seq.size())
        return MAKE_ERROR << "close_iff_elim_r: neg_F_iff_idx OOB";
    const Formula& nf = ts.seq[neg_F_iff_idx].get();
    if (!nf.is_compound() || nf.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_iff_elim_r: ¬F_iff not (X ∨ Y)";
    FormulaHandle and_a_negb = nf.as_compound().left;
    FormulaHandle nega_and_b = nf.as_compound().right;
    if (!nega_and_b.get().is_compound() || nega_and_b.get().as_compound().op != Op::And)
        return MAKE_ERROR << "close_iff_elim_r: right disjunct not ¬A ∧ B";
    FormulaHandle negA  = nega_and_b.get().as_compound().left;
    FormulaHandle B_nnf = nega_and_b.get().as_compound().right;

    lkr::Or orop{}; orop.principal = neg_F_iff_idx; ts.emit(std::move(orop));
    ts.seq[neg_F_iff_idx] = and_a_negb;
    ts.seq.push_back(nega_and_b);
    size_t and_neg_idx = ts.seq.size() - 1;

    auto pre_and = ts.seq;
    lkr::And andop{}; andop.principal = and_neg_idx; ts.emit(std::move(andop));
    ts.seq = pre_and; ts.seq[and_neg_idx] = negA;
    { lkr::AxiomGen ax{}; ax.a = and_neg_idx; ax.b = F_k_idx; ts.emit(std::move(ax)); }
    ts.seq = pre_and; ts.seq[and_neg_idx] = B_nnf;
    { lkr::AxiomGen ax{}; ax.a = and_neg_idx; ax.b = neg_F_b_idx; ts.emit(std::move(ax)); }
    return util::Ok();
}

util::ResultStatus close_or_intro_l(TS& ts, size_t F_k_idx, size_t neg_F_a_idx) {
    if (F_k_idx >= ts.seq.size())
        return MAKE_ERROR << "close_or_intro_l: F_k_idx OOB";
    const Formula& f = ts.seq[F_k_idx].get();
    if (!f.is_compound() || f.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_or_intro_l: F_k not A ∨ B";
    FormulaHandle A = f.as_compound().left;
    FormulaHandle B = f.as_compound().right;
    lkr::Or orop{}; orop.principal = F_k_idx; ts.emit(std::move(orop));
    ts.seq[F_k_idx] = A; ts.seq.push_back(B);
    lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_F_a_idx; ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus close_or_intro_r(TS& ts, size_t F_k_idx, size_t neg_F_b_idx) {
    if (F_k_idx >= ts.seq.size())
        return MAKE_ERROR << "close_or_intro_r: F_k_idx OOB";
    const Formula& f = ts.seq[F_k_idx].get();
    if (!f.is_compound() || f.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_or_intro_r: F_k not A ∨ B";
    FormulaHandle A = f.as_compound().left;
    FormulaHandle B = f.as_compound().right;
    lkr::Or orop{}; orop.principal = F_k_idx; ts.emit(std::move(orop));
    ts.seq[F_k_idx] = A; ts.seq.push_back(B);
    size_t B_idx = ts.seq.size() - 1;
    lkr::AxiomGen ax{}; ax.a = B_idx; ax.b = neg_F_b_idx; ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus close_exists_intro(TS& ts, size_t F_k_idx,
                                        size_t neg_F_body_idx, TermRef witness) {
    lkr::Exists ex{}; ex.principal = F_k_idx; ex.witness = witness;
    ts.emit(std::move(ex));
    lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = neg_F_body_idx;
    ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus close_excluded_middle(TS& ts, size_t F_k_idx) {
    if (F_k_idx >= ts.seq.size())
        return MAKE_ERROR << "close_excluded_middle: F_k_idx OOB";
    const Formula& f = ts.seq[F_k_idx].get();
    if (!f.is_compound() || f.as_compound().op != Op::Or)
        return MAKE_ERROR << "close_excluded_middle: F_k not (A ∨ ¬A)";
    FormulaHandle phi = f.as_compound().left;
    FormulaHandle psi = f.as_compound().right;
    lkr::Or orop{}; orop.principal = F_k_idx; ts.emit(std::move(orop));
    ts.seq[F_k_idx] = phi; ts.seq.push_back(psi);
    size_t psi_idx = ts.seq.size() - 1;
    lkr::AxiomGen ax{}; ax.a = F_k_idx; ax.b = psi_idx; ts.emit(std::move(ax));
    return util::Ok();
}

// =========================================================================
// translate_flat_step: emit Cut(F_k) + close-LEFT for one flat ND rule.
// =========================================================================
//
// On entry: ts.seq mirrors the current goal, with all relevant ¬F_j_nnf
// already cut in (recorded in ts.step_to_neg_idx).
// On exit: ts.seq mirrors the post-cut RIGHT subgoal, with ¬F_k_nnf
// appended; ts.step_to_neg_idx[k] points to that entry.

util::ResultStatus translate_flat_step(TS& ts, uint32_t k,
                                         const Program<nd::Instr>& in)
{
    const auto& instr = in.instrs[k];

    auto resolve_neg = [&](StepRef r, const char* op) -> util::Result<size_t> {
        auto it = ts.step_to_neg_idx.find(r.idx);
        if (it == ts.step_to_neg_idx.end())
            return MAKE_ERROR << op << ": step %" << r.idx << " not yet cut-in";
        return it->second;
    };

    return std::visit(overloaded{

        [&](const nd::Use& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            auto snapshot = emit_cut(ts, F_raw);
            TRY(close_use(ts, op.axiom.name));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::Let& /*op*/) -> util::ResultStatus {
            // Let emits no LKR ops; its formula is already in step_formula
            // (computed by the pre-pass). Nothing to do here.
            ts.step_formula_nnf[k] = nnf_of(ts, ts.step_formula.at(k));
            return util::Ok();
        },

        [&](const nd::ForallElim& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_F_h_idx, resolve_neg(op.formula, "forall_elim"));
            TRY_ASSIGN(lkr_witness, ts.resolve_lkr_termref(op.term, "forall_elim"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_forall_elim(ts, neg_F_h_idx, lkr_witness, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::ImpliesElim& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_impl_idx, resolve_neg(op.impl, "implies_elim"));
            TRY_ASSIGN(neg_ant_idx,  resolve_neg(op.ant,  "implies_elim"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_implies_elim(ts, neg_impl_idx, neg_ant_idx, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::AndIntro& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_a_idx, resolve_neg(op.a, "and_intro"));
            TRY_ASSIGN(neg_b_idx, resolve_neg(op.b, "and_intro"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_and_intro(ts, F_k_idx, neg_a_idx, neg_b_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::AndElimL& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_of_idx, resolve_neg(op.of, "and_elim_l"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_and_elim_l(ts, neg_of_idx, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::AndElimR& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_of_idx, resolve_neg(op.of, "and_elim_r"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_and_elim_r(ts, neg_of_idx, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::IffIntro& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_ab_idx, resolve_neg(op.ab, "iff_intro"));
            TRY_ASSIGN(neg_ba_idx, resolve_neg(op.ba, "iff_intro"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_iff_intro(ts, F_k_idx, neg_ab_idx, neg_ba_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::OrElim& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_or_idx, resolve_neg(op.or_formula, "or_elim"));
            TRY_ASSIGN(neg_ac_idx, resolve_neg(op.ac,         "or_elim"));
            TRY_ASSIGN(neg_bc_idx, resolve_neg(op.bc,         "or_elim"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_or_elim(ts, F_k_idx, neg_or_idx, neg_ac_idx, neg_bc_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::IffElimL& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_iff_idx, resolve_neg(op.iff, "iff_elim_l"));
            TRY_ASSIGN(neg_a_idx,   resolve_neg(op.a,   "iff_elim_l"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_iff_elim_l(ts, neg_iff_idx, neg_a_idx, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::IffElimR& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_iff_idx, resolve_neg(op.iff, "iff_elim_r"));
            TRY_ASSIGN(neg_b_idx,   resolve_neg(op.b,   "iff_elim_r"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_iff_elim_r(ts, neg_iff_idx, neg_b_idx, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::OrIntroL& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_a_idx, resolve_neg(op.a, "or_intro_l"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_or_intro_l(ts, F_k_idx, neg_a_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::OrIntroR& op) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_b_idx, resolve_neg(op.b, "or_intro_r"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_or_intro_r(ts, F_k_idx, neg_b_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::ExistsIntro& op) -> util::ResultStatus {
            // Only explicit-witness form reaches here; scope-closing form
            // is handled at the Block level.
            if (!op.witness.has_value()) {
                return MAKE_ERROR << "exists_intro: scope-closing form must be a block closer";
            }
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            TRY_ASSIGN(neg_body_idx, resolve_neg(op.body, "exists_intro"));
            TRY_ASSIGN(lkr_witness, ts.resolve_lkr_termref(*op.witness, "exists_intro"));
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            // After Exists rule, F_k_idx becomes body_nnf[x:=witness] =
            // ts.step_formula_nnf[op.body.idx]. Update shadow seq.
            ts.seq[F_k_idx] = ts.step_formula_nnf.at(op.body.idx);
            TRY(close_exists_intro(ts, F_k_idx, neg_body_idx, lkr_witness));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::NotElim& /*op*/) -> util::ResultStatus {
            // NotElim's "result" is ⊥ — there's no useful Cut on ⊥, since
            // [Γ, ⊥] is unprovable in isolation. The contradiction is
            // already available in the goal: cuts on the operands have
            // placed φ_nnf and ¬φ_nnf as disjuncts. Subsequent ops that
            // need the contradiction (BottomElim, or NotIntro at the
            // block level) look up the operands directly.
            //
            // No LKR ops emitted; step_to_neg_idx is intentionally NOT
            // populated for k.
            ts.step_formula_nnf[k] = nnf_of(ts, ts.step_formula.at(k));
            return util::Ok();
        },

        [&](const nd::BottomElim& op) -> util::ResultStatus {
            // BottomElim(h_bot, h_target): produce h_target's formula
            // from the contradiction available via h_bot. h_bot must be
            // a NotElim step whose operands' duals are in the goal.
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            // Look up the NotElim instr.
            const auto& bot_instr = in.instrs[op.bottom.idx];
            const nd::NotElim* ne = std::get_if<nd::NotElim>(&bot_instr);
            if (!ne) {
                return MAKE_ERROR << "bottom_elim: bot step %" << op.bottom.idx
                                  << " is not a not_elim (other contradiction "
                                     "patterns not yet supported)";
            }
            TRY_ASSIGN(neg_neg_idx, resolve_neg(ne->negation, "bottom_elim"));
            TRY_ASSIGN(neg_pos_idx, resolve_neg(ne->formula,  "bottom_elim"));
            auto snapshot = emit_cut(ts, F_raw);
            // LEFT close: AxiomGen on the contradicting cut-in pair (already
            // in Γ before the BottomElim cut, hence in LEFT after the cut).
            { lkr::AxiomGen ax{}; ax.a = neg_neg_idx; ax.b = neg_pos_idx; ts.emit(std::move(ax)); }
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const nd::ExcludedMiddle& /*op*/) -> util::ResultStatus {
            FormulaHandle F_raw = ts.step_formula.at(k);
            FormulaHandle negF_nnf = nnf_neg_of(ts, F_raw);
            auto snapshot = emit_cut(ts, F_raw);
            size_t F_k_idx = ts.seq.size() - 1;
            TRY(close_excluded_middle(ts, F_k_idx));
            enter_right(ts, std::move(snapshot), negF_nnf);
            ts.step_formula_nnf[k] = nnf_of(ts, F_raw);
            ts.step_to_neg_idx[k]  = ts.seq.size() - 1;
            return util::Ok();
        },

        [&](const auto& op) -> util::ResultStatus {
            (void)op;
            return MAKE_ERROR
                << "translate_flat_step: ND op variant index "
                << instr.index() << " not yet supported";
        },

    }, instr);
}

// =========================================================================
// translate_block: recursive emit for a Block of any kind.
// =========================================================================
//
// Pre-condition: ts.seq mirrors the LEFT subgoal at this depth, with the
// block's `result_nnf` at slot `result_idx` (placed there by the parent
// Cut). For OUTER, ts.seq is the initial goal sequent and result_idx is
// the index where the outer claim disjunct lives.
//
// Post-condition: the block's LEFT subgoal closes; the verifier pops to
// the parent's RIGHT.

util::ResultStatus translate_block(TS& ts, const Block& block,
                                     size_t result_idx,
                                     const Program<nd::Instr>& in);

// Helper: given a Block whose `result_idx` slot in ts.seq currently holds
// the result_nnf, apply the appropriate opening rule to set up the body's
// initial state.
//
// Returns the index in ts.seq where the body's "qed-target slot" lives —
// the slot that the final AxiomGen will reference.
util::Result<size_t> emit_opener(TS& ts, const Block& block, size_t result_idx) {
    switch (block.kind) {
        case BlockKind::OUTER:
            // OUTER: no opener. The body proves the goal disjunct directly.
            return result_idx;

        case BlockKind::FORALL: {
            // result_nnf at result_idx is ∀x. body_nnf. Apply Forall rule
            // to introduce eigenvar; entry becomes body_nnf[x:=eigen].
            const Formula& f = ts.seq[result_idx].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Forall)
                return MAKE_ERROR << "emit_opener(FORALL): result_nnf is not ∀x.φ";
            uint32_t lkr_idx = static_cast<uint32_t>(ts.out.instrs.size());
            lkr::Forall fop{}; fop.principal = result_idx;
            ts.emit(std::move(fop));
            ts.nd_to_lkr_termref[block.opener_idx] = lkr_idx;
            FormulaHandle body_inst = ts.builder.instantiate_quantifier_body(
                f.as_quantified().body, block.eigen_term);
            ts.seq[result_idx] = body_inst;
            return result_idx;
        }

        case BlockKind::IMPLIES: {
            // result_nnf at result_idx is ¬A_nnf ∨ body_nnf. Apply Or
            // rule: replaces with ¬A_nnf at result_idx, appends body_nnf.
            const Formula& f = ts.seq[result_idx].get();
            if (!f.is_compound() || f.as_compound().op != Op::Or)
                return MAKE_ERROR << "emit_opener(IMPLIES): result_nnf is not ¬A ∨ body";
            FormulaHandle negA = f.as_compound().left;
            FormulaHandle body = f.as_compound().right;
            lkr::Or orop{}; orop.principal = result_idx; ts.emit(std::move(orop));
            ts.seq[result_idx] = negA;
            ts.seq.push_back(body);
            // Mark the assumption's ND idx as cut-in at result_idx so flat
            // body steps can reference it via implies_elim et al.
            ts.step_to_neg_idx[block.opener_idx] = result_idx;
            return ts.seq.size() - 1;  // body slot
        }

        case BlockKind::NOT: {
            // result_nnf at result_idx is ¬A_nnf (atomic-ish). No opening
            // rule. The "qed-target slot" is conceptually the
            // ¬A_nnf entry, but for NOT the close uses the body's
            // contradiction, not the result slot. Caller must handle.
            //
            // Mark the assumption as available: its ¬A_nnf is at result_idx.
            ts.step_to_neg_idx[block.opener_idx] = result_idx;
            return result_idx;
        }

        case BlockKind::EXISTS_ELIM: {
            // The ∃-formula's ¬-NNF (= ∀x.¬φ) must already be cut into
            // the goal — i.e., step_to_neg_idx[block.exists_formula_step]
            // is set. Apply Forall on that entry to introduce the eigen
            // and obtain ¬φ[eigen] in the goal.
            auto neg_exists_it = ts.step_to_neg_idx.find(
                block.exists_formula_step.idx);
            if (neg_exists_it == ts.step_to_neg_idx.end())
                return MAKE_ERROR << "emit_opener(EXISTS_ELIM): exists step %"
                                  << block.exists_formula_step.idx
                                  << " not yet cut-in";
            size_t neg_exists_idx = neg_exists_it->second;
            const Formula& f = ts.seq[neg_exists_idx].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Forall)
                return MAKE_ERROR << "emit_opener(EXISTS_ELIM): cut-in is not ∀x.¬φ";
            uint32_t lkr_idx = static_cast<uint32_t>(ts.out.instrs.size());
            lkr::Forall fop{}; fop.principal = neg_exists_idx;
            ts.emit(std::move(fop));
            ts.nd_to_lkr_termref[block.opener_idx] = lkr_idx;
            FormulaHandle inst = ts.builder.instantiate_quantifier_body(
                f.as_quantified().body, block.eigen_term);
            ts.seq[neg_exists_idx] = inst;
            // Mark the opener as available (the eigen-inst body is at
            // neg_exists_idx).
            ts.step_to_neg_idx[block.opener_idx] = neg_exists_idx;
            // result_idx still holds the lifted-out formula F (= the
            // EXISTS_ELIM result). Final close compares against it.
            return result_idx;
        }
    }
    return MAKE_ERROR << "emit_opener: unhandled block kind";
}

util::ResultStatus emit_closer(TS& ts, const Block& block, size_t qed_slot,
                                 const Program<nd::Instr>& in) {
    if (block.kind == BlockKind::NOT) {
        // For NOT, the "result" is ¬A and the body proves ⊥ (a contradiction).
        // The close_target must be a `not_elim` step whose two operands form
        // a dual literal pair. After the body's cuts, both sides of the
        // contradiction are in the goal as ¬-cut-ins.
        const auto& closer_instr = in.instrs[block.close_target_idx];
        if (auto* ne = std::get_if<nd::NotElim>(&closer_instr)) {
            auto neg_it = ts.step_to_neg_idx.find(ne->negation.idx);
            auto pos_it = ts.step_to_neg_idx.find(ne->formula.idx);
            if (neg_it == ts.step_to_neg_idx.end() ||
                pos_it == ts.step_to_neg_idx.end()) {
                return MAKE_ERROR << "emit_closer(NOT): not_elim's operands "
                                     "not yet cut-in";
            }
            lkr::AxiomGen ax{}; ax.a = neg_it->second; ax.b = pos_it->second;
            ts.emit(std::move(ax));
            return util::Ok();
        }
        return MAKE_ERROR << "emit_closer(NOT): close_target #"
                          << block.close_target_idx
                          << " is not a not_elim step (other contradiction "
                             "patterns not yet supported)";
    }

    // For OUTER / FORALL / IMPLIES / EXISTS_ELIM: AxiomGen between
    // the qed-target's result-side slot and its negation cut-in.
    auto neg_it = ts.step_to_neg_idx.find(block.close_target_idx);
    if (neg_it == ts.step_to_neg_idx.end())
        return MAKE_ERROR << "emit_closer: close_target step %"
                          << block.close_target_idx << " not cut-in";
    lkr::AxiomGen ax{}; ax.a = qed_slot; ax.b = neg_it->second;
    ts.emit(std::move(ax));
    return util::Ok();
}

util::ResultStatus translate_block(TS& ts, const Block& block,
                                     size_t result_idx,
                                     const Program<nd::Instr>& in)
{
    TRY_ASSIGN(qed_slot, emit_opener(ts, block, result_idx));

    for (const auto& item : block.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            TRY(translate_flat_step(ts, flat->nd_idx, in));
        } else {
            const Block& sub = *std::get<std::unique_ptr<Block>>(item);
            FormulaHandle sub_result_raw = ts.step_formula.at(sub.closer_idx);
            FormulaHandle sub_result_nnf = nnf_of(ts, sub_result_raw);
            FormulaHandle sub_neg_nnf    = nnf_neg_of(ts, sub_result_raw);
            ts.step_formula_nnf[sub.closer_idx] = sub_result_nnf;

            auto snapshot = ts.seq;

            lkr::Cut cut{}; cut.cut_formula = sub_result_nnf;
            ts.emit(std::move(cut));
            ts.seq.push_back(sub_result_nnf);
            size_t sub_result_idx = ts.seq.size() - 1;

            TRY(translate_block(ts, sub, sub_result_idx, in));

            // After translate_block(sub): LEFT closed, verifier popped to
            // parent RIGHT. Mirror RIGHT in ts.seq.
            snapshot.push_back(sub_neg_nnf);
            ts.seq = std::move(snapshot);
            ts.step_to_neg_idx[sub.closer_idx] = ts.seq.size() - 1;
        }
    }

    return emit_closer(ts, block, qed_slot, in);
}

// =========================================================================
// Initial sequent setup for OUTER block
// =========================================================================
//
// The OUTER block's "result" is the entire claim formula. Initial verifier
// sequent is [NNF(claim_root)]. We mirror this in ts.seq: a single entry
// containing NNF(claim) — which serves as the OUTER block's result_idx=0.

util::Result<size_t> setup_outer_initial(TS& ts, GlobalContext& ctx,
                                           const std::string& claim_name) {
    SentenceHandle claim_sentence{};
    if (auto cl = ctx.find_claim(claim_name)) {
        claim_sentence = cl.value();
    } else if (auto kn = ctx.find_known(claim_name)) {
        claim_sentence = kn.value();
    } else {
        return MAKE_ERROR << "NDtoLKR: claim '" << claim_name
                          << "' not found in context";
    }
    FormulaHandle nnf_claim = ts.builder.to_nnf(claim_sentence.get().root());
    ts.seq.clear();
    ts.seq.push_back(nnf_claim);
    return size_t{0};
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

    TS ts(*ctx_, out);

    // Wrap the three passes in a try-block: any std::out_of_range or
    // similar exception (e.g., from a missing step_formula entry) is
    // converted to a translator error rather than aborting the process.
    // This is defensive — translator invariants should mean these
    // exceptions don't fire in practice — but it preserves the contract
    // that NDtoLKR::apply returns Result, never throws.
    try {
        // Pass 1: decompose the flat ND IR into a Block tree.
        auto outer_r = decompose_blocks(in, *ctx_, ts.builder,
                                         ts.name_table, ts.term_for_idx);
        if (!outer_r.ok()) return outer_r.error();
        std::unique_ptr<Block> outer = std::move(outer_r).unwrap();

        // Pass 2: compute each ND step's derived raw formula (and NNF form).
        TRY(compute_block_formulas(in, *outer, ts.builder, *ctx_,
                                    ts.step_formula, ts.step_formula_nnf,
                                    ts.term_for_idx, ts.name_table));

        // Initial sequent: [NNF(claim_root)] at index 0.
        TRY_ASSIGN(outer_result_idx, setup_outer_initial(ts, *ctx_, in.claim_name));

        // Pass 3: recursive emit.
        TRY(translate_block(ts, *outer, outer_result_idx, in));

        return out;
    } catch (const std::out_of_range& e) {
        return MAKE_ERROR << "NDtoLKR: internal map lookup miss: " << e.what();
    } catch (const std::exception& e) {
        return MAKE_ERROR << "NDtoLKR: internal exception: " << e.what();
    }
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
