#include "cut_spine.h"

#include "emit_close.h"

#include "src/proof/ir.h"

#include <algorithm>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

// =========================================================================
// Multiplicative-And split helper. Centralises the (small but error-prone)
// position remapping that LEFT and RIGHT subgoals undergo, and emits the
// And op with the computed partition.
//
// Inputs:
//   principal       — the And's principal index in the parent shadow.
//   left_needs      — parent indices that the LEFT subgoal needs (in
//                     addition to entries naturally inherited).
//   right_needs     — parent indices that the RIGHT subgoal needs.
//   left_phi        — the formula appended at the end of LEFT (the And's
//                     left conjunct).
//   right_theta     — the formula appended at the end of RIGHT.
//
// Outputs:
//   left_shadow, left_phi_idx          — child shadow + position of left_phi
//   right_shadow, right_theta_idx      — child shadow + position of right_theta
//   left_remap, right_remap            — parent_idx → child_idx maps
//
// Splitting rules:
//   - principal stays in neither child (consumed by the And op).
//   - Indices in right_needs go to RIGHT.
//   - Everything else (including indices in left_needs) goes to LEFT.
//
// Indices appearing in BOTH sets are an error (need a Weakening prep
// step before calling this helper). Indices in neither set go to LEFT
// by default — they're "carried along" entries.
struct AndSplit {
    SequentShadow                            left;
    SequentShadow                            right;
    size_t                                   left_phi_idx{0};
    size_t                                   right_theta_idx{0};
    std::unordered_map<size_t, size_t>       left_remap;
    std::unordered_map<size_t, size_t>       right_remap;
};

util::Result<AndSplit> emit_and_split(
    SequentShadow&             parent,
    size_t                     principal,
    const std::vector<size_t>& right_needs,
    FormulaHandle              left_phi,
    FormulaHandle              right_theta,
    std::vector<lkr::Instr>&   out)
{
    std::unordered_set<size_t> right_set(
        right_needs.begin(), right_needs.end());
    if (right_set.count(principal)) {
        return MAKE_ERROR
            << "emit_and_split: principal #" << principal
            << " appears in right_needs (use Weakening prep)";
    }

    std::vector<size_t> left_partition;
    left_partition.reserve(parent.entries.size());
    for (size_t k = 0; k < parent.entries.size(); ++k) {
        if (k == principal) continue;
        if (right_set.count(k)) continue;
        left_partition.push_back(k);
    }

    {
        lkr::And op{};
        op.principal       = principal;
        op.left_partition  = left_partition;
        out.emplace_back(std::move(op));
    }

    AndSplit s;
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
    s.left.entries.push_back(left_phi);

    for (size_t i = 0; i < parent.entries.size(); ++i) {
        if (i == principal) continue;
        if (!right_set.count(i)) continue;
        s.right_remap[i] = s.right.entries.size();
        s.right.entries.push_back(parent.entries[i]);
    }
    s.right_theta_idx = s.right.entries.size();
    s.right.entries.push_back(right_theta);

    return s;
}

// =========================================================================
// Flat-step classifier — which ND ops emit no LKR ops vs which trigger the
// cut-spine schema.
// =========================================================================

// "Marker" ops: scope opener/closer markers and inert helpers. The block
// tree consumed Fix/Assume/ExistsElim and the closers (ForallIntro,
// ImpliesIntro, NotIntro, scope-closing ExistsIntro). The remaining
// no-emit cases are Let (inert formula handle) and NotElim (ghost ⊥
// consumed only by enclosing NOT closer or BottomElim).
bool is_no_emit_flat(const nd::Instr& instr) {
    return std::holds_alternative<nd::Let>(instr) ||
           std::holds_alternative<nd::NotElim>(instr);
}

// =========================================================================
// Per-rule close_X handlers — proven (= deriving F_k from Γ ∪ {F_k_nnf})
// on the LEFT branch of the cut spine.
// =========================================================================

util::ResultStatus close_use(
    CutSpineContext&         cc,
    const nd::Use&           op,
    SequentShadow& /*left*/,
    size_t /*f_k_idx*/,
    std::vector<lkr::Instr>& out)
{
    (void)cc;
    // NNF(F_k) equals NNF(the axiom/theorem's formula) — verifier checks.
    lkr::CloseByLemma cb{};
    cb.axiom = AxiomRef{op.axiom.name};
    out.emplace_back(std::move(cb));
    return util::Ok();
}

util::ResultStatus close_schema_inst(
    CutSpineContext&         cc,
    const nd::SchemaInst&    op,
    SequentShadow& /*left*/,
    size_t /*f_k_idx*/,
    std::vector<lkr::Instr>& out)
{
    (void)cc;
    lkr::CloseByLemma cb{};
    cb.axiom    = AxiomRef{op.data.schema.name};
    cb.bindings = op.data.bindings;
    out.emplace_back(std::move(cb));
    return util::Ok();
}

// close_forall_elim: F_k = body[x:=t] from step h whose formula is ∀x.body.
// i_h holds ∃x.NNF(¬body). Emit Exists(i_h, witness=t_lkr) — shadow mutates
// to NNF(¬body)[x:=t] at i_h. Then emit_close(F_k_idx, i_h) — the two
// entries are NNF-dual by construction (NNF(¬body)[x:=t] = NNF(¬(body[x:=t]))).
util::ResultStatus close_forall_elim(
    CutSpineContext&         cc,
    const nd::ForallElim&    op,
    SequentShadow&           left,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out)
{
    auto i_h_it = left.step_to_neg_idx.find(op.formula.idx);
    if (i_h_it == left.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "close_forall_elim: source step #" << op.formula.idx
            << " has no negation entry in the LEFT shadow";
    }
    size_t i_h = i_h_it->second;

    auto t_it = left.lkr_term_for.find(op.term.idx);
    if (t_it == left.lkr_term_for.end()) {
        return MAKE_ERROR
            << "close_forall_elim: ND TermRef #" << op.term.idx
            << " has no LKR TermRef mapping (term not bound by Fix / "
            << "ExistsElim?)";
    }
    const auto& binding = t_it->second;

    FormulaHandle entry = left.entries[i_h];
    if (!entry.get().is_quantified() ||
        entry.get().as_quantified().op != Op::Exists) {
        return MAKE_ERROR
            << "close_forall_elim: entry at i_h=" << i_h
            << " is not ∃x.NNF(¬body)";
    }
    FormulaHandle neg_body = entry.get().as_quantified().body;
    FormulaHandle inst = cc.builder.instantiate_quantifier_body(
        neg_body, binding.value);

    {
        lkr::Exists eop{};
        eop.principal = i_h;
        eop.witness   = binding.lkr_ref;
        out.emplace_back(std::move(eop));
    }
    left.entries[i_h] = inst;

    EmitCloseContext ecc{cc.builder};
    return emit_close(ecc, left, f_k_idx, i_h, out);
}

util::ResultStatus dispatch_close(
    CutSpineContext&         cc,
    uint32_t                 nd_idx,
    SequentShadow&           left,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out)
{
    const auto& instr = cc.prog.instrs[nd_idx];
    if (auto* op = std::get_if<nd::Use>(&instr)) {
        return close_use(cc, *op, left, f_k_idx, out);
    }
    if (auto* op = std::get_if<nd::SchemaInst>(&instr)) {
        return close_schema_inst(cc, *op, left, f_k_idx, out);
    }
    if (auto* op = std::get_if<nd::ForallElim>(&instr)) {
        return close_forall_elim(cc, *op, left, f_k_idx, out);
    }

    // -- Propositional rules --

    if (auto* op = std::get_if<nd::AndIntro>(&instr)) {
        // F_k = A ∧ B at f_k_idx. i_a holds NNF(¬A); i_b holds NNF(¬B).
        // Mult-And on f_k_idx with partition: LEFT gets i_a, RIGHT gets i_b.
        auto i_a_it = left.step_to_neg_idx.find(op->a.idx);
        auto i_b_it = left.step_to_neg_idx.find(op->b.idx);
        if (i_a_it == left.step_to_neg_idx.end() ||
            i_b_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR
                << "close_and_intro: missing negation entry for operand";
        }
        size_t i_a = i_a_it->second;
        size_t i_b = i_b_it->second;
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_compound() ||
            cut_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR
                << "close_and_intro: cut entry is not And";
        }
        FormulaHandle nnf_a = cut_entry.get().as_compound().left;
        FormulaHandle nnf_b = cut_entry.get().as_compound().right;
        TRY_ASSIGN(split, emit_and_split(left, f_k_idx, {i_b}, nnf_a, nnf_b, out));
        size_t left_i_a = split.left_remap.at(i_a);
        EmitCloseContext ecc{cc.builder};
        TRY(emit_close(ecc, split.left, split.left_phi_idx, left_i_a, out));
        size_t right_i_b = split.right_remap.at(i_b);
        return emit_close(ecc, split.right, split.right_theta_idx, right_i_b, out);
    }

    if (auto* op = std::get_if<nd::AndElimL>(&instr)) {
        // F_k = A. i_of holds NNF(¬A) ∨ NNF(¬B).
        // Emit Or(i_of) → entries[i_of] := NNF(¬A); appended NNF(¬B).
        // emit_close(f_k_idx, i_of).
        auto i_of_it = left.step_to_neg_idx.find(op->of.idx);
        if (i_of_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_and_elim_l: missing negation for operand";
        }
        size_t i_of = i_of_it->second;
        FormulaHandle of_entry = left.entries[i_of];
        if (!of_entry.get().is_compound() ||
            of_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_and_elim_l: negation entry is not Or";
        }
        FormulaHandle neg_a = of_entry.get().as_compound().left;
        FormulaHandle neg_b = of_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = i_of;
            out.emplace_back(std::move(oop));
        }
        left.entries[i_of] = neg_a;
        left.append(neg_b);
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, i_of, out);
    }

    if (auto* op = std::get_if<nd::AndElimR>(&instr)) {
        // Symmetric: F_k = B; close f_k_idx vs the appended NNF(¬B).
        auto i_of_it = left.step_to_neg_idx.find(op->of.idx);
        if (i_of_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_and_elim_r: missing negation for operand";
        }
        size_t i_of = i_of_it->second;
        FormulaHandle of_entry = left.entries[i_of];
        if (!of_entry.get().is_compound() ||
            of_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_and_elim_r: negation entry is not Or";
        }
        FormulaHandle neg_a = of_entry.get().as_compound().left;
        FormulaHandle neg_b = of_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = i_of;
            out.emplace_back(std::move(oop));
        }
        left.entries[i_of] = neg_a;
        size_t neg_b_idx = left.append(neg_b);
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, neg_b_idx, out);
    }

    if (auto* op = std::get_if<nd::OrIntroL>(&instr)) {
        // F_k = A ∨ B (a derived = A, b_formula = B). Emit Or(f_k_idx) →
        // entries[f_k_idx] := NNF(A); appended NNF(B). i_a (negation of A)
        // is in scope. emit_close(f_k_idx, i_a). The appended NNF(B) is
        // unused (the goal will be closed by the AxiomLit on the (NNF(A),
        // NNF(¬A)) pair, leaving the appended entry irrelevant).
        auto i_a_it = left.step_to_neg_idx.find(op->a.idx);
        if (i_a_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_or_intro_l: missing negation for a";
        }
        size_t i_a = i_a_it->second;
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_compound() ||
            cut_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_or_intro_l: cut entry is not Or";
        }
        FormulaHandle nnf_a = cut_entry.get().as_compound().left;
        FormulaHandle nnf_b = cut_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = f_k_idx;
            out.emplace_back(std::move(oop));
        }
        left.entries[f_k_idx] = nnf_a;
        left.append(nnf_b);
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, i_a, out);
    }

    if (auto* op = std::get_if<nd::OrIntroR>(&instr)) {
        // Symmetric: a_formula = A, b derived = B. Or(f_k_idx) splits.
        // emit_close on appended NNF(B) vs i_b.
        auto i_b_it = left.step_to_neg_idx.find(op->b.idx);
        if (i_b_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_or_intro_r: missing negation for b";
        }
        size_t i_b = i_b_it->second;
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_compound() ||
            cut_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_or_intro_r: cut entry is not Or";
        }
        FormulaHandle nnf_a = cut_entry.get().as_compound().left;
        FormulaHandle nnf_b = cut_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = f_k_idx;
            out.emplace_back(std::move(oop));
        }
        left.entries[f_k_idx] = nnf_a;
        size_t nnf_b_idx = left.append(nnf_b);
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, nnf_b_idx, i_b, out);
    }

    if (auto* op = std::get_if<nd::ImpliesElim>(&instr)) {
        // F_k = consequent. i_impl holds NNF(¬(A→B)) = NNF(A) ∧ NNF(¬B).
        // i_ant holds NNF(¬A).
        // Mult-And on i_impl: LEFT needs i_ant; RIGHT needs f_k_idx.
        // LEFT pairs NNF(A) (left_phi) with NNF(¬A) (at i_ant);
        // RIGHT pairs NNF(¬B) (right_theta) with NNF(B) (at f_k_idx).
        auto i_impl_it = left.step_to_neg_idx.find(op->impl.idx);
        auto i_ant_it  = left.step_to_neg_idx.find(op->ant.idx);
        if (i_impl_it == left.step_to_neg_idx.end() ||
            i_ant_it  == left.step_to_neg_idx.end()) {
            return MAKE_ERROR
                << "close_implies_elim: missing negation for operand";
        }
        size_t i_impl = i_impl_it->second;
        size_t i_ant  = i_ant_it->second;
        FormulaHandle impl_entry = left.entries[i_impl];
        if (!impl_entry.get().is_compound() ||
            impl_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR
                << "close_implies_elim: i_impl entry is not And";
        }
        FormulaHandle nnf_a    = impl_entry.get().as_compound().left;
        FormulaHandle nnf_negb = impl_entry.get().as_compound().right;
        TRY_ASSIGN(split, emit_and_split(left, i_impl, {f_k_idx},
                                          nnf_a, nnf_negb, out));
        size_t left_i_ant = split.left_remap.at(i_ant);
        EmitCloseContext ecc{cc.builder};
        TRY(emit_close(ecc, split.left, split.left_phi_idx, left_i_ant, out));
        size_t right_f_k = split.right_remap.at(f_k_idx);
        return emit_close(ecc, split.right, split.right_theta_idx, right_f_k, out);
    }

    if (auto* op = std::get_if<nd::BottomElim>(&instr)) {
        // F_k = target_formula. `bottom` is a NotElim ghost: find its
        // negation/formula operands, get their negation entries (positions
        // of NNF(formula) and NNF(¬formula)), pair via emit_close.
        // The verifier accepts an AxiomLit closing any open goal — the
        // F_k entry sits at f_k_idx but doesn't need to participate.
        const auto& bot_instr = cc.prog.instrs[op->bottom.idx];
        if (!std::holds_alternative<nd::NotElim>(bot_instr)) {
            return MAKE_ERROR
                << "close_bottom_elim: BottomElim.bottom at #" << op->bottom.idx
                << " is not a NotElim";
        }
        const auto& ne = std::get<nd::NotElim>(bot_instr);
        auto i_neg_it  = left.step_to_neg_idx.find(ne.negation.idx);
        auto i_form_it = left.step_to_neg_idx.find(ne.formula.idx);
        if (i_neg_it  == left.step_to_neg_idx.end() ||
            i_form_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR
                << "close_bottom_elim: NotElim operand has no negation entry";
        }
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, i_neg_it->second, i_form_it->second, out);
    }

    if (auto* op = std::get_if<nd::DoubleNegElim>(&instr)) {
        // F_k = A; step_formula[of] = ¬¬A. NNF erases the double-neg, so
        // F_k_nnf = NNF(A) and ¬F_of_nnf = NNF(¬¬¬A) = NNF(¬A). They are
        // duals — close directly.
        auto i_of_it = left.step_to_neg_idx.find(op->of.idx);
        if (i_of_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_double_neg_elim: missing negation for of";
        }
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, i_of_it->second, out);
    }

    if (auto* op = std::get_if<nd::ExcludedMiddle>(&instr)) {
        (void)op;
        // F_k = A ∨ ¬A. F_k_nnf = NNF(A) ∨ NNF(¬A) — the two disjuncts
        // are NNF-dual by construction (the second is by definition
        // NNF(¬A) which is the dual of NNF(A)). Or(f_k_idx) splits, then
        // emit_close closes the two leaves.
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_compound() ||
            cut_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_excluded_middle: cut entry is not Or";
        }
        FormulaHandle nnf_a   = cut_entry.get().as_compound().left;
        FormulaHandle nnf_neg = cut_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = f_k_idx;
            out.emplace_back(std::move(oop));
        }
        left.entries[f_k_idx] = nnf_a;
        size_t neg_idx = left.append(nnf_neg);
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, neg_idx, out);
    }

    if (auto* op = std::get_if<nd::OrElim>(&instr)) {
        // F_k = C. i_or = NNF(¬A) ∧ NNF(¬B). i_ac = NNF(A) ∧ NNF(¬C).
        // i_bc = NNF(B) ∧ NNF(¬C). Both sides of the outer And split need
        // a copy of NNF(C) (to contradict the inner NNF(¬C)). Weakening
        // duplicates NNF(C) first; then a nested mult-And pattern closes.
        auto i_or_it = left.step_to_neg_idx.find(op->or_formula.idx);
        auto i_ac_it = left.step_to_neg_idx.find(op->ac.idx);
        auto i_bc_it = left.step_to_neg_idx.find(op->bc.idx);
        if (i_or_it == left.step_to_neg_idx.end() ||
            i_ac_it == left.step_to_neg_idx.end() ||
            i_bc_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_or_elim: missing negation for operand";
        }
        size_t i_or = i_or_it->second;
        size_t i_ac = i_ac_it->second;
        size_t i_bc = i_bc_it->second;

        FormulaHandle or_entry = left.entries[i_or];
        if (!or_entry.get().is_compound() ||
            or_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR << "close_or_elim: i_or entry is not And";
        }
        FormulaHandle neg_a = or_entry.get().as_compound().left;
        FormulaHandle neg_b = or_entry.get().as_compound().right;
        FormulaHandle nnf_c = left.entries[f_k_idx];

        // Weakening: append another copy of NNF(C).
        {
            lkr::Weakening wop{};
            wop.formula = nnf_c;
            out.emplace_back(std::move(wop));
        }
        size_t f_k_dup_idx = left.append(nnf_c);

        // Outer mult-And on i_or. LEFT keeps {i_ac, f_k_idx}; RIGHT needs
        // {i_bc, f_k_dup_idx}.
        TRY_ASSIGN(outer, emit_and_split(left, i_or, {i_bc, f_k_dup_idx},
                                          neg_a, neg_b, out));

        // LEFT outer subgoal:
        //   left_phi at outer.left_phi_idx        = NNF(¬A)
        //   i_ac at outer.left_remap[i_ac]        = NNF(A) ∧ NNF(¬C)
        //   f_k_idx at outer.left_remap[f_k_idx]  = NNF(C)
        // Inner mult-And on i_ac: LEFT keeps {NNF(¬A) entry}; RIGHT needs
        // {NNF(C) entry}. After split:
        //   LEFT inner: NNF(A) (left_phi) paired with NNF(¬A) — AxiomLit.
        //   RIGHT inner: NNF(¬C) (right_theta) paired with NNF(C) — AxiomLit.
        {
            FormulaHandle ac_entry = outer.left.entries[outer.left_remap.at(i_ac)];
            if (!ac_entry.get().is_compound() ||
                ac_entry.get().as_compound().op != Op::And) {
                return MAKE_ERROR << "close_or_elim: i_ac entry is not And";
            }
            FormulaHandle nnf_a    = ac_entry.get().as_compound().left;
            FormulaHandle nnf_negc = ac_entry.get().as_compound().right;
            size_t l_i_ac  = outer.left_remap.at(i_ac);
            size_t l_f_k   = outer.left_remap.at(f_k_idx);
            size_t l_neg_a = outer.left_phi_idx;
            TRY_ASSIGN(inner, emit_and_split(outer.left, l_i_ac, {l_f_k},
                                              nnf_a, nnf_negc, out));
            size_t in_l_neg_a = inner.left_remap.at(l_neg_a);
            EmitCloseContext ecc{cc.builder};
            TRY(emit_close(ecc, inner.left, inner.left_phi_idx, in_l_neg_a, out));
            size_t in_r_f_k = inner.right_remap.at(l_f_k);
            TRY(emit_close(ecc, inner.right, inner.right_theta_idx, in_r_f_k, out));
        }

        // RIGHT outer subgoal: symmetric with B and f_k_dup.
        {
            FormulaHandle bc_entry = outer.right.entries[outer.right_remap.at(i_bc)];
            if (!bc_entry.get().is_compound() ||
                bc_entry.get().as_compound().op != Op::And) {
                return MAKE_ERROR << "close_or_elim: i_bc entry is not And";
            }
            FormulaHandle nnf_b    = bc_entry.get().as_compound().left;
            FormulaHandle nnf_negc = bc_entry.get().as_compound().right;
            size_t r_i_bc  = outer.right_remap.at(i_bc);
            size_t r_f_k_d = outer.right_remap.at(f_k_dup_idx);
            size_t r_neg_b = outer.right_theta_idx;
            TRY_ASSIGN(inner, emit_and_split(outer.right, r_i_bc, {r_f_k_d},
                                              nnf_b, nnf_negc, out));
            size_t in_l_neg_b = inner.left_remap.at(r_neg_b);
            EmitCloseContext ecc{cc.builder};
            TRY(emit_close(ecc, inner.left, inner.left_phi_idx, in_l_neg_b, out));
            size_t in_r_f_k_d = inner.right_remap.at(r_f_k_d);
            return emit_close(ecc, inner.right, inner.right_theta_idx, in_r_f_k_d, out);
        }
    }

    if (auto* op = std::get_if<nd::IffIntro>(&instr)) {
        // F_k = A ↔ B; F_k_nnf = (¬A∨B) ∧ (A∨¬B). i_ab holds NNF(A∧¬B);
        // i_ba holds NNF(B∧¬A). Mult-And on f_k_idx: LEFT needs i_ab,
        // RIGHT needs i_ba. emit_close on each — generic dual-decomp
        // (with commutativity awareness in emit_close) handles both.
        auto i_ab_it = left.step_to_neg_idx.find(op->ab.idx);
        auto i_ba_it = left.step_to_neg_idx.find(op->ba.idx);
        if (i_ab_it == left.step_to_neg_idx.end() ||
            i_ba_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_iff_intro: missing negation for operand";
        }
        size_t i_ab = i_ab_it->second;
        size_t i_ba = i_ba_it->second;
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_compound() ||
            cut_entry.get().as_compound().op != Op::And) {
            return MAKE_ERROR << "close_iff_intro: cut entry is not And";
        }
        FormulaHandle left_phi    = cut_entry.get().as_compound().left;
        FormulaHandle right_theta = cut_entry.get().as_compound().right;
        TRY_ASSIGN(split, emit_and_split(left, f_k_idx, {i_ba},
                                          left_phi, right_theta, out));
        size_t l_i_ab = split.left_remap.at(i_ab);
        EmitCloseContext ecc{cc.builder};
        TRY(emit_close(ecc, split.left, split.left_phi_idx, l_i_ab, out));
        size_t r_i_ba = split.right_remap.at(i_ba);
        return emit_close(ecc, split.right, split.right_theta_idx, r_i_ba, out);
    }

    if (auto* op = std::get_if<nd::IffElimL>(&instr)) {
        // F_k = B; i_iff holds (NNF(A)∧NNF(¬B)) ∨ (NNF(¬A)∧NNF(B));
        // i_a holds NNF(¬A). Emit Or(i_iff) → first clause stays at
        // i_iff; second clause appended (and benign — LEFT subgoal closes
        // before needing it). Then mult-And on i_iff splitting LEFT/RIGHT
        // such that LEFT pairs NNF(A) with NNF(¬A) (at i_a) and RIGHT
        // pairs NNF(¬B) with NNF(B) (at f_k_idx).
        auto i_iff_it = left.step_to_neg_idx.find(op->iff.idx);
        auto i_a_it   = left.step_to_neg_idx.find(op->a.idx);
        if (i_iff_it == left.step_to_neg_idx.end() ||
            i_a_it   == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_iff_elim_l: missing negation for operand";
        }
        size_t i_iff = i_iff_it->second;
        size_t i_a   = i_a_it->second;
        FormulaHandle iff_entry = left.entries[i_iff];
        if (!iff_entry.get().is_compound() ||
            iff_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_iff_elim_l: i_iff entry is not Or";
        }
        FormulaHandle first_clause  = iff_entry.get().as_compound().left;
        FormulaHandle second_clause = iff_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = i_iff;
            out.emplace_back(std::move(oop));
        }
        left.entries[i_iff] = first_clause;
        left.append(second_clause);
        if (!first_clause.get().is_compound() ||
            first_clause.get().as_compound().op != Op::And) {
            return MAKE_ERROR << "close_iff_elim_l: first clause is not And";
        }
        FormulaHandle nnf_a    = first_clause.get().as_compound().left;
        FormulaHandle nnf_negb = first_clause.get().as_compound().right;
        TRY_ASSIGN(split, emit_and_split(left, i_iff, {f_k_idx},
                                          nnf_a, nnf_negb, out));
        size_t l_i_a = split.left_remap.at(i_a);
        EmitCloseContext ecc{cc.builder};
        TRY(emit_close(ecc, split.left, split.left_phi_idx, l_i_a, out));
        size_t r_f_k = split.right_remap.at(f_k_idx);
        return emit_close(ecc, split.right, split.right_theta_idx, r_f_k, out);
    }

    if (auto* op = std::get_if<nd::IffElimR>(&instr)) {
        // F_k = A; i_iff as above; i_b holds NNF(¬B). After Or(i_iff),
        // the SECOND clause (NNF(¬A) ∧ NNF(B)) is the one we want — emit
        // a structural Or move, then mult-And on the second clause's idx
        // (= the appended position). Then LEFT pairs NNF(¬A) with NNF(A)
        // (at f_k_idx), RIGHT pairs NNF(B) with NNF(¬B) (at i_b).
        auto i_iff_it = left.step_to_neg_idx.find(op->iff.idx);
        auto i_b_it   = left.step_to_neg_idx.find(op->b.idx);
        if (i_iff_it == left.step_to_neg_idx.end() ||
            i_b_it   == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_iff_elim_r: missing negation for operand";
        }
        size_t i_iff = i_iff_it->second;
        size_t i_b   = i_b_it->second;
        FormulaHandle iff_entry = left.entries[i_iff];
        if (!iff_entry.get().is_compound() ||
            iff_entry.get().as_compound().op != Op::Or) {
            return MAKE_ERROR << "close_iff_elim_r: i_iff entry is not Or";
        }
        FormulaHandle first_clause  = iff_entry.get().as_compound().left;
        FormulaHandle second_clause = iff_entry.get().as_compound().right;
        {
            lkr::Or oop{};
            oop.principal = i_iff;
            out.emplace_back(std::move(oop));
        }
        left.entries[i_iff] = first_clause;
        size_t second_idx = left.append(second_clause);
        if (!second_clause.get().is_compound() ||
            second_clause.get().as_compound().op != Op::And) {
            return MAKE_ERROR << "close_iff_elim_r: second clause is not And";
        }
        FormulaHandle nnf_nega = second_clause.get().as_compound().left;
        FormulaHandle nnf_b    = second_clause.get().as_compound().right;
        TRY_ASSIGN(split, emit_and_split(left, second_idx, {i_b},
                                          nnf_nega, nnf_b, out));
        size_t l_f_k = split.left_remap.at(f_k_idx);
        EmitCloseContext ecc{cc.builder};
        TRY(emit_close(ecc, split.left, split.left_phi_idx, l_f_k, out));
        size_t r_i_b = split.right_remap.at(i_b);
        return emit_close(ecc, split.right, split.right_theta_idx, r_i_b, out);
    }

    if (auto* op = std::get_if<nd::ExistsIntro>(&instr)) {
        // F_k = ∃x.body. i_body holds NNF(¬body[x:=witness]).
        // Emit Exists(f_k_idx, witness=t_lkr); entries[f_k_idx] becomes
        // NNF(body)[x:=witness]. emit_close(f_k_idx, i_body).
        if (!op->witness.has_value()) {
            // Closing form is handled by EXISTS_ELIM block, not as a flat
            // step. Reaching it here means the block tree mis-classified.
            return MAKE_ERROR
                << "close_exists_intro: scope-closing ExistsIntro should "
                << "be the closer of an EXISTS_ELIM block";
        }
        auto i_body_it = left.step_to_neg_idx.find(op->body.idx);
        if (i_body_it == left.step_to_neg_idx.end()) {
            return MAKE_ERROR << "close_exists_intro: missing negation for body";
        }
        auto t_it = left.lkr_term_for.find(op->witness->idx);
        if (t_it == left.lkr_term_for.end()) {
            return MAKE_ERROR
                << "close_exists_intro: ND TermRef #" << op->witness->idx
                << " has no LKR mapping";
        }
        const auto& binding = t_it->second;
        FormulaHandle cut_entry = left.entries[f_k_idx];
        if (!cut_entry.get().is_quantified() ||
            cut_entry.get().as_quantified().op != Op::Exists) {
            return MAKE_ERROR
                << "close_exists_intro: cut entry is not ∃";
        }
        FormulaHandle body = cut_entry.get().as_quantified().body;
        FormulaHandle inst = cc.builder.instantiate_quantifier_body(
            body, binding.value);
        {
            lkr::Exists eop{};
            eop.principal = f_k_idx;
            eop.witness   = binding.lkr_ref;
            out.emplace_back(std::move(eop));
        }
        left.entries[f_k_idx] = inst;
        EmitCloseContext ecc{cc.builder};
        return emit_close(ecc, left, f_k_idx, i_body_it->second, out);
    }

    return MAKE_ERROR
        << "NDtoLKR: ND op at #" << nd_idx
        << " not yet handled by cut-spine driver (variant index "
        << instr.index() << ")";
}

// =========================================================================
// Cut-spine body iteration.
// =========================================================================

util::ResultStatus translate_body(
    CutSpineContext&         cc,
    const std::vector<BodyItem>& body,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out);

util::ResultStatus translate_flat(
    CutSpineContext&         cc,
    uint32_t                 nd_idx,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    const auto& instr = cc.prog.instrs[nd_idx];
    if (is_no_emit_flat(instr)) return util::Ok();

    // F_k for this step.
    if (nd_idx >= cc.trace.step_env.size() || !cc.trace.step_env[nd_idx].valid()) {
        return MAKE_ERROR
            << "NDtoLKR: trace formula missing for ND step #" << nd_idx;
    }
    FormulaHandle f_k     = cc.trace.step_env[nd_idx];
    FormulaHandle f_k_nnf = cc.builder.to_nnf(f_k);
    FormulaHandle neg_f_k_nnf = cc.builder.to_nnf_neg(f_k);

    // Emit Cut(F_k_nnf).
    {
        lkr::Cut op{};
        op.cut_formula = f_k_nnf;
        out.emplace_back(std::move(op));
    }

    // LEFT: clone shadow + append F_k_nnf. Run close_X.
    SequentShadow left = shadow;  // copy
    size_t f_k_idx = left.append(f_k_nnf);
    TRY(dispatch_close(cc, nd_idx, left, f_k_idx, out));

    // RIGHT: replace working shadow with parent + neg_f_k_nnf appended.
    size_t neg_idx = shadow.append(neg_f_k_nnf);
    shadow.step_to_neg_idx[nd_idx] = neg_idx;
    return util::Ok();
}

util::ResultStatus translate_block(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out);

util::ResultStatus translate_body(
    CutSpineContext&         cc,
    const std::vector<BodyItem>& body,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    for (const auto& item : body) {
        if (auto* fs = std::get_if<FlatStep>(&item)) {
            TRY(translate_flat(cc, fs->nd_idx, shadow, out));
        } else {
            const auto& sub_uptr =
                std::get<std::unique_ptr<Block>>(item);
            TRY(translate_block(cc, *sub_uptr, shadow, out));
        }
    }
    return util::Ok();
}

// =========================================================================
// Sub-block translation. Each kind is treated as a "block-as-flat-step":
// the parent emits Cut(F_block_nnf) where F_block is the result formula
// of the block (= trace[closer_idx]). The LEFT subgoal proves F_block via
// the block-specific opener+body+close pattern; the RIGHT subgoal carries
// NNF(¬F_block) for siblings to reference via step_to_neg_idx[closer_idx].
// =========================================================================

util::ResultStatus translate_block_body_with_close(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           left,        // LEFT subgoal of the block's Cut
    size_t                   qed_slot,    // position the body must close at
    size_t                   target_neg_origin, // not used; reserved
    std::vector<lkr::Instr>& out)
{
    (void)target_neg_origin;
    TRY(translate_body(cc, blk.body, left, out));
    // After body, the body's last "deriving step" is blk.target_idx (the
    // step whose formula equals the block's body result). Close qed_slot
    // against step_to_neg_idx[target_idx].
    auto it = left.step_to_neg_idx.find(blk.target_idx);
    if (it == left.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "translate_block: target step #" << blk.target_idx
            << " (block kind " << static_cast<int>(blk.kind)
            << ") did not produce a Cut entry";
    }
    EmitCloseContext ecc{cc.builder};
    return emit_close(ecc, left, qed_slot, it->second, out);
}

util::ResultStatus translate_block_forall(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    // F_block = ∀x.body, from trace[closer_idx].
    if (blk.closer_idx >= cc.trace.step_env.size() ||
        !cc.trace.step_env[blk.closer_idx].valid()) {
        return MAKE_ERROR
            << "translate_block_forall: missing trace for closer at #"
            << blk.closer_idx;
    }
    FormulaHandle f_block = cc.trace.step_env[blk.closer_idx];
    FormulaHandle f_block_nnf = cc.builder.to_nnf(f_block);
    FormulaHandle neg_f_block_nnf = cc.builder.to_nnf_neg(f_block);

    // Recover the ND-side fix var so LKR's Forall uses the same eigen as
    // the trace did. This makes the body's trace formulas (which reference
    // Term::fixed(fix_var)) directly usable in the LEFT shadow without
    // re-keying.
    if (blk.opener_idx >= cc.trace.term_env.size() ||
        !cc.trace.term_present[blk.opener_idx]) {
        return MAKE_ERROR
            << "translate_block_forall: missing term binding for Fix at #"
            << blk.opener_idx;
    }
    Term fix_term = cc.trace.term_env[blk.opener_idx];
    if (!fix_term.is_fixed()) {
        return MAKE_ERROR
            << "translate_block_forall: Fix at #" << blk.opener_idx
            << " did not bind a fixed-var term";
    }
    var_index fix_var = fix_term.as_variable();

    // Cut(F_block_nnf).
    {
        lkr::Cut op{};
        op.cut_formula = f_block_nnf;
        out.emplace_back(std::move(op));
    }

    // LEFT subgoal: copy + append f_block_nnf at f_block_idx.
    SequentShadow left = shadow;
    size_t f_block_idx = left.append(f_block_nnf);

    // Emit Forall on the cut entry; LEFT entries[f_block_idx] becomes
    // NNF(body)[Gen 0 := fixed(fix_var)] = NNF of the body step's trace
    // formula. Record the LKR TermRef so forall_elim / other consumers
    // can use this Fix var as an LKR witness.
    uint32_t lkr_forall_idx = static_cast<uint32_t>(out.size());
    {
        lkr::Forall op{};
        op.principal = f_block_idx;
        op.eigen     = fix_var;
        out.emplace_back(std::move(op));
    }
    const Quantified& q = f_block_nnf.get().as_quantified();
    FormulaHandle inst_body = cc.builder.instantiate_quantifier_body(
        q.body, Term::fixed(fix_var));
    left.entries[f_block_idx] = inst_body;
    left.lkr_term_for[blk.opener_idx] = SequentShadow::TermBinding{
        TermRef{lkr_forall_idx}, Term::fixed(fix_var)};

    // Body cuts and closes; qed_slot is the cut entry (now holding the
    // instantiated body NNF).
    TRY(translate_block_body_with_close(cc, blk, left, f_block_idx, 0, out));

    // RIGHT subgoal: parent + [neg_F_block_nnf]; register closer_idx → neg slot.
    size_t neg_idx = shadow.append(neg_f_block_nnf);
    shadow.step_to_neg_idx[blk.closer_idx] = neg_idx;
    return util::Ok();
}

util::ResultStatus translate_block_implies(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    if (blk.closer_idx >= cc.trace.step_env.size() ||
        !cc.trace.step_env[blk.closer_idx].valid()) {
        return MAKE_ERROR
            << "translate_block_implies: missing trace for closer at #"
            << blk.closer_idx;
    }
    FormulaHandle f_block = cc.trace.step_env[blk.closer_idx];
    FormulaHandle f_block_nnf = cc.builder.to_nnf(f_block);
    FormulaHandle neg_f_block_nnf = cc.builder.to_nnf_neg(f_block);

    // Cut(F_block_nnf).
    {
        lkr::Cut op{};
        op.cut_formula = f_block_nnf;
        out.emplace_back(std::move(op));
    }

    // LEFT subgoal: copy + cut entry at f_block_idx holding
    // NNF(A → body) = NNF(¬A) ∨ NNF(body).
    SequentShadow left = shadow;
    size_t f_block_idx = left.append(f_block_nnf);

    if (!f_block_nnf.get().is_compound() ||
        f_block_nnf.get().as_compound().op != Op::Or) {
        return MAKE_ERROR
            << "translate_block_implies: cut formula NNF is not Or (got"
            << " variant " << f_block_nnf.get().is_compound() << ")";
    }
    FormulaHandle neg_a_nnf  = f_block_nnf.get().as_compound().left;
    FormulaHandle body_nnf   = f_block_nnf.get().as_compound().right;

    // Emit Or(f_block_idx): entries[f_block_idx] := NNF(¬A); appended NNF(body).
    {
        lkr::Or op{};
        op.principal = f_block_idx;
        out.emplace_back(std::move(op));
    }
    left.entries[f_block_idx] = neg_a_nnf;
    size_t body_idx = left.append(body_nnf);

    // Register the opener (Assume) so flat-step refs to it resolve to the
    // negation entry.
    left.step_to_neg_idx[blk.opener_idx] = f_block_idx;

    TRY(translate_block_body_with_close(cc, blk, left, body_idx, 0, out));

    // RIGHT subgoal: register the closer's negation.
    size_t neg_idx = shadow.append(neg_f_block_nnf);
    shadow.step_to_neg_idx[blk.closer_idx] = neg_idx;
    return util::Ok();
}

// NOT block. NotIntro(bottom) derives ¬A where A was the assumption.
// In the LEFT subgoal of the block's Cut, NNF(¬A) is the cut formula AND
// the assumption's negation slot — they coincide. The body's last step is
// a NotElim that pairs two derived steps' negations as duals via
// emit_close.
util::ResultStatus translate_block_not(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    if (blk.closer_idx >= cc.trace.step_env.size() ||
        !cc.trace.step_env[blk.closer_idx].valid()) {
        return MAKE_ERROR
            << "translate_block_not: missing trace for closer at #"
            << blk.closer_idx;
    }
    FormulaHandle f_block = cc.trace.step_env[blk.closer_idx];
    FormulaHandle f_block_nnf = cc.builder.to_nnf(f_block);
    FormulaHandle neg_f_block_nnf = cc.builder.to_nnf_neg(f_block);

    {
        lkr::Cut op{};
        op.cut_formula = f_block_nnf;
        out.emplace_back(std::move(op));
    }
    SequentShadow left = shadow;
    size_t f_block_idx = left.append(f_block_nnf);
    // Assumption A: its negation in the LEFT shadow is NNF(¬A) = f_block_nnf
    // at f_block_idx. Body steps that reference the assumption via step_to_neg_idx
    // see the assumption's negation here.
    left.step_to_neg_idx[blk.opener_idx] = f_block_idx;

    TRY(translate_body(cc, blk.body, left, out));

    // NotIntro.bottom is a NotElim step; pair its operands' negations.
    const auto& closer_instr = cc.prog.instrs[blk.closer_idx];
    const auto& ni = std::get<nd::NotIntro>(closer_instr);
    const auto& bot_instr = cc.prog.instrs[ni.bottom.idx];
    if (!std::holds_alternative<nd::NotElim>(bot_instr)) {
        return MAKE_ERROR
            << "translate_block_not: NotIntro.bottom at #" << ni.bottom.idx
            << " is not a NotElim (got variant " << bot_instr.index() << ")";
    }
    const auto& ne = std::get<nd::NotElim>(bot_instr);
    auto i_neg_it  = left.step_to_neg_idx.find(ne.negation.idx);
    auto i_form_it = left.step_to_neg_idx.find(ne.formula.idx);
    if (i_neg_it  == left.step_to_neg_idx.end() ||
        i_form_it == left.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "translate_block_not: NotElim operand has no negation entry "
            << "(negation step=" << ne.negation.idx
            << ", formula step=" << ne.formula.idx << ")";
    }
    EmitCloseContext ecc{cc.builder};
    TRY(emit_close(ecc, left, i_neg_it->second, i_form_it->second, out));

    size_t neg_idx = shadow.append(neg_f_block_nnf);
    shadow.step_to_neg_idx[blk.closer_idx] = neg_idx;
    return util::Ok();
}

// EXISTS_ELIM block. Opener is `exists_elim h_src, w` on ∃x.φ from a
// derived step; closer is `exists_intro h_body` (no witness). The block's
// result is the re-existed body — typically ∃y.body[w→y], but if body
// doesn't reference w it's just body unchanged.
//
// Strategy (per design §4.5, adapted for block-as-cut):
//   1. Cut(F_block_nnf).
//   2. LEFT subgoal has F_block_nnf at f_block_idx, AND
//      shadow.step_to_neg_idx[h_src.idx] = neg_exists_idx (from h_src's
//      earlier flat-step cut) holding ∀x.NNF(¬φ).
//   3. Emit Forall on neg_exists_idx with eigen v (= ND's ExistsElim
//      witness var). Sequent entries[neg_exists_idx] becomes NNF(¬φ)[v].
//      Set step_to_neg_idx[ee_opener_idx] = neg_exists_idx so body
//      references work, and lkr_term_for[ee_opener_idx] = the Forall's
//      TermRef so body's exists_intro-with-witness handlers can use v.
//   4. Recurse body.
//   5. After body: emit_close(f_block_idx, step_to_neg_idx[block.target_idx]).
util::ResultStatus translate_block_exists_elim(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    if (blk.closer_idx >= cc.trace.step_env.size() ||
        !cc.trace.step_env[blk.closer_idx].valid()) {
        return MAKE_ERROR
            << "translate_block_exists_elim: missing trace for closer at #"
            << blk.closer_idx;
    }
    FormulaHandle f_block = cc.trace.step_env[blk.closer_idx];
    FormulaHandle f_block_nnf = cc.builder.to_nnf(f_block);
    FormulaHandle neg_f_block_nnf = cc.builder.to_nnf_neg(f_block);

    // The ND ExistsElim opener.
    const auto& opener_instr = cc.prog.instrs[blk.opener_idx];
    const auto& ee = std::get<nd::ExistsElim>(opener_instr);

    if (blk.opener_idx >= cc.trace.term_env.size() ||
        !cc.trace.term_present[blk.opener_idx]) {
        return MAKE_ERROR
            << "translate_block_exists_elim: ExistsElim at #"
            << blk.opener_idx << " did not bind a term";
    }
    Term v_term = cc.trace.term_env[blk.opener_idx];
    if (!v_term.is_fixed()) {
        return MAKE_ERROR
            << "translate_block_exists_elim: ExistsElim's witness is not fixed-var";
    }
    var_index v = v_term.as_variable();

    {
        lkr::Cut op{};
        op.cut_formula = f_block_nnf;
        out.emplace_back(std::move(op));
    }
    SequentShadow left = shadow;
    size_t f_block_idx = left.append(f_block_nnf);

    // Locate neg_exists_idx (where the source ∃x.φ's negation = ∀x.NNF(¬φ)
    // sits in the LEFT shadow — copied from parent at the time of the
    // earlier cut for ee.formula).
    auto neg_it = left.step_to_neg_idx.find(ee.formula.idx);
    if (neg_it == left.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "translate_block_exists_elim: source step #" << ee.formula.idx
            << " has no negation entry (must be cut earlier in the spine)";
    }
    size_t neg_exists_idx = neg_it->second;
    FormulaHandle neg_entry = left.entries[neg_exists_idx];
    if (!neg_entry.get().is_quantified() ||
        neg_entry.get().as_quantified().op != Op::Forall) {
        return MAKE_ERROR
            << "translate_block_exists_elim: negation entry at #"
            << neg_exists_idx << " is not ∀ (got " << neg_entry.get() << ")";
    }

    // Emit Forall on the negation entry; binds v as the LKR eigen.
    uint32_t lkr_forall_idx = static_cast<uint32_t>(out.size());
    {
        lkr::Forall op{};
        op.principal = neg_exists_idx;
        op.eigen     = v;
        out.emplace_back(std::move(op));
    }
    FormulaHandle inst_body = cc.builder.instantiate_quantifier_body(
        neg_entry.get().as_quantified().body, Term::fixed(v));
    left.entries[neg_exists_idx] = inst_body;

    // Body refs to the opener (e.g., as the source step for further work)
    // see NNF(¬φ)[v] as its "negation" — same slot.
    left.step_to_neg_idx[blk.opener_idx] = neg_exists_idx;
    left.lkr_term_for[blk.opener_idx] = SequentShadow::TermBinding{
        TermRef{lkr_forall_idx}, Term::fixed(v)};

    TRY(translate_body(cc, blk.body, left, out));

    // Close: f_block_idx (= F_block_nnf) vs step_to_neg_idx[block.target].
    auto tgt_it = left.step_to_neg_idx.find(blk.target_idx);
    if (tgt_it == left.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "translate_block_exists_elim: target step #" << blk.target_idx
            << " did not produce a Cut entry";
    }
    EmitCloseContext ecc{cc.builder};
    TRY(emit_close(ecc, left, f_block_idx, tgt_it->second, out));

    size_t neg_idx = shadow.append(neg_f_block_nnf);
    shadow.step_to_neg_idx[blk.closer_idx] = neg_idx;
    return util::Ok();
}

util::ResultStatus translate_block(
    CutSpineContext&         cc,
    const Block&             blk,
    SequentShadow&           shadow,
    std::vector<lkr::Instr>& out)
{
    switch (blk.kind) {
        case BlockKind::FORALL:
            return translate_block_forall(cc, blk, shadow, out);
        case BlockKind::IMPLIES:
            return translate_block_implies(cc, blk, shadow, out);
        case BlockKind::NOT_:
            return translate_block_not(cc, blk, shadow, out);
        case BlockKind::EXISTS_ELIM:
            return translate_block_exists_elim(cc, blk, shadow, out);
        case BlockKind::OUTER:
            return MAKE_ERROR
                << "translate_block: OUTER should be handled by translate_outer";
    }
    return MAKE_ERROR << "translate_block: unknown block kind";
}

}  // namespace

util::Result<std::vector<lkr::Instr>> translate_outer(
    CutSpineContext&    cc,
    const Block&        outer,
    FormulaHandle       goal_nnf)
{
    if (outer.kind != BlockKind::OUTER) {
        return MAKE_ERROR
            << "translate_outer: block is not OUTER";
    }
    if (outer.target_idx == kInvalidIdx ||
        outer.target_idx >= cc.prog.instrs.size())
    {
        return MAKE_ERROR
            << "translate_outer: OUTER has invalid target_idx";
    }

    std::vector<lkr::Instr> out;
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);
    size_t qed_slot = 0;

    TRY(translate_body(cc, outer.body, shadow, out));

    // After the body, the cut-spine has accumulated all body steps' ¬F_k
    // entries. The qed step's derivation is `outer.target_idx`; close
    // by dual-decomposing qed_slot vs step_to_neg_idx[target].
    auto it = shadow.step_to_neg_idx.find(outer.target_idx);
    if (it == shadow.step_to_neg_idx.end()) {
        return MAKE_ERROR
            << "translate_outer: target step #" << outer.target_idx
            << " did not produce a Cut entry (likely a no-emit step "
            << "was used as Qed.derived, which is unsupported)";
    }
    EmitCloseContext ecc{cc.builder};
    TRY(emit_close(ecc, shadow, qed_slot, it->second, out));

    return out;
}

}  // namespace logic::proof::translate::nd_to_lkr
