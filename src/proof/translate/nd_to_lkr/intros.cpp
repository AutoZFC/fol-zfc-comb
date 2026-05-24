#include "intros.h"

#include "emit_close.h"

#include "src/proof/ir.h"

#include <utility>

namespace logic::proof::translate::nd_to_lkr::intros {

namespace {

// Helper: extract the left/right children of a binary Compound entry.
// Returns Error with `op_label` in the message if the principal isn't
// a Compound of `expected_op`.
struct BinChildren {
    FormulaHandle left;
    FormulaHandle right;
};

util::Result<BinChildren> require_compound(
    FormulaHandle h, Op expected_op, const char* op_label)
{
    if (!h.get().is_compound() ||
        h.get().as_compound().op != expected_op) {
        return MAKE_ERROR
            << op_label << ": principal is not the expected compound";
    }
    return BinChildren{h.get().as_compound().left,
                       h.get().as_compound().right};
}

util::Result<FormulaHandle> require_quantified(
    FormulaHandle h, Op expected_op, const char* op_label)
{
    if (!h.get().is_quantified() ||
        h.get().as_quantified().op != expected_op) {
        return MAKE_ERROR
            << op_label << ": principal is not the expected quantifier";
    }
    return h.get().as_quantified().body;
}

// Helper: assert demand is DemandNone for an emitter that doesn't
// accept demand-aware short-circuits.
util::ResultStatus require_demand_none(const Demand& demand, const char* op_label) {
    if (!std::holds_alternative<DemandNone>(demand)) {
        return MAKE_ERROR
            << op_label << ": unsupported non-NONE demand (variant index "
            << demand.index() << ") — translator routing bug";
    }
    return util::Ok();
}

}  // namespace

// =========================================================================
// OrIntroL — single Or rule. Premise position = f_k_idx (the left disjunct
// after Or replaces principal in place).
// =========================================================================
util::Result<IntroResult> emit_or_intro_l(
    Ctx&                     /*cc*/,
    const nd::OrIntroL&      op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    TRY(require_demand_none(demand, "emit_or_intro_l"));
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_or_intro_l: f_k_idx out of range";
    }
    auto kids = require_compound(shadow.entries[f_k_idx], Op::Or,
                                 "emit_or_intro_l");
    if (!kids.ok()) return kids.error();

    out.emplace_back(lkr::Or{{}, f_k_idx});

    SequentShadow post = shadow;  // copy
    post.entries[f_k_idx] = kids.value().left;
    post.entries.push_back(kids.value().right);
    return IntroResult{OnePremise{std::move(post), f_k_idx, op.a}};
}

// =========================================================================
// OrIntroR — single Or rule. Premise position = end (the right disjunct
// after Or appends it).
// =========================================================================
util::Result<IntroResult> emit_or_intro_r(
    Ctx&                     /*cc*/,
    const nd::OrIntroR&      op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    TRY(require_demand_none(demand, "emit_or_intro_r"));
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_or_intro_r: f_k_idx out of range";
    }
    auto kids = require_compound(shadow.entries[f_k_idx], Op::Or,
                                 "emit_or_intro_r");
    if (!kids.ok()) return kids.error();

    out.emplace_back(lkr::Or{{}, f_k_idx});

    SequentShadow post = shadow;
    post.entries[f_k_idx] = kids.value().left;
    post.entries.push_back(kids.value().right);
    size_t end_idx = post.entries.size() - 1;
    return IntroResult{OnePremise{std::move(post), end_idx, op.b}};
}

// =========================================================================
// ImpliesIntro — NNF(A→B) = NNF(¬A) ∨ NNF(B). Same Or rule as OrIntroR;
// premise position = the B (at end). The NNF(¬A) at f_k_idx is the
// assumption's dual — references to the assumption close against it.
// =========================================================================
util::Result<IntroResult> emit_implies_intro(
    Ctx&                     /*cc*/,
    const nd::ImpliesIntro&  op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    TRY(require_demand_none(demand, "emit_implies_intro"));
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_implies_intro: f_k_idx out of range";
    }
    auto kids = require_compound(shadow.entries[f_k_idx], Op::Or,
                                 "emit_implies_intro");
    if (!kids.ok()) return kids.error();

    out.emplace_back(lkr::Or{{}, f_k_idx});

    SequentShadow post = shadow;
    post.entries[f_k_idx] = kids.value().left;   // NNF(¬A)
    post.entries.push_back(kids.value().right);  // NNF(B)
    size_t end_idx = post.entries.size() - 1;
    return IntroResult{OnePremise{std::move(post), end_idx, op.conclusion}};
}

// =========================================================================
// ForallIntro — single Forall rule. Premise position = f_k_idx
// (body[x:=Term::fixed(eigen)] in place).
// =========================================================================
util::Result<IntroResult> emit_forall_intro(
    Ctx&                     cc,
    const nd::ForallIntro&   op,
    var_index                eigen,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_forall_intro: f_k_idx out of range";
    }

    // Demand-aware INSTANCE(t): substitute eigen→t in the body instead
    // of emitting Forall. shadow.entries[f_k_idx] already holds
    // NNF(φ[x:=t]) (the consumer placed it there). The body's
    // recursion uses the substituted formula at f_k_idx; any TermRef
    // references to this Fix's eigen resolve to t via the dispatcher's
    // post-emit lkr_term_for binding (caller handles).
    if (std::holds_alternative<DemandInstance>(demand)) {
        // No LKR ops emitted. Return premise pointing at op.body.
        return IntroResult{OnePremise{shadow, f_k_idx, op.body}};
    }
    TRY(require_demand_none(demand, "emit_forall_intro"));

    auto body = require_quantified(shadow.entries[f_k_idx], Op::Forall,
                                   "emit_forall_intro");
    if (!body.ok()) return body.error();

    out.emplace_back(lkr::Forall{{}, f_k_idx, eigen});

    SequentShadow post = shadow;
    Term fixed_term = Term::fixed(eigen);
    post.entries[f_k_idx] =
        cc.builder.instantiate_quantifier_body(body.value(), fixed_term);
    return IntroResult{OnePremise{std::move(post), f_k_idx, op.body}};
}

// =========================================================================
// ExistsIntro (witness form) — single Exists rule. The witness's LKR
// TermRef comes from shadow.lkr_term_for[t.idx].
// =========================================================================
util::Result<IntroResult> emit_exists_intro(
    Ctx&                     cc,
    const nd::ExistsIntro&   op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    TRY(require_demand_none(demand, "emit_exists_intro"));
    if (!op.witness.has_value()) {
        return MAKE_ERROR
            << "emit_exists_intro: no-witness form is Phase 4 (EXISTS_ELIM closer)";
    }
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_exists_intro: f_k_idx out of range";
    }
    auto body = require_quantified(shadow.entries[f_k_idx], Op::Exists,
                                   "emit_exists_intro");
    if (!body.ok()) return body.error();

    auto t_it = shadow.lkr_term_for.find(op.witness->idx);
    if (t_it == shadow.lkr_term_for.end()) {
        return MAKE_ERROR
            << "emit_exists_intro: ND TermRef #" << op.witness->idx
            << " has no LKR mapping in shadow";
    }
    const auto& binding = t_it->second;

    out.emplace_back(lkr::Exists{{}, f_k_idx, binding.lkr_ref});

    SequentShadow post = shadow;
    post.entries[f_k_idx] =
        cc.builder.instantiate_quantifier_body(body.value(), binding.value);
    return IntroResult{OnePremise{std::move(post), f_k_idx, op.body}};
}

// =========================================================================
// AndIntro — multiplicative ∧R with full-context duplication.
//
//   Initial shadow: [γ_0, ..., γ_{n-1}, A∧B at f_k_idx, γ_n, ...].
//   Step 1: for each non-principal entry γ_i, emit Weakening{γ_i}.
//           After: |Γ|-many entries appended (duplicate copies of Γ).
//   Step 2: emit And{principal=f_k_idx, right_needs=[dup indices]}.
//           LEFT  = original non-principal entries + A.
//           RIGHT = duplicated non-principal entries + B.
//
// Returns TwoPremise with each subgoal's shadow + per-premise position
// (= the A or B position at the end of each subgoal).
// =========================================================================
util::Result<IntroResult> emit_and_intro(
    Ctx&                     /*cc*/,
    const nd::AndIntro&      op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_and_intro: f_k_idx out of range";
    }

    // Demand-aware short-circuits: AND_LEFT or AND_RIGHT route the
    // recursion to op.a or op.b respectively, with no LKR emission.
    // The shadow is unchanged (caller's f_k_idx already holds the
    // demanded sub-formula's NNF — the AndIntro's contribution to the
    // LK proof is absorbed into the routed premise's translation).
    if (std::holds_alternative<DemandAndLeft>(demand)) {
        return IntroResult{OnePremise{shadow, f_k_idx, op.a}};
    }
    if (std::holds_alternative<DemandAndRight>(demand)) {
        return IntroResult{OnePremise{shadow, f_k_idx, op.b}};
    }
    TRY(require_demand_none(demand, "emit_and_intro"));

    auto kids = require_compound(shadow.entries[f_k_idx], Op::And,
                                 "emit_and_intro");
    if (!kids.ok()) return kids.error();
    FormulaHandle phi   = kids.value().left;   // A
    FormulaHandle theta = kids.value().right;  // B

    // Build the "post-Weakening" shadow representing the parent after
    // emit-time. The Weakenings append duplicate copies of every
    // non-principal entry.
    SequentShadow weakened = shadow;
    const size_t original_size = shadow.entries.size();
    std::vector<size_t> right_needs;
    right_needs.reserve(original_size - 1);
    for (size_t i = 0; i < original_size; ++i) {
        if (i == f_k_idx) continue;
        const FormulaHandle dup = shadow.entries[i];
        out.emplace_back(lkr::Weakening{{}, dup});
        right_needs.push_back(weakened.entries.size());
        weakened.entries.push_back(dup);
    }

    // Emit the And. right_needs go to RIGHT; everything else
    // (non-principal, non-right_needs) goes to LEFT.
    out.emplace_back(lkr::And{{}, f_k_idx, right_needs});

    // Compute LEFT and RIGHT shadows by mirroring emit_and_split's
    // semantics (sorted left partition; principal consumed).
    SequentShadow left_post;
    left_post.lkr_term_for    = shadow.lkr_term_for;
    left_post.step_to_neg_idx = shadow.step_to_neg_idx;
    SequentShadow right_post;
    right_post.lkr_term_for    = shadow.lkr_term_for;
    right_post.step_to_neg_idx = shadow.step_to_neg_idx;

    // Build a quick lookup for right_needs.
    std::vector<bool> in_right(weakened.entries.size(), false);
    for (size_t i : right_needs) in_right[i] = true;

    // LEFT: indices that are non-principal and NOT in right_needs.
    // emit_and_split sorts left_partition; we iterate in index order.
    for (size_t i = 0; i < weakened.entries.size(); ++i) {
        if (i == f_k_idx) continue;
        if (in_right[i]) continue;
        left_post.entries.push_back(weakened.entries[i]);
    }
    size_t left_pos = left_post.entries.size();
    left_post.entries.push_back(phi);

    // RIGHT: indices in right_needs.
    for (size_t i : right_needs) {
        right_post.entries.push_back(weakened.entries[i]);
    }
    size_t right_pos = right_post.entries.size();
    right_post.entries.push_back(theta);

    return IntroResult{TwoPremise{std::move(left_post), std::move(right_post),
                                   left_pos, right_pos, op.a, op.b}};
}

// =========================================================================
// IffIntro — NNF(A↔B) = (NNF(¬A)∨NNF(B)) ∧ (NNF(A)∨NNF(¬B)). Structurally
// identical to AndIntro at the LKR level — both decompose a top-level And
// via multiplicative ∧R with full-context duplication. Returns TwoPremise
// with each branch's premise_pos pointing at the Or-shaped conjunct (the
// dispatcher's recursion on ab/ba — typically ImpliesIntro emitters — then
// emits Or on each side).
//
// LEFT subgoal: [Γ_left..., NNF(A→B)]. Premise position = the Or-shaped
//               first conjunct.
// RIGHT subgoal: [Γ_right..., NNF(B→A)]. Premise position = the Or-shaped
//               second conjunct.
//
// Type-check: validates the principal is And and both conjuncts are Or
// (the canonical NNF(A↔B) shape). Other shapes indicate the caller passed
// a non-Iff principal — a translator bug.
// =========================================================================
util::Result<IntroResult> emit_iff_intro(
    Ctx&                     /*cc*/,
    const nd::IffIntro&      op,
    const SequentShadow&     shadow,
    size_t                   f_k_idx,
    std::vector<lkr::Instr>& out,
    Demand                   demand)
{
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_iff_intro: f_k_idx out of range";
    }

    // Demand-aware short-circuits: IFF_LEFT → recurse on op.ab (forward
    // direction A→B); IFF_RIGHT → recurse on op.ba (reverse B→A). No
    // LKR emission.
    if (std::holds_alternative<DemandIffLeft>(demand)) {
        return IntroResult{OnePremise{shadow, f_k_idx, op.ab}};
    }
    if (std::holds_alternative<DemandIffRight>(demand)) {
        return IntroResult{OnePremise{shadow, f_k_idx, op.ba}};
    }
    TRY(require_demand_none(demand, "emit_iff_intro"));

    auto outer = require_compound(shadow.entries[f_k_idx], Op::And,
                                  "emit_iff_intro");
    if (!outer.ok()) return outer.error();
    auto left_or  = require_compound(outer.value().left,  Op::Or,
                                     "emit_iff_intro (left conjunct)");
    if (!left_or.ok()) return left_or.error();
    auto right_or = require_compound(outer.value().right, Op::Or,
                                     "emit_iff_intro (right conjunct)");
    if (!right_or.ok()) return right_or.error();

    const FormulaHandle phi   = outer.value().left;   // NNF(A→B) = ¬A ∨ B
    const FormulaHandle theta = outer.value().right;  // NNF(B→A) = A ∨ ¬B

    // Step 1: Weakening duplication, identical to AndIntro.
    SequentShadow weakened = shadow;
    const size_t original_size = shadow.entries.size();
    std::vector<size_t> right_needs;
    right_needs.reserve(original_size - 1);
    for (size_t i = 0; i < original_size; ++i) {
        if (i == f_k_idx) continue;
        const FormulaHandle dup = shadow.entries[i];
        out.emplace_back(lkr::Weakening{{}, dup});
        right_needs.push_back(weakened.entries.size());
        weakened.entries.push_back(dup);
    }

    // Step 2: And split.
    out.emplace_back(lkr::And{{}, f_k_idx, right_needs});

    // Step 3: per-branch shadows. Each branch's premise position points
    // at the Or-shaped conjunct; the dispatcher's recursion emits Or
    // there.
    SequentShadow left_post;
    left_post.lkr_term_for    = shadow.lkr_term_for;
    left_post.step_to_neg_idx = shadow.step_to_neg_idx;
    SequentShadow right_post;
    right_post.lkr_term_for    = shadow.lkr_term_for;
    right_post.step_to_neg_idx = shadow.step_to_neg_idx;

    std::vector<bool> in_right(weakened.entries.size(), false);
    for (size_t i : right_needs) in_right[i] = true;

    for (size_t i = 0; i < weakened.entries.size(); ++i) {
        if (i == f_k_idx) continue;
        if (in_right[i]) continue;
        left_post.entries.push_back(weakened.entries[i]);
    }
    size_t left_phi_idx = left_post.entries.size();
    left_post.entries.push_back(phi);

    for (size_t i : right_needs) {
        right_post.entries.push_back(weakened.entries[i]);
    }
    size_t right_theta_idx = right_post.entries.size();
    right_post.entries.push_back(theta);

    return IntroResult{TwoPremise{std::move(left_post), std::move(right_post),
                                   left_phi_idx, right_theta_idx,
                                   op.ab, op.ba}};
}

// =========================================================================
// ExcludedMiddle — Or + emit_close.
//   Initial: shadow.entries[f_k_idx] = NNF(A) ∨ NNF(¬A).
//   After Or: NNF(A) at f_k_idx, NNF(¬A) at end. They're NNF-dual by
//   construction, so emit_close discharges via AxiomLit (atomic) or
//   structural recursion (compound). Returns ZeroPremise.
// =========================================================================
util::Result<IntroResult> emit_excluded_middle(
    Ctx&                       cc,
    const nd::ExcludedMiddle&  /*op*/,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand)
{
    TRY(require_demand_none(demand, "emit_excluded_middle"));
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_excluded_middle: f_k_idx out of range";
    }
    auto kids = require_compound(shadow.entries[f_k_idx], Op::Or,
                                 "emit_excluded_middle");
    if (!kids.ok()) return kids.error();

    out.emplace_back(lkr::Or{{}, f_k_idx});

    SequentShadow work = shadow;
    work.entries[f_k_idx] = kids.value().left;
    size_t neg_idx = work.entries.size();
    work.entries.push_back(kids.value().right);

    EmitCloseContext ecc{cc.builder};
    auto cr = emit_close(ecc, work, f_k_idx, neg_idx, out);
    if (!cr.ok()) {
        return MAKE_ERROR
            << "emit_excluded_middle: emit_close failed: "
            << cr.error().to_string();
    }
    return IntroResult{ZeroPremise{}};
}

// =========================================================================
// Peirce — fixed cut-free skeleton.
//   NNF(((A→B)→A)→A) = ((NNF(¬A) ∨ NNF(B)) ∧ NNF(¬A)) ∨ NNF(A).
//   Skeleton:
//     Or{f_k_idx}        : conjunct at f_k_idx, A appended.
//     Weakening{A}       : another A appended.
//     And{f_k_idx, ...}  : split conjunct; LEFT gets first A, RIGHT gets
//                          second A.
//     LEFT:  [A, NNF(¬A)∨NNF(B)]. Or → [A, NNF(¬A), NNF(B)].
//            emit_close on (0, 1).
//     RIGHT: [A, NNF(¬A)]. emit_close on (0, 1).
//   Returns ZeroPremise.
//
// Precondition: shadow.entries has ONLY the principal at f_k_idx
// (no surrounding context — Peirce is a closed tautology). This holds
// when Peirce is the root of a sub-derivation; the dispatcher arranges
// the call site appropriately.
// =========================================================================
util::Result<IntroResult> emit_peirce(
    Ctx&                       cc,
    const nd::Peirce&          /*op*/,
    const SequentShadow&       shadow,
    size_t                     f_k_idx,
    std::vector<lkr::Instr>&   out,
    Demand                     demand)
{
    TRY(require_demand_none(demand, "emit_peirce"));
    if (f_k_idx >= shadow.entries.size()) {
        return MAKE_ERROR << "emit_peirce: f_k_idx out of range";
    }
    if (shadow.entries.size() != 1 || f_k_idx != 0) {
        return MAKE_ERROR
            << "emit_peirce: requires isolated sequent with single principal "
               "at index 0 (got "
            << shadow.entries.size() << " entries, principal at "
            << f_k_idx << ")";
    }

    // outer = ((¬A ∨ B) ∧ ¬A) ∨ A
    auto outer = require_compound(shadow.entries[f_k_idx], Op::Or,
                                  "emit_peirce");
    if (!outer.ok()) return outer.error();
    // outer.left = (¬A ∨ B) ∧ ¬A;  outer.right = A
    auto conj = require_compound(outer.value().left, Op::And,
                                 "emit_peirce (left disjunct)");
    if (!conj.ok()) return conj.error();
    auto disj = require_compound(conj.value().left, Op::Or,
                                 "emit_peirce (left conjunct)");
    if (!disj.ok()) return disj.error();

    const FormulaHandle a_nnf      = outer.value().right;   // NNF(A)
    const FormulaHandle conj_left  = conj.value().left;     // ¬A ∨ B
    const FormulaHandle conj_right = conj.value().right;    // ¬A
    const FormulaHandle disj_left  = disj.value().left;     // ¬A
    const FormulaHandle disj_right = disj.value().right;    // B
    (void)disj_right;  // unused — B vanishes after the Or under LEFT

    // Step 1: Or on the outer disjunction.
    out.emplace_back(lkr::Or{{}, f_k_idx});
    SequentShadow work = shadow;
    work.entries[f_k_idx] = outer.value().left;     // conjunct
    work.entries.push_back(a_nnf);                  // A (first copy)

    // Step 2: Weakening{A}.
    out.emplace_back(lkr::Weakening{{}, a_nnf});
    size_t a2_idx = work.entries.size();
    work.entries.push_back(a_nnf);                  // A (second copy)

    // Step 3: And on the conjunct. right_needs = [a2_idx].
    std::vector<size_t> right_needs = {a2_idx};
    out.emplace_back(lkr::And{{}, f_k_idx, right_needs});

    // LEFT subgoal: [a1_idx's value, conj_left] = [A, ¬A ∨ B].
    SequentShadow left_work;
    left_work.entries.push_back(a_nnf);             // A
    size_t left_or_idx = left_work.entries.size();
    left_work.entries.push_back(conj_left);         // ¬A ∨ B

    // LEFT step 4: Or on (¬A ∨ B).
    out.emplace_back(lkr::Or{{}, left_or_idx});
    left_work.entries[left_or_idx] = disj_left;     // ¬A
    left_work.entries.push_back(disj_right);        // B

    // LEFT step 5: emit_close on (0, left_or_idx) — A vs ¬A.
    {
        EmitCloseContext ecc{cc.builder};
        auto cr = emit_close(ecc, left_work, 0, left_or_idx, out);
        if (!cr.ok()) {
            return MAKE_ERROR
                << "emit_peirce: LEFT emit_close failed: "
                << cr.error().to_string();
        }
    }

    // RIGHT subgoal: [a2_idx's value, conj_right] = [A, ¬A].
    SequentShadow right_work;
    right_work.entries.push_back(a_nnf);            // A
    right_work.entries.push_back(conj_right);       // ¬A

    // RIGHT step 6: emit_close on (0, 1).
    {
        EmitCloseContext ecc{cc.builder};
        auto cr = emit_close(ecc, right_work, 0, 1, out);
        if (!cr.ok()) {
            return MAKE_ERROR
                << "emit_peirce: RIGHT emit_close failed: "
                << cr.error().to_string();
        }
    }

    return IntroResult{ZeroPremise{}};
}

}  // namespace logic::proof::translate::nd_to_lkr::intros
