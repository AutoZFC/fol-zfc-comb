#include "emit_close.h"

#include "src/proof/ir.h"

#include <algorithm>

namespace logic::proof::translate::nd_to_lkr {

namespace {

bool is_atomic_literal(FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_predicate() || f.is_schema_var()) return true;
    if (f.is_compound() && f.as_compound().op == Op::Not) {
        FormulaHandle inner = f.as_compound().left;
        return inner.get().is_predicate() || inner.get().is_schema_var();
    }
    return false;
}

bool is_top_literal(FormulaHandle h) {
    const Formula& f = h.get();
    if (!f.is_compound() || f.as_compound().op != Op::Not) return false;
    FormulaHandle inner = f.as_compound().left;
    return inner.valid() && inner.get().is_compound() &&
           inner.get().as_compound().op == Op::Bottom;
}

bool is_or(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Or;
}

bool is_and(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::And;
}

bool is_forall(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_quantified() && f.as_quantified().op == Op::Forall;
}

bool is_exists(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_quantified() && f.as_quantified().op == Op::Exists;
}

}  // namespace

util::ResultStatus emit_close(
    EmitCloseContext&         cc,
    SequentShadow&            shadow,
    size_t                    pos_a,
    size_t                    pos_b,
    std::vector<lkr::Instr>&  out)
{
    if (pos_a >= shadow.entries.size() || pos_b >= shadow.entries.size()) {
        return MAKE_ERROR
            << "emit_close: out-of-range positions (a=" << pos_a
            << ", b=" << pos_b << ", size=" << shadow.entries.size() << ")";
    }
    if (pos_a == pos_b) {
        return MAKE_ERROR
            << "emit_close: pos_a == pos_b (" << pos_a
            << ") — a formula is never its own dual";
    }

    FormulaHandle a = shadow.entries[pos_a];
    FormulaHandle b = shadow.entries[pos_b];

    // -- Top literal closes via Hughes §11 `One` regardless of the other side.
    if (is_top_literal(a)) {
        lkr::One op{};
        op.idx = pos_a;
        out.emplace_back(std::move(op));
        return util::Ok();
    }
    if (is_top_literal(b)) {
        lkr::One op{};
        op.idx = pos_b;
        out.emplace_back(std::move(op));
        return util::Ok();
    }

    // -- Atomic literals close via AxiomLit. LKR verifier confirms duality.
    if (is_atomic_literal(a) && is_atomic_literal(b)) {
        lkr::AxiomLit op{};
        op.lit_a = pos_a;
        op.lit_b = pos_b;
        out.emplace_back(std::move(op));
        return util::Ok();
    }

    // -- Normalise so OR/FORALL is on side a, AND/EXISTS on side b.
    //    By the precondition (a ⊥ b), exactly one of {Or, And} or
    //    {Forall, Exists} pairs applies. Swap only if b is the dual
    //    shape — otherwise (And, And) / (Exists, Exists) would loop.
    if ((is_and(a) && is_or(b)) ||
        (is_exists(a) && is_forall(b))) {
        return emit_close(cc, shadow, pos_b, pos_a, out);
    }

    if (is_or(a)) {
        if (!is_and(b)) {
            return MAKE_ERROR
                << "emit_close: a is ∨ but b is not ∧ (precondition violation)";
        }
        // a = φ ∨ ψ. b = β1 ∧ β2 where {β1, β2} ⊃ {NNF(¬φ), NNF(¬ψ)} —
        // possibly in either order, since NNF preserves ∧/∨ but not their
        // commutativity. Detect alignment so the partition routes each
        // subgoal to a genuinely-dual pair.
        FormulaHandle phi    = a.get().as_compound().left;
        FormulaHandle psi    = a.get().as_compound().right;
        FormulaHandle b1     = b.get().as_compound().left;   // → LEFT subgoal (b's left_phi)
        FormulaHandle b2     = b.get().as_compound().right;  // → RIGHT subgoal (b's right_theta)
        FormulaHandle neg_phi = cc.builder.to_nnf_neg(phi);
        FormulaHandle neg_psi = cc.builder.to_nnf_neg(psi);

        bool straight = (neg_phi == b1) && (neg_psi == b2);
        bool swapped  = (neg_phi == b2) && (neg_psi == b1);
        if (!straight && !swapped) {
            return MAKE_ERROR
                << "emit_close: ∨/∧ children not dual under either alignment"
                << " (NNF commutativity mismatch)";
        }

        // Or(pos_a): entries[pos_a] := φ; ψ appended at psi_idx.
        {
            lkr::Or op{};
            op.principal = pos_a;
            out.emplace_back(std::move(op));
        }
        shadow.entries[pos_a] = phi;
        size_t psi_idx = shadow.append(psi);

        // Decide which of (pos_a, psi_idx) routes to which subgoal so the
        // recursion sees a structurally dual pair.
        //   LEFT  subgoal gets b1 as left_phi at the appended position.
        //   RIGHT subgoal gets b2 as right_theta at the appended position.
        size_t left_pair_entry  = straight ? pos_a   : psi_idx;
        size_t right_pair_entry = straight ? psi_idx : pos_a;

        // Mult-And on pos_b. Partition: left_partition = everything except
        // pos_b (principal) and right_pair_entry (which routes to RIGHT).
        std::vector<size_t> left_partition;
        left_partition.reserve(shadow.entries.size());
        for (size_t k = 0; k < shadow.entries.size(); ++k) {
            if (k == pos_b) continue;
            if (k == right_pair_entry) continue;
            left_partition.push_back(k);
        }
        {
            lkr::And op{};
            op.principal = pos_b;
            op.left_partition = left_partition;
            out.emplace_back(std::move(op));
        }

        // LEFT shadow: sorted left_partition entries + b1 appended.
        SequentShadow left_shadow;
        left_shadow.lkr_term_for    = shadow.lkr_term_for;
        left_shadow.step_to_neg_idx = shadow.step_to_neg_idx;
        std::vector<size_t> sorted_left = left_partition;
        std::sort(sorted_left.begin(), sorted_left.end());
        size_t left_pair_new = static_cast<size_t>(-1);
        for (size_t i : sorted_left) {
            if (i == left_pair_entry) left_pair_new = left_shadow.entries.size();
            left_shadow.entries.push_back(shadow.entries[i]);
        }
        size_t left_b1_idx = left_shadow.append(b1);
        TRY(emit_close(cc, left_shadow, left_pair_new, left_b1_idx, out));

        // RIGHT shadow: everything not in left_partition (and not pos_b),
        // including right_pair_entry; b2 appended.
        SequentShadow right_shadow;
        right_shadow.lkr_term_for    = shadow.lkr_term_for;
        right_shadow.step_to_neg_idx = shadow.step_to_neg_idx;
        std::vector<bool> in_left(shadow.entries.size(), false);
        for (size_t i : left_partition) in_left[i] = true;
        size_t right_pair_new = static_cast<size_t>(-1);
        for (size_t i = 0; i < shadow.entries.size(); ++i) {
            if (i == pos_b) continue;
            if (in_left[i]) continue;
            if (i == right_pair_entry) right_pair_new = right_shadow.entries.size();
            right_shadow.entries.push_back(shadow.entries[i]);
        }
        size_t right_b2_idx = right_shadow.append(b2);
        return emit_close(cc, right_shadow, right_pair_new, right_b2_idx, out);
    }

    if (is_forall(a)) {
        if (!is_exists(b)) {
            return MAKE_ERROR
                << "emit_close: a is ∀ but b is not ∃ (precondition violation)";
        }
        // Allocate a fresh eigen for the Forall side.
        var_index v = cc.builder.enter_scope();

        // Forall(pos_a, eigen=v): shadow.entries[pos_a] := body[Gen(0):=fixed(v)]
        FormulaHandle a_body = a.get().as_quantified().body;
        FormulaHandle a_inst = cc.builder.instantiate_quantifier_body(
            a_body, Term::fixed(v));
        TermRef witness_ref{static_cast<uint32_t>(out.size())};
        {
            lkr::Forall op{};
            op.principal = pos_a;
            op.eigen = v;
            out.emplace_back(std::move(op));
        }
        shadow.entries[pos_a] = a_inst;

        // Exists(pos_b, witness=TermRef↑Forall).
        FormulaHandle b_body = b.get().as_quantified().body;
        FormulaHandle b_inst = cc.builder.instantiate_quantifier_body(
            b_body, Term::fixed(v));
        {
            lkr::Exists op{};
            op.principal = pos_b;
            op.witness = witness_ref;
            out.emplace_back(std::move(op));
        }
        shadow.entries[pos_b] = b_inst;

        return emit_close(cc, shadow, pos_a, pos_b, out);
    }

    return MAKE_ERROR
        << "emit_close: precondition violation — a and b shapes don't match. "
        << "a is " << (is_atomic_literal(a) ? "literal" :
                       is_or(a) ? "or" :
                       is_and(a) ? "and" :
                       is_forall(a) ? "forall" :
                       is_exists(a) ? "exists" :
                       is_top_literal(a) ? "top" : "other")
        << ", b is " << (is_atomic_literal(b) ? "literal" :
                          is_or(b) ? "or" :
                          is_and(b) ? "and" :
                          is_forall(b) ? "forall" :
                          is_exists(b) ? "exists" :
                          is_top_literal(b) ? "top" : "other");
}

}  // namespace logic::proof::translate::nd_to_lkr
