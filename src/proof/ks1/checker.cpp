#include "src/proof/ks1/checker.h"

namespace logic::proof::ks1 {

using util::Result;
using util::ResultStatus;
using util::Ok;

namespace {

// ---- formula shape helpers (NNF; ⊤ = ¬⊥, ⊥ = Bottom) -----------------

bool is_bottom(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Bottom;
}
bool is_top(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not &&
           f.as_compound().left.valid() && is_bottom(f.as_compound().left);
}
// A proper atomic literal: a predicate or its negation (used by ai/ac).
bool is_atom_literal(FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_predicate()) return true;
    return f.is_compound() && f.as_compound().op == Op::Not &&
           f.as_compound().left.valid() && f.as_compound().left.get().is_predicate();
}
bool is_op(FormulaHandle h, Op op) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == op;
}
bool is_quant(FormulaHandle h, Op op) {
    const Formula& f = h.get();
    return f.is_quantified() && f.as_quantified().op == op;
}

FormulaHandle make_top(FormulaBuilder& fb) { return fb.make_not(fb.make_bottom()); }

// NNF dual of a literal: ¬p ↦ p, p ↦ ¬p, ⊥ ↦ ⊤, ⊤ ↦ ⊥.
FormulaHandle dual_literal(FormulaBuilder& fb, FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_compound() && f.as_compound().op == Op::Not && f.as_compound().left.valid())
        return f.as_compound().left;       // ¬X ↦ X
    return fb.make_not(h);                  // X ↦ ¬X
}

// Rebuild a compound preserving its op, via FormulaBuilder's public makers
// (the Formula(Compound) ctor is private). KS1 NNF uses And/Or/Not/Bottom.
FormulaHandle remake(FormulaBuilder& fb, Op op, FormulaHandle l, FormulaHandle r) {
    switch (op) {
        case Op::And:     return fb.make_and(l, r);
        case Op::Or:      return fb.make_or(l, r);
        case Op::Implies: return fb.make_implies(l, r);
        case Op::Iff:     return fb.make_iff(l, r);
        case Op::Not:     return fb.make_not(l);
        case Op::Bottom:  return fb.make_bottom();
        default:          return fb.make_or(l, r);  // unreachable for KS1 NNF
    }
}

// ---- De Bruijn helpers (only what shift_formula/instantiate_gen lack) ----

// Does the free generalized variable Gen(target) occur in h?
bool gen_occurs_free(FormulaHandle h, var_index target) {
    const Formula& f = h.get();
    if (f.is_predicate()) {
        for (const Term& t : f.as_predicate().args()) {
            if (t.is_generalized() && t.as_variable() == target) return true;
            if (t.is_description() &&
                gen_occurs_free(t.as_description().body, target + 1))
                return true;
        }
        return false;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        return (c.left.valid()  && gen_occurs_free(c.left,  target)) ||
               (c.right.valid() && gen_occurs_free(c.right, target));
    }
    if (f.is_quantified())
        return gen_occurs_free(f.as_quantified().body, target + 1);
    return false;  // SchemaVar / Sentence: not produced by KS1 inputs
}

FormulaHandle swap_gen(FormulaBuilder& fb, FormulaHandle h, var_index lo);

// Swap free Gen(lo) and Gen(lo+1) in a term (KS1 is description-free; a
// description body binds one variable, so its indices shift by 1 inside).
Term swap_in_term(FormulaBuilder& fb, const Term& t, var_index lo) {
    if (t.is_generalized()) {
        var_index v = t.as_variable();
        if (v == lo)     return Term::generalized(lo + 1);
        if (v == lo + 1) return Term::generalized(lo);
        return t;
    }
    if (t.is_description())
        return Term::description(swap_gen(fb, t.as_description().body, lo + 1));
    return t;
}

FormulaHandle swap_gen(FormulaBuilder& fb, FormulaHandle h, var_index lo) {
    const Formula& f = h.get();
    if (f.is_predicate()) {
        std::vector<Term> args;
        args.reserve(f.as_predicate().args().size());
        for (const Term& t : f.as_predicate().args())
            args.push_back(swap_in_term(fb, t, lo));
        return fb.predicate(f.as_predicate().predicate(), std::move(args));
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        FormulaHandle l = c.left.valid()  ? swap_gen(fb, c.left,  lo) : c.left;
        FormulaHandle r = c.right.valid() ? swap_gen(fb, c.right, lo) : c.right;
        return remake(fb, c.op, l, r);
    }
    if (f.is_quantified())
        return fb.make_quantified(f.as_quantified().op,
                                  swap_gen(fb, f.as_quantified().body, lo + 1));
    return h;
}

// ---- context navigation (paper §V) -----------------------------------

Result<FormulaHandle> sub_at(FormulaHandle root, const Path& p, size_t i) {
    if (i == p.size()) return root;
    const Formula& f = root.get();
    switch (p[i]) {
        case Dir::Left:
            if (!f.is_compound() || !f.as_compound().left.valid())
                return MAKE_ERROR << "context: Left into non-binary node";
            return sub_at(f.as_compound().left, p, i + 1);
        case Dir::Right:
            if (!f.is_compound() || !f.as_compound().right.valid())
                return MAKE_ERROR << "context: Right into non-binary node";
            return sub_at(f.as_compound().right, p, i + 1);
        case Dir::Down:
            if (!f.is_quantified())
                return MAKE_ERROR << "context: Down into non-quantifier node";
            return sub_at(f.as_quantified().body, p, i + 1);
    }
    return MAKE_ERROR << "context: bad direction";
}

Result<FormulaHandle> rewrite_at(FormulaBuilder& fb, FormulaHandle root,
                                 const Path& p, size_t i, FormulaHandle sub) {
    if (i == p.size()) return sub;
    const Formula& f = root.get();
    if (p[i] == Dir::Down) {
        if (!f.is_quantified())
            return MAKE_ERROR << "context: Down into non-quantifier node";
        auto child = rewrite_at(fb, f.as_quantified().body, p, i + 1, sub);
        if (child.is_error()) return std::move(child).error();
        return fb.make_quantified(f.as_quantified().op, child.value());
    }
    if (!f.is_compound() || !f.as_compound().left.valid())
        return MAKE_ERROR << "context: descent into non-binary node";
    const Compound& c = f.as_compound();
    FormulaHandle nl = c.left, nr = c.right;
    if (p[i] == Dir::Left) {
        auto child = rewrite_at(fb, c.left, p, i + 1, sub);
        if (child.is_error()) return std::move(child).error();
        nl = child.value();
    } else {
        if (!c.right.valid())
            return MAKE_ERROR << "context: Right into unary node";
        auto child = rewrite_at(fb, c.right, p, i + 1, sub);
        if (child.is_error()) return std::move(child).error();
        nr = child.value();
    }
    return remake(fb, c.op, nl, nr);
}

// ---- the eq (2) equivalence equations (single-step, both directions) ----

Result<FormulaHandle> apply_eq(FormulaBuilder& fb, EqRule eq, EqDir dir,
                               FormulaHandle P) {
    auto comm = [&](Op op) -> Result<FormulaHandle> {
        if (!is_op(P, op)) return MAKE_ERROR << "≡ comm: redex not the expected ∧/∨";
        const Compound& c = P.get().as_compound();
        return remake(fb, op, c.right, c.left);
    };
    auto assoc = [&](Op op) -> Result<FormulaHandle> {
        // Forward: (A∘B)∘C → A∘(B∘C);  Backward: A∘(B∘C) → (A∘B)∘C.
        if (dir == EqDir::Forward) {
            if (!is_op(P, op) || !is_op(P.get().as_compound().left, op))
                return MAKE_ERROR << "≡ assoc→: redex not (A∘B)∘C";
            FormulaHandle C = P.get().as_compound().right;
            const Compound& lc = P.get().as_compound().left.get().as_compound();
            return remake(fb, op, lc.left, remake(fb, op, lc.right, C));
        }
        if (!is_op(P, op) || !is_op(P.get().as_compound().right, op))
            return MAKE_ERROR << "≡ assoc←: redex not A∘(B∘C)";
        FormulaHandle A = P.get().as_compound().left;
        const Compound& rc = P.get().as_compound().right.get().as_compound();
        return remake(fb, op, remake(fb, op, A, rc.left), rc.right);
    };
    auto swap = [&](Op q) -> Result<FormulaHandle> {
        // Qx.Qy.A → Qy.Qx.A : strip both binders, swap Gen0/Gen1, rewrap.
        if (!is_quant(P, q) || !is_quant(P.get().as_quantified().body, q))
            return MAKE_ERROR << "≡ swap: redex not Qx.Qy.A";
        FormulaHandle inner = P.get().as_quantified().body;          // Qy.A
        FormulaHandle body  = inner.get().as_quantified().body;       // A
        FormulaHandle swapped = swap_gen(fb, body, 0);
        return fb.make_quantified(q, fb.make_quantified(q, swapped));
    };
    // ∀-over-∨ (dist=Or for ∀) / ∃-over-∧ (dist=And for ∃).
    auto dist = [&](Op q, Op op) -> Result<FormulaHandle> {
        if (dir == EqDir::Forward) {
            // Qx.(A op B) → (Qx.A) op B,  requires x (Gen0) not free in B.
            if (!is_quant(P, q) || !is_op(P.get().as_quantified().body, op))
                return MAKE_ERROR << "≡ dist→: redex not Qx.(A op B)";
            const Compound& c = P.get().as_quantified().body.get().as_compound();
            FormulaHandle Ab = c.left, Bb = c.right;
            if (gen_occurs_free(Bb, 0))
                return MAKE_ERROR << "≡ dist→: bound var occurs free in B";
            FormulaHandle B = fb.shift_formula(Bb, 1, -1);  // drop the binder over B
            return remake(fb, op, fb.make_quantified(q, Ab), B);
        }
        // (Qx.A) op B → Qx.(A op B).
        if (!is_op(P, op) || !is_quant(P.get().as_compound().left, q))
            return MAKE_ERROR << "≡ dist←: redex not (Qx.A) op B";
        FormulaHandle Ab = P.get().as_compound().left.get().as_quantified().body;
        FormulaHandle B  = P.get().as_compound().right;
        FormulaHandle Bup = fb.shift_formula(B, 0, 1);  // B moves under the binder
        return fb.make_quantified(q, remake(fb, op, Ab, Bup));
    };
    switch (eq) {
        case EqRule::CommAnd:   return comm(Op::And);
        case EqRule::CommOr:    return comm(Op::Or);
        case EqRule::AssocAnd:  return assoc(Op::And);
        case EqRule::AssocOr:   return assoc(Op::Or);
        case EqRule::SwapForall:return swap(Op::Forall);
        case EqRule::SwapExists:return swap(Op::Exists);
        case EqRule::DistForall:return dist(Op::Forall, Op::Or);
        case EqRule::DistExists:return dist(Op::Exists, Op::And);
    }
    return MAKE_ERROR << "≡: unknown equation";
}

// ---- apply one rule to the redex P, producing the conclusion Q -------

Result<FormulaHandle> apply_rule(FormulaBuilder& fb, const Step& s, FormulaHandle P) {
    switch (s.rule) {
        case Rule::ForallUnit:  // S{t}/S{∀x.t}
            if (!is_top(P)) return MAKE_ERROR << "∀: redex is not ⊤";
            return fb.make_quantified(Op::Forall, make_top(fb));

        case Rule::Ai: {        // S{t}/S{a∨ā}
            if (!is_top(P)) return MAKE_ERROR << "ai: redex is not ⊤";
            if (!s.f_param.valid() || !is_atom_literal(s.f_param))
                return MAKE_ERROR << "ai: parameter is not an atomic literal";
            return fb.make_or(s.f_param, dual_literal(fb, s.f_param));
        }
        case Rule::Tu:          // S{A}/S{A∧t}
            return fb.make_and(P, make_top(fb));

        case Rule::Sw: {        // S{A∧(B∨C)}/S{(A∧B)∨C}
            if (!is_op(P, Op::And) || !is_op(P.get().as_compound().right, Op::Or))
                return MAKE_ERROR << "s: redex not A∧(B∨C)";
            FormulaHandle A = P.get().as_compound().left;
            const Compound& orc = P.get().as_compound().right.get().as_compound();
            return fb.make_or(fb.make_and(A, orc.left), orc.right);
        }
        case Rule::Mix: {       // S{A∧B}/S{A∨B}
            if (!is_op(P, Op::And)) return MAKE_ERROR << "mix: redex not A∧B";
            const Compound& c = P.get().as_compound();
            return fb.make_or(c.left, c.right);
        }
        case Rule::Ex: {        // S{A[x/t]}/S{∃x.A}
            if (!s.f_param.valid()) return MAKE_ERROR << "∃: missing body parameter";
            FormulaHandle inst = fb.instantiate_gen(s.f_param, s.t_param);
            if (!(inst == P)) return MAKE_ERROR << "∃: A[x/t] does not match the redex";
            return fb.make_quantified(Op::Exists, s.f_param);
        }
        case Rule::Eqv:         // S{B}/S{A}, A≡B
            return apply_eq(fb, s.eq, s.dir, P);

        case Rule::W:           // S{A}/S{A∨B}
            if (!s.f_param.valid()) return MAKE_ERROR << "w: missing formula parameter";
            return fb.make_or(P, s.f_param);

        case Rule::WForall:     // S{A}/S{∀x.A}, x∉A
            return fb.make_quantified(Op::Forall, fb.shift_formula(P, 0, 1));

        case Rule::Ac: {        // S{a∨a}/S{a}
            if (!is_op(P, Op::Or)) return MAKE_ERROR << "ac: redex not a∨a";
            const Compound& c = P.get().as_compound();
            if (!(c.left == c.right)) return MAKE_ERROR << "ac: operands differ";
            if (!is_atom_literal(c.left)) return MAKE_ERROR << "ac: operand not atomic";
            return c.left;
        }
        case Rule::CForall: {   // S{∀x.∀x.A}/S{∀x.A}
            if (!is_quant(P, Op::Forall) ||
                !is_quant(P.get().as_quantified().body, Op::Forall))
                return MAKE_ERROR << "c∀: redex not ∀x.∀x.A";
            FormulaHandle body2 = P.get().as_quantified().body.get().as_quantified().body;
            return fb.make_quantified(Op::Forall, fb.shift_formula(body2, 1, -1));
        }
        case Rule::M: {         // S{(A∧C)∨(B∧D)}/S{(A∨B)∧(C∨D)}
            if (!is_op(P, Op::Or) || !is_op(P.get().as_compound().left, Op::And) ||
                !is_op(P.get().as_compound().right, Op::And))
                return MAKE_ERROR << "m: redex not (A∧C)∨(B∧D)";
            const Compound& lc = P.get().as_compound().left.get().as_compound();
            const Compound& rc = P.get().as_compound().right.get().as_compound();
            return fb.make_and(fb.make_or(lc.left, rc.left),
                               fb.make_or(lc.right, rc.right));
        }
        case Rule::MForall: {   // S{(∀x.A)∨(∀x.B)}/S{∀x.(A∨B)}
            if (!is_op(P, Op::Or) || !is_quant(P.get().as_compound().left, Op::Forall) ||
                !is_quant(P.get().as_compound().right, Op::Forall))
                return MAKE_ERROR << "m∀: redex not (∀x.A)∨(∀x.B)";
            FormulaHandle Ab = P.get().as_compound().left.get().as_quantified().body;
            FormulaHandle Bb = P.get().as_compound().right.get().as_quantified().body;
            return fb.make_quantified(Op::Forall, fb.make_or(Ab, Bb));
        }
        case Rule::MExists: {   // S{(∃x.A)∨(∃x.B)}/S{∃x.(A∨B)}
            if (!is_op(P, Op::Or) || !is_quant(P.get().as_compound().left, Op::Exists) ||
                !is_quant(P.get().as_compound().right, Op::Exists))
                return MAKE_ERROR << "m∃: redex not (∃x.A)∨(∃x.B)";
            FormulaHandle Ab = P.get().as_compound().left.get().as_quantified().body;
            FormulaHandle Bb = P.get().as_compound().right.get().as_quantified().body;
            return fb.make_quantified(Op::Exists, fb.make_or(Ab, Bb));
        }
    }
    return MAKE_ERROR << "unknown rule";
}

}  // namespace

Result<FormulaHandle> replay(FormulaBuilder& fb, FormulaHandle top,
                             const std::vector<Step>& steps) {
    if (!top.valid()) return MAKE_ERROR << "derivation: top not set";
    FormulaHandle current = top;
    for (const Step& s : steps) {
        auto P = sub_at(current, s.context, 0);
        if (P.is_error()) return std::move(P).error();
        auto Q = apply_rule(fb, s, P.value());
        if (Q.is_error()) return std::move(Q).error();
        auto next = rewrite_at(fb, current, s.context, 0, Q.value());
        if (next.is_error()) return std::move(next).error();
        current = next.value();
    }
    return current;
}

ResultStatus check(FormulaBuilder& fb, const Derivation& d) {
    if (!d.bottom.valid()) return MAKE_ERROR << "derivation: bottom not set";
    auto end = replay(fb, d.top, d.steps);
    if (end.is_error()) return std::move(end).error();
    if (!(end.value() == d.bottom))
        return MAKE_ERROR << "derivation: final formula does not match bottom";
    return Ok();
}

}  // namespace logic::proof::ks1
