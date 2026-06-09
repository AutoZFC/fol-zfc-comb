#include "src/proof/ks1/checker.h"

#include "src/proof/ks1/equiv.h"

#include <cassert>
#include <vector>

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
// An atom of HSW's grammar `a ::= t | f | p(...) | p̄(...)` — i.e., a positive
// predicate, a negated predicate, or one of the truth units. Used by ai/ac.
bool is_atom_literal(FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_predicate()) return true;
    if (!f.is_compound()) return false;
    Op op = f.as_compound().op;
    if (op == Op::Bottom) return true;   // f (⊥)
    if (op != Op::Not || !f.as_compound().left.valid()) return false;
    const Formula& inner = f.as_compound().left.get();
    if (inner.is_predicate()) return true;                                      // p̄
    return inner.is_compound() && inner.as_compound().op == Op::Bottom;         // t (¬⊥)
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

// ---- ∧/∨-chain helpers (for AC-tolerant rule matching, modulo ≡) ---------
// Derivations are checked modulo ≡ (the working formula is kept canonical), so
// a rule's redex may be spread across a flattened ∧/∨-chain rather than sitting
// in the exact binary bracketing the schema shows. These flatten/rebuild a
// chain so a rule can pick its operands.

// Flatten the maximal `op`-chain rooted at `h` into its operands, left to right.
void flatten_chain(FormulaHandle h, Op op, std::vector<FormulaHandle>& out) {
    const Formula& f = h.get();
    if (f.is_compound() && f.as_compound().op == op) {
        flatten_chain(f.as_compound().left, op, out);
        flatten_chain(f.as_compound().right, op, out);
    } else {
        out.push_back(h);
    }
}

// Build a right-leaning `op`-chain from `ops` (size ≥ 1).
FormulaHandle build_chain(FormulaBuilder& fb, Op op,
                          const std::vector<FormulaHandle>& ops) {
    FormulaHandle acc = ops.back();
    for (std::size_t i = ops.size() - 1; i-- > 0;)
        acc = (op == Op::And) ? fb.make_and(ops[i], acc) : fb.make_or(ops[i], acc);
    return acc;
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

// Swap free Gen(lo) and Gen(lo+1) in a term. KS1 is description-free
// (precondition the comb layer also enforces — see comb_proof.h), so the
// only term shapes here are Gen and Fixed; assert against descriptions.
Term swap_in_term(const Term& t, var_index lo) {
    assert(!t.is_description() && "KS1: description in atom args (eliminate first)");
    if (t.is_generalized()) {
        var_index v = t.as_variable();
        if (v == lo)     return Term::generalized(lo + 1);
        if (v == lo + 1) return Term::generalized(lo);
    }
    return t;
}

FormulaHandle swap_gen(FormulaBuilder& fb, FormulaHandle h, var_index lo) {
    const Formula& f = h.get();
    if (f.is_predicate()) {
        std::vector<Term> args;
        args.reserve(f.as_predicate().args().size());
        for (const Term& t : f.as_predicate().args())
            args.push_back(swap_in_term(t, lo));
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

// A Compound is "navigable" via Left/Right only if it is ∧ or ∨. Per the
// paper §V, the context S{·}'s hole sits in atom position; in NNF that means
// at a literal slot. Descending into a Compound{Not, atom} (a literal) or
// Compound{Bottom} would place the hole BELOW the atom-position, allowing a
// rule like Tu to plug a non-literal there and produce a non-NNF formula.
bool is_navigable_binary(const Formula& f) {
    if (!f.is_compound()) return false;
    Op op = f.as_compound().op;
    return op == Op::And || op == Op::Or;
}

Result<FormulaHandle> sub_at(FormulaHandle root, const Path& p, size_t i) {
    if (i == p.size()) return root;
    const Formula& f = root.get();
    switch (p[i]) {
        case Dir::Left:
            if (!is_navigable_binary(f))
                return MAKE_ERROR << "context: Left into non-∧/∨ node (hole would leave atom position)";
            return sub_at(f.as_compound().left, p, i + 1);
        case Dir::Right:
            if (!is_navigable_binary(f))
                return MAKE_ERROR << "context: Right into non-∧/∨ node (hole would leave atom position)";
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
    if (!is_navigable_binary(f))
        return MAKE_ERROR << "context: descent into non-∧/∨ node (hole would leave atom position)";
    const Compound& c = f.as_compound();
    FormulaHandle nl = c.left, nr = c.right;
    if (p[i] == Dir::Left) {
        auto child = rewrite_at(fb, c.left, p, i + 1, sub);
        if (child.is_error()) return std::move(child).error();
        nl = child.value();
    } else {
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
    // ∀-over-∨ (op=Or for ∀) / ∃-over-∧ (op=And for ∃), AC-tolerant: the working
    // formula is canonical, so the binder's body is a flattened op-chain and the
    // x-free operands may sit anywhere. Forward floats ALL x-free operands out.
    auto dist = [&](Op q, Op op) -> Result<FormulaHandle> {
        if (dir == EqDir::Forward) {
            // Qx.(C₁ op … op Cₙ) → Qx.(those with x) op (those without x, floated)
            if (!is_quant(P, q) || !is_op(P.get().as_quantified().body, op))
                return MAKE_ERROR << "≡ dist→: redex not Qx.(op-chain)";
            std::vector<FormulaHandle> ops;
            flatten_chain(P.get().as_quantified().body, op, ops);
            std::vector<FormulaHandle> hasX, floated;
            for (FormulaHandle o : ops) {
                if (gen_occurs_free(o, 0)) hasX.push_back(o);
                else floated.push_back(fb.shift_formula(o, 1, -1));  // leaves the binder
            }
            if (floated.empty())
                return MAKE_ERROR << "≡ dist→: no x-free operand to float";
            if (hasX.empty())
                return MAKE_ERROR << "≡ dist→: every operand is x-free (vacuous binder)";
            std::vector<FormulaHandle> chain{
                fb.make_quantified(q, build_chain(fb, op, hasX))};
            for (FormulaHandle b : floated) chain.push_back(b);
            return build_chain(fb, op, chain);
        }
        // (Qx.A) op B → Qx.(A op B).  (binary; un-distribution is not AC-driven)
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

        case Rule::Sw: {        // S{A∧(B∨C)}/S{(A∧B)∨C}  (binary: A=∧.left, B∨C=∧.right)
            // HSW's switch acts on opaque structures, so we split the TOP binary
            // nodes — no ∧/∨ flattening — and B / C survive whatever their own
            // shape (a ∨-typed B, a structured C). The emitter brackets B∨C as
            // the right conjunct via ≡ steps.
            if (!is_op(P, Op::And)) return MAKE_ERROR << "s: redex not a ∧";
            const Compound& pc = P.get().as_compound();
            if (!is_op(pc.right, Op::Or))
                return MAKE_ERROR << "s: right conjunct is not a ∨ (bracket B∨C on the right)";
            const Compound& oc = pc.right.get().as_compound();
            return fb.make_or(fb.make_and(pc.left, oc.left), oc.right);  // (A∧B)∨C
        }
        case Rule::Mix: {       // S{A∧B}/S{A∨B}  (AC: split the ∧-chain at `split`)
            if (!is_op(P, Op::And)) return MAKE_ERROR << "mix: redex not A∧B";
            std::vector<FormulaHandle> conj;
            flatten_chain(P, Op::And, conj);
            std::size_t k = s.split ? s.split : 1;
            if (k >= conj.size()) return MAKE_ERROR << "mix: split out of range";
            FormulaHandle A = build_chain(fb, Op::And, {conj.begin(), conj.begin() + k});
            FormulaHandle B = build_chain(fb, Op::And, {conj.begin() + k, conj.end()});
            return fb.make_or(A, B);
        }
        case Rule::Ex: {        // S{A[x/t]}/S{∃x.A}  (instance matched modulo ≡)
            if (!s.f_param.valid()) return MAKE_ERROR << "∃: missing body parameter";
            FormulaHandle inst = fb.instantiate_gen(s.f_param, s.t_param);
            if (!equiv(fb, inst, P))
                return MAKE_ERROR << "∃: A[x/t] does not match the redex";
            return fb.make_quantified(Op::Exists, s.f_param);
        }
        case Rule::Eqv:         // S{B}/S{A}, A≡B
            return apply_eq(fb, s.eq, s.dir, P);

        case Rule::W:           // S{A}/S{A∨B}
            if (!s.f_param.valid()) return MAKE_ERROR << "w: missing formula parameter";
            return fb.make_or(P, s.f_param);

        case Rule::WForall:     // S{A}/S{∀x.A}, x∉A
            return fb.make_quantified(Op::Forall, fb.shift_formula(P, 0, 1));

        case Rule::Ac: {        // S{a∨a}/S{a}  (AC: contract two EQUAL atoms anywhere)
            if (!is_op(P, Op::Or)) return MAKE_ERROR << "ac: redex not a ∨";
            std::vector<FormulaHandle> disj;
            flatten_chain(P, Op::Or, disj);
            std::size_t i = SIZE_MAX, j = SIZE_MAX;
            if (!s.operands.empty()) {                       // explicit: contract operand i's twin
                i = s.operands[0];
                for (std::size_t k = 0; k < disj.size(); ++k)
                    if (k != i && i < disj.size() && disj[k] == disj[i]) { j = k; break; }
            } else {
                for (std::size_t p = 0; p < disj.size() && j == SIZE_MAX; ++p)
                    for (std::size_t q = p + 1; q < disj.size(); ++q)
                        if (disj[p] == disj[q]) { i = p; j = q; break; }
            }
            if (i == SIZE_MAX || j == SIZE_MAX || !(disj[i] == disj[j]))
                return MAKE_ERROR << "ac: no two equal ∨-operands";
            if (!is_atom_literal(disj[i])) return MAKE_ERROR << "ac: operand not atomic";
            disj.erase(disj.begin() + j);                   // drop one copy
            return build_chain(fb, Op::Or, disj);
        }
        case Rule::CForall: {   // S{∀x.∀x.A}/S{∀x.A}
            if (!is_quant(P, Op::Forall) ||
                !is_quant(P.get().as_quantified().body, Op::Forall))
                return MAKE_ERROR << "c∀: redex not ∀x.∀x.A";
            FormulaHandle body2 = P.get().as_quantified().body.get().as_quantified().body;
            return fb.make_quantified(Op::Forall, fb.shift_formula(body2, 1, -1));
        }
        // The three medials share the ∨-chain operand selection: pick two
        // operands (default the first two), replace them with the medial result,
        // keep any others in the ∨-chain. `replay` re-canonicalizes after.
        case Rule::M:
        case Rule::MForall:
        case Rule::MExists: {
            if (!is_op(P, Op::Or)) return MAKE_ERROR << "m: redex not a ∨";
            std::vector<FormulaHandle> disj;
            flatten_chain(P, Op::Or, disj);
            std::size_t j = 0, k = 1;
            if (s.operands.size() == 2) { j = s.operands[0]; k = s.operands[1]; }
            if (j >= disj.size() || k >= disj.size() || j == k)
                return MAKE_ERROR << "m: operand selectors out of range";
            FormulaHandle L = disj[j], R = disj[k], medial;
            if (s.rule == Rule::M) {                         // (A∧C)∨(B∧D)→(A∨B)∧(C∨D)
                if (!is_op(L, Op::And) || !is_op(R, Op::And))
                    return MAKE_ERROR << "m: selected operands not both ∧";
                std::vector<FormulaHandle> lc, rc;
                flatten_chain(L, Op::And, lc);
                flatten_chain(R, Op::And, rc);
                std::size_t sl = s.split ? s.split : 1, sr = sl;
                if (sl >= lc.size() || sr >= rc.size())
                    return MAKE_ERROR << "m: ∧ split out of range";
                FormulaHandle A = build_chain(fb, Op::And, {lc.begin(), lc.begin() + sl});
                FormulaHandle C = build_chain(fb, Op::And, {lc.begin() + sl, lc.end()});
                FormulaHandle B = build_chain(fb, Op::And, {rc.begin(), rc.begin() + sr});
                FormulaHandle D = build_chain(fb, Op::And, {rc.begin() + sr, rc.end()});
                medial = fb.make_and(fb.make_or(A, B), fb.make_or(C, D));
            } else {                                         // (Qx.A)∨(Qx.B)→Qx.(A∨B)
                Op q = (s.rule == Rule::MForall) ? Op::Forall : Op::Exists;
                if (!is_quant(L, q) || !is_quant(R, q))
                    return MAKE_ERROR << "m∀/m∃: selected operands not both the quantifier";
                medial = fb.make_quantified(q, fb.make_or(L.get().as_quantified().body,
                                                          R.get().as_quantified().body));
            }
            std::vector<FormulaHandle> rest{medial};         // medial + the untouched operands
            for (std::size_t i = 0; i < disj.size(); ++i)
                if (i != j && i != k) rest.push_back(disj[i]);
            return build_chain(fb, Op::Or, rest);
        }
    }
    return MAKE_ERROR << "unknown rule";
}

}  // namespace

// Replay MODULO ≡ (HSW §II eq (2)): formulas are taken up to ≡, so
// reassociation/commutation of ∧/∨ is free and never a recorded step. Rather
// than force a canonical representative (which would make ∧/∨-operand positions
// — and hence context Paths — unstable), the rules MATCH their redex AC-tolerantly
// (see the chain arms in `apply_rule`): a rule applies if its premise shape is
// present at `context` up to ≡. The working formula evolves exactly as the rules
// produce it, so context Paths stay stable; `check` compares the endpoints
// modulo ≡. The remaining explicit `Eqv` steps are quantifier shifts the
// AC-tolerant arms do not absorb (only `DistForall` is emitted today).
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
    if (!equiv(fb, end.value(), d.bottom))
        return MAKE_ERROR << "derivation: final formula does not match bottom (modulo ≡)";
    return Ok();
}

}  // namespace logic::proof::ks1
