#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include "src/proof/translate/lkr_to_ks1/reconcile.h"

#include <variant>
#include <vector>

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// A formula is a negative literal iff its top connective is ¬ (NNF: only atoms
// are negated). Ai's parameter is the POSITIVE atom a; Ai emits the pair a∨ā.
bool is_negative_literal(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not;
}

// (Γ) — the formula of a sequent: the LEFT-associated disjunction of its
// entries (HSW §II.B). The contract of `tr` is "ends at denote(Γ)".
FormulaHandle denote(FormulaBuilder& fb, const std::vector<FormulaHandle>& g) {
    FormulaHandle acc = g[0];
    for (std::size_t i = 1; i < g.size(); ++i) acc = fb.make_or(acc, g[i]);
    return acc;
}

// Prepend `d` to every step's context — composes a sub-derivation (t ⟶ X)
// inside the context S{·} = [d, …] (e.g. the Left branch of an ∧). See
// LKR_TO_KS1_DESIGN.md.
void prefix_context(std::vector<ks1::Step>& steps, ks1::Dir d) {
    for (ks1::Step& s : steps) s.context.insert(s.context.begin(), d);
}

ks1::Step eqv_step(ks1::EqRule eq, ks1::Path ctx) {
    ks1::Step s;
    s.rule = ks1::Rule::Eqv; s.eq = eq; s.dir = ks1::EqDir::Forward;
    s.context = std::move(ctx);
    return s;
}
ks1::Step sw_step(ks1::Path ctx) {
    ks1::Step s; s.rule = ks1::Rule::Sw; s.context = std::move(ctx); return s;
}

ks1::Step ai_step(FormulaHandle positive_atom) {
    ks1::Step s;
    s.rule    = ks1::Rule::Ai;
    s.f_param = positive_atom;
    return s;
}

ks1::Step comm_or_root() { return eqv_step(ks1::EqRule::CommOr, {}); }

ks1::Step tu_root() {
    ks1::Step s;
    s.rule = ks1::Rule::Tu;           // A → A∧t
    return s;
}

// tr(d): KS1 steps realizing t ⟶ (d.conclusion), where (Γ) is the
// left-associated disjunction of the sequent (LKR_TO_KS1_DESIGN.md §"The
// sequent–formula correspondence"). K6.1 scope is the switch-free linear
// shapes: a 2-literal axiom, a single-formula Or wrapper, and an empty-context
// And. Everything else (switch sequence, multi-formula reconciliation,
// quantifiers, resource rules) errors with the phase that owns it.
util::Result<std::vector<ks1::Step>> tr(FormulaBuilder& fb, const lce::Deriv& d) {
    // --- RAx: pure 2-literal axiom ⊢ φ,ψ (duals). (Γ) = φ∨ψ. -------------
    if (const auto* ax = std::get_if<lce::RAx>(&d.rule)) {
        if (d.conclusion.size() != 2)
            return MAKE_ERROR << "lkr_to_ks1: K6.1 axiom must be exactly 2 literals "
                                 "(got " << d.conclusion.size()
                              << "); axiom-with-weakening is K6.3";
        FormulaHandle lit_a = d.conclusion[ax->a];
        FormulaHandle lit_b = d.conclusion[ax->b];
        FormulaHandle positive = is_negative_literal(lit_a) ? lit_b : lit_a;
        std::vector<ks1::Step> steps{ai_step(positive)};   // t → α∨ᾱ
        // (Γ) reads disjuncts in sequent order. Ai emits α∨ᾱ; if the sequent
        // lists the negative literal first, commute to ᾱ∨α.
        if (is_negative_literal(d.conclusion[0]))
            steps.push_back(comm_or_root());
        return steps;
    }

    // --- ROr / RExchange: the sequent's (Γ) is an ≡-reshape of the child's.
    // Recurse, then reconcile denote(child) ⟶ denote(node) with Eqv steps. ---
    if (const auto* orr = std::get_if<lce::ROr>(&d.rule)) {
        TRY_ASSIGN(steps, tr(fb, *orr->child));
        TRY_ASSIGN(rec, equiv_steps(fb, denote(fb, orr->child->conclusion),
                                    denote(fb, d.conclusion)));
        steps.insert(steps.end(), rec.begin(), rec.end());
        return steps;
    }
    if (const auto* ex = std::get_if<lce::RExchange>(&d.rule)) {
        TRY_ASSIGN(steps, tr(fb, *ex->child));
        TRY_ASSIGN(rec, equiv_steps(fb, denote(fb, ex->child->conclusion),
                                    denote(fb, d.conclusion)));
        steps.insert(steps.end(), rec.begin(), rec.end());
        return steps;
    }

    // --- RAnd: ⊢ Γ_L,φ and ⊢ Γ_R,ψ ⊢ Γ_L,Γ_R,φ∧ψ. ---------------------
    // Build t ⟶ (P∨φ)∧(Q∨ψ) [P=(Γ_L), Q=(Γ_R)], then the switch sequence to
    // ((φ∧ψ)∨P)∨Q, then reconcile to denote(node). Empty contexts (P and/or Q
    // absent) skip the switches entirely (LKR_TO_KS1_DESIGN.md §RAnd).
    if (const auto* andr = std::get_if<lce::RAnd>(&d.rule)) {
        const lce::Deriv* L = andr->left.get();
        const lce::Deriv* R = andr->right.get();
        const bool emptyL = L->conclusion.size() == 1;   // Γ_L = ∅ (just φ)
        const bool emptyR = R->conclusion.size() == 1;   // Γ_R = ∅ (just ψ)

        TRY_ASSIGN(stepsL, tr(fb, *L));   // t ⟶ P∨φ (or φ if Γ_L=∅)
        TRY_ASSIGN(stepsR, tr(fb, *R));   // t ⟶ Q∨ψ (or ψ if Γ_R=∅)
        prefix_context(stepsL, ks1::Dir::Left);
        prefix_context(stepsR, ks1::Dir::Right);
        std::vector<ks1::Step> steps{tu_root()};                    // t → t∧t
        steps.insert(steps.end(), stepsL.begin(), stepsL.end());    // → (P∨φ)∧t
        steps.insert(steps.end(), stepsR.begin(), stepsR.end());    // → (P∨φ)∧(Q∨ψ)

        FormulaHandle phi = L->conclusion.back();
        FormulaHandle psi = R->conclusion.back();
        using P = ks1::Path; using D = ks1::Dir; using E = ks1::EqRule;
        if (!emptyL && !emptyR) {
            // (P∨φ)∧(Q∨ψ) ⟶ ((φ∧ψ)∨P)∨Q  (design doc steps 4–9).
            steps.push_back(eqv_step(E::CommOr, P{D::Right}));       // (Q∨ψ)→(ψ∨Q)
            steps.push_back(sw_step({}));                           // → ((P∨φ)∧ψ)∨Q
            steps.push_back(eqv_step(E::CommOr, P{D::Left, D::Left}));// (P∨φ)→(φ∨P)
            steps.push_back(eqv_step(E::CommAnd, P{D::Left}));       // → (ψ∧(φ∨P))∨Q
            steps.push_back(sw_step(P{D::Left}));                   // → ((ψ∧φ)∨P)∨Q
            steps.push_back(eqv_step(E::CommAnd, P{D::Left, D::Left}));// (ψ∧φ)→(φ∧ψ)
        } else if (emptyL && !emptyR) {
            // φ∧(Q∨ψ) ⟶ (φ∧ψ)∨Q
            steps.push_back(eqv_step(E::CommOr, P{D::Right}));       // (Q∨ψ)→(ψ∨Q)
            steps.push_back(sw_step({}));                           // → (φ∧ψ)∨Q
        } else if (!emptyL && emptyR) {
            // (P∨φ)∧ψ ⟶ (φ∧ψ)∨P
            steps.push_back(eqv_step(E::CommOr, P{D::Left}));        // (P∨φ)→(φ∨P)
            steps.push_back(eqv_step(E::CommAnd, {}));               // → ψ∧(φ∨P)
            steps.push_back(sw_step({}));                           // → (ψ∧φ)∨P
            steps.push_back(eqv_step(E::CommAnd, P{D::Left}));       // (ψ∧φ)→(φ∧ψ)
        }
        // else emptyL && emptyR: cur = φ∧ψ already; no switches.

        // cur is now an ≡-reshape of denote(node); reconcile.
        FormulaHandle cur;
        if (emptyL && emptyR)       cur = fb.make_and(phi, psi);
        else {
            FormulaHandle conj = fb.make_and(phi, psi);
            if (!emptyL && !emptyR) {
                FormulaHandle Pf = denote(fb, {L->conclusion.begin(), L->conclusion.end() - 1});
                FormulaHandle Qf = denote(fb, {R->conclusion.begin(), R->conclusion.end() - 1});
                cur = fb.make_or(fb.make_or(conj, Pf), Qf);
            } else if (emptyL) {
                FormulaHandle Qf = denote(fb, {R->conclusion.begin(), R->conclusion.end() - 1});
                cur = fb.make_or(conj, Qf);
            } else {
                FormulaHandle Pf = denote(fb, {L->conclusion.begin(), L->conclusion.end() - 1});
                cur = fb.make_or(conj, Pf);
            }
        }
        TRY_ASSIGN(rec, equiv_steps(fb, cur, denote(fb, d.conclusion)));
        steps.insert(steps.end(), rec.begin(), rec.end());
        return steps;
    }

    // --- RForall: ⊢ Γ, φ[eigen] ⊢ Γ, ∀x.φ. ------------------------------
    // ForallUnit gives ∀x.t; the child derivation runs under [Down] with the
    // eigenvariable rebound to the ∀'s bound var (fixed(eigen) → gen0), so the
    // body becomes φ. K6.2 first cut: Γ empty (single-formula goal); the
    // DistForall pull-out for a non-empty context, and nested-binder de Bruijn
    // depth, are K6.2b.
    if (const auto* far = std::get_if<lce::RForall>(&d.rule)) {
        if (d.conclusion.size() != 1)
            return MAKE_ERROR << "lkr_to_ks1: K6.2 RForall supports only a "
                                 "single-formula goal (Γ empty); DistForall context = K6.2b";
        const Formula& qf = d.conclusion[0].get();
        if (!(qf.is_quantified() && qf.as_quantified().op == Op::Forall))
            return MAKE_ERROR << "lkr_to_ks1: RForall principal is not a ∀";
        TRY_ASSIGN(child_steps, tr(fb, *far->child));
        for (ks1::Step& s : child_steps) {
            // De Bruijn index of the new ∀'s var, as seen from this step's
            // redex = the number of binders (quantifier `Down`s) above it.
            int depth = 0;
            for (ks1::Dir dd : s.context) if (dd == ks1::Dir::Down) ++depth;
            // Ex's f_param is the ∃-BODY — one binder deeper than the redex; its
            // t_param (witness) sits at the redex level. All other params (Ai's
            // literal, W's formula) sit at the redex level.
            if (s.f_param.valid()) {
                int fd = depth + (s.rule == ks1::Rule::Ex ? 1 : 0);
                s.f_param = fb.translate_term(s.f_param, Term::fixed(far->eigen),
                                              Term::generalized(fd));
            }
            if (s.rule == ks1::Rule::Ex)
                s.t_param = fb.translate_in_term(s.t_param, Term::fixed(far->eigen),
                                                 Term::generalized(depth));
            s.context.insert(s.context.begin(), ks1::Dir::Down);
        }
        ks1::Step fu; fu.rule = ks1::Rule::ForallUnit;       // t → ∀x.t  (ctx {})
        std::vector<ks1::Step> steps{fu};
        steps.insert(steps.end(), child_steps.begin(), child_steps.end());
        return steps;
    }

    // --- RExists: ⊢ Γ, φ[x:=t] ⊢ Γ, ∃x.φ. -------------------------------
    // Isolate the instance φ[t] as the rightmost disjunct, apply Ex there
    // (S{A[x/t]}/S{∃x.A}), then reconcile to denote(node).
    if (const auto* exr = std::get_if<lce::RExists>(&d.rule)) {
        const lce::Deriv* child = exr->child.get();
        const std::size_t pr = exr->principal;
        FormulaHandle quant = d.conclusion[pr];                  // ∃x.φ
        const Formula& qf = quant.get();
        if (!(qf.is_quantified() && qf.as_quantified().op == Op::Exists))
            return MAKE_ERROR << "lkr_to_ks1: RExists principal is not an ∃";
        FormulaHandle body = qf.as_quantified().body;            // φ with gen0
        FormulaHandle inst = fb.instantiate_gen(body, exr->witness);  // φ[t]

        TRY_ASSIGN(steps, tr(fb, *child));                       // → denote(child)
        const bool single = child->conclusion.size() == 1;
        FormulaHandle iso, after_ex;
        ks1::Path ex_ctx;
        if (single) {
            iso = inst; after_ex = quant; ex_ctx = {};
        } else {
            std::vector<FormulaHandle> rest;
            for (std::size_t i = 0; i < child->conclusion.size(); ++i)
                if (i != pr) rest.push_back(child->conclusion[i]);
            FormulaHandle restF = denote(fb, rest);
            iso = fb.make_or(restF, inst);
            after_ex = fb.make_or(restF, quant);
            ex_ctx = {ks1::Dir::Right};
        }
        TRY_ASSIGN(r1, equiv_steps(fb, denote(fb, child->conclusion), iso));
        steps.insert(steps.end(), r1.begin(), r1.end());
        ks1::Step ex; ex.rule = ks1::Rule::Ex; ex.f_param = body;
        ex.t_param = exr->witness; ex.context = ex_ctx;
        steps.push_back(ex);
        TRY_ASSIGN(r2, equiv_steps(fb, after_ex, denote(fb, d.conclusion)));
        steps.insert(steps.end(), r2.begin(), r2.end());
        return steps;
    }

    // --- RWeaken: ⊢ Γ ⊢ Γ,φ (the weakened-in φ is at idx). ---------------
    // Φ2 resource step: prove the linear core for the child (Γ without φ), then
    // W in φ (S{A}/S{A∨B}) and reconcile to denote(node). This stays decomposed
    // only when no linear rule sits between this weakening and the root (φ added
    // "high"); otherwise the W lands mid-Φ1 and ks1::split rejects it — the
    // rule-permutation that pushes weakening to the bottom (Thm 29) is K6.3b.
    if (const auto* w = std::get_if<lce::RWeaken>(&d.rule)) {
        const lce::Deriv* child = w->child.get();
        FormulaHandle weakened = d.conclusion[w->idx];
        TRY_ASSIGN(steps, tr(fb, *child));                 // Φ1: → denote(child)
        ks1::Step ws; ws.rule = ks1::Rule::W; ws.f_param = weakened;  // ctx {}
        steps.push_back(ws);                               // → denote(child)∨φ
        FormulaHandle after = fb.make_or(denote(fb, child->conclusion), weakened);
        TRY_ASSIGN(rec, equiv_steps(fb, after, denote(fb, d.conclusion)));
        steps.insert(steps.end(), rec.begin(), rec.end());
        return steps;
    }

    // --- RDuplicate: ⊢ Γ,φ,φ ⊢ Γ,φ (the child has an extra copy of φ=node[src]
    // appended; this node contracts it back). -----------------------------
    // Φ1 proves the doubled core (denote(child) = denote(node) ∨ φ), then Φ2
    // reshapes the two φ copies adjacent as φ∨φ, contracts (contract_steps), and
    // reconciles to denote(node). Decomposed when the child's derivation is all
    // linear (no interspersed weakening/contraction above — that needs Thm 29).
    if (const auto* dup = std::get_if<lce::RDuplicate>(&d.rule)) {
        const lce::Deriv* child = dup->child.get();
        FormulaHandle X = d.conclusion[dup->src];
        TRY_ASSIGN(steps, tr(fb, *child));                 // Φ1: → denote(child)

        std::vector<FormulaHandle> rest;
        for (std::size_t i = 0; i < d.conclusion.size(); ++i)
            if (i != dup->src) rest.push_back(d.conclusion[i]);
        FormulaHandle XX = fb.make_or(X, X);
        const bool has_rest = !rest.empty();
        FormulaHandle iso = has_rest ? fb.make_or(denote(fb, rest), XX) : XX;

        TRY_ASSIGN(r1, equiv_steps(fb, denote(fb, child->conclusion), iso));
        steps.insert(steps.end(), r1.begin(), r1.end());
        TRY_ASSIGN(con, contract_steps(fb, X));            // φ∨φ → φ; at [Right] if rest
        for (ks1::Step& s : con) {
            if (has_rest) s.context.insert(s.context.begin(), ks1::Dir::Right);
            steps.push_back(std::move(s));
        }
        FormulaHandle afterC = has_rest ? fb.make_or(denote(fb, rest), X) : X;
        TRY_ASSIGN(r2, equiv_steps(fb, afterC, denote(fb, d.conclusion)));
        steps.insert(steps.end(), r2.begin(), r2.end());
        return steps;
    }

    return MAKE_ERROR << "lkr_to_ks1: K6.3 — this rule not yet handled "
                         "(RContract = K6.3b, interspersed weakening/contraction = Thm 29)";
}

}  // namespace

util::Result<ks1::Derivation> lkr_to_ks1(FormulaBuilder& fb,
                                         const lce::Deriv& cutfree) {
    if (cutfree.conclusion.size() != 1)
        return MAKE_ERROR << "lkr_to_ks1: expected a single-formula (closed) goal "
                             "sequent, got " << cutfree.conclusion.size()
                          << " formulas";
    FormulaHandle goal = cutfree.conclusion[0];

    TRY_ASSIGN(steps, tr(fb, cutfree));
    FormulaHandle top = fb.make_not(fb.make_bottom());   // ⊤ = ¬⊥
    return ks1::Derivation{top, goal, std::move(steps)};
}

}  // namespace logic::proof::translate::lkr_to_ks1
