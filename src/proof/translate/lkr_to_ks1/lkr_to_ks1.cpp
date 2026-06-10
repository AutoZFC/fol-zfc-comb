#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include "src/proof/translate/lkr_to_ks1/reconcile.h"
#include "src/proof/ks1/checker.h"

#include <cstdlib>
#include <iostream>
#include <variant>
#include <vector>

// LKR (sequent tree) → KS1 (deep-inference chain).  HSW's translation is a TABLE:
// each LK rule maps to a fixed KS1 "macro" on the sequent's denotation
//   (Γ) = A₁∨…∨Aₙ   (left-associated; the `entries` bag is Γ, order-free).
// This file is that table folded over the `Deriv` tree (`std::visit`, so the
// compiler checks every rule is handled), with one shared harness:
//
//   * `Seq` owns the live formula and advances it by REPLAYING each emitted step,
//     so `cur` is always the true formula — no macro ever hand-predicts shape
//     (the bug class that hand-reconstruction invited).
//   * `Seq::reconcile` is the single boundary-aware ≡-reshape (reconcile_to);
//     the macros never open-code associativity/permutation bureaucracy.
//
// The accidental ≡-steps (Comm/Assoc/reorder) are NOT in HSW — they are impedance
// between our structural `Path` addressing and the paper's mod-≡ world, and live
// only inside the reconcile primitives.

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// One node's translation: the KS1 steps and the sequent ENTRIES (= Γ).
// Invariant (held by construction via `Seq`): replay(⊤, steps) == denote(entries).
struct Tr {
    std::vector<ks1::Step>     steps;
    std::vector<FormulaHandle> entries;
};

constexpr std::size_t kNone = static_cast<std::size_t>(-1);

FormulaHandle top(FormulaBuilder& fb) { return fb.make_not(fb.make_bottom()); }

// (Γ): the LEFT-associated ∨ of the entries (HSW §II.B).
FormulaHandle denote(FormulaBuilder& fb, const std::vector<FormulaHandle>& g) {
    FormulaHandle acc = g[0];
    for (std::size_t i = 1; i < g.size(); ++i) acc = fb.make_or(acc, g[i]);
    return acc;
}

// `env` = the ancestor eigenvariables that bind this node in the final KS1 term,
// OUTERMOST first.  `localize` rewrites a formula/term read from the LKR sequent
// (where eigenvars are FIXED vars) into the De Bruijn gen-form it must take at
// this node's denotation level: env[L] → gen(|env|-1-L) (innermost eigenvar →
// gen0).  subst_fixed_impl is depth-aware, so an occurrence under m internal
// binders of `h` correctly becomes gen(idx+m); distinct eigenvars map to distinct
// gens, so the substitutions never alias.  This is Option A: steps are born in
// gen-form, so the RForall [Down]-wrap needs NO post-hoc eigenvar rebind — adding
// an outer binder leaves inner-binder gen distances unchanged.
FormulaHandle localize(FormulaBuilder& fb, FormulaHandle h,
                       const std::vector<var_index>& env) {
    for (std::size_t L = 0; L < env.size(); ++L)
        h = fb.subst_fixed_impl(h, env[L], Term::generalized(env.size() - 1 - L), 0);
    return h;
}
Term localize(FormulaBuilder& fb, const Term& t, const std::vector<var_index>& env) {
    Term r = t;
    for (std::size_t L = 0; L < env.size(); ++L)
        r = fb.subst_fixed_in_term(r, env[L], Term::generalized(env.size() - 1 - L), 0);
    return r;
}

// A formula is a negative literal iff its top connective is ¬ (NNF). Ai's
// parameter is the POSITIVE atom; Ai emits the pair a∨ā.
bool is_negative_literal(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not;
}

std::size_t index_of(const std::vector<FormulaHandle>& e, FormulaHandle x,
                     std::size_t skip = kNone) {
    for (std::size_t i = 0; i < e.size(); ++i)
        if (i != skip && e[i] == x) return i;
    return kNone;
}
std::size_t last_index_of(const std::vector<FormulaHandle>& e, FormulaHandle x) {
    std::size_t r = kNone;
    for (std::size_t i = 0; i < e.size(); ++i) if (e[i] == x) r = i;
    return r;
}

// Path from the root of an n-entry LEFT-associated ∨-tree to entry `i`:
//   i==n-1 : [Right];  0<i<n-1 : [Left]^(n-1-i)++[Right];  i==0 : [Left]^(n-1).
ks1::Path path_to_entry(std::size_t i, std::size_t n) {
    ks1::Path p(n - 1 - i, ks1::Dir::Left);
    if (i != 0) p.push_back(ks1::Dir::Right);
    return p;
}

ks1::Step eqv_step(ks1::EqRule eq, ks1::Path ctx) {
    ks1::Step s; s.rule = ks1::Rule::Eqv; s.eq = eq; s.dir = ks1::EqDir::Forward;
    s.context = std::move(ctx);
    return s;
}
ks1::Step rule_step(ks1::Rule r, ks1::Path ctx = {}) {
    ks1::Step s; s.rule = r; s.context = std::move(ctx); return s;
}

// --- the harness: a derivation under construction ---------------------------
// Owns the live formula `cur` (== replay(⊤, steps)) and the steps. Every mutator
// advances `cur` by replaying the new step(s), so a context Path is always taken
// against the real formula.
struct Seq {
    FormulaBuilder&        fb;
    FormulaHandle          cur;
    std::vector<ks1::Step> steps;

    explicit Seq(FormulaBuilder& f) : fb(f), cur(top(f)) {}

    util::ResultStatus emit(ks1::Step s) {
        auto r = ks1::replay(fb, cur, {s});
        if (r.is_error()) return std::move(r).error();
        cur = r.value();
        steps.push_back(std::move(s));
        return util::Ok();
    }
    util::ResultStatus emit(std::vector<ks1::Step> ss) {
        for (auto& s : ss) TRY(emit(std::move(s)));
        return util::Ok();
    }
    // Splice a translated child (its steps build ⊤ ⟶ denote(child)) under the
    // context `under` (∅ ⇒ the child IS this whole sequent).
    util::ResultStatus splice(std::vector<ks1::Step> child, const ks1::Path& under) {
        for (ks1::Step& s : child)
            s.context.insert(s.context.begin(), under.begin(), under.end());
        return emit(std::move(child));
    }
    // Reshape cur to the canonical denote(entries) (boundary-aware).
    util::ResultStatus reconcile(const std::vector<FormulaHandle>& entries) {
        TRY_ASSIGN(rs, reconcile_to(fb, cur, entries));
        return emit(std::move(rs));
    }
};

// Reshape a translated node so entry `x` is its LAST entry (so a branch reads
// (Γ)∨x). Used by ∧R / ∨R to expose the principal as the rightmost disjunct.
util::Result<Tr> move_to_last(FormulaBuilder& fb, Tr t, FormulaHandle x) {
    std::size_t k = last_index_of(t.entries, x);
    if (k == kNone) return MAKE_ERROR << "lkr_to_ks1: node lacks the principal";
    if (k + 1 == t.entries.size()) return t;             // already last
    std::vector<FormulaHandle> order = t.entries;
    order.erase(order.begin() + k);
    order.push_back(x);
    Seq s(fb);
    TRY(s.emit(std::move(t.steps)));
    TRY(s.reconcile(order));
    return Tr{std::move(s.steps), std::move(order)};
}

// Group entries A and B into the single ∨-entry A∨B: reconcile so B sits just
// after A (left-assoc), then one AssocOr brackets the pair. Returns the new
// entries. Shared by ∨R (keep the group) and the contraction in RDuplicate.
util::Result<std::vector<FormulaHandle>> group_pair(
    Seq& s, std::vector<FormulaHandle> e, FormulaHandle A, FormulaHandle B) {
    std::size_t ia = index_of(e, A);
    std::size_t ib = index_of(e, B, ia);
    if (ia == kNone || ib == kNone)
        return MAKE_ERROR << "lkr_to_ks1: group_pair missing A/B";
    std::vector<FormulaHandle> order = e;
    order.erase(order.begin() + ib);
    const std::size_t i = ib < ia ? ia - 1 : ia;         // A's index after erase
    order.insert(order.begin() + i + 1, B);
    TRY(s.reconcile(order));                             // cur = denote(order)
    const std::size_t n = order.size();
    if (i > 0)                                           // (P∨A)∨B → P∨(A∨B)
        TRY(s.emit(eqv_step(ks1::EqRule::AssocOr, ks1::Path(n - 2 - i, ks1::Dir::Left))));
    std::vector<FormulaHandle> entries = std::move(order);
    entries[i] = s.fb.make_or(A, B);
    entries.erase(entries.begin() + i + 1);
    return entries;
}

util::Result<Tr> tr(FormulaBuilder& fb, const lce::Deriv& d,
                    const std::vector<var_index>& env);          // fwd (recursion)

// ===== the HSW translation table — one macro per LK rule ====================

// ax ⊢ Γ closing on the dual pair {a,b}: Ai introduces α∨ᾱ, every OTHER entry is
// weakened in (the axiom closes on the pair alone), giving denote([α,ᾱ,…]).
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RAx& ax,
                       const std::vector<var_index>& env) {
    FormulaHandle la = localize(fb, d.conclusion[ax.a], env);
    FormulaHandle lb = localize(fb, d.conclusion[ax.b], env);
    FormulaHandle pos = is_negative_literal(la) ? lb : la;
    FormulaHandle neg = is_negative_literal(la) ? la : lb;
    Seq s(fb);
    ks1::Step ai = rule_step(ks1::Rule::Ai); ai.f_param = pos;
    TRY(s.emit(ai));                                     // ⊤ → α∨ᾱ
    std::vector<FormulaHandle> entries{pos, neg};
    for (std::size_t i = 0; i < d.conclusion.size(); ++i) {
        if (i == ax.a || i == ax.b) continue;
        FormulaHandle e = localize(fb, d.conclusion[i], env);
        ks1::Step w = rule_step(ks1::Rule::W); w.f_param = e;
        TRY(s.emit(w));                                  // F → F∨entry
        entries.push_back(e);
    }
    return Tr{std::move(s.steps), std::move(entries)};
}

// ∨R: ⊢ Γ,A,B ⊢ Γ,A∨B. Translate the child, then group its A and B into A∨B.
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv&, const lce::ROr& orr,
                       const std::vector<var_index>& env) {
    FormulaHandle A = localize(fb, orr.child->conclusion[orr.principal], env);
    FormulaHandle B = localize(fb, orr.child->conclusion.back(), env);
    TRY_ASSIGN(child, tr(fb, *orr.child, env));
    Seq s(fb);
    TRY(s.emit(std::move(child.steps)));                 // cur = denote(child)
    TRY_ASSIGN(entries, group_pair(s, std::move(child.entries), A, B));
    return Tr{std::move(s.steps), std::move(entries)};
}

// Exchange is free under ≡ (entries are order-free) — pass the child through.
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv&, const lce::RExchange& ex,
                       const std::vector<var_index>& env) {
    return tr(fb, *ex.child, env);
}

// ∧R: ⊢ Γ_L,φ and ⊢ Γ_R,ψ ⊢ Γ_L,Γ_R,φ∧ψ. Build (Γ_L∨φ)∧(Γ_R∨ψ) via Tu+splices,
// then the BINARY switch sequence to ((φ∧ψ)∨Γ_L)∨Γ_R, then reconcile. Each Sw is
// binary (its ∨ is the right conjunct, B/C opaque) — see ks1::Step `Sw`.
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RAnd& andr,
                       const std::vector<var_index>& env) {
    const lce::Deriv* L = andr.left.get();
    const lce::Deriv* R = andr.right.get();
    const bool emptyL = L->conclusion.size() == 1;       // Γ_L = ∅ (just φ)
    const bool emptyR = R->conclusion.size() == 1;       // Γ_R = ∅ (just ψ)
    FormulaHandle phi = localize(fb, L->conclusion.back(), env);
    FormulaHandle psi = localize(fb, R->conclusion.back(), env);

    TRY_ASSIGN(LR, tr(fb, *L, env));  TRY_ASSIGN(LL, move_to_last(fb, std::move(LR), phi));
    TRY_ASSIGN(RR, tr(fb, *R, env));  TRY_ASSIGN(RL, move_to_last(fb, std::move(RR), psi));

    Seq s(fb);
    TRY(s.emit(rule_step(ks1::Rule::Tu)));               // ⊤ → ⊤∧⊤
    TRY(s.splice(std::move(LL.steps), {ks1::Dir::Left}));   // → (Γ_L∨φ)∧⊤
    TRY(s.splice(std::move(RL.steps), {ks1::Dir::Right}));  // → (Γ_L∨φ)∧(Γ_R∨ψ)

    using P = ks1::Path; using D = ks1::Dir; using E = ks1::EqRule;
    auto sw = [&] { return s.emit(rule_step(ks1::Rule::Sw)); };   // ∨ on the right
    if (!emptyL && !emptyR) {
        TRY(s.emit(eqv_step(E::CommOr, P{D::Right})));       // (Γ_R∨ψ)→(ψ∨Γ_R)
        TRY(s.emit(rule_step(ks1::Rule::Sw)));               // → ((Γ_L∨φ)∧ψ)∨Γ_R  [B=ψ]
        TRY(s.emit(eqv_step(E::CommOr, P{D::Left, D::Left})));// (Γ_L∨φ)→(φ∨Γ_L)
        TRY(s.emit(eqv_step(E::CommAnd, P{D::Left})));       // → (ψ∧(φ∨Γ_L))∨Γ_R
        TRY(s.emit(rule_step(ks1::Rule::Sw, P{D::Left})));   // → ((ψ∧φ)∨Γ_L)∨Γ_R  [B=φ]
        TRY(s.emit(eqv_step(E::CommAnd, P{D::Left, D::Left})));// (ψ∧φ)→(φ∧ψ)
    } else if (emptyL && !emptyR) {
        TRY(s.emit(eqv_step(E::CommOr, P{D::Right})));       // (Γ_R∨ψ)→(ψ∨Γ_R)
        TRY(sw());                                           // φ∧(ψ∨Γ_R) → (φ∧ψ)∨Γ_R
    } else if (!emptyL && emptyR) {
        TRY(s.emit(eqv_step(E::CommOr, P{D::Left})));        // (Γ_L∨φ)→(φ∨Γ_L)
        TRY(s.emit(eqv_step(E::CommAnd, {})));               // → ψ∧(φ∨Γ_L)
        TRY(sw());                                           // → (ψ∧φ)∨Γ_L
        TRY(s.emit(eqv_step(E::CommAnd, P{D::Left})));       // (ψ∧φ)→(φ∧ψ)
    }   // emptyL && emptyR: cur = φ∧ψ already.

    std::vector<FormulaHandle> entries{fb.make_and(phi, psi)};
    entries.insert(entries.end(), LL.entries.begin(), LL.entries.end() - 1);  // Γ_L
    entries.insert(entries.end(), RL.entries.begin(), RL.entries.end() - 1);  // Γ_R
    TRY(s.reconcile(entries));
    return Tr{std::move(s.steps), std::move(entries)};
}

// ∀R: ⊢ Γ,φ[eigen] ⊢ Γ,∀x.φ. ForallUnit gives ∀x.t; the child is translated
// already under the binder (env ++ [eigen], so its steps are born with the
// eigenvar as gen0 — no post-hoc rebind) and spliced under [Down], building
// ∀x.((Γ)∨φ); a DistForall then pulls (Γ) back out (x∉Γ — the eigenvar
// condition), which decrements Γ's free gens, landing them in the PARENT env.
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RForall& far,
                       const std::vector<var_index>& env) {
    const std::size_t pr = far.principal;
    FormulaHandle quant = localize(fb, d.conclusion[pr], env);   // ∀x.φ (parent env)
    const Formula& qf = quant.get();
    if (!(qf.is_quantified() && qf.as_quantified().op == Op::Forall))
        return MAKE_ERROR << "lkr_to_ks1: RForall principal is not a ∀";
    const lce::Deriv* child = far.child.get();

    std::vector<var_index> cenv = env;                   // child env = env ++ [eigen]
    cenv.push_back(far.eigen);

    std::vector<FormulaHandle> delta;                    // Γ in CHILD env (for iso)
    for (std::size_t i = 0; i < child->conclusion.size(); ++i)
        if (i != pr) delta.push_back(localize(fb, child->conclusion[i], cenv));
    const bool emptyG = delta.empty();

    TRY_ASSIGN(childRes, tr(fb, *child, cenv));
    std::vector<ks1::Step> body = std::move(childRes.steps);
    if (!emptyG) {                                       // reshape to (Γ)∨φ
        std::vector<FormulaHandle> iso = delta;
        iso.push_back(localize(fb, child->conclusion[pr], cenv));
        TRY_ASSIGN(rs, reconcile_to(fb, denote(fb, childRes.entries), iso));
        body.insert(body.end(), rs.begin(), rs.end());
    }

    Seq s(fb);
    TRY(s.emit(rule_step(ks1::Rule::ForallUnit)));       // ⊤ → ∀x.t
    TRY(s.splice(std::move(body), {ks1::Dir::Down}));    // → ∀x.((Γ)∨φ)  (or ∀x.φ)
    if (!emptyG) {
        TRY(s.emit(eqv_step(ks1::EqRule::CommOr, ks1::Path{ks1::Dir::Down})));  // → ∀x.(φ∨(Γ))
        ks1::Step dist = rule_step(ks1::Rule::Eqv);
        dist.eq = ks1::EqRule::DistForall; dist.dir = ks1::EqDir::Forward;
        TRY(s.emit(dist));                               // → (∀x.φ)∨(Γ)
    }
    // Output entries are in the PARENT env: quant is read at parent level; each Γ
    // entry's free gens were decremented by the DistForall pull-out (cenv→env).
    std::vector<FormulaHandle> entries{quant};
    for (std::size_t i = 0; i < child->conclusion.size(); ++i)
        if (i != pr) entries.push_back(localize(fb, child->conclusion[i], env));
    TRY(s.reconcile(entries));
    return Tr{std::move(s.steps), std::move(entries)};
}

// ∃R: ⊢ Γ,φ[x:=t] ⊢ Γ,∃x.φ. Apply Ex at the instance entry φ[t] (matched mod ≡).
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RExists& exr,
                       const std::vector<var_index>& env) {
    const std::size_t pr = exr.principal;
    FormulaHandle quant = localize(fb, d.conclusion[pr], env);    // ∃x.φ
    const Formula& qf = quant.get();
    if (!(qf.is_quantified() && qf.as_quantified().op == Op::Exists))
        return MAKE_ERROR << "lkr_to_ks1: RExists principal is not an ∃";
    FormulaHandle qbody = qf.as_quantified().body;       // φ (gen0 = x)
    Term witness = localize(fb, exr.witness, env);
    FormulaHandle inst = fb.instantiate_gen(qbody, witness);      // φ[t]

    TRY_ASSIGN(childRes, tr(fb, *exr.child, env));
    Seq s(fb);
    TRY(s.emit(std::move(childRes.steps)));
    std::vector<FormulaHandle> entries = std::move(childRes.entries);
    std::size_t idx = index_of(entries, inst);
    if (idx == kNone)
        return MAKE_ERROR << "lkr_to_ks1: RExists child lacks the instance φ[t]";
    ks1::Step ex = rule_step(ks1::Rule::Ex, path_to_entry(idx, entries.size()));
    ex.f_param = qbody; ex.t_param = witness;
    TRY(s.emit(ex));                                     // φ[t] → ∃x.φ
    entries[idx] = quant;
    return Tr{std::move(s.steps), std::move(entries)};
}

// W: ⊢ Γ ⊢ Γ,φ. Prove the core, then weaken φ in as a fresh entry (order free).
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RWeaken& w,
                       const std::vector<var_index>& env) {
    FormulaHandle weakened = localize(fb, d.conclusion[w.idx], env);
    TRY_ASSIGN(childRes, tr(fb, *w.child, env));
    Seq s(fb);
    TRY(s.emit(std::move(childRes.steps)));
    ks1::Step ws = rule_step(ks1::Rule::W); ws.f_param = weakened;
    TRY(s.emit(ws));                                     // F → F∨φ
    std::vector<FormulaHandle> entries = std::move(childRes.entries);
    entries.push_back(weakened);
    return Tr{std::move(s.steps), std::move(entries)};
}

// Contraction: ⊢ Γ,φ,φ ⊢ Γ,φ. Prove the doubled core, group the two φ copies as
// φ∨φ, then contract (medials + Ac) on that subtree.
util::Result<Tr> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RDuplicate& dup,
                       const std::vector<var_index>& env) {
    FormulaHandle X = localize(fb, d.conclusion[dup.src], env);
    TRY_ASSIGN(childRes, tr(fb, *dup.child, env));
    Seq s(fb);
    TRY(s.emit(std::move(childRes.steps)));

    // Group the two copies into the entry X∨X (at index i), then contract it.
    std::size_t i0 = index_of(childRes.entries, X);
    std::size_t j0 = index_of(childRes.entries, X, i0);
    if (i0 == kNone || j0 == kNone)
        return MAKE_ERROR << "lkr_to_ks1: RDuplicate child lacks two copies of X";
    TRY_ASSIGN(grouped, group_pair(s, std::move(childRes.entries), X, X));
    std::size_t gi = index_of(grouped, fb.make_or(X, X));
    TRY_ASSIGN(con, contract_steps(fb, X));              // X∨X → X
    ks1::Path at = path_to_entry(gi, grouped.size());
    for (ks1::Step& cs : con) {
        cs.context.insert(cs.context.begin(), at.begin(), at.end());
        TRY(s.emit(std::move(cs)));
    }
    grouped[gi] = X;                                     // the contracted entry
    return Tr{std::move(s.steps), std::move(grouped)};
}

// --- rules that a CUT-FREE goal derivation never contains ------------------
// std::visit forces an arm for every variant alternative; these reject cleanly.
util::Result<Tr> macro(FormulaBuilder&, const lce::Deriv&, const lce::ROne&,
                       const std::vector<var_index>&) {
    return MAKE_ERROR << "lkr_to_ks1: ROne (⊤ literal) unsupported";
}
util::Result<Tr> macro(FormulaBuilder&, const lce::Deriv&, const lce::RLemma&,
                       const std::vector<var_index>&) {
    return MAKE_ERROR << "lkr_to_ks1: RLemma must be internalized before translation";
}
util::Result<Tr> macro(FormulaBuilder&, const lce::Deriv&, const lce::RContract&,
                       const std::vector<var_index>&) {
    return MAKE_ERROR << "lkr_to_ks1: RContract should be RDuplicate after build()";
}
util::Result<Tr> macro(FormulaBuilder&, const lce::Deriv&, const lce::RCut&,
                       const std::vector<var_index>&) {
    return MAKE_ERROR << "lkr_to_ks1: input is not cut-free (RCut present)";
}

// --- dispatch + a thin step-budget guard -----------------------------------
struct Budget { long long max = 0; };
thread_local Budget g_budget;

util::Result<Tr> tr(FormulaBuilder& fb, const lce::Deriv& d,
                    const std::vector<var_index>& env) {
    auto r = std::visit([&](const auto& rule) { return macro(fb, d, rule, env); }, d.rule);
    if (r.ok() && g_budget.max > 0 &&
        static_cast<long long>(r.value().steps.size()) > g_budget.max)
        return MAKE_ERROR << "lkr_to_ks1: step budget exceeded ("
                          << r.value().steps.size() << " > " << g_budget.max << ")";
    return r;
}

}  // namespace

util::Result<ks1::Derivation> lkr_to_ks1(FormulaBuilder& fb,
                                         const lce::Deriv& cutfree) {
    if (cutfree.conclusion.size() != 1)
        return MAKE_ERROR << "lkr_to_ks1: expected a single-formula (closed) goal "
                             "sequent, got " << cutfree.conclusion.size()
                          << " formulas";
    FormulaHandle goal = cutfree.conclusion[0];

    g_budget = Budget{};
    if (const char* b = std::getenv("LKR_TO_KS1_MAX_STEPS")) g_budget.max = std::atoll(b);
    TRY_ASSIGN(result, tr(fb, cutfree, {}));
    if (std::getenv("LKR_TO_KS1_STATS")) {
        long long eqv = 0;
        for (const auto& s : result.steps) if (s.rule == ks1::Rule::Eqv) ++eqv;
        std::cerr << "[l2k stats] total=" << result.steps.size()
                  << " EQV=" << eqv << " NON-EQV=" << (result.steps.size() - eqv)
                  << std::endl;
    }
    return ks1::Derivation{top(fb), goal, std::move(result.steps)};
}

}  // namespace logic::proof::translate::lkr_to_ks1
