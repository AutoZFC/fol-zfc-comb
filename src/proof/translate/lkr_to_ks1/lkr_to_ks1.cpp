#include "src/proof/translate/lkr_to_ks1/lkr_to_ks1.h"

#include "src/proof/translate/lkr_to_ks1/reconcile.h"

#include <cstdlib>
#include <iostream>
#include <variant>
#include <vector>

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// The result of translating one node: the KS1 steps and the sequent's ENTRIES
// (LKR_TO_KS1_DESIGN.md §K6.5). Invariant: replay(⊤, steps) == denote(entries)
// by handle, where denote left-associates the entries. `entries` is an
// order-free bag of opaque subtrees — it need NOT match `d.conclusion`'s order;
// rules locate entries by identity. A ∨-valued entry is kept GROUPED (never
// flattened) so its boundary survives.
struct Tr {
    std::vector<ks1::Step>     steps;
    std::vector<FormulaHandle> entries;
};

// --- Diagnostic instrumentation (gated on env; zero cost by default) -------
// `tr` is a thin wrapper around `tr_impl` that tracks recursion depth, total
// emitted steps, and per-rule step tallies, with an optional hard budget that
// turns a translation blowup into a clean error instead of an OOM. Set
// LKR_TO_KS1_MAX_STEPS to cap; LKR_TO_KS1_TRACE=1 to log entry/exit per call.
util::Result<Tr> tr_impl(FormulaBuilder& fb, const lce::Deriv& d);

int rule_idx(const lce::Deriv& d) {
    if (std::get_if<lce::RAx>(&d.rule))        return 0;
    if (std::get_if<lce::ROr>(&d.rule))        return 1;
    if (std::get_if<lce::RExchange>(&d.rule))  return 2;
    if (std::get_if<lce::RAnd>(&d.rule))       return 3;
    if (std::get_if<lce::RForall>(&d.rule))    return 4;
    if (std::get_if<lce::RExists>(&d.rule))    return 5;
    if (std::get_if<lce::RWeaken>(&d.rule))    return 6;
    if (std::get_if<lce::RDuplicate>(&d.rule)) return 7;
    return 8;
}
const char* kRuleName[9] = {"RAx", "ROr", "RExchange", "RAnd", "RForall",
                            "RExists", "RWeaken", "RDuplicate", "R?"};

struct TrStats {
    long long calls = 0, total = 0, per_rule[9] = {}, per_rule_calls[9] = {};
    int depth = 0, max_depth = 0, max_conc = 0;
    std::vector<long long> child_sum;   // child_sum[d] = Σ sizes returned at depth d+1
    long long budget = 0;
    bool trace = false;
    std::string per_rule_dump() const {
        std::string s;                  // per-rule SELF-steps (excl. children) / node count
        for (int i = 0; i < 9; ++i)
            if (per_rule[i] || per_rule_calls[i])
                s += std::string(kRuleName[i]) + "=" + std::to_string(per_rule[i]) +
                     "/" + std::to_string(per_rule_calls[i]) + "n ";
        return s;
    }
};
thread_local TrStats g_tr;

util::Result<Tr> tr(FormulaBuilder& fb, const lce::Deriv& d) {
    ++g_tr.calls;
    if (++g_tr.depth > g_tr.max_depth) g_tr.max_depth = g_tr.depth;
    const int mydepth = g_tr.depth, ri = rule_idx(d);
    ++g_tr.per_rule_calls[ri];
    if (static_cast<int>(d.conclusion.size()) > g_tr.max_conc)
        g_tr.max_conc = static_cast<int>(d.conclusion.size());
    if (static_cast<int>(g_tr.child_sum.size()) <= mydepth)
        g_tr.child_sum.resize(mydepth + 1, 0);
    g_tr.child_sum[mydepth] = 0;        // reset: accumulate MY children's returned sizes
    if (g_tr.trace)
        std::cerr << "[l2k] >> d=" << mydepth << " " << kRuleName[ri]
                  << " conc=" << d.conclusion.size() << " calls=" << g_tr.calls
                  << std::endl;
    auto r = tr_impl(fb, d);
    --g_tr.depth;
    if (r.ok()) {
        const long long n = static_cast<long long>(r.value().steps.size());
        const long long self = n - g_tr.child_sum[mydepth];   // steps THIS node added
        g_tr.per_rule[ri] += self;
        if (mydepth >= 1) g_tr.child_sum[mydepth - 1] += n;    // report up to parent
        if (mydepth == 1) g_tr.total = n;                      // root = true total
        if (g_tr.trace)
            std::cerr << "[l2k] << d=" << mydepth << " " << kRuleName[ri]
                      << " ret=" << n << " self=" << self << std::endl;
        if (g_tr.budget > 0 && n > g_tr.budget)               // guard on real size
            return MAKE_ERROR << "lkr_to_ks1: step budget exceeded ("
                              << n << " > " << g_tr.budget
                              << ") at " << kRuleName[ri] << " depth " << mydepth
                              << "; max_depth=" << g_tr.max_depth
                              << "; max_conc=" << g_tr.max_conc
                              << "; by-rule(self): " << g_tr.per_rule_dump();
    }
    return r;
}

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

// Path from the root of denote(entries) (the n-entry LEFT-associated ∨-tree) to
// the entry at index `i`. denote = (…((e₀∨e₁)∨e₂)…)∨e_{n-1}, so e_{n-1} sits at
// [Right], and every earlier entry is reached by descending [Left] first:
//   i == n-1 : [Right]            (n ≥ 2)
//   i  < n-1 : [Left]^(n-1-i) ++ [Right]   (i ≥ 1)
//   i == 0   : [Left]^(n-1)       (the all-left spine; empty when n == 1)
[[maybe_unused]] ks1::Path path_to_entry(std::size_t i, std::size_t n) {
    ks1::Path p(n - 1 - i, ks1::Dir::Left);
    if (i != 0) p.push_back(ks1::Dir::Right);
    return p;
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

ks1::Step tu_root() {
    ks1::Step s;
    s.rule = ks1::Rule::Tu;           // A → A∧t
    return s;
}

// tr(d): KS1 steps realizing t ⟶ (d.conclusion), where (Γ) is the
// left-associated disjunction of the sequent (LKR_TO_KS1_DESIGN.md §"The
// sequent–formula correspondence"). Reconciliation (reorder_steps/equiv_steps)
// keeps each node's output at denote(node) exactly.
util::Result<Tr> tr_impl(FormulaBuilder& fb, const lce::Deriv& d) {
    // --- RAx: axiom ⊢ Γ closing on the dual pair at {a,b}. ---------------
    // Ai introduces α∨ᾱ; any OTHER sequent entries are weakened in (the axiom
    // closes on the pair alone — implicit weakening), each a Φ2 W step; then
    // reconcile to denote(node). A 2-literal axiom is the no-weakening case.
    if (const auto* ax = std::get_if<lce::RAx>(&d.rule)) {
        FormulaHandle lit_a = d.conclusion[ax->a];
        FormulaHandle lit_b = d.conclusion[ax->b];
        FormulaHandle positive = is_negative_literal(lit_a) ? lit_b : lit_a;
        FormulaHandle negative = is_negative_literal(lit_a) ? lit_a : lit_b;
        std::vector<ks1::Step> steps{ai_step(positive)};        // t → α∨ᾱ
        // entries = [α, ᾱ] ++ weakened-in others. denote of this left-assoc list
        // is exactly (α∨ᾱ)∨e₁∨… = what Ai+W produce, so NO reconcile; the pair is
        // listed ungrouped so a parent can still find α / ᾱ by identity.
        std::vector<FormulaHandle> entries{positive, negative};
        for (std::size_t i = 0; i < d.conclusion.size(); ++i) {
            if (i == ax->a || i == ax->b) continue;             // the axiom pair
            ks1::Step ws; ws.rule = ks1::Rule::W; ws.f_param = d.conclusion[i];
            steps.push_back(ws);                                // F → F∨entry
            entries.push_back(d.conclusion[i]);
        }
        return Tr{std::move(steps), std::move(entries)};
    }

    // --- ROr: build splits node[pr]=A∨B into A at pr and B appended. Move B
    // back adjacent to A (pure permutation) then one AssocOr regroups (A∨B) at
    // pr — local, not equiv_steps canon over the whole sequent. ---
    if (const auto* orr = std::get_if<lce::ROr>(&d.rule)) {
        const lce::Deriv* child = orr->child.get();
        const std::size_t pr = orr->principal;
        TRY_ASSIGN(childRes, tr(fb, *child));
        auto steps = std::move(childRes.steps);
        FormulaHandle A = child->conclusion[pr];
        FormulaHandle B = child->conclusion.back();
        std::vector<FormulaHandle> inter;                 // [node…, A, B at pr+1, …]
        for (std::size_t i = 0; i < d.conclusion.size(); ++i) {
            inter.push_back(d.conclusion[i]);
            if (i == pr) { inter.back() = A; inter.push_back(B); }
        }
        TRY_ASSIGN(r, reorder_steps(fb, childRes.entries, inter));
        steps.insert(steps.end(), r.begin(), r.end());
        if (pr > 0) {                                     // (prefix∨A)∨B → prefix∨(A∨B)
            const std::size_t N = d.conclusion.size();
            ks1::Step a; a.rule = ks1::Rule::Eqv;
            a.eq = ks1::EqRule::AssocOr; a.dir = ks1::EqDir::Forward;
            a.context = ks1::Path(N - 1 - pr, ks1::Dir::Left);
            steps.push_back(a);
        }
        return Tr{std::move(steps), d.conclusion};
    }
    if (const auto* ex = std::get_if<lce::RExchange>(&d.rule)) {
        // A pure entry permutation. Entry ORDER carries no meaning under modulo-≡
        // checking (rules locate entries by identity; the final endpoint is
        // compared order-free), so emit NOTHING — pass the child's steps and
        // entries through unchanged (LKR_TO_KS1_DESIGN.md §K6.5).
        return tr(fb, *ex->child);
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

        TRY_ASSIGN(LRes, tr(fb, *L));     // t ⟶ (Γ_L)∨φ (or φ if Γ_L=∅)
        TRY_ASSIGN(RRes, tr(fb, *R));     // t ⟶ (Γ_R)∨ψ (or ψ if Γ_R=∅)
        FormulaHandle phi = L->conclusion.back();
        FormulaHandle psi = R->conclusion.back();
        // The switch sequence needs φ / ψ as the RIGHTMOST entry of F_L / F_R, so
        // that the branch is (P∨φ) / (Q∨ψ). Entry order is free, so move a φ-entry
        // (resp. ψ) to the end — a bounded reorder over the entry list, not a leaf
        // canonicalization.
        for (int side = 0; side < 2; ++side) {
            std::vector<FormulaHandle>& e  = side ? RRes.entries : LRes.entries;
            std::vector<ks1::Step>&     st = side ? RRes.steps   : LRes.steps;
            FormulaHandle x = side ? psi : phi;
            std::size_t k = e.size();
            for (std::size_t t = 0; t < e.size(); ++t) if (e[t] == x) k = t;  // last
            if (k == e.size())
                return MAKE_ERROR << "lkr_to_ks1: RAnd branch lacks its principal";
            if (k + 1 != e.size()) {                          // not already last
                std::vector<FormulaHandle> tgt = e;
                tgt.erase(tgt.begin() + k);
                tgt.push_back(x);
                TRY_ASSIGN(r, reorder_steps(fb, e, tgt));
                st.insert(st.end(), r.begin(), r.end());
                e = std::move(tgt);
            }
        }
        auto stepsL = std::move(LRes.steps);
        auto stepsR = std::move(RRes.steps);
        prefix_context(stepsL, ks1::Dir::Left);
        prefix_context(stepsR, ks1::Dir::Right);
        std::vector<ks1::Step> steps{tu_root()};                    // t → t∧t
        steps.insert(steps.end(), stepsL.begin(), stepsL.end());    // → (P∨φ)∧t
        steps.insert(steps.end(), stepsR.begin(), stepsR.end());    // → (P∨φ)∧(Q∨ψ)

        using P = ks1::Path; using D = ks1::Dir; using E = ks1::EqRule;
        if (!emptyL && !emptyR) {
            // (P∨φ)∧(Q∨ψ) ⟶ ((φ∧ψ)∨P)∨Q  (design doc steps 4–9).
            steps.push_back(eqv_step(E::CommOr, P{D::Right}));       // (Q∨ψ)→(ψ∨Q)
            { ks1::Step sw = sw_step({}); sw.operands = {1};        // ∨-operand = (ψ∨Q)
              steps.push_back(sw); }                                // → ((P∨φ)∧ψ)∨Q
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
                FormulaHandle Pf = denote(fb, {LRes.entries.begin(), LRes.entries.end() - 1});
                FormulaHandle Qf = denote(fb, {RRes.entries.begin(), RRes.entries.end() - 1});
                cur = fb.make_or(fb.make_or(conj, Pf), Qf);
            } else if (emptyL) {
                FormulaHandle Qf = denote(fb, {RRes.entries.begin(), RRes.entries.end() - 1});
                cur = fb.make_or(conj, Qf);
            } else {
                FormulaHandle Pf = denote(fb, {LRes.entries.begin(), LRes.entries.end() - 1});
                cur = fb.make_or(conj, Pf);
            }
        }
        TRY_ASSIGN(rec, equiv_steps(fb, cur, denote(fb, d.conclusion)));
        steps.insert(steps.end(), rec.begin(), rec.end());
        return Tr{std::move(steps), d.conclusion};
    }

    // --- RForall: ⊢ Γ, φ[eigen] ⊢ Γ, ∀x.φ. ------------------------------
    // ForallUnit gives ∀x.t; the child derivation runs under [Down] with the
    // eigenvariable rebound to the ∀'s bound var (depth-aware fixed(eigen)→gen),
    // building ∀x.(child). With Γ=∅ that already is the goal. With Γ≠∅ the body
    // is ∀x.((Δ)∨φ), so a DistForall pulls Δ back out: comm to ∀x.(φ∨(Δ)), then
    // ∀x.(A∨B)→(∀x.A)∨B (x∉Δ since the eigenvar is fresh), then reconcile.
    if (const auto* far = std::get_if<lce::RForall>(&d.rule)) {
        const std::size_t pr = far->principal;
        FormulaHandle quant = d.conclusion[pr];                 // ∀x.φ
        const Formula& qf = quant.get();
        if (!(qf.is_quantified() && qf.as_quantified().op == Op::Forall))
            return MAKE_ERROR << "lkr_to_ks1: RForall principal is not a ∀";
        const lce::Deriv* child = far->child.get();

        std::vector<FormulaHandle> delta;                       // Γ (entries ≠ pr)
        for (std::size_t i = 0; i < child->conclusion.size(); ++i)
            if (i != pr) delta.push_back(child->conclusion[i]);
        const bool emptyG = delta.empty();

        TRY_ASSIGN(childRes, tr(fb, *child));                   // → denote(child)
        auto steps = std::move(childRes.steps);
        // Reshape (Δ),φ so φ is the rightmost disjunct — BEFORE wrapping, on the
        // fixed-eigenvar formulas (so the ∀-body's reshape target is known).
        if (!emptyG) {
            FormulaHandle iso = fb.make_or(denote(fb, delta), child->conclusion[pr]);
            TRY_ASSIGN(r, equiv_steps(fb, denote(fb, childRes.entries), iso));
            steps.insert(steps.end(), r.begin(), r.end());
        }
        // Wrap everything so far in ∀x: prefix [Down] + rebind the eigenvar.
        for (ks1::Step& s : steps) {
            int depth = 0;
            for (ks1::Dir dd : s.context) if (dd == ks1::Dir::Down) ++depth;
            if (s.f_param.valid()) {
                int fd = depth + (s.rule == ks1::Rule::Ex ? 1 : 0);  // Ex body deeper
                s.f_param = fb.translate_term(s.f_param, Term::fixed(far->eigen),
                                              Term::generalized(fd));
            }
            if (s.rule == ks1::Rule::Ex)
                s.t_param = fb.translate_in_term(s.t_param, Term::fixed(far->eigen),
                                                 Term::generalized(depth));
            s.context.insert(s.context.begin(), ks1::Dir::Down);
        }
        ks1::Step fu; fu.rule = ks1::Rule::ForallUnit;          // t → ∀x.t
        std::vector<ks1::Step> out{fu};
        out.insert(out.end(), steps.begin(), steps.end());      // → ∀x.(child[bound])

        if (!emptyG) {
            // ∀x.((Δ)∨φ) → ∀x.(φ∨(Δ)) → (∀x.φ)∨(Δ) → denote(node).
            out.push_back(eqv_step(ks1::EqRule::CommOr, ks1::Path{ks1::Dir::Down}));
            ks1::Step dist; dist.rule = ks1::Rule::Eqv;
            dist.eq = ks1::EqRule::DistForall; dist.dir = ks1::EqDir::Forward;  // ctx {}
            out.push_back(dist);
            FormulaHandle afterDist = fb.make_or(quant, denote(fb, delta));
            TRY_ASSIGN(r2, equiv_steps(fb, afterDist, denote(fb, d.conclusion)));
            out.insert(out.end(), r2.begin(), r2.end());
        }
        return Tr{std::move(out), d.conclusion};
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

        TRY_ASSIGN(childRes, tr(fb, *child));                    // → denote(child)
        auto steps = std::move(childRes.steps);
        // Apply Ex IN PLACE at the instance entry φ[t] — no reorder (order free).
        std::vector<FormulaHandle> entries = std::move(childRes.entries);
        std::size_t idx = entries.size();
        for (std::size_t i = 0; i < entries.size(); ++i) if (entries[i] == inst) idx = i;
        if (idx == entries.size())
            return MAKE_ERROR << "lkr_to_ks1: RExists child lacks the instance φ[t]";
        ks1::Step ex; ex.rule = ks1::Rule::Ex; ex.f_param = body;
        ex.t_param = exr->witness;
        ex.context = path_to_entry(idx, entries.size());
        steps.push_back(ex);                                     // φ[t] → ∃x.φ
        entries[idx] = quant;
        return Tr{std::move(steps), std::move(entries)};
    }

    // --- RWeaken: ⊢ Γ ⊢ Γ,φ (the weakened-in φ is at idx). ---------------
    // Φ2 resource step: prove the linear core for the child (Γ without φ), then
    // W in φ (S{A}/S{A∨B}) and reconcile to denote(node).
    if (const auto* w = std::get_if<lce::RWeaken>(&d.rule)) {
        const lce::Deriv* child = w->child.get();
        FormulaHandle weakened = d.conclusion[w->idx];
        TRY_ASSIGN(childRes, tr(fb, *child));              // Φ1: → denote(child)
        auto steps = std::move(childRes.steps);
        ks1::Step ws; ws.rule = ks1::Rule::W; ws.f_param = weakened;  // ctx {}
        steps.push_back(ws);                               // F → F∨φ
        // φ is appended as a fresh entry; order is free, so NO reorder.
        std::vector<FormulaHandle> entries = std::move(childRes.entries);
        entries.push_back(weakened);
        return Tr{std::move(steps), std::move(entries)};
    }

    // --- RDuplicate: ⊢ Γ,φ,φ ⊢ Γ,φ (the child has an extra copy of φ=node[src]
    // appended; this node contracts it back). -----------------------------
    // Φ1 proves the doubled core (denote(child) = denote(node) ∨ φ), then Φ2
    // reshapes the two φ copies adjacent as φ∨φ, contracts (contract_steps), and
    // reconciles to denote(node).
    if (const auto* dup = std::get_if<lce::RDuplicate>(&d.rule)) {
        const lce::Deriv* child = dup->child.get();
        FormulaHandle X = d.conclusion[dup->src];
        TRY_ASSIGN(childRes, tr(fb, *child));              // Φ1: → denote(child)
        auto steps = std::move(childRes.steps);

        // childRes.entries holds two copies of X. Bring the SECOND copy adjacent
        // to the first — a LOCAL move (O(distance), not a reorder of the whole
        // sequent into a canonical order) — group them as X∨X, and contract in
        // place with the fixed-context contractor, which touches only the X∨X
        // subtree and so preserves every other entry's grouping. Order is free,
        // so the rest of the sequent keeps its current order.
        const std::vector<FormulaHandle>& cur = childRes.entries;
        std::size_t i = SIZE_MAX, j = SIZE_MAX;
        for (std::size_t k = 0; k < cur.size(); ++k)
            if (cur[k] == X) { if (i == SIZE_MAX) i = k; else { j = k; break; } }
        if (j == SIZE_MAX)
            return MAKE_ERROR << "lkr_to_ks1: RDuplicate child lacks two copies of X";

        std::vector<FormulaHandle> target = cur;           // move copy j to i+1
        target.erase(target.begin() + j);
        target.insert(target.begin() + i + 1, X);
        TRY_ASSIGN(r1, reorder_steps(fb, cur, target));
        steps.insert(steps.end(), r1.begin(), r1.end());

        const std::size_t n = target.size();
        ks1::Path grp(n - 2 - i, ks1::Dir::Left);          // node holding {…,X,X}
        ks1::Path cpath = grp;
        if (i > 0) {                                       // (P∨X)∨X → P∨(X∨X)
            ks1::Step a; a.rule = ks1::Rule::Eqv;
            a.eq = ks1::EqRule::AssocOr; a.dir = ks1::EqDir::Forward;
            a.context = grp;
            steps.push_back(a);
            cpath.push_back(ks1::Dir::Right);
        }
        TRY_ASSIGN(con, contract_steps(fb, X));            // X∨X → X at cpath
        for (ks1::Step& s : con) {
            s.context.insert(s.context.begin(), cpath.begin(), cpath.end());
            steps.push_back(std::move(s));
        }
        std::vector<FormulaHandle> entries = cur;          // drop the second copy
        entries.erase(entries.begin() + j);
        return Tr{std::move(steps), std::move(entries)};
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

    g_tr = TrStats{};
    if (const char* b = std::getenv("LKR_TO_KS1_MAX_STEPS")) g_tr.budget = std::atoll(b);
    g_tr.trace = std::getenv("LKR_TO_KS1_TRACE") != nullptr;
    TRY_ASSIGN(result, tr(fb, cutfree));
    auto steps = std::move(result.steps);
    if (std::getenv("LKR_TO_KS1_STATS")) {
        long long eqv = 0;
        for (const auto& s : steps) if (s.rule == ks1::Rule::Eqv) ++eqv;
        std::cerr << "[l2k stats] total=" << g_tr.total << " nodes=" << g_tr.calls
                  << " max_depth=" << g_tr.max_depth << " max_conc=" << g_tr.max_conc
                  << " EQV=" << eqv << " NON-EQV=" << (g_tr.total - eqv)
                  << " by-rule(self): " << g_tr.per_rule_dump() << std::endl;
    }
    FormulaHandle top = fb.make_not(fb.make_bottom());   // ⊤ = ¬⊥
    return ks1::Derivation{top, goal, std::move(steps)};
}

}  // namespace logic::proof::translate::lkr_to_ks1
