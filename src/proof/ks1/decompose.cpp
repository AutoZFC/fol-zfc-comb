#include "src/proof/ks1/decompose.h"

#include "src/proof/ks1/checker.h"

#include <cstdio>
#include <cstdlib>
#include <optional>
#include <utility>
#include <vector>

namespace logic::proof::ks1 {

using util::Result;

bool is_mls1x(Rule r) {
    switch (r) {
        case Rule::ForallUnit: case Rule::Ai: case Rule::Tu:
        case Rule::Sw: case Rule::Mix: case Rule::Ex: case Rule::Eqv:
            return true;
        default:
            return false;
    }
}

bool is_resource(Rule r) {
    switch (r) {
        case Rule::W: case Rule::WForall: case Rule::Ac: case Rule::CForall:
        case Rule::M: case Rule::MForall: case Rule::MExists: case Rule::Eqv:
            return true;
        default:
            return false;
    }
}

namespace {

// A resource-only step (non-≡): marks the MLS1^X/resource boundary.
bool is_resource_only(Rule r) { return is_resource(r) && !is_mls1x(r); }

// Phase of a non-≡ rule (≡ is flexible and excluded from the order check).
Phase phase_of(Rule r) {
    switch (r) {
        case Rule::ForallUnit: case Rule::Ai: case Rule::Tu: return Phase::Axioms;
        case Rule::Sw: case Rule::Mix:                       return Phase::Linear;
        case Rule::Ex:                                       return Phase::Inst;
        case Rule::M: case Rule::MForall: case Rule::MExists: return Phase::Medial;
        case Rule::Ac: case Rule::CForall:                   return Phase::Contraction;
        case Rule::W: case Rule::WForall:                    return Phase::Weakening;
        case Rule::Eqv:  break;  // flexible; callers skip ≡
    }
    return Phase::Weakening;  // unreachable for non-≡
}

// Index of the first resource-only step (= derivation size if none).
size_t boundary_index(const Derivation& d) {
    for (size_t i = 0; i < d.steps.size(); ++i)
        if (is_resource_only(d.steps[i].rule)) return i;
    return d.steps.size();
}

}  // namespace

bool is_decomposed(const Derivation& d) {
    size_t b = boundary_index(d);
    // The bridge needs only the MLS1^X / resource BOUNDARY: every step before the
    // first resource-only step is MLS1^X (linear or ≡), every step from it on is
    // resource (or ≡). The paper's finer intra-half phase order (Axioms<Linear<
    // Inst, Medial<Contraction<Weakening) is NOT required — read_fonet (Φ1) and
    // read_skew (Φ2) each replay their half in order, robust to intra-half
    // arrangement, and CombVerifier is the soundness oracle. Dropping the
    // intra-half monotone check lets decompose stop once linear precedes resource
    // (it need not also sort medials before contractions, etc.).
    for (size_t i = 0; i < b; ++i)
        if (!is_mls1x(d.steps[i].rule)) return false;
    for (size_t i = b; i < d.steps.size(); ++i)
        if (!is_resource(d.steps[i].rule)) return false;
    return true;
}

// ---- constructive Thm 17: reorganize into decomposed form (DECOMPOSE_DESIGN.md)
namespace {

// Rewrite / search the binary+quantifier formula tree along a Path.
FormulaHandle put_at(FormulaBuilder& fb, FormulaHandle h, const Path& p, size_t i,
                     FormulaHandle sub) {
    if (i == p.size()) return sub;
    const Formula& f = h.get();
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        FormulaHandle nl = c.left, nr = c.right;
        if (p[i] == Dir::Left) nl = put_at(fb, c.left, p, i + 1, sub);
        else                   nr = put_at(fb, c.right, p, i + 1, sub);
        switch (c.op) {
            case Op::And: return fb.make_and(nl, nr);
            case Op::Or:  return fb.make_or(nl, nr);
            case Op::Not: return fb.make_not(nl);
            case Op::Bottom: return fb.make_bottom();
            default: return fb.make_or(nl, nr);
        }
    }
    if (f.is_quantified())
        return fb.make_quantified(f.as_quantified().op,
                                  put_at(fb, f.as_quantified().body, p, i + 1, sub));
    return sub;
}
bool is_prefix(const Path& p, const Path& q) {
    if (p.size() > q.size()) return false;
    for (size_t i = 0; i < p.size(); ++i) if (p[i] != q[i]) return false;
    return true;
}
FormulaHandle nav_at(FormulaHandle h, const Path& p) {
    for (Dir d : p) {
        const Formula& f = h.get();
        if (f.is_compound()) h = (d == Dir::Left) ? f.as_compound().left : f.as_compound().right;
        else if (f.is_quantified()) h = f.as_quantified().body;
        else return FormulaHandle{};
    }
    return h;
}
std::optional<Path> find_handle(FormulaHandle h, FormulaHandle target) {
    if (h == target) return Path{};
    const Formula& f = h.get();
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid())
            if (auto p = find_handle(c.left, target)) { p->insert(p->begin(), Dir::Left); return p; }
        if (c.right.valid())
            if (auto p = find_handle(c.right, target)) { p->insert(p->begin(), Dir::Right); return p; }
    } else if (f.is_quantified()) {
        if (auto p = find_handle(f.as_quantified().body, target)) { p->insert(p->begin(), Dir::Down); return p; }
    }
    return std::nullopt;
}

// Swap adjacent steps x (earlier) and y (later), given Fx = formula before x, so
// that the pair (y′, x′) replayed from Fx reaches the SAME formula as (x, y).
// y keeps its rule/params/context (its redex pre-exists x, else this fails);
// x′ keeps its rule/params but its context is remapped through y by marking x's
// redex with a fresh sentinel atom, applying y, and locating the sentinel. The
// result is self-VERIFIED by replay — any case not covered (binder crossing,
// x created y's redex, AC chains merged by y) fails the check and returns
// nullopt, so the caller safely leaves the pair in place (no wrong proof).
const char* rule_name(Rule r) {
    switch (r) {
        case Rule::ForallUnit: return "ForallUnit"; case Rule::Ai: return "Ai";
        case Rule::Tu: return "Tu"; case Rule::Sw: return "Sw"; case Rule::Mix: return "Mix";
        case Rule::Ex: return "Ex"; case Rule::Eqv: return "Eqv"; case Rule::W: return "W";
        case Rule::WForall: return "WForall"; case Rule::Ac: return "Ac";
        case Rule::CForall: return "CForall"; case Rule::M: return "M";
        case Rule::MForall: return "MForall"; case Rule::MExists: return "MExists";
    }
    return "?";
}
thread_local const char* g_swap_fail = "";

std::optional<std::pair<Step, Step>> try_swap(FormulaBuilder& fb, FormulaHandle Fx,
                                              const Step& x, const Step& y,
                                              PredicateHandle sentinel) {
#define SWAP_BAIL(R) do { g_swap_fail = (R); return std::nullopt; } while (0)
    auto end = replay(fb, Fx, {x, y});
    if (end.is_error()) SWAP_BAIL("end-replay-error");

    // Binder-crossing: y = Ex abstracts an instance φ[t] → ∃x.φ, and x lived
    // STRICTLY INSIDE that instance. abstract_var only RENAMES the fixed witness
    // to Gen(0) (no tree restructuring), so the context remap is exact and
    // analytic. y′ re-abstracts the PRE-x instance; x′ moves under the new [Down]
    // with its params abstracted by the same witness. When x is DISJOINT from the
    // instance (x.context not under y.context) the binder is not crossed — the
    // generic sentinel path below handles it (and any witness shape), so we only
    // take this branch for the genuine crossing.
    if (y.rule == Rule::Ex && is_prefix(y.context, x.context)) {
        if (!y.t_param.is_fixed()) SWAP_BAIL("Ex-nonfixed-witness");
        var_index w = y.t_param.as_variable();
        FormulaHandle inst = nav_at(Fx, y.context);
        if (!inst.valid()) SWAP_BAIL("Ex-bad-context");
        Step yp = y;
        yp.f_param = fb.abstract_var(inst, w);                // body of the pre-x ∃
        Step xp = x;
        Path c(y.context.begin(), y.context.end());
        c.push_back(Dir::Down);
        c.insert(c.end(), x.context.begin() + y.context.size(), x.context.end());
        xp.context = std::move(c);
        if (xp.f_param.valid()) xp.f_param = fb.abstract_var(xp.f_param, w);
        auto chk = replay(fb, Fx, {yp, xp});
        if (chk.is_error()) SWAP_BAIL("Ex-verify-replay-error");
        if (chk.value() != end.value()) SWAP_BAIL("Ex-verify-mismatch");
        return std::make_pair(yp, xp);
    }

    FormulaHandle Z = fb.predicate(sentinel, {});
    FormulaHandle FxZ = put_at(fb, Fx, x.context, 0, Z);
    auto yz = replay(fb, FxZ, {y});                 // y on the sentinel'd formula
    if (yz.is_error()) SWAP_BAIL("y-no-match-before-x");
    auto cxp = find_handle(yz.value(), Z);           // where x's redex moved.
    if (!cxp) SWAP_BAIL("sentinel-lost");

    Step xp = x; xp.context = *cxp;
    auto chk = replay(fb, Fx, {y, xp});
    if (chk.is_error()) SWAP_BAIL("verify-replay-error");
    if (chk.value() != end.value()) SWAP_BAIL("verify-mismatch");
    return std::make_pair(y, xp);
#undef SWAP_BAIL
}

// Should the later step b move before the earlier step a? The bridge needs only
// the linear/resource BOUNDARY: every linear (non-≡ MLS1^X) step must precede
// every resource-only step. We bubble two kinds of pair:
//   (1) a linear b after a resource/≡ a → move b earlier (the boundary fix), and
//       let it hop a flexible ≡ that would otherwise block it;
//   (2) a flexible ≡ b after a resource-only a → move b earlier too. A later
//       linear step often DEPENDS on an ≡ reshape (e.g. Sw needs a CommOr); if
//       that ≡ is stuck behind a resource step, it anchors the linear step there
//       too. ≡ is phase-flexible, so landing it in Φ1 is always legal; try_swap
//       self-verifies, so an ≡ that genuinely consumes the resource's output
//       simply fails to move and stays in Φ2 (still decomposed).
bool should_precede(const Step& b, const Step& a) {
    bool a_resource_only = a.rule != Rule::Eqv && is_resource_only(a.rule);
    if (b.rule == Rule::Eqv) return a_resource_only;                  // (2)
    if (!is_mls1x(b.rule)) return false;                              // b not linear
    bool a_resource = a.rule != Rule::Eqv && is_resource(a.rule);
    return a_resource || a.rule == Rule::Eqv;                         // (1)
}

}  // namespace

Result<Derivation> decompose(FormulaBuilder& fb, const Derivation& d) {
    if (is_decomposed(d)) return d;                  // already decomposed (fast path)
    PredicateHandle sentinel = fb.context().add_predicate("$decomp_sentinel", 0);
    std::vector<Step> steps = d.steps;
    const bool dbg = std::getenv("KS1_DECOMPOSE_DEBUG") != nullptr;
    const std::size_t cap = 4 * steps.size() + 16;   // bubble-pass backstop
    std::size_t npass = 0, nswap = 0; bool replay_ok = true;
    for (std::size_t pass = 0; pass < cap; ++pass) {
        ++npass;
        // Prefix formulas F[i] = state before step i (recomputed each pass).
        std::vector<FormulaHandle> F(steps.size() + 1);
        F[0] = d.top;
        bool ok = true;
        for (std::size_t i = 0; i < steps.size(); ++i) {
            auto r = replay(fb, F[i], {steps[i]});
            if (r.is_error()) {
                if (dbg && pass == 0)
                    std::fprintf(stderr, "[decompose] replay FAIL at step %zu (%s): %s\n",
                                 i, rule_name(steps[i].rule), r.error().to_string().c_str());
                ok = false; break;
            }
            F[i + 1] = r.value();
        }
        if (!ok) { replay_ok = false; break; }
        bool changed = false;
        for (std::size_t i = 0; i + 1 < steps.size(); ++i) {
            if (!should_precede(steps[i + 1], steps[i])) continue;
            auto sw = try_swap(fb, F[i], steps[i], steps[i + 1], sentinel);
            if (!sw) {
                if (std::getenv("KS1_DECOMPOSE_DEBUG"))
                    std::fprintf(stderr, "[decompose] no-swap %s before %s: %s\n",
                                 rule_name(steps[i].rule), rule_name(steps[i + 1].rule),
                                 g_swap_fail);
                continue;
            }
            steps[i] = sw->first; steps[i + 1] = sw->second;
            auto r = replay(fb, F[i], {steps[i]});
            if (r.is_error()) break;
            F[i + 1] = r.value();
            changed = true; ++nswap;
        }
        if (!changed) break;
    }
    Derivation out = d;
    out.steps = std::move(steps);
    if (dbg)
        std::fprintf(stderr, "[decompose] n=%zu passes=%zu swaps=%zu replay_ok=%d decomposed=%d\n",
                     d.steps.size(), npass, nswap, replay_ok ? 1 : 0, is_decomposed(out) ? 1 : 0);
    if (std::getenv("KS1_DECOMPOSE_DUMP") && !is_decomposed(out)) {
        auto nm = [](Rule r) { return rule_name(r); };
        auto ctxs = [](const Path& p) {
            std::string s = "[";
            for (Dir d : p) s += (d == Dir::Left ? "L" : d == Dir::Right ? "R" : "D");
            return s + "]";
        };
        for (std::size_t i = 0; i < out.steps.size(); ++i) {
            const Step& s = out.steps[i];
            const char* ph = s.rule == Rule::Eqv ? "eqv"
                           : is_resource_only(s.rule) ? "RES" : "lin";
            std::fprintf(stderr, "[dump] %3zu %-10s %-3s %s\n", i, nm(s.rule), ph,
                         ctxs(s.context).c_str());
        }
    }
    if (std::getenv("KS1_DECOMPOSE_DEBUG") && !is_decomposed(out)) {
        auto name = [](Rule r) -> const char* {
            switch (r) {
                case Rule::ForallUnit: return "ForallUnit"; case Rule::Ai: return "Ai";
                case Rule::Tu: return "Tu"; case Rule::Sw: return "Sw"; case Rule::Mix: return "Mix";
                case Rule::Ex: return "Ex"; case Rule::Eqv: return "Eqv"; case Rule::W: return "W";
                case Rule::WForall: return "WForall"; case Rule::Ac: return "Ac";
                case Rule::CForall: return "CForall"; case Rule::M: return "M";
                case Rule::MForall: return "MForall"; case Rule::MExists: return "MExists";
            }
            return "?";
        };
        // Report each remaining phase-descent in the non-≡ subsequence.
        const Step* prev = nullptr;
        for (const Step& s : out.steps) {
            if (s.rule == Rule::Eqv) continue;
            if (prev && static_cast<int>(phase_of(s.rule)) < static_cast<int>(phase_of(prev->rule)))
                std::fprintf(stderr, "[decompose] stuck: %s(p%d) before %s(p%d)\n",
                             name(prev->rule), static_cast<int>(phase_of(prev->rule)),
                             name(s.rule), static_cast<int>(phase_of(s.rule)));
            prev = &s;
        }
    }
    return out;   // may be partial; split() checks is_decomposed.
}

Result<Split> split(FormulaBuilder& fb, const Derivation& d) {
    TRY_ASSIGN(dec, decompose(fb, d));
    if (!is_decomposed(dec))
        return MAKE_ERROR << "split: derivation is not in Thm 17 decomposed form";
    size_t b = boundary_index(dec);

    Split out;
    out.phi1.top = dec.top;
    out.phi1.steps.assign(dec.steps.begin(), dec.steps.begin() + b);

    auto a_prime = replay(fb, dec.top, out.phi1.steps);
    if (a_prime.is_error()) return std::move(a_prime).error();
    out.a_prime = a_prime.value();

    out.phi1.bottom = out.a_prime;
    out.phi2.top = out.a_prime;
    out.phi2.steps.assign(dec.steps.begin() + b, dec.steps.end());
    out.phi2.bottom = dec.bottom;
    return out;
}

}  // namespace logic::proof::ks1
