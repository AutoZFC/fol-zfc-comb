#include "src/proof/ks1/decompose.h"

#include "src/proof/ks1/checker.h"

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
    // Everything before the boundary must be MLS1^X; everything from it on
    // must be resource.
    for (size_t i = 0; i < b; ++i)
        if (!is_mls1x(d.steps[i].rule)) return false;
    for (size_t i = b; i < d.steps.size(); ++i)
        if (!is_resource(d.steps[i].rule)) return false;
    // Non-≡ phases must be non-decreasing within each half.
    auto monotone = [&](size_t lo, size_t hi) {
        int last = 0;
        for (size_t i = lo; i < hi; ++i) {
            if (d.steps[i].rule == Rule::Eqv) continue;
            int ph = static_cast<int>(phase_of(d.steps[i].rule));
            if (ph < last) return false;
            last = ph;
        }
        return true;
    };
    return monotone(0, b) && monotone(b, d.steps.size());
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
std::optional<std::pair<Step, Step>> try_swap(FormulaBuilder& fb, FormulaHandle Fx,
                                              const Step& x, const Step& y,
                                              PredicateHandle sentinel) {
    auto end = replay(fb, Fx, {x, y});
    if (end.is_error()) return std::nullopt;

    FormulaHandle Z = fb.predicate(sentinel, {});
    FormulaHandle FxZ = put_at(fb, Fx, x.context, 0, Z);
    auto yz = replay(fb, FxZ, {y});                 // y on the sentinel'd formula
    if (yz.is_error()) return std::nullopt;          // y's redex absent before x.
    auto cxp = find_handle(yz.value(), Z);           // where x's redex moved.
    if (!cxp) return std::nullopt;

    Step xp = x; xp.context = *cxp;
    auto chk = replay(fb, Fx, {y, xp});
    if (chk.is_error() || chk.value() != end.value()) return std::nullopt;
    return std::make_pair(y, xp);
}

// Should the later step b move before the earlier step a? Sort non-≡ steps by
// phase; let a linear step jump left past an ≡ (which is phase-flexible) so an ≡
// between two out-of-order non-≡ steps does not block the sort.
bool should_precede(const Step& b, const Step& a) {
    bool ae = a.rule == Rule::Eqv, be = b.rule == Rule::Eqv;
    if (!ae && !be) return static_cast<int>(phase_of(b.rule)) < static_cast<int>(phase_of(a.rule));
    if (ae && !be)  return static_cast<int>(phase_of(b.rule)) <= static_cast<int>(Phase::Inst);
    return false;
}

}  // namespace

Result<Derivation> decompose(FormulaBuilder& fb, const Derivation& d) {
    if (is_decomposed(d)) return d;                  // already decomposed (fast path)
    PredicateHandle sentinel = fb.context().add_predicate("$decomp_sentinel", 0);
    std::vector<Step> steps = d.steps;
    const std::size_t cap = 4 * steps.size() + 16;   // bubble-pass backstop
    for (std::size_t pass = 0; pass < cap; ++pass) {
        // Prefix formulas F[i] = state before step i (recomputed each pass).
        std::vector<FormulaHandle> F(steps.size() + 1);
        F[0] = d.top;
        bool ok = true;
        for (std::size_t i = 0; i < steps.size(); ++i) {
            auto r = replay(fb, F[i], {steps[i]});
            if (r.is_error()) { ok = false; break; }
            F[i + 1] = r.value();
        }
        if (!ok) break;
        bool changed = false;
        for (std::size_t i = 0; i + 1 < steps.size(); ++i) {
            if (!should_precede(steps[i + 1], steps[i])) continue;
            auto sw = try_swap(fb, F[i], steps[i], steps[i + 1], sentinel);
            if (!sw) continue;
            steps[i] = sw->first; steps[i + 1] = sw->second;
            auto r = replay(fb, F[i], {steps[i]});
            if (r.is_error()) break;
            F[i + 1] = r.value();
            changed = true;
        }
        if (!changed) break;
    }
    Derivation out = d;
    out.steps = std::move(steps);
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
