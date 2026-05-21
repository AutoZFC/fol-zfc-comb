#include "src/proof/ks1/decompose.h"

#include "src/proof/ks1/checker.h"

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

Result<Split> split(FormulaBuilder& fb, const Derivation& d) {
    if (!is_decomposed(d))
        return MAKE_ERROR << "split: derivation is not in Thm 17 decomposed form";
    size_t b = boundary_index(d);

    Split out;
    out.phi1.top = d.top;
    out.phi1.steps.assign(d.steps.begin(), d.steps.begin() + b);

    auto a_prime = replay(fb, d.top, out.phi1.steps);
    if (a_prime.is_error()) return std::move(a_prime).error();
    out.a_prime = a_prime.value();

    out.phi1.bottom = out.a_prime;
    out.phi2.top = out.a_prime;
    out.phi2.steps.assign(d.steps.begin() + b, d.steps.end());
    out.phi2.bottom = d.bottom;
    return out;
}

}  // namespace logic::proof::ks1
