// Weakening-elimination engine. Spec:
//   src/proof/translate/lkr_weak_elim/WEAKENING_ELIM_DESIGN.md

#include "src/proof/translate/lkr_weak_elim/reduce.h"

#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

#include <type_traits>
#include <utility>
#include <variant>

namespace logic::proof::translate::lkr_weak_elim {

using namespace lkr_cut_elim;

namespace {

// Deep-clone a Deriv (a Deriv→Deriv pass returns a fresh tree;
// no in-place mutation).
DerivPtr clone(const Deriv& d) {
    auto out = std::make_unique<Deriv>();
    out->conclusion = d.conclusion;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx>)        { out->rule = r; }
        else if constexpr (std::is_same_v<T, ROne>)  { out->rule = r; }
        else if constexpr (std::is_same_v<T, RLemma>){ out->rule = r; }
        else if constexpr (std::is_same_v<T, RExchange>) {
            out->rule = RExchange{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            out->rule = RWeaken{r.added, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            out->rule = RContract{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            out->rule = RAnd{r.principal, r.left_partition,
                clone(*r.left), clone(*r.right)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            out->rule = ROr{r.principal, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            out->rule = RForall{r.principal, r.eigen, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            out->rule = RExists{r.principal, r.witness, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            out->rule = RCut{r.cut_formula, clone(*r.left), clone(*r.right)};
        }
    }, d.rule);
    return out;
}

// ---- §4.1 leaf absorption ---------------------------------------------------
//
// W's child is a closing rule (RAx, ROne, RLemma) — these accept arbitrary
// extra context (axiom + weakening convention). If the W'd entry is NOT
// involved in the closure (= non-principal), the W layer is redundant:
// replace it with the closing rule directly, on the smaller conclusion.
//
// Preconditions (called from `try_reduce_W` with `w.child` already
// known to be a closing rule):
//   w.rule = RWeaken{added=φ, child=C}
//   w.conclusion = Γ
//   C.conclusion = Γ + φ
//   φ at position |Γ| (= w.conclusion.size()) in C.conclusion
//
// Returns nullptr if the case doesn't apply (W'd entry is principal in the
// closure — out-of-fragment for W1).
DerivPtr try_absorb_at_leaf(const Deriv& w) {
    const auto* w_rule = std::get_if<RWeaken>(&w.rule);
    if (!w_rule) return nullptr;
    const Deriv& c = *w_rule->child;
    const std::size_t phi_pos = w.conclusion.size();

    if (const auto* ax = std::get_if<RAx>(&c.rule)) {
        // Non-principal in φ: both literal slots in Γ (< phi_pos).
        if (ax->a == phi_pos || ax->b == phi_pos) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;        // = Γ
        out->rule = RAx{ax->a, ax->b};
        return out;
    }
    if (const auto* one = std::get_if<ROne>(&c.rule)) {
        // Non-principal in φ: idx in Γ (< phi_pos).
        if (one->idx == phi_pos) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;        // = Γ
        out->rule = ROne{one->idx};
        return out;
    }
    if (const auto* lem = std::get_if<RLemma>(&c.rule)) {
        // RLemma closes when the lemma's NNF appears anywhere in the
        // sequent. The closure depends on φ iff the lemma's NNF is φ
        // AND no other entry in Γ equals φ. (If another entry in Γ
        // equals the lemma's NNF, the lemma was already closable on Γ
        // alone — the W'd entry is incidental.)
        //
        // Conservative form: absorb iff Γ already contains *some* entry
        // equal to W's `added` — wait, that's not quite the right
        // condition. The right condition is: Γ already contains the
        // *lemma's NNF*. If yes, replace with RLemma on Γ. If no, the
        // lemma was closing using φ (the W'd entry); the W is
        // load-bearing for the lemma. That case stays in the fragment
        // for now (will need an LkrCtx + builder to recover the lemma's
        // NNF from `target`); skip for the W1 baseline.
        //
        // For W1 to land cleanly without dragging in schema/builder
        // dependencies, defer RLemma absorption to a later phase. Mark
        // explicitly: return nullptr (= irreducible by W1).
        (void)lem;
        return nullptr;
    }
    return nullptr;
}

// =========================================================================
// Driver: recursively reduce a Deriv. Post-order — children first, then
// attempt the per-rule reduction at this node.
// =========================================================================
DerivPtr reduce(const Deriv& d) {
    // 1. Rebuild d with reduced children (post-order).
    DerivPtr rebuilt = std::visit([&](auto&& r) -> DerivPtr {
        using T = std::decay_t<decltype(r)>;
        auto out = std::make_unique<Deriv>();
        out->conclusion = d.conclusion;
        if constexpr (std::is_same_v<T, RAx>)        { out->rule = r; }
        else if constexpr (std::is_same_v<T, ROne>)  { out->rule = r; }
        else if constexpr (std::is_same_v<T, RLemma>){ out->rule = r; }
        else if constexpr (std::is_same_v<T, RExchange>) {
            out->rule = RExchange{r.i, r.j, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            out->rule = RWeaken{r.added, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            out->rule = RContract{r.i, r.j, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            out->rule = RAnd{r.principal, r.left_partition,
                reduce(*r.left), reduce(*r.right)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            out->rule = ROr{r.principal, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            out->rule = RForall{r.principal, r.eigen, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            out->rule = RExists{r.principal, r.witness, reduce(*r.child)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            out->rule = RCut{r.cut_formula,
                reduce(*r.left), reduce(*r.right)};
        }
        return out;
    }, d.rule);

    // 2. Per-node reduction. Currently only RWeaken targets.
    if (std::holds_alternative<RWeaken>(rebuilt->rule)) {
        // Try §4.1 leaf absorption.
        if (auto out = try_absorb_at_leaf(*rebuilt)) {
            // The result might still contain Ws above (callers handle
            // recursion); but for now the result is W-free for §4.1.
            return out;
        }
        // No reduction applies; pass through.
    }
    return rebuilt;
}

}  // namespace

util::Result<DerivPtr> eliminate_weakenings(
    FormulaBuilder& /*builder*/, const Deriv& root)
{
    return reduce(root);
}

}  // namespace logic::proof::translate::lkr_weak_elim
