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
// Forward declarations.
DerivPtr swap_subtree_positions(const Deriv& d,
                                std::size_t lo, std::size_t hi);

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

// ---- §4.2 unary permutation -------------------------------------------------
//
// W above a unary rule R where R's principal/positional fields all refer
// to positions in Γ (NOT the W'd slot at |Γ|). Permute so R fires first,
// then W. For ROr, an additional inner RExchange is needed to restore
// the original child's [..., φ, ψ] tail order (§4.2.1).
//
// Precondition (caller): w.rule is RWeaken{φ, child=C}, w.conclusion = Γ,
// C.conclusion = Γ + φ' where φ' is at position |Γ| (= the W'd slot).
//
// Returns nullptr if the case doesn't apply (W-principal or out-of-frag).
DerivPtr try_permute_unary(const Deriv& w) {
    const auto* w_rule = std::get_if<RWeaken>(&w.rule);
    if (!w_rule) return nullptr;
    const Deriv& inner = *w_rule->child;
    const std::size_t gamma_size = w.conclusion.size();
    const FormulaHandle& phi = w_rule->added;

    auto make_inner_w_from_orig_child =
        [&](const Deriv& orig_child) -> DerivPtr {
            // The new inner W's child is a clone of the original
            // inner-rule's child; its conclusion is unchanged. The W
            // node's conclusion = child's conclusion minus the last
            // entry (= φ at the tail).
            auto wn = std::make_unique<Deriv>();
            wn->conclusion = orig_child.conclusion;
            if (wn->conclusion.empty()) return nullptr;
            wn->conclusion.pop_back();
            wn->rule = RWeaken{phi, clone(orig_child)};
            return wn;
        };

    // --- ROr (§4.2.1) ---
    if (const auto* o = std::get_if<ROr>(&inner.rule)) {
        if (o->principal >= gamma_size) return nullptr;  // W-principal: §4.3.1
        // Or's child `c` was built expecting tail [..., φ@|Γ|, ψ@|Γ|+1].
        // After permutation, the new tail is [..., ψ@|Γ|, φ@|Γ|+1]. We
        // rewrite c with a (|Γ|, |Γ|+1) swap via swap_subtree_positions,
        // covering leaf-like c and rules that propagate the swap
        // cleanly (ROr/RForall/RExists/RAnd-with-both-in-side).
        //
        // The alternative (insert RExchange to fix tail order) produced
        // structures the W couldn't permute past in the subsequent
        // recursion — strictly worse. Bail if swap fails; the W stays
        // and a different reduction order may catch it.
        const Deriv& c = *o->child;
        if (c.conclusion.size() < 2) return nullptr;
        auto new_w_child = swap_subtree_positions(c, gamma_size, gamma_size + 1);
        if (!new_w_child) return nullptr;

        auto new_w = std::make_unique<Deriv>();
        new_w->conclusion = new_w_child->conclusion;
        new_w->conclusion.pop_back();
        new_w->rule = RWeaken{phi, std::move(new_w_child)};

        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;        // = Γ
        out->rule = ROr{o->principal, std::move(new_w)};
        return out;
    }

    // --- RForall (§4.2.2) ---
    if (const auto* f = std::get_if<RForall>(&inner.rule)) {
        if (f->principal >= gamma_size) return nullptr;  // W-principal: §4.3.2
        auto new_w = make_inner_w_from_orig_child(*f->child);
        if (!new_w) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;
        out->rule = RForall{f->principal, f->eigen, std::move(new_w)};
        return out;
    }

    // --- RExists (§4.2.3) ---
    if (const auto* e = std::get_if<RExists>(&inner.rule)) {
        if (e->principal >= gamma_size) return nullptr;  // W-principal: §4.3.3
        auto new_w = make_inner_w_from_orig_child(*e->child);
        if (!new_w) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;
        out->rule = RExists{e->principal, e->witness, std::move(new_w)};
        return out;
    }

    // --- RExchange (§4.2.4) ---
    if (const auto* x = std::get_if<RExchange>(&inner.rule)) {
        if (x->i >= gamma_size || x->j >= gamma_size) return nullptr;  // edge
        auto new_w = make_inner_w_from_orig_child(*x->child);
        if (!new_w) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;
        out->rule = RExchange{x->i, x->j, std::move(new_w)};
        return out;
    }

    // --- RContract (§4.2.5) ---
    if (const auto* k = std::get_if<RContract>(&inner.rule)) {
        if (k->i >= gamma_size || k->j >= gamma_size) return nullptr;  // edge
        auto new_w = make_inner_w_from_orig_child(*k->child);
        if (!new_w) return nullptr;
        auto out = std::make_unique<Deriv>();
        out->conclusion = w.conclusion;
        out->rule = RContract{k->i, k->j, std::move(new_w)};
        return out;
    }

    // --- RWeaken over RWeaken (§4.2.6) ---
    // Handled by the driver's post-order: the inner W reduces first
    // (potentially absorbing at a leaf), then the outer W's child
    // becomes the inner W's reduction. If the inner W couldn't reduce,
    // we leave the outer W in place too (out-of-fragment for W2).

    return nullptr;
}

// Swap positions `lo` and `hi` in a subtree's rule fields and conclusion.
// Recurses through rules whose effect on the sequent preserves the
// (lo, hi) swap structure to the child's sequent (ROr, RForall,
// RExists — they only modify the principal slot + optionally append).
// Returns nullptr if a rule in the subtree can't be cleanly remapped
// (RExchange/RContract/RAnd/RCut/RWeaken — these change positions in
// ways that require composing the outer swap with the rule's internal
// position shift; deferred until a producer needs it).
DerivPtr swap_subtree_positions(const Deriv& d,
                                std::size_t lo, std::size_t hi) {
    if (lo >= d.conclusion.size() || hi >= d.conclusion.size()) {
        return nullptr;
    }
    auto remap = [&](std::size_t p) -> std::size_t {
        return p == lo ? hi : (p == hi ? lo : p);
    };
    auto out = std::make_unique<Deriv>();
    out->conclusion = d.conclusion;
    std::swap(out->conclusion[lo], out->conclusion[hi]);

    if (const auto* ax = std::get_if<RAx>(&d.rule)) {
        out->rule = RAx{remap(ax->a), remap(ax->b)};
        return out;
    }
    if (const auto* one = std::get_if<ROne>(&d.rule)) {
        out->rule = ROne{remap(one->idx)};
        return out;
    }
    if (const auto* lem = std::get_if<RLemma>(&d.rule)) {
        out->rule = RLemma{lem->target, lem->source_name};
        return out;
    }
    if (const auto* o = std::get_if<ROr>(&d.rule)) {
        // Or fires on position remap(principal); appends ψ at end.
        // Child's positions: same (lo, hi) swap (positions in pre-Or
        // sequent and post-Or sequent line up except for the principal
        // slot, which is the one we're remapping). The appended ψ is
        // at child.conclusion.size()-1 in BOTH original and swapped
        // child — unchanged by the swap (swap doesn't touch the end).
        auto new_child = swap_subtree_positions(*o->child, lo, hi);
        if (!new_child) return nullptr;
        out->rule = ROr{remap(o->principal), std::move(new_child)};
        return out;
    }
    if (const auto* f = std::get_if<RForall>(&d.rule)) {
        auto new_child = swap_subtree_positions(*f->child, lo, hi);
        if (!new_child) return nullptr;
        out->rule = RForall{remap(f->principal), f->eigen,
                            std::move(new_child)};
        return out;
    }
    if (const auto* e = std::get_if<RExists>(&d.rule)) {
        auto new_child = swap_subtree_positions(*e->child, lo, hi);
        if (!new_child) return nullptr;
        out->rule = RExists{remap(e->principal), e->witness,
                            std::move(new_child)};
        return out;
    }
    if (const auto* a = std::get_if<RAnd>(&d.rule)) {
        // Don't permute the swap if either lo or hi is the principal
        // (or both); the principal-shift case is sound but the partition
        // and child-routing math gets gnarly. Bail; W3 caller falls
        // through and the W stays.
        if (lo == a->principal || hi == a->principal) return nullptr;

        auto in_partition = [&](std::size_t k) {
            for (std::size_t p : a->left_partition) if (p == k) return true;
            return false;
        };
        bool lo_in_part = in_partition(lo);
        bool hi_in_part = in_partition(hi);

        // Compute new_partition by remapping each entry. As a multiset
        // {lo↔hi} is identity, but if exactly one of lo, hi is in the
        // partition, the swap reshapes sorted(partition).
        std::vector<std::size_t> new_partition;
        new_partition.reserve(a->left_partition.size());
        for (std::size_t p : a->left_partition) {
            new_partition.push_back(remap(p));
        }

        // CASE A: both in partition. sorted(partition) order may change
        // numerically; LEFT child sees swap at (idx_lo, idx_hi).
        if (lo_in_part && hi_in_part) {
            std::vector<std::size_t> sp(a->left_partition.begin(),
                                       a->left_partition.end());
            std::sort(sp.begin(), sp.end());
            std::size_t lo_idx = 0, hi_idx = 0;
            for (std::size_t i = 0; i < sp.size(); ++i) {
                if (sp[i] == lo) lo_idx = i;
                if (sp[i] == hi) hi_idx = i;
            }
            auto new_left = swap_subtree_positions(*a->left, lo_idx, hi_idx);
            if (!new_left) return nullptr;
            out->rule = RAnd{a->principal, new_partition,
                             std::move(new_left), clone(*a->right)};
            return out;
        }

        // CASE B: both in complement (not in partition, not principal).
        if (!lo_in_part && !hi_in_part) {
            std::vector<std::size_t> compl_set;
            for (std::size_t k = 0; k < d.conclusion.size(); ++k) {
                if (k != a->principal && !in_partition(k)) {
                    compl_set.push_back(k);
                }
            }
            std::sort(compl_set.begin(), compl_set.end());
            std::size_t lo_idx = 0, hi_idx = 0;
            for (std::size_t i = 0; i < compl_set.size(); ++i) {
                if (compl_set[i] == lo) lo_idx = i;
                if (compl_set[i] == hi) hi_idx = i;
            }
            auto new_right = swap_subtree_positions(*a->right, lo_idx, hi_idx);
            if (!new_right) return nullptr;
            out->rule = RAnd{a->principal, new_partition,
                             clone(*a->left), std::move(new_right)};
            return out;
        }

        // CASE C: lo and hi straddle the partition/complement split.
        // The LEFT and RIGHT children's sequents both reshape; need to
        // carefully recompute the position remapping inside each. Defer
        // (more invasive math; the simpler partition-uniform cases above
        // already capture the common shape we hit).
        return nullptr;
    }
    // RExchange/RContract/RCut/RWeaken: out of fragment.
    return nullptr;
}

// ---- §4.4.1 W above RAnd (binary split) -------------------------------------
//
// W above RAnd where the And's principal is in Γ (NOT the W'd slot at
// |Γ| — that case is §4.3.4, out of scope). The W'd entry at position
// |Γ| in `inner.conclusion` (= Γ+φ) is EITHER in `left_partition`
// (→ goes to LEFT) OR in the complement (→ goes to RIGHT).
//
// Permuted form:
//   new_partition = left_partition with |Γ| removed (if present).
//   The side that originally held the W'd entry gets a fresh RWeaken
//   on top; the other side is cloned unchanged.
//
// The affected side's subtree expected a tail order [..., φ, side_aux]
// (where side_aux is LEFT_phi or RIGHT_psi); in the permuted form the
// tail becomes [..., side_aux, φ] (φ at end because W appends). We
// rewrite the leaf's positions for this swap. Non-leaf cases on the
// affected side fall back to nullptr (out of fragment for the initial
// impl; see swap_subtree_positions).
DerivPtr try_permute_and(const Deriv& w) {
    const auto* w_rule = std::get_if<RWeaken>(&w.rule);
    if (!w_rule) return nullptr;
    const Deriv& inner = *w_rule->child;
    const auto* a = std::get_if<RAnd>(&inner.rule);
    if (!a) return nullptr;

    const std::size_t gamma_size = w.conclusion.size();
    const FormulaHandle& phi = w_rule->added;

    if (a->principal >= gamma_size) return nullptr;  // W-principal: §4.3.4

    bool in_left = false;
    for (std::size_t p : a->left_partition) {
        if (p == gamma_size) { in_left = true; break; }
    }

    std::vector<std::size_t> new_partition;
    new_partition.reserve(a->left_partition.size());
    for (std::size_t p : a->left_partition) {
        if (p != gamma_size) new_partition.push_back(p);
    }

    auto build_W_side = [&](const Deriv& orig_side) -> DerivPtr {
        // orig_side.conclusion's tail is [..., φ, side_aux]. After
        // permutation we want post-W = [..., side_aux, φ]. Swap the
        // last two positions in the leaf.
        if (orig_side.conclusion.size() < 2) return nullptr;
        std::size_t lo = orig_side.conclusion.size() - 2;
        std::size_t hi = orig_side.conclusion.size() - 1;
        auto rewritten = swap_subtree_positions(orig_side, lo, hi);
        if (!rewritten) return nullptr;
        auto wn = std::make_unique<Deriv>();
        wn->conclusion = rewritten->conclusion;
        wn->conclusion.pop_back();                  // strip φ
        wn->rule = RWeaken{phi, std::move(rewritten)};
        return wn;
    };

    DerivPtr new_left, new_right;
    if (in_left) {
        new_left = build_W_side(*a->left);
        if (!new_left) return nullptr;
        new_right = clone(*a->right);
    } else {
        new_right = build_W_side(*a->right);
        if (!new_right) return nullptr;
        new_left = clone(*a->left);
    }

    auto out = std::make_unique<Deriv>();
    out->conclusion = w.conclusion;     // = Γ
    out->rule = RAnd{a->principal, new_partition,
                     std::move(new_left), std::move(new_right)};
    return out;
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
        // Try §4.1 leaf absorption first (drops the W entirely).
        if (auto out = try_absorb_at_leaf(*rebuilt)) {
            return out;
        }
        // Try §4.2 unary permutation. The result still contains the
        // same W (moved deeper); recurse so the displaced W can
        // continue reducing at its new position (potentially landing
        // at a leaf for §4.1 absorption).
        if (auto out = try_permute_unary(*rebuilt)) {
            return reduce(*out);
        }
        // Try §4.4.1 RAnd permutation. The W moves into one side of the
        // And (the side that originally held the W'd entry); recurse so
        // the displaced W can continue reducing.
        if (auto out = try_permute_and(*rebuilt)) {
            return reduce(*out);
        }
        // No reduction applies; pass through (out-of-fragment for now).
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
