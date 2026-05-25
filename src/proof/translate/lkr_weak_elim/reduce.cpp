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
        // The Or's child `c` was built expecting tail [..., φ@|Γ|, ψ@|Γ|+1].
        // After permutation, the new tail at this depth is [..., ψ@|Γ|, φ@|Γ|+1].
        // Two realizations (spec §4.2.1):
        //   (a) Insert RExchange{|Γ|, |Γ|+1, c} to fix the tail. But this
        //       creates an Exchange touching the W'd slot, which the
        //       subsequent W-elim recursion can't permute past (edge
        //       case in §4.2.4) — the W gets stuck.
        //   (b) Rewrite c's position references for the swap. Simpler
        //       when c is a leaf (just remap the RAx/ROne positions);
        //       general subtree rewrite gets tangled with downstream
        //       rule semantics. We do (b) for leaves and fall back to
        //       (a) otherwise — the (a) tree is still sound; just not
        //       fully W-free.
        const Deriv& c = *o->child;
        if (c.conclusion.size() < 2) return nullptr;

        auto swap_in_leaf = [&](const Deriv& leaf) -> DerivPtr {
            // Build a new leaf with positions gamma_size and gamma_size+1
            // swapped in both the conclusion entries and the rule fields.
            std::size_t lo = gamma_size, hi = gamma_size + 1;
            auto remap = [&](std::size_t p) -> std::size_t {
                return p == lo ? hi : (p == hi ? lo : p);
            };
            auto out_leaf = std::make_unique<Deriv>();
            out_leaf->conclusion = leaf.conclusion;
            std::swap(out_leaf->conclusion[lo], out_leaf->conclusion[hi]);
            if (const auto* ax = std::get_if<RAx>(&leaf.rule)) {
                out_leaf->rule = RAx{remap(ax->a), remap(ax->b)};
            } else if (const auto* one = std::get_if<ROne>(&leaf.rule)) {
                out_leaf->rule = ROne{remap(one->idx)};
            } else if (const auto* lem = std::get_if<RLemma>(&leaf.rule)) {
                // RLemma doesn't reference positions; the lemma's NNF
                // is matched against the sequent. Swapping entries
                // doesn't change membership; just clone the rule.
                out_leaf->rule = *lem;
            } else {
                return nullptr;
            }
            return out_leaf;
        };

        DerivPtr new_w_child;  // becomes the new RWeaken's child.
        if (std::holds_alternative<RAx>(c.rule) ||
            std::holds_alternative<ROne>(c.rule) ||
            std::holds_alternative<RLemma>(c.rule)) {
            // Realization (b): leaf with swapped positions.
            new_w_child = swap_in_leaf(c);
            if (!new_w_child) return nullptr;
        } else {
            // Realization (a): insert RExchange to fix tail order.
            // The W will then be stuck above the Exchange (out of
            // fragment for W2). Sound but not fully reducing.
            auto exch = std::make_unique<Deriv>();
            exch->conclusion = c.conclusion;
            std::swap(exch->conclusion[gamma_size],
                      exch->conclusion[gamma_size + 1]);
            exch->rule = RExchange{gamma_size, gamma_size + 1, clone(c)};
            new_w_child = std::move(exch);
        }

        // new_inner_w.conclusion = (Γ' + ψ). The W's child conclusion
        // (= new_w_child.conclusion) has φ at the tail.
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

// Swap positions `lo` and `hi` in a LEAF rule's positional fields, and
// in the leaf's conclusion entries. Returns nullptr if `d` is not a
// closing rule (the position-rewrite for non-leaves needs to track
// each rule's effect on positions through the subtree — out of fragment
// for the initial impl).
DerivPtr swap_leaf_positions(const Deriv& d, std::size_t lo, std::size_t hi) {
    auto remap = [&](std::size_t p) -> std::size_t {
        return p == lo ? hi : (p == hi ? lo : p);
    };
    auto out = std::make_unique<Deriv>();
    out->conclusion = d.conclusion;
    if (lo >= out->conclusion.size() || hi >= out->conclusion.size()) {
        return nullptr;
    }
    std::swap(out->conclusion[lo], out->conclusion[hi]);
    if (const auto* ax = std::get_if<RAx>(&d.rule)) {
        out->rule = RAx{remap(ax->a), remap(ax->b)};
    } else if (const auto* one = std::get_if<ROne>(&d.rule)) {
        out->rule = ROne{remap(one->idx)};
    } else if (const auto* lem = std::get_if<RLemma>(&d.rule)) {
        out->rule = RLemma{lem->target, lem->source_name};
    } else {
        return nullptr;
    }
    return out;
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
// impl; see swap_leaf_positions).
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
        auto rewritten = swap_leaf_positions(orig_side, lo, hi);
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
