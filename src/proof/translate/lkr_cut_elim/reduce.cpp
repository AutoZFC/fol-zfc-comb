#include "src/proof/translate/lkr_cut_elim/reduce.h"

#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

DerivPtr clone(const Deriv& d) {
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> ||
                      std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            n->rule = r;
        } else if constexpr (std::is_same_v<T, RExchange>) {
            n->rule = RExchange{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            n->rule = RWeaken{r.idx, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RDuplicate>) {
            n->rule = RDuplicate{r.src, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            n->rule = RContract{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n->rule = RAnd{r.principal, r.left_partition,
                           clone(*r.left), clone(*r.right)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            n->rule = ROr{r.principal, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            n->rule = RForall{r.principal, r.eigen, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            n->rule = RExists{r.principal, r.witness, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            n->rule = RCut{r.cut_formula, clone(*r.left), clone(*r.right)};
        }
    }, d.rule);
    return n;
}

// --- find max degree across all cuts; track whether any cut exists ---
void scan_cuts(const Deriv& d, std::size_t& max_deg, bool& any) {
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            any = true;
            std::size_t dg = degree(r.cut_formula);
            if (dg > max_deg) max_deg = dg;
            scan_cuts(*r.left, max_deg, any);
            scan_cuts(*r.right, max_deg, any);
        } else if constexpr (std::is_same_v<T, RAnd>) {
            scan_cuts(*r.left, max_deg, any);
            scan_cuts(*r.right, max_deg, any);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            scan_cuts(*r.child, max_deg, any);
        }
    }, d.rule);
}

// --- DFS for a max-degree RCut, stopping at the first one (= topmost) ---
bool find_topmost(const Deriv& d, std::size_t target_deg,
                  CutPath& path_so_far, CutPath& result) {
    return std::visit([&](auto&& r) -> bool {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            if (degree(r.cut_formula) == target_deg) {
                result = path_so_far;
                return true;  // topmost — don't descend further.
            }
            path_so_far.push_back(0);
            if (find_topmost(*r.left,  target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            path_so_far.push_back(1);
            if (find_topmost(*r.right, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        } else if constexpr (std::is_same_v<T, RAnd>) {
            path_so_far.push_back(0);
            if (find_topmost(*r.left,  target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            path_so_far.push_back(1);
            if (find_topmost(*r.right, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            path_so_far.push_back(0);
            if (find_topmost(*r.child, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        }
        return false;
    }, d.rule);
}

// --- Read the subtree at a path (no ownership transfer). ---
const Deriv* at_path(const Deriv& tree, const CutPath& path) {
    const Deriv* cur = &tree;
    for (int step : path) {
        const Deriv* next = nullptr;
        std::visit([&](auto&& r) {
            using T = std::decay_t<decltype(r)>;
            if constexpr (std::is_same_v<T, RAnd> || std::is_same_v<T, RCut>) {
                next = (step == 0) ? r.left.get() : r.right.get();
            } else if constexpr (std::is_same_v<T, RExchange> ||
                                 std::is_same_v<T, RWeaken>   ||
                                 std::is_same_v<T, RDuplicate>||
                                 std::is_same_v<T, RContract> ||
                                 std::is_same_v<T, ROr>       ||
                                 std::is_same_v<T, RForall>   ||
                                 std::is_same_v<T, RExists>) {
                next = r.child.get();
            }
        }, cur->rule);
        if (!next) return nullptr;
        cur = next;
    }
    return cur;
}

// --- Substitute a new subtree at the given path; returns a fresh tree. ---
util::Result<DerivPtr> substitute_at(const Deriv& tree, const CutPath& path,
                                      DerivPtr new_subtree,
                                      std::size_t depth = 0) {
    if (depth == path.size())
        return util::Result<DerivPtr>(std::move(new_subtree));

    int step = path[depth];
    auto n = std::make_unique<Deriv>();
    n->conclusion = tree.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAnd>) {
            if (step == 0) {
                TRY_ASSIGN(nl, substitute_at(*r.left, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RAnd{r.principal, r.left_partition,
                               std::move(nl), clone(*r.right)};
            } else {
                TRY_ASSIGN(nr, substitute_at(*r.right, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RAnd{r.principal, r.left_partition,
                               clone(*r.left), std::move(nr)};
            }
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RCut>) {
            if (step == 0) {
                TRY_ASSIGN(nl, substitute_at(*r.left, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RCut{r.cut_formula, std::move(nl), clone(*r.right)};
            } else {
                TRY_ASSIGN(nr, substitute_at(*r.right, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RCut{r.cut_formula, clone(*r.left), std::move(nr)};
            }
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RExchange{r.i, r.j, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RWeaken{r.idx, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RDuplicate>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RDuplicate{r.src, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RContract{r.i, r.j, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = ROr{r.principal, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RForall{r.principal, r.eigen, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RExists{r.principal, r.witness, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else {
            return MAKE_ERROR << "substitute_at: cannot descend into leaf rule at path";
        }
    }, tree.rule);
}

// =========================================================================
// §5 case implementations — Step 4 of STAGE3_RESET_PLAN.
//
// Each try_* returns a DerivPtr on success or nullptr to signal "this
// case does not apply." dispatch_cut chains them in order; the first
// applicable case fires.
// =========================================================================

// --- B1: axiom case, non-principal (§5.2). -------------------------------
//
// One premise's rule is RAx with literals at positions {a, b}, and the
// cut formula (at position |Γ_side| in that premise's conclusion) is NOT
// among {a, b}. The axiom closes within the side's Γ alone; the cut
// formula is just side context the axiom ignores.
//
// Reduction: discard the OTHER premise; produce a new RAx on the mult
// conclusion Γ_L ++ Γ_R using the same literal positions (shifted if the
// axiom is on the RIGHT, since right's positions are second half of the
// mult conclusion).
DerivPtr try_b1_ax_nonprincipal(const Deriv& cut_node, const RCut& cut,
                                 bool ax_on_left) {
    const Deriv* ax_side = ax_on_left ? cut.left.get() : cut.right.get();
    const auto* ax = std::get_if<RAx>(&ax_side->rule);
    if (!ax) return nullptr;
    const std::size_t cut_pos = ax_side->conclusion.size() - 1;
    if (ax->a == cut_pos || ax->b == cut_pos) return nullptr;  // principal — different case.

    auto out = std::make_unique<Deriv>();
    out->conclusion = cut_node.conclusion;

    if (ax_on_left) {
        // Left's positions a, b (both < |Γ_L|) map directly to the same
        // positions in cut_node.conclusion (Γ_L is the first |Γ_L| entries).
        out->rule = RAx{ax->a, ax->b};
    } else {
        // Right's positions a, b (both < |Γ_R|) are at positions
        // (a + |Γ_L|, b + |Γ_L|) in cut_node.conclusion.
        const std::size_t gl = cut.left->conclusion.size() - 1;
        out->rule = RAx{ax->a + gl, ax->b + gl};
    }
    return out;
}

// --- B1: ROne case, non-principal. ---------------------------------------
//
// Like RAx non-principal but with the single truth-literal (1 / ¬⊥). The
// cut formula must NOT be at the ROne's idx position; otherwise the idx
// shifts in the mult conclusion.
DerivPtr try_b1_one_nonprincipal(const Deriv& cut_node, const RCut& cut,
                                  bool one_on_left) {
    const Deriv* one_side = one_on_left ? cut.left.get() : cut.right.get();
    const auto* one = std::get_if<ROne>(&one_side->rule);
    if (!one) return nullptr;
    const std::size_t cut_pos = one_side->conclusion.size() - 1;
    if (one->idx == cut_pos) return nullptr;  // principal — separate case.

    auto out = std::make_unique<Deriv>();
    out->conclusion = cut_node.conclusion;
    if (one_on_left) {
        out->rule = ROne{one->idx};
    } else {
        const std::size_t gl = cut.left->conclusion.size() - 1;
        out->rule = ROne{one->idx + gl};
    }
    return out;
}

// --- B1: axiom case, PRINCIPAL (§5.2). -----------------------------------
//
// One premise is RAx with the cut formula principal: φ sits at that side's
// last position (cut_pos) and IS one of the axiom literals. The axiom closes
// that side on φ and its dual φ̄, so φ̄ already appears in that side's Γ at
// the OTHER axiom position. The cut is therefore redundant — graft the OTHER
// premise's derivation D onto the mult conclusion node = Γ_L ++ Γ_R.
//
// This reduction needs to SHRINK the doubled-looking context down to D's
// conclusion; that is exactly what the (now sound, drop-semantics) Weakening
// provides — see WEAKENING_FIX_DESIGN.md.
//
//   ax on LEFT  (left = RAx on (p, gl), Γ_L[p] = φ̄):
//     drop every Γ_L entry except p  → [φ̄] ++ Γ_R   (φ̄ at front)
//     rotate φ̄ to the back           → Γ_R ++ {φ̄}
//     graft D = cut.right (proves Γ_R ++ {φ̄}).
//   ax on RIGHT (right = RAx on (q, gr), Γ_R[q] = φ):
//     drop every Γ_R entry except q  → Γ_L ++ {φ}   (φ at last position gl)
//     graft D = cut.left (proves Γ_L ++ {φ}); no reorder needed.
DerivPtr try_b1_ax_principal(const Deriv& cut_node, const RCut& cut,
                             bool ax_on_left) {
    const Deriv* ax_side = ax_on_left ? cut.left.get() : cut.right.get();
    const auto* ax = std::get_if<RAx>(&ax_side->rule);
    if (!ax) return nullptr;
    const std::size_t cut_pos = ax_side->conclusion.size() - 1;
    std::size_t dual_in_side;
    if      (ax->a == cut_pos) dual_in_side = ax->b;
    else if (ax->b == cut_pos) dual_in_side = ax->a;
    else return nullptr;   // non-principal — handled by try_b1_ax_nonprincipal.

    const std::size_t gl = cut.left->conclusion.size() - 1;
    const std::size_t gr = cut.right->conclusion.size() - 1;
    const std::vector<FormulaHandle>& full = cut_node.conclusion;  // Γ_L ++ Γ_R

    std::size_t keep, side_lo, side_hi;
    DerivPtr D;
    if (ax_on_left) {
        keep = dual_in_side;           // < gl; same index in `full`
        side_lo = 0; side_hi = gl;
        D = clone(*cut.right);
    } else {
        keep = gl + dual_in_side;      // dual at full position gl + q
        side_lo = gl; side_hi = gl + gr;
        D = clone(*cut.left);
    }

    // Positions to drop (the axiom side's Γ except `keep`), descending so each
    // stays valid as higher positions are removed first.
    std::vector<std::size_t> drop_idxs;
    for (std::size_t i = side_hi; i-- > side_lo; )
        if (i != keep) drop_idxs.push_back(i);

    // concls[k] = `full` with drop_idxs[0..k-1] removed; concls.back() is the
    // axiom side reduced to its dual + the other side's Γ.
    std::vector<std::vector<FormulaHandle>> concls;
    concls.push_back(full);
    for (std::size_t d : drop_idxs) {
        std::vector<FormulaHandle> next = concls.back();
        next.erase(next.begin() + d);
        concls.push_back(std::move(next));
    }

    DerivPtr cur = std::move(D);
    if (ax_on_left) {
        // D = cut.right with concl Γ_R ++ {φ̄}; rotate φ̄ (last) to the front
        // so the chain bottoms out at [φ̄] ++ Γ_R = concls.back().
        for (std::size_t k = gr; k-- > 0; ) {
            auto node = std::make_unique<Deriv>();
            node->conclusion = cur->conclusion;
            std::swap(node->conclusion[k], node->conclusion[k + 1]);
            node->rule = RExchange{k, k + 1, std::move(cur)};
            cur = std::move(node);
        }
    }

    // Wrap with the RWeaken drops, innermost → outermost.
    for (std::size_t k = drop_idxs.size(); k-- > 0; ) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = concls[k];
        node->rule = RWeaken{drop_idxs[k], std::move(cur)};
        cur = std::move(node);
    }
    return cur;   // cur.conclusion == cut_node.conclusion
}

// --- permutation helpers (used by B2 / future B4) ------------------------
//
// selection_swaps(perm): swaps that, applied in order to the identity
// arrangement [0..n-1], produce `perm` (perm[t] = source index landing at t).
std::vector<std::pair<std::size_t, std::size_t>>
selection_swaps(const std::vector<std::size_t>& perm) {
    const std::size_t n = perm.size();
    std::vector<std::size_t> arr(n), pos(n);
    for (std::size_t i = 0; i < n; ++i) { arr[i] = i; pos[i] = i; }
    std::vector<std::pair<std::size_t, std::size_t>> swaps;
    for (std::size_t t = 0; t < n; ++t) {
        const std::size_t want = perm[t];
        const std::size_t cur = pos[want];
        if (cur != t) {
            const std::size_t other = arr[t];
            std::swap(arr[t], arr[cur]);
            pos[want] = t; pos[other] = cur;
            swaps.emplace_back(t, cur);
        }
    }
    return swaps;
}

// Wrap `inner` with RExchange nodes applying `swaps` in order (first swap
// deepest). Result conclusion = inner.conclusion permuted by the swaps.
DerivPtr apply_swaps(DerivPtr inner,
                     const std::vector<std::pair<std::size_t, std::size_t>>& swaps) {
    DerivPtr cur = std::move(inner);
    for (const auto& sw : swaps) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = cur->conclusion;
        std::swap(node->conclusion[sw.first], node->conclusion[sw.second]);
        node->rule = RExchange{sw.first, sw.second, std::move(cur)};
        cur = std::move(node);
    }
    return cur;
}

// match_perm(src, tgt): m[t] = a distinct source index with src[m[t]] == tgt[t].
// Requires src and tgt to be permutations of each other (same multiset).
std::vector<std::size_t> match_perm(const std::vector<FormulaHandle>& src,
                                    const std::vector<FormulaHandle>& tgt) {
    const std::size_t n = src.size();
    std::vector<bool> used(n, false);
    std::vector<std::size_t> m(n, 0);
    for (std::size_t t = 0; t < n; ++t)
        for (std::size_t p = 0; p < n; ++p)
            if (!used[p] && src[p] == tgt[t]) { used[p] = true; m[t] = p; break; }
    return m;
}

// --- B2: principal logical, ∧ vs ∨ (§5.3). -------------------------------
//
// Cut on φ where one premise ends in (∧) producing φ=β∧γ and the other ends
// in (∨) producing φ̄=β̄∨γ̄ (the dual pair, by De Morgan). The ∧-premise
// supplies Lβ ⊢ Π₁,β and Lγ ⊢ Π₂,γ (Π₁⊎Π₂ = its context C_∧); the ∨-premise
// supplies Oc ⊢ C_∨,β̄,γ̄. Replace with two lower-degree cuts:
//   cut β :  Lβ (Π₁,β)  ×  Oc' (C_∨,γ̄,β̄)   ⟹  Π₁,C_∨,γ̄
//   cut γ :  Lγ (Π₂,γ)  ×  (Π₁,C_∨,γ̄)      ⟹  Π₂,Π₁,C_∨
// then reorder Π₂,Π₁,C_∨ into node.conclusion (= C_∧,C_∨ or C_∨,C_∧). Works
// for both orientations (φ=∧ left, or φ=∨ left): only node order differs, and
// the final reorder absorbs it. d(β),d(γ) < d(β∧γ). ✓
DerivPtr try_b2_and_or(const Deriv& cut_node, const RCut& cut) {
    const RAnd* andR = std::get_if<RAnd>(&cut.left->rule);
    const ROr*  orR  = std::get_if<ROr>(&cut.right->rule);
    const Deriv* andD = cut.left.get();
    const Deriv* orD  = cut.right.get();
    if (!andR || !orR) {                 // try the other orientation (φ=∨ left)
        andR = std::get_if<RAnd>(&cut.right->rule);
        orR  = std::get_if<ROr>(&cut.left->rule);
        andD = cut.right.get();
        orD  = cut.left.get();
    }
    if (!andR || !orR) return nullptr;   // not an ∧-vs-∨ principal cut.

    // The ∧/∨ must be principal: it sits at the premise's last position (the
    // cut slot). RAnd/ROr.principal is that slot iff it equals |Γ_side|.
    if (andR->principal != andD->conclusion.size() - 1) return nullptr;
    if (orR->principal  != orD->conclusion.size()  - 1) return nullptr;

    const Deriv* Lb = andR->left.get();      // Π₁ ++ {β}
    const Deriv* Lg = andR->right.get();     // Π₂ ++ {γ}
    const Deriv* Oc = orR->child.get();      // C_∨ ++ {β̄, γ̄}
    const std::size_t cv = Oc->conclusion.size() - 2;   // |C_∨|

    const std::vector<FormulaHandle>& LbC = Lb->conclusion;
    const std::vector<FormulaHandle>& LgC = Lg->conclusion;
    const std::vector<FormulaHandle>& OcC = Oc->conclusion;
    const FormulaHandle beta  = LbC.back();
    const FormulaHandle gamma = LgC.back();
    const FormulaHandle gbar  = OcC.back();        // γ̄

    // Π₁, Π₂, C_∨ as sequences.
    std::vector<FormulaHandle> Pi1(LbC.begin(), LbC.end() - 1);
    std::vector<FormulaHandle> Pi2(LgC.begin(), LgC.end() - 1);
    std::vector<FormulaHandle> Cvee(OcC.begin(), OcC.begin() + cv);

    // Oc' = Oc with its last two (β̄, γ̄) swapped → C_∨, γ̄, β̄.
    auto Ocp = std::make_unique<Deriv>();
    Ocp->conclusion = OcC;
    std::swap(Ocp->conclusion[cv], Ocp->conclusion[cv + 1]);
    Ocp->rule = RExchange{cv, cv + 1, clone(*Oc)};

    // cut β.
    auto cut1 = std::make_unique<Deriv>();
    cut1->conclusion = Pi1;
    cut1->conclusion.insert(cut1->conclusion.end(), Cvee.begin(), Cvee.end());
    cut1->conclusion.push_back(gbar);
    cut1->rule = RCut{beta, clone(*Lb), std::move(Ocp)};

    // cut γ.
    auto cut2 = std::make_unique<Deriv>();
    cut2->conclusion = Pi2;
    cut2->conclusion.insert(cut2->conclusion.end(), Pi1.begin(), Pi1.end());
    cut2->conclusion.insert(cut2->conclusion.end(), Cvee.begin(), Cvee.end());
    cut2->rule = RCut{gamma, clone(*Lg), std::move(cut1)};

    // Reorder cut2 (Π₂,Π₁,C_∨) into node.conclusion (same multiset).
    auto swaps = selection_swaps(match_perm(cut2->conclusion, cut_node.conclusion));
    return apply_swaps(std::move(cut2), swaps);
}

// =========================================================================
// dispatch_cut — try cases in order. nullptr-or-error from each case.
// =========================================================================
util::Result<DerivPtr> dispatch_cut(FormulaBuilder& /*builder*/,
                                     const Deriv& cut_node,
                                     const RCut& cut) {
    // B1 — axiom / truth-literal non-principal on either side.
    if (auto out = try_b1_ax_nonprincipal(cut_node, cut, /*ax_on_left=*/true))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b1_ax_nonprincipal(cut_node, cut, /*ax_on_left=*/false))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b1_one_nonprincipal(cut_node, cut, /*one_on_left=*/true))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b1_one_nonprincipal(cut_node, cut, /*one_on_left=*/false))
        return util::Result<DerivPtr>(std::move(out));

    // B1 — axiom principal (cut formula IS one of the axiom's literals).
    if (auto out = try_b1_ax_principal(cut_node, cut, /*ax_on_left=*/true))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b1_ax_principal(cut_node, cut, /*ax_on_left=*/false))
        return util::Result<DerivPtr>(std::move(out));

    // B2 — principal logical, ∧ vs ∨ (either orientation).
    if (auto out = try_b2_and_or(cut_node, cut))
        return util::Result<DerivPtr>(std::move(out));

    // TODO Step 4 continued: B1 principal ROne; B2 ∀ vs ∃ (needs B3
    // capture-avoiding substitution); B4 permutation; B5 structural W/C/X.
    return MAKE_ERROR << "dispatch_cut: §5 case not yet implemented (Step 4 in progress)";
}

}  // namespace

std::size_t degree(FormulaHandle f) {
    if (!f.valid()) return 0;
    const Formula& formula = f.get();
    if (formula.is_predicate() || formula.is_schema_var()) return 0;
    if (formula.is_sentence()) return degree(formula.as_sentence().get().root());
    if (formula.is_compound()) {
        const auto& c = formula.as_compound();
        if (c.op == Op::Bottom) return 0;
        if (c.op == Op::Not) return 1 + degree(c.left);
        // And, Or, Implies, Iff: binary.
        return 1 + std::max(degree(c.left), degree(c.right));
    }
    if (formula.is_quantified()) {
        return 1 + degree(formula.as_quantified().body);
    }
    return 0;
}

std::optional<CutCandidate> find_topmost_max_deg_cut(const Deriv& root) {
    std::size_t max_deg = 0;
    bool any = false;
    scan_cuts(root, max_deg, any);
    if (!any) return std::nullopt;
    CutPath path, result;
    if (!find_topmost(root, max_deg, path, result)) return std::nullopt;
    return CutCandidate{std::move(result), max_deg};
}

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root) {
    TRY(validate(root));
    // B0: every additive Cut → multiplicative (CUT_ELIM_DESIGN §4). The §5
    // cases below assume the multiplicative shape (node = Γ_L ++ Γ_R).
    // Idempotent on already-multiplicative / cut-free trees.
    TRY_ASSIGN(current, additive_to_multiplicative(root));

    // Worklist loop: find topmost max-degree cut, attempt dispatch,
    // replace on success, give up on stub failure.
    while (true) {
        auto cand = find_topmost_max_deg_cut(*current);
        if (!cand) break;  // no cuts remain.

        const Deriv* cut_node = at_path(*current, cand->path);
        if (!cut_node)
            return MAKE_ERROR << "eliminate_cuts: lost cut node at path";
        const auto* cut = std::get_if<RCut>(&cut_node->rule);
        if (!cut)
            return MAKE_ERROR << "eliminate_cuts: at_path returned non-cut";

        auto reduced = dispatch_cut(builder, *cut_node, *cut);
        if (!reduced.ok()) {
            // Step 3 scaffold: all cases are stubs. Give up.
            break;
        }

        TRY_ASSIGN(new_tree, substitute_at(*current, cand->path,
                                            std::move(reduced).unwrap()));
        current = std::move(new_tree);
        TRY(validate(*current));
    }

    return util::Result<DerivPtr>(std::move(current));
}

}  // namespace logic::proof::translate::lkr_cut_elim
