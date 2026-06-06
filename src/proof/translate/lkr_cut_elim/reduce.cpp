#include "src/proof/translate/lkr_cut_elim/reduce.h"

#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <algorithm>
#include <memory>
#include <type_traits>
#include <unordered_map>
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

// --- DFS for a max-degree RCut that is TOPMOST in the proof: no cut of the
// same (maximal) degree strictly above it = none among its descendants in
// the IR. We therefore descend FIRST and only accept a node once its subtree
// has no qualifying cut. This is the order Gentzen's reduction requires —
// a max-degree cut whose two subderivations are free of max-degree cuts —
// and it is essential for the structural cases (B5), whose reduction nests a
// fresh same-degree cut inside a premise that cannot reduce until the inner
// (deeper) cut is gone.
bool find_topmost(const Deriv& d, std::size_t target_deg,
                  CutPath& path_so_far, CutPath& result) {
    return std::visit([&](auto&& r) -> bool {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            path_so_far.push_back(0);
            if (find_topmost(*r.left,  target_deg, path_so_far, result)) return true;
            path_so_far.back() = 1;
            if (find_topmost(*r.right, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            if (degree(r.cut_formula) == target_deg) {
                result = path_so_far;   // no deeper max-degree cut — accept this one.
                return true;
            }
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

// See through pure-permutation exchanges to an underlying RAx, mapping the
// axiom's literal positions up through each swap so they are expressed in
// `d`'s own conclusion coordinates. This lets B1 fire when an appending-rule
// permutation (B4) has wrapped the axiom in a φ-to-last exchange — the
// wrapper is discarded by the reduction anyway. Returns {a, b} or nullopt.
std::optional<std::pair<std::size_t, std::size_t>> effective_axiom(const Deriv* d) {
    if (const RAx* ax = std::get_if<RAx>(&d->rule))
        return std::make_pair(ax->a, ax->b);
    if (const RExchange* ex = std::get_if<RExchange>(&d->rule)) {
        auto inner = effective_axiom(ex->child.get());
        if (!inner) return std::nullopt;
        auto sw = [&](std::size_t p) {
            return p == ex->i ? ex->j : (p == ex->j ? ex->i : p);
        };
        return std::make_pair(sw(inner->first), sw(inner->second));
    }
    return std::nullopt;
}

// --- B1: axiom case, non-principal (§5.2). -------------------------------
//
// One premise closes by an axiom (possibly under permutation exchanges) with
// literals at positions {a, b}, and the cut formula (at position |Γ_side|) is
// NOT among {a, b}. The axiom closes within the side's Γ alone; the cut
// formula is just side context the axiom ignores. Discard the OTHER premise;
// produce a new RAx on the mult conclusion Γ_L ++ Γ_R.
DerivPtr try_b1_ax_nonprincipal(const Deriv& cut_node, const RCut& cut,
                                 bool ax_on_left) {
    const Deriv* ax_side = ax_on_left ? cut.left.get() : cut.right.get();
    auto ax = effective_axiom(ax_side);
    if (!ax) return nullptr;
    const std::size_t cut_pos = ax_side->conclusion.size() - 1;
    if (ax->first == cut_pos || ax->second == cut_pos) return nullptr;  // principal.

    auto out = std::make_unique<Deriv>();
    out->conclusion = cut_node.conclusion;

    if (ax_on_left) {
        out->rule = RAx{ax->first, ax->second};
    } else {
        const std::size_t gl = cut.left->conclusion.size() - 1;
        out->rule = RAx{ax->first + gl, ax->second + gl};
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
    auto ax = effective_axiom(ax_side);   // sees through permutation exchanges
    if (!ax) return nullptr;
    const std::size_t cut_pos = ax_side->conclusion.size() - 1;
    std::size_t dual_in_side;
    if      (ax->first  == cut_pos) dual_in_side = ax->second;
    else if (ax->second == cut_pos) dual_in_side = ax->first;
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

// --- B3: principal logical, ∀ vs ∃ (§5.3 + §6 capture-avoidance). --------
//
// Cut on ∀x.β where one premise ends in (∀) with eigenvar a producing
// ⊢ Γ_fa, β[x:=a], and the other ends in (∃) with witness t on the dual
// ∃x.β̄ producing ⊢ Γ_ex, β̄[x:=t]. Substitute a:=t throughout the (∀)
// subderivation Lc (sound: a∉FV(Γ_fa)), giving ⊢ Γ_fa, β[x:=t]; then cut on
// β[x:=t] (degree d(β) < d(∀x.β)) against the (∃) premise.
//
// §6 hazard: a:=t can capture if t mentions a fixed var that is also an
// eigenvar deeper in Lc. We therefore RECTIFY as we substitute — every
// eigenvar in Lc is renamed to a globally fresh index (> every fixed var in
// Lc and t) via a scope-map, BEFORE the a:=t replacement at each formula.

void collect_max_fixed_formula(FormulaHandle h, std::size_t& floor);
void collect_max_fixed_term(const Term& t, std::size_t& floor) {
    if (t.is_fixed()) floor = std::max(floor, t.as_variable() + 1);
    if (t.is_description()) collect_max_fixed_formula(t.as_description().body, floor);
}
void collect_max_fixed_formula(FormulaHandle h, std::size_t& floor) {
    const Formula& f = h.get();
    if (f.is_schema_var()) return;
    if (f.is_predicate()) {
        for (const Term& t : f.as_predicate().args()) collect_max_fixed_term(t, floor);
    } else if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid())  collect_max_fixed_formula(c.left, floor);
        if (c.right.valid()) collect_max_fixed_formula(c.right, floor);
    } else if (f.is_quantified()) {
        collect_max_fixed_formula(f.as_quantified().body, floor);
    }
}

using Rename = std::unordered_map<var_index, var_index>;

FormulaHandle apply_fv(FormulaHandle h, const Rename& rn,
                       var_index a, const Term& t, FormulaBuilder& b) {
    for (const auto& kv : rn)
        h = b.translate_term(h, Term::fixed(kv.first), Term::fixed(kv.second));
    return b.subst_fixed_impl(h, a, t, 0);
}
Term apply_fv_term(Term w, const Rename& rn,
                   var_index a, const Term& t, FormulaBuilder& b) {
    for (const auto& kv : rn)
        w = b.translate_in_term(w, Term::fixed(kv.first), Term::fixed(kv.second));
    return b.subst_fixed_in_term(w, a, t, 0);
}

// Rename in-scope eigenvars (via `rn`) and substitute a:=t through `d`.
DerivPtr freshen_subst(const Deriv& d, Rename rn, var_index a, const Term& t,
                       var_index& fresh, FormulaBuilder& b) {
    auto n = std::make_unique<Deriv>();
    n->conclusion.reserve(d.conclusion.size());
    for (FormulaHandle h : d.conclusion)
        n->conclusion.push_back(apply_fv(h, rn, a, t, b));

    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> || std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            n->rule = r;  // leaf; positions / closed targets unchanged.
        } else if constexpr (std::is_same_v<T, RExchange>) {
            n->rule = RExchange{r.i, r.j, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            n->rule = RWeaken{r.idx, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RDuplicate>) {
            n->rule = RDuplicate{r.src, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            n->rule = RContract{r.i, r.j, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            n->rule = ROr{r.principal, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            var_index e2 = fresh++;
            Rename rn2 = rn; rn2[r.eigen] = e2;
            n->rule = RForall{r.principal, e2, freshen_subst(*r.child, rn2, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            Term w2 = apply_fv_term(r.witness, rn, a, t, b);
            n->rule = RExists{r.principal, w2, freshen_subst(*r.child, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n->rule = RAnd{r.principal, r.left_partition,
                           freshen_subst(*r.left, rn, a, t, fresh, b),
                           freshen_subst(*r.right, rn, a, t, fresh, b)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            FormulaHandle cf = apply_fv(r.cut_formula, rn, a, t, b);
            n->rule = RCut{cf, freshen_subst(*r.left, rn, a, t, fresh, b),
                               freshen_subst(*r.right, rn, a, t, fresh, b)};
        }
    }, d.rule);
    return n;
}

DerivPtr try_b3_forall_exists(const Deriv& cut_node, const RCut& cut,
                              FormulaBuilder& b) {
    const RForall* fa = std::get_if<RForall>(&cut.left->rule);
    const RExists* ex = std::get_if<RExists>(&cut.right->rule);
    const Deriv* faD = cut.left.get();
    const Deriv* exD = cut.right.get();
    bool fa_on_left = true;
    if (!fa || !ex) {
        fa = std::get_if<RForall>(&cut.right->rule);
        ex = std::get_if<RExists>(&cut.left->rule);
        faD = cut.right.get();
        exD = cut.left.get();
        fa_on_left = false;
    }
    if (!fa || !ex) return nullptr;
    // Principal: the ∀ / ∃ is the cut slot (last position of its premise).
    if (fa->principal != faD->conclusion.size() - 1) return nullptr;
    if (ex->principal != exD->conclusion.size() - 1) return nullptr;

    // Fresh floor: above every fixed var in Lc and the witness t.
    std::size_t fresh = fa->eigen + 1;
    for (FormulaHandle h : fa->child->conclusion) collect_max_fixed_formula(h, fresh);
    collect_max_fixed_term(ex->witness, fresh);

    // Lc' = Lc with a:=t (rectified). Concl = Γ_fa ++ {β[x:=t]}.
    DerivPtr Lcp = freshen_subst(*fa->child, Rename{}, fa->eigen, ex->witness, fresh, b);
    DerivPtr Rc  = clone(*ex->child);   // Γ_ex ++ {β̄[x:=t]}

    auto out = std::make_unique<Deriv>();
    out->conclusion = cut_node.conclusion;
    if (fa_on_left) {
        FormulaHandle cf = Lcp->conclusion.back();      // β[x:=t]
        out->rule = RCut{cf, std::move(Lcp), std::move(Rc)};
    } else {
        FormulaHandle cf = Rc->conclusion.back();        // β̄[x:=t]
        out->rule = RCut{cf, std::move(Rc), std::move(Lcp)};
    }
    return out;
}

// --- B4: permutation / commutative case (§5.4). --------------------------
//
// The cut formula is a SIDE formula of one premise's last rule R (R's
// principal ≠ the cut slot). Permute the cut ABOVE R: cut φ out of R's
// premise against the other side, then re-apply R below the cut. The cut
// keeps its degree but moves strictly upward (rank decreases), so the
// worklist eventually reaches a principal/axiom position.
//
// Implemented uniformly with the permutation helpers: find φ in R's premise,
// exchange it to the cut slot, cut, then reorder (by formula-matching) to the
// shape R consumes, and wrap in R. Currently: ROr on the left premise.

// Cut φ out of `prem` against `other` and reorder the result to `target`
// (same multiset). `prem` ends the cut on φ; `other` carries φ̄ at its last.
DerivPtr cut_out_and_reorder(const Deriv* prem, FormulaHandle phi,
                             const Deriv* other,
                             const std::vector<FormulaHandle>& target) {
    // Move some occurrence of φ to prem's last position.
    std::size_t last = prem->conclusion.size() - 1;
    std::size_t q = last;
    for (std::size_t k = 0; k < prem->conclusion.size(); ++k)
        if (prem->conclusion[k] == phi) { q = k; break; }
    DerivPtr px = clone(*prem);
    if (q != last) {
        auto ex = std::make_unique<Deriv>();
        ex->conclusion = px->conclusion;
        std::swap(ex->conclusion[q], ex->conclusion[last]);
        ex->rule = RExchange{q, last, std::move(px)};
        px = std::move(ex);
    }
    // New cut on φ: node = (px minus φ) ++ (other minus φ̄).
    auto nc = std::make_unique<Deriv>();
    nc->conclusion.assign(px->conclusion.begin(), px->conclusion.end() - 1);
    nc->conclusion.insert(nc->conclusion.end(),
                          other->conclusion.begin(), other->conclusion.end() - 1);
    nc->rule = RCut{phi, std::move(px), clone(*other)};
    return apply_swaps(std::move(nc), selection_swaps(match_perm(nc->conclusion, target)));
}

// `remap`/`cs` carry the cut premise's geometry after PEELING any leading
// exchanges (see peel_exchanges): remap[k] = the node position of the under-
// lying rule's conclusion position k; cs = φ's position within it. remap[cs]
// is the invalid sentinel below (φ has no node position — it is the cut slot,
// consumed by the cut). Permuting past the rule UNDER an exchange chain — not
// just a bare top rule — is what lets B4 drive an appending rule (ROr / RAnd /
// RDuplicate / quantifier) over a NON-axiom rule, the deep-chain case.
constexpr std::size_t kNoPos = static_cast<std::size_t>(-1);

struct Peeled {
    const Deriv*              cur;     // underlying rule (exchanges stripped)
    std::vector<std::size_t>  remap;   // cur position → node position (kNoPos at cs)
    std::size_t               cs;      // φ position in cur
};

// Peel all leading RExchange nodes off `prem`, folding their permutations into
// `remap`. `base` is the premise's offset into node (0 left, |Γ_L| right). The
// φ-to-last exchanges inserted by cut_out_and_reorder, and any clean side
// exchanges, are absorbed transparently — the cut permutes past them.
Peeled peel_exchanges(const Deriv* prem, std::size_t base) {
    std::vector<std::size_t> remap(prem->conclusion.size());
    for (std::size_t k = 0; k < remap.size(); ++k) remap[k] = base + k;
    std::size_t cs = prem->conclusion.size() - 1;   // φ is at the last position
    remap[cs] = kNoPos;
    const Deriv* cur = prem;
    while (const RExchange* r = std::get_if<RExchange>(&cur->rule)) {
        auto sw = [&](std::size_t x) { return x == r->i ? r->j : (x == r->j ? r->i : x); };
        std::vector<std::size_t> nr(remap.size());
        for (std::size_t k = 0; k < nr.size(); ++k) nr[k] = remap[sw(k)];
        remap = std::move(nr);
        cs = sw(cs);
        cur = r->child.get();
    }
    return {cur, std::move(remap), cs};
}

// Permute the cut past a UNARY rule R = `cur`'s top rule (exchanges already
// peeled), where R's affected position ≠ the cut slot. `cut_formula` is the
// formula to cut out of R's premise (φ on the left, φ̄ on the right); `other`
// is the opposite cut premise. Returns the rebuilt R{…, cut} or nullptr.
DerivPtr try_b4_unary(const std::vector<FormulaHandle>& node, const Deriv* cur,
                      const std::vector<std::size_t>& remap, std::size_t cs,
                      FormulaHandle cut_formula, const Deriv* other,
                      FormulaBuilder& b) {
    if (const ROr* r = std::get_if<ROr>(&cur->rule)) {
        if (r->principal == cs) return nullptr;            // principal → B2
        const Formula& f = node[remap[r->principal]].get();
        std::vector<FormulaHandle> target = node;
        target[remap[r->principal]] = f.as_compound().left;
        target.push_back(f.as_compound().right);
        DerivPtr child = cut_out_and_reorder(r->child.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = ROr{remap[r->principal], std::move(child)};
        return out;
    }
    if (const RExists* r = std::get_if<RExists>(&cur->rule)) {
        if (r->principal == cs) return nullptr;            // principal → B3
        const Formula& f = node[remap[r->principal]].get();   // ∃x.ψ
        FormulaHandle inst = b.instantiate_quantifier_body(f.as_quantified().body, r->witness);
        std::vector<FormulaHandle> target = node;
        target[remap[r->principal]] = inst;
        DerivPtr child = cut_out_and_reorder(r->child.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = RExists{remap[r->principal], r->witness, std::move(child)};
        return out;
    }
    if (const RForall* r = std::get_if<RForall>(&cur->rule)) {
        if (r->principal == cs) return nullptr;            // principal → B3
        // Rectify the eigenvar so it cannot be captured by `other`'s context.
        std::size_t fresh = r->eigen + 1;
        for (FormulaHandle h : node) collect_max_fixed_formula(h, fresh);
        for (FormulaHandle h : other->conclusion) collect_max_fixed_formula(h, fresh);
        for (FormulaHandle h : r->child->conclusion) collect_max_fixed_formula(h, fresh);
        var_index e2 = fresh++;
        DerivPtr Rc2 = freshen_subst(*r->child, Rename{}, r->eigen, Term::fixed(e2), fresh, b);
        const Formula& f = node[remap[r->principal]].get();   // ∀x.ψ
        FormulaHandle inst = b.instantiate_quantifier_body(f.as_quantified().body, Term::fixed(e2));
        std::vector<FormulaHandle> target = node;
        target[remap[r->principal]] = inst;
        DerivPtr child = cut_out_and_reorder(Rc2.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = RForall{remap[r->principal], e2, std::move(child)};
        return out;
    }
    if (const RWeaken* r = std::get_if<RWeaken>(&cur->rule)) {
        if (r->idx == cs) return nullptr;                  // dropping φ → B5
        std::vector<FormulaHandle> target = node;
        target.erase(target.begin() + remap[r->idx]);
        DerivPtr child = cut_out_and_reorder(r->child.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = RWeaken{remap[r->idx], std::move(child)};
        return out;
    }
    if (const RContract* r = std::get_if<RContract>(&cur->rule)) {
        if (r->i == cs || r->j == cs) return nullptr;
        std::vector<FormulaHandle> target = node;
        target.erase(target.begin() + remap[r->j]);
        DerivPtr child = cut_out_and_reorder(r->child.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = RContract{remap[r->i], remap[r->j], std::move(child)};
        return out;
    }
    if (const RDuplicate* r = std::get_if<RDuplicate>(&cur->rule)) {
        if (r->src == cs) return nullptr;        // duplicating φ → contraction-of-cut (B5)
        std::vector<FormulaHandle> target = node;
        target.push_back(node[remap[r->src]]);
        DerivPtr child = cut_out_and_reorder(r->child.get(), cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        out->rule = RDuplicate{remap[r->src], std::move(child)};
        return out;
    }
    // RExchange is impossible here (peeled). RAnd handled separately; leaves B1.
    return nullptr;
}

// Permute the cut past a binary RAnd = `cur`'s top rule (exchanges peeled).
// The cut formula sits in exactly one of the ∧'s two sub-premises (determined
// by the partition); cut it into THAT sub-premise, leave the other untouched,
// and re-apply (∧) below — routing the other cut side's Γ into the same branch.
// `on_left` = whether `cur` is the cut's LEFT premise (fixes where `other`'s Γ
// sits in node).
DerivPtr try_b4_and(const std::vector<FormulaHandle>& node, const Deriv* cur,
                    const std::vector<std::size_t>& remap, std::size_t cs,
                    FormulaHandle cut_formula, const Deriv* other, bool on_left) {
    const RAnd* a = std::get_if<RAnd>(&cur->rule);
    if (!a) return nullptr;
    if (a->principal == cs) return nullptr;               // ∧ is the cut formula → B2
    const std::size_t og = other->conclusion.size() - 1;  // |Γ_other|
    const Formula& f = node[remap[a->principal]].get();   // α∧γ
    FormulaHandle alpha = f.as_compound().left, gamma = f.as_compound().right;

    bool cs_in_lp = false;
    for (std::size_t p : a->left_partition) if (p == cs) { cs_in_lp = true; break; }

    // node positions of `cur`'s left-partition slice.
    std::vector<bool> in_lp_node(node.size(), false);
    for (std::size_t p : a->left_partition)
        if (p != cs) in_lp_node[remap[p]] = true;
    // `other`'s Γ occupies a contiguous block: the end of node if `cur` is the
    // left premise, the start otherwise (cur's own Γ stays within its block).
    const std::size_t other_base = on_left ? (node.size() - og) : 0;

    // Decide which branch the cut formula (and `other`'s Γ) flow into.
    auto build = [&](bool into_left) -> DerivPtr {
        const Deriv* into  = into_left ? a->left.get()  : a->right.get();
        FormulaHandle tail = into_left ? alpha : gamma;
        std::vector<std::size_t> part;          // = the new left_partition
        std::vector<FormulaHandle> target;
        for (std::size_t k = 0; k < node.size(); ++k) {
            if (k == remap[a->principal]) continue;
            bool in_left_branch = in_lp_node[k];
            if (k >= other_base && k < other_base + og) in_left_branch = into_left;
            if (in_left_branch) part.push_back(k);
            if (in_left_branch == into_left) target.push_back(node[k]);
        }
        target.push_back(tail);
        DerivPtr cutd = cut_out_and_reorder(into, cut_formula, other, target);
        auto out = std::make_unique<Deriv>(); out->conclusion = node;
        if (into_left)
            out->rule = RAnd{remap[a->principal], part, std::move(cutd), clone(*a->right)};
        else
            out->rule = RAnd{remap[a->principal], part, clone(*a->left), std::move(cutd)};
        return out;
    };
    return build(cs_in_lp);
}

DerivPtr try_b4_permute(const Deriv& cut_node, const RCut& cut, FormulaBuilder& b) {
    const std::vector<FormulaHandle>& node = cut_node.conclusion;
    const std::size_t gl = cut.left->conclusion.size() - 1;
    FormulaHandle phibar = cut.right->conclusion.back();

    Peeled L = peel_exchanges(cut.left.get(), 0);
    if (auto out = try_b4_unary(node, L.cur, L.remap, L.cs, cut.cut_formula,
                                cut.right.get(), b))
        return out;
    if (auto out = try_b4_and(node, L.cur, L.remap, L.cs, cut.cut_formula,
                              cut.right.get(), /*on_left=*/true))
        return out;

    Peeled Rt = peel_exchanges(cut.right.get(), gl);
    if (auto out = try_b4_unary(node, Rt.cur, Rt.remap, Rt.cs, phibar,
                                cut.left.get(), b))
        return out;
    if (auto out = try_b4_and(node, Rt.cur, Rt.remap, Rt.cs, phibar,
                              cut.left.get(), /*on_left=*/false))
        return out;
    return nullptr;
}

// --- B5: structural cases (§5.5). ----------------------------------------
//
// The cut formula is PRINCIPAL in a structural rule of one premise:
//   - introduced by (W)            → dead cut (try_b5_weaken_dead)
//   - produced by a contraction    → duplicate-and-cut (try_b5_contraction)
// (Exchange is pure permutation — handled by B4 / the φ-to-last machinery.)

// --- B5-W: Weakening dead cut. -------------------------------------------
//
// The cut formula was weakened into one premise: that premise is
// RWeaken{idx = cut slot}, whose child proves Γ_side WITHOUT the cut formula.
// The cut is then DEAD — discard the OTHER premise entirely and weaken the
// child up to the multiplicative conclusion Γ_L ++ Γ_R. The cut vanishes.
DerivPtr try_b5_weaken_dead(const Deriv& cut_node, const RCut& cut,
                            bool w_on_left) {
    const Deriv* w_side = w_on_left ? cut.left.get() : cut.right.get();
    const RWeaken* w = std::get_if<RWeaken>(&w_side->rule);
    if (!w) return nullptr;
    const std::size_t cs = w_side->conclusion.size() - 1;   // cut slot
    if (w->idx != cs) return nullptr;     // weakening a context formula → B4.

    const std::size_t gl = cut.left->conclusion.size() - 1;
    const std::size_t gr = cut.right->conclusion.size() - 1;
    const std::vector<FormulaHandle>& full = cut_node.conclusion;  // Γ_L ++ Γ_R

    // The W-premise's child proves Γ_side; weaken in the OTHER side's Γ.
    std::size_t lo, hi;
    if (w_on_left) { lo = gl; hi = gl + gr; }   // keep Γ_L, weaken Γ_R back in
    else           { lo = 0;  hi = gl;      }   // keep Γ_R, weaken Γ_L back in

    std::vector<std::size_t> drop_idxs;          // descending
    for (std::size_t i = hi; i-- > lo; ) drop_idxs.push_back(i);

    std::vector<std::vector<FormulaHandle>> concls;
    concls.push_back(full);
    for (std::size_t d : drop_idxs) {
        std::vector<FormulaHandle> next = concls.back();
        next.erase(next.begin() + d);
        concls.push_back(std::move(next));
    }
    // concls.back() == child->conclusion (Γ_side).

    DerivPtr cur = clone(*w->child);
    for (std::size_t k = drop_idxs.size(); k-- > 0; ) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = concls[k];
        node->rule = RWeaken{drop_idxs[k], std::move(cur)};
        cur = std::move(node);
    }
    return cur;   // conclusion == cut_node.conclusion
}

// Bubble position `from` to the last position via adjacent exchanges.
DerivPtr rotate_to_back(DerivPtr d, std::size_t from) {
    const std::size_t last = d->conclusion.size() - 1;
    DerivPtr cur = std::move(d);
    for (std::size_t k = from; k < last; ++k) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = cur->conclusion;
        std::swap(node->conclusion[k], node->conclusion[k + 1]);
        node->rule = RExchange{k, k + 1, std::move(cur)};
        cur = std::move(node);
    }
    return cur;
}

// --- B5-C: Contraction on the cut. ---------------------------------------
//
// The cut formula on one premise was produced by a contraction. In the goal-
// directed IR a forward contraction ⊢ Δ,ψ,ψ ⟹ ⊢ Δ,ψ is an RDuplicate{src}:
// node = Δ,ψ, child = Δ,ψ,ψ (the duplicated copy appended). It is the
// "contraction of the cut" exactly when src = cut slot (the duplicated copy
// IS the cut formula). Gentzen's reduction (CUT_ELIM_DESIGN §5.5) DUPLICATES
// the other premise O = ⊢ Γ_O,ψ and cuts it against the contraction PREMISE
// C2 = ⊢ Γ_C,ψ̄,ψ̄ twice, then contracts away the doubled Γ_O:
//   cut1 : O × C2          ⟹ ⊢ Γ_O,Γ_C,ψ̄
//   cut2 : O × cut1        ⟹ ⊢ Γ_O,Γ_O,Γ_C
//   then C×|Γ_O|           ⟹ ⊢ Γ_O,Γ_C
// The two new cuts keep the degree but are pushed strictly upward (they cut
// against C2, the contraction's premise — strictly smaller rank), so the
// lexicographic (degree, rank) measure still descends.
DerivPtr try_b5_contraction(const Deriv& cut_node, const RCut& cut,
                            bool dup_on_left) {
    const Deriv* dup_side = dup_on_left ? cut.left.get() : cut.right.get();
    const RDuplicate* dup = std::get_if<RDuplicate>(&dup_side->rule);
    if (!dup) return nullptr;
    const std::size_t cs = dup_side->conclusion.size() - 1;   // cut slot
    if (dup->src != cs) return nullptr;   // duplicating a context formula → B4.

    const std::size_t gl = cut.left->conclusion.size() - 1;   // |Γ_L|
    const std::size_t gr = cut.right->conclusion.size() - 1;  // |Γ_R|
    const FormulaHandle phi = cut.cut_formula;
    const Deriv* C2 = dup->child.get();    // proves Γ_C ++ {ψ, ψ}

    if (dup_on_left) {
        // Contraction on the LEFT premise: C2 = Γ_L ++ {φ, φ}, O = Γ_R ++ {φ̄}.
        const Deriv* O = cut.right.get();
        // cut1 = RCut{φ, C2, O}: node = Γ_L ++ {φ} ++ Γ_R (φ left in the middle).
        std::vector<FormulaHandle> n1(C2->conclusion.begin(), C2->conclusion.end() - 1);
        n1.insert(n1.end(), O->conclusion.begin(), O->conclusion.end() - 1);
        auto cut1 = std::make_unique<Deriv>();
        cut1->conclusion = std::move(n1);
        cut1->rule = RCut{phi, clone(*C2), clone(*O)};
        // Rotate the residual φ (at position gl) to the back → Γ_L ++ Γ_R ++ {φ}.
        DerivPtr cut1r = rotate_to_back(std::move(cut1), gl);
        // cut2 = RCut{φ, cut1r, O}: node = Γ_L ++ Γ_R ++ Γ_R (extra Γ_R at end).
        std::vector<FormulaHandle> n2(cut1r->conclusion.begin(), cut1r->conclusion.end() - 1);
        n2.insert(n2.end(), O->conclusion.begin(), O->conclusion.end() - 1);
        auto cut2 = std::make_unique<Deriv>();
        cut2->conclusion = std::move(n2);
        cut2->rule = RCut{phi, std::move(cut1r), clone(*O)};
        // Fold the trailing Γ_R copy into the kept Γ_R (positions gl..gl+gr-1).
        DerivPtr cur = std::move(cut2);
        for (std::size_t j = gr; j-- > 0; ) {
            auto node = std::make_unique<Deriv>();
            node->conclusion = cur->conclusion;
            node->conclusion.pop_back();
            node->rule = RDuplicate{gl + j, std::move(cur)};
            cur = std::move(node);
        }
        return cur;   // conclusion == Γ_L ++ Γ_R
    } else {
        // Contraction on the RIGHT premise: C2 = Γ_R ++ {φ̄, φ̄}, O = Γ_L ++ {φ}.
        const Deriv* O = cut.left.get();
        // cut1 = RCut{φ, O, C2}: node = Γ_L ++ Γ_R ++ {φ̄} (φ̄ already at back).
        std::vector<FormulaHandle> n1(O->conclusion.begin(), O->conclusion.end() - 1);
        n1.insert(n1.end(), C2->conclusion.begin(), C2->conclusion.end() - 1);
        auto cut1 = std::make_unique<Deriv>();
        cut1->conclusion = std::move(n1);
        cut1->rule = RCut{phi, clone(*O), clone(*C2)};
        // cut2 = RCut{φ, O, cut1}: node = Γ_L ++ Γ_L ++ Γ_R (extra Γ_L in middle).
        std::vector<FormulaHandle> n2(O->conclusion.begin(), O->conclusion.end() - 1);
        n2.insert(n2.end(), cut1->conclusion.begin(), cut1->conclusion.end() - 1);
        auto cut2 = std::make_unique<Deriv>();
        cut2->conclusion = std::move(n2);
        cut2->rule = RCut{phi, clone(*O), std::move(cut1)};
        // Reorder Γ_L ++ Γ_L ++ Γ_R → Γ_L ++ Γ_R ++ Γ_L (extra Γ_L at the end).
        std::vector<std::size_t> m(2 * gl + gr);
        for (std::size_t t = 0; t < gl; ++t) m[t]           = t;            // keep Γ_L
        for (std::size_t t = 0; t < gr; ++t) m[gl + t]      = 2 * gl + t;   // Γ_R block
        for (std::size_t t = 0; t < gl; ++t) m[gl + gr + t] = gl + t;       // spare Γ_L
        DerivPtr cur = apply_swaps(std::move(cut2), selection_swaps(m));
        // Fold the trailing Γ_L copy into the kept Γ_L (positions 0..gl-1).
        for (std::size_t j = gl; j-- > 0; ) {
            auto node = std::make_unique<Deriv>();
            node->conclusion = cur->conclusion;
            node->conclusion.pop_back();
            node->rule = RDuplicate{j, std::move(cur)};
            cur = std::move(node);
        }
        return cur;   // conclusion == Γ_L ++ Γ_R
    }
}

// =========================================================================
// dispatch_cut — try cases in order. nullptr-or-error from each case.
// =========================================================================
util::Result<DerivPtr> dispatch_cut(FormulaBuilder& builder,
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

    // B3 — principal logical, ∀ vs ∃ (capture-avoiding witness substitution).
    if (auto out = try_b3_forall_exists(cut_node, cut, builder))
        return util::Result<DerivPtr>(std::move(out));

    // B5 — structural principal: the cut formula was introduced by (W) [dead
    // cut] or produced by a contraction (RDuplicate at the cut slot). Tried
    // before B4 so the cheap structural reduction wins over a generic
    // permutation; B5/B4 are disjoint anyway (cut-slot vs non-cut-slot).
    if (auto out = try_b5_weaken_dead(cut_node, cut, /*w_on_left=*/true))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b5_weaken_dead(cut_node, cut, /*w_on_left=*/false))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b5_contraction(cut_node, cut, /*dup_on_left=*/true))
        return util::Result<DerivPtr>(std::move(out));
    if (auto out = try_b5_contraction(cut_node, cut, /*dup_on_left=*/false))
        return util::Result<DerivPtr>(std::move(out));

    // B4 — permutation (cut formula is a side formula of a premise's rule).
    if (auto out = try_b4_permute(cut_node, cut, builder))
        return util::Result<DerivPtr>(std::move(out));

    // TODO Step 4 continued: B1 principal ROne; B4 appending rules over
    // non-axiom chains (φ-position-aware permutation); Stage A RLemma inlining.
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

// =========================================================================
// Stage A — lemma inlining (CUT_ELIM_DESIGN §3, §7a).
//
// A proven theorem cited by RLemma carries a cached, cut-free, lemma-free
// §11 proof of ⊢ φ_L. To discharge the citation, REPLAY that proof with the
// citing node's other formulas Γ prepended as inert context: every spliced
// sequent gains Γ; no rule inspects it; axioms/lemmas close ignoring it. The
// result derives ⊢ Γ, φ_L with no Cut and no RLemma introduced.
//
// Axiom / schema citations (no cached proof) are IRREDUCIBLE (§7a) — left
// untouched. They are the standard residue of the extended Hauptsatz.
// =========================================================================

namespace {

// Greatest fixed-variable index used anywhere in `d` (conclusions, witnesses,
// eigenvars), as a floor for fresh eigenvariable allocation during rectify.
void collect_max_fixed_deriv(const Deriv& d, std::size_t& floor) {
    for (FormulaHandle h : d.conclusion) collect_max_fixed_formula(h, floor);
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RExchange> || std::is_same_v<T, RWeaken> ||
                      std::is_same_v<T, RDuplicate> || std::is_same_v<T, RContract> ||
                      std::is_same_v<T, ROr> || std::is_same_v<T, RForall>) {
            if constexpr (std::is_same_v<T, RForall>) floor = std::max(floor, r.eigen + 1);
            collect_max_fixed_deriv(*r.child, floor);
        } else if constexpr (std::is_same_v<T, RExists>) {
            collect_max_fixed_term(r.witness, floor);
            collect_max_fixed_deriv(*r.child, floor);
        } else if constexpr (std::is_same_v<T, RAnd> || std::is_same_v<T, RCut>) {
            collect_max_fixed_deriv(*r.left, floor);
            collect_max_fixed_deriv(*r.right, floor);
        }
        // RAx / ROne / RLemma: leaves, conclusion already scanned.
    }, d.rule);
}

// Prepend `gamma` to every sequent of `d`, shifting all positional fields by
// |gamma|. The §11 rules act on their (shifted) principal; gamma rides as
// inert context. Binary rules (RAnd/RCut) route gamma entirely into the LEFT
// premise (sound: context placement is free), so the right premise is cloned
// unchanged. Lemma proofs are cut-free + lemma-free, so RCut/RLemma here are
// for totality only.
DerivPtr prepend_context(const Deriv& d, const std::vector<FormulaHandle>& gamma) {
    const std::size_t g = gamma.size();
    auto n = std::make_unique<Deriv>();
    n->conclusion.reserve(g + d.conclusion.size());
    n->conclusion.insert(n->conclusion.end(), gamma.begin(), gamma.end());
    n->conclusion.insert(n->conclusion.end(), d.conclusion.begin(), d.conclusion.end());

    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx>) {
            n->rule = RAx{r.a + g, r.b + g};
        } else if constexpr (std::is_same_v<T, ROne>) {
            n->rule = ROne{r.idx + g};
        } else if constexpr (std::is_same_v<T, RLemma>) {
            n->rule = r;   // inert leaf; φ closes ignoring the shifted context.
        } else if constexpr (std::is_same_v<T, RExchange>) {
            n->rule = RExchange{r.i + g, r.j + g, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            n->rule = RWeaken{r.idx + g, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RDuplicate>) {
            n->rule = RDuplicate{r.src + g, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            n->rule = RContract{r.i + g, r.j + g, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            n->rule = ROr{r.principal + g, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            n->rule = RForall{r.principal + g, r.eigen, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            n->rule = RExists{r.principal + g, r.witness, prepend_context(*r.child, gamma)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            std::vector<std::size_t> part;
            part.reserve(g + r.left_partition.size());
            for (std::size_t k = 0; k < g; ++k) part.push_back(k);   // gamma → left branch
            for (std::size_t p : r.left_partition) part.push_back(p + g);
            n->rule = RAnd{r.principal + g, std::move(part),
                           prepend_context(*r.left, gamma), clone(*r.right)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            n->rule = RCut{r.cut_formula, prepend_context(*r.left, gamma), clone(*r.right)};
        }
    }, d.rule);
    return n;
}

// Splice one proven-theorem RLemma node: replay `PL` (a cut-free proof of
// ⊢ φ_L) with the node's other formulas as inert context, concluding the
// node's own sequent. Returns nullptr if the citation is not inlinable
// (schema / base-axiom — no cached proof).
util::Result<DerivPtr> splice_lemma(FormulaBuilder& b, const Deriv& node,
                                    const RLemma& lem, const LemmaProofs& lemmas) {
    const AxiomRef* ax = std::get_if<AxiomRef>(&lem.target);
    if (!ax) return util::Result<DerivPtr>(DerivPtr{});       // schema → irreducible.
    auto it = lemmas.find(ax->sentence);
    if (it == lemmas.end()) return util::Result<DerivPtr>(DerivPtr{});  // base axiom.
    const Deriv* PL = it->second;
    if (PL->conclusion.size() != 1)
        return MAKE_ERROR << "splice_lemma: lemma proof goal is not a 1-formula sequent";
    const FormulaHandle phiL = PL->conclusion[0];

    const std::vector<FormulaHandle>& C = node.conclusion;
    std::size_t pos = C.size();
    for (std::size_t k = 0; k < C.size(); ++k)
        if (C[k] == phiL) { pos = k; break; }
    if (pos == C.size())
        // The cached proof concludes a formula that does not appear in the
        // citing sequent — the citation is of a different (e.g. wrapped-goal /
        // axiom-dependent) form than this cut-free proof discharges. Treat as
        // irreducible (§7a) rather than an error: leave the RLemma in place.
        return util::Result<DerivPtr>(DerivPtr{});

    std::vector<FormulaHandle> gamma;            // C minus the φ_L slot (order kept)
    gamma.reserve(C.size() - 1);
    for (std::size_t k = 0; k < C.size(); ++k)
        if (k != pos) gamma.push_back(C[k]);

    // Rectify PL's eigenvars above every fixed var in gamma and PL, so the
    // prepended context cannot capture an eigenvariable (§6). The a:=fixed(a)
    // substitution is the identity; freshen_subst's job here is the renaming.
    std::size_t fresh = 0;
    for (FormulaHandle h : gamma) collect_max_fixed_formula(h, fresh);
    collect_max_fixed_deriv(*PL, fresh);
    DerivPtr rect = freshen_subst(*PL, Rename{}, /*a=*/0, Term::fixed(0), fresh, b);

    DerivPtr spliced = prepend_context(*rect, gamma);   // concl = gamma ++ [φ_L]

    // Reorder gamma ++ [φ_L] into C (move φ_L from the end to position `pos`).
    const std::size_t n = C.size();
    std::vector<std::size_t> m(n);
    for (std::size_t t = 0; t < pos; ++t)       m[t] = t;
    m[pos] = n - 1;                                       // φ_L (spliced last)
    for (std::size_t t = pos + 1; t < n; ++t)   m[t] = t - 1;
    return util::Result<DerivPtr>(apply_swaps(std::move(spliced), selection_swaps(m)));
}

// Rebuild `d`, splicing every inlinable proven-theorem RLemma. Cut-free lemma
// proofs are themselves lemma-free, so one pass suffices (no fixpoint).
util::Result<DerivPtr> inline_lemmas(FormulaBuilder& b, const Deriv& d,
                                     const LemmaProofs& lemmas) {
    if (const RLemma* lem = std::get_if<RLemma>(&d.rule)) {
        TRY_ASSIGN(spliced, splice_lemma(b, d, *lem, lemmas));
        if (spliced) return util::Result<DerivPtr>(std::move(spliced));
        return util::Result<DerivPtr>(clone(d));          // not inlinable — keep.
    }
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;
    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> || std::is_same_v<T, ROne>) {
            n->rule = r;
        } else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RExchange{r.i, r.j, std::move(c)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RWeaken{r.idx, std::move(c)};
        } else if constexpr (std::is_same_v<T, RDuplicate>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RDuplicate{r.src, std::move(c)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RContract{r.i, r.j, std::move(c)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = ROr{r.principal, std::move(c)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RForall{r.principal, r.eigen, std::move(c)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(c, inline_lemmas(b, *r.child, lemmas));
            n->rule = RExists{r.principal, r.witness, std::move(c)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            TRY_ASSIGN(l, inline_lemmas(b, *r.left, lemmas));
            TRY_ASSIGN(rr, inline_lemmas(b, *r.right, lemmas));
            n->rule = RAnd{r.principal, r.left_partition, std::move(l), std::move(rr)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            TRY_ASSIGN(l, inline_lemmas(b, *r.left, lemmas));
            TRY_ASSIGN(rr, inline_lemmas(b, *r.right, lemmas));
            n->rule = RCut{r.cut_formula, std::move(l), std::move(rr)};
        } else {
            n->rule = r;   // RLemma handled above.
        }
        return util::Result<DerivPtr>(std::move(n));
    }, d.rule);
}

}  // namespace

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root,
                                      const LemmaProofs& lemmas) {
    TRY(validate(root));
    // Stage A: inline proven-theorem lemma citations (§3). Run before B0/B so
    // the surrounding cuts become logical and reduce.
    TRY_ASSIGN(inlined, inline_lemmas(builder, root, lemmas));
    TRY(validate(*inlined));
    return eliminate_cuts(builder, *inlined);
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

    // Any residual (irreducible, §7a) cut is still multiplicative; convert
    // back to additive so the output emits to the additive LKR (Cut) and
    // re-verifies. No-op when fully cut-free.
    return multiplicative_to_additive(*current);
}

}  // namespace logic::proof::translate::lkr_cut_elim
