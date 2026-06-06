#include "src/proof/translate/lkr_cut_elim/reduce.h"

#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <algorithm>
#include <cstdlib>
#include <memory>
#include <type_traits>
#include <unordered_map>
#include <utility>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

// Name of the §5 case/sub-case that last fired (debug diagnostics only).
const char* g_last_case = "";

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

// --- Single-pass topmost-max-degree cut selection (B6). ------------------
//
// The driver needs the TOPMOST cut of MAXIMAL degree: a max-degree cut with
// no other max-degree cut strictly above it (= deepest in the IR, since the
// proof grows toward the leaves). This is the order Gentzen's reduction
// requires, and is essential for the structural cases (B5), whose reduction
// nests a fresh same-degree cut inside a premise that cannot reduce until the
// inner (deeper) cut is gone.
//
// Previously this took TWO full traversals — scan_cuts (global max degree)
// then find_topmost (descend to it). One bottom-up pass suffices: each call
// returns its subtree's max cut-degree and the (relative) path to the topmost
// cut achieving it. The invariant that makes this correct: we only ever follow
// a branch whose local max equals the combined max, so "topmost of local max"
// in that branch IS "topmost of the global max". Tie-breaks (prefer a child
// over self, prefer left over right) match the old DFS pre-order exactly.
struct TopmostScan {
    bool        has_cut = false;
    std::size_t max_deg = 0;
    CutPath     path;          // from this node to the chosen cut.
};
TopmostScan scan_topmost(const Deriv& d) {
    return std::visit([&](auto&& r) -> TopmostScan {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            TopmostScan L = scan_topmost(*r.left);
            TopmostScan R = scan_topmost(*r.right);
            std::size_t dg = degree(r.cut_formula);
            std::size_t m = dg;
            if (L.has_cut) m = std::max(m, L.max_deg);
            if (R.has_cut) m = std::max(m, R.max_deg);
            TopmostScan out; out.has_cut = true; out.max_deg = m;
            if (L.has_cut && L.max_deg == m) {            // deeper, prefer left.
                out.path.push_back(0);
                out.path.insert(out.path.end(), L.path.begin(), L.path.end());
            } else if (R.has_cut && R.max_deg == m) {
                out.path.push_back(1);
                out.path.insert(out.path.end(), R.path.begin(), R.path.end());
            }   // else this cut itself is the topmost of degree m (empty path).
            return out;
        } else if constexpr (std::is_same_v<T, RAnd>) {
            TopmostScan L = scan_topmost(*r.left);
            TopmostScan R = scan_topmost(*r.right);
            if (!L.has_cut && !R.has_cut) return TopmostScan{};
            std::size_t m = std::max(L.has_cut ? L.max_deg : 0,
                                     R.has_cut ? R.max_deg : 0);
            TopmostScan out; out.has_cut = true; out.max_deg = m;
            if (L.has_cut && L.max_deg == m) {
                out.path.push_back(0);
                out.path.insert(out.path.end(), L.path.begin(), L.path.end());
            } else {
                out.path.push_back(1);
                out.path.insert(out.path.end(), R.path.begin(), R.path.end());
            }
            return out;
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            TopmostScan c = scan_topmost(*r.child);
            if (!c.has_cut) return TopmostScan{};
            TopmostScan out; out.has_cut = true; out.max_deg = c.max_deg;
            out.path.push_back(0);
            out.path.insert(out.path.end(), c.path.begin(), c.path.end());
            return out;
        }
        return TopmostScan{};   // RAx / ROne / RLemma: no cut.
    }, d.rule);
}

// --- Read the subtree at a path (no ownership transfer). ---
// Mutable pointer to the owning DerivPtr slot at `path` (the slot in `root`'s
// own pointer for the empty path, else a child slot of the node above the
// target). Returning the OWNING slot lets the driver splice a reduction in
// place — `*slot = reduction` — instead of rebuilding the spine and cloning
// every sibling subtree, which is the O(tree) copy substitute_at paid every
// step (B6). Returns nullptr if the path runs off a leaf.
DerivPtr* slot_at_path(DerivPtr& root, const CutPath& path) {
    DerivPtr* slot = &root;
    for (int step : path) {
        DerivPtr* next = nullptr;
        std::visit([&](auto&& r) {
            using T = std::decay_t<decltype(r)>;
            if constexpr (std::is_same_v<T, RAnd> || std::is_same_v<T, RCut>) {
                next = (step == 0) ? &r.left : &r.right;
            } else if constexpr (std::is_same_v<T, RExchange> ||
                                 std::is_same_v<T, RWeaken>   ||
                                 std::is_same_v<T, RDuplicate>||
                                 std::is_same_v<T, RContract> ||
                                 std::is_same_v<T, ROr>       ||
                                 std::is_same_v<T, RForall>   ||
                                 std::is_same_v<T, RExists>) {
                next = &r.child;
            }
        }, (*slot)->rule);
        if (!next) return nullptr;
        slot = next;
    }
    return slot;
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

// --- exchange peeling (shared by the principal cases B2/B3/B5 and B4) ----
//
// `remap`/`cs` carry a cut premise's geometry after PEELING any leading
// exchanges: remap[k] = the node position of the underlying rule's conclusion
// position k; cs = φ's position within it. remap[cs] is the kNoPos sentinel.
// Seeing the rule UNDER a φ-to-last exchange chain — not just the bare top
// rule — is what lets every case fire on the shapes NDtoLKR / prior
// permutations produce.
constexpr std::size_t kNoPos = static_cast<std::size_t>(-1);

struct Peeled {
    const Deriv*              cur;     // underlying rule (exchanges stripped)
    std::vector<std::size_t>  remap;   // cur position → node position (kNoPos at cs)
    std::size_t               cs;      // φ position in cur
};

inline Peeled peel_exchanges(const Deriv* prem, std::size_t base) {
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

// Bubble position `from` to the last position via adjacent exchanges (move a
// rule's principal-position output to a premise's cut slot).
inline DerivPtr rotate_to_back(DerivPtr d, std::size_t from) {
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
    // Peel φ-to-last exchanges so a ∧/∨ principal on the cut formula UNDER them
    // is seen. cs = φ/φ̄ position within the peeled rule's conclusion.
    Peeled pl = peel_exchanges(cut.left.get(),  0);
    Peeled pr = peel_exchanges(cut.right.get(), 0);
    const RAnd* andR = std::get_if<RAnd>(&pl.cur->rule);
    const ROr*  orR  = std::get_if<ROr>(&pr.cur->rule);
    std::size_t and_cs = pl.cs, or_cs = pr.cs;
    if (!andR || !orR) {                 // other orientation (∨ left, ∧ right)
        andR = std::get_if<RAnd>(&pr.cur->rule);
        orR  = std::get_if<ROr>(&pl.cur->rule);
        and_cs = pr.cs; or_cs = pl.cs;
    }
    if (!andR || !orR) return nullptr;   // not an ∧-vs-∨ principal cut.

    if (andR->principal != and_cs) return nullptr;   // ∧ principal on φ
    if (orR->principal  != or_cs)  return nullptr;   // ∨ principal on φ̄

    const Deriv* Lb = andR->left.get();      // Π₁ ++ {β}
    const Deriv* Lg = andR->right.get();     // Π₂ ++ {γ}

    // Normalize the ∨-child to canonical C_∨ ++ {β̄, γ̄}: ROr puts β̄ at the
    // principal position or_cs and γ̄ at the end; move β̄ to size-2 if needed.
    const Deriv* OcRaw = orR->child.get();
    const std::size_t ocsz = OcRaw->conclusion.size();
    DerivPtr Oc_owned;
    if (or_cs == ocsz - 2) {
        Oc_owned = clone(*OcRaw);
    } else {
        Oc_owned = std::make_unique<Deriv>();
        Oc_owned->conclusion = OcRaw->conclusion;
        std::swap(Oc_owned->conclusion[or_cs], Oc_owned->conclusion[ocsz - 2]);
        Oc_owned->rule = RExchange{or_cs, ocsz - 2, clone(*OcRaw)};
    }
    const Deriv* Oc = Oc_owned.get();        // C_∨ ++ {β̄, γ̄}
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

// Greatest fixed-var index used ANYWHERE in `d` — every conclusion formula, ∃
// witness, and ∀ eigenvar, recursively. The correct floor for allocating a
// fresh eigenvariable that must avoid capture against a whole subderivation
// (§6): scanning only `d.conclusion` misses eigenvars/witnesses buried deeper,
// which is exactly the capture bug B3 / B4-unary-∀ hit on large proofs.
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
    // Peel φ-to-last exchanges so a ∀/∃ principal under them is seen.
    Peeled pl = peel_exchanges(cut.left.get(),  0);
    Peeled pr = peel_exchanges(cut.right.get(), 0);
    const RForall* fa = std::get_if<RForall>(&pl.cur->rule);
    const RExists* ex = std::get_if<RExists>(&pr.cur->rule);
    bool fa_on_left = true;
    if (!fa || !ex) {
        fa = std::get_if<RForall>(&pr.cur->rule);
        ex = std::get_if<RExists>(&pl.cur->rule);
        fa_on_left = false;
    }
    if (!fa || !ex) return nullptr;
    const std::size_t fa_cs = fa_on_left ? pl.cs : pr.cs;
    const std::size_t ex_cs = fa_on_left ? pr.cs : pl.cs;
    if (fa->principal != fa_cs) return nullptr;   // ∀ principal on φ
    if (ex->principal != ex_cs) return nullptr;   // ∃ principal on φ̄

    // Fresh floor: above every fixed var ANYWHERE in the ∀-subderivation, the
    // ∃-subderivation, and the witness t — not just their conclusions, else a
    // renamed eigenvar can collide with one buried deeper (§6 capture).
    std::size_t fresh = fa->eigen + 1;
    collect_max_fixed_deriv(*fa->child, fresh);
    collect_max_fixed_deriv(*ex->child, fresh);
    collect_max_fixed_term(ex->witness, fresh);

    // Lc' = Lc with a:=t (rectified): the instantiated body β[x:=t] sits at the
    // ∀'s principal position (fa->principal), NOT the end — rotate it to the
    // cut slot. Likewise β̄[x:=t] is at the ∃'s principal in Rc.
    DerivPtr Lcp = freshen_subst(*fa->child, Rename{}, fa->eigen, ex->witness, fresh, b);
    Lcp = rotate_to_back(std::move(Lcp), fa->principal);
    DerivPtr Rc  = clone(*ex->child);
    Rc  = rotate_to_back(std::move(Rc), ex->principal);

    // Build the residual cut with its NATURAL mult conclusion Γ_fa ++ Γ_ex,
    // then reorder to cut_node.conclusion (the peeled exchanges permuted Γ).
    auto out = std::make_unique<Deriv>();
    if (fa_on_left) {
        FormulaHandle cf = Lcp->conclusion.back();      // β[x:=t]
        out->conclusion.assign(Lcp->conclusion.begin(), Lcp->conclusion.end() - 1);
        out->conclusion.insert(out->conclusion.end(),
                               Rc->conclusion.begin(), Rc->conclusion.end() - 1);
        out->rule = RCut{cf, std::move(Lcp), std::move(Rc)};
    } else {
        FormulaHandle cf = Rc->conclusion.back();        // β̄[x:=t]
        out->conclusion.assign(Rc->conclusion.begin(), Rc->conclusion.end() - 1);
        out->conclusion.insert(out->conclusion.end(),
                               Lcp->conclusion.begin(), Lcp->conclusion.end() - 1);
        out->rule = RCut{cf, std::move(Rc), std::move(Lcp)};
    }
    auto swaps = selection_swaps(match_perm(out->conclusion, cut_node.conclusion));
    return apply_swaps(std::move(out), swaps);
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
        // Rectify the eigenvar fresh above every fixed var ANYWHERE in `other`
        // and the ∀-subderivation (whole subtrees, not just conclusions — a
        // deep eigenvar in `other` is exactly what captured e2 on the corpus),
        // and above node's vars.
        std::size_t fresh = r->eigen + 1;
        for (FormulaHandle h : node) collect_max_fixed_formula(h, fresh);
        collect_max_fixed_deriv(*other, fresh);
        collect_max_fixed_deriv(*r->child, fresh);
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

    bool into_left = false;
    for (std::size_t p : a->left_partition) if (p == cs) { into_left = true; break; }

    // node positions of `cur`'s left-partition slice.
    std::vector<bool> in_lp_node(node.size(), false);
    for (std::size_t p : a->left_partition)
        if (p != cs) in_lp_node[remap[p]] = true;
    // `other`'s Γ occupies a contiguous block: the end of node if `cur` is the
    // left premise, the start otherwise (cur's own Γ stays within its block).
    const std::size_t other_base = on_left ? (node.size() - og) : 0;
    const std::size_t prin = remap[a->principal];

    // Partition node's non-principal positions into the two branches: `other`'s
    // Γ joins the cut formula's branch (into_left); the rest keep their side.
    auto branch = [&](std::size_t k) -> bool {   // true = left branch
        if (k >= other_base && k < other_base + og) return into_left;
        return in_lp_node[k];
    };
    std::vector<std::size_t> left_pos, right_pos;
    std::vector<FormulaHandle> left_tgt, right_tgt;
    for (std::size_t k = 0; k < node.size(); ++k) {
        if (k == prin) continue;
        if (branch(k)) { left_pos.push_back(k);  left_tgt.push_back(node[k]); }
        else           { right_pos.push_back(k); right_tgt.push_back(node[k]); }
    }
    left_tgt.push_back(alpha);
    right_tgt.push_back(gamma);

    // The cut routes into the cut formula's branch (`into`); the OTHER branch is
    // untouched but must be REORDERED to node order — validate reconstructs each
    // child from the partition's NODE positions, which differ from the ∧'s own
    // order once exchanges have been peeled (remap ≠ identity).
    const Deriv* into = into_left ? a->left.get() : a->right.get();
    const Deriv* keep = into_left ? a->right.get() : a->left.get();
    const std::vector<FormulaHandle>& into_tgt = into_left ? left_tgt : right_tgt;
    const std::vector<FormulaHandle>& keep_tgt = into_left ? right_tgt : left_tgt;

    DerivPtr cutd = cut_out_and_reorder(into, cut_formula, other, into_tgt);
    DerivPtr keptd = apply_swaps(clone(*keep),
                       selection_swaps(match_perm(keep->conclusion, keep_tgt)));

    auto out = std::make_unique<Deriv>(); out->conclusion = node;
    if (into_left)
        out->rule = RAnd{prin, left_pos, std::move(cutd), std::move(keptd)};
    else
        out->rule = RAnd{prin, left_pos, std::move(keptd), std::move(cutd)};
    return out;
}

// Permute the cut past a binary RCut = `cur`'s top rule (a LOWER-degree cut in
// a premise; exchanges peeled). The cut formula ψ sits in one positional side
// (Γ_A | Γ_B) of the inner θ-cut; route the outer cut into that side, re-apply
// the inner cut, reorder to `target_node`. Only fires when degree(θ) <
// degree(ψ) — an equal/higher inner cut is a deeper max-degree cut, picked
// first by find_topmost.
DerivPtr try_b4_cut(const std::vector<FormulaHandle>& target_node, const Deriv* cur,
                    std::size_t cs, FormulaHandle cut_formula, const Deriv* other) {
    const RCut* tc = std::get_if<RCut>(&cur->rule);
    if (!tc) return nullptr;
    if (degree(tc->cut_formula) >= degree(cut_formula)) return nullptr;

    const Deriv* A = tc->left.get();              // Γ_A ++ {θ}
    const Deriv* B = tc->right.get();             // Γ_B ++ {θ̄}
    const std::size_t ga = A->conclusion.size() - 1;
    const FormulaHandle theta = tc->cut_formula;

    const bool into_left = cs < ga;               // ψ in Γ_A?
    const Deriv* into = into_left ? A : B;
    const Deriv* keep = into_left ? B : A;
    const std::size_t psi_pos = into_left ? cs : (cs - ga);   // ψ in into's context

    // target_branch = (into context minus ψ) ++ Γ_O ++ {tail}, tail = θ / θ̄.
    const FormulaHandle tail = into->conclusion.back();
    std::vector<FormulaHandle> tb;
    for (std::size_t k = 0; k + 1 < into->conclusion.size(); ++k)
        if (k != psi_pos) tb.push_back(into->conclusion[k]);
    for (std::size_t k = 0; k + 1 < other->conclusion.size(); ++k)
        tb.push_back(other->conclusion[k]);
    tb.push_back(tail);
    DerivPtr nbr = cut_out_and_reorder(into, cut_formula, other, tb);

    // Re-apply the inner cut; natural node = (branch minus tail) ++ Γ_keep.
    std::vector<FormulaHandle> nb(nbr->conclusion.begin(), nbr->conclusion.end() - 1);
    std::vector<FormulaHandle> kg(keep->conclusion.begin(), keep->conclusion.end() - 1);
    auto out = std::make_unique<Deriv>();
    if (into_left) {
        out->conclusion = nb;
        out->conclusion.insert(out->conclusion.end(), kg.begin(), kg.end());
        out->rule = RCut{theta, std::move(nbr), clone(*keep)};
    } else {
        out->conclusion = kg;
        out->conclusion.insert(out->conclusion.end(), nb.begin(), nb.end());
        out->rule = RCut{theta, clone(*keep), std::move(nbr)};
    }
    auto swaps = selection_swaps(match_perm(out->conclusion, target_node));
    return apply_swaps(std::move(out), swaps);
}

DerivPtr try_b4_permute(const Deriv& cut_node, const RCut& cut, FormulaBuilder& b) {
    const std::vector<FormulaHandle>& node = cut_node.conclusion;
    const std::size_t gl = cut.left->conclusion.size() - 1;
    FormulaHandle phibar = cut.right->conclusion.back();

    Peeled L = peel_exchanges(cut.left.get(), 0);
    if (auto out = try_b4_unary(node, L.cur, L.remap, L.cs, cut.cut_formula,
                                cut.right.get(), b)) { g_last_case = "B4-unary-L"; return out; }
    if (auto out = try_b4_and(node, L.cur, L.remap, L.cs, cut.cut_formula,
                              cut.right.get(), /*on_left=*/true)) { g_last_case = "B4-and-L"; return out; }
    if (auto out = try_b4_cut(node, L.cur, L.cs, cut.cut_formula, cut.right.get())) { g_last_case = "B4-cut-L"; return out; }

    Peeled Rt = peel_exchanges(cut.right.get(), gl);
    if (auto out = try_b4_unary(node, Rt.cur, Rt.remap, Rt.cs, phibar,
                                cut.left.get(), b)) { g_last_case = "B4-unary-R"; return out; }
    if (auto out = try_b4_and(node, Rt.cur, Rt.remap, Rt.cs, phibar,
                              cut.left.get(), /*on_left=*/false)) { g_last_case = "B4-and-R"; return out; }
    if (auto out = try_b4_cut(node, Rt.cur, Rt.cs, phibar, cut.left.get())) { g_last_case = "B4-cut-R"; return out; }
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
    // Peel φ-to-last exchanges so an RWeaken introducing the cut formula under
    // them is seen.
    Peeled pw = peel_exchanges(w_on_left ? cut.left.get() : cut.right.get(), 0);
    const RWeaken* w = std::get_if<RWeaken>(&pw.cur->rule);
    if (!w) return nullptr;
    if (w->idx != pw.cs) return nullptr;   // weakening a context formula → B4.

    // The W-premise's child proves Γ_w (its context, peeled order); the cut is
    // dead. Weaken Γ_w up to a permutation of cut_node.conclusion (adding the
    // discarded side's Γ = the multiset difference), then reorder.
    const Deriv* child = w->child.get();
    const std::vector<FormulaHandle>& gamma_w = child->conclusion;
    std::vector<FormulaHandle> to_add;
    {
        std::vector<bool> used(gamma_w.size(), false);
        for (FormulaHandle h : cut_node.conclusion) {
            bool matched = false;
            for (std::size_t k = 0; k < gamma_w.size(); ++k)
                if (!used[k] && gamma_w[k] == h) { used[k] = true; matched = true; break; }
            if (!matched) to_add.push_back(h);
        }
    }
    std::vector<FormulaHandle> N = gamma_w;                 // = Γ_w ++ to_add
    N.insert(N.end(), to_add.begin(), to_add.end());

    std::vector<std::size_t> drop;                          // descending
    for (std::size_t i = N.size(); i-- > gamma_w.size(); ) drop.push_back(i);
    std::vector<std::vector<FormulaHandle>> concls;
    concls.push_back(N);
    for (std::size_t d : drop) {
        std::vector<FormulaHandle> next = concls.back();
        next.erase(next.begin() + d);
        concls.push_back(std::move(next));
    }
    DerivPtr cur = clone(*child);
    for (std::size_t k = drop.size(); k-- > 0; ) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = concls[k];
        node->rule = RWeaken{drop[k], std::move(cur)};
        cur = std::move(node);
    }
    // cur.conclusion == N (a permutation of cut_node.conclusion); reorder.
    auto swaps = selection_swaps(match_perm(cur->conclusion, cut_node.conclusion));
    return apply_swaps(std::move(cur), swaps);
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
                            FormulaBuilder& b, var_index gfloor) {
    // Find the premise that ends in a contraction (RDuplicate{src==cut slot})
    // under φ-to-last exchanges; the other premise is O. Unified across both
    // orientations: the duplicated formula ψ (= φ or φ̄) is cut against O's dual
    // ψ̄, and the natural result Γ_C ++ Γ_o is reordered to cut_node.conclusion.
    Peeled pL = peel_exchanges(cut.left.get(),  0);
    Peeled pR = peel_exchanges(cut.right.get(), 0);
    const RDuplicate* dup = nullptr;
    const Deriv* O = nullptr; std::size_t cs_dup = 0;
    if (const auto* d = std::get_if<RDuplicate>(&pL.cur->rule); d && d->src == pL.cs) {
        dup = d; cs_dup = pL.cs; O = cut.right.get();
    } else if (const auto* d = std::get_if<RDuplicate>(&pR.cur->rule); d && d->src == pR.cs) {
        dup = d; cs_dup = pR.cs; O = cut.left.get();
    }
    if (!dup) return nullptr;

    const Deriv* C2 = dup->child.get();           // Γ_C with ψ at cs_dup and last
    const FormulaHandle psi = C2->conclusion.back();   // duplicated cut formula ψ
    const std::size_t go = O->conclusion.size() - 1;   // |Γ_o|

    // cut1 = RCut{ψ, C2, O}: consume C2's trailing ψ against O's ψ̄.
    //   node1 = (C2 minus last ψ) ++ Γ_o = curD ++ Γ_o   (ψ still at cs_dup).
    std::vector<FormulaHandle> n1(C2->conclusion.begin(), C2->conclusion.end() - 1);
    n1.insert(n1.end(), O->conclusion.begin(), O->conclusion.end() - 1);
    auto cut1 = std::make_unique<Deriv>();
    cut1->conclusion = std::move(n1);
    cut1->rule = RCut{psi, clone(*C2), clone(*O)};

    // Rotate the residual ψ (at cs_dup) to the back, then cut it again against O.
    DerivPtr cut1r = rotate_to_back(std::move(cut1), cs_dup);
    std::vector<FormulaHandle> n2(cut1r->conclusion.begin(), cut1r->conclusion.end() - 1);
    n2.insert(n2.end(), O->conclusion.begin(), O->conclusion.end() - 1);
    // The SECOND copy of O must have eigenvars distinct from the first (and from
    // everything): O is DUPLICATED here, breaking global eigenvar distinctness;
    // rectify the copy fresh above the whole current tree (gfloor) so a later
    // commutation that merges the two O-branches cannot capture (§6).
    var_index fresh = gfloor;
    DerivPtr O2 = freshen_subst(*O, Rename{}, /*a=*/0, Term::fixed(0), fresh, b);
    auto cut2 = std::make_unique<Deriv>();
    cut2->conclusion = std::move(n2);                   // (Γ_C ++ Γ_o) ++ Γ_o
    cut2->rule = RCut{psi, std::move(cut1r), std::move(O2)};

    // Fold the trailing Γ_o copy into the kept one (kept block starts at |Γ_C|).
    const std::size_t base_o = cut2->conclusion.size() - 2 * go;
    DerivPtr cur = std::move(cut2);
    for (std::size_t j = go; j-- > 0; ) {
        auto node = std::make_unique<Deriv>();
        node->conclusion = cur->conclusion;
        node->conclusion.pop_back();
        node->rule = RDuplicate{base_o + j, std::move(cur)};
        cur = std::move(node);
    }
    // cur.conclusion == Γ_C ++ Γ_o (natural); reorder to cut_node.conclusion.
    auto swaps = selection_swaps(match_perm(cur->conclusion, cut_node.conclusion));
    return apply_swaps(std::move(cur), swaps);
}

// =========================================================================
// dispatch_cut — try cases in order. nullptr-or-error from each case.
// =========================================================================
util::Result<DerivPtr> dispatch_cut(FormulaBuilder& builder,
                                     const Deriv& cut_node,
                                     const RCut& cut,
                                     var_index gfloor) {
#define DISPATCH_TRY(NAME, EXPR)                              \
    if (auto out = (EXPR)) {                                  \
        g_last_case = NAME;                                   \
        return util::Result<DerivPtr>(std::move(out));        \
    }
    // B1 — axiom / truth-literal non-principal on either side.
    DISPATCH_TRY("B1-ax-nonprin-L", try_b1_ax_nonprincipal(cut_node, cut, true))
    DISPATCH_TRY("B1-ax-nonprin-R", try_b1_ax_nonprincipal(cut_node, cut, false))
    DISPATCH_TRY("B1-one-nonprin-L", try_b1_one_nonprincipal(cut_node, cut, true))
    DISPATCH_TRY("B1-one-nonprin-R", try_b1_one_nonprincipal(cut_node, cut, false))
    // B1 — axiom principal (cut formula IS one of the axiom's literals).
    DISPATCH_TRY("B1-ax-prin-L", try_b1_ax_principal(cut_node, cut, true))
    DISPATCH_TRY("B1-ax-prin-R", try_b1_ax_principal(cut_node, cut, false))
    // B2 — principal logical, ∧ vs ∨ (either orientation).
    DISPATCH_TRY("B2-and-or", try_b2_and_or(cut_node, cut))
    // B3 — principal logical, ∀ vs ∃ (capture-avoiding witness substitution).
    DISPATCH_TRY("B3-forall-exists", try_b3_forall_exists(cut_node, cut, builder))
    // B5 — structural principal (W dead cut / C contraction). Before B4.
    DISPATCH_TRY("B5-weaken-L", try_b5_weaken_dead(cut_node, cut, true))
    DISPATCH_TRY("B5-weaken-R", try_b5_weaken_dead(cut_node, cut, false))
    DISPATCH_TRY("B5-contraction", try_b5_contraction(cut_node, cut, builder, gfloor))
    // B4 — permutation (cut formula is a side formula of a premise's rule).
    // try_b4_permute sets g_last_case to the specific sub-case itself.
    if (auto out = try_b4_permute(cut_node, cut, builder))
        return util::Result<DerivPtr>(std::move(out));
#undef DISPATCH_TRY
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
    TopmostScan s = scan_topmost(root);
    if (!s.has_cut) return std::nullopt;
    return CutCandidate{std::move(s.path), s.max_deg};
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

namespace {

// Debug dump of a Deriv subtree (LKR_CUT_ELIM_DEBUG): rule + key fields + the
// node's conclusion as formula strings. Used to capture the exact cut a buggy
// reduction was applied to, for building a focused §8 repro.
void dump_deriv(const Deriv& d, int indent) {
    std::string pad(static_cast<std::size_t>(indent) * 2, ' ');
    std::string concl;
    for (FormulaHandle h : d.conclusion)
        concl += (concl.empty() ? "" : ", ") + h.get().to_string();
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        const char* nm =
            std::is_same_v<T, RAx> ? "Ax" : std::is_same_v<T, ROne> ? "One" :
            std::is_same_v<T, RLemma> ? "Lemma" : std::is_same_v<T, RExchange> ? "Exch" :
            std::is_same_v<T, RWeaken> ? "Weak" : std::is_same_v<T, RDuplicate> ? "Dup" :
            std::is_same_v<T, RContract> ? "Contr" : std::is_same_v<T, RAnd> ? "And" :
            std::is_same_v<T, ROr> ? "Or" : std::is_same_v<T, RForall> ? "Forall" :
            std::is_same_v<T, RExists> ? "Exists" : "Cut";
        std::fprintf(stderr, "%s%s |- %s\n", pad.c_str(), nm, concl.c_str());
        if constexpr (std::is_same_v<T, RExchange> || std::is_same_v<T, RWeaken> ||
                      std::is_same_v<T, RDuplicate> || std::is_same_v<T, RContract> ||
                      std::is_same_v<T, ROr> || std::is_same_v<T, RForall> ||
                      std::is_same_v<T, RExists>) {
            dump_deriv(*r.child, indent + 1);
        } else if constexpr (std::is_same_v<T, RAnd> || std::is_same_v<T, RCut>) {
            dump_deriv(*r.left, indent + 1);
            dump_deriv(*r.right, indent + 1);
        }
    }, d.rule);
}

// Rectify (Hughes Def 10.10 / CUT_ELIM_DESIGN §6): α-rename EVERY eigenvariable
// to a globally-distinct fresh index (above all fixed vars; identity on free
// vars). This establishes the variable condition as an INVARIANT: with all
// eigenvars unique across the whole derivation, the commutation cases (B4) that
// relocate/merge subderivations can never make one eigenvar denote two things
// (capture). Without it, an eigenvar reused in two independent subproofs
// collides once a cut is permuted to bring them into one context — the
// verifier then instantiates a quantifier body wrongly and a downstream axiom
// sees non-duals. (Duplication — B5-C — still re-rectifies its copy; see there.)
DerivPtr rectify_eigenvars(const Deriv& d, FormulaBuilder& b) {
    std::size_t fresh = 0;
    collect_max_fixed_deriv(d, fresh);     // 1 + max fixed var anywhere
    // Identity substitution (0:=fixed(0)); freshen_subst's job here is purely
    // the eigenvar renaming.
    return freshen_subst(d, Rename{}, /*a=*/0, Term::fixed(0), fresh, b);
}

// The B-stage worklist loop (rectify, B0, §5 reductions, then mult→additive).
// The optional `verify_step` is an extra per-step gate beyond the structural
// validate (see reduce.h); on a rejected reduction the last valid tree is kept.
util::Result<DerivPtr> reduce_loop(FormulaBuilder& builder, const Deriv& start,
                                   const VerifyStep& verify_step) {
    // Variable-condition invariant for the commutation cases (§6).
    DerivPtr rectified = rectify_eigenvars(start, builder);
    TRY_ASSIGN(current, additive_to_multiplicative(*rectified));

    // Step cap (B6 backstop): Gentzen cut-elim is non-elementary worst-case and
    // B5-C duplicates subderivations, so a large proof can blow up. Cap steps so
    // eliminate_cuts always terminates; on the cap it returns the current valid
    // (partially-reduced) tree. Override via LKR_CUT_ELIM_MAX_STEPS.
    std::size_t max_steps = 200000;
    if (const char* m = std::getenv("LKR_CUT_ELIM_MAX_STEPS")) {
        long v = std::atol(m);
        if (v > 0) max_steps = static_cast<std::size_t>(v);
    }
    const bool dbg = std::getenv("LKR_CUT_ELIM_DEBUG") != nullptr;

    // Monotonic fresh-eigenvar floor (B6): rather than re-scan the whole tree
    // each step, maintain `g_fresh` >= 1 + (max fixed/eigen var anywhere in
    // `current`) as an INVARIANT. Initialized once over the rectified tree; B5-C
    // draws its duplicate's rename from it; after each committed reduction it is
    // bumped past any fresh vars the reduction minted by scanning ONLY the
    // spliced subtree (the rest of `current` is unchanged, so its vars are still
    // below the old floor). Monotone non-decreasing ⇒ eigenvars stay globally
    // distinct across the whole run (Hughes Def 10.10), and gfloor is always a
    // safe (indeed conservative) floor for the duplication case.
    std::size_t g_fresh = 0;
    collect_max_fixed_deriv(*current, g_fresh);

    for (std::size_t step = 0; step < max_steps; ++step) {
        auto cand = find_topmost_max_deg_cut(*current);
        if (!cand) break;  // no cuts remain.

        DerivPtr* slot = slot_at_path(current, cand->path);
        if (!slot || !*slot)
            return MAKE_ERROR << "eliminate_cuts: lost cut node at path";
        const Deriv* cut_node = slot->get();
        const auto* cut = std::get_if<RCut>(&cut_node->rule);
        if (!cut)
            return MAKE_ERROR << "eliminate_cuts: slot_at_path returned non-cut";

        // dispatch_cut takes the cut node by const ref and only CLONES what it
        // keeps (never moves out of cut_node), so cut_node stays intact here.
        auto reduced = dispatch_cut(builder, *cut_node, *cut, g_fresh);
        if (!reduced.ok()) break;   // no §5 case applies — give up (residual).

        // Splice the reduction in place. Detach (not clone) the old cut subtree
        // into `saved` first so the fail-safe can restore it in O(1) — the rest
        // of the tree is never copied (the B6 win over substitute_at). `cut_node`
        // still points into `saved` (same pointee) and stays valid this step.
        DerivPtr saved = std::move(*slot);
        *slot = std::move(reduced).unwrap();
        // Fail-safe: every reduction must produce a structurally-valid tree and
        // (if verify_step is set) survive the full verifier. Reject a buggy
        // reduction — restore the last valid subtree, stop. Soundness preserved.
        if (!validate(*current).ok() ||
            (verify_step && !verify_step(*current))) {
            if (dbg) {
                std::fprintf(stderr, "[cut-elim] reduction REJECTED at step %zu "
                             "(case %s); offending cut (input to dispatch):\n",
                             step, g_last_case);
                dump_deriv(*cut_node, 1);
            }
            *slot = std::move(saved);   // restore — current is again last-valid.
            break;
        }
        // Committed: bump the floor past any fresh vars in the new subtree only.
        collect_max_fixed_deriv(**slot, g_fresh);
    }

    // Any residual (irreducible) cut is still multiplicative; convert back to
    // additive so the output emits to the additive LKR (Cut). No-op if cut-free.
    return multiplicative_to_additive(*current);
}

}  // namespace

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root,
                                      const LemmaProofs& lemmas,
                                      const VerifyStep& verify_step) {
    TRY(validate(root));
    // Stage A: inline proven-theorem lemma citations (§3). Run before B0/B so
    // the surrounding cuts become logical and reduce.
    TRY_ASSIGN(inlined, inline_lemmas(builder, root, lemmas));
    TRY(validate(*inlined));
    return reduce_loop(builder, *inlined, verify_step);
}

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root) {
    TRY(validate(root));
    return reduce_loop(builder, root, {});
}

}  // namespace logic::proof::translate::lkr_cut_elim
