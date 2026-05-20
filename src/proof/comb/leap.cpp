// Leap graph + bimatching-freeness (Phase 2C). See leap.h for the math.
//
// PRECONDITION: the input CombProof is description-free — atom args
// are Fixed (binder refs) or Gen (description-internal, opaque, not
// fonet binder refs). Descriptions are eliminated by the translator
// before reaching the comb layer (CombVerifier::verify enforces this
// at the boundary).

#include "src/proof/comb/leap.h"
#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/util/error.h"

#include <cwchar>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace logic::proof::comb {

namespace {

// Union-find over existential variables. Each class root may carry an
// `anchor`: the rigid term the class is pinned to. With no
// descriptions, an anchor can only be Fixed(v) where v is universal.
struct UnionFind {
    std::unordered_map<var_index, var_index> parent;
    std::unordered_map<var_index, Term>      anchor;   // keyed by ROOT only

    void make(var_index x) { if (!parent.count(x)) parent[x] = x; }

    var_index find(var_index x) {
        var_index r = x;
        while (parent[r] != r) r = parent[r];
        while (parent[x] != r) { var_index n = parent[x]; parent[x] = r; x = n; }
        return r;
    }

    // Merge two existential-var classes. Returns false on anchor conflict.
    bool unite(var_index a, var_index b) {
        a = find(a);
        b = find(b);
        if (a == b) return true;

        // Snapshot anchors before mutating (operator[] insertion can
        // rehash, invalidating iterators we'd otherwise want to use later).
        auto a_itr  = anchor.find(a);
        auto b_itr  = anchor.find(b);
        bool has_a  = a_itr != anchor.end();
        bool has_b  = b_itr != anchor.end();
        if (has_a && has_b && a_itr->second != b_itr->second) return false;

        Term saved;
        if (has_a) saved = a_itr->second;

        parent[a] = b;
        if (has_a && !has_b) anchor[b] = saved;
        if (has_a)           anchor.erase(a);
        return true;
    }

    // Pin an existential-var class to a rigid term. Returns false on
    // conflict with an existing anchor.
    bool set_anchor(var_index x, const Term& rigid) {
        var_index r = find(x);
        auto      it = anchor.find(r);
        if (it != anchor.end() && it->second != rigid) return false;
        anchor[r] = rigid;
        return true;
    }
};

}  // namespace

util::Result<std::unordered_map<var_index, Term>>
most_general_dualizer(const CombProof& proof) {
    const Fonet& N = proof.source;

    // Existential variable set (the unknowns of the unification problem).
    std::unordered_set<var_index> existential;
    for (size_t v = 0; v < N.num_vertex; ++v) {
        const VertexLabel& lbl = proof.source_label(v);
        if (lbl.kind == VertexKind::Binder && lbl.is_existential)
            existential.insert(lbl.var);
    }

    // A term is an "unknown" iff it is an existential binder variable.
    // Everything else (universal var, Gen) is rigid.
    auto is_unknown = [&](const Term& t) {
        return t.is_fixed() && existential.count(t.as_variable()) > 0;
    };

    // Union-find over existential vars, fed by the link equations. No
    // function symbols ⇒ unification is direct: variable identity for
    // rigid/rigid; union-find for unknowns; anchor for mixed.
    UnionFind uf;
    for (var_index x : existential) uf.make(x);

    // PRECONDITION: t, u are Fixed. The Fograph builder rewrites Gen →
    // Fixed in all atom args, and descriptions are rejected at the
    // verifier boundary, so atom args here are always Fixed.
    auto unify = [&](const Term& t, const Term& u) -> bool {
        int e = (is_unknown(t) << 1) | is_unknown(u);
        switch (e) {
            case 0b11: return uf.unite(t.as_variable(), u.as_variable());
            case 0b10: return uf.set_anchor(t.as_variable(), u);
            case 0b01: return uf.set_anchor(u.as_variable(), t);
            case 0b00: return t.as_variable() == u.as_variable();
        }
        return false;
    };

    for (const Edge& link : N.links) {
        const VertexLabel& a1 = proof.source_label(link.first);
        const VertexLabel& a2 = proof.source_label(link.second);
        // 2A.2 already guaranteed same predicate ⇒ matching arity.
        for (size_t i = 0; i < a1.args.size(); ++i) {
            if (!unify(a1.args[i], a2.args[i])) {
                return MAKE_ERROR << "most_general_dualizer: link arguments do "
                                     "not unify — no dualizer exists";
            }
        }
    }

    // δ: each existential's class anchor (absent ⇒ unconstrained/stem).
    std::unordered_map<var_index, Term> delta;
    for (var_index x : existential) {
        auto it = uf.anchor.find(uf.find(x));
        if (it != uf.anchor.end()) delta[x] = it->second;
    }
    return delta;
}

util::Result<Edges> build_leap_graph(const CombProof& proof) {
    const Fonet& N = proof.source;

    // Binder var → vertex id, for turning dependency vars into edges.
    std::unordered_map<var_index, size_t> binder_vertex;
    for (size_t v = 0; v < N.num_vertex; ++v) {
        const VertexLabel& lbl = proof.source_label(v);
        if (lbl.kind == VertexKind::Binder) binder_vertex[lbl.var] = v;
    }

    // L_N = links ∪ dependencies. Dependencies come from the MGU
    // (Lemma 10.12 / 10.13): {x, y} is a dependency iff δ(x) contains the
    // universal y. With no function symbols, δ(x) is a single rigid var.
    TRY_ASSIGN(delta, most_general_dualizer(proof));

    Edges leaps;
    for (const Edge& link : N.links) leaps.push_back(link);
    for (const auto& [x, rigid] : delta) {
        if (!rigid.is_fixed()) continue;               // defensively skip non-Fixed
        leaps.push_back({binder_vertex[x], binder_vertex[rigid.as_variable()]});
    }
    return leaps;
}

// verify_no_bimatching -- paper Sec. 14.2, driven by Lemmas 10.16-10.22.
//
// =====================================================================
// What we're checking
// =====================================================================
//
// N is the linked fograph stored in proof.source. L_N is the leap graph
// just built by build_leap_graph (links union dependencies). We must
// confirm that N admits NO induced bimatching (paper Def. 5.3):
//
//   W subset of V_N induces a bimatching in N iff
//     W induces a matching in the cograph (V_N, E_N)  AND
//     W induces a matching in the leap   graph (V_N, L_N).
//
// Direct subset enumeration is exponential. We use the constructive
// characterization from paper Sec. 10.1:
//
//   Lemma 10.22.  Every fonet is constructible from axioms by fusion
//                 and quantification.
//
// So we verify "N is a fonet" by attempting the decomposition. If it
// succeeds all the way down to axioms, N is a fonet. If at any step
// the required structural decomposition is missing, N admits an
// induced bimatching -- reject.
//
// Polynomial-time guarantee: Theorem 14.3, with Lemma 14.2 showing
// each decomposition step is polynomial.
//
// =====================================================================
// Recursive driver  is_fonet(W)
// =====================================================================
//
// W subset of V_N is the current sub-fonet. G[W] is the cograph
// restricted to W; L_N[W] is the leap graph restricted to W. Exactly
// one of three cases applies at each level:
//
// --- Case A: base case (Lemma 10.17) ---------------------------------
//
//   If E(G[W]) is empty:
//     Require every v in W to be an atom (literal). If so, N[W] is a
//     union of literal-axioms; recursion bottoms out OK. Otherwise,
//     error -- a binder in a no-edge subgraph would be a universal in
//     no edge, but Case B should have stripped it first.
//
// --- Case B: strip a universal binder (Lemma 10.16) ------------------
//
//   If there exists a binder vertex *x in W with no incident cograph
//   edge in G[W]:
//     *x must be universal (an existential binder is x-joined to its
//     scope and so always has a cograph edge). By Lemma 10.16, N[W] is
//     the universal quantification of N[W \ {*x}]. Recurse on W \ {*x}.
//
// --- Case C: Omega-bridge decomposition (Lemma 10.21) ----------------
//
//   N[W] is non-universal with at least one edge. Decompose the
//   underlying cograph per Lemma 10.21:
//
//     G[W] = (G_1 x G_2) + (G_3 x G_4) + ... + (G_{n-1} x G_n) + L
//
//   where each G_i is a cograph, L is a (possibly empty) union of lone
//   literal vertices, and n >= 1.
//
//   Read this off the cotree of G[W]:
//     - root is + (JOIN, G[W] disconnected):
//         - leaf children that are literals go into L,
//         - each x (UNION) child is a x-component, binary-split as
//           G_{2i-1} x G_{2i} (first sub-child vs the rest);
//     - root is x (UNION, G[W] connected):
//         - the whole graph is a single G_1 x G_2, L is empty.
//
//   Build the auxiliary graph Omega (Lemma 10.21 proof, paragraph 1):
//
//     V(Omega)              = {G_1, ..., G_n}
//     {G_i, G_j} in E(Omega) iff there exist v in V(G_i), w in V(G_j)
//                                with {v,w} in E_N[W] union L_N[W].
//
//   NOTE: both cograph edges AND leaps contribute to Omega-adjacency.
//   This is the only place L_N enters the structural check.
//
//   Z = {G_1 G_2, G_3 G_4, ..., G_{n-1} G_n} is a 1-factor of Omega
//   automatically (each G_{2i-1} x G_{2i} forces a cograph edge between
//   them, hence an Omega-edge).
//
//   Paper claim (Lemma 10.21 proof, paragraph 2):
//
//     If N is a fonet, then Z is the UNIQUE 1-factor of Omega.
//
//   Contrapositive: a second 1-factor Z' would, via Z' \ Z, witness
//   leaps whose union induces a bimatching in N.
//
//   By Kotzig's theorem (paper refs [Kot59, LP86]): Omega has a unique
//   1-factor iff some edge of Z is a BRIDGE of Omega (removing it
//   disconnects its component). So the per-level structural test is:
//
//     find e in Z such that e is a bridge of Omega
//       ==> success at this level
//     no such e
//       ==> induced bimatching exists  ==>  reject.
//
//   Split at the bridge: let e = {G_m, G_{m+1}}. Removing e partitions
//   V(Omega) into X (component of G_m) and Y (component of G_{m+1}).
//   Partition the lone literals by where their link mate lies:
//
//     L_X = { l in L : mate(l) in union_{i in X} V(G_i) }
//     L_Y = L \ L_X
//
//   Then
//     K_1 = L_X + sum_{i in X, i != m}   G_i
//     K_2 = L_Y + sum_{j in Y, j != m+1} G_j
//
//   By construction:  G[W] = K_1 + (G_m x G_{m+1}) + K_2.
//
//   Sub-cases (Lemma 10.21 proof, paragraph 4):
//
//     C.1  Both G_m and G_{m+1} contain a literal.
//          By Lemma 10.18 (H_1=G_m, H_2=G_{m+1}), N[W] is a FUSION of
//            N[V(K_1) union V(G_m)]   and   N[V(G_{m+1}) union V(K_2)].
//          Recurse on each; both must succeed.
//
//     C.2  One of G_m, G_{m+1} contains no literal -- WLOG G_m = {*x}.
//          Then G_{m+1} contains a literal (else G_m x G_{m+1} would
//          not be a fograph). The variable *x is necessarily
//          existential (universals were stripped in Case B).
//          Lemma 10.19 + 10.20: the bridge condition forces *x to be
//          in no leap of N[W], so N[W] is an EXISTENTIAL QUANTIFICATION
//          of N[W \ {*x}]. Recurse on W \ {*x}.
//
// =====================================================================
// Termination + complexity (Theorem 14.3)
// =====================================================================
//
// Termination:  each recursive call strictly reduces |W| (B and C.2
// remove a vertex) or splits W into two strict subsets (C.1). Depth
// O(|V_N|).
//
// Per-level cost (Lemma 14.2's argument):
//   - cograph restriction + cotree (re)build: O(|V_N|^2) with our
//     naive recognizer (Hughes cites [CLS81] for the linear-time
//     alternative; we don't need it for correctness).
//   - build Omega: one pass over E_N union L_N + O(|V_N|) lookup.
//   - bridge in Z: |Z| = n/2 connectivity checks, each O(|E(Omega)|).
//   - split / partition: linear in |W|.
//
// Total: polynomial in |V_N| + |E_N| + |L_N|. Combined with Phase
// 2C.1 (build_leap_graph, Lemma 14.1), this discharges Theorem 14.3
// for our verifier.
//
// =====================================================================
// TODO -- implementation plan
// =====================================================================
//
// Data:
using Mask = std::vector<bool>;            // mask[v] = "v is in W"
//   // re-indexing maps maintained per recursive level (for building
//   // restricted cotrees on 0..|W|-1 indices)
//
// Helpers (write once):
//   TODO (you): Edges restrict_edges(const Edges&, const Mask&);
//   TODO (you): Cotree restrict_cotree(const Mask&, const Edges& cograph_full);
//                  // also returns the re-index map
//   TODO (you): build mate[u] = v for {u,v} in proof.source.links;

Edges restrict_edges(const Edges & edges, const Mask & mask) {
    Edges res;
    for (const Edge & edge : edges) {
        if (mask[edge.first] && mask[edge.second]) {
            res.push_back(edge);
        }
    }
    return res;
}

Cotree restrict_cotree(const Mask & mask, const Edges & cograph_full) {
    return Cotree(mask.size(), restrict_edges(cograph_full, mask));
}



// Driver:
//   TODO (you): is_fonet(Mask W) returning ResultStatus.
//     -- Case A test: E(G[W]) empty + every v in W is Atom.
//     -- Case B test: iterate W; find a binder with deg_{G[W]}(v) = 0;
//                     if found, recurse on W \ {v}.
//     -- Case C: invoke the decomposition pipeline below.
//
// Case C pipeline:
//   TODO (you): cotree_to_parts(cotree, mask) -> (parts, L)
//                where parts is vector<vector<size_t>> of vertex ids
//                (each G_i's vertex set) and L is vector<size_t> of
//                lone literal vertex ids.
//   TODO (you): build_omega(parts, E_N[W], L_N[W])
//                -> adjacency over part indices 0..n-1.
//   TODO (you): bridge_in_Z(omega_adj) -> optional<edge>
//                iterate Z = {(0,1), (2,3), ...}; for each, DFS-test if
//                bridge; return first found or nullopt.
//   TODO (you): split_at_bridge((m, m+1), omega_adj, parts, L, mate)
//                -> (W_left, W_right, sub_case)
//                where sub_case is FUSION or EXISTS_QUANT and W_right
//                is empty in the EXISTS_QUANT case (we recurse on
//                W ∖ {the lone binder} -- the whole W minus that one
//                vertex, not split).

// Wire-in (orchestration):
//   TODO (you): replace the TODO comment in verify_fonet that says
//               "2C (no induced bimatching in the leap graph)" with:
//                 TRY_ASSIGN(leaps, build_leap_graph(proof));
//                 TRY(verify_no_bimatching(proof, cotree, leaps));
//               Note: cotree is the one already built for 2A.3 -- thread
//               it through (currently it's a local in verify_fonet).
//
// Tests to write alongside (pinning each piece of the math):
//   TODO (you): single-literal fonet           -- Case A bottoming out
//   TODO (you): forall x. (P(x) and not P(x)) -- Case B strip
//   TODO (you): exists x. (P(x) and not P(x)) -- Case C.2 quantification
//   TODO (you): (A and not A) or (B and not B) -- Case C.1 fusion
//   TODO (you): hand-built 2K2 + crossing leaps -- bimatching, must reject
//   TODO (you): combined small ZFC-style fonet (post-translator) -- pass
//
// Watch out for:
//   - vertex re-indexing bugs: keep mask <-> sub-index translation
//     isolated to the restrict_cotree helper.
//   - empty Y after the bridge (singleton component on one side).
//   - n must be even for Z to be a 1-factor; odd n implies upstream bug.
//   - bridge test should not mutate omega_adj across iterations; either
//     copy-and-mutate or skip-an-edge-during-traversal.
util::ResultStatus verify_no_bimatching(const CombProof& proof,
                                        const Cotree&    /*cotree*/,
                                        const Edges&     leap_edges) {
    // Pre-compute link mate map. mate[v] = w iff {v,w} is a link;
    // SIZE_MAX if v is not in any link (binders, or the truth literal *1).
    std::vector<size_t> mate(proof.source.num_vertex, SIZE_MAX);
    for (const Edge& link : proof.source.links) {
        mate[link.first]  = link.second;
        mate[link.second] = link.first;
    }

    // Recursive driver -- declared as std::function so the lambda can
    // refer to itself for the recursive calls in Cases B and C.
    std::function<util::ResultStatus(const Mask&)> is_fonet =
        [&](const Mask& W) -> util::ResultStatus {
            Edges E_W = restrict_edges(proof.source.cograph_edges, W);

            // Case B (Lemma 10.16) -- run first. A binder *x in W with
            // no incident cograph edge in G[W] is necessarily universal
            // (existentials are x-joined to their scope, so they always
            // have an edge). N[W] is the universal quantification of
            // N[W \ {*x}]; strip it and recurse.
            for (size_t i = 0; i < W.size(); ++i) {
                if (!W[i]) continue;
                const VertexLabel& lbl = proof.source_label(i);
                if (lbl.kind != VertexKind::Binder) continue;
                bool has_edge = false;
                for (const Edge& e : E_W) {
                    if (e.first == i || e.second == i) { has_edge = true; break; }
                }
                if (!has_edge) {
                    // Defensive: Lemma 10.16's "necessarily universal".
                    // 2A.3-1 already enforces the stored label matches
                    // the cograph structure, but we check here too so
                    // an out-of-band call to verify_no_bimatching does
                    // not bypass the constraint.
                    if (lbl.is_existential) {
                        return MAKE_ERROR << "is_fonet: Case B found binder "
                                          << i << " with no incident edge but "
                                          "is_existential=true (Hughes Lemma "
                                          "10.16 requires a universal binder; "
                                          "existentials must have ×-edges to "
                                          "their non-empty scope)";
                    }
                    Mask W2 = W;
                    W2[i] = false;
                    return is_fonet(W2);
                }
            }

            // Case A (Lemma 10.17) -- base. After Case B, any remaining
            // binder has an incident edge in G[W]; so if E_W is empty,
            // no binders remain, and W is a union of literals (Atom or
            // One -- the truth literal *1). Recursion bottoms out OK.
            if (E_W.empty()) {
                // Defensive: Lemma 10.17's "no edge AND no binder".
                for (size_t i = 0; i < W.size(); ++i) {
                    if (!W[i]) continue;
                    auto k = proof.source_label(i).kind;
                    if (k == VertexKind::Atom || k == VertexKind::One) continue;
                    return MAKE_ERROR << "is_fonet: Case A reached empty-edge "
                                         "subgraph with non-literal vertex "
                                      << i << " still in W (Hughes Lemma "
                                      "10.17 requires no binder); Case B "
                                      "should have stripped it";
                }
                return util::Ok();
            }

            // Case C (Lemma 10.21): Omega-bridge decomposition.
            //
            // We perform DFS over binarization choices. Each multi-child
            // × cotree-node is a choice point: which one of its in-W
            // children becomes parts[2k] (rest becomes parts[2k+1]).
            // The combination of all choices fully determines parts/L
            // and hence Ω. We test the bridge / recurse on each
            // combination; success on any combination decomposes the
            // sub-fonet.
            //
            // Hughes Lemma 10.21 only proves existence of SOME valid
            // representation, so a greedy choice can reject paper-valid
            // fonets. Backtracking closes that completeness gap.
            Cotree C = restrict_cotree(W, proof.source.cograph_edges);
            if (!C.ok()) {
                return MAKE_ERROR << "is_fonet: source restricted to W is not "
                                     "a cograph (induced P_4)";
            }

            auto collect_in_W_leaves = [&](size_t node_id) {
                std::vector<size_t> out;
                C.for_each_leaf_in_subtree(node_id, [&](size_t v) {
                    if (W[v]) out.push_back(v);
                });
                return out;
            };

            auto child_has_literal = [&](const std::vector<size_t>& vs) {
                for (size_t v : vs) {
                    auto k = proof.source_label(v).kind;
                    if (k == VertexKind::Atom || k == VertexKind::One) return true;
                }
                return false;
            };

            // --- Gather direct-L vertices + per-×-node children -----
            std::vector<size_t> direct_L;
            // Per × cotree-node: list of in-W child leaf-sets (each is
            // one G_i candidate). If size==1 we fold into L (literal
            // check). If size>=2 it's a choice point with that many
            // candidates.
            std::vector<std::vector<std::vector<size_t>>> union_children;

            const Cotree::Node& root = C.node(C.root());
            auto gather_one_union = [&](size_t union_node_id) -> util::ResultStatus {
                const Cotree::Node& un = C.node(union_node_id);
                std::vector<std::vector<size_t>> child_leaves;
                for (size_t cid : un.children) {
                    auto cl = collect_in_W_leaves(cid);
                    if (!cl.empty()) child_leaves.push_back(std::move(cl));
                }
                if (child_leaves.empty()) return util::Ok();
                if (child_leaves.size() == 1) {
                    // Degenerate × node: fold to L iff all literals.
                    for (size_t v : child_leaves[0]) {
                        VertexKind k = proof.source_label(v).kind;
                        if (k != VertexKind::Atom && k != VertexKind::One) {
                            return MAKE_ERROR << "is_fonet: degenerate × cotree-node "
                                                 "with a single in-W child contains a "
                                                 "non-literal (vertex " << v << "); "
                                                 "Hughes Lemma 10.21 requires L to be "
                                                 "a union of literals only";
                        }
                    }
                    for (size_t v : child_leaves[0]) direct_L.push_back(v);
                    return util::Ok();
                }
                union_children.push_back(std::move(child_leaves));
                return util::Ok();
            };

            if (root.kind == Cotree::NodeKind::JOIN) {
                for (size_t cid : root.children) {
                    const Cotree::Node& child = C.node(cid);
                    if (child.kind == Cotree::NodeKind::LEAF) {
                        if (W[child.vertex]) direct_L.push_back(child.vertex);
                    } else if (child.kind == Cotree::NodeKind::UNION) {
                        TRY(gather_one_union(cid));
                    }
                }
            } else if (root.kind == Cotree::NodeKind::UNION) {
                TRY(gather_one_union(C.root()));
            } else {
                return MAKE_ERROR << "is_fonet: unexpected leaf root in Case C";
            }

            // No multi-child × nodes? Then n==0; nothing to decompose.
            // (E_W non-empty was asserted earlier; with no pairs there
            // must be an inconsistency upstream.)
            if (union_children.empty()) {
                return MAKE_ERROR << "is_fonet: Case C reached with E_W non-empty "
                                     "but no multi-child × cotree-node found "
                                     "(malformed cotree decomposition)";
            }

            // --- Compute per-×-node choice order (priority-sorted) ---
            //
            // For each × node, we try children in this priority order:
            //   1. Singleton existential binder leaf (direct C.2).
            //   2. A child with a literal where rest also has a literal
            //      (C.1 fusion).
            //   3. Anything else (residual fallback).
            // The priority is just a search-order heuristic; backtracking
            // ensures we'll try alternatives if the first choice fails.
            std::vector<std::vector<size_t>> choice_order(union_children.size());
            for (size_t un = 0; un < union_children.size(); ++un) {
                const auto& cl = union_children[un];
                std::vector<size_t> p1, p2, p3;
                for (size_t i = 0; i < cl.size(); ++i) {
                    bool is_singleton_existential =
                        cl[i].size() == 1 &&
                        proof.source_label(cl[i][0]).kind == VertexKind::Binder &&
                        proof.source_label(cl[i][0]).is_existential;
                    if (is_singleton_existential) { p1.push_back(i); continue; }
                    bool this_has_lit = child_has_literal(cl[i]);
                    bool rest_has_lit = false;
                    for (size_t k = 0; k < cl.size(); ++k) {
                        if (k == i) continue;
                        if (child_has_literal(cl[k])) { rest_has_lit = true; break; }
                    }
                    if (this_has_lit && rest_has_lit) {
                        p2.push_back(i);
                    } else {
                        p3.push_back(i);
                    }
                }
                auto& ord = choice_order[un];
                ord.insert(ord.end(), p1.begin(), p1.end());
                ord.insert(ord.end(), p2.begin(), p2.end());
                ord.insert(ord.end(), p3.begin(), p3.end());
            }

            // --- DFS over choice tuples -----------------------------
            //
            // try_with_choices builds parts/L from a complete choice
            // tuple and runs the bridge test + recursion. Returns Ok
            // on first success; aggregates last error otherwise.
            std::vector<size_t>              parts_n;  // accumulated parts.size()
            std::vector<std::vector<size_t>> parts;
            util::ResultStatus               last_err = MAKE_ERROR
                << "is_fonet: no valid binarization found (Case C)";

            std::function<util::ResultStatus()> try_decomposition;
            std::function<util::ResultStatus(size_t)> dfs;

            dfs = [&](size_t un_idx) -> util::ResultStatus {
                if (un_idx == union_children.size()) {
                    auto r = try_decomposition();
                    if (!r.is_error()) return r;
                    last_err = std::move(r);
                    return last_err;  // signal failure; outer DFS keeps trying
                }
                const auto& cl  = union_children[un_idx];
                const auto& ord = choice_order[un_idx];
                for (size_t pick : ord) {
                    // parts[2*un_idx]   = cl[pick]
                    // parts[2*un_idx+1] = rest
                    std::vector<size_t> rest;
                    for (size_t k = 0; k < cl.size(); ++k) {
                        if (k == pick) continue;
                        for (size_t v : cl[k]) rest.push_back(v);
                    }
                    parts.push_back(cl[pick]);
                    parts.push_back(std::move(rest));
                    auto r = dfs(un_idx + 1);
                    if (!r.is_error()) return r;
                    parts.pop_back();
                    parts.pop_back();
                }
                return last_err;
            };

            // try_decomposition is the per-tuple bridge-test + split
            // + recurse, factored out so dfs can call it once per leaf.
            try_decomposition = [&]() -> util::ResultStatus {
                const std::vector<size_t>& L = direct_L;
                const size_t n = parts.size();
                if (n == 0 || n % 2 != 0) {
                    return MAKE_ERROR << "is_fonet: malformed parts decomposition "
                                         "(n = " << n << ")";
                }

                // --- Build Omega ------------------------------------
                std::vector<int> part_of(proof.source.num_vertex, -1);
                for (size_t p = 0; p < n; ++p) {
                    for (size_t v : parts[p]) part_of[v] = static_cast<int>(p);
                }
                std::vector<std::unordered_set<int>> omega_adj(n);
                auto add_omega_edge = [&](size_t u, size_t v) {
                    if (!W[u] || !W[v]) return;
                    int pu = part_of[u];
                    int pv = part_of[v];
                    if (pu == -1 || pv == -1 || pu == pv) return;
                    omega_adj[pu].insert(pv);
                    omega_adj[pv].insert(pu);
                };
                for (const Edge& e : E_W)        add_omega_edge(e.first, e.second);
                for (const Edge& e : leap_edges) add_omega_edge(e.first, e.second);

                // --- Find a bridge in Z -----------------------------
                auto is_bridge = [&](int a, int b) {
                    std::vector<bool> visited(n, false);
                    std::vector<int>  stack{a};
                    visited[a] = true;
                    while (!stack.empty()) {
                        int u = stack.back(); stack.pop_back();
                        for (int v : omega_adj[u]) {
                            if ((u == a && v == b) || (u == b && v == a)) continue;
                            if (visited[v]) continue;
                            visited[v] = true;
                            stack.push_back(v);
                        }
                    }
                    return !visited[b];
                };

                int m = -1;
                for (size_t i = 0; i + 1 < n; i += 2) {
                    if (is_bridge(static_cast<int>(i), static_cast<int>(i + 1))) {
                        m = static_cast<int>(i);
                        break;
                    }
                }
                if (m < 0) {
                    return MAKE_ERROR << "is_fonet: no bridge in Z -- this "
                                         "binarization fails (induced "
                                         "bimatching, or wrong binarization "
                                         "choice — DFS will try alternatives)";
                }

                // --- Split at the bridge ---------------------------
                std::vector<bool> in_X(n, false);
                {
                    std::vector<int> stack{m};
                    in_X[m] = true;
                    while (!stack.empty()) {
                        int u = stack.back(); stack.pop_back();
                        for (int v : omega_adj[u]) {
                            if ((u == m && v == m + 1) || (u == m + 1 && v == m)) continue;
                            if (in_X[v]) continue;
                            in_X[v] = true;
                            stack.push_back(v);
                        }
                    }
                }

                auto contains_literal = [&](const std::vector<size_t>& part) {
                    for (size_t v : part) {
                        auto k = proof.source_label(v).kind;
                        if (k == VertexKind::Atom || k == VertexKind::One) return true;
                    }
                    return false;
                };
                const bool gm_lit   = contains_literal(parts[m]);
                const bool gm1_lit  = contains_literal(parts[m + 1]);

                // --- Sub-case C.2 ----------------------------------
                if (!gm_lit || !gm1_lit) {
                    size_t lone = (!gm_lit) ? static_cast<size_t>(m)
                                            : static_cast<size_t>(m + 1);
                    if (parts[lone].size() != 1) {
                        return MAKE_ERROR << "is_fonet: C.2 expected a singleton "
                                             "binder, got part of size "
                                          << parts[lone].size();
                    }
                    size_t binder_v = parts[lone][0];
                    const VertexLabel& binder_lbl = proof.source_label(binder_v);
                    if (binder_lbl.kind != VertexKind::Binder) {
                        return MAKE_ERROR << "is_fonet: C.2 expected a binder";
                    }
                    if (!binder_lbl.is_existential) {
                        return MAKE_ERROR << "is_fonet: C.2 found a universal "
                                             "binder on the no-literal side "
                                             "(Hughes Lemma 10.20 requires an "
                                             "existential); Case B should have "
                                             "stripped it";
                    }
                    Mask W2 = W;
                    W2[binder_v] = false;
                    return is_fonet(W2);
                }

                // --- Sub-case C.1 ----------------------------------
                Mask W_left(W.size(), false);
                Mask W_right(W.size(), false);
                for (size_t p = 0; p < n; ++p) {
                    Mask& target = in_X[p] ? W_left : W_right;
                    for (size_t v : parts[p]) target[v] = true;
                }
                for (size_t v : L) {
                    bool to_left;
                    if (mate[v] == SIZE_MAX) {
                        to_left = true;
                    } else {
                        int mate_part = part_of[mate[v]];
                        to_left = (mate_part == -1) ? true : in_X[mate_part];
                    }
                    (to_left ? W_left : W_right)[v] = true;
                }

                auto r_left = is_fonet(W_left);
                if (r_left.is_error()) return r_left;
                return is_fonet(W_right);
            };  // end try_decomposition

            return dfs(0);
        };  // end is_fonet

    Mask seed(proof.source.num_vertex, true);
    return is_fonet(seed);
}

}  // namespace logic::proof::comb
