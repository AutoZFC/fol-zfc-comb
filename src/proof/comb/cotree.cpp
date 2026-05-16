#include "src/proof/comb/cotree.h"

#include <algorithm>
#include <cstddef>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace logic::proof::comb {

// =====================================================================
// Naive O(n³) cograph recognizer + cotree builder.
//
// Theorem (Lerchs 1971): a graph G on ≥2 vertices is a cograph iff G is
// disconnected (+ / NodeKind::JOIN) or its complement Ḡ is disconnected
// (× / NodeKind::UNION); each (co-)component is itself a cograph.
//
// Per recursion: O(n²) to compute (co-)components by BFS, O(n) recursion
// depth in the worst case — O(n³) total.
//
// Naming: cotree.h's enum uses an internal convention,
//   NodeKind::JOIN  ≡ disjoint union (+ in Hughes' notation)
//   NodeKind::UNION ≡ graph join     (× in Hughes' notation)
// The header comments are the source of truth.
// =====================================================================

namespace {

using Adjacency = std::vector<std::unordered_set<size_t>>;

Adjacency build_adjacency(
    size_t                                        n,
    std::vector<std::pair<size_t, size_t>> const& edges)
{
    Adjacency adj(n);
    for (auto const& e : edges) {
        if (e.first == e.second) continue;
        adj[e.first].insert(e.second);
        adj[e.second].insert(e.first);
    }
    return adj;
}

// Connected components of the subgraph induced by `vs`. If `complement`
// is true, components are taken over Ḡ[vs] (u ~ v iff (u,v) ∉ adj and
// u ≠ v).
//
// `vs` is expected sorted ascending. Each returned component is sorted,
// and components are listed in order of their smallest vertex, so the
// cotree's child ordering is deterministic.
std::vector<std::vector<size_t>> components(
    std::vector<size_t> const& vs,
    Adjacency const&           adj,
    bool                       complement)
{
    std::unordered_map<size_t, bool> visited;
    visited.reserve(vs.size());
    for (size_t v : vs) visited.emplace(v, false);

    std::vector<std::vector<size_t>> out;
    for (size_t start : vs) {
        if (visited[start]) continue;
        std::vector<size_t> comp;
        std::vector<size_t> stack = {start};
        visited[start]            = true;
        while (!stack.empty()) {
            size_t u = stack.back();
            stack.pop_back();
            comp.push_back(u);
            for (size_t w : vs) {
                if (w == u || visited[w]) continue;
                bool a         = adj[u].count(w) != 0;
                bool effective = complement ? !a : a;
                if (effective) {
                    visited[w] = true;
                    stack.push_back(w);
                }
            }
        }
        std::sort(comp.begin(), comp.end());
        out.push_back(std::move(comp));
    }
    return out;
}

struct CotreeData {
    std::vector<Cotree::Node> nodes;
    std::vector<size_t>       leaf_of_vertex;
    std::vector<size_t>       parent_of;
    bool                      is_cograph = true;
};

// Recursive builder. Pre-allocates the current node *before* recursing,
// so the root naturally lands at index 0.
size_t build_subtree(
    std::vector<size_t> const& vs,
    Adjacency const&           adj,
    CotreeData&                data)
{
    size_t my_id = data.nodes.size();
    data.nodes.push_back({});
    data.parent_of.push_back(my_id);  // self-parent; caller overwrites if non-root.

    if (vs.size() == 1) {
        Cotree::Node& n            = data.nodes[my_id];
        n.kind                     = Cotree::NodeKind::LEAF;
        n.vertex                   = vs[0];
        data.leaf_of_vertex[vs[0]] = my_id;
        return my_id;
    }

    auto comps = components(vs, adj, /*complement=*/false);
    if (comps.size() > 1) {
        std::vector<size_t> child_ids;
        child_ids.reserve(comps.size());
        for (auto const& c : comps) {
            size_t cid = build_subtree(c, adj, data);
            if (!data.is_cograph) return 0;
            data.parent_of[cid] = my_id;
            child_ids.push_back(cid);
        }
        data.nodes[my_id].kind     = Cotree::NodeKind::JOIN;
        data.nodes[my_id].children = std::move(child_ids);
        return my_id;
    }

    auto co_comps = components(vs, adj, /*complement=*/true);
    if (co_comps.size() > 1) {
        std::vector<size_t> child_ids;
        child_ids.reserve(co_comps.size());
        for (auto const& c : co_comps) {
            size_t cid = build_subtree(c, adj, data);
            if (!data.is_cograph) return 0;
            data.parent_of[cid] = my_id;
            child_ids.push_back(cid);
        }
        data.nodes[my_id].kind     = Cotree::NodeKind::UNION;
        data.nodes[my_id].children = std::move(child_ids);
        return my_id;
    }

    // Both G[vs] and Ḡ[vs] connected ⇒ induced P_4 ⇒ not a cograph.
    data.is_cograph = false;
    return 0;
}

}  // namespace

Cotree::Cotree(
    size_t                                        num_vertex,
    std::vector<std::pair<size_t, size_t>> const& cograph_edges)
    : num_input_vertex_{num_vertex}
{
    if (num_vertex == 0) return;

    Adjacency adj = build_adjacency(num_vertex, cograph_edges);

    CotreeData data;
    data.leaf_of_vertex.assign(num_vertex, 0);

    std::vector<size_t> all_vertices(num_vertex);
    for (size_t i = 0; i < num_vertex; ++i) all_vertices[i] = i;

    build_subtree(all_vertices, adj, data);

    if (!data.is_cograph) return;

    nodes          = std::move(data.nodes);
    leaf_of_vertex = std::move(data.leaf_of_vertex);
    parent_of      = std::move(data.parent_of);
}

}  // namespace logic::proof::comb
