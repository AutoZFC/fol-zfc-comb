// src/proof/comb/cotree.h
#pragma once

#include "src/util/error.h"

#include <cstddef>
#include <utility>
#include <vector>

namespace logic::proof::comb {

// Cotree = modular decomposition tree of a cograph (paper §3).
// Every internal node is labelled + (disjoint union) or × (join);
// every leaf corresponds to one vertex of the source cograph.
//
// Storage: a flat std::vector<Node> indexed by node-id (size_t). Node 0
// is the root. This avoids per-node heap allocation and makes parent/
// child pointers compact.
class Cotree {
public:
    enum class NodeKind {
        LEAF,
        JOIN,    // disjoint union — children are unrelated in the cograph
        UNION,   // join — every leaf in one child is adjacent to every leaf in another
    };

    struct Node {
        NodeKind            kind{NodeKind::LEAF};
        std::vector<size_t> children{};   // node-ids; empty for Leaf
        size_t              vertex{0};    // valid only when kind == Leaf
    };
    Cotree(size_t num_vertex, std::vector<std::pair<size_t, size_t>> const & cograph_edges);

    // True iff construction produced a valid cotree. False means the
    // input was not a cograph (an induced P_4 was detected) — except when
    // num_vertex == 0, in which case the cotree is trivially-empty but
    // still "ok".
    bool ok() const { return nodes.size() > 0 || num_input_vertex_ == 0; }

    size_t num_vertex() const { return leaf_of_vertex.size(); }
    size_t num_nodes()  const { return nodes.size(); }
    size_t root() const { return 0; }

    // Per-node read API. node_id must be < num_nodes().
    const Node& node(size_t node_id) const { return nodes[node_id]; }

    // Parent of node_id. The root is its own parent.
    size_t parent(size_t node_id) const { return parent_of[node_id]; }

    // The leaf node-id for vertex v (v must be < num_vertex()).
    size_t leaf_of(size_t v) const { return leaf_of_vertex[v]; }

    // Call `visit(vertex)` for every leaf-vertex index under the
    // subtree rooted at node_id, in cotree pre-order. No allocation;
    // recursion depth is bounded by cotree depth.
    template <typename Visit>
    void for_each_leaf_in_subtree(size_t node_id, Visit&& visit) const {
        const Node& n = nodes[node_id];
        if (n.kind == NodeKind::LEAF) {
            visit(n.vertex);
            return;
        }
        for (size_t child_id : n.children) {
            for_each_leaf_in_subtree(child_id, visit);
        }
    }

private:
    std::vector<Node>   nodes{};            // node 0 is root
    std::vector<size_t> leaf_of_vertex{};   // vertex index → leaf node-id
    std::vector<size_t> parent_of{};        // node-id → parent node-id; root maps to itself
    size_t              num_input_vertex_{0};  // num_vertex the ctor was called with
};

  }  // namespace logic::proof::comb

