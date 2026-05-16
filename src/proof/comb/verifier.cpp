#include "src/proof/comb/verifier.h"

#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/cotree.h"
#include "src/proof/comb/leap.h"
#include "src/util/error.h"

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

namespace logic::proof::comb {

namespace {

// Walk a formula looking for a Description term. We do not recurse
// into description bodies — finding one anywhere is enough to reject.
bool formula_has_description(FormulaHandle h);

bool term_or_descend_has_description(const Term& t) {
    return t.is_description();
}

bool formula_has_description(FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_predicate()) {
        for (const auto& arg : f.as_predicate().args()) {
            if (term_or_descend_has_description(arg)) return true;
        }
        return false;
    }
    if (f.is_compound()) {
        const auto& c = f.as_compound();
        if (c.left.valid()  && formula_has_description(c.left))  return true;
        if (c.right.valid() && formula_has_description(c.right)) return true;
        return false;
    }
    if (f.is_quantified()) {
        return formula_has_description(f.as_quantified().body);
    }
    return false;
}

// Boundary check: the comb proof system is description-free. The
// translator (see translate/ELIMINATE_DESCRIPTIONS.md) is responsible
// for running `eliminate_descriptions` before handing a formula to the
// comb verifier. This check enforces the invariant: scan the goal, any
// atom-label args, and any dualizer image terms for descriptions.
util::ResultStatus check_description_free(FormulaHandle goal_formula,
                                          const CombProof& cp) {
    if (formula_has_description(goal_formula)) {
        return MAKE_ERROR << "CombVerifier: goal formula contains a description "
                             "term; comb proof system is description-free, run "
                             "eliminate_descriptions in the translator first";
    }
    for (size_t i = 0; i < cp.target.labels.size(); ++i) {
        const auto& lbl = cp.target.labels[i];
        if (lbl.kind != VertexKind::Atom) continue;
        for (const auto& arg : lbl.args) {
            if (arg.is_description()) {
                return MAKE_ERROR << "CombVerifier: target label " << i
                                  << " contains a description term in its args";
            }
        }
    }
    for (const auto& [x, term] : cp.source.dualizer) {
        if (term.is_description()) {
            return MAKE_ERROR << "CombVerifier: dualizer(" << x
                              << ") image is a description";
        }
    }
    return util::Ok();
}

}  // namespace

util::ResultStatus CombVerifier::verify(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const Proof&   proof)
{
    last_used_.clear();

    if (proof.system != System::COMB ||
        !std::holds_alternative<CombProof>(proof.body)) {
        return MAKE_ERROR << "CombVerifier: proof is not a CombProof";
    }
    const CombProof& cp = std::get<CombProof>(proof.body);

    TRY(check_description_free(goal_formula, cp));
    TRY(verify_well_formed(cp));
    TRY(verify_target_is_formula_graph(ctx, goal_formula, cp));
    TRY(verify_fonet(cp));
    TRY(verify_skew_bifibration(cp));

    last_used_ = cp.last_used;
    return util::Ok();
}

util::ResultStatus CombVerifier::verify_well_formed(
    const CombProof& proof) const
{
    const size_t fonet_vertex_size = proof.source.num_vertex;
    if (proof.fibration.size() != fonet_vertex_size) {
        return MAKE_ERROR << "Fibration domain mismatch";
    }
    for (size_t i = 0; i < proof.fibration.size(); i++) {
        if (proof.fibration[i] >= proof.target.labels.size()) {
            return MAKE_ERROR << "Fibration range mismatch";
        }
    }
    for (const auto& edge : proof.source.cograph_edges) {
        if (!(edge.first < fonet_vertex_size && edge.second < fonet_vertex_size)) {
            return MAKE_ERROR << "Fonet cograph edge ill-formed: " << edge.first << ", " << edge.second;
        }
    }
    for (const auto& edge : proof.source.binding_edges) {
        if (!(edge.first < fonet_vertex_size && edge.second < fonet_vertex_size)) {
            return MAKE_ERROR << "Fonet bind edge ill-formed: " << edge.first << ", " << edge.second;
        }
    }
    // Links are 2-element colour classes (paper Def. 5.1) — endpoints
    // must be in range and distinct.
    for (const auto& link : proof.source.links) {
        if (!(link.first < fonet_vertex_size && link.second < fonet_vertex_size)) {
            return MAKE_ERROR << "Fonet link ill-formed: " << link.first << ", " << link.second;
        }
        if (link.first == link.second) {
            return MAKE_ERROR << "Fonet link is a self-pair: " << link.first;
        }
    }

    const size_t fograph_vertex_size = proof.target.labels.size();
    for (const auto& edge : proof.target.cograph_edges) {
        if (!(edge.first < fograph_vertex_size && edge.second < fograph_vertex_size)) {
            return MAKE_ERROR << "Fograph cograph edge ill-formed: " << edge.first << ", " << edge.second;
        }
    }
    for (const auto& edge : proof.target.binding_edges) {
        if (!(edge.first < fograph_vertex_size && edge.second < fograph_vertex_size)) {
            return MAKE_ERROR << "Fograph bind edge ill-formed: " << edge.first << ", " << edge.second;
        }
    }

    if (!proof.target.source_formula.valid()) {
        return MAKE_ERROR << "Fograph source_formula is invalid";
    }

    return util::Ok();
}

// =====================================================================
// Phase 1 — target == G(goal_formula)
// =====================================================================
//
// Strategy S1 (strict positional): build the canonical G(NNF(goal_formula))
// with the in-house Fograph constructor, then compare element-wise to
// the proof's stored target. Vertex order is the builder's pre-order;
// translators must emit in the same order.
//
// Edge comparison is multiset-equality modulo normalization:
//   * cograph_edges are undirected → normalize each pair to (min, max)
//   * binding_edges are directed   → no swap, just sort.

namespace {

bool labels_equal(const VertexLabel& a, const VertexLabel& b) {
    if (a.kind != b.kind) return false;
    switch (a.kind) {
        case VertexKind::Atom:
            return a.pred == b.pred && a.negated == b.negated && a.args == b.args;
        case VertexKind::Binder:
            return a.var == b.var && a.is_existential == b.is_existential;
        case VertexKind::One:
            return true;
    }
    return false;
}

std::vector<std::pair<size_t, size_t>>
sorted_undirected(std::vector<std::pair<size_t, size_t>> es) {
    for (auto& e : es) if (e.first > e.second) std::swap(e.first, e.second);
    std::sort(es.begin(), es.end());
    return es;
}

std::vector<std::pair<size_t, size_t>>
sorted_directed(std::vector<std::pair<size_t, size_t>> es) {
    std::sort(es.begin(), es.end());
    return es;
}

util::ResultStatus compare_fographs(const Fograph& expected,
                                    const Fograph& actual)
{
    if (expected.labels.size() != actual.labels.size()) {
        return MAKE_ERROR
            << "vertex count mismatch: expected " << expected.labels.size()
            << ", got " << actual.labels.size();
    }
    for (size_t i = 0; i < expected.labels.size(); ++i) {
        if (!labels_equal(expected.labels[i], actual.labels[i])) {
            return MAKE_ERROR << "vertex label mismatch at index " << i;
        }
    }
    if (sorted_undirected(expected.cograph_edges) !=
        sorted_undirected(actual.cograph_edges))
    {
        return MAKE_ERROR << "cograph_edges differ";
    }
    if (sorted_directed(expected.binding_edges) !=
        sorted_directed(actual.binding_edges))
    {
        return MAKE_ERROR << "binding_edges differ";
    }
    return util::Ok();
}

}  // namespace

util::ResultStatus CombVerifier::verify_target_is_formula_graph(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const CombProof& proof) const
{
    FormulaBuilder fb(ctx);
    FormulaHandle  nnf_goal = fb.to_nnf(goal_formula);
    Fograph        expected(nnf_goal);
    return compare_fographs(expected, proof.target);
}

// Apply the dualizer δ to a single Term. With no descriptions, terms
// are Fixed or Gen; only Fixed leaves are subject to substitution
// (Gens at the top level are not fonet binder refs).
Term apply_dualizer_to_term(
    const Term& t,
    const std::unordered_map<var_index, Term>& delta)
{
    if (t.is_fixed()) {
        auto it = delta.find(t.as_variable());
        if (it != delta.end()) return it->second;
    }
    return t;
}

std::vector<Term> apply_dualizer_to_args(
    const std::vector<Term>& args,
    const std::unordered_map<var_index, Term>& delta)
{
    std::vector<Term> out;
    out.reserve(args.size());
    for (const auto& a : args) out.push_back(apply_dualizer_to_term(a, delta));
    return out;
}

util::ResultStatus CombVerifier::verify_fonet(
    const CombProof& proof) const
{
    // 2A.1 — every atom is in exactly one link; binders and 1 are unlinked.
    std::vector<int> in_link(proof.source.num_vertex);
    for (const auto & link : proof.source.links) {
        in_link[link.first]++;
        in_link[link.second]++;
    }
    for (size_t v = 0; v < proof.source.num_vertex; v++) {
        switch (proof.source_label(v).kind) {
            case VertexKind::Atom:
                if (in_link[v] != 1)
                    return MAKE_ERROR << "Atom must have exactly one link (has " << in_link[v] << ")";
                break;
            case VertexKind::One:
            case VertexKind::Binder:
                if (in_link[v] != 0)
                    return MAKE_ERROR << "Binder or 1 can't be in a link";
                break;
        }
    }

    // Collect existential and universal *variable indices* (from each
    // binder's label) for use by the dualizer checks.
    std::unordered_set<var_index> universal;
    std::unordered_set<var_index> existential;
    for (size_t v = 0; v < proof.source.num_vertex; v++) {
        const VertexLabel& lbl = proof.source_label(v);
        if (lbl.kind == VertexKind::Binder) {
            (lbl.is_existential ? existential : universal).insert(lbl.var);
        }
    }

    // 2B.1 / 2B.2 — dualizer keys are existential vars, image terms
    // reference only universal vars (no existentials). With no
    // descriptions, a dualizer image is either Fixed (a universal var)
    // or Gen (not a fonet binder ref — ignore).
    for (auto const & [x, term] : proof.source.dualizer) {
        if (!existential.count(x)) {
            return MAKE_ERROR
                << "dualizer(" << x << ") is not an existential-binder variable";
        }
        if (term.is_fixed() && existential.count(term.as_variable())) {
            return MAKE_ERROR
                << "dualizer(" << x << ") references existential variable "
                << term.as_variable();
        }
    }

    // 2B.1 totality — every existential must have an entry in the dualizer.
    for (var_index x : existential) {
        if (!proof.source.dualizer.count(x)) {
            return MAKE_ERROR
                << "dualizer is missing existential-binder variable " << x;
        }
    }

    // 2A.2 — link endpoints are pre-dual (same predicate, opposite polarity).
    // 2B.3 — link endpoints become exactly dual after applying the dualizer.
    for (auto const & link : proof.source.links) {
        auto const & l1 = proof.source_label(link.first);
        auto const & l2 = proof.source_label(link.second);
        if (l1.negated == l2.negated || l1.pred != l2.pred) {
            return MAKE_ERROR << link.first << " and " << link.second << " are not predual";
        }

        auto args1 = apply_dualizer_to_args(l1.args, proof.source.dualizer);
        auto args2 = apply_dualizer_to_args(l2.args, proof.source.dualizer);
        if (args1 != args2) {
            return MAKE_ERROR
                << "link {" << link.first << ", " << link.second
                << "}: args do not unify under dualizer";
        }
    }
    
    // 2A.3 — binder legality (paper Def. 3.2).
    //   (C1) every binder's scope contains ≥1 atom-labelled vertex;
    //   (C2) every binder's scope contains no other binder with the same var.
    // Scope of binder b = leaves under parent(leaf_of(b)) in the cotree.
    Cotree cotree(proof.source.num_vertex, proof.source.cograph_edges);
    if (!cotree.ok()) {
        return MAKE_ERROR << "source cograph_edges do not form a cograph (induced P_4)";
    }
    for (size_t v = 0; v < proof.source.num_vertex; v++) {
        const VertexLabel& label = proof.source_label(v);
        if (label.kind != VertexKind::Binder) continue;

        size_t v_node    = cotree.leaf_of(v);
        size_t v_subtree = cotree.parent(v_node);
        if (v_subtree == v_node) {
            return MAKE_ERROR << "binder " << v << " has no proper scope module";
        }

        bool has_atom   = false;
        bool dup_binder = false;
        cotree.for_each_leaf_in_subtree(v_subtree, [&](size_t u) {
            if (u == v) return;
            const VertexLabel& u_label = proof.source_label(u);
            if (u_label.kind == VertexKind::Atom) has_atom = true;
            if (u_label.kind == VertexKind::Binder && u_label.var == label.var)
                dup_binder = true;
        });
        if (!has_atom) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") has no literal in scope (Def. 3.2)";
        }
        if (dup_binder) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") shares variable with another binder in scope (Def. 3.2)";
        }
    }
    // 2C — no induced bimatching in the leap graph. Per paper §14.2
    // we use the cotree-driven decomposition of Lemmas 10.21/10.22
    // rather than direct bimatching detection (see leap.{h,cpp}).
    auto const & leap = build_leap_graph(proof);
    if (leap.is_error()) {
        return leap.error();
    }
    return verify_no_bimatching(proof, cotree, leap.value());
}

// is_homomorphism_dir — f is a *directed* graph homomorphism.
//
//   Spec (paper §4): f : (V,E) → (V',E') is a homomorphism iff
//       ∀ ⟨u,v⟩ ∈ E.   ⟨f(u), f(v)⟩ ∈ E'
//   Every source edge maps to a target edge, *direction preserved* —
//   dst membership is tested with the exact ordering, no swap.
//
//   Applied to the binding graph (edges directed binder → literal).
//   `fibration` is f indexed by source vertex; `src_edges` is E,
//   `dst_edges` is E'. Ok iff every source edge is covered.
util::ResultStatus is_homomorphism_dir(std::vector<size_t> const &fibration,
                     Edges const & src_edges,
                     Edges const & dst_edges)
{
    std::set<Edge> dst_edges_set;
    for (auto const & e : dst_edges) {
        dst_edges_set.insert(e);
    }
    for (auto const & e : src_edges) {
        if (!dst_edges_set.count({fibration[e.first], fibration[e.second]})) 
            return MAKE_ERROR << "Fibration is not homomorphism at edge " << e.first << ", " << e.second;
    }
    return util::Ok();
}

// is_homomorphism — f is an *undirected* graph homomorphism.
//
//   Spec (paper §4): f : (V,E) → (V',E') is a homomorphism iff
//       ∀ {u,v} ∈ E.   {f(u), f(v)} ∈ E'
//   Every source edge maps to a target edge. Edges are undirected,
//   so dst membership is tested in *both* orderings.
//
//   Applied to the cograph (the ∧/∨ structure). `fibration` is f
//   indexed by source vertex; `src_edges` is E, `dst_edges` is E'.
//   Ok iff every source edge is covered.
util::ResultStatus is_homomorphism(std::vector<size_t> const &fibration,
                     Edges const & src_edges,
                     Edges const & dst_edges)
{
    std::set<Edge> dst_edges_set;
    for (auto const & e : dst_edges) {
        dst_edges_set.insert(e);
        dst_edges_set.insert({e.second, e.first});
    }
    for (auto const & e : src_edges) {
        if (!dst_edges_set.count({fibration[e.first], fibration[e.second]})) 
            return MAKE_ERROR << "Fibration is not homomorphism at edge " << e.first << ", " << e.second;
    }
    return util::Ok();
}

// is_skew_fibration — f is an undirected *skew fibration* (paper §4).
//
//   Spec: f : (V,E) → (V',E') is a skew fibration iff
//       ∀ v ∈ V.  ∀ w with {w, f(v)} ∈ E'.
//           ∃ w̃ ∈ V.  {w̃, v} ∈ E   ∧   {f(w̃), w} ∉ E'
//   Read: every target edge incident to f(v) is "covered" by a
//   source edge at v whose far endpoint maps to something *not
//   adjacent* to w. The lift may land on w itself — that satisfies
//   {f(w̃),w} ∉ E' automatically, since there are no self-loops.
//
//   This is strictly weaker than an ordinary fibration: the lift
//   need not be unique and need not map exactly onto w. That slack
//   is what models weakening + contraction on the ∧/∨ structure.
//
//   Applied to the cograph. Assumes f is already a homomorphism.
//   `src_n` / `dst_n` size the vertex sets (isolated vertices have
//   no edges, so they can't be recovered from the edge lists).
util::ResultStatus is_skew_fibration(std::vector<size_t> const &fibration,
                     size_t src_n, Edges const & src_edges,
                     size_t dst_n, Edges const & dst_edges)
{
    (void)dst_n;
    if (auto status = is_homomorphism(fibration, src_edges, dst_edges); status.is_error()) {
        return status;
    }
    std::unordered_map<size_t, std::unordered_set<size_t>> dst_adj;
    std::set<Edge> src_edge_set;
    for (Edge const & e : dst_edges) {
        dst_adj[e.first].insert(e.second);
        dst_adj[e.second].insert(e.first);
    }
    for (Edge const & e : src_edges) {
        src_edge_set.insert(e);
        src_edge_set.insert({e.second, e.first});
    }
    for (size_t v = 0; v < src_n; v++) {
        for(size_t w : dst_adj[fibration[v]]) {
            bool check = false;
            for (size_t w_ = 0; w_ < src_n; w_++) {
                if (src_edge_set.count({v, w_}) && !dst_adj[w].count(fibration[w_])) {
                    check = true;
                    break;
                }
            }
            if (!check) {
                return MAKE_ERROR << "Skew fibration does not hold for vertex " << v;
            }
        }
    }
    return util::Ok();
}

// is_fibration_dir — f is a directed *(ordinary) fibration* (paper §4).
//
//   Spec: f : (V,E) → (V',E') is a fibration iff
//       ∀ v ∈ V.  ∀ w with ⟨w, f(v)⟩ ∈ E'.
//           ∃! w̃ ∈ V.  ⟨w̃, v⟩ ∈ E   ∧   f(w̃) = w
//   Read: every target edge pointing *into* f(v) lifts to a *unique*
//   source edge pointing into v that maps *exactly* onto it. No skew
//   slack here — binding structure is rigid (no weakening/contraction
//   acts on binders).
//
//   Applied to the binding graph (edges directed binder → literal),
//   so the relevant edges are those *into* f(v): f(v) is the literal.
//   Assumes f is already a homomorphism.
util::ResultStatus is_fibration_dir(std::vector<size_t> const &fibration,
                     size_t src_n, Edges const & src_edges,
                     size_t dst_n, Edges const & dst_edges)
{
    (void)dst_n;
    if (auto status = is_homomorphism_dir(fibration, src_edges, dst_edges); status.is_error()) {
        return status;
    }
    std::unordered_map<size_t, std::unordered_set<size_t>> inverse_fibration;
    for (size_t i = 0; i < src_n; i++) {
         inverse_fibration[fibration[i]].insert(i);
    }
    // Predecessor map: dst_pred[x] = { y : ⟨y, x⟩ ∈ E' }. The spec
    // quantifies over edges *into* f(v), so we need predecessors, not
    // successors.
    std::unordered_map<size_t, std::unordered_set<size_t>> dst_pred;
    std::set<Edge> src_edge_set;
    for (Edge const & e : dst_edges) {
        dst_pred[e.second].insert(e.first);
    }
    for (Edge const & e : src_edges) {
        src_edge_set.insert(e);
    }
    for (size_t v = 0; v < src_n; v++) {
        for(size_t w : dst_pred[fibration[v]]) {
            size_t num_w_ = 0;
            for (size_t w_ : inverse_fibration[w]) {
                num_w_ += src_edge_set.count({w_, v});
            }
            if (num_w_ != 1) {
                return MAKE_ERROR << "Binding fibration does not hold for vertex " << v << " with witness count " << num_w_;
            }
        }
    }
    return util::Ok();
}

util::ResultStatus CombVerifier::verify_skew_bifibration(
    const CombProof& proof) const
{
    if (proof.fibration.size() != proof.source.num_vertex) {
        return MAKE_ERROR << "Fibration doesn't cover full domain";
    }
    if (auto status = is_fibration_dir(proof.fibration, proof.source.num_vertex, proof.source.binding_edges, proof.target.num_vertex(), proof.target.binding_edges); status.is_error()) {
        return status;
    }
    return is_skew_fibration(proof.fibration, proof.source.num_vertex, proof.source.cograph_edges, proof.target.num_vertex(), proof.target.cograph_edges);
}

}  // namespace logic::proof::comb
