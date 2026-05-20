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

// Boundary check: enforce the term-system scope of the comb verifier.
//
// Hughes (2019) allows compound terms in atom args and in dualizer
// images (e.g., δ(x) = f(y, z)). The project's Term type has no
// compound variant — only Fixed (a variable), Gen (de-Bruijn), and
// Description (iota). The downstream unification in build_leap_graph
// and the substitution in apply_dualizer_to_term both assume every
// atom arg and dualizer image is a single Fixed variable.
//
// This precondition is enforced here so the assumption is explicit:
//   * Descriptions are upstream-eliminated and rejected here.
//   * Gen is supposed to be rewritten to Fixed by the Fograph builder
//     before reaching the verifier; we reject any residue.
//   * Anything else (a future compound variant) is rejected too.
//
// Without this check, a future Term variant would be silently treated
// as rigid-opaque by apply_dualizer_to_term (which falls through to
// `return t;`), producing under-counted dependencies and a verifier
// that can accept non-proofs (Hughes Lemma 10.13).
util::ResultStatus check_term_system_scope(FormulaHandle goal_formula,
                                           const CombProof& cp) {
    if (formula_has_description(goal_formula)) {
        return MAKE_ERROR << "CombVerifier: goal formula contains a description "
                             "term; comb proof system is description-free, run "
                             "eliminate_descriptions in the translator first";
    }
    auto check_arg = [](const Term& arg, const char* where, size_t idx) -> util::ResultStatus {
        if (arg.is_fixed()) return util::Ok();
        if (arg.is_description()) {
            return MAKE_ERROR << "CombVerifier: " << where << " " << idx
                              << " contains a description term";
        }
        if (arg.is_generalized()) {
            return MAKE_ERROR << "CombVerifier: " << where << " " << idx
                              << " contains a Gen (de-Bruijn) term; "
                                 "Fograph builder must rewrite Gen→Fixed "
                                 "before reaching the verifier";
        }
        return MAKE_ERROR << "CombVerifier: " << where << " " << idx
                          << " contains an unknown Term variant; "
                             "verifier scope is Fixed-only (see Hughes "
                             "Lemma 10.13 for the compound-term case)";
    };
    for (size_t i = 0; i < cp.target.labels.size(); ++i) {
        const auto& lbl = cp.target.labels[i];
        if (lbl.kind != VertexKind::Atom) continue;
        for (const auto& arg : lbl.args) {
            TRY(check_arg(arg, "target atom-label", i));
        }
    }
    for (const auto& [x, term] : cp.source.dualizer) {
        TRY(check_arg(term, "dualizer image for var", x));
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

    TRY(check_term_system_scope(goal_formula, cp));
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
    // WF-2: cograph edges are simple (no self-loops, no duplicates) per
    // Hughes §2: "(V, E) is a set V of vertices and a set E ⊆ {{v,w} :
    // v,w ∈ V, v ≠ w} of edges." We normalize {u,v} as (min, max) for
    // duplicate detection. Self-loops would corrupt the cotree builder
    // and Ω construction; duplicates inflate iteration in Case C.
    auto check_simple_undirected = [&](const Edges& es, const char* where,
                                       size_t bound) -> util::ResultStatus {
        std::set<std::pair<size_t, size_t>> seen;
        for (const auto& e : es) {
            if (!(e.first < bound && e.second < bound)) {
                return MAKE_ERROR << where << " edge ill-formed: "
                                  << e.first << ", " << e.second;
            }
            if (e.first == e.second) {
                return MAKE_ERROR << where << " has self-loop at vertex "
                                  << e.first;
            }
            auto norm = std::minmax(e.first, e.second);
            auto [it, inserted] = seen.insert({norm.first, norm.second});
            if (!inserted) {
                return MAKE_ERROR << where << " has duplicate edge {"
                                  << norm.first << ", " << norm.second << "}";
            }
        }
        return util::Ok();
    };
    TRY(check_simple_undirected(proof.source.cograph_edges,
                                "fonet cograph", fonet_vertex_size));

    // WF-3: binding edges are directed binder → atom (Hughes §3). Source
    // must be a Binder vertex, target must be an Atom (the literal it
    // binds). Without this, Phase 3's is_fibration_dir is given garbage.
    auto check_binding = [&](const Edges& es, const Fograph* labels_src,
                             const CombProof* cp_for_source,
                             const char* where, size_t bound) -> util::ResultStatus {
        std::set<std::pair<size_t, size_t>> seen;
        for (const auto& e : es) {
            if (!(e.first < bound && e.second < bound)) {
                return MAKE_ERROR << where << " edge ill-formed: "
                                  << e.first << ", " << e.second;
            }
            if (e.first == e.second) {
                return MAKE_ERROR << where << " has self-loop at vertex "
                                  << e.first;
            }
            auto [it, inserted] = seen.insert({e.first, e.second});
            if (!inserted) {
                return MAKE_ERROR << where << " has duplicate directed edge ("
                                  << e.first << ", " << e.second << ")";
            }
            // Endpoint kind check. labels_src is non-null for the target
            // fograph; for the source we look up via cp_for_source->source_label.
            const VertexLabel& src_lbl = labels_src
                ? labels_src->labels[e.first]
                : cp_for_source->source_label(e.first);
            const VertexLabel& dst_lbl = labels_src
                ? labels_src->labels[e.second]
                : cp_for_source->source_label(e.second);
            if (src_lbl.kind != VertexKind::Binder) {
                return MAKE_ERROR << where << " binding edge source "
                                  << e.first << " is not a Binder";
            }
            if (dst_lbl.kind != VertexKind::Atom) {
                return MAKE_ERROR << where << " binding edge target "
                                  << e.second << " is not an Atom";
            }
        }
        return util::Ok();
    };
    TRY(check_binding(proof.source.binding_edges, nullptr, &proof,
                      "fonet binding", fonet_vertex_size));

    // Links are 2-element colour classes (paper Def. 5.1) — endpoints
    // must be in range and distinct. 2A.1 enforces every-literal-in-link
    // counts; here we add explicit duplicate-link rejection.
    {
        std::set<std::pair<size_t, size_t>> seen_links;
        for (const auto& link : proof.source.links) {
            if (!(link.first < fonet_vertex_size && link.second < fonet_vertex_size)) {
                return MAKE_ERROR << "Fonet link ill-formed: " << link.first << ", " << link.second;
            }
            if (link.first == link.second) {
                return MAKE_ERROR << "Fonet link is a self-pair: " << link.first;
            }
            auto norm = std::minmax(link.first, link.second);
            auto [it, inserted] = seen_links.insert({norm.first, norm.second});
            if (!inserted) {
                return MAKE_ERROR << "Fonet has duplicate link {"
                                  << norm.first << ", " << norm.second << "}";
            }
        }
    }

    const size_t fograph_vertex_size = proof.target.labels.size();
    TRY(check_simple_undirected(proof.target.cograph_edges,
                                "fograph cograph", fograph_vertex_size));
    TRY(check_binding(proof.target.binding_edges, &proof.target, nullptr,
                      "fograph binding", fograph_vertex_size));

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

    // 2A.0 — rectification (Hughes Def. §3 / Def. 5.2 precondition).
    //
    // Def. 5.2: "Without loss of generality, assume K is rectified."
    // The dualizer and the dependency characterization (Lemma 10.13)
    // are only well-defined on rectified fographs. Rectification (Def.
    // §3) requires each variable to label EXACTLY ONE binder. 2A.3 only
    // checks "no same-var binder in scope"; two binders sharing a var
    // across disjoint scopes would pass 2A.3 yet break build_leap_graph
    // (binder_vertex[var] keeps only the last; the existential/universal
    // sets collapse them). We enforce global var-uniqueness here.
    {
        std::unordered_set<var_index> seen_binder_vars;
        for (size_t v = 0; v < proof.source.num_vertex; v++) {
            const VertexLabel& lbl = proof.source_label(v);
            if (lbl.kind != VertexKind::Binder) continue;
            if (!seen_binder_vars.insert(lbl.var).second) {
                return MAKE_ERROR
                    << "source fonet is not rectified: variable " << lbl.var
                    << " labels more than one binder (Hughes Def. §3 / Def. 5.2 "
                       "precondition; build_leap_graph keys by var and would "
                       "conflate them)";
            }
        }
    }

    // Collect existential and universal *variable indices* (from each
    // binder's label) for use by the dualizer checks. After 2A.0 each
    // var labels exactly one binder, so these sets are unambiguous.
    std::unordered_set<var_index> universal;
    std::unordered_set<var_index> existential;
    for (size_t v = 0; v < proof.source.num_vertex; v++) {
        const VertexLabel& lbl = proof.source_label(v);
        if (lbl.kind == VertexKind::Binder) {
            (lbl.is_existential ? existential : universal).insert(lbl.var);
        }
    }

    // 2B.1 / 2B.2 — dualizer keys are existential vars; image terms
    // reference only known universal-binder vars.
    //
    // Hughes Def. 5.2: δ images may contain universal binder variables
    // (and stems for the most-general-dualizer construction, Lemma
    // 10.12). The project's term system does not separately track
    // stems, so within this verifier's scope, the image variable must
    // be a known universal binder.
    //
    // check_term_system_scope already verified the image is Fixed.
    for (auto const & [x, term] : proof.source.dualizer) {
        if (!existential.count(x)) {
            return MAKE_ERROR
                << "dualizer(" << x << ") is not an existential-binder variable";
        }
        if (!term.is_fixed()) {
            return MAKE_ERROR
                << "dualizer(" << x << ") image is not a Fixed term "
                   "(check_term_system_scope should have caught this)";
        }
        var_index image_var = term.as_variable();
        if (existential.count(image_var)) {
            return MAKE_ERROR
                << "dualizer(" << x << ") references existential variable "
                << image_var;
        }
        if (!universal.count(image_var)) {
            return MAKE_ERROR
                << "dualizer(" << x << ") image variable " << image_var
                << " is not a known universal binder of the fonet "
                   "(Hughes Def. 5.2 requires image vars to be universal "
                   "binders; this term system does not track stems)";
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
    //   (C2) every binder's scope contains no other binder with the same var;
    //   (C3) the stored is_existential agrees with the cograph structure:
    //        existential ⇔ b is ×-adjacent to every other vertex in its scope,
    //        universal   ⇔ b is ×-adjacent to no other vertex in its scope.
    //        Paper Def. 3.2's footnote 4: every binder is either existential
    //        or universal (and not both) because the scope is a proper strong
    //        module. Without this check, Case B in leap.cpp (which reads edges
    //        only) and Case C.2 (which trusts the stored label) can disagree.
    // Scope of binder b = leaves under parent(leaf_of(b)) in the cotree.
    Cotree cotree(proof.source.num_vertex, proof.source.cograph_edges);
    if (!cotree.ok()) {
        return MAKE_ERROR << "source cograph_edges do not form a cograph (induced P_4)";
    }
    // Adjacency set for the cograph, for the existential/universal check (C3).
    std::vector<std::unordered_set<size_t>> source_adj(proof.source.num_vertex);
    for (const Edge& e : proof.source.cograph_edges) {
        source_adj[e.first].insert(e.second);
        source_adj[e.second].insert(e.first);
    }
    // Index source binding_edges by binder for the scope check (C4 below).
    std::vector<std::vector<size_t>> bind_targets(proof.source.num_vertex);
    for (const Edge& e : proof.source.binding_edges) {
        bind_targets[e.first].push_back(e.second);
    }
    for (size_t v = 0; v < proof.source.num_vertex; v++) {
        const VertexLabel& label = proof.source_label(v);
        if (label.kind != VertexKind::Binder) continue;

        size_t v_node    = cotree.leaf_of(v);
        size_t v_subtree = cotree.parent(v_node);
        if (v_subtree == v_node) {
            return MAKE_ERROR << "binder " << v << " has no proper scope module";
        }

        bool has_atom        = false;
        bool dup_binder      = false;
        size_t scope_others  = 0;          // # of other vertices in scope
        size_t adj_others    = 0;          // # of those ×-adjacent to v
        std::unordered_set<size_t> scope_members;  // V(scope) for C4
        cotree.for_each_leaf_in_subtree(v_subtree, [&](size_t u) {
            scope_members.insert(u);
            if (u == v) return;
            const VertexLabel& u_label = proof.source_label(u);
            if (u_label.kind == VertexKind::Atom) has_atom = true;
            if (u_label.kind == VertexKind::Binder && u_label.var == label.var)
                dup_binder = true;
            ++scope_others;
            if (source_adj[v].count(u)) ++adj_others;
        });
        if (!has_atom) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") has no literal in scope (Def. 3.2)";
        }
        if (dup_binder) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") shares variable with another binder in scope (Def. 3.2)";
        }
        // (C3) Existential ⇔ ×-adjacent to *every* other scope vertex.
        //       Universal   ⇔ ×-adjacent to *no*    other scope vertex.
        // Anything in between is not a valid logical-cograph binder per
        // Def. 3.2 (footnote 4): the scope is a proper strong module, so
        // adjacency to the binder is all-or-nothing.
        const bool structurally_existential = (adj_others == scope_others);
        const bool structurally_universal   = (adj_others == 0);
        if (!structurally_existential && !structurally_universal) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") is adjacent to " << adj_others << " of "
                              << scope_others << " scope vertices — neither "
                              "existential (all) nor universal (none) "
                              "(Def. 3.2 footnote 4)";
        }
        if (label.is_existential != structurally_existential) {
            return MAKE_ERROR << "binder " << v << " (var " << label.var
                              << ") stored is_existential=" << label.is_existential
                              << " disagrees with cograph structure (× adj to "
                              << adj_others << "/" << scope_others
                              << " scope vertices)";
        }
        // (C4) Every binding edge from b must target a vertex IN b's scope.
        // Hughes Def. 3.2: "An x-binder binds every x-literal in its scope."
        // A binding edge to a literal outside the scope is a phantom edge —
        // possible if a Fixed atom-arg's var_index accidentally collides
        // with the binder's fresh next_binder_var++ index. See PAPER_AUDIT
        // P1-3.
        for (size_t bound_v : bind_targets[v]) {
            if (!scope_members.count(bound_v)) {
                return MAKE_ERROR << "binder " << v << " (var " << label.var
                                  << ") has a binding edge to vertex "
                                  << bound_v << " outside its cograph scope "
                                  "module (Def. 3.2 — phantom binding edge; "
                                  "likely a var_index collision between a "
                                  "Fixed atom-arg and a binder's fresh var)";
            }
        }
    }
    // 2C — no induced bimatching in the leap graph. Per paper §14.2
    // we use the cotree-driven decomposition of Lemmas 10.21/10.22
    // rather than direct bimatching detection (see leap.{h,cpp}).
    auto const & leap = build_leap_graph(proof);
    if (leap.is_error()) {
        return leap.error();
    }

    // 2C.0 — leap/cograph disjointness (Def. 5.3 consequence).
    //
    // In a fonet, no leap connects two cograph-adjacent vertices: if
    // {u,v} is both a cograph edge AND a leap (link or dependency),
    // then W = {u,v} induces a matching in K (the cograph edge) AND in
    // L_K (the leap), which is exactly an induced bimatching. By
    // Def. 5.3 this rules out fonet-hood.
    //
    // This is the structural fact that closes the apparent gap in
    // Hughes' Lemma 10.21 → 10.18 step: the bridge condition in Ω only
    // forbids leaps between *different* ×-pairs, but 10.18's
    // precondition also requires no leap *within* the bridge ×-pair
    // (G_m × G_{m+1}). The disjointness above ensures the within-pair
    // case is vacuous.
    //
    // The decomposition algorithm in leap.cpp assumes this fact
    // without checking it directly. We enforce it explicitly here so
    // that an adversarial input with overlapping leap/cograph edges
    // is rejected at the 2C boundary rather than producing an
    // unsound decomposition downstream.
    {
        std::set<std::pair<size_t, size_t>> cograph_pairs;
        for (const Edge& e : proof.source.cograph_edges) {
            auto norm = std::minmax(e.first, e.second);
            cograph_pairs.insert({norm.first, norm.second});
        }
        for (const Edge& l : leap.value()) {
            auto norm = std::minmax(l.first, l.second);
            if (cograph_pairs.count({norm.first, norm.second})) {
                return MAKE_ERROR
                    << "Fonet has a leap {" << norm.first << ", "
                    << norm.second << "} that is also a cograph edge — "
                    "this induces a bimatching on W = {u,v}, violating "
                    "Def. 5.3 (closes Hughes' Lemma 10.21 → 10.18 gap)";
            }
        }
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
