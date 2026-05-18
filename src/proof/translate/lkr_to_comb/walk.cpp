#include "walk.h"

#include <algorithm>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

size_t count_fograph_vertices(FormulaHandle f) {
    const Formula& fm = f.get();
    if (fm.is_predicate() || fm.is_schema_var()) return 1;
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        if (c.op == Op::Not) return 1;
        if (c.op == Op::And || c.op == Op::Or) {
            return count_fograph_vertices(c.left) +
                   count_fograph_vertices(c.right);
        }
        return 0;
    }
    if (fm.is_quantified()) {
        return 1 + count_fograph_vertices(fm.as_quantified().body);
    }
    return 0;
}

// =====================================================================
// Leaf builders.
// =====================================================================

// =====================================================================
// Rule: CloseByLemma  (Hughes §15 Strategy B; LKR_TO_COMB_DESIGN.md §4.11)
//
// Premise: (none — closing leaf)
// Conclusion: CombProof of any sequent containing φ_L, where φ_L is
//   the formula of the lemma named in `op.axiom`. Strategy B
//   precondition: the closing op must be preceded by Cut(φ_L), so
//   that the LEFT subgoal's last entry is φ_L.
//
// Operation (per §4.11):
//   - Look up the lemma's pre-built CombProof L_proof in cc.lemmas.
//   - Target = shared outer canonical target.
//   - Source = lemma's source (edges/links inherited; dualizer rebuilt).
//   - Position remap σ_pos = entry_positions.back() (= φ_L's
//     positions in the outer canonical target).
//   - Fibration = lemma's fibration composed with σ_pos:
//       fibration[v] := σ_pos(lemma.fibration[v])
//   - σ build: for each binder vertex i in lemma.target, pair
//     lemma-canonical var var_L(i) with outer-canonical var
//     var_O(σ_pos(i)). Verify binder kind matches as a precondition.
//   - Dualizer remap (σ_remap): for each (x_L, t_L) in L_proof's
//     dualizer, emit (σ(x_L), σ_T(t_L)) where σ_T applies σ to
//     Fixed terms (one-pass, identity on Gen).
//
// Soundness: the lemma was verified standalone, so L_proof is a valid
//   CombProof of φ_L. Position-remapping + σ_remap preserves the
//   fibration's shape under the structural iso between lemma.target
//   and the outer slice. Strategy B's pairing with a preceding
//   Cut(φ_L) handles the §15 augmentation: (φ_L ∧ ¬φ_L) becomes a
//   new disjunct of the augmented goal.
//
// Scope limitation (open obligation; see COMPLETENESS.md): this
//   implementation assumes lemma_cp.target = G(φ_L_nnf), not the
//   §15-augmented form. Lemma CombProofs built via the full ND→Comb
//   pipeline currently target their augmented goal (extra positions
//   from any internal Cuts in the lemma proof), which doesn't match
//   the outer cut formula's slice. Cut-free lemmas (and lemmas built
//   via hand-crafted LKR programs without Cut ops) work cleanly.
util::Result<comb::CombProof> build_leaf_close_by_lemma(
    WalkContext&                                 cc,
    const lkr::CloseByLemma&                     op,
    const std::vector<std::vector<size_t>>&      entry_positions)
{
    // After Strategy A (LKR_TO_COMB_DESIGN.md §4.12), CloseByLemma ops
    // are spliced out of the LKR program by the lemma_inliner pre-pass
    // before walk runs. If walk encounters one, the pre-pass either
    // wasn't run or the lemma was missing from the registry — both are
    // translator bugs that should surface here as a clear error rather
    // than as an obscure verifier failure downstream.
    (void)cc;
    (void)entry_positions;
    return MAKE_ERROR
        << "walk(CloseByLemma): op for lemma '" << op.axiom.name
        << "' reached the walk; lemma_inliner pre-pass should have "
        << "spliced it (Strategy A, §4.12). Likely cause: lemma not "
        << "in the registry, or pipeline ordering bug.";
}

// =====================================================================
// Rule: AxiomLit  (Hughes §11.1 base case; LKR_TO_COMB_DESIGN.md §4.1)
//
// Premise: (none — closing leaf)
// Conclusion: CombProof of any sequent containing atom α at lit_a and
//   its dual ᾱ at lit_b (atomic literals, opposite polarity, dual args
//   under the dualizer).
//
// Operation: build N = {u_α, u_ᾱ} with one link {u_α, u_ᾱ}; empty
//   dualizer, no cograph/binding edges (binding edges are derived in
//   the post-pass, see derive_binding_edges); f maps the two source
//   vertices to the canonical positions of lit_a and lit_b.
//
// Soundness: the leaf is a well-formed fonet piece (Def. 5.3): every
//   atom in exactly one link, no binders so dualizer totality is
//   vacuous, no induced bimatching in the trivially-empty leap graph.
//   The skew bifibration conditions are discharged by the surrounding
//   per-rule operations after composition.
// =====================================================================
// Rule: One  (Hughes §11.1 base case; LKR_TO_COMB_DESIGN.md §4.2)
//
// Premise: (none — closing leaf)
// Conclusion: CombProof of any sequent containing the truth literal
//   ¬⊥ at index `op.idx`. LKRVerifier enforces entries[idx] = ¬⊥.
//
// Operation: build N = {u_1} with one vertex of kind One (no link;
//   the truth literal is unlinked per Def. 5.3). No cograph or binding
//   edges, empty dualizer. f maps the single source vertex to the
//   canonical position of entries[idx] — that position holds a single
//   VertexKind::One vertex in the canonical target (Fograph extension
//   in fograph.cpp::build for Compound{Not, Compound{Bottom}}).
//
// Soundness: the leaf is a well-formed fonet piece (Def. 5.3).
//   Link covering vacuous (no Atom). Dualizer totality vacuous (no
//   binders). Leap graph empty. The skew/binding fibration conditions
//   are discharged by the surrounding per-rule operations after
//   composition — identical framing to AxiomLit.
util::Result<comb::CombProof> build_leaf_one(
    WalkContext&                                 cc,
    const lkr::One&                              op,
    const std::vector<FormulaHandle>&            conclusion_entries,
    const std::vector<std::vector<size_t>>&      entry_positions)
{
    if (op.idx >= conclusion_entries.size()) {
        return MAKE_ERROR << "walk(One): idx OOR";
    }
    // One precondition: entries[idx] = ¬⊥, which Fograph maps to a
    // single VertexKind::One vertex — so exactly one canonical position.
    if (entry_positions[op.idx].size() != 1) {
        return MAKE_ERROR
            << "walk(One): entry at idx=" << op.idx << " has "
            << entry_positions[op.idx].size()
            << " canonical positions (expected 1 for ¬⊥)";
    }
    comb::CombProof cp;
    cp.target = cc.canonical_target;
    cp.source.num_vertex = 1;
    cp.fibration.resize(1);
    cp.fibration[0] = entry_positions[op.idx][0];
    return cp;
}

util::Result<comb::CombProof> build_leaf_axiom_lit(
    WalkContext&                                 cc,
    const lkr::AxiomLit&                         op,
    const std::vector<FormulaHandle>&            conclusion_entries,
    const std::vector<std::vector<size_t>>&      entry_positions)
{
    if (op.lit_a == op.lit_b) {
        return MAKE_ERROR
            << "walk(AxiomLit): lit_a == lit_b (" << op.lit_a << ")";
    }
    if (op.lit_a >= conclusion_entries.size() ||
        op.lit_b >= conclusion_entries.size()) {
        return MAKE_ERROR << "walk(AxiomLit): lit OOR";
    }
    // AxiomLit precondition: the entries at lit_a/lit_b are atomic
    // literals — each has exactly one canonical position.
    if (entry_positions[op.lit_a].size() != 1 ||
        entry_positions[op.lit_b].size() != 1) {
        return MAKE_ERROR
            << "walk(AxiomLit): entries are not atomic (lit_a has "
            << entry_positions[op.lit_a].size() << " positions, lit_b has "
            << entry_positions[op.lit_b].size() << ")";
    }
    comb::CombProof cp;
    cp.target = cc.canonical_target;  // shared canonical target
    cp.source.num_vertex = 2;
    cp.source.links.push_back({0, 1});
    cp.fibration.resize(2);
    cp.fibration[0] = entry_positions[op.lit_a][0];
    cp.fibration[1] = entry_positions[op.lit_b][0];
    return cp;
}

// =====================================================================
// Rule: And  (Hughes §11.1 ∧-case; LKR_TO_COMB_DESIGN.md §4.9)
//
// Premise: CombProof(Γ_1, φ_1)   CombProof(Γ_2, φ_2)
// Conclusion: CombProof(Γ_1, Γ_2, φ_1 ∧ φ_2)
//
// Operation: G(C) = G(Γ_1) + G(Γ_2) + (G(φ_1) × G(φ_2)) — note the
//   × join on the conjuncts' fographs.
//
//   Witness portions:  P_i = f_i^{-1}(V_{G(φ_i)})
//   Strong/weak:       f_i is strong iff P_i ≠ ∅, weak otherwise.
//
//   - Both strong | both weak  → fuse disjointly with cograph edges
//     P_1 × P_2 added between the witness portions (the new × in C).
//   - One weak, one strong     → keep the weak side alone (the weak
//     side doesn't actually use its conjunct; it suffices via the
//     canonical injection for the joined conclusion).
//
// Soundness: Hughes §11.1 ∧-case lemma. Strong/weak classification
//   preserves fonet well-formedness; the fibration extends to the
//   join (cograph edges of the source mirror the new × in target).
util::Result<comb::CombProof> rule_and(
    WalkContext&                                 cc,
    const lkr::And&                              op,
    comb::CombProof                              left_cp,
    comb::CombProof                              right_cp,
    const std::vector<FormulaHandle>&            conclusion_entries,
    const std::vector<std::vector<size_t>>&      entry_positions)
{
    if (op.principal >= conclusion_entries.size()) {
        return MAKE_ERROR << "rule_and: principal OOR";
    }
    const Formula& cf = conclusion_entries[op.principal].get();
    if (!cf.is_compound() || cf.as_compound().op != Op::And) {
        return MAKE_ERROR << "rule_and: principal entry is not ∧";
    }
    FormulaHandle phi = cf.as_compound().left;
    size_t phi_count = count_fograph_vertices(phi);

    const auto& princ_pos = entry_positions[op.principal];
    if (princ_pos.size() < phi_count) {
        return MAKE_ERROR
            << "rule_and: principal positions vector smaller than phi count";
    }

    // Witness portions in canonical coordinates.
    std::unordered_set<size_t> phi_canonical(
        princ_pos.begin(), princ_pos.begin() + phi_count);
    std::unordered_set<size_t> theta_canonical(
        princ_pos.begin() + phi_count, princ_pos.end());

    std::vector<size_t> P_L, P_R;
    for (size_t v = 0; v < left_cp.fibration.size(); ++v) {
        if (phi_canonical.count(left_cp.fibration[v])) P_L.push_back(v);
    }
    for (size_t v = 0; v < right_cp.fibration.size(); ++v) {
        if (theta_canonical.count(right_cp.fibration[v])) P_R.push_back(v);
    }

    bool left_strong  = !P_L.empty();
    bool right_strong = !P_R.empty();

    comb::CombProof out;
    out.target = cc.canonical_target;

    auto fuse_disjoint = [&](size_t n_L,
                              const comb::Fonet& src_L,
                              const std::vector<size_t>& fib_L,
                              size_t n_R,
                              const comb::Fonet& src_R,
                              const std::vector<size_t>& fib_R,
                              bool add_cross_edges) {
        out.source.num_vertex = n_L + n_R;
        out.source.cograph_edges = src_L.cograph_edges;
        for (auto e : src_R.cograph_edges) {
            out.source.cograph_edges.push_back({e.first + n_L, e.second + n_L});
        }
        if (add_cross_edges) {
            for (size_t l : P_L) {
                for (size_t r : P_R) {
                    out.source.cograph_edges.push_back({l, r + n_L});
                }
            }
        }
        out.source.binding_edges = src_L.binding_edges;
        for (auto e : src_R.binding_edges) {
            out.source.binding_edges.push_back({e.first + n_L, e.second + n_L});
        }
        out.source.links = src_L.links;
        for (auto l : src_R.links) {
            out.source.links.push_back({l.first + n_L, l.second + n_L});
        }
        out.source.dualizer = src_L.dualizer;
        for (const auto& [k, v] : src_R.dualizer) {
            out.source.dualizer.emplace(k, v);
        }
        out.fibration = fib_L;
        out.fibration.insert(out.fibration.end(), fib_R.begin(), fib_R.end());
    };

    if (left_strong && right_strong) {
        fuse_disjoint(left_cp.source.num_vertex, left_cp.source,
                       left_cp.fibration,
                       right_cp.source.num_vertex, right_cp.source,
                       right_cp.fibration, /*add_cross=*/true);
    } else if (left_strong && !right_strong) {
        // RIGHT is weak — keep RIGHT alone.
        out.source    = std::move(right_cp.source);
        out.fibration = std::move(right_cp.fibration);
    } else if (!left_strong && right_strong) {
        // LEFT is weak — keep LEFT alone.
        out.source    = std::move(left_cp.source);
        out.fibration = std::move(left_cp.fibration);
    } else {
        // Both weak — fuse disjointly (no cross-edges, P_L × P_R = ∅).
        fuse_disjoint(left_cp.source.num_vertex, left_cp.source,
                       left_cp.fibration,
                       right_cp.source.num_vertex, right_cp.source,
                       right_cp.fibration, /*add_cross=*/false);
    }

    return out;
}

// =====================================================================
// Rule: Cut  (Hughes §15; LKR_TO_COMB_DESIGN.md §4.10)
//
// Premise: CombProof(Γ ∪ {θ})   CombProof(Γ ∪ {¬θ})
// Conclusion: CombProof of the §15-augmented goal, where the running
//   goal gains a disjunct (θ ∧ ¬θ). The augmentation is built once,
//   ahead of the walk, by cut_augment.cpp; the canonical target
//   already accounts for every Cut's contribution at stable positions.
//
// Operation: identical fusion to the And rule, but the "principal"
//   entry doesn't exist in the pre-Cut sequent. We treat the cut
//   formula's θ-portion on LEFT and ¬θ-portion on RIGHT as the
//   witness portions P_L, P_R; strong/weak classification proceeds
//   exactly as in rule_and.
//
// Soundness: Hughes §15 Theorem 15.1 — cut combinatorial proofs of
//   φ are by definition ordinary combinatorial proofs of the augmented
//   φ ∨ ⋁ (θ_i ∧ ¬θ_i), which is classically equivalent to φ. Each
//   (θ ∧ ¬θ) disjunct is contradictory, so adding them preserves
//   validity. Thm 15.1 ensures this is sound and complete.
util::Result<comb::CombProof> rule_cut(
    WalkContext&                                 cc,
    comb::CombProof                              left_cp,
    comb::CombProof                              right_cp,
    const std::vector<size_t>&                   theta_positions,
    const std::vector<size_t>&                   neg_theta_positions)
{
    std::unordered_set<size_t> theta_canonical(
        theta_positions.begin(), theta_positions.end());
    std::unordered_set<size_t> neg_theta_canonical(
        neg_theta_positions.begin(), neg_theta_positions.end());

    std::vector<size_t> P_L, P_R;
    for (size_t v = 0; v < left_cp.fibration.size(); ++v) {
        if (theta_canonical.count(left_cp.fibration[v])) P_L.push_back(v);
    }
    for (size_t v = 0; v < right_cp.fibration.size(); ++v) {
        if (neg_theta_canonical.count(right_cp.fibration[v])) P_R.push_back(v);
    }

    bool left_strong  = !P_L.empty();
    bool right_strong = !P_R.empty();

    comb::CombProof out;
    out.target = cc.canonical_target;

    auto fuse_disjoint = [&](size_t n_L,
                              const comb::Fonet& src_L,
                              const std::vector<size_t>& fib_L,
                              size_t n_R,
                              const comb::Fonet& src_R,
                              const std::vector<size_t>& fib_R,
                              bool add_cross_edges) {
        out.source.num_vertex = n_L + n_R;
        out.source.cograph_edges = src_L.cograph_edges;
        for (auto e : src_R.cograph_edges) {
            out.source.cograph_edges.push_back({e.first + n_L, e.second + n_L});
        }
        if (add_cross_edges) {
            for (size_t l : P_L) {
                for (size_t r : P_R) {
                    out.source.cograph_edges.push_back({l, r + n_L});
                }
            }
        }
        out.source.binding_edges = src_L.binding_edges;
        for (auto e : src_R.binding_edges) {
            out.source.binding_edges.push_back({e.first + n_L, e.second + n_L});
        }
        out.source.links = src_L.links;
        for (auto l : src_R.links) {
            out.source.links.push_back({l.first + n_L, l.second + n_L});
        }
        out.source.dualizer = src_L.dualizer;
        for (const auto& [k, v] : src_R.dualizer) {
            out.source.dualizer.emplace(k, v);
        }
        out.fibration = fib_L;
        out.fibration.insert(out.fibration.end(), fib_R.begin(), fib_R.end());
    };

    if (left_strong && right_strong) {
        fuse_disjoint(left_cp.source.num_vertex, left_cp.source,
                       left_cp.fibration,
                       right_cp.source.num_vertex, right_cp.source,
                       right_cp.fibration, /*add_cross=*/true);
    } else if (left_strong && !right_strong) {
        out.source    = std::move(right_cp.source);
        out.fibration = std::move(right_cp.fibration);
    } else if (!left_strong && right_strong) {
        out.source    = std::move(left_cp.source);
        out.fibration = std::move(left_cp.fibration);
    } else {
        fuse_disjoint(left_cp.source.num_vertex, left_cp.source,
                       left_cp.fibration,
                       right_cp.source.num_vertex, right_cp.source,
                       right_cp.fibration, /*add_cross=*/false);
    }

    return out;
}

// =====================================================================
// Rule: Forall  (Hughes §11.1 ∀-case; LKR_TO_COMB_DESIGN.md §4.7 + §7.5)
//
// Premise: CombProof(Γ, φ)   side condition: x not free in Γ
// Conclusion: CombProof(Γ, ∀x.φ)
//
// Operation: G(C) = G(Γ) + (•x + G(φ)) — note the + (universal is
//   `+`-attached to its body, i.e., no cograph edges between the
//   binder and the body in the cograph).
//
//   Witness portion: P = f^{-1}(V_{G(φ)})
//   - Case A (P = ∅): G(φ) was weakened in; •x stays uncovered, return
//     child unchanged.
//   - Case B (P ≠ ∅): add a new vertex b_x to N, no new cograph edges;
//     map b_x ↦ •x (the canonical binder position).
//
// Binding edges in source: NOT constructed here. They are derived
//   from labels in derive_binding_edges() at the end of walk, per
//   Hughes Def. 3.1. The previous per-rule construction (edges to
//   P only) missed atoms in carried-over sequent entries that share
//   the bound var (see §7.5 for the failure mode and resolution).
//
// Var alignment: requires the alpha-rename pre-pass (see
//   alpha_rename.{h,cpp}) so that op.eigen equals the canonical
//   binder var Fograph allocates at this principal's binder position.
//
// Soundness: Hughes §11.1 ∀-case lemma. The skew bifibration extends
//   to the join; the post-pass guarantees source binding edges mirror
//   the target's (which Fograph derives identically from labels).
util::Result<comb::CombProof> rule_forall(
    WalkContext&                                 cc,
    const lkr::Forall& /*op*/,
    comb::CombProof                              child,
    const std::vector<std::vector<size_t>>&      entry_positions,
    size_t                                       principal)
{
    if (principal >= entry_positions.size()) {
        return MAKE_ERROR << "rule_forall: principal OOR";
    }
    const auto& princ_pos = entry_positions[principal];
    if (princ_pos.empty()) {
        return MAKE_ERROR
            << "rule_forall: principal entry has no canonical positions "
            << "(binder stripped without preserving body)";
    }
    size_t binder_pos = princ_pos[0];
    std::unordered_set<size_t> body_canonical(
        princ_pos.begin() + 1, princ_pos.end());

    std::vector<size_t> P;
    for (size_t v = 0; v < child.fibration.size(); ++v) {
        if (body_canonical.count(child.fibration[v])) P.push_back(v);
    }

    if (P.empty()) {
        // Case A: preimage empty → •x stays uncovered in target.
        return child;
    }

    // Case B: add binder vertex; no cograph edges (universal is +-attached).
    // Binding edges are NOT added here — they're derived from labels in a
    // single post-pass at the end of walk(), matching Fograph's spec for
    // the target. See comment in derive_binding_edges() below.
    comb::CombProof out = std::move(child);
    size_t new_v = out.source.num_vertex;
    out.source.num_vertex = new_v + 1;
    out.fibration.push_back(binder_pos);
    (void)P;
    return out;
}

// =====================================================================
// Rule: Exists  (Hughes §11.1 ∃-case; LKR_TO_COMB_DESIGN.md §4.8 + §7.5)
//
// Premise: CombProof(Γ, φ{x ↦ t})   for some witness term t
// Conclusion: CombProof(Γ, ∃x.φ)
//
// Operation: G(C) = G(Γ) + (•x × G(φ)) — note the × (existential is
//   `×`-attached to its body, i.e., the binder gets cograph edges to
//   every vertex of G(φ)).
//
//   Witness portion: P = f^{-1}(V_{G(φ{x↦t})})
//   - Case A (P = ∅): φ was weakened in; return child unchanged.
//   - Case B (P ≠ ∅): add a new vertex b_x to N with cograph edges
//     {b_x, p} for every p ∈ P (mirroring the × in target); map
//     b_x ↦ •x. Extend dualizer with δ(x) = t (the witness term, looked
//     up through cc.replay.term_env via op.witness's TermRef).
//
// Binding edges in source: NOT constructed here (same as Forall;
//   derived in derive_binding_edges).
//
// Dualizer conflict check: if the same eigen has been bound by an
//   earlier Exists with a different witness, that's a translator bug
//   (the LKR program would be inconsistent). Conflicting bindings
//   surface here as MAKE_ERROR rather than via verifier failure.
//
// Soundness: Hughes §11.1 ∃-case lemma. δ(x) records the witness so
//   the linked atoms unify under δ; the cograph cross-edges encode
//   the × join in the target.
util::Result<comb::CombProof> rule_exists(
    WalkContext&                                 cc,
    const lkr::Exists&                           op,
    comb::CombProof                              child,
    const std::vector<std::vector<size_t>>&      entry_positions,
    size_t                                       principal)
{
    if (principal >= entry_positions.size()) {
        return MAKE_ERROR << "rule_exists: principal OOR";
    }
    const auto& princ_pos = entry_positions[principal];
    if (princ_pos.empty()) {
        return MAKE_ERROR << "rule_exists: principal entry has no positions";
    }
    size_t binder_pos = princ_pos[0];
    std::unordered_set<size_t> body_canonical(
        princ_pos.begin() + 1, princ_pos.end());

    std::vector<size_t> P;
    for (size_t v = 0; v < child.fibration.size(); ++v) {
        if (body_canonical.count(child.fibration[v])) P.push_back(v);
    }

    if (P.empty()) {
        // Case A: preimage empty.
        return child;
    }

    comb::CombProof out = std::move(child);
    size_t new_v = out.source.num_vertex;
    out.source.num_vertex = new_v + 1;
    out.fibration.push_back(binder_pos);

    // Cograph edges: existential binder is ×-attached to its body
    // literals in target; mirror in source for the witness portion.
    // Binding edges are derived from labels in a single post-pass at the
    // end of walk().
    for (size_t p : P) {
        out.source.cograph_edges.push_back({new_v, p});
    }

    // Dualizer: δ(eigen_x) = witness. eigen_x is the canonical binder's
    // var (= target.labels[binder_pos].var). Witness resolved via
    // replay's term_env using op.witness's TermRef.
    if (op.witness.idx >= cc.replay.term_env.size() ||
        !cc.replay.term_env[op.witness.idx].has_value()) {
        return MAKE_ERROR
            << "rule_exists: witness TermRef #" << op.witness.idx
            << " unresolved";
    }
    Term witness = *cc.replay.term_env[op.witness.idx];
    var_index eigen_x = cc.canonical_target.labels[binder_pos].var;
    // Conflicting binding for the same eigen across subgoals is OK if
    // identical; otherwise the verifier rejects.
    auto it = out.source.dualizer.find(eigen_x);
    if (it == out.source.dualizer.end()) {
        out.source.dualizer.emplace(eigen_x, witness);
    } else if (!(it->second == witness)) {
        return MAKE_ERROR
            << "rule_exists: dualizer conflict for eigen f_" << eigen_x;
    }
    return out;
}

// =====================================================================
// Post-pass: source binding-edge derivation
//   (Hughes Def. 3.1, applied to fonet; LKR_TO_COMB_DESIGN.md §7.5)
//
// In a fograph — and hence in a fonet, which is a linked fograph — the
// binding edges are not free parameters: they are DERIVED from labels.
// For each binder vertex b with var v and each atom vertex a whose
// args contain Fixed(v), the pair (b, a) is a binding edge.
//
// Fograph builds the target's binding edges this way in
// fograph.cpp::add_binding_edges. The source must follow the same
// recipe — anything else risks producing fonets whose binding edges
// fail the verifier's unique-lift fibration check against the target.
//
// Implementation: source labels via fibration (source_label(v) =
//   target.labels[fibration[v]]), then run the same per-vertex scan.
//   Any binding edges accumulated by per-rule code earlier in walk are
//   discarded — this post-pass is the single source of truth.
//
// History: the previous code constructed source binding edges per-rule
//   (rule_forall: edges to atoms in principal's body only). This was a
//   completeness bug, invisible until quantified end-to-end tests
//   exercised it (the §7.5 cut-shared-var case). The math-grounded fix
//   is this post-pass — matching Hughes' definition verbatim — rather
//   than patching per-rule constructions.
void derive_binding_edges(comb::CombProof& cp,
                          const comb::Fograph& target) {
    cp.source.binding_edges.clear();
    const size_t n = cp.source.num_vertex;
    for (size_t b = 0; b < n; ++b) {
        const comb::VertexLabel& b_lbl = target.labels[cp.fibration[b]];
        if (b_lbl.kind != comb::VertexKind::Binder) continue;
        var_index v = b_lbl.var;
        for (size_t a = 0; a < n; ++a) {
            if (a == b) continue;
            const comb::VertexLabel& a_lbl = target.labels[cp.fibration[a]];
            if (a_lbl.kind != comb::VertexKind::Atom) continue;
            for (const Term& arg : a_lbl.args) {
                if (arg.is_fixed() && arg.as_variable() == v) {
                    cp.source.binding_edges.push_back({b, a});
                    break;
                }
            }
        }
    }
}

util::Result<comb::CombProof> walk_recursive(
    WalkContext&           cc,
    const DerivationTree&  tree);

}  // namespace

util::Result<comb::CombProof> walk(
    WalkContext&           cc,
    const DerivationTree&  tree)
{
    TRY_ASSIGN(cp, walk_recursive(cc, tree));
    derive_binding_edges(cp, cc.canonical_target);
    return cp;
}

namespace {

util::Result<comb::CombProof> walk_recursive(
    WalkContext&           cc,
    const DerivationTree&  tree)
{
    if (auto* leaf = std::get_if<LeafNode>(&tree.node)) {
        const auto& seq    = cc.replay.sequent_before[leaf->op_idx];
        const auto& posv   = cc.replay.entry_positions[leaf->op_idx];
        const auto& instr  = cc.prog.instrs[leaf->op_idx];
        if (auto* ax = std::get_if<lkr::AxiomLit>(&instr)) {
            return build_leaf_axiom_lit(cc, *ax, seq, posv);
        }
        if (auto* one = std::get_if<lkr::One>(&instr)) {
            return build_leaf_one(cc, *one, seq, posv);
        }
        if (auto* cbl = std::get_if<lkr::CloseByLemma>(&instr)) {
            return build_leaf_close_by_lemma(cc, *cbl, posv);
        }
        return MAKE_ERROR
            << "walk(Leaf): op variant " << instr.index()
            << " not yet supported";
    }

    if (auto* lin = std::get_if<LinearNode>(&tree.node)) {
        TRY_ASSIGN(child, walk_recursive(cc, *lin->child));
        const auto& posv  = cc.replay.entry_positions[lin->op_idx];
        const auto& instr = cc.prog.instrs[lin->op_idx];
        if (auto* op = std::get_if<lkr::Forall>(&instr)) {
            return rule_forall(cc, *op, std::move(child), posv, op->principal);
        }
        if (auto* op = std::get_if<lkr::Exists>(&instr)) {
            return rule_exists(cc, *op, std::move(child), posv, op->principal);
        }
        if (std::holds_alternative<lkr::Or>(instr) ||
            std::holds_alternative<lkr::Exchange>(instr) ||
            std::holds_alternative<lkr::Weakening>(instr)) {
            // -------------------------------------------------------------
            // Rule: Or  (Hughes §11.1 ∨-case; LKR_TO_COMB_DESIGN.md §4.6)
            //   G(H) = G(C) identically (cograph associativity). f, N
            //   unchanged — the cheapest rule.
            //
            // Rule: Exchange  (Hughes §11.1 X-case; §4.3)
            //   Cograph commutativity. Vertices identified by occurrence
            //   (canonical position), so the canonical bijection is the
            //   identity at the structural level. f, N unchanged.
            //
            // Rule: Weakening  (Hughes §11.1 W-case; §4.4)
            //   PARTIAL: G(C) = G(H) + G(φ) with new G(φ) vertices
            //   uncovered. When the weakened entry's positions fall
            //   inside the canonical target's range (built from the
            //   §15-augmented goal), this is a no-op on N and f.
            //   When the weakened entry lands outside that range, the
            //   canonical target must be augmented — see open obligation
            //   row "Weakening" in COMPLETENESS.md.
            //
            // Soundness (all three): trivial; child is already a valid
            //   CombProof against the shared canonical target.
            // -------------------------------------------------------------
            return child;
        }
        return MAKE_ERROR
            << "walk(Linear): op variant " << instr.index()
            << " not yet supported (only Or/Exchange/Weakening handled "
            << "in phase 4)";
    }

    if (auto* br = std::get_if<BranchingNode>(&tree.node)) {
        const auto& seq   = cc.replay.sequent_before[br->op_idx];
        const auto& posv  = cc.replay.entry_positions[br->op_idx];
        const auto& instr = cc.prog.instrs[br->op_idx];
        if (auto* op = std::get_if<lkr::And>(&instr)) {
            TRY_ASSIGN(left_cp,  walk_recursive(cc, *br->left));
            TRY_ASSIGN(right_cp, walk_recursive(cc, *br->right));
            return rule_and(cc, *op, std::move(left_cp),
                             std::move(right_cp), seq, posv);
        }
        if (std::holds_alternative<lkr::Cut>(instr)) {
            TRY_ASSIGN(left_cp,  walk_recursive(cc, *br->left));
            TRY_ASSIGN(right_cp, walk_recursive(cc, *br->right));
            // The Cut's LEFT subgoal has θ as its last entry. Use the
            // FIRST op-position inside the LEFT subtree to read the
            // post-Cut sequent's positions for the cut entry.
            // Simpler: look at the LEFT child's first op's positions[last_entry].
            // We need theta_positions and neg_theta_positions. The Cut
            // appended them to the child subgoals' positions vectors.
            // Recover them from the LEFT child's first op snapshot.
            uint32_t left_first_op = static_cast<uint32_t>(-1);
            if (auto* l = std::get_if<LeafNode>(&br->left->node))
                left_first_op = l->op_idx;
            else if (auto* l = std::get_if<LinearNode>(&br->left->node))
                left_first_op = l->op_idx;
            else if (auto* l = std::get_if<BranchingNode>(&br->left->node))
                left_first_op = l->op_idx;
            if (left_first_op == static_cast<uint32_t>(-1)) {
                return MAKE_ERROR
                    << "walk(Cut): LEFT subtree first op not located";
            }
            const auto& left_first_posv =
                cc.replay.entry_positions[left_first_op];
            if (left_first_posv.empty()) {
                return MAKE_ERROR
                    << "walk(Cut): LEFT subgoal has no entries";
            }
            const std::vector<size_t>& theta_positions =
                left_first_posv.back();

            uint32_t right_first_op = static_cast<uint32_t>(-1);
            if (auto* r = std::get_if<LeafNode>(&br->right->node))
                right_first_op = r->op_idx;
            else if (auto* r = std::get_if<LinearNode>(&br->right->node))
                right_first_op = r->op_idx;
            else if (auto* r = std::get_if<BranchingNode>(&br->right->node))
                right_first_op = r->op_idx;
            if (right_first_op == static_cast<uint32_t>(-1)) {
                return MAKE_ERROR
                    << "walk(Cut): RIGHT subtree first op not located";
            }
            const auto& right_first_posv =
                cc.replay.entry_positions[right_first_op];
            if (right_first_posv.empty()) {
                return MAKE_ERROR
                    << "walk(Cut): RIGHT subgoal has no entries";
            }
            const std::vector<size_t>& neg_theta_positions =
                right_first_posv.back();

            (void)seq;
            (void)posv;
            return rule_cut(cc, std::move(left_cp), std::move(right_cp),
                             theta_positions, neg_theta_positions);
        }
        return MAKE_ERROR
            << "walk(Branching): op variant " << instr.index()
            << " not yet supported";
    }

    return MAKE_ERROR << "walk: unreachable tree node variant";
}

}  // namespace

}  // namespace logic::proof::translate::lkr_to_comb
