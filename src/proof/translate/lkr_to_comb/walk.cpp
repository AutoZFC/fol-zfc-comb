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
// CloseByLemma — Strategy B leaf builder.
//
// The lemma's CombProof is a proof of φ_L (NNF). It was built against
// G(φ_L) as its target with its own vertex numbering [0, |φ_L|). To
// paste it into our LEFT subgoal:
//   - target = our shared canonical target
//   - source = lemma's source (with possibly remapped dualizer eigens)
//   - fibration[v] = lemma_target_positions[lemma.fibration[v]]
//
// `lemma_target_positions` = entry_positions.back() = canonical
// positions of the LEFT subgoal's LAST entry (= φ_L), which is the cut
// formula introduced by the preceding Cut(φ_L). The lemma's vertex k
// (at lemma.target position k) maps to canonical position
// lemma_target_positions[k].
//
// Note on dualizer: the lemma's dualizer maps lemma's eigen-vars (which
// correspond to binder vertices in lemma.target) to terms. After
// pasting, those eigens should be remapped to the canonical target's
// binder vars at the corresponding positions. For lemmas without
// quantifiers (empty dualizer), no remap is needed — the common case.
util::Result<comb::CombProof> build_leaf_close_by_lemma(
    WalkContext&                                 cc,
    const lkr::CloseByLemma&                     op,
    const std::vector<std::vector<size_t>>&      entry_positions)
{
    auto it = cc.lemmas.find(op.axiom.name);
    if (it == cc.lemmas.end()) {
        return MAKE_ERROR
            << "close_by_lemma: lemma '" << op.axiom.name
            << "' not in registry";
    }
    const comb::CombProof& lemma_cp = it->second;
    if (entry_positions.empty()) {
        return MAKE_ERROR << "close_by_lemma: empty sequent";
    }
    // Strategy B precondition: the cut formula (φ_L) is the last entry
    // of the LEFT subgoal. Its canonical positions are
    // entry_positions.back().
    const auto& lemma_target_positions = entry_positions.back();
    if (lemma_cp.target.labels.size() != lemma_target_positions.size()) {
        return MAKE_ERROR
            << "close_by_lemma: lemma '" << op.axiom.name
            << "' vertex count (" << lemma_cp.target.labels.size()
            << ") doesn't match cut formula positions ("
            << lemma_target_positions.size() << ")";
    }

    // Dualizer remap support: for now require empty (no quantifiers in
    // lemma); a non-empty dualizer would need eigen-var translation
    // (lemma's eigen → canonical target's binder var at the same
    // position-remapped vertex).
    if (!lemma_cp.source.dualizer.empty()) {
        return MAKE_ERROR
            << "close_by_lemma: lemma '" << op.axiom.name
            << "' has a non-empty dualizer; eigen-var remap not yet "
            << "implemented (first-cut limitation)";
    }

    comb::CombProof cp;
    cp.target = cc.canonical_target;
    cp.source = lemma_cp.source;  // same shape, no eigen remap needed
    cp.fibration.reserve(lemma_cp.fibration.size());
    for (size_t fib : lemma_cp.fibration) {
        if (fib >= lemma_target_positions.size()) {
            return MAKE_ERROR
                << "close_by_lemma: lemma fibration position " << fib
                << " out of remap range";
        }
        cp.fibration.push_back(lemma_target_positions[fib]);
    }

    // Propagate the lemma's dependency-tracking last_used through.
    cp.last_used = lemma_cp.last_used;
    cp.last_used.insert(op.axiom.name);
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
// And — fusion of two combinatorial proofs (paper §11.1 ∧ case).
// =====================================================================

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
// Cut — per Hughes §15: identical to the And rule's fusion, but the
// "principal" entry doesn't exist in the pre-Cut sequent; the Cut adds
// θ to LEFT and ¬θ to RIGHT, and the augmented goal includes (θ ∧ ¬θ)
// as a new disjunct. The cut formula's positions are pre-computed by
// cut_augment.
// =====================================================================

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
// Forall — add a universal binder vertex (Case B) or pass through (Case A).
// =====================================================================

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
// Exists — add an existential binder vertex with cograph (×) edges to
// the witness portion. Extend dualizer with δ(x) = witness term.
// =====================================================================

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
// Source binding-edge derivation (Hughes Def. 3.1, applied to fonet).
//
// In a fograph — and hence in a fonet, which is a linked fograph — the
// binding edges aren't free parameters: they're DERIVED from labels.
// Concretely, for each binder vertex b with var v and each atom vertex
// a whose args contain Fixed(v), the pair (b, a) is a binding edge.
//
// Fograph builds the target's binding edges this way in
// fograph.cpp::add_binding_edges. The source must follow the same
// recipe — anything else risks producing fonets whose binding edges
// fail the verifier's unique-lift fibration check against the target.
//
// We compute source labels via fibration (source_label(v) =
// target.labels[fibration[v]]), then run the same per-vertex scan.
// Any binding edges accumulated by per-rule code earlier in walk are
// discarded; this is the single source of truth.
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
            // Or/Exchange: cograph associativity/commutativity → fonet
            // and fibration unchanged. Target is the shared canonical
            // target; no need to mutate.
            // Weakening: new vertices are uncovered; canonical target
            // already includes them at the goal-canonical position if
            // the weakened entry survives to the goal. (For Weakening
            // ops that introduce entries with empty position vectors —
            // i.e., truly new positions outside the canonical target —
            // proper target augmentation is phase-7 work.)
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
