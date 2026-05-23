#include "walk.h"

#include "build_target.h"

#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// =====================================================================
// Vertex counting (must match Fograph's pre-order layout).
// =====================================================================

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
// WalkResult — per-subtree return value.
// =====================================================================
//
// Each walk_recursive call returns a triple (source, target,
// fibration) per Hughes §11.1, plus bookkeeping needed by per-rule
// operations:
//
//   - entry_positions[k] = vertex positions in `target` for the k-th
//     main sequent entry (matches sequent_before[op_idx]).
//   - cut_summands accumulates the (θ ∧ ¬θ) formulas added by Cut
//     nodes in this subtree, in op-stream order. They sit AFTER the
//     main entries in `target`.
//   - cut_summand_positions[k] mirrors entry_positions for cut_summands.

struct WalkResult {
    comb::Fonet                source;
    comb::Fograph              target;
    std::vector<size_t>        fibration;
    std::vector<std::vector<size_t>> entry_positions;
    std::vector<FormulaHandle>       cut_summands;
    std::vector<std::vector<size_t>> cut_summand_positions;
};

// =====================================================================
// Binder-var renumbering — keep per-hypothesis target vars in a
// walk-global fresh range so they never collide with LKR Forall
// eigens (which appear as witness terms in dualizer values).
// =====================================================================

var_index renumber_binders(comb::Fograph& f, var_index offset) {
    std::unordered_map<var_index, var_index> map;
    for (auto& lbl : f.labels) {
        if (lbl.kind == comb::VertexKind::Binder) {
            map[lbl.var] = offset;
            lbl.var = offset++;
        }
    }
    for (auto& lbl : f.labels) {
        if (lbl.kind != comb::VertexKind::Atom) continue;
        for (auto& t : lbl.args) {
            if (t.is_fixed()) {
                auto it = map.find(t.as_variable());
                if (it != map.end()) t = Term::fixed(it->second);
            }
        }
    }
    return offset;
}

util::Result<SequentTarget> build_target(
    WalkContext& cc,
    const std::vector<FormulaHandle>& entries)
{
    TRY_ASSIGN(st, build_sequent_target(cc.builder, entries));
    cc.next_target_var = renumber_binders(st.target, cc.next_target_var);
    return st;
}

// =====================================================================
// Lifting source through a rule's z embedding.
//
// For each rule going bottom-up, the source vertices keep their
// identity but their fibration shifts from child target positions to
// parent target positions. As a consequence, source labels (derived
// via fibration from target) change — binder vars and atom args use
// parent target's var allocation. The dualizer's keys and Fixed
// values must be remapped to match.
// =====================================================================

std::unordered_map<var_index, var_index> lift_fibration(
    std::vector<size_t>&       fibration,
    const std::vector<size_t>& z,
    const comb::Fograph&       child_target,
    const comb::Fograph&       parent_target)
{
    std::unordered_map<var_index, var_index> var_remap;
    for (size_t u = 0; u < fibration.size(); ++u) {
        size_t old_pos = fibration[u];
        size_t new_pos = z[old_pos];
        fibration[u] = new_pos;
        const auto& old_lbl = child_target.labels[old_pos];
        const auto& new_lbl = parent_target.labels[new_pos];
        if (old_lbl.kind == comb::VertexKind::Binder &&
            new_lbl.kind == comb::VertexKind::Binder)
        {
            var_remap[old_lbl.var] = new_lbl.var;
        }
    }
    return var_remap;
}

void apply_var_remap_to_dualizer(
    comb::Fonet&                                            source,
    const std::unordered_map<var_index, var_index>&         var_remap)
{
    if (var_remap.empty()) return;
    auto remap_var = [&](var_index v) {
        auto it = var_remap.find(v);
        return it == var_remap.end() ? v : it->second;
    };
    std::unordered_map<var_index, Term> new_d;
    new_d.reserve(source.dualizer.size());
    for (const auto& [k, t] : source.dualizer) {
        Term new_t = t;
        if (t.is_fixed()) new_t = Term::fixed(remap_var(t.as_variable()));
        new_d.emplace(remap_var(k), new_t);
    }
    source.dualizer = std::move(new_d);
}

// =====================================================================
// Build z : child target positions → parent target positions.
//
// `entry_map`: for each child main entry index k, where it lands in
// parent — entry_map[k] = {parent_entry_idx, offset, is_summand}
// meaning child's k-th entry occupies parent_target's
// entry_positions[parent_entry_idx][offset..offset+|entry|].
//
// `cut_summand_map`: same for child's cut summands; map to parent's
// cut summands (typically identity-with-offset for sub-trees, or
// disjoint-union for branching).
// =====================================================================

struct ZEntryTarget {
    bool   is_dropped;    // true → this child entry has no parent counterpart (Weakening's scaffolding entry)
    bool   is_summand;    // false → parent main entry, true → parent cut summand
    size_t parent_idx;    // which parent entry / cut summand
    size_t offset;        // offset within parent entry/summand vertex range
};

std::vector<size_t> build_z(
    const std::vector<std::vector<size_t>>& child_entry_positions,
    const std::vector<std::vector<size_t>>& child_summand_positions,
    const std::vector<std::vector<size_t>>& parent_entry_positions,
    const std::vector<std::vector<size_t>>& parent_summand_positions,
    const std::vector<ZEntryTarget>&        entry_map,
    const std::vector<ZEntryTarget>&        summand_map,
    size_t                                  target_size)
{
    std::vector<size_t> z(target_size, static_cast<size_t>(-1));
    auto bind = [&](const std::vector<size_t>& child_pos,
                    const ZEntryTarget&         tgt) {
        if (tgt.is_dropped) return;
        const auto& parent_pos = tgt.is_summand
            ? parent_summand_positions[tgt.parent_idx]
            : parent_entry_positions[tgt.parent_idx];
        for (size_t i = 0; i < child_pos.size(); ++i) {
            z[child_pos[i]] = parent_pos[tgt.offset + i];
        }
    };
    for (size_t k = 0; k < child_entry_positions.size(); ++k) {
        bind(child_entry_positions[k], entry_map[k]);
    }
    for (size_t k = 0; k < child_summand_positions.size(); ++k) {
        bind(child_summand_positions[k], summand_map[k]);
    }
    return z;
}

// Apply `z` to fibration and remap dualizer.
void lift_source(
    WalkResult&                child,
    const std::vector<size_t>& z,
    const comb::Fograph&       parent_target)
{
    auto var_remap = lift_fibration(child.fibration, z,
                                    child.target, parent_target);
    apply_var_remap_to_dualizer(child.source, var_remap);
}

// =====================================================================
// Disjoint-union fusion of two sources (used by And and Cut).
//
// Both children's fibrations must already be lifted into parent_target
// before calling. P_L / P_R are the witness portions (vertex indices in
// each child's source). When add_cross_edges is true, an edge is added
// for every (l ∈ P_L, r ∈ P_R) — Hughes Def. 10.4 fusion at portions.
// =====================================================================

void fuse_disjoint(
    WalkResult&                fused_out,
    WalkResult&&               left,
    WalkResult&&               right,
    const std::vector<size_t>& P_L,
    const std::vector<size_t>& P_R,
    bool                       add_cross_edges)
{
    const size_t n_L = left.source.num_vertex;
    const size_t n_R = right.source.num_vertex;

    auto& src = fused_out.source;
    src.num_vertex = n_L + n_R;

    src.cograph_edges = std::move(left.source.cograph_edges);
    for (auto e : right.source.cograph_edges) {
        src.cograph_edges.push_back({e.first + n_L, e.second + n_L});
    }
    if (add_cross_edges) {
        for (size_t l : P_L) {
            for (size_t r : P_R) {
                src.cograph_edges.push_back({l, r + n_L});
            }
        }
    }

    src.binding_edges = std::move(left.source.binding_edges);
    for (auto e : right.source.binding_edges) {
        src.binding_edges.push_back({e.first + n_L, e.second + n_L});
    }

    src.links = std::move(left.source.links);
    for (auto l : right.source.links) {
        src.links.push_back({l.first + n_L, l.second + n_L});
    }

    src.dualizer = std::move(left.source.dualizer);
    for (auto& [k, t] : right.source.dualizer) {
        // Conflict means the same existential binder var appears in
        // both subtrees with different witnesses — that's a translator
        // bug. Keep the LEFT entry; verifier will catch any divergence.
        src.dualizer.emplace(k, std::move(t));
    }

    fused_out.fibration = std::move(left.fibration);
    fused_out.fibration.insert(fused_out.fibration.end(),
                               right.fibration.begin(),
                               right.fibration.end());
}

// =====================================================================
// Source binding-edge derivation (Hughes Def. 3.1, post-pass).
//
// In a fograph — and hence in a fonet — binding edges are NOT free
// parameters: they are DERIVED from labels. For each binder vertex b
// with var v and each atom vertex a whose args contain Fixed(v),
// (b, a) is a binding edge. Fograph builds the target's binding edges
// this way; the source must too, or the unique-lift fibration check
// rejects.
//
// Implementation: source labels are looked up via fibration. Any
// binding edges accumulated by per-rule code are discarded; this
// post-pass is the single source of truth.
// =====================================================================

void derive_binding_edges(comb::Fonet& source,
                          const std::vector<size_t>& fibration,
                          const comb::Fograph& target) {
    source.binding_edges.clear();
    const size_t n = source.num_vertex;
    for (size_t b = 0; b < n; ++b) {
        const comb::VertexLabel& b_lbl = target.labels[fibration[b]];
        if (b_lbl.kind != comb::VertexKind::Binder) continue;
        var_index v = b_lbl.var;
        for (size_t a = 0; a < n; ++a) {
            if (a == b) continue;
            const comb::VertexLabel& a_lbl = target.labels[fibration[a]];
            if (a_lbl.kind != comb::VertexKind::Atom) continue;
            for (const Term& arg : a_lbl.args) {
                if (arg.is_fixed() && arg.as_variable() == v) {
                    source.binding_edges.push_back({b, a});
                    break;
                }
            }
        }
    }
}

// =====================================================================
// Per-rule operations.
// =====================================================================

util::Result<WalkResult> rule_axiom_lit(
    WalkContext&                            cc,
    const lkr::AxiomLit&                    op,
    const std::vector<FormulaHandle>&       sequent)
{
    if (op.lit_a == op.lit_b) {
        return MAKE_ERROR
            << "walk(AxiomLit): lit_a == lit_b (" << op.lit_a << ")";
    }
    if (op.lit_a >= sequent.size() || op.lit_b >= sequent.size()) {
        return MAKE_ERROR << "walk(AxiomLit): lit OOR";
    }

    TRY_ASSIGN(st, build_target(cc, sequent));
    if (st.entry_positions[op.lit_a].size() != 1 ||
        st.entry_positions[op.lit_b].size() != 1) {
        return MAKE_ERROR
            << "walk(AxiomLit): entries are not atomic (lit_a has "
            << st.entry_positions[op.lit_a].size() << " positions, lit_b has "
            << st.entry_positions[op.lit_b].size() << ")";
    }

    WalkResult res;
    res.target          = std::move(st.target);
    res.entry_positions = std::move(st.entry_positions);
    res.source.num_vertex = 2;
    res.source.links.push_back({0, 1});
    res.fibration = { res.entry_positions[op.lit_a][0],
                      res.entry_positions[op.lit_b][0] };
    return res;
}

util::Result<WalkResult> rule_one(
    WalkContext&                            cc,
    const lkr::One&                         op,
    const std::vector<FormulaHandle>&       sequent)
{
    if (op.idx >= sequent.size()) {
        return MAKE_ERROR << "walk(One): idx OOR";
    }
    TRY_ASSIGN(st, build_target(cc, sequent));
    if (st.entry_positions[op.idx].size() != 1) {
        return MAKE_ERROR
            << "walk(One): entry at idx=" << op.idx << " has "
            << st.entry_positions[op.idx].size()
            << " canonical positions (expected 1 for ¬⊥)";
    }
    WalkResult res;
    res.target          = std::move(st.target);
    res.entry_positions = std::move(st.entry_positions);
    res.source.num_vertex = 1;
    res.fibration = { res.entry_positions[op.idx][0] };
    return res;
}

util::Result<WalkResult> rule_close_by_lemma(
    WalkContext&,
    const lkr::CloseByLemma& op)
{
    // Diagnostic only: dispatch on the variant to emit a useful identifier.
    std::string ident = std::visit([](const auto& t) -> std::string {
        using T = std::decay_t<decltype(t)>;
        if constexpr (std::is_same_v<T, AxiomRef>) {
            return "<axiom SentenceHandle>";       // ctx-less here; identity is the handle
        } else {
            return std::string("schema '") + t.schema.schema->name + "'";
        }
    }, op.target);
    return MAKE_ERROR
        << "walk(CloseByLemma): op for " << ident
        << " reached the walk; lemma_inliner pre-pass should have "
        << "spliced it (Strategy A, §4.12). Likely cause: lemma not "
        << "in the registry, or pipeline ordering bug.";
}

// Build the parent target for a linear rule and the trivial entry/summand
// maps assuming the child's main entries and cut_summands map 1:1 (modulo
// principal-entry rewriting that the caller handles separately).
//
// `entry_map` and `summand_map` are populated by the caller for the
// non-trivial cases; this helper just assembles parent's effective
// entries (= parent_main_entries ∪ child.cut_summands).
util::Result<SequentTarget> build_parent_target_with_summands(
    WalkContext& cc,
    const std::vector<FormulaHandle>& parent_main_entries,
    const std::vector<FormulaHandle>& cut_summands)
{
    std::vector<FormulaHandle> all = parent_main_entries;
    all.insert(all.end(), cut_summands.begin(), cut_summands.end());
    return build_target(cc, all);
}

// Split a SequentTarget that was built with main_entries followed by
// cut_summands back into the two halves.
void split_target_positions(
    SequentTarget&                           st,
    size_t                                   main_count,
    std::vector<std::vector<size_t>>&        out_main_pos,
    std::vector<std::vector<size_t>>&        out_summand_pos)
{
    out_main_pos.assign(st.entry_positions.begin(),
                        st.entry_positions.begin() + main_count);
    out_summand_pos.assign(st.entry_positions.begin() + main_count,
                           st.entry_positions.end());
}

// Trivial entry map for "child entry k → parent entry k, no offset".
ZEntryTarget identity_map(size_t k) {
    return ZEntryTarget{ /*is_dropped=*/false, /*is_summand=*/false,
                         /*parent_idx=*/k, /*offset=*/0 };
}
ZEntryTarget summand_map(size_t k) {
    return ZEntryTarget{ /*is_dropped=*/false, /*is_summand=*/true,
                         /*parent_idx=*/k, /*offset=*/0 };
}
ZEntryTarget dropped_map() {
    return ZEntryTarget{ /*is_dropped=*/true, /*is_summand=*/false,
                         /*parent_idx=*/0, /*offset=*/0 };
}

// Helper: build cut_summand maps as identity (child summand k → parent
// summand k). Used by all rules that don't introduce new cuts.
std::vector<ZEntryTarget> summands_identity(size_t n) {
    std::vector<ZEntryTarget> r;
    r.reserve(n);
    for (size_t i = 0; i < n; ++i) r.push_back(summand_map(i));
    return r;
}

util::Result<WalkResult> rule_or(
    WalkContext&                            cc,
    const lkr::Or&                          op,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Hypothesis H = Γ, ϕ, θ (LKR's Or replaces principal with ϕ and
    // appends θ). Conclusion C = Γ, (ϕ ∨ θ).
    if (op.principal >= parent_seq.size()) {
        return MAKE_ERROR << "rule_or: principal OOR";
    }
    const Formula& cf = parent_seq[op.principal].get();
    if (!cf.is_compound() || cf.as_compound().op != Op::Or) {
        return MAKE_ERROR << "rule_or: principal entry is not ∨";
    }
    FormulaHandle phi = cf.as_compound().left;
    size_t phi_count = count_fograph_vertices(phi);

    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // Child main entries: parent_seq with op.principal → phi, plus
    // theta appended at the end. So child index k:
    //   if k < parent_seq.size and k != op.principal: maps to parent k.
    //   if k == op.principal: maps to parent op.principal, offset 0
    //     (taking first phi_count positions).
    //   if k == parent_seq.size (= theta entry): maps to parent
    //     op.principal, offset phi_count.
    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size() + 1);
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        if (k == op.principal) {
            entry_map.push_back(ZEntryTarget{ false, false, op.principal, 0 });
        } else {
            entry_map.push_back(identity_map(k));
        }
    }
    entry_map.push_back(ZEntryTarget{ false, false, op.principal, phi_count });

    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());

    lift_source(child, z, st.target);

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);
    return res;
}

util::Result<WalkResult> rule_exchange(
    WalkContext&                            cc,
    const lkr::Exchange&                    op,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Conclusion C = Γ with entries[i] and entries[j] swapped relative
    // to child's H. Build parent target with parent_seq (= child's
    // entries with i, j swapped, viewed bottom-up).
    if (op.i >= parent_seq.size() || op.j >= parent_seq.size()) {
        return MAKE_ERROR << "rule_exchange: index OOR";
    }
    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // Child's entries are parent_seq with op.i, op.j swapped.
    // Child entry k → parent entry: if k==i then j, if k==j then i, else k.
    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size());
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        size_t pk = k;
        if (k == op.i) pk = op.j;
        else if (k == op.j) pk = op.i;
        entry_map.push_back(identity_map(pk));
    }
    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());
    lift_source(child, z, st.target);

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);
    return res;
}

util::Result<WalkResult> rule_weakening(
    WalkContext&                            cc,
    const lkr::Weakening& /*op*/,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // LKR Weakening (going top-down): top-of-stack Γ → Γ ∪ {ϕ}.
    // Going bottom-up, child has parent_seq + [ϕ] entries; the
    // ϕ entry is "scaffolding" and per I-2 InputGate invariant has
    // no source vertices mapped to it, so we drop it.
    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size() + 1);
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        entry_map.push_back(identity_map(k));
    }
    entry_map.push_back(dropped_map());

    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());
    // I-2 invariant: no source vertex maps to the weakened-in entry.
    // If any did, z[fib[v]] would still be the sentinel (size_t)-1.
    for (size_t v = 0; v < child.fibration.size(); ++v) {
        if (z[child.fibration[v]] == static_cast<size_t>(-1)) {
            return MAKE_ERROR
                << "rule_weakening: source vertex " << v
                << " maps to weakened-in entry (I-2 violation slipped past gate)";
        }
    }
    lift_source(child, z, st.target);

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);
    return res;
}

util::Result<WalkResult> rule_contraction(
    WalkContext&                            cc,
    const lkr::Contraction&                 op,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Hypothesis: child's entries are parent_seq with entries[op.i]
    // duplicated at op.j. Conclusion: parent_seq (drops the dup).
    if (op.i >= parent_seq.size()) {
        return MAKE_ERROR << "rule_contraction: i OOR";
    }
    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // Child has parent_seq + one duplicate of entries[i] inserted at
    // position j. The duplicate maps to parent entry op.i too.
    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size() + 1);
    // The LKR Contraction op records (i, j) where j is the index of the
    // duplicate-to-remove. Going bottom-up: child entry at position k
    // maps to parent entry at:
    //   if k < op.j: k (unchanged)
    //   if k == op.j: op.i (the dup mapped to the kept entry)
    //   if k > op.j: k - 1 (shift)
    for (size_t k = 0; k < parent_seq.size() + 1; ++k) {
        size_t pk;
        if (k < op.j) pk = k;
        else if (k == op.j) pk = op.i;
        else pk = k - 1;
        entry_map.push_back(identity_map(pk));
    }
    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());
    lift_source(child, z, st.target);

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);
    return res;
}

util::Result<WalkResult> rule_forall(
    WalkContext&                            cc,
    const lkr::Forall&                      op,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Hypothesis H = Γ, ϕ[x↦Fixed(eigen)]. Conclusion C = Γ, ∀x.ϕ.
    // G(C)'s principal entry has a Binder vertex first, then body
    // vertices. Child's principal entry has just the body (no binder).
    if (op.principal >= parent_seq.size()) {
        return MAKE_ERROR << "rule_forall: principal OOR";
    }
    const Formula& cf = parent_seq[op.principal].get();
    if (!cf.is_quantified() || cf.as_quantified().op != Op::Forall) {
        return MAKE_ERROR << "rule_forall: principal entry is not ∀";
    }

    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // Child entry k → parent entry k. For k == principal: child's
    // principal occupies the parent principal's body (offset 1 — skip
    // the binder vertex).
    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size());
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        if (k == op.principal) {
            entry_map.push_back(ZEntryTarget{ false, false, op.principal, 1 });
        } else {
            entry_map.push_back(identity_map(k));
        }
    }
    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());

    // After alpha_rename, op.eigen equals the canonical-target binder
    // var for this Forall's binder position. The walk's per-hypothesis
    // targets allocate binder vars in a higher range that doesn't
    // collide with eigens, so dualizer values (Fixed(eigen)) stay in
    // canonical-var space throughout the walk — no per-rule eigen
    // rename needed; only the source-binder var changes captured by
    // lift_fibration matter.
    lift_source(child, z, st.target);
    size_t binder_pos = parent_main_pos[op.principal][0];

    // Determine whether the principal body is "covered" by the child —
    // i.e., the preimage f^{-1}(V_{G(ϕ)}) is non-empty. If empty,
    // skip adding the binder vertex (Hughes Case A).
    std::unordered_set<size_t> body_pos(
        parent_main_pos[op.principal].begin() + 1,
        parent_main_pos[op.principal].end());
    bool covered = false;
    for (size_t v : child.fibration) {
        if (body_pos.count(v)) { covered = true; break; }
    }

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);

    if (covered) {
        size_t new_v = res.source.num_vertex;
        res.source.num_vertex = new_v + 1;
        res.fibration.push_back(binder_pos);
    }
    return res;
}

util::Result<WalkResult> rule_exists(
    WalkContext&                            cc,
    const lkr::Exists&                      op,
    WalkResult                              child,
    const std::vector<FormulaHandle>&       parent_seq)
{
    if (op.principal >= parent_seq.size()) {
        return MAKE_ERROR << "rule_exists: principal OOR";
    }
    const Formula& cf = parent_seq[op.principal].get();
    if (!cf.is_quantified() || cf.as_quantified().op != Op::Exists) {
        return MAKE_ERROR << "rule_exists: principal entry is not ∃";
    }

    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, child.cut_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    std::vector<ZEntryTarget> entry_map;
    entry_map.reserve(parent_seq.size());
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        if (k == op.principal) {
            entry_map.push_back(ZEntryTarget{ false, false, op.principal, 1 });
        } else {
            entry_map.push_back(identity_map(k));
        }
    }
    auto sum_map = summands_identity(child.cut_summands.size());
    auto z = build_z(child.entry_positions, child.cut_summand_positions,
                     parent_main_pos, parent_sum_pos,
                     entry_map, sum_map, child.target.labels.size());

    lift_source(child, z, st.target);

    size_t binder_pos = parent_main_pos[op.principal][0];
    std::unordered_set<size_t> body_pos(
        parent_main_pos[op.principal].begin() + 1,
        parent_main_pos[op.principal].end());
    std::vector<size_t> P;
    for (size_t v = 0; v < child.fibration.size(); ++v) {
        if (body_pos.count(child.fibration[v])) P.push_back(v);
    }

    WalkResult res;
    res.source                = std::move(child.source);
    res.fibration             = std::move(child.fibration);
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(child.cut_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);

    if (P.empty()) {
        // Case A: preimage empty.
        return res;
    }

    // Case B: add binder vertex with ×-edges to every vertex in P.
    size_t new_v = res.source.num_vertex;
    res.source.num_vertex = new_v + 1;
    res.fibration.push_back(binder_pos);
    for (size_t p : P) {
        res.source.cograph_edges.push_back({new_v, p});
    }

    // Add δ(parent_v) = witness. Witness comes from replay's term_env
    // by op.witness's TermRef. If the witness references an LKR eigen
    // (e.g., from a Forall above us in the tree), it will be remapped
    // when that Forall's rule_forall lift fires.
    if (op.witness.idx >= cc.replay.term_env.size() ||
        !cc.replay.term_env[op.witness.idx].has_value()) {
        return MAKE_ERROR
            << "rule_exists: witness TermRef #" << op.witness.idx
            << " unresolved";
    }
    Term witness = *cc.replay.term_env[op.witness.idx];
    var_index parent_v = res.target.labels[binder_pos].var;
    auto it = res.source.dualizer.find(parent_v);
    if (it == res.source.dualizer.end()) {
        res.source.dualizer.emplace(parent_v, witness);
    } else if (!(it->second == witness)) {
        return MAKE_ERROR
            << "rule_exists: dualizer conflict for var " << parent_v;
    }
    return res;
}

util::Result<WalkResult> rule_and(
    WalkContext&                            cc,
    const lkr::And&                         op,
    WalkResult                              left,
    WalkResult                              right,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Conclusion C = Γ_L ∪ Γ_R ∪ {ϕ_L ∧ ϕ_R}, where
    // Γ_L = parent_seq[k] for k ∈ sorted(op.left_partition),
    // Γ_R = parent_seq[k] for k ∉ left_partition ∪ {op.principal},
    // and the principal entry is parent_seq[op.principal] = ϕ_L ∧ ϕ_R.
    //
    // LEFT child's entries (per sequent_replay): sorted Γ_L entries
    //   followed by ϕ_L at the end.
    // RIGHT child's entries: Γ_R entries (in original order)
    //   followed by ϕ_R at the end.

    if (op.principal >= parent_seq.size()) {
        return MAKE_ERROR << "rule_and: principal OOR";
    }
    const Formula& cf = parent_seq[op.principal].get();
    if (!cf.is_compound() || cf.as_compound().op != Op::And) {
        return MAKE_ERROR << "rule_and: principal entry is not ∧";
    }
    FormulaHandle phi_L = cf.as_compound().left;
    size_t phi_L_count = count_fograph_vertices(phi_L);

    std::unordered_set<size_t> left_set(
        op.left_partition.begin(), op.left_partition.end());
    if (left_set.count(op.principal)) {
        return MAKE_ERROR << "rule_and: partition includes principal";
    }
    for (size_t k : op.left_partition) {
        if (k >= parent_seq.size()) {
            return MAKE_ERROR << "rule_and: partition OOR";
        }
    }
    std::vector<size_t> sorted_left(op.left_partition.begin(),
                                    op.left_partition.end());
    std::sort(sorted_left.begin(), sorted_left.end());
    std::vector<size_t> right_indices;
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        if (k == op.principal) continue;
        if (left_set.count(k)) continue;
        right_indices.push_back(k);
    }

    // Combined cut summands (LEFT's then RIGHT's in op-stream order).
    std::vector<FormulaHandle> combined_summands = left.cut_summands;
    combined_summands.insert(combined_summands.end(),
                             right.cut_summands.begin(),
                             right.cut_summands.end());

    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, combined_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // LEFT child entry map: for k = 0..sorted_left.size()-1, maps to
    // parent entry sorted_left[k]. For k = sorted_left.size() (the ϕ_L
    // entry), maps to parent op.principal, offset 0 (first phi_L_count
    // positions).
    std::vector<ZEntryTarget> left_entry_map;
    left_entry_map.reserve(sorted_left.size() + 1);
    for (size_t k = 0; k < sorted_left.size(); ++k) {
        left_entry_map.push_back(identity_map(sorted_left[k]));
    }
    left_entry_map.push_back(ZEntryTarget{ false, false, op.principal, 0 });

    // RIGHT child entry map: for k = 0..right_indices.size()-1, maps
    // to parent entry right_indices[k]. For k = right_indices.size()
    // (the ϕ_R entry), maps to parent op.principal, offset phi_L_count.
    std::vector<ZEntryTarget> right_entry_map;
    right_entry_map.reserve(right_indices.size() + 1);
    for (size_t k = 0; k < right_indices.size(); ++k) {
        right_entry_map.push_back(identity_map(right_indices[k]));
    }
    right_entry_map.push_back(ZEntryTarget{ false, false, op.principal, phi_L_count });

    // Summand maps: LEFT keeps its own summand indices; RIGHT shifts.
    std::vector<ZEntryTarget> left_sum_map  =
        summands_identity(left.cut_summands.size());
    std::vector<ZEntryTarget> right_sum_map;
    right_sum_map.reserve(right.cut_summands.size());
    for (size_t k = 0; k < right.cut_summands.size(); ++k) {
        right_sum_map.push_back(summand_map(k + left.cut_summands.size()));
    }

    auto z_L = build_z(left.entry_positions, left.cut_summand_positions,
                       parent_main_pos, parent_sum_pos,
                       left_entry_map, left_sum_map,
                       left.target.labels.size());
    auto z_R = build_z(right.entry_positions, right.cut_summand_positions,
                       parent_main_pos, parent_sum_pos,
                       right_entry_map, right_sum_map,
                       right.target.labels.size());

    lift_source(left, z_L, st.target);
    lift_source(right, z_R, st.target);

    // Witness portions: P_L = f_L^{-1}(V_{G(ϕ_L)});
    //                   P_R = f_R^{-1}(V_{G(ϕ_R)}).
    std::unordered_set<size_t> phi_L_canonical(
        parent_main_pos[op.principal].begin(),
        parent_main_pos[op.principal].begin() + phi_L_count);
    std::unordered_set<size_t> phi_R_canonical(
        parent_main_pos[op.principal].begin() + phi_L_count,
        parent_main_pos[op.principal].end());

    std::vector<size_t> P_L, P_R;
    for (size_t v = 0; v < left.fibration.size(); ++v) {
        if (phi_L_canonical.count(left.fibration[v])) P_L.push_back(v);
    }
    for (size_t v = 0; v < right.fibration.size(); ++v) {
        if (phi_R_canonical.count(right.fibration[v])) P_R.push_back(v);
    }

    bool left_strong  = !P_L.empty();
    bool right_strong = !P_R.empty();

    WalkResult res;
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(combined_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);

    if (left_strong && right_strong) {
        fuse_disjoint(res, std::move(left), std::move(right),
                       P_L, P_R, /*add_cross=*/true);
    } else if (left_strong && !right_strong) {
        // RIGHT is weak — keep RIGHT alone.
        res.source    = std::move(right.source);
        res.fibration = std::move(right.fibration);
    } else if (!left_strong && right_strong) {
        res.source    = std::move(left.source);
        res.fibration = std::move(left.fibration);
    } else {
        // Both weak — fuse without cross-edges.
        fuse_disjoint(res, std::move(left), std::move(right),
                       P_L, P_R, /*add_cross=*/false);
    }
    return res;
}

util::Result<WalkResult> rule_cut(
    WalkContext&                            cc,
    const lkr::Cut&                         op,
    WalkResult                              left,
    WalkResult                              right,
    const std::vector<FormulaHandle>&       parent_seq)
{
    // Cut(θ): LEFT premise's entries = parent_seq + [θ_nnf]
    //         RIGHT premise's entries = parent_seq + [¬θ_nnf]
    // Conclusion target adds the (θ ∧ ¬θ) augmentation as a new cut
    // summand on top of the merged LEFT+RIGHT cut summands.

    auto* h = std::get_if<FormulaHandle>(&op.cut_formula);
    if (!h || !h->valid()) {
        return MAKE_ERROR
            << "rule_cut: cut_formula is deferred AST (unsupported)";
    }
    FormulaHandle theta_nnf     = cc.builder.to_nnf(*h);
    FormulaHandle neg_theta_nnf = cc.builder.to_nnf_neg(*h);
    FormulaHandle theta_block   = cc.builder.make_and(theta_nnf, neg_theta_nnf);
    size_t theta_count     = count_fograph_vertices(theta_nnf);
    size_t neg_theta_count = count_fograph_vertices(neg_theta_nnf);

    // Combined summands in op-stream order: this (outer) cut's block
    // comes FIRST, then deeper LEFT-subtree summands, then deeper
    // RIGHT-subtree summands. This matches build_cut_augmentation's
    // linear op-order scan, which the root renormalization assumes.
    std::vector<FormulaHandle> combined_summands;
    combined_summands.reserve(1 + left.cut_summands.size() +
                              right.cut_summands.size());
    combined_summands.push_back(theta_block);
    combined_summands.insert(combined_summands.end(),
                             left.cut_summands.begin(),
                             left.cut_summands.end());
    combined_summands.insert(combined_summands.end(),
                             right.cut_summands.begin(),
                             right.cut_summands.end());

    TRY_ASSIGN(st, build_parent_target_with_summands(
        cc, parent_seq, combined_summands));
    std::vector<std::vector<size_t>> parent_main_pos, parent_sum_pos;
    split_target_positions(st, parent_seq.size(),
                           parent_main_pos, parent_sum_pos);

    // The new (θ ∧ ¬θ) summand is now at index 0 of parent_sum_pos.
    // Its vertex positions are split: first theta_count for θ, rest
    // for ¬θ.
    size_t new_summand_idx = 0;
    const auto& new_summand_pos = parent_sum_pos[new_summand_idx];
    if (new_summand_pos.size() != theta_count + neg_theta_count) {
        return MAKE_ERROR
            << "rule_cut: new summand position count mismatch";
    }

    // LEFT child entry map: parent_seq entries identity; child's last
    // entry (θ) maps to the new summand's first theta_count positions.
    std::vector<ZEntryTarget> left_entry_map;
    left_entry_map.reserve(parent_seq.size() + 1);
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        left_entry_map.push_back(identity_map(k));
    }
    left_entry_map.push_back(ZEntryTarget{
        /*is_dropped=*/false,
        /*is_summand=*/true,
        /*parent_idx=*/new_summand_idx,
        /*offset=*/0 });

    std::vector<ZEntryTarget> right_entry_map;
    right_entry_map.reserve(parent_seq.size() + 1);
    for (size_t k = 0; k < parent_seq.size(); ++k) {
        right_entry_map.push_back(identity_map(k));
    }
    right_entry_map.push_back(ZEntryTarget{
        /*is_dropped=*/false,
        /*is_summand=*/true,
        /*parent_idx=*/new_summand_idx,
        /*offset=*/theta_count });

    // Summand maps: LEFT's summands shift by 1 (this cut's block
    // is at index 0); RIGHT's shift by 1 + left.cut_summands.size().
    std::vector<ZEntryTarget> left_sum_map;
    left_sum_map.reserve(left.cut_summands.size());
    for (size_t k = 0; k < left.cut_summands.size(); ++k) {
        left_sum_map.push_back(summand_map(k + 1));
    }
    std::vector<ZEntryTarget> right_sum_map;
    right_sum_map.reserve(right.cut_summands.size());
    for (size_t k = 0; k < right.cut_summands.size(); ++k) {
        right_sum_map.push_back(summand_map(k + 1 + left.cut_summands.size()));
    }

    auto z_L = build_z(left.entry_positions, left.cut_summand_positions,
                       parent_main_pos, parent_sum_pos,
                       left_entry_map, left_sum_map,
                       left.target.labels.size());
    auto z_R = build_z(right.entry_positions, right.cut_summand_positions,
                       parent_main_pos, parent_sum_pos,
                       right_entry_map, right_sum_map,
                       right.target.labels.size());

    lift_source(left, z_L, st.target);
    lift_source(right, z_R, st.target);

    // Witness portions over the new summand's θ / ¬θ halves.
    std::unordered_set<size_t> theta_canonical(
        new_summand_pos.begin(), new_summand_pos.begin() + theta_count);
    std::unordered_set<size_t> neg_theta_canonical(
        new_summand_pos.begin() + theta_count, new_summand_pos.end());

    std::vector<size_t> P_L, P_R;
    for (size_t v = 0; v < left.fibration.size(); ++v) {
        if (theta_canonical.count(left.fibration[v])) P_L.push_back(v);
    }
    for (size_t v = 0; v < right.fibration.size(); ++v) {
        if (neg_theta_canonical.count(right.fibration[v])) P_R.push_back(v);
    }

    bool left_strong  = !P_L.empty();
    bool right_strong = !P_R.empty();

    WalkResult res;
    res.target                = std::move(st.target);
    res.entry_positions       = std::move(parent_main_pos);
    res.cut_summands          = std::move(combined_summands);
    res.cut_summand_positions = std::move(parent_sum_pos);

    if (left_strong && right_strong) {
        fuse_disjoint(res, std::move(left), std::move(right),
                       P_L, P_R, /*add_cross=*/true);
    } else if (left_strong && !right_strong) {
        res.source    = std::move(right.source);
        res.fibration = std::move(right.fibration);
    } else if (!left_strong && right_strong) {
        res.source    = std::move(left.source);
        res.fibration = std::move(left.fibration);
    } else {
        fuse_disjoint(res, std::move(left), std::move(right),
                       P_L, P_R, /*add_cross=*/false);
    }
    return res;
}

// =====================================================================
// Walk dispatch.
// =====================================================================

util::Result<WalkResult> walk_recursive(
    WalkContext&           cc,
    const DerivationTree&  tree);

util::Result<WalkResult> walk_leaf(
    WalkContext&     cc,
    const LeafNode&  leaf)
{
    const auto& seq   = cc.replay.sequent_before[leaf.op_idx];
    const auto& instr = cc.prog.instrs[leaf.op_idx];
    if (auto* ax = std::get_if<lkr::AxiomLit>(&instr)) {
        return rule_axiom_lit(cc, *ax, seq);
    }
    if (auto* one = std::get_if<lkr::One>(&instr)) {
        return rule_one(cc, *one, seq);
    }
    if (auto* cbl = std::get_if<lkr::CloseByLemma>(&instr)) {
        return rule_close_by_lemma(cc, *cbl);
    }
    return MAKE_ERROR
        << "walk(Leaf): op variant " << instr.index() << " unsupported";
}

util::Result<WalkResult> walk_linear(
    WalkContext&       cc,
    const LinearNode&  lin)
{
    TRY_ASSIGN(child, walk_recursive(cc, *lin.child));
    const auto& parent_seq = cc.replay.sequent_before[lin.op_idx];
    const auto& instr      = cc.prog.instrs[lin.op_idx];

    if (auto* op = std::get_if<lkr::Or>(&instr)) {
        return rule_or(cc, *op, std::move(child), parent_seq);
    }
    if (auto* op = std::get_if<lkr::Exchange>(&instr)) {
        return rule_exchange(cc, *op, std::move(child), parent_seq);
    }
    if (auto* op = std::get_if<lkr::Weakening>(&instr)) {
        return rule_weakening(cc, *op, std::move(child), parent_seq);
    }
    if (auto* op = std::get_if<lkr::Contraction>(&instr)) {
        return rule_contraction(cc, *op, std::move(child), parent_seq);
    }
    if (auto* op = std::get_if<lkr::Forall>(&instr)) {
        return rule_forall(cc, *op, std::move(child), parent_seq);
    }
    if (auto* op = std::get_if<lkr::Exists>(&instr)) {
        return rule_exists(cc, *op, std::move(child), parent_seq);
    }
    return MAKE_ERROR
        << "walk(Linear): op variant " << instr.index() << " unsupported";
}

util::Result<WalkResult> walk_branching(
    WalkContext&          cc,
    const BranchingNode&  br)
{
    TRY_ASSIGN(left,  walk_recursive(cc, *br.left));
    TRY_ASSIGN(right, walk_recursive(cc, *br.right));
    const auto& parent_seq = cc.replay.sequent_before[br.op_idx];
    const auto& instr      = cc.prog.instrs[br.op_idx];
    if (auto* op = std::get_if<lkr::And>(&instr)) {
        return rule_and(cc, *op, std::move(left), std::move(right),
                         parent_seq);
    }
    if (auto* op = std::get_if<lkr::Cut>(&instr)) {
        return rule_cut(cc, *op, std::move(left), std::move(right),
                         parent_seq);
    }
    return MAKE_ERROR
        << "walk(Branching): op variant " << instr.index() << " unsupported";
}

util::Result<WalkResult> walk_recursive(
    WalkContext&           cc,
    const DerivationTree&  tree)
{
    if (auto* leaf = std::get_if<LeafNode>(&tree.node)) {
        return walk_leaf(cc, *leaf);
    }
    if (auto* lin = std::get_if<LinearNode>(&tree.node)) {
        return walk_linear(cc, *lin);
    }
    if (auto* br = std::get_if<BranchingNode>(&tree.node)) {
        return walk_branching(cc, *br);
    }
    return MAKE_ERROR << "walk: unreachable tree node variant";
}

}  // namespace

util::Result<comb::CombProof> walk(
    WalkContext&           cc,
    const DerivationTree&  tree,
    FormulaHandle          augmented_goal_formula)
{
    TRY_ASSIGN(wr, walk_recursive(cc, tree));

    // Replace the root target with the canonical Fograph(NNF(augmented
    // goal)) so its binder vars start from 0 (matching what
    // CombVerifier rebuilds for structural comparison). The walk's
    // per-hypothesis targets use a fresh higher range to avoid
    // collisions with LKR eigens; we renormalize at the root boundary.
    //
    // The two fographs are structurally identical (same vertex count,
    // kinds, edges, positions) by construction — only binder var
    // labels and atom args differ. We rebuild a var_remap from the
    // walk's target vars to the canonical vars and apply it to the
    // source's dualizer.
    FormulaHandle augmented_nnf = cc.builder.to_nnf(augmented_goal_formula);
    comb::Fograph canonical_target(augmented_nnf);
    if (canonical_target.labels.size() != wr.target.labels.size()) {
        return MAKE_ERROR
            << "walk root: canonical target has " << canonical_target.labels.size()
            << " vertices, walk target has " << wr.target.labels.size();
    }
    std::unordered_map<var_index, var_index> root_remap;
    for (size_t i = 0; i < canonical_target.labels.size(); ++i) {
        const auto& w_lbl = wr.target.labels[i];
        const auto& c_lbl = canonical_target.labels[i];
        if (w_lbl.kind == comb::VertexKind::Binder &&
            c_lbl.kind == comb::VertexKind::Binder)
        {
            root_remap[w_lbl.var] = c_lbl.var;
        }
    }
    apply_var_remap_to_dualizer(wr.source, root_remap);
    wr.target = std::move(canonical_target);

    derive_binding_edges(wr.source, wr.fibration, wr.target);

    comb::CombProof cp;
    cp.source    = std::move(wr.source);
    cp.target    = std::move(wr.target);
    cp.fibration = std::move(wr.fibration);
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
