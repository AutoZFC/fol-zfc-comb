#include "src/proof/translate/lkr_to_comb/lkr_to_comb.h"

#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

// Hughes §11.1 LKR→comb fold over the cut-free `Deriv` tree. Each node returns
// a `WalkResult` = (fonet source, symbolic fibration, conclusion entries). The
// `std::visit` dispatch forces an arm for every Rule alternative, so the
// compiler checks exhaustiveness; rules outside the current phase reject.

namespace logic::proof::translate::lkr_to_comb {

namespace comb = logic::proof::comb;
namespace lce  = logic::proof::translate::lkr_cut_elim;

namespace {

// Pre-order vertex count of G(f), matching Fograph's layout (fograph.cpp):
// one vertex per atom / ¬atom / ¬⊥, ∧ and ∨ concatenate their operands' blocks,
// a quantifier contributes one binder vertex plus its body's block.
std::size_t count_vertices(FormulaHandle f) {
    const Formula& fm = f.get();
    if (fm.is_predicate()) return 1;
    if (fm.is_compound()) {
        const Compound& c = fm.as_compound();
        if (c.op == Op::Not) return 1;                 // ¬atom or ¬⊥
        if (c.op == Op::And || c.op == Op::Or)
            return count_vertices(c.left) + count_vertices(c.right);
        return 0;
    }
    if (fm.is_quantified()) return 1 + count_vertices(fm.as_quantified().body);
    return 0;
}

// A symbolic fibration target: vertex v maps to the `offset`-th vertex (in
// pre-order) of the `entry`-th sequent entry's fograph G(entries[entry]).
struct Fib { std::size_t entry{}; std::size_t offset{}; };

// One node's translation: the fonet built so far, the symbolic fibration of
// each of its vertices, and the conclusion sequent Γ this node derives.
//
// `source.dualizer` and `source.binding_edges` are left EMPTY during the fold:
// the fold runs in eigenvariable space, and all canonicalization is deferred to
// the root (where the target — hence canonical binder vars — is materialized).
// `forall_binders` / `ex_witness` carry the per-binder data needed there. Their
// vertex indices are local to this subtree, so `fuse` shifts the right child's.
struct WalkResult {
    comb::Fonet                source;     // num_vertex, cograph_edges, links
    std::vector<Fib>           fibration;  // length == source.num_vertex
    std::vector<FormulaHandle> entries;    // the conclusion sequent (= Γ)

    // (∀-eigenvar, its binder source-vertex): at the root, eigen renames to the
    // canonical var target.labels[fibration[vertex]].var (Forall Case B only).
    std::vector<std::pair<var_index, std::size_t>>  forall_binders;
    // (∃-binder source-vertex, witness term in eigenvar space): at the root the
    // dualizer gains key target.labels[fibration[vertex]].var ↦ renamed witness.
    std::vector<std::pair<std::size_t, Term>>       ex_witness;
};

util::Result<WalkResult> tr(FormulaBuilder& fb, const lce::Deriv& d);  // fwd

// How a child's entry maps into the parent: which parent entry it becomes and
// how far its vertex block is shifted within that parent entry's fograph.
struct EntryMap { std::size_t parent_entry{}; std::size_t offset_delta{}; };

// Remap a child's symbolic fibration into parent-entry space (m indexed by
// child entry). The fonet vertex set is unchanged — only the targets move.
std::vector<Fib> remap_fib(const std::vector<Fib>& fib,
                           const std::vector<EntryMap>& m) {
    std::vector<Fib> out;
    out.reserve(fib.size());
    for (const Fib& f : fib)
        out.push_back(Fib{m[f.entry].parent_entry, m[f.entry].offset_delta + f.offset});
    return out;
}

// Fuse two child fonets (§11.1 ∧-case / fuse_disjoint). Both fibrations are
// already in parent-entry space. Right's vertices shift by n_L; cograph/link
// edges, the fibration, and the per-binder records shift accordingly. When
// `add_cross`, add the ×-join cograph edges P_L × P_R between the witness
// portions (P_L left-local, P_R right-local vertex indices).
WalkResult fuse(WalkResult&& left, WalkResult&& right,
                const std::vector<std::size_t>& P_L,
                const std::vector<std::size_t>& P_R, bool add_cross) {
    const std::size_t n_L = left.source.num_vertex;
    WalkResult res;
    comb::Fonet& s = res.source;
    s.num_vertex = n_L + right.source.num_vertex;

    s.cograph_edges = std::move(left.source.cograph_edges);
    for (auto e : right.source.cograph_edges) s.cograph_edges.push_back({e.first + n_L, e.second + n_L});
    if (add_cross)
        for (std::size_t l : P_L)
            for (std::size_t r : P_R) s.cograph_edges.push_back({l, r + n_L});

    s.links = std::move(left.source.links);
    for (auto l : right.source.links) s.links.push_back({l.first + n_L, l.second + n_L});

    res.fibration = std::move(left.fibration);
    res.fibration.insert(res.fibration.end(), right.fibration.begin(), right.fibration.end());

    res.forall_binders = std::move(left.forall_binders);
    for (auto& [e, v] : right.forall_binders) res.forall_binders.emplace_back(e, v + n_L);
    res.ex_witness = std::move(left.ex_witness);
    for (auto& [v, t] : right.ex_witness) res.ex_witness.emplace_back(v + n_L, t);
    return res;
}

// ===== §11.1 per-rule operations ===========================================

// ax ⊢ Γ closing on the dual pair {a,b}: the fonet is the two linked atom
// vertices; every OTHER entry of Γ is uncovered (no source vertex fibrates to
// it — Hughes' weakening-in-the-axiom). f sends each vertex to offset 0 of its
// own entry block (a and b are whole atomic entries).
util::Result<WalkResult> macro(FormulaBuilder&, const lce::Deriv& d, const lce::RAx& ax) {
    if (ax.a == ax.b) return MAKE_ERROR << "lkr_to_comb: RAx a == b";
    if (ax.a >= d.conclusion.size() || ax.b >= d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RAx index OOR";
    if (count_vertices(d.conclusion[ax.a]) != 1 ||
        count_vertices(d.conclusion[ax.b]) != 1)
        return MAKE_ERROR << "lkr_to_comb: RAx entries are not atomic";

    WalkResult res;
    res.entries           = d.conclusion;
    res.source.num_vertex = 2;
    res.source.links.push_back({0, 1});
    res.fibration = {Fib{ax.a, 0}, Fib{ax.b, 0}};
    return res;
}

// ∨R: ⊢ Γ,φ,θ ⊢ Γ,φ∨θ. Cograph associativity — G(H) = G(C) identically, so the
// fonet and the per-vertex offsets are unchanged; only the entry bookkeeping
// merges φ (at `principal`) and θ (at the child's back) into the single entry
// φ∨θ at `principal`. θ's vertices shift into the merged block after φ's.
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::ROr& orr) {
    TRY_ASSIGN(child, tr(fb, *orr.child));
    const std::size_t pr   = orr.principal;
    const std::size_t back = child.entries.size() - 1;
    if (pr >= child.entries.size() || pr == back)
        return MAKE_ERROR << "lkr_to_comb: ROr principal OOR";

    FormulaHandle phi = child.entries[pr];
    FormulaHandle tht = child.entries[back];
    const std::size_t phi_n = count_vertices(phi);

    WalkResult res;
    res.source = std::move(child.source);
    res.entries = child.entries;
    res.entries[pr] = fb.make_or(phi, tht);
    res.entries.pop_back();                              // drop θ from the back

    res.fibration.reserve(child.fibration.size());
    for (const Fib& f : child.fibration) {
        if (f.entry == back)      res.fibration.push_back(Fib{pr, phi_n + f.offset});
        else                      res.fibration.push_back(f);   // pr keeps its offset
    }
    res.forall_binders = std::move(child.forall_binders);       // ∨ doesn't touch binders
    res.ex_witness     = std::move(child.ex_witness);
    return res;
}

// Exchange is free: entries are an order-free bag for (Γ). Reorder the two
// entries and remap fibration entry-indices; offsets are unchanged.
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv&, const lce::RExchange& ex) {
    TRY_ASSIGN(child, tr(fb, *ex.child));
    if (ex.i >= child.entries.size() || ex.j >= child.entries.size())
        return MAKE_ERROR << "lkr_to_comb: RExchange index OOR";
    std::swap(child.entries[ex.i], child.entries[ex.j]);
    for (Fib& f : child.fibration) {
        if (f.entry == ex.i)      f.entry = ex.j;
        else if (f.entry == ex.j) f.entry = ex.i;
    }
    return child;
}

// --- rules outside Phase 1 — reject cleanly (std::visit exhaustiveness) -----
util::Result<WalkResult> macro(FormulaBuilder&, const lce::Deriv&, const lce::ROne&) {
    return MAKE_ERROR << "lkr_to_comb: ROne not yet implemented";
}
util::Result<WalkResult> macro(FormulaBuilder&, const lce::Deriv&, const lce::RLemma&) {
    return MAKE_ERROR << "lkr_to_comb: RLemma must be internalized before translation";
}
// W: ⊢ Γ ⊢ Γ,φ. The child proves Γ (without φ); φ is weakened in at `idx` and
// left UNCOVERED (no source vertex fibrates to it — Hughes §11.1 W, Case A).
// Child entry k shifts to parent entry k (k<idx) or k+1 (k≥idx); the inserted
// entry has no preimage, so the fonet is unchanged.
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RWeaken& w) {
    TRY_ASSIGN(child, tr(fb, *w.child));
    if (w.idx > d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RWeaken idx OOR";
    std::vector<EntryMap> m(child.entries.size());
    for (std::size_t k = 0; k < child.entries.size(); ++k)
        m[k] = EntryMap{k < w.idx ? k : k + 1, 0};
    WalkResult res;
    res.source         = std::move(child.source);
    res.fibration      = remap_fib(child.fibration, m);
    res.forall_binders = std::move(child.forall_binders);   // W doesn't touch binders
    res.ex_witness     = std::move(child.ex_witness);
    res.entries        = d.conclusion;
    return res;
}
// Contraction: ⊢ Γ,φ,φ' ⊢ Γ,φ (RDuplicate's child has the copy φ' appended at the
// back; the conclusion drops it). G(C) = G(H) − G(φ'): the fibration FOLDS the φ'
// block onto φ's positions (child back entry → parent entry `src`, offset 0),
// becoming non-injective — exactly contraction (the skew fibration's many-to-one).
// Hughes §11.1 C-case. (Footnote-24 duplicator collapse for universal binders is
// deferred — added only if the corpus surfaces a binder-fibration rejection.)
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RDuplicate& dup) {
    TRY_ASSIGN(child, tr(fb, *dup.child));
    if (child.entries.size() != d.conclusion.size() + 1)
        return MAKE_ERROR << "lkr_to_comb: RDuplicate child arity mismatch";
    if (dup.src >= d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RDuplicate src OOR";
    const std::size_t back = child.entries.size() - 1;
    std::vector<EntryMap> m(child.entries.size());
    for (std::size_t k = 0; k < back; ++k) m[k] = EntryMap{k, 0};
    m[back] = EntryMap{dup.src, 0};                     // fold φ' onto φ

    WalkResult res;
    res.source         = std::move(child.source);
    res.fibration      = remap_fib(child.fibration, m);
    res.forall_binders = std::move(child.forall_binders);
    res.ex_witness     = std::move(child.ex_witness);
    res.entries        = d.conclusion;
    return res;
}
util::Result<WalkResult> macro(FormulaBuilder&, const lce::Deriv&, const lce::RContract&) {
    return MAKE_ERROR << "lkr_to_comb: RContract should be RDuplicate after build()";
}
// ∧R: ⊢ Γ_L,φ_L and ⊢ Γ_R,φ_R ⊢ Γ_L,Γ_R,(φ_L∧φ_R). Build the two child fonets,
// fuse at the witness portions (Hughes §11.1 ∧-case, design §4.9). G(C) has the
// principal entry's vertices = G(φ_L)++G(φ_R) (a × join → P_L×P_R cograph edges).
// Strong/weak: a side is strong iff its φ portion is covered (P≠∅). Both same →
// fuse (cross edges iff both strong); mixed → keep the weak side alone.
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RAnd& andr) {
    const std::size_t pr = andr.principal;
    if (pr >= d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RAnd principal OOR";
    const Formula& cf = d.conclusion[pr].get();
    if (!cf.is_compound() || cf.as_compound().op != Op::And)
        return MAKE_ERROR << "lkr_to_comb: RAnd principal is not ∧";
    const std::size_t phi_L_n = count_vertices(cf.as_compound().left);

    // Parent positions of the LEFT Γ entries (ascending) and the RIGHT Γ entries
    // (the non-left, non-principal entries, ascending) — build()'s convention.
    std::vector<bool> in_left(d.conclusion.size(), false);
    for (std::size_t k : andr.left_partition) {
        if (k >= d.conclusion.size() || k == pr)
            return MAKE_ERROR << "lkr_to_comb: RAnd partition OOR/principal";
        in_left[k] = true;
    }
    std::vector<std::size_t> sorted_left, right_idx;
    for (std::size_t k = 0; k < d.conclusion.size(); ++k) {
        if (k == pr) continue;
        (in_left[k] ? sorted_left : right_idx).push_back(k);
    }

    TRY_ASSIGN(left,  tr(fb, *andr.left));
    TRY_ASSIGN(right, tr(fb, *andr.right));
    if (left.entries.size() != sorted_left.size() + 1 ||
        right.entries.size() != right_idx.size() + 1)
        return MAKE_ERROR << "lkr_to_comb: RAnd child arity mismatch";

    // Witness portions: vertices fibrating to the child's last entry (φ_L / φ_R).
    const std::size_t llast = left.entries.size() - 1, rlast = right.entries.size() - 1;
    std::vector<std::size_t> P_L, P_R;
    for (std::size_t v = 0; v < left.fibration.size(); ++v)
        if (left.fibration[v].entry == llast) P_L.push_back(v);
    for (std::size_t v = 0; v < right.fibration.size(); ++v)
        if (right.fibration[v].entry == rlast) P_R.push_back(v);

    // Entry maps into parent space: Γ entries to their parent positions, the
    // principal's φ_L at offset 0 and φ_R at offset phi_L_n.
    std::vector<EntryMap> mL(left.entries.size()), mR(right.entries.size());
    for (std::size_t k = 0; k < sorted_left.size(); ++k) mL[k] = EntryMap{sorted_left[k], 0};
    mL[llast] = EntryMap{pr, 0};
    for (std::size_t k = 0; k < right_idx.size(); ++k) mR[k] = EntryMap{right_idx[k], 0};
    mR[rlast] = EntryMap{pr, phi_L_n};
    left.fibration  = remap_fib(left.fibration, mL);    // now in parent space
    right.fibration = remap_fib(right.fibration, mR);

    const bool strong_L = !P_L.empty(), strong_R = !P_R.empty();
    WalkResult res;
    if (strong_L == strong_R) {                          // both strong → cross edges
        res = fuse(std::move(left), std::move(right), P_L, P_R, /*add_cross=*/strong_L);
    } else if (strong_L) {                               // RIGHT weak → keep RIGHT
        res = std::move(right);
    } else {                                             // LEFT weak → keep LEFT
        res = std::move(left);
    }
    res.entries = d.conclusion;
    return res;
}
// ∀R: ⊢ Γ,φ[eigen] ⊢ Γ,∀x.φ. G(∀x.φ) = •x binder (offset 0) + G(φ) (offset 1+),
// the binder +-attached (NO cograph edges). Case B (φ-portion covered): add the
// binder source vertex and record (eigen, vertex) for root canonicalization;
// Case A (φ weakened, portion empty): binder uncovered, fonet unchanged. The
// child's principal entry (φ[eigen]) sits at the same index — shift it past the
// binder by offset_delta 1. (§4.7)
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RForall& far) {
    const std::size_t pr = far.principal;
    if (pr >= d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RForall principal OOR";
    const Formula& cf = d.conclusion[pr].get();
    if (!(cf.is_quantified() && cf.as_quantified().op == Op::Forall))
        return MAKE_ERROR << "lkr_to_comb: RForall principal is not ∀";
    TRY_ASSIGN(child, tr(fb, *far.child));

    std::vector<EntryMap> m(child.entries.size());
    for (std::size_t k = 0; k < child.entries.size(); ++k)
        m[k] = EntryMap{k, k == pr ? std::size_t{1} : std::size_t{0}};
    std::vector<std::size_t> P;
    for (std::size_t v = 0; v < child.fibration.size(); ++v)
        if (child.fibration[v].entry == pr) P.push_back(v);

    WalkResult res;
    res.source         = std::move(child.source);
    res.fibration      = remap_fib(child.fibration, m);
    res.forall_binders = std::move(child.forall_binders);
    res.ex_witness     = std::move(child.ex_witness);
    res.entries        = d.conclusion;
    if (!P.empty()) {                                   // Case B
        std::size_t b = res.source.num_vertex++;
        res.fibration.push_back(Fib{pr, 0});
        res.forall_binders.emplace_back(far.eigen, b);
    }
    return res;
}

// ∃R: ⊢ Γ,φ[x:=t] ⊢ Γ,∃x.φ. G(∃x.φ) = •x binder (offset 0) + G(φ) (offset 1+),
// the binder ×-attached to the body. Case B (witness portion covered): add the
// binder vertex with ×-cograph-edges to every body vertex, and record
// (vertex, t) so the root dualizer gains x ↦ t (witness in eigenvar space).
// Case A: body weakened, fonet unchanged. (§4.8)
util::Result<WalkResult> macro(FormulaBuilder& fb, const lce::Deriv& d, const lce::RExists& exr) {
    const std::size_t pr = exr.principal;
    if (pr >= d.conclusion.size())
        return MAKE_ERROR << "lkr_to_comb: RExists principal OOR";
    const Formula& cf = d.conclusion[pr].get();
    if (!(cf.is_quantified() && cf.as_quantified().op == Op::Exists))
        return MAKE_ERROR << "lkr_to_comb: RExists principal is not ∃";
    TRY_ASSIGN(child, tr(fb, *exr.child));

    std::vector<EntryMap> m(child.entries.size());
    for (std::size_t k = 0; k < child.entries.size(); ++k)
        m[k] = EntryMap{k, k == pr ? std::size_t{1} : std::size_t{0}};
    std::vector<std::size_t> P;
    for (std::size_t v = 0; v < child.fibration.size(); ++v)
        if (child.fibration[v].entry == pr) P.push_back(v);

    WalkResult res;
    res.source         = std::move(child.source);
    res.fibration      = remap_fib(child.fibration, m);
    res.forall_binders = std::move(child.forall_binders);
    res.ex_witness     = std::move(child.ex_witness);
    res.entries        = d.conclusion;
    if (!P.empty()) {                                   // Case B
        std::size_t b = res.source.num_vertex++;
        res.fibration.push_back(Fib{pr, 0});
        for (std::size_t p : P) res.source.cograph_edges.push_back({b, p});
        res.ex_witness.emplace_back(b, exr.witness);
    }
    return res;
}
util::Result<WalkResult> macro(FormulaBuilder&, const lce::Deriv&, const lce::RCut&) {
    return MAKE_ERROR << "lkr_to_comb: input is not cut-free (RCut present)";
}

util::Result<WalkResult> tr(FormulaBuilder& fb, const lce::Deriv& d) {
    return std::visit([&](const auto& rule) { return macro(fb, d, rule); }, d.rule);
}

// Source binding edges are DERIVED (Hughes Def. 3.1), not constructed per-rule:
// (b,a) iff source binder b's var (read from target via fibration) appears in
// source atom a's args. Same recipe as Fograph::add_binding_edges, on the source
// vertex set via the fibration. (design §7.5 Fix 2)
void derive_binding_edges(comb::Fonet& src, const std::vector<std::size_t>& fib,
                          const comb::Fograph& target) {
    src.binding_edges.clear();
    const std::size_t n = src.num_vertex;
    for (std::size_t b = 0; b < n; ++b) {
        const comb::VertexLabel& bl = target.labels[fib[b]];
        if (bl.kind != comb::VertexKind::Binder) continue;
        for (std::size_t a = 0; a < n; ++a) {
            if (a == b) continue;
            const comb::VertexLabel& al = target.labels[fib[a]];
            if (al.kind != comb::VertexKind::Atom) continue;
            for (const Term& arg : al.args)
                if (arg.is_fixed() && arg.as_variable() == bl.var) {
                    src.binding_edges.push_back({b, a});
                    break;
                }
        }
    }
}

}  // namespace

util::Result<comb::CombProof> lkr_to_comb(FormulaBuilder& fb, const lce::Deriv& cutfree) {
    if (cutfree.conclusion.size() != 1)
        return MAKE_ERROR << "lkr_to_comb: expected a single-formula (closed) goal "
                             "sequent, got " << cutfree.conclusion.size() << " formulas";
    FormulaHandle goal = cutfree.conclusion[0];

    TRY_ASSIGN(root, tr(fb, cutfree));

    // Materialize the symbolic fibration to absolute G(goal) vertex indices.
    // Block offset of entry k = Σ_{j<k} |G(entries[j])| (left-assoc ∨ layout).
    std::vector<std::size_t> block_off(root.entries.size(), 0);
    for (std::size_t k = 1; k < root.entries.size(); ++k)
        block_off[k] = block_off[k - 1] + count_vertices(root.entries[k - 1]);

    comb::CombProof cp;
    cp.target = comb::Fograph(goal);
    cp.source = std::move(root.source);
    cp.fibration.reserve(root.fibration.size());
    for (const Fib& f : root.fibration) {
        if (f.entry >= block_off.size())
            return MAKE_ERROR << "lkr_to_comb: fibration entry index OOR";
        std::size_t pos = block_off[f.entry] + f.offset;
        if (pos >= cp.target.labels.size())
            return MAKE_ERROR << "lkr_to_comb: fibration position OOR";
        cp.fibration.push_back(pos);
    }

    // Canonicalize binder vars: the fold ran in eigenvar space; the dualizer and
    // binding edges must be in the target's canonical-var space. Each ∀-eigenvar
    // renames to the canonical var at its binder vertex; each ∃ contributes a
    // dualizer entry (canonical var ↦ renamed witness).
    auto canon_var_at = [&](std::size_t v, var_index& out) -> util::ResultStatus {
        const comb::VertexLabel& lbl = cp.target.labels[cp.fibration[v]];
        if (lbl.kind != comb::VertexKind::Binder)
            return MAKE_ERROR << "lkr_to_comb: binder vertex maps to a non-binder target";
        out = lbl.var;
        return util::Ok();
    };
    std::unordered_map<var_index, var_index> rename;
    for (const auto& [eigen, v] : root.forall_binders) {
        var_index cv{};
        TRY(canon_var_at(v, cv));
        rename[eigen] = cv;
    }
    for (const auto& [v, witness] : root.ex_witness) {
        var_index key{};
        TRY(canon_var_at(v, key));
        Term val = witness;
        if (val.is_fixed()) {
            auto it = rename.find(val.as_variable());
            if (it != rename.end()) val = Term::fixed(it->second);
        }
        auto [it, inserted] = cp.source.dualizer.emplace(key, val);
        if (!inserted && !(it->second == val))
            return MAKE_ERROR << "lkr_to_comb: dualizer conflict for var " << key;
    }

    derive_binding_edges(cp.source, cp.fibration, cp.target);

    // Gated diagnostic: list each source binder vertex, its target var/polarity,
    // and whether it carries a dualizer entry. Surfaced the ROr/RWeaken record-drop
    // bugs (a source ∃-binder with no dualizer entry ⇒ a rule dropped its record).
    if (std::getenv("LKR_TO_COMB_DUMP")) {
        std::cerr << "[l2c dump] verts=" << cp.source.num_vertex
                  << " forall_binders=" << root.forall_binders.size()
                  << " ex_witness=" << root.ex_witness.size()
                  << " dualizer_keys=" << cp.source.dualizer.size() << "\n";
        for (std::size_t v = 0; v < cp.source.num_vertex; ++v) {
            const auto& l = cp.target.labels[cp.fibration[v]];
            if (l.kind == comb::VertexKind::Binder)
                std::cerr << "  v" << v << " -> pos" << cp.fibration[v]
                          << " BINDER var=" << l.var << (l.is_existential ? " ∃" : " ∀")
                          << " in_dualizer=" << cp.source.dualizer.count(l.var) << "\n";
        }
    }
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
