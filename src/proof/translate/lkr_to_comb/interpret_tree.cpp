#include "src/proof/translate/lkr_to_comb/interpret_tree.h"

#include "src/proof/comb/leap.h"
#include "src/proof/translate/lkr_to_comb/comb_build.h"
#include "src/util/error.h"

#include <algorithm>
#include <cstdint>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// Conclusion sequent of the op at `op_idx` = the top open goal just
// before that op runs (replay.sequent_before). Used from P1 onward.
const std::vector<FormulaHandle>& conclusion_of(
    const SequentReplay& r, uint32_t op_idx) {
    return r.sequent_before[op_idx];
}

// op_idx pinned at a derivation-tree node (all three node kinds carry it).
uint32_t tree_op_idx(const DerivationTree& t) {
    return std::visit([](const auto& n) { return n.op_idx; }, t.node);
}

struct Interp {
    GlobalContext&             ctx;
    FormulaBuilder             fb;
    const Program<lkr::Instr>& prog;
    const SequentReplay&       replay;

    Interp(GlobalContext& c, const Program<lkr::Instr>& p,
           const SequentReplay& r)
        : ctx(c), fb(c), prog(p), replay(r) {}

    util::Result<NodeProof> node(const DerivationTree& t) {
        return std::visit([&](const auto& n) { return dispatch(n); }, t.node);
    }

    // Canonical injection G(H) → G(C) shared by the binder-introducing
    // rules ∀ and ∃: C inserts •x first in the principal block, so the
    // map is identity on Γ entries, +1-shift on the principal body (past
    // •x), and +1-shift on entries after principal (•x added one vertex).
    // Returns remap[H-vertex] = C-vertex, plus C's entry offsets (which
    // the callers need for the •x position and the body range).
    struct BinderRemap {
        std::vector<size_t> remap;  // G(H) vertex → G(C) vertex
        std::vector<size_t> Coff;   // C entry offsets
    };
    BinderRemap binder_insert_remap(const std::vector<FormulaHandle>& C,
                                    const std::vector<FormulaHandle>& H,
                                    size_t p) {
        std::vector<size_t> Coff = entry_vertex_offsets(fb, C);
        std::vector<size_t> Hoff = entry_vertex_offsets(fb, H);
        std::vector<size_t> remap(Hoff.back());
        for (size_t h = 0; h < H.size(); ++h) {
            size_t len     = Hoff[h + 1] - Hoff[h];
            size_t c_start = (h == p) ? Coff[p] + 1   // body, past •x
                                      : Coff[h];        // Γ entries
            for (size_t k = 0; k < len; ++k) remap[Hoff[h] + k] = c_start + k;
        }
        return {std::move(remap), std::move(Coff)};
    }

    // ---- LeafNode: closing ops (P1: AxiomLit, One) -------------------
    //
    // Both close a (possibly larger) sequent Γ. The combinatorial proof
    // has target G(Φ(Γ)); the source is the minimal axiom mapped to the
    // closing entries; every other entry of Γ is left uncovered by the
    // fibration (weakening — paper §11.1's W is folded into the leaf).
    util::Result<NodeProof> dispatch(const LeafNode& n) {
        const lkr::Instr& op = prog.instrs[n.op_idx];
        const std::vector<FormulaHandle>& seq = conclusion_of(replay, n.op_idx);

        comb::Fograph target = build_sequent_fograph(fb, seq);
        std::vector<size_t> off = entry_vertex_offsets(fb, seq);

        if (const auto* ax = std::get_if<lkr::AxiomLit>(&op)) {
            // §11.1 α,ᾱ rule: source = two dual literals sharing one
            // link, no edges, empty dualizer. They map to the atom
            // vertices of entries lit_a and lit_b (each atomic ⇒ one
            // vertex). LKRVerifier already guaranteed they are dual.
            if (ax->lit_a >= seq.size() || ax->lit_b >= seq.size()) {
                return MAKE_ERROR << "interpret_tree: AxiomLit index out of range";
            }
            auto is_single = [&](size_t e) { return off[e + 1] - off[e] == 1; };
            if (!is_single(ax->lit_a) || !is_single(ax->lit_b)) {
                return MAKE_ERROR << "interpret_tree: AxiomLit entry is not a "
                                     "single-atom literal";
            }
            NodeProof np;
            np.target = std::move(target);
            np.source.num_vertex = 2;
            np.source.links = {{0, 1}};
            np.fibration = {off[ax->lit_a], off[ax->lit_b]};
            return np;
        }

        if (const auto* one = std::get_if<lkr::One>(&op)) {
            // §11.1 1 rule: source = a single 1-labelled vertex, no
            // link, no edges, empty dualizer (the minimal fonet •1).
            if (one->idx >= seq.size()) {
                return MAKE_ERROR << "interpret_tree: One index out of range";
            }
            if (off[one->idx + 1] - off[one->idx] != 1) {
                return MAKE_ERROR << "interpret_tree: One entry is not a single "
                                     "vertex";
            }
            NodeProof np;
            np.target = std::move(target);
            np.source.num_vertex = 1;
            np.fibration = {off[one->idx]};
            return np;
        }

        if (std::holds_alternative<lkr::CloseByLemma>(op)) {
            return MAKE_ERROR << "interpret_tree: CloseByLemma is out of scope "
                                 "(cut-free only)";
        }
        return MAKE_ERROR << "interpret_tree: unexpected leaf op";
    }

    // ---- LinearNode: one-child ops -----------------------------------
    util::Result<NodeProof> dispatch(const LinearNode& n) {
        auto child = node(*n.child);
        if (child.is_error()) return child.error();
        const lkr::Instr& op = prog.instrs[n.op_idx];

        const std::vector<FormulaHandle>& C = conclusion_of(replay, n.op_idx);
        const std::vector<FormulaHandle>& H =
            conclusion_of(replay, tree_op_idx(*n.child));

        if (const auto* orr = std::get_if<lkr::Or>(&op)) {
            // §11.1 ∨ rule. Hughes' G(H)=G(C) gives g=f, but THIS LKR's
            // Or moves θ to the end of H (H = Γ split: φ@principal, θ
            // appended), so G(H) and G(C) differ in vertex ORDER. We
            // realize Hughes' canonical iso as a vertex remap π and set
            // f_C = π ∘ f_H. Source is unchanged.
            //
            //   C = [c_0 … c_{p-1}, φ∨θ, c_{p+1} … c_{m-1}]   (m entries)
            //   H = [c_0 … c_{p-1}, φ,   c_{p+1} … c_{m-1}, θ] (m+1 entries)
            size_t p = orr->principal;
            if (p >= C.size() || !C[p].get().is_compound() ||
                C[p].get().as_compound().op != Op::Or) {
                return MAKE_ERROR << "interpret_tree: Or principal is not a "
                                     "disjunction";
            }
            const size_t m = C.size();
            if (H.size() != m + 1) {
                return MAKE_ERROR << "interpret_tree: Or hypothesis arity "
                                     "mismatch (expected " << (m + 1)
                                  << ", got " << H.size() << ")";
            }
            std::vector<size_t> Coff = entry_vertex_offsets(fb, C);
            std::vector<size_t> Hoff = entry_vertex_offsets(fb, H);
            size_t phi_len = fograph_vertex_count(fb, C[p].get().as_compound().left);

            std::vector<size_t> remap(Hoff.back());
            for (size_t h = 0; h < H.size(); ++h) {
                size_t c_start;
                if (h < p)            c_start = Coff[h];        // prefix
                else if (h == p)      c_start = Coff[p];        // φ part of φ∨θ
                else if (h < m)       c_start = Coff[h];        // middle c_{>p}
                else                  c_start = Coff[p] + phi_len; // θ part
                size_t len = Hoff[h + 1] - Hoff[h];
                for (size_t k = 0; k < len; ++k) remap[Hoff[h] + k] = c_start + k;
            }

            NodeProof np;
            np.target    = build_sequent_fograph(fb, C);
            np.source    = std::move(child.value().source);
            np.fibration = std::move(child.value().fibration);
            for (auto& fv : np.fibration) fv = remap[fv];
            return np;
        }
        if (const auto* ex = std::get_if<lkr::Exchange>(&op)) {
            // §11.1 X rule: g = x ∘ f, x the canonical iso reordering the
            // swapped entries. H = C with entries i,j swapped, so H
            // entry i = C entry j (and vice versa); all others identity.
            size_t i = ex->i, j = ex->j;
            if (i >= C.size() || j >= C.size()) {
                return MAKE_ERROR << "interpret_tree: Exchange index out of range";
            }
            if (H.size() != C.size()) {
                return MAKE_ERROR << "interpret_tree: Exchange arity mismatch";
            }
            std::vector<size_t> Coff = entry_vertex_offsets(fb, C);
            std::vector<size_t> Hoff = entry_vertex_offsets(fb, H);
            std::vector<size_t> remap(Hoff.back());
            for (size_t h = 0; h < H.size(); ++h) {
                size_t c_entry = (h == i) ? j : (h == j) ? i : h;
                size_t len = Hoff[h + 1] - Hoff[h];
                for (size_t k = 0; k < len; ++k)
                    remap[Hoff[h] + k] = Coff[c_entry] + k;
            }
            NodeProof np;
            np.target    = build_sequent_fograph(fb, C);
            np.source    = std::move(child.value().source);
            np.fibration = std::move(child.value().fibration);
            for (auto& fv : np.fibration) fv = remap[fv];
            return np;
        }
        if (std::holds_alternative<lkr::Weakening>(op)) {
            // §11.1 W rule. This LKR appends φ to the hypothesis
            // (H = Γ,φ); the conclusion C = Γ is H with the last entry
            // dropped. Hughes' canonical injection w : G(Γ) → G(Γ,φ)
            // here runs the other way: G(C) = G(Γ) is the PREFIX of the
            // child's G(H) = G(Γ)+G(φ), with φ's vertices the suffix.
            //
            // Soundness: φ must be UNCOVERED in the child (no source
            // vertex maps into φ's block). Otherwise the weakening is
            // load-bearing — the proof's content lives in φ, so dropping
            // it is unsound. Reject (matches the I-2 input-gate intent).
            //
            // Since φ is the suffix, the fibration is unchanged: every
            // covered position is < |G(Γ)|.
            NodeProof np;
            np.target = build_sequent_fograph(fb, C);  // G(Γ)
            const size_t phi_start = np.target.num_vertex();
            for (size_t fv : child.value().fibration) {
                if (fv >= phi_start) {
                    return MAKE_ERROR << "interpret_tree: load-bearing Weakening — "
                                         "a source vertex maps into the weakened "
                                         "formula's block (covered position " << fv
                                      << " ≥ |G(Γ)|=" << phi_start << "); "
                                         "Hughes §11.1 W introduces an UNCOVERED φ";
                }
            }
            np.source    = std::move(child.value().source);
            np.fibration = std::move(child.value().fibration);
            return np;
        }
        if (const auto* fa = std::get_if<lkr::Forall>(&op)) {
            // §11.1 ∀ rule. C = [Γ, ∀x.φ @principal]; H = [Γ, φ[x:=eigen]
            // @principal]. G(∀x.φ) = •x + G(φ): the Fograph builder puts
            // •x first in the principal block, then the body. So:
            //   canonical injection a : G(H) → G(C) is identity on Γ
            //   before principal, +1-shift on the principal body (past
            //   •x), and +1-shift on entries after principal.
            // If the body is uncovered (no source vertex lands in it),
            // g = a∘f. Otherwise add a universal •x source vertex (no
            // cograph edges — Def. 10.7) mapped to G(C)'s •x, with
            // binding edges to the source preimages of •x's bound atoms.
            size_t p = fa->principal;
            if (p >= C.size() || !C[p].get().is_quantified() ||
                C[p].get().as_quantified().op != Op::Forall) {
                return MAKE_ERROR << "interpret_tree: Forall principal is not ∀";
            }
            if (H.size() != C.size()) {
                return MAKE_ERROR << "interpret_tree: Forall arity mismatch";
            }
            comb::Fograph target = build_sequent_fograph(fb, C);
            BinderRemap   br     = binder_insert_remap(C, H, p);
            const size_t  bx     = br.Coff[p];  // •x position in G(C)

            std::vector<size_t> fib = std::move(child.value().fibration);
            for (auto& fv : fib) fv = br.remap[fv];

            bool covered = false;
            for (size_t fv : fib)
                if (fv > bx && fv < br.Coff[p + 1]) { covered = true; break; }

            NodeProof np;
            np.target    = std::move(target);
            np.source    = std::move(child.value().source);
            np.fibration = std::move(fib);

            if (covered) {
                // Universal •x: +-disjoint (no cograph edges). Binding
                // edges are computed at the root from G(goal) (per-node
                // targets can alias a fresh binder var with a free eigen
                // var and fabricate phantom binding edges).
                np.fibration.push_back(bx);  // •x_src ↦ •x
                np.source.num_vertex += 1;
            }
            return np;
        }
        if (const auto* ex = std::get_if<lkr::Exists>(&op)) {
            // §11.1 ∃ rule. C = [Γ, ∃x.φ @principal]; H = [Γ, φ[x:=t]
            // @principal] for the witness t. G(∃x.φ) = •x × G(φ): •x is
            // ×-JOINED to the body (existential), unlike ∀ where it is
            // +-disjoint. The canonical injection e : G(H) → G(C) is the
            // same shape as ∀ (•x inserted first in the principal block).
            //
            // P = source vertices landing in the body. If empty, g = e∘f.
            // Else add an existential •x source vertex with cograph edges
            // to EVERY vertex in P (the ×-join → existential), mapped to
            // G(C)'s •x, plus binding edges to its bound x-literals.
            //
            // The witness t is NOT used here: the dualizer is the MGU of
            // the links (Lemma 10.12), computed once at the root.
            size_t p = ex->principal;
            if (p >= C.size() || !C[p].get().is_quantified() ||
                C[p].get().as_quantified().op != Op::Exists) {
                return MAKE_ERROR << "interpret_tree: Exists principal is not ∃";
            }
            if (H.size() != C.size()) {
                return MAKE_ERROR << "interpret_tree: Exists arity mismatch";
            }
            comb::Fograph target = build_sequent_fograph(fb, C);
            BinderRemap   br     = binder_insert_remap(C, H, p);
            const size_t  bx     = br.Coff[p];

            std::vector<size_t> fib = std::move(child.value().fibration);
            for (auto& fv : fib) fv = br.remap[fv];

            std::vector<size_t> P;
            for (size_t v = 0; v < fib.size(); ++v)
                if (fib[v] > bx && fib[v] < br.Coff[p + 1]) P.push_back(v);

            NodeProof np;
            np.target    = std::move(target);
            np.source    = std::move(child.value().source);
            np.fibration = std::move(fib);

            if (!P.empty()) {
                size_t xsrc = np.source.num_vertex;
                np.source.num_vertex += 1;
                // ×-join: •x_src adjacent to every vertex in P (this is
                // what makes it existential). Binding edges are computed
                // at the root from G(goal) — see Forall note.
                for (size_t v : P) np.source.cograph_edges.push_back({xsrc, v});
                np.fibration.push_back(bx);  // •x_src ↦ •x
            }
            return np;
        }
        if (const auto* ct = std::get_if<lkr::Contraction>(&op)) {
            // §11 C rule, in this LKR's direction. Contraction(i,j)
            // removes entry j, so the node conclusion C = Γ,ϕᵢ,ϕⱼ has
            // two α-equal copies at i,j and the child proves the subgoal
            // H = C with entry j removed (one copy). Hughes §11.1
            // collapses two→one going DOWN; the fold builds two from one
            // going UP. Since H (one copy) is already a complete proof,
            // C follows by reinstating the duplicate ϕⱼ UNCOVERED — i.e.
            // Weakening at position j. (ϕᵢ ≡ ϕⱼ, so G(ϕⱼ) is identical
            // structure; leaving it uncovered is sound.)
            size_t jdx = ct->j;
            if (jdx >= C.size()) {
                return MAKE_ERROR << "interpret_tree: Contraction j out of range";
            }
            if (H.size() != C.size() - 1) {
                return MAKE_ERROR << "interpret_tree: Contraction arity mismatch "
                                     "(expected " << (C.size() - 1) << ", got "
                                  << H.size() << ")";
            }
            std::vector<size_t> Coff = entry_vertex_offsets(fb, C);
            std::vector<size_t> Hoff = entry_vertex_offsets(fb, H);
            std::vector<size_t> remap(Hoff.back());
            for (size_t k = 0; k < H.size(); ++k) {
                size_t c_entry = (k < jdx) ? k : k + 1;  // skip inserted copy j
                size_t len = Hoff[k + 1] - Hoff[k];
                for (size_t m = 0; m < len; ++m)
                    remap[Hoff[k] + m] = Coff[c_entry] + m;
            }
            NodeProof np;
            np.target    = build_sequent_fograph(fb, C);
            np.source    = std::move(child.value().source);
            np.fibration = std::move(child.value().fibration);
            for (auto& fv : np.fibration) fv = remap[fv];
            return np;
        }
        return MAKE_ERROR << "interpret_tree: unexpected linear op";
    }

    // ---- BranchingNode: two-child ops --------------------------------
    util::Result<NodeProof> dispatch(const BranchingNode& n) {
        const lkr::Instr& op = prog.instrs[n.op_idx];
        if (std::holds_alternative<lkr::Cut>(op)) {
            return MAKE_ERROR << "interpret_tree: Cut is out of scope (cut-free only)";
        }
        const auto* andop = std::get_if<lkr::And>(&op);
        if (!andop) return MAKE_ERROR << "interpret_tree: unexpected branching op";

        // §11.1 ∧ rule (multiplicative). C = [Γ1,Γ2, φ∧θ @principal];
        // the LEFT premise H1 = [Γ1, φ] and RIGHT premise H2 = [Γ2, θ],
        // where Γ is split by left_partition. G(C) puts the φ∧θ block as
        // G(φ)×G(θ) at `principal`. Each premise injects: z_i : G(H_i) →
        // G(C). P_i = source vertices landing in φ_i (the conjunct). f_i
        // is "weak" if P_i empty.
        //   both strong / both weak → fuse K1,K2 at P1,P2 (Def. 10.4:
        //     union + cograph edges between every P1 and every P2 vertex);
        //   one weak → take the weak side alone (its Γ_i already closes C).
        auto left  = node(*n.left);
        if (left.is_error())  return left.error();
        auto right = node(*n.right);
        if (right.is_error()) return right.error();

        const std::vector<FormulaHandle>& C  = conclusion_of(replay, n.op_idx);
        const std::vector<FormulaHandle>& H1 = conclusion_of(replay, tree_op_idx(*n.left));
        const std::vector<FormulaHandle>& H2 = conclusion_of(replay, tree_op_idx(*n.right));

        size_t p = andop->principal;
        if (p >= C.size() || !C[p].get().is_compound() ||
            C[p].get().as_compound().op != Op::And) {
            return MAKE_ERROR << "interpret_tree: And principal is not ∧";
        }
        std::vector<size_t> Lpart = andop->left_partition;
        std::sort(Lpart.begin(), Lpart.end());
        std::vector<size_t> Rpart;
        {
            std::unordered_set<size_t> inL(Lpart.begin(), Lpart.end());
            for (size_t i = 0; i < C.size(); ++i)
                if (i != p && !inL.count(i)) Rpart.push_back(i);
        }
        if (H1.size() != Lpart.size() + 1 || H2.size() != Rpart.size() + 1) {
            return MAKE_ERROR << "interpret_tree: And premise arity mismatch";
        }

        comb::Fograph       target = build_sequent_fograph(fb, C);
        std::vector<size_t> Coff   = entry_vertex_offsets(fb, C);
        std::vector<size_t> H1off  = entry_vertex_offsets(fb, H1);
        std::vector<size_t> H2off  = entry_vertex_offsets(fb, H2);
        size_t phi_len = fograph_vertex_count(fb, C[p].get().as_compound().left);

        // z1 : G(H1) → G(C). H1 = [Γ1 entries (sorted Lpart), φ].
        std::vector<size_t> z1(H1off.back());
        for (size_t k = 0; k < Lpart.size(); ++k)
            for (size_t j = 0, len = H1off[k + 1] - H1off[k]; j < len; ++j)
                z1[H1off[k] + j] = Coff[Lpart[k]] + j;
        for (size_t k = Lpart.size(), j = 0, len = H1off[k + 1] - H1off[k]; j < len; ++j)
            z1[H1off[k] + j] = Coff[p] + j;                 // φ part of φ∧θ
        // z2 : G(H2) → G(C). H2 = [Γ2 entries (sorted Rpart), θ].
        std::vector<size_t> z2(H2off.back());
        for (size_t k = 0; k < Rpart.size(); ++k)
            for (size_t j = 0, len = H2off[k + 1] - H2off[k]; j < len; ++j)
                z2[H2off[k] + j] = Coff[Rpart[k]] + j;
        for (size_t k = Rpart.size(), j = 0, len = H2off[k + 1] - H2off[k]; j < len; ++j)
            z2[H2off[k] + j] = Coff[p] + phi_len + j;        // θ part of φ∧θ

        std::vector<size_t> f1 = std::move(left.value().fibration);
        for (auto& v : f1) v = z1[v];
        std::vector<size_t> f2 = std::move(right.value().fibration);
        for (auto& v : f2) v = z2[v];

        const size_t phi_lo = Coff[p],          phi_hi = Coff[p] + phi_len;
        const size_t the_lo = Coff[p] + phi_len, the_hi = Coff[p + 1];
        std::vector<size_t> P1, P2;
        for (size_t v = 0; v < f1.size(); ++v)
            if (f1[v] >= phi_lo && f1[v] < phi_hi) P1.push_back(v);
        for (size_t v = 0; v < f2.size(); ++v)
            if (f2[v] >= the_lo && f2[v] < the_hi) P2.push_back(v);
        const bool w1 = P1.empty(), w2 = P2.empty();

        NodeProof np;
        np.target = std::move(target);

        if (w1 != w2) {
            // Mixed: the weak side's Γ_i already closes C (its conjunct
            // is uncovered); take it alone, drop the other premise.
            if (w1) { np.source = std::move(left.value().source);  np.fibration = std::move(f1); }
            else    { np.source = std::move(right.value().source); np.fibration = std::move(f2); }
            return np;
        }

        // Both strong or both weak: fusion of K1 and K2 at P1, P2.
        comb::Fonet& L = left.value().source;
        comb::Fonet& R = right.value().source;
        const size_t off = L.num_vertex;
        np.source.num_vertex = L.num_vertex + R.num_vertex;
        np.source.links = L.links;
        for (auto e : R.links)         np.source.links.push_back({e.first + off, e.second + off});
        np.source.cograph_edges = L.cograph_edges;
        for (auto e : R.cograph_edges) np.source.cograph_edges.push_back({e.first + off, e.second + off});
        // Fusion edges: every P1 (left) ×-joined to every P2 (right).
        for (size_t a : P1) for (size_t b : P2)
            np.source.cograph_edges.push_back({a, b + off});
        np.fibration = std::move(f1);
        for (size_t v : f2) np.fibration.push_back(v);
        return np;
    }
};

// The combinatorial proof's dualizer is the MGU of the final links
// (Hughes Lemma 10.12) — shared with the verifier via
// comb::most_general_dualizer. We compute it once at the root, where the
// source labels reference the final G(goal) vars, so δ lands in the
// right namespace regardless of the per-node target rebuilds.
//
// The translator requires δ to be TOTAL on existentials: an existential
// left unconstrained by the links would need a fresh stem witness, which
// this Term language doesn't yet support — reject it explicitly.
util::Result<std::unordered_map<var_index, Term>> root_dualizer(
    const comb::CombProof& cp)
{
    TRY_ASSIGN(delta, comb::most_general_dualizer(cp));
    for (size_t v = 0; v < cp.source.num_vertex; ++v) {
        const auto& lbl = cp.source_label(v);
        if (lbl.kind == comb::VertexKind::Binder && lbl.is_existential &&
            !delta.count(lbl.var)) {
            return MAKE_ERROR << "root_dualizer: existential " << lbl.var
                              << " is unconstrained by links (no witness); "
                                 "stem witnesses are not yet supported";
        }
    }
    return delta;
}

}  // namespace

util::Result<comb::CombProof> interpret_tree(
    GlobalContext&             ctx,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog,
    const DerivationTree&      root,
    const SequentReplay&       replay)
{
    Interp interp(ctx, prog, replay);
    auto rp = interp.node(root);
    if (rp.is_error()) return rp.error();
    NodeProof& np = rp.value();

    // Root conclusion must be the goal: target == G(goal_nnf).
    // (Phase-1 equality is re-checked by CombVerifier downstream; here we
    // just assemble the CombProof.)
    (void)goal_nnf;

    comb::CombProof cp;
    cp.target    = std::move(np.target);
    cp.source    = std::move(np.source);
    cp.fibration = std::move(np.fibration);

    // Source binding edges = pullback of G(goal)'s binding graph along
    // the fibration: (S,A) is a source binding edge iff (f(S),f(A)) is a
    // target binding edge. Computed at the root because G(goal) is a
    // sentence (no free eigenvars), so its binder var allocation cannot
    // alias a free var — unlike the per-node intermediate targets.
    {
        std::set<std::pair<size_t, size_t>> tgt_bind;
        for (const auto& e : cp.target.binding_edges) tgt_bind.insert(e);
        // Identify source binder vertices.
        for (size_t s = 0; s < cp.source.num_vertex; ++s) {
            if (cp.source_label(s).kind != comb::VertexKind::Binder) continue;
            for (size_t a = 0; a < cp.source.num_vertex; ++a) {
                if (cp.source_label(a).kind != comb::VertexKind::Atom) continue;
                if (tgt_bind.count({cp.fibration[s], cp.fibration[a]}))
                    cp.source.binding_edges.push_back({s, a});
            }
        }
    }

    // Dualizer = MGU of the final links (Lemma 10.12), in G(goal) vars.
    auto delta = root_dualizer(cp);
    if (delta.is_error()) return delta.error();
    cp.source.dualizer = std::move(delta.value());
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
