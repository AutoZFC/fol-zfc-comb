#include "src/proof/translate/lkr_to_comb/interpret_tree.h"

#include "src/proof/translate/lkr_to_comb/comb_build.h"
#include "src/util/error.h"

#include <cstdint>
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
        if (std::holds_alternative<lkr::Forall>(op))
            return MAKE_ERROR << "interpret_tree: Forall not yet implemented (P4)";
        if (std::holds_alternative<lkr::Exists>(op))
            return MAKE_ERROR << "interpret_tree: Exists not yet implemented (P5)";
        if (std::holds_alternative<lkr::Contraction>(op))
            return MAKE_ERROR << "interpret_tree: Contraction not yet implemented (P7)";
        return MAKE_ERROR << "interpret_tree: unexpected linear op";
    }

    // ---- BranchingNode: two-child ops --------------------------------
    util::Result<NodeProof> dispatch(const BranchingNode& n) {
        const lkr::Instr& op = prog.instrs[n.op_idx];
        if (std::holds_alternative<lkr::Cut>(op)) {
            return MAKE_ERROR << "interpret_tree: Cut is out of scope (cut-free only)";
        }
        if (std::holds_alternative<lkr::And>(op)) {
            return MAKE_ERROR << "interpret_tree: And not yet implemented (P6)";
        }
        return MAKE_ERROR << "interpret_tree: unexpected branching op";
    }
};

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
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
