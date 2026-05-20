#include "src/proof/translate/lkr_to_comb/interpret_tree.h"

#include "src/proof/translate/lkr_to_comb/comb_build.h"
#include "src/util/error.h"

#include <cstdint>
#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// Conclusion sequent of the op at `op_idx` = the top open goal just
// before that op runs (replay.sequent_before). Used from P1 onward.
[[maybe_unused]] const std::vector<FormulaHandle>& conclusion_of(
    const SequentReplay& r, uint32_t op_idx) {
    return r.sequent_before[op_idx];
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

        if (std::holds_alternative<lkr::Or>(op))
            return MAKE_ERROR << "interpret_tree: Or not yet implemented (P2)";
        if (std::holds_alternative<lkr::Exchange>(op))
            return MAKE_ERROR << "interpret_tree: Exchange not yet implemented (P2)";
        if (std::holds_alternative<lkr::Weakening>(op))
            return MAKE_ERROR << "interpret_tree: Weakening not yet implemented (P3)";
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
