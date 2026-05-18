#include "lkr_to_comb.h"

#include "alpha_rename.h"
#include "cut_augment.h"
#include "input_gate.h"
#include "lemma_inliner.h"
#include "output_gate.h"
#include "sequent_replay.h"
#include "tree.h"
#include "walk.h"

#include <variant>

namespace logic::proof::translate::lkr_to_comb {

namespace {

// Compute a safe starting binder-var index for per-hypothesis targets:
// strictly greater than any Fixed var that appears in goal formulas or
// LKR ops. This guarantees that Fograph-allocated binder vars in
// per-hypothesis targets never collide with vars that show up as
// witness terms in the dualizer (which come from LKR Forall eigens).
struct MaxFixedScan {
    var_index high{0};   // one past max seen (so it's a valid "next" allocator)

    void see(var_index v) {
        if (v + 1 > high) high = v + 1;
    }
    void scan_term(const Term& t) {
        if (t.is_fixed()) see(t.as_variable());
    }
    void scan_formula(FormulaHandle h) {
        if (!h.valid()) return;
        const Formula& f = h.get();
        if (f.is_predicate()) {
            for (const auto& a : f.as_predicate().args()) scan_term(a);
            return;
        }
        if (f.is_compound()) {
            if (f.as_compound().left.valid())
                scan_formula(f.as_compound().left);
            if (f.as_compound().right.valid())
                scan_formula(f.as_compound().right);
            return;
        }
        if (f.is_quantified()) scan_formula(f.as_quantified().body);
    }
    void scan_program(const Program<lkr::Instr>& prog) {
        for (const auto& instr : prog.instrs) {
            std::visit([&](auto const& op) {
                using T = std::decay_t<decltype(op)>;
                if constexpr (std::is_same_v<T, lkr::Forall>) {
                    see(op.eigen);
                } else if constexpr (std::is_same_v<T, lkr::Weakening>) {
                    if (auto* h = std::get_if<FormulaHandle>(&op.formula)) {
                        scan_formula(*h);
                    }
                } else if constexpr (std::is_same_v<T, lkr::Cut>) {
                    if (auto* h = std::get_if<FormulaHandle>(&op.cut_formula)) {
                        scan_formula(*h);
                    }
                }
            }, instr);
        }
    }
};

}  // namespace

util::Result<comb::CombProof> LKRtoComb::apply(
    const Program<lkr::Instr>& in)
{
    TRY(InputGate::verify(ctx_, goal_, in));

    FormulaBuilder builder(ctx_);
    FormulaHandle goal_nnf = builder.to_nnf(goal_);

    // Strategy A (§4.12): splice lemma LKR programs into the outer at
    // each CloseByLemma. The lemma's cuts then propagate into the
    // combined program's §15 augmented goal naturally.
    TRY_ASSIGN(inlined, inline_lemmas(builder, goal_nnf, in, lemmas_));

    // Rename LKR Forall eigens (and any fix-vars baked into Cut/
    // Weakening formulas) to match the canonical vars Fograph allocates
    // for the §15-augmented goal. This puts witness terms in dualizer
    // values into canonical-var space from the start of the walk, so
    // they don't need per-rule renaming machinery.
    TRY_ASSIGN(renamed, alpha_rename_to_canonical(builder, goal_nnf, inlined));

    // The augmented goal is built for the OutputGate's verify call
    // (CombVerifier rebuilds Fograph(NNF(augmented_goal)) and compares
    // structurally to the proof's target).
    TRY_ASSIGN(cut_aug, build_cut_augmentation(builder, goal_nnf, renamed));

    TRY_ASSIGN(tree,   rebuild_tree(renamed));
    TRY_ASSIGN(replay, replay_sequents(builder, goal_nnf, renamed, cut_aug));

    // Seed next_target_var above any Fixed var that could appear as
    // a "real" var in source labels or dualizer values. After
    // alpha_rename, LKR Forall eigens equal canonical-target binder
    // vars, so witness terms in dualizer are in canonical space.
    // Per-hypothesis target binders must avoid colliding with this
    // canonical space — scan the canonical target for max var.
    comb::Fograph canonical_for_max(builder.to_nnf(cut_aug.augmented_goal));
    MaxFixedScan scan;
    scan.scan_formula(goal_nnf);
    scan.scan_formula(cut_aug.augmented_goal);
    scan.scan_program(renamed);
    for (const auto& lbl : canonical_for_max.labels) {
        if (lbl.kind == comb::VertexKind::Binder) scan.see(lbl.var);
        if (lbl.kind == comb::VertexKind::Atom) {
            for (const auto& a : lbl.args) scan.scan_term(a);
        }
    }

    WalkContext wc{builder, renamed, replay, lemmas_, scan.high};
    TRY_ASSIGN(cp, walk(wc, *tree, cut_aug.augmented_goal));
    cp.claim_name = in.claim_name;

    TRY(OutputGate::verify(ctx_, cut_aug.augmented_goal, cp));
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
