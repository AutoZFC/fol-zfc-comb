#include "lkr_to_comb.h"

#include "alpha_rename.h"
#include "cut_augment.h"
#include "input_gate.h"
#include "interpret_tree.h"
#include "lemma_inliner.h"
#include "output_gate.h"
#include "sequent_replay.h"
#include "tree.h"
#include "walk.h"

#include "src/proof/translate/lkr_cut_elim/cut_elim.h"

#include <cstdio>
#include <cstdlib>
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

// Translate a CUT-FREE LKR program via the paper-exact Hughes §11.1
// fold (interpret_tree), targeting G(goal). No §15 augmentation,
// alpha_rename, or walk: interpret_tree derives the dualizer (MGU of
// links, Lemma 10.12) and the binding edges (pullback of G(goal)) at
// the root, in canonical G(goal) vars.
util::Result<comb::CombProof> fold_cut_free(
    GlobalContext&             ctx,
    FormulaBuilder&            builder,
    FormulaHandle              goal,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog,
    const std::string&         claim_name)
{
    TRY_ASSIGN(tree, rebuild_tree(prog));
    CutAugmentation empty_aug;  // cut-free ⇒ target is G(goal), unaugmented
    TRY_ASSIGN(replay, replay_sequents(builder, goal_nnf, prog, empty_aug));
    TRY_ASSIGN(cp, interpret_tree(ctx, goal_nnf, prog, *tree, replay));
    cp.claim_name = claim_name;
    TRY(OutputGate::verify(ctx, goal, cp));
    return cp;
}

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

    // The §11.1 fold (interpret_tree) is the paper-exact translator but
    // covers only cut-free programs. So:
    //   - cut-free input → fold directly (target G(goal));
    //   - cut-bearing input → eliminate cuts (Gentzen Hauptsatz) to a
    //     cut-free LKR proof of the SAME goal, then fold.
    // The legacy walk path (§15-augmented goal) remains only as a
    // fallback if cut-elimination — or the resulting fold — fails on
    // some shape, so currently-passing proofs cannot regress.
    bool has_cut = false;
    for (const auto& instr : inlined.instrs) {
        if (std::holds_alternative<lkr::Cut>(instr) ||
            std::holds_alternative<lkr::CloseByLemma>(instr)) {
            has_cut = true;
            break;
        }
    }

    if (!has_cut) {
        return fold_cut_free(ctx_, builder, goal_, goal_nnf, inlined,
                             in.claim_name);
    }

    // Cut-bearing: eliminate cuts, then fold via the §11.1 path.
    //
    // NOTE: lkr_cut_elim::eliminate_cuts is currently PARTIAL — it
    // reduces atom cuts and dead (unused) cuts, but leaves live logical
    // cuts in place (cut_elim.cpp walk_reduce, the recurse-without-reduce
    // branches). When its output still contains a Cut, the cut-free fold
    // rejects it (replay sees a Cut with no augmentation) and we fall
    // back to walk. So today this fast path only fires for proofs whose
    // cuts are all atom/dead; everything else still goes through walk.
    // Completing eliminate_cuts (full Gentzen Hauptsatz) auto-activates
    // this path for all cuts and lets walk be retired.
    if (auto cf = lkr_cut_elim::eliminate_cuts(builder, inlined); cf.ok()) {
        bool still_has_cut = false;
        for (const auto& instr : cf.value().instrs)
            if (std::holds_alternative<lkr::Cut>(instr) ||
                std::holds_alternative<lkr::CloseByLemma>(instr)) {
                still_has_cut = true;
                break;
            }
        if (!still_has_cut) {
            auto folded = fold_cut_free(ctx_, builder, goal_, goal_nnf,
                                        cf.value(), in.claim_name);
            if (folded.ok()) return folded.value();
        }
    }

    // ---- Fallback: legacy walk on the §15-augmented goal --------------
    TRY_ASSIGN(renamed, alpha_rename_to_canonical(builder, goal_nnf, inlined));
    TRY_ASSIGN(cut_aug, build_cut_augmentation(builder, goal_nnf, renamed));
    TRY_ASSIGN(tree,   rebuild_tree(renamed));
    TRY_ASSIGN(replay, replay_sequents(builder, goal_nnf, renamed, cut_aug));

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
