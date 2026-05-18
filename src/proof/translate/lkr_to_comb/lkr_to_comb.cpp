#include "lkr_to_comb.h"

#include "alpha_rename.h"
#include "cut_augment.h"
#include "input_gate.h"
#include "output_gate.h"
#include "sequent_replay.h"
#include "tree.h"
#include "walk.h"

namespace logic::proof::translate::lkr_to_comb {

util::Result<comb::CombProof> LKRtoComb::apply(
    const Program<lkr::Instr>& in)
{
    TRY(InputGate::verify(ctx_, goal_, in));

    FormulaBuilder builder(ctx_);
    FormulaHandle goal_nnf = builder.to_nnf(goal_);

    // Pre-pass: align Forall eigens (and any fix-vars baked into Cut/
    // Weakening formula handles) with the canonical binder vars
    // Fograph will allocate for the §15-augmented goal. Without this,
    // NDtoLKR-style programs trip the link-args-unify check in
    // CombVerifier on any quantified goal. See
    // LKR_TO_COMB_DESIGN.md §7.5 (Option B).
    TRY_ASSIGN(renamed, alpha_rename_to_canonical(builder, goal_nnf, in));

    // Build the §15-augmented goal so that Cut-introduced sequent
    // entries have stable canonical positions in the augmented fograph.
    TRY_ASSIGN(cut_aug, build_cut_augmentation(builder, goal_nnf, renamed));

    TRY_ASSIGN(tree,   rebuild_tree(renamed));
    TRY_ASSIGN(replay, replay_sequents(builder, goal_nnf, renamed, cut_aug));

    // Canonical target: G(augmented_goal). All subgoals share this;
    // fibrations are built in its coordinates.
    comb::Fograph canonical_target(cut_aug.augmented_goal);

    WalkContext wc{builder, renamed, replay, canonical_target, lemmas_};
    TRY_ASSIGN(cp, walk(wc, *tree));
    cp.claim_name = in.claim_name;

    // Output gate runs CombVerifier against the augmented goal.
    TRY(OutputGate::verify(ctx_, cut_aug.augmented_goal, cp));
    return cp;
}

}  // namespace logic::proof::translate::lkr_to_comb
