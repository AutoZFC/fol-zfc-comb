#pragma once

// Step 2 of STAGE3_RESET_PLAN: additive→multiplicative cut conversion.
//
// LKR's Cut op is additive (both children's conclusions share the same Γ).
// CUT_ELIM_DESIGN.md §4: Gentzen's Hauptsatz reductions are cleanest on
// the *multiplicative* form. This pass rewrites every additive RCut to a
// (|Γ| RWeakens) wrapper above a multiplicative RCut, preserving the outer
// node's conclusion so the surrounding proof is unaffected.
//
// IR shapes (validate.h documents both — RCut accepts either):
//   - Additive:        left.concl = node.concl ++ {φ}
//                      right.concl = node.concl ++ {dual}
//                      node.concl = Γ   (|node| = |left|-1 = |right|-1)
//
//   - Multiplicative:  left.concl = Γ_L ++ {φ}
//                      right.concl = Γ_R ++ {dual}
//                      node.concl = Γ_L ++ Γ_R    (|node| = |left|+|right|-2)
//
// B0 rewrite at an additive RCut where node.concl = Γ:
//
//   - Inner: a multiplicative RCut with the SAME children and node.concl
//     = Γ ++ Γ. The children are unchanged (their concls are already
//     Γ ++ {φ} / Γ ++ {dual}, which is the multiplicative form for the
//     special case Γ_L = Γ_R = Γ).
//
//   - Wrapper: |Γ| nested RWeakens above the mult-Cut. Each W's added
//     formula is one of Γ's entries (in order). The OUTERMOST W has
//     node.concl = Γ (matching the original additive RCut's node.concl);
//     each descending W's node grows by one entry until the INNERMOST W's
//     child IS the mult-Cut with node.concl = Γ ++ Γ.
//
// Post-condition: every RCut in the output is in multiplicative shape.
// The output passes validate() (additive shape is also acceptable, but
// after this pass none remain).

#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

namespace logic::proof::translate::lkr_cut_elim {

util::Result<DerivPtr> additive_to_multiplicative(const Deriv& root);

}  // namespace logic::proof::translate::lkr_cut_elim
