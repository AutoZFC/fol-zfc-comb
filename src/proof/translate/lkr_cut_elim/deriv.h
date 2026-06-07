#pragma once

// Deriv — an explicit, sequent-carrying derivation tree for LKR.
//
// The flat LKR program + rebuild_tree gives a tree whose nodes only hold
// op indices; the sequent at each node is implicit in the verifier's stack.
// Gentzen cut-elimination (CUT_ELIM_DESIGN.md) must DUPLICATE and SUBSTITUTE
// into subderivations, so each node here is self-contained: it carries its
// own conclusion sequent and its rule's data, with child Derivs (not op
// indices). Each rule stores the positional fields it needs (relative to
// THIS node's conclusion) plus children. A Deriv→Deriv reduction is
// responsible for keeping a rewritten node's conclusion and its positional
// fields consistent; emit then trusts them. There is no global ShiftPoint
// index-arithmetic across the program (the old walk_reduce's hack) —
// positions are always local to a node's own conclusion.
//
// build(): flat Program<lkr::Instr> (verifier-accepted) → Deriv, computed by
//          replaying the verifier's per-op sequent mutations.
// emit():  Deriv → flat Program<lkr::Instr>, by a pre-order walk that
//          recomputes each op's positional fields by searching the node's
//          conclusion sequent. The result re-verifies under LKRVerifier.
//
// build∘emit is the identity-on-meaning round-trip (P0): a verifier-accepted
// program builds and re-emits to a verifier-accepted program of the same
// goal. Reductions (Stage A/B0/B) are Deriv→Deriv rewrites between the two.

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/proof.h"
#include "src/util/error.h"

#include <cstddef>
#include <memory>
#include <variant>
#include <vector>

namespace logic::proof::translate::lkr_cut_elim {

struct Deriv;
using DerivPtr = std::unique_ptr<Deriv>;

// Closing rules (leaves).
struct RAx     { std::size_t a{}; std::size_t b{}; };  // dual literals at a,b
struct ROne    { std::size_t idx{}; };                 // truth literal ¬⊥ at idx
// Mirrors lkr::CloseByLemma — typed target (AxiomRef carrying SentenceHandle,
// or full SchemaInstData) plus the diagnostic source-cited name forwarded
// through the build/emit round-trip so used_names tracking survives a cut-
// elim pass.
struct RLemma  {
    std::variant<AxiomRef, SchemaInstData> target{};
    std::string                            source_name{};
};

// Structural rules (one child).
struct RExchange { std::size_t i{}; std::size_t j{}; DerivPtr child; };
// Weakening mirrors the (goal-directed) verifier: the child's conclusion is
// THIS node's conclusion with position `idx` REMOVED (child is SMALLER).
// This is Hughes W read backward (Γ,φ → Γ). See WEAKENING_FIX_DESIGN.md.
struct RWeaken   { std::size_t idx{}; DerivPtr child; };
// Duplicate: the child's conclusion is THIS conclusion with a copy of
// position `src` appended (child is BIGGER). Inverse of RContract.
struct RDuplicate{ std::size_t src{}; DerivPtr child; };
struct RContract { std::size_t i{}; std::size_t j{}; DerivPtr child; };

// Logical rules.
struct RAnd   { std::size_t principal{}; std::vector<std::size_t> left_partition; DerivPtr left; DerivPtr right; };
struct ROr    { std::size_t principal{}; DerivPtr child; };
struct RForall{ std::size_t principal{}; var_index eigen{}; DerivPtr child; };
struct RExists{ std::size_t principal{}; Term witness{}; DerivPtr child; };

// Cut (additive): both children's conclusions are THIS conclusion with the
// cut formula (resp. its NNF dual) appended at the end.
struct RCut   { FormulaHandle cut_formula{}; DerivPtr left; DerivPtr right; };

using Rule = std::variant<
    RAx, ROne, RLemma,
    RExchange, RWeaken, RDuplicate, RContract,
    RAnd, ROr, RForall, RExists,
    RCut>;

struct Deriv {
    std::vector<FormulaHandle> conclusion;  // the sequent this node derives
    Rule                       rule;
};

// Build a Deriv from a verifier-accepted LKR program. `goal_nnf` seeds the
// root conclusion. Mirrors LKRVerifier's per-op mutations exactly.
util::Result<DerivPtr> build(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog);

// Emit a flat LKR program from a Deriv. Positional fields are recomputed by
// searching each node's conclusion. The result, run against the same goal,
// re-verifies under LKRVerifier.
util::Result<Program<lkr::Instr>> emit(const Deriv& root);

// Normalize: coalesce each maximal chain of RExchange nodes into the minimal
// set of transpositions realizing the chain's net permutation (an identity
// chain collapses to nothing). Cut-elimination emits an RExchange per
// permutation step and never merges them, inflating the cut-free Deriv with
// reordering bookkeeping (e.g. eq_iff_eq: 0 → 2765 exchanges, ~40× total). This
// rewrites the tree IN PLACE. Pure reordering: every node's conclusion is
// preserved, so emit→LKRVerifier (and the comb back end) still accept.
void coalesce_exchanges(DerivPtr& root);

}  // namespace logic::proof::translate::lkr_cut_elim
