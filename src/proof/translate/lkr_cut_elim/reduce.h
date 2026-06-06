#pragma once

// Stage 3 cut-elimination driver — STAGE3_RESET_PLAN Step 3.
//
// CUT_ELIM_DESIGN.md §5: select a topmost cut of maximal degree, dispatch
// by case on the rule pair (left.rule, right.rule), replace the cut's
// subtree with the reduction's output, loop. Termination per §5.6
// (multiset well-order on cut-degrees).
//
// This file is the scaffold: the driver loop, the (degree, topmost)
// selection, the dispatch surface. Every §5 case currently returns
// "not implemented"; the driver, on hitting an irreducible cut, gives
// up and returns the current tree unchanged. Step 4 fills in cases.
//
// Composition note: this driver assumes its input is already in
// multiplicative form (no additive RCuts). Run
// b0::additive_to_multiplicative first. The driver itself does NOT
// call B0 (separation of passes per the Stage 3 plan).

#include "src/core/formula.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/util/error.h"

#include <cstddef>
#include <optional>
#include <unordered_map>
#include <vector>

namespace logic::proof::translate::lkr_cut_elim {

// Cut-free, lemma-free proofs of cited theorems, keyed by the theorem's
// statement (the AxiomRef SentenceHandle a citing RLemma carries). Stage A
// (CUT_ELIM_DESIGN §3) splices these in; citations absent from the map —
// base axioms and schema instances — are irreducible (§7a) and left as-is.
// The mapped Deriv must outlive the eliminate_cuts call.
using LemmaProofs =
    std::unordered_map<SentenceHandle, const Deriv*, SentenceHandleHash>;

// Eliminate Cuts and (proven-theorem) RLemmas from a Deriv via Gentzen's
// Hauptsatz: Stage A inlines lemma citations from `lemmas`, then B0 +
// Stage B reduce the resulting logical cuts. Returns a fresh Deriv with the
// same end-sequent. On hitting an unimplemented case, returns the tree as-is
// (soundness preserved; completeness narrows).
//
// Preconditions: root passes validate().
util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root,
                                      const LemmaProofs& lemmas);

// Convenience overload with no lemma citations to inline (pure cut-elim).
util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root);

// Structural complexity of a formula (CUT_ELIM_DESIGN.md §5.1).
//   - PredicateInstance, SchemaVar, ⊥: 0.
//   - Compound (∧/∨/→/↔/¬): 1 + max(children degrees).
//   - Quantified (∀/∃): 1 + degree(body).
// SentenceHandle resolves to its referenced Formula.
std::size_t degree(FormulaHandle f);

// Path from root to a particular subtree: each step is the child index
// (0 = left/child, 1 = right) of the rule at that level.
using CutPath = std::vector<int>;

struct CutCandidate {
    CutPath     path;
    std::size_t cut_degree;
};

// Find a topmost cut of maximal degree (CUT_ELIM_DESIGN.md §5.1).
// Returns nullopt if the tree has no RCut nodes. "Topmost" = no other
// max-degree cut strictly above it; encoded by stopping descent into
// the first max-degree cut a DFS encounters.
std::optional<CutCandidate> find_topmost_max_deg_cut(const Deriv& root);

}  // namespace logic::proof::translate::lkr_cut_elim
