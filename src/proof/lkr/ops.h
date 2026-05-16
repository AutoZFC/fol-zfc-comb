#pragma once

// LKR op structs and the lkr::Instr variant.
//
// LKR is the right-sided one-sided classical sequent calculus of
// Hughes 2019, "First-order proofs without syntax", §11.
//
// =========================================================================
// Paper-pure rules (Hughes §11)
// =========================================================================
//
// A sequent is a finite *sequence* of formulas in NNF; the empty sequent
// is unprovable. The nine §11 rules are:
//
//   AxiomLit  (α, ᾱ)   atomic axiom: atom α and its dual close a sequent.
//   One       (1)      truth-constant axiom (encoded as ¬⊥ in our NNF).
//   Exchange  (X)      Γ,φ,θ,Δ ⊢ Γ,θ,φ,Δ.
//   Weakening (W)      Γ ⊢ Γ,φ.
//   Contraction (C)    Γ,φ,φ' ⊢ Γ,φ where φ' =α φ.
//   And       (∧)      multiplicative: Γ,φ  Δ,θ ⊢ Γ,Δ,φ∧θ.
//   Or        (∨)      Γ,φ,θ ⊢ Γ,φ∨θ.
//   Forall    (∀)      Γ,φ ⊢ Γ,∀x.φ, with x not free in Γ.
//   Exists    (∃)      Γ,φ{x↦t} ⊢ Γ,∃x.φ.
//
// =========================================================================
// Hughes §15-endorsed extensions
// =========================================================================
//
//   Cut         Hughes §15 "cut combinatorial proofs": from Γ,φ and Γ,¬φ
//               derive Γ. Additive presentation; the multiplicative form
//               is admissibly equivalent via Contraction.
//
//   CloseByLemma   The lemma-as-cut realizer. Closes the current goal by
//               appeal to a previously-verified theorem (or an instantiated
//               schema). Soundness: theorems enter the registry only when
//               their proofs have been verified, so a `CloseByLemma(L)` op
//               on a sequent containing φ_L_nnf is admissibly equivalent
//               to splicing L's proof followed by Weakening up to Γ.
//               In Hughes-pure form this op is eliminated by inlining the
//               named lemma's proof; the combinatorial-proof construction
//               of §11.1 sees only inlined proofs.
//
// No other extensions exist. AxiomGen, UseTheorem, and SchemaInst (which
// previous revisions admitted as separate primitives) have been removed
// in favor of structural decomposition + AxiomLit (for AxiomGen) and
// CloseByLemma (for UseTheorem and SchemaInst).
//
// =========================================================================
// Op stream semantics
// =========================================================================
//
// Each op operates on the top of an open-goals stack. Initial state:
// open_goals = [[NNF(goal)]]. Success: empty open_goals after the last op.
//
//   Closing ops  (AxiomLit, One, CloseByLemma): pop the current goal.
//   Linear  ops  (Exchange, Weakening, Contraction, Or, Forall, Exists):
//     replace the current goal with one new goal.
//   Branching ops (And, Cut): pop the current goal, push two new ones
//     (depth-first; the second is on top so the next instruction operates
//     on it).

#include "src/core/formula.h"
#include "src/parser/formula_ast.h"
#include "src/proof/ir.h"

#include <cstddef>
#include <memory>
#include <variant>
#include <vector>

namespace logic::proof::lkr {

// FormulaSource — payload for ops that introduce a new formula.
//
// Either a deferred AST (parsed at execute time against the verifier's
// scope-name table) or a pre-resolved FormulaHandle (produced by a
// translator pass that already has the formula). Both lower to the same
// FormulaHandle in the verifier — and are NNF-normalized at the use
// site.
using FormulaSource = std::variant<std::shared_ptr<ASTNode>, FormulaHandle>;

// =========================================================================
// Closing rules (§11)
// =========================================================================

// AxiomLit (α, ᾱ): close the goal when entries[lit_a] and entries[lit_b]
// are dual atomic literals (one positive, one negative for the same atom).
struct AxiomLit {
    OpHeader h{};
    size_t   lit_a{0};
    size_t   lit_b{0};
};

// One (1): close the goal when entries[idx] is the truth-constant literal.
// In our NNF, 1 is encoded as ¬⊥ (Compound{Not, Bottom}); a bare Bottom
// formula is 0 and is unprovable.
struct One {
    OpHeader h{};
    size_t   idx{0};
};

// =========================================================================
// Closing rule (§15-endorsed): lemma-as-cut realizer
// =========================================================================

// CloseByLemma: close the current goal by appealing to a previously-
// verified theorem or a schema. The verifier resolves `axiom.name` and
// `bindings` to a closing formula φ:
//   * `bindings` empty → look up theorem/axiom by name; φ = its formula.
//   * `bindings` non-empty → look up schema by name; φ = body[bindings].
// φ_nnf must appear in the current sequent. The op pops the goal.
//
// This is the LKR realizer of "use a previously-proven lemma": its caller
// typically pairs it with Cut(φ) so that LEFT closes via CloseByLemma
// while RIGHT continues with ¬φ available as a cut-in.
struct CloseByLemma {
    OpHeader                   h{};
    AxiomRef                   axiom{};
    std::vector<SchemaBinding> bindings{};
};

// =========================================================================
// Structural rules (§11 X / W / C)
// =========================================================================

// Exchange: swap entries[i] and entries[j].
struct Exchange {
    OpHeader h{};
    size_t   i{0};
    size_t   j{0};
};

// Weakening: append `formula` to the entries.
struct Weakening {
    OpHeader      h{};
    FormulaSource formula{};
};

// Contraction: remove entries[j] when entries[i] == entries[j] (alpha-
// equivalence captured via FormulaHandle equality).
struct Contraction {
    OpHeader h{};
    size_t   i{0};
    size_t   j{0};
};

// =========================================================================
// Logical rules (§11 ∧ / ∨ / ∀ / ∃)
// =========================================================================

// And: multiplicative split. Conclusion sequent has entries[principal] =
// φ ∧ θ. The translator partitions the non-principal entries into
// `left_partition` (going to the LEFT premise) and the implicit complement
// (going to RIGHT).
//
// LEFT subgoal: entries[i] for i in sorted(left_partition), in original
// order, followed by φ at the end.
//
// RIGHT subgoal: entries[j] for j NOT in left_partition and j != principal,
// in original order, followed by θ at the end.
//
// Constraints: left_partition is a sequence of distinct indices, all
// strictly less than the sequent size, and none equal to `principal`.
// The op stores them un-sorted; the verifier sorts internally.
struct And {
    OpHeader            h{};
    size_t              principal{0};
    std::vector<size_t> left_partition{};
};

// Or: principal entries[principal] = φ ∨ θ. Replace with adjacent entries
// φ at `principal` and θ appended at the end.
struct Or {
    OpHeader h{};
    size_t   principal{0};
};

// Forall: principal entries[principal] = ∀x.ϕ. Replace the principal
// entry with ϕ[x:=Term::fixed(eigen)]. Side condition: `eigen` must not
// occur free in any other entry (Hughes' "x not free in Γ" condition);
// the verifier checks this.
//
// `eigen` is chosen by the constructor of the LKR program (the translator,
// or a hand-written test). The verifier reads it; it does not allocate.
// This keeps the eigenvariable's identity intrinsic to the proof rather
// than dependent on which agent happens to interpret it.
//
// The op also binds a TermRef at this instr's index (for use by later
// Exists witnesses) — that TermRef resolves to `Term::fixed(eigen)`.
struct Forall {
    OpHeader  h{};
    size_t    principal{0};
    var_index eigen{};
};

// Exists: principal entries[principal] = ∃x.ϕ. Replace with ϕ[x:=witness]
// for the given TermRef.
struct Exists {
    OpHeader h{};
    size_t   principal{0};
    TermRef  witness{};
};

// =========================================================================
// Cut — Hughes §15 endorsed extension
// =========================================================================

// Cut: from Γ derive two subgoals
//   left  : Γ ∪ {φ_nnf}
//   right : Γ ∪ {¬φ_nnf}
// (Additive form. The multiplicative form `Γ,φ  Δ,¬φ ⊢ Γ,Δ` is admissibly
// equivalent via Contraction.) The next instruction operates on LEFT
// (pushed last); the one after LEFT closes operates on RIGHT.
struct Cut {
    OpHeader      h{};
    FormulaSource cut_formula{};
};

// =========================================================================
// Sum type
// =========================================================================
using Instr = std::variant<
    AxiomLit, One, CloseByLemma,
    Exchange, Weakening, Contraction,
    And, Or, Forall, Exists,
    Cut
>;

}  // namespace logic::proof::lkr
