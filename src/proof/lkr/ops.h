#pragma once

// LKR op structs and the lkr::Instr variant.
//
// LKR = one-sided, multi-conclusion, classical sequent calculus following
// Hughes 2019, "First-order proofs without syntax", §11. The core nine
// rules are equivalent to Troelstra-Schwichtenberg's GS1 (Basic Proof
// Theory, 2000, §3.5.2): sound and complete for classical first-order
// logic.
//
// Sequent shape: a single vector<FormulaHandle> in NNF. There is no
// antecedent. Formulas are restricted to literals + ∧ + ∨ + ∀ + ∃ + ⊥;
// → and ↔ are eliminated by the NNF pass before LKR sees them.
//
// =========================================================================
// Layering: core (Hughes 2019 §11) + admissible extensions
// =========================================================================
//
// HUGHES CORE (the nine rules of LKR as defined in §11, verbatim):
//   AxiomLit (α, ᾱ)   — atomic-literal duality close.
//   One       (1)     — top-as-literal close.
//   Exchange  (X)     — swap two entries.
//   Weakening (W)     — append a formula.
//   Contraction (C)   — drop an α-equivalent duplicate.
//   And       (∧)     — split principal A ∧ B.
//   Or        (∨)     — unfold principal A ∨ B.
//   Forall    (∀)     — introduce eigenvariable for principal ∀x.ϕ.
//   Exists    (∃)     — instantiate principal ∃x.ϕ with witness.
//
// These nine, plus the structural well-formedness invariants, are the
// formal system. A proof using only these is a Hughes-core proof and is
// directly translatable to a combinatorial proof per §11.1.
//
// ADMISSIBLE EXTENSIONS (each with a derivation back to core):
//
//   Cut        — Gentzen's cut rule. Admissible by Gentzen's Hauptsatz
//                (1934); cut-elimination converts Cut-using proofs to
//                cut-free Hughes-core proofs. Hughes acknowledges Cut as
//                an extension in §11.2: "Just as sequent calculus proofs
//                may include cuts, combinatorial proofs can be extended."
//                Implemented here in additive form (both subgoals retain
//                Γ); the additive-from-multiplicative-via-contraction
//                derivation is standard (Troelstra-Schwichtenberg §3.1).
//
//   AxiomGen   — closure on NNF-dual non-atomic formulas. Admissible from
//                AxiomLit by structural induction: any A and ¬A_NNF can
//                be reduced via Or/And/Forall/Exists rules (matching the
//                connective trees in lockstep) until atomic literal pairs
//                appear, which AxiomLit closes. Promoted to a primitive
//                here for translator efficiency; an "AxiomGen elimination"
//                pass would restore Hughes-core form.
//
//   UseTheorem — closure when some entry equals NNF(named theorem's root).
//                Admissible by inlining: a verified theorem T has its own
//                LKR proof π_T deriving [T_nnf]; replace each UseTheorem(T)
//                with π_T followed by Weakening + Exchange to produce
//                Γ ∪ {T_nnf}. Conservative theory extension.
//
//   SchemaInst — closure on a proven-schema instantiation. Same admissibility
//                pattern as UseTheorem: each schema's verified-once body
//                π_S can be re-instantiated and inlined.
//
// All four extensions are eliminable: an extended-LKR proof can be
// transformed into a Hughes-core proof by repeated application of the
// admissibility theorems above. For combinatorial-proofs work (Hughes'
// main theorem), the elimination passes produce the pure-Hughes form
// the combinatorial-proof construction expects.
//
// =========================================================================
// Op stream semantics (operational)
// =========================================================================
//
// Each op operates on the top of an open-goals stack:
//   * "closing" ops (AxiomLit, AxiomGen, One, UseTheorem, SchemaInst):
//      pop the current goal.
//   * "linear" ops (Exchange, Weakening, Contraction, Or, Forall, Exists):
//      replace the current goal with one new goal.
//   * "branching" ops (And, Cut): pop the current goal, push two new
//      ones (depth-first; the second is on top so the next instruction
//      operates on it).
//
// LKR has no Qed: success is termination of the instr stream with an
// empty open_goals stack.

#include "../../core/formula.h"
#include "../../parser/formula_ast.h"
#include "../ir.h"

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
// Closing rules
// =========================================================================

// [HUGHES CORE — §11 axiom rule "α, ᾱ"]
// AxiomLit: close the current goal when entries[lit_a] and entries[lit_b]
// are dual atomic literals (one is +L, the other is −L for the same
// atom L). Other entries are admissibly weakened away via Hughes' W rule
// (the closing rule produces the empty witness sequent; Weakening then
// adds back the rest).
struct AxiomLit {
    OpHeader h{};
    size_t   lit_a{0};
    size_t   lit_b{0};
};

// [ADMISSIBLE EXTENSION — eliminable to AxiomLit by structural induction]
// AxiomGen: close the current goal when entries[a] and entries[b] are
// NNF duals (any formula pair where one is to_nnf(¬other)). Derivable
// in Hughes core by descending into both formulas in lockstep using
// Or/And/Forall/Exists rules until atomic-literal pairs appear, which
// close via AxiomLit. Promoted to a primitive for translator efficiency;
// an elimination pass would restore Hughes-core form.
struct AxiomGen {
    OpHeader h{};
    size_t   a{0};
    size_t   b{0};
};

// [HUGHES CORE — §11 "1" rule]
// One: close the current goal when entries[idx] is the top-as-literal
// placeholder ¬⊥. Rare in practice but part of the formal calculus.
struct One {
    OpHeader h{};
    size_t   idx{0};
};

// [ADMISSIBLE EXTENSION — eliminable by theorem-proof inlining + Weakening]
// UseTheorem: close the current goal iff some entry equals
// NNF(theorem.root). Conservative theory extension: each verified theorem
// has an LKR proof π_T deriving [T_nnf]; UseTheorem(T) is shorthand for
// inlining π_T then admissibly weakening to add the surrounding context.
struct UseTheorem {
    OpHeader h{};
    AxiomRef axiom{};
};

// [ADMISSIBLE EXTENSION — eliminable like UseTheorem, with schema instantiation]
// SchemaInst: close the current goal iff some entry equals
// NNF(instantiated schema body). Same theorem-inlining justification as
// UseTheorem, applied after schema instantiation.
struct SchemaInst {
    OpHeader       h{};
    SchemaInstData data{};
};

// =========================================================================
// Structural rules — Hughes core (§11 X / W / C)
// =========================================================================

// [HUGHES CORE — §11 X rule]
// Exchange: swap entries[i] and entries[j].
struct Exchange {
    OpHeader h{};
    size_t   i{0};
    size_t   j{0};
};

// [HUGHES CORE — §11 W rule]
// Weakening: append `formula` to the entries.
struct Weakening {
    OpHeader      h{};
    FormulaSource formula{};
};

// [HUGHES CORE — §11 C rule]
// Contraction: remove entries[j] when entries[i] == entries[j] (alpha-
// equivalence captured via FormulaHandle equality, since the global
// formula registry interns alpha-equivalent forms to the same handle).
struct Contraction {
    OpHeader h{};
    size_t   i{0};
    size_t   j{0};
};

// =========================================================================
// Logical rules — Hughes core (§11 ∧ / ∨ / ∀ / ∃)
// =========================================================================

// [HUGHES CORE — §11 ∧ rule, additive presentation]
// And: principal entry entries[principal] = ϕ ∧ θ. Two subgoals.
// Hughes' multiplicative form is `Γ, ϕ   Δ, θ ⊢ Γ, Δ, ϕ ∧ θ` (Γ and Δ
// split between premises). The additive form `Γ, ϕ   Γ, θ ⊢ Γ, ϕ ∧ θ`
// (both retain all of Γ) is provably equivalent in Hughes core via
// Contraction; we use the additive form for translator simplicity.
struct And {
    OpHeader h{};
    size_t   principal{0};
};

// [HUGHES CORE — §11 ∨ rule]
// Or: principal entries[principal] = ϕ ∨ θ. Replace with two adjacent
// entries ϕ, θ.
struct Or {
    OpHeader h{};
    size_t   principal{0};
};

// [HUGHES CORE — §11 ∀ rule]
// Forall: principal entries[principal] = ∀x.ϕ. Introduce a fresh
// eigenvariable (TermRef bound at this instr's index); replace
// principal with ϕ[x:=eigen]. Side condition: eigen must not occur
// free in any other entry (Hughes' "x not free in Γ" condition).
struct Forall {
    OpHeader h{};
    size_t   principal{0};
};

// [HUGHES CORE — §11 ∃ rule]
// Exists: principal entries[principal] = ∃x.ϕ. Replace principal with
// ϕ[x:=witness] for the given TermRef.
struct Exists {
    OpHeader h{};
    size_t   principal{0};
    TermRef  witness{};
};

// =========================================================================
// Cut — admissible extension (Hughes §11.2; eliminable via Hauptsatz)
// =========================================================================

// [ADMISSIBLE EXTENSION — eliminable to Hughes core via cut-elimination]
// Cut: from goal Γ, generate two subgoals
//   left  : Γ ∪ {ϕ_nnf}
//   right : Γ ∪ {¬ϕ_nnf}
// Both subgoals retain all of Γ (additive form). Hughes' multiplicative
// cut `Γ, ϕ   Δ, ¬ϕ ⊢ Γ, Δ` is admissible in classical sequent calculus
// (Gentzen 1934 Hauptsatz); the additive variant is provably equivalent
// via Contraction. Hughes acknowledges Cut as an extension in §11.2.
// Order on the stack: right pushed first (deeper), left on top.
struct Cut {
    OpHeader      h{};
    FormulaSource cut_formula{};
};

// =========================================================================
// Sum type
// =========================================================================
using Instr = std::variant<
    AxiomLit, AxiomGen, One, UseTheorem, SchemaInst,
    Exchange, Weakening, Contraction,
    And, Or, Forall, Exists,
    Cut
>;

}  // namespace logic::proof::lkr
