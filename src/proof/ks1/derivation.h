#pragma once

// KS1 derivations (HSW 2021 Fig. 6) — Track 2 phase K2.
//
// A KS1 derivation transforms a `top` formula into a `bottom` formula by a
// sequence of deep-inference rule instances, read TOP-DOWN: each step rewrites
// an occurrence S{P} (the rule's premise, sitting at a context position) into
// S{Q} (its conclusion). Provability of A means a derivation from t (⊤) to A.
//
// Formulas are core::FormulaHandle in NNF (the LKR convention): a literal is a
// PredicateInstance or Compound{Not, atom}; ⊥ is Compound{Bottom}; the truth
// unit ⊤ = ¬⊥ = Compound{Not, Bottom}. No parallel KS1 formula type.
//
// The deep-inference context S{·} (paper §V) is represented by a `Path` from
// the formula root to the root of the redex subformula P. A rule rewrites that
// subformula in place; ancestors are rebuilt (formulas are interned/immutable).
// All KS1 contexts are positive (NNF has no connective negation), so no
// polarity tracking is needed.
//
// Rule schemas `S{P} / S{Q}` (premise over conclusion), exactly as Fig. 6
// (verified via pdftotext; see translate/KS1_TRACK2_DESIGN.md §4):
//
//   MLS1^X (linear core):
//     ForallUnit  S{t}            / S{∀x.t}
//     Ai          S{t}            / S{a ∨ ā}            (param: literal a)
//     Tu          S{A}            / S{A ∧ t}
//     Sw          S{A ∧ (B ∨ C)}  / S{(A ∧ B) ∨ C}
//     Mix         S{A ∧ B}        / S{A ∨ B}
//     Ex          S{A[x/t]}       / S{∃x.A}             (param: body A, term t)
//     Eqv         S{B}            / S{A}    (A ≡ B)     (param: equation+dir)
//   resource fragment:
//     W           S{A}            / S{A ∨ B}            (param: formula B)
//     WForall     S{A}            / S{∀x.A}  (x∉A)
//     Ac          S{a ∨ a}        / S{a}
//     CForall     S{∀x.∀x.A}      / S{∀x.A}
//     M           S{(A∧C) ∨ (B∧D)}/ S{(A∨B) ∧ (C∨D)}
//     MForall     S{(∀x.A)∨(∀x.B)}/ S{∀x.(A∨B)}
//     MExists     S{(∃x.A)∨(∃x.B)}/ S{∃x.(A∨B)}

#include "src/core/formula.h"

#include <vector>

namespace logic::proof::ks1 {

// One navigation step from a node to a child (paper context S{·}).
enum class Dir {
    Left,   // into a Compound's left operand
    Right,  // into a Compound's right operand
    Down,   // into a Quantified's body
};
using Path = std::vector<Dir>;

enum class Rule {
    ForallUnit, Ai, Tu, Sw, Mix, Ex, Eqv,        // MLS1^X
    W, WForall, Ac, CForall, M, MForall, MExists, // resource
};

// The eq (2) equivalence equations (HSW §II), each usable in both directions.
enum class EqRule {
    CommAnd,   // A ∧ B ≡ B ∧ A
    CommOr,    // A ∨ B ≡ B ∨ A
    AssocAnd,  // (A ∧ B) ∧ C ≡ A ∧ (B ∧ C)
    AssocOr,   // (A ∨ B) ∨ C ≡ A ∨ (B ∨ C)
    SwapForall,// ∀x.∀y.A ≡ ∀y.∀x.A
    SwapExists,// ∃x.∃y.A ≡ ∃y.∃x.A
    DistForall,// ∀x.(A ∨ B) ≡ (∀x.A) ∨ B   (x not free in B)
    DistExists,// ∃x.(A ∧ B) ≡ (∃x.A) ∧ B   (x not free in B)
};

// Direction the equation's LHS≡RHS is applied at the redex (premise→conclusion
// is read top-down, so the redex P is the LHS form for `Forward`).
enum class EqDir { Forward, Backward };

// One rule instance. `context` locates the redex P; the remaining fields are
// the rule's parameters (kind-tagged by `rule`, mirroring VertexLabel's flat
// record style — only the subset relevant to `rule` is meaningful).
struct Step {
    Rule          rule{};
    Path          context{};

    FormulaHandle f_param{};  // Ai: literal a;  W: formula B;  Ex: body A (Gen0=x)
    Term          t_param{};  // Ex: witness term t

    EqRule        eq{};       // Eqv: which eq(2) equation
    EqDir         dir{};      // Eqv: direction
};

// A derivation from `top` to `bottom` via `steps` (applied in order, top-down).
struct Derivation {
    FormulaHandle           top{};     // usually ⊤ for a proof of `bottom`
    FormulaHandle           bottom{};  // the derived formula (the theorem)
    std::vector<Step>       steps{};
};

}  // namespace logic::proof::ks1
