#pragma once

// Natural-deduction op structs and the nd::Instr variant.
//
// Each op is a struct holding exactly the fields its rule requires.
// Instr is the sum type formed by std::variant; an exhaustive std::visit
// over a fully-typed Instr is a compile-time-checked dispatch table.
//
// Soundness contract per op is documented in the design's per-op semantic
// table; the verifier (src/proof/nd/verifier.cpp) realizes that table by
// routing each op to the corresponding ClassicalProofStack method.
//
// Naming convention: each op takes "result"-bound StepRefs/TermRefs by the
// instr index of the producing instruction. There is no `result` field on
// any op — the producing instruction's index *is* the StepRef/TermRef the
// op binds.

#include "src/parser/formula_ast.h"   // ASTNode (deferred formula payloads)
#include "src/proof/ir.h"

#include <memory>
#include <optional>
#include <variant>

namespace logic::proof::nd {

// =========================================================================
// Scope-opening ops
// =========================================================================
// Fix introduces a fresh fixed variable. The op's instr-index serves as the
// canonical TermRef binding. var_name is recorded so that subsequent
// deferred formulas (Assume/Let) can reference the source-level name.
struct Fix {
    OpHeader  h{};
    ScopeName var_name{};
};

// Assume opens an assumption scope and derives its formula. The deferred
// AST is parsed at execute time against the verifier's name->Term table,
// matching today's runtime behavior.
//
// `resolved`, if set, supplies the assumed formula directly and bypasses
// AST parsing. This path exists for translator-synthesized Assume ops
// (e.g., axiom_rewrap's boundary `assume H`) where the formula is already
// a closed sentence built via FormulaBuilder and has no source-level
// var-name dependencies. Mutually exclusive with `formula` in practice:
// lowering sets `formula` (AST-deferred); translators set `resolved`.
struct Assume {
    OpHeader h{};
    std::shared_ptr<ASTNode>      formula{};
    std::optional<FormulaHandle>  resolved{};
};

// Let creates a formula handle without deriving it. Used as a payload for
// or_intro_l / or_intro_r and the classical ops that need formula handles
// for their "untouched" disjunct/operand. Same deferred-AST treatment.
struct Let {
    OpHeader h{};
    std::shared_ptr<ASTNode> formula{};
};

// =========================================================================
// Theory imports
// =========================================================================
// Use pulls a previously-proven axiom or theorem in by name. The name is
// resolved against GlobalContext at execute time.
struct Use {
    OpHeader h{};
    AxiomRef axiom{};
};

// SchemaInst instantiates a proven schema with concrete bindings.
struct SchemaInst {
    OpHeader       h{};
    SchemaInstData data{};
};

// =========================================================================
// Conjunction
// =========================================================================
struct AndIntro { OpHeader h{}; StepRef a{}; StepRef b{}; };
struct AndElimL { OpHeader h{}; StepRef of{}; };
struct AndElimR { OpHeader h{}; StepRef of{}; };

// =========================================================================
// Disjunction
// =========================================================================
// or_intro_l/r in ProofStack take a derived formula and an "other-side
// formula handle" (which is allowed to be a Let-bound, undelivered
// formula). We keep both fields strongly named.
struct OrIntroL { OpHeader h{}; StepRef a{};         StepRef b_formula{}; };
struct OrIntroR { OpHeader h{}; StepRef a_formula{}; StepRef b{};         };
struct OrElim   { OpHeader h{}; StepRef or_formula{}; StepRef ac{}; StepRef bc{}; };

// =========================================================================
// Implication
// =========================================================================
struct ImpliesIntro { OpHeader h{}; StepRef conclusion{}; };
struct ImpliesElim  { OpHeader h{}; StepRef impl{}; StepRef ant{}; };

// =========================================================================
// Negation
// =========================================================================
struct NotIntro { OpHeader h{}; StepRef bottom{}; };
struct NotElim  { OpHeader h{}; StepRef negation{}; StepRef formula{}; };

// =========================================================================
// Bottom
// =========================================================================
struct BottomElim { OpHeader h{}; StepRef bottom{}; StepRef target_formula{}; };

// =========================================================================
// Biconditional
// =========================================================================
struct IffIntro { OpHeader h{}; StepRef ab{}; StepRef ba{}; };
struct IffElimL { OpHeader h{}; StepRef iff{}; StepRef a{}; };
struct IffElimR { OpHeader h{}; StepRef iff{}; StepRef b{}; };

// =========================================================================
// Quantifiers
// =========================================================================
struct ForallIntro { OpHeader h{}; StepRef body{}; };
struct ForallElim  { OpHeader h{}; StepRef formula{}; TermRef term{}; };

// ExistsIntro: with explicit witness, derives ∃x.body from body[t]. Without
// witness, closes the current Exists scope.
struct ExistsIntro {
    OpHeader h{};
    StepRef body{};
    std::optional<TermRef> witness{};
};

// ExistsElim opens an Exists scope on a derived ∃x.φ; the introduced fresh
// var becomes a TermRef bound at this instr's index. bind_witness, when
// present, names the fresh var so subsequent deferred formulas can refer to
// it by source name (matches today's `exists_elim h, witness_name` form).
struct ExistsElim {
    OpHeader h{};
    StepRef formula{};
    std::optional<ScopeName> bind_witness{};
};

// =========================================================================
// Equality
// =========================================================================
struct EqSubst { OpHeader h{}; StepRef eq_formula{}; StepRef target{}; };
struct EqSym   { OpHeader h{}; StepRef eq_formula{}; };

// =========================================================================
// Classical extensions
// =========================================================================
struct DoubleNegElim   { OpHeader h{}; StepRef of{}; };
struct ExcludedMiddle  { OpHeader h{}; StepRef formula_let{}; };
struct ClassicalAbsurd { OpHeader h{}; StepRef bottom{}; };
struct Peirce          { OpHeader h{}; StepRef a_let{}; StepRef b_let{}; };

// =========================================================================
// Definite descriptions
// =========================================================================
// IotaElim binds a TermRef at this instr's index for the produced iota
// term, optionally exposing it under a source-level name.
struct IotaElim {
    OpHeader h{};
    StepRef  exists_formula{};
    std::optional<ScopeName> bind_iota{};
};

// =========================================================================
// Termination
// =========================================================================
// Qed names the step whose derivation is the proof's conclusion.
struct Qed { OpHeader h{}; StepRef derived{}; };

// =========================================================================
// Sum type
// =========================================================================
using Instr = std::variant<
    Fix, Assume, Let, Use, SchemaInst,
    AndIntro, AndElimL, AndElimR,
    OrIntroL, OrIntroR, OrElim,
    ImpliesIntro, ImpliesElim,
    NotIntro, NotElim, BottomElim,
    IffIntro, IffElimL, IffElimR,
    ForallIntro, ForallElim, ExistsIntro, ExistsElim,
    EqSubst, EqSym,
    DoubleNegElim, ExcludedMiddle, ClassicalAbsurd, Peirce,
    IotaElim,
    Qed
>;

}  // namespace logic::proof::nd
