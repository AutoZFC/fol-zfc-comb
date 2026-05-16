# Next step: LKR → Combinatorial Proofs

Reference: Dominic J. D. Hughes, *First-order proofs without syntax*, arXiv 1906.11236, June 2019.

This document scopes the implementation of the combinatorial-proof construction that follows the LKR refactor and the ND→LKR translator already in place.

---

## 1. Goal

Given an LKR derivation `Π : LKRProgram` (verified by `LKRVerifier` against a goal formula `ϕ`), produce a combinatorial proof of `ϕ` per Hughes §11.1, extended for our admissible `Cut` op via §15.

This is the conceptual destination of the multi-system framework. The pipeline becomes:

```
ParsedProof  →  NDProgram  →  LKRProgram  →  CombinatorialProof
              (lower)       (translate)     (this pass)
```

A combinatorial proof is a graph-theoretic object — a *skew bifibration* `f : N → G(ϕ)` from a *fonet* `N` to the *fograph* `G(ϕ)` of the formula. It is verifiable in polynomial time (paper §13) and serves as the ultimate witness of validity, independent of any sequent-calculus syntax.

## 2. Soundness foundation

Hughes's main theorem (Theorem 6.4): a first-order formula is valid iff it has a combinatorial proof. The construction we implement is the *completeness* direction:

- **Lemma 11.1**: LKR is sound and complete (= GS1, Troelstra-Schwichtenberg).
- **§11.1**: each LKR rule's interpretation as an operation on combinatorial proofs.
- **Lemma 11.2**: each operation produces a well-defined combinatorial proof.
- **§11.2**: chaining the per-rule operations along a cut-free LKR derivation yields a combinatorial proof of the goal.

Our LKR contains the admissible extension `Cut`. We handle it via §15:

- **§15 / Theorem 15.1**: an *n-cut combinatorial proof* of `ϕ` is an ordinary (cut-free) combinatorial proof of `ϕ ∨ (θ1 ∧ ¬θ1) ∨ … ∨ (θn ∧ ¬θn)`. Each `θi` is a cut formula. Cut combinatorial proofs are sound and complete.

So our LKR `Cut(θ)` ops translate to *augmenting the goal formula* with a `θ ∧ ¬θ` disjunct, then proceeding with §11.1 over the augmented goal.

The remaining admissible extensions (`AxiomGen`, `UseTheorem`, `SchemaInst`) require their own treatment — see §6.3 of this doc.

## 3. Path choice: keep cuts (no cut-elimination)

Two paths to a combinatorial proof:

| Path | Steps | Trade-offs |
|---|---|---|
| **A — cut-free** | Cut-elimination at LKR level (Gentzen Hauptsatz) → §11.1 mapping → cut-free combinatorial proof. | Cleanest output. Cut-elimination at sequent level is well-studied. **Loses modularity**: each theorem use is inlined, blowing up proof size. |
| **B — cut-allowed (chosen)** | Keep `Cut` ops in LKR → §11.1 mapping over the §15-augmented goal → cut combinatorial proof. | Smaller. Preserves modularity (`UseTheorem` ↔ `Cut` ↔ §15 augmentation; theorem proofs stay separate). Matches §15 directly. |

**We choose Path B.** Rationale:
1. First-order cut-elimination at the *combinatorial-proof level* is an open problem in the paper (§17, "Conclusion and related work"). Doing it at the sequent level is feasible but unnecessary if §15 suffices.
2. Path B preserves library/modularity properties: each theorem's combinatorial proof is built once and referenced via the cut-augmentation mechanism.
3. The output is still a fully-fledged sound-and-complete combinatorial proof per Theorem 15.1.

## 4. Data structures (new)

A new package `src/proof/combinatorial/` containing the graph-theoretic types from paper §3-§6.

### 4.1 Fograph (paper §3)

```cpp
// src/proof/combinatorial/fograph.h
struct Fograph {
    // Vertices, each labelled with an atom/literal/binder.
    struct Vertex {
        enum Kind { Predicate, NegPredicate, Binder, Constant };
        Kind kind;
        // For Predicate / NegPredicate: which predicate symbol.
        PredicateHandle pred;
        std::vector<Term> args;
        // For Binder: ∀ or ∃, which variable.
        Op binder_op;     // Forall or Exists
        var_index var;
        // For Constant: 0 (=⊥) or 1 (=⊤).
        bool constant_one;
    };
    std::vector<Vertex> vertices;
    // Adjacency. Edges are between vertices in different "scope" relations.
    std::vector<std::pair<size_t, size_t>> edges;

    bool is_logical_cograph() const;       // §3 well-formedness
    bool binders_legal() const;            // Def. 3.2
};

// Algorithm: Fograph G(formula) from a formula in NNF.
Fograph build_fograph(FormulaHandle formula_nnf, FormulaBuilder& builder);
```

The `G(ϕ)` mapping is paper Def. 3.1: literals become vertices; ∧ becomes a +-node in modular decomposition (vertices in different submodules are *not* connected); ∨ becomes a ×-node (vertices in different submodules *are* connected); quantifiers add a labelled binder vertex at the appropriate scope. Implementation walks the NNF formula recursively, assembling vertices and edges per the modular decomposition recipe.

### 4.2 Linked fograph, dualizer, fonet (paper §5)

```cpp
// src/proof/combinatorial/fonet.h
struct LinkedFograph {
    Fograph base;
    // Colouring: maps each vertex to a colour class. Two vertices of the
    // same colour with dual literals form a "link".
    std::vector<int> colour;
};

struct Dualizer {
    // A perfect matching pairing each predicate vertex with its dual.
    std::vector<std::pair<size_t, size_t>> matching;
};

struct Fonet {
    LinkedFograph linked;
    Dualizer dualizer;
    // Invariants (Def. 5.3): has a dualizer, has no induced bimatching.
    bool valid() const;
};
```

### 4.3 Skew bifibration (paper §4)

```cpp
// src/proof/combinatorial/bifibration.h
struct SkewBifibration {
    const Fograph& source;       // K
    const Fograph& target;       // G
    // Vertex map K → G.
    std::vector<size_t> vertex_map;

    // Verify Def. 4.1: label-preserving, existential-preserving,
    // skew-fibration condition, directed-graph-fibration condition.
    bool verify() const;
};
```

### 4.4 Combinatorial proof (paper Def. 6.1)

```cpp
// src/proof/combinatorial/proof.h
struct CombinatorialProof {
    Fonet net;                    // The source N
    SkewBifibration bifibration;  // f : N → G(ϕ)
    FormulaHandle proved_formula;
};
```

A combinatorial proof of formula `ϕ` is a skew bifibration `f : N → G(ϕ)` from a fonet `N` (Def. 6.1).

## 5. The §11.1 translation pass

```cpp
// src/proof/translate/lkr_to_combinatorial.h
class LKRtoCombinatorial : public Pass<lkr::Instr, /* output: CombinatorialProof */> {
public:
    explicit LKRtoCombinatorial(GlobalContext& ctx);

    // Apply produces a CombinatorialProof from an LKRProgram.
    util::Result<CombinatorialProof> apply_to_proof(
        const Program<lkr::Instr>& prog,
        FormulaHandle goal_formula);
};
```

Implementation walks the LKR derivation tree (reconstructed from the flat instruction list) and applies §11.1's per-rule operation at each node. The reconstruction mirrors what `LKRVerifier` does internally — consume ops in order, maintaining an open-goals stack — except instead of just discharging goals we *build a combinatorial proof* for each goal and combine them at branching ops.

### 5.1 Per-rule operations

Implements paper §11.1 verbatim. Each operation takes the input combinatorial proof(s) and produces the output:

| LKR rule | Hughes rule | Operation (sketch) |
|---|---|---|
| `AxiomLit(a, b)` | `α, ᾱ` | `g = identity` on `α• •α`, both vertices same colour. |
| `One(idx)` | `1` | `g = identity` on `•1`, no colour. |
| `Exchange(i, j)` | `X` | `g = x ∘ f` where `x` is canonical iso `G(H) → G(C)`. |
| `Weakening(ϕ)` | `W` | `g = w ∘ f` where `w` is canonical injection. |
| `Contraction(i, j)` | `C` | Duplicator collapse on outer universal binders (footnote 24). |
| `And(p)` (additive)<sup>†</sup> | `∧` | Fusion of `K1, K2` at portions; weak/strong classification. |
| `Or(p)` | `∨` | `g = f` (target's graph equals hypothesis's graph). |
| `Forall(p)` | `∀` | Extend with `•x` if body uses `x`; else compose canonical injection. |
| `Exists(p, t)` | `∃` | Extend `Ks` with vertex `v` and edges to witness portions. |

<sup>†</sup> Our `And` is additive (both subgoals retain Γ). Hughes's `∧` is multiplicative. The additive form is admissible from multiplicative via `C`/`W`. The translator either: (a) emits a Hughes-multiplicative operation followed by contractions to recover the additive shape, or (b) implements an additive direct operation (admissible derived). Path (a) is simpler.

### 5.2 Cut handling (§15)

For each `Cut(θ)` op, the strategy:

1. **Augment the goal**: if the original goal is `ϕ`, the LKR `Cut(θ)` means we will need a combinatorial proof of `ϕ ∨ (θ ∧ ¬θ)`. Update the running "expected goal formula" to include the new cut disjunct.
2. **Build the cut-formula graph**: `G(θ ∧ ¬θ)` is straightforward — a +-node combining `G(θ)` and `G(¬θ)`. Compute it.
3. **Combine the two subgoal proofs**: the LKR `Cut` produces two subgoals (LEFT with `Γ ∪ {θ}`, RIGHT with `Γ ∪ {¬θ}`, additive). When both have been translated into combinatorial proofs `f_L` and `f_R`, fuse them via the `∧` rule's operation between the `θ` portion of `f_L` and the `¬θ` portion of `f_R` to obtain a combinatorial proof of `Γ ∨ (θ ∧ ¬θ)`. The `Γ` portions combine like the `∧` rule's Γ-handling.
4. **Repeat per cut**: each additional cut adds another `θi ∧ ¬θi` disjunct.

After all cuts are processed, the result is a combinatorial proof of `goal_formula ∨ (θ1 ∧ ¬θ1) ∨ … ∨ (θn ∧ ¬θn)`, which by Theorem 15.1 is sound for `goal_formula`.

### 5.3 Admissible-extension handling

| Extension | Hughes treatment | Implementation |
|---|---|---|
| `AxiomGen(a, b)` | Not in paper (paper has only `α, ᾱ`). | Eliminate to a sequence of structural rules (`Or`, `And`, `Forall`, `Exists`) that descend into both formulas in lockstep until atomic literals appear, then close via `AxiomLit`. Equivalently: implement `AxiomGen` as a derived rule that locally produces the equivalent §11.1 operations. |
| `UseTheorem(T)` | Not in paper. | Desugar to `Cut(T_formula)` whose right sub-derivation is the previously-built combinatorial proof of `T`. Requires `ProofRunner` to retain combinatorial proofs keyed by theorem name (see §6.3). |
| `SchemaInst(S, bindings)` | Not in paper. | Same as `UseTheorem` but instantiates the schema's body before using its combinatorial proof. |

## 6. Implementation phases

### Phase 0 — Fograph + verifier (independent, testable)

Build `src/proof/combinatorial/fograph.{h,cpp}` and a unit-tested `build_fograph` that produces `G(ϕ)` from an NNF formula. Add `Fograph::is_logical_cograph()` and `Fograph::binders_legal()` per Defs. 3.1, 3.2.

Build `src/proof/combinatorial/bifibration.{h,cpp}` with `SkewBifibration::verify()` per Def. 4.1.

Build `src/proof/combinatorial/fonet.{h,cpp}` with `Fonet::valid()` per Def. 5.3.

These three are pure data-structure work, independently testable against small hand-built examples (the four combinatorial proofs in Fig. 2 of the paper make excellent fixtures).

### Phase 1 — `CombinatorialProofVerifier`

Implement a polynomial-time verifier (paper §13) that, given a `CombinatorialProof` and a formula, checks soundness:

1. Verify `f.target == G(ϕ)`.
2. Verify `f.source` (`N`) is a fonet (Def. 5.3).
3. Verify `f` is a skew bifibration (Def. 4.1).

Expose as `CombinatorialProofVerifier::verify(CombinatorialProof, FormulaHandle)`.

This verifier is independent of the §11.1 translator: any combinatorial proof object — however constructed — can be checked. It is the soundness witness for the framework's combinatorial output.

### Phase 2 — §11.1 translator (cut-free LKR)

Implement `LKRtoCombinatorial::apply_to_proof` for the cut-free fragment:

- Process each LKR rule per §11.1's specified operation.
- Maintain a combinatorial-proof stack mirroring the verifier's open-goals stack.
- Branching ops (`And`) pop two proofs, fuse, push one.
- Linear ops apply their operation in place.
- Closing ops produce a final combinatorial proof for the goal.

Test: for each successful translation of a corpus proof through ND→LKR (currently 73/84 modulo equality), apply LKR→combinatorial and check via the verifier from Phase 1.

### Phase 3 — Cut handling (§15)

Extend `LKRtoCombinatorial` for `Cut` ops:

- Track cut formulas as the derivation unfolds.
- At cut points, fuse the LEFT and RIGHT sub-derivations' combinatorial proofs via the `∧` operation between the `θ` and `¬θ` portions.
- Augment the final goal formula with `θ ∧ ¬θ` disjuncts per cut.
- Final combinatorial proof is over the augmented goal; the verifier checks it against that augmented form.

### Phase 4 — Admissible extensions

- `AxiomGen` reduction: emit the structural-induction sequence inline. Or alternatively, pre-process the LKR program to replace each `AxiomGen` with the equivalent rule sequence before §11.1 mapping.
- `UseTheorem` / `SchemaInst`: extend `ProofRunner` to retain a combinatorial proof per theorem (alongside the formula). Translator looks them up at `UseTheorem` ops and embeds via Cut-style fusion.

### Phase 5 — Test depth + corpus regression

- `combinatorial_smoke_test`: hand-built combinatorial proofs from paper Fig. 2 as fixtures; verify Phase-1 verifier accepts.
- `lkr_to_combinatorial_test`: small LKR programs, check round-trip via Phase-1 verifier.
- `corpus_combinatorial_test`: extend the existing `nd_to_lkr_corpus_test` to additionally produce + verify a combinatorial proof for each successfully-translated proof. Soundness gate: any failure is a bug in either §11.1's implementation or the augmented-goal handling.

## 7. Out of scope

The following are documented as future work:

- **Equality**. Hughes' paper is FOL without equality. Adding combinatorial-proof support for equality is open research. Our 11 corpus rejections that depend on `EqSubst`/`EqSym` remain unaddressed.
- **Cut-elimination at the combinatorial-proof level**. Open per §17. Not required: Theorem 15.1 says cut combinatorial proofs are already sound and complete.
- **Cut-elimination at the LKR level**. Possible (Gentzen Hauptsatz), but not on this roadmap. We chose Path B above.
- **Theorem-proof inlining**. Would lose modularity; supplanted by `Cut`-via-§15.
- **Intuitionistic combinatorial proofs**. Open per §17.
- **Definite descriptions / iota terms**. Not in the paper; not in our LKR.

## 8. Estimated scope

| Phase | Approx. lines | Approx. effort |
|---|---|---|
| 0 — fograph + bifibration + fonet types | ~400 | 1-2 days |
| 1 — combinatorial-proof verifier | ~300 | 1 day |
| 2 — §11.1 translator (cut-free) | ~600 | 2-3 days |
| 3 — cut handling (§15) | ~200 | 1 day |
| 4 — admissible-extension reductions | ~300 | 1-2 days |
| 5 — tests + corpus regression | ~400 | 1-2 days |
| **Total** | **~2200** | **~7-11 days focused** |

## 9. Soundness contract

At each phase boundary the soundness chain is:

1. ND verifier proves the original ND derivation is valid.
2. ND→LKR translator emits an LKR derivation, verified by `LKRVerifier`.
3. LKR→combinatorial translator emits a combinatorial proof, verified by `CombinatorialProofVerifier` (Phase 1).
4. The combinatorial proof's existence witnesses the goal formula's classical validity by Theorem 6.4 + Theorem 15.1.

Each verifier is independent. A bug at any layer surfaces as a verification failure at that layer — never as silent unsoundness in a later layer. The translators are *not* trusted; the verifiers are.

## 10. References

- Hughes 2019 (arXiv 1906.11236) §3, §4, §5, §6, §11, §13, §15, §17.
- Gentzen 1934 (Hauptsatz / cut-elimination) — referenced for Path A; not on chosen path.
- Troelstra-Schwichtenberg 2000, *Basic Proof Theory* §3.5.2 (GS1) — referenced for LKR equivalence.
- Hughes 2006a, *Proofs without syntax* (propositional case) — referenced for context.

---

*Status: planning. No code in `src/proof/combinatorial/` yet. The current LKR + ND→LKR pipeline (commits `dfc8f4c`, `ca0971a`) provides everything Phase 0 needs as input.*
