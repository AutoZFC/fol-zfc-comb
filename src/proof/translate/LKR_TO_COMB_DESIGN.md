# LKR → Combinatorial Proofs: Mathematical Specification

Reference: Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236,
§11.1 (LKR-rule operations on combinatorial proofs) + §15 (cut handling).

This document specifies the LKR → CombProof translator at the math level.
The C++ implementation in `src/proof/translate/lkr_to_comb/` realises it
faithfully; correctness rests on `CombVerifier` accepting the output.

## 0. Status

In design. Translator not yet implemented. The receiving infrastructure
(`src/proof/comb/`: `comb_proof.h`, `fograph.cpp`, `cotree.{h,cpp}`,
`leap.{h,cpp}`, `verifier.{h,cpp}`) is in place.

## 1. Scope

**Input.** `Program<lkr::Instr>` produced by `NDtoLKR` (or any other
source) and accepted by `LKRVerifier`. Iota-free, eq_subst-free (the
LKR rule set already forbids these; the upstream pipeline enforces it).

**Output.** `comb::CombProof` accepted by `comb::CombVerifier` against
the (possibly augmented per §15) goal formula.

**Goal.** Build, in one pass over the LKR derivation tree, a combinatorial
proof `(N, G(φ), f)` that witnesses validity of φ classically.

**Trust boundary.** The translator is not trusted; `CombVerifier` is.

## 2. Math

### 2.1 Combinatorial proof (paper Def. 6.1)

A combinatorial proof of formula φ is a triple `(N, G, f)`:
- `G = G(φ)` — the fograph of φ (paper §3, Def. 3.1).
- `N` — a fonet (paper §5, Def. 5.3): a linked fograph with a dualizer
  and no induced bimatching.
- `f : V_N → V_G` — a skew bifibration (paper §4, Def. 4.1).

Soundness (Hughes Theorem 6.4): φ is classically valid iff it has a
combinatorial proof.

### 2.2 LKR-rule operations on combinatorial proofs (paper §11.1)

For each LKR rule whose verifier-execution turns hypothesis sequent(s)
`H` into conclusion sequent `C`, paper §11.1 defines how to build a
combinatorial proof of `Φ(C)` from combinatorial proof(s) of `Φ(H)`,
where `Φ(Γ) = ⋁ Γ`.

Notation. Each LKR rule's operation:
| LKR op | Hypotheses → Conclusion | Effect on `(N, f)` |
|---|---|---|
| `AxiomLit(α, ᾱ)` | (none) → `α, ᾱ` | Build base `N = {u_α, u_ᾱ}` linked; `f = id` to `G(α, ᾱ) = •α + •ᾱ`. |
| `One(idx)` | (none) → `1` | Build base `N = {u_1}` unlinked; `f = id` to `G(1) = •1`. |
| `Exchange(i, j)` | `Γ, φ, θ, Δ` → `Γ, θ, φ, Δ` | Compose `f` with canonical isomorphism `G(H) ≅ G(C)` (cograph `+` is commutative). |
| `Weakening(φ)` | `Γ` → `Γ, φ` | `N` unchanged; `f` composed with canonical injection `G(Γ) ↪ G(Γ) + G(φ)`; new vertices uncovered. |
| `Contraction(i, j)` | `Γ, φ, φ'` → `Γ, φ` | Compose `f` with surjection folding `G(φ')` onto `G(φ)`; collapse *duplicators* (outer universal binders with two preimages). Paper footnote 24. |
| `And(p, partition)` | `Γ_1, φ_1` and `Γ_2, φ_2` → `Γ_1, Γ_2, φ_1 ∧ φ_2` | Fuse `N_1, N_2` at witness portions; strong/weak classification (paper §11.1 ∧-case). |
| `Or(p)` | `Γ, φ, θ` → `Γ, φ ∨ θ` | `N` unchanged; `f` unchanged (cograph `+` is associative → graphs equal). |
| `Forall(p, v)` | `Γ, φ` → `Γ, ∀x.φ` (`x` not free in `Γ`) | If preimage of `G(φ)` is non-empty in `N`, add `•x` binder vertex; otherwise compose with canonical injection. |
| `Exists(p, t)` | `Γ, φ{x↦t}` → `Γ, ∃x.φ` | If preimage of `G(φ{x↦t})` non-empty, add new skeleton vertex `v` with edges to preimage; map `v ↦ •x`. |
| `Cut(θ)` | `Γ, θ` and `Γ, ¬θ` → `Γ` (augmented per §15) | Apply ∧-rule's fusion between θ-portion of LEFT and ¬θ-portion of RIGHT; augment running goal with `θ ∧ ¬θ` disjunct. |
| `CloseByLemma(L)` | (none) → (any containing `φ_L`) | Push `L`'s pre-built combinatorial proof, applied to the current goal sequent. |

### 2.3 Cut handling (paper §15, Theorem 15.1)

An *n-cut combinatorial proof* of φ is, by definition, an ordinary
combinatorial proof of

```
φ ∨ ⋁_{i=1..n} (θ_i ∧ ¬θ_i)
```

Each `θ_i` is a cut formula. Theorem 15.1 says cut combinatorial proofs
are sound and complete. So we keep `Cut` ops in LKR and *augment the
goal formula* at translation time.

This is Path B from `src/proof/COMBINATORIAL_PROOFS.md` §3 — chosen
because cut-elimination at the combinatorial-proof level is an open
problem (paper §17), and §15 provides a complete alternative.

### 2.4 `CloseByLemma` (§15-endorsed extension)

Two strategies:
- **Strategy A (inline)**: substitute the lemma's combinatorial proof
  in-place. Loses modularity; proof size blows up.
- **Strategy B (cut-via-§15)**: require `CloseByLemma(L)` be the LEFT
  closer of a preceding `Cut(φ_L)`. Then the §15 augmentation accounts
  for the lemma's role automatically; the LEFT subgoal's combinatorial
  proof is the lemma's, pulled from a registry.

We choose **Strategy B**. Implementation note: when the translator
encounters `CloseByLemma(L)` without a paired `Cut(φ_L)`, it fails
(precondition violation).

## 3. Architecture

```
                  Program<lkr::Instr>
                          │
                          ▼
                ┌───────────────────┐
                │   input gate      │  Run LKRVerifier (input contract);
                │                   │  reject if it doesn't verify.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   tree rebuild    │  Reconstruct branching tree from
                │                   │  the flat op stream by tracking
                │                   │  the open-goals stack.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   §11.1 walk      │  Per-rule operations on the
                │                   │  combinatorial-proof state stack.
                │                   │  §15 Cut augments the running
                │                   │  goal formula.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   output gate     │  CombVerifier::verify against
                │                   │  the augmented goal.
                └─────────┬─────────┘
                          ▼
                    comb::CombProof
```

### 3.1 Pass shape

```cpp
class LKRtoComb {
public:
    LKRtoComb(GlobalContext& ctx, FormulaHandle goal_formula,
              const TheoremCombProofs& lemma_registry);

    util::Result<comb::CombProof> apply(const Program<lkr::Instr>& in);
};
```

The output type is `comb::CombProof`, not `Program<comb::Instr>` — Comb
is not an instruction stream; it is a graph-theoretic object. So this
Pass deviates from `Pass<From, To>` in its output shape. We provide a
parallel `apply(prog) -> Result<CombProof>` interface.

`TheoremCombProofs` is the registry that holds previously-translated
lemma combinatorial proofs, keyed by lemma name. Strategy B's
`CloseByLemma(L)` looks up `L` here.

### 3.2 Tree rebuild

LKR is consumed by a stack-based verifier. The translator must
reconstruct the *branching tree* of the derivation:

```
TreeNode ::= Closing { op : AxiomLit | One | CloseByLemma }
           | Linear  { op : Exchange | Weakening | Contraction
                          | Or | Forall | Exists, child : TreeNode }
           | Branching { op : And | Cut, left : TreeNode, right : TreeNode }
```

Algorithm:
1. Walk `prog.instrs` linearly maintaining a stack of "open" tree nodes.
2. Each closing op finalises the top open node into a leaf and pops.
3. Each linear op attaches itself to the top open node as a child wrapper.
4. Each branching op pushes two open nodes (LEFT and RIGHT subgoals).

After the walk, the stack contains exactly one finalised root.

### 3.3 §11.1 walk

```cpp
struct CombProofState {
    comb::Fonet               source;
    comb::Fograph             target;
    std::vector<size_t>       fibration;
    // Plus internal modular-decomposition cache for binder additions.
};
```

Recursive translation `translate(node) → CombProofState`:
- Leaves: build the base `(N, G, f)` per the rule (AxiomLit, One,
  CloseByLemma).
- Linear: recurse on child, then apply the per-rule transformation to
  the returned state.
- Branching: recurse on both children, fuse per the rule.

At the root, `state.target == G(augmented_goal)`. Package into
`comb::CombProof` and return.

### 3.4 Goal augmentation

Track a `vector<FormulaHandle> cut_formulas` during the walk. Each `Cut(θ)`
appends `θ` to this list. The "augmented goal" is

```
goal_nnf ∨ ⋁ (θ_i ∧ ¬θ_i)
```

The output `CombProof.target` is `G(augmented_goal)`, and the output
gate runs `CombVerifier::verify` against the augmented goal (not the
original goal). The augmented goal is classically equivalent to the
original (each `θ ∧ ¬θ` is contradictory), so it's a valid witness for
the original goal.

## 4. Per-rule operations (Hughes §11.1, in detail)

For each rule, we record: the inputs (combinatorial proof(s) of
hypothesis sequent(s)), the conclusion sequent, the per-rule operation
on the (`N`, `f`) state.

### 4.1 `AxiomLit(α, ᾱ)`

Base: `N = {u_α, u_ᾱ}` with one link `{u_α, u_ᾱ}`; `G(C) = •α + •ᾱ`;
`f = { u_α ↦ •α, u_ᾱ ↦ •ᾱ }`. Empty dualizer.

### 4.2 `One(idx)`

Base: `N = {u_1}` (no link); `G(C) = •1`; `f = { u_1 ↦ •1 }`. Empty
dualizer.

### 4.3 `Exchange(i, j)`

Cograph commutativity. `N` unchanged; `f' = π ∘ f` where `π : G(H) → G(C)`
is the canonical bijection swapping the positions of `φ` and `θ`. If
vertex identity is by occurrence rather than position, `π = id` and
Exchange is a no-op.

### 4.4 `Weakening(φ)`

`G(C) = G(H) + G(φ)`. `N` unchanged. `f' = ι ∘ f` where `ι : G(H) ↪ G(C)`
is the canonical injection. The new `G(φ)` vertices are *uncovered* in
`f`.

### 4.5 `Contraction(i, j)` (φ' ≡_α φ)

`G(C) = G(H) - G(φ')` (one copy of `G(φ)` removed). `f` composed with
the surjection `c : G(H) ↠ G(C)` folding `G(φ')` onto `G(φ)`. Then:

**Duplicator collapse.** Any outer universal binder `b ∈ V_{G(C)}` with
`|f⁻¹(b)| = 2` becomes a *duplicator*. Delete one of its two preimages
from `N`. Paper footnote 24 explains why this preserves fonet
well-formedness.

### 4.6 `Or(p)`

Cograph associativity. `G(H) = G(C)` identically. `f, N` unchanged. The
cheapest rule.

### 4.7 `Forall(p, v)`

`G(C) = G(Γ) + (•v + G(φ))`. Let `P = f⁻¹(V_{G(φ)})` (the *φ-portion*).

- **Case A** (`P = ∅`): `G(φ)` was weakened in. `N` unchanged; `f' = ι ∘ f`
  with `•v` uncovered.
- **Case B** (`P ≠ ∅`): add new vertex `b_v ∈ V_N`. New source `N' = {b_v} ∪ V_N`
  with no new edges (universal binder is `+`-attached). Map
  `f' = (ι ∘ f) ∪ { b_v ↦ •v }`.

The scope condition (`v` not free in `Γ`) is the LKR-side check; for
the combinatorial proof it's encoded in the fograph structure.

### 4.8 `Exists(p, t)`

`G(C) = G(Γ) + (•x × G(φ))`. Let `P = f⁻¹(V_{G(φ{x↦t})})` (the *witness
portion*).

- **Case A** (`P = ∅`): `φ` was weakened in. `N` unchanged; `f' = ι ∘ f`.
- **Case B** (`P ≠ ∅`): add new vertex `v ∈ V_N` with edges `{v, w}` for
  every `w ∈ P` (because `•x` is `×`-attached to `G(φ)`'s vertices).
  Map extension: `v ↦ •x`. Dualizer extended: `δ(x) = t` (the witness).
  The dependency `x ↦ t` may introduce leap edges if `t` contains a
  universal-bound variable.

### 4.9 `And(p, partition)` (multiplicative)

`G(C) = G(Γ_1) + G(Γ_2) + (G(φ_1) × G(φ_2))`. Note the join.

`P_i = f_i⁻¹(V_{G(φ_i)})` are the *witness portions*.

**Strong/weak classification** (paper §11.1):
- `f_i` is *strong* if `P_i ≠ ∅`.
- `f_i` is *weak* if `P_i = ∅`.

**Case (both strong) or (both weak):**
Fuse `N_1, N_2` at portions `P_1, P_2`:
- `V_N = V_{N_1} ⊔ V_{N_2}`.
- `E_N = E_{N_1} ∪ E_{N_2} ∪ (P_1 × P_2)` (cograph edges joined).
- Links inherited from both.
- `f = (ι_1 ∘ f_1) ∪ (ι_2 ∘ f_2)`.

**Case (one weak, one strong):**
Keep the weak side; discard the strong. `N = N_weak`, `f = ι_weak ∘ f_weak`.
Intuition: the weak proof doesn't actually use its `φ_i`, so it suffices
for the conclusion via weakening.

### 4.10 `Cut(θ)` (paper §15)

Process as `And` between LEFT's `θ`-portion and RIGHT's `¬θ`-portion;
augment the running goal with `θ ∧ ¬θ` as a new disjunct.

Concretely:
- `P_L = f_L⁻¹(V_{G(θ)})`, `P_R = f_R⁻¹(V_{G(¬θ)})`.
- Apply the `And`-rule operation between `(N_L, f_L)` and `(N_R, f_R)`
  with the `θ ∧ ¬θ` shape — giving a combinatorial proof of
  `Γ ∨ (θ ∧ ¬θ)`.
- Augmented running goal gains `(θ ∧ ¬θ)` disjunct.

### 4.11 `CloseByLemma(L)`

Strategy B: require the closing op be preceded by `Cut(φ_L)` such that
LEFT is the lemma's combinatorial proof.

At the `CloseByLemma(L)`:
- Look up `L` in `lemma_registry`. Get `comb::CombProof L_proof`.
- The current open goal is the LEFT subgoal of the preceding `Cut`,
  containing `φ_L_nnf` at the end.
- Push `L_proof` as the combinatorial proof of this leaf.

The §15 augmentation handles the modularity: the lemma's proof is
referenced as if cut-in, and the augmented goal gains `(φ_L ∧ ¬φ_L)`.

## 5. Soundness contract

**Input gate**:
1. `LKRVerifier::verify(ctx, goal_formula, in)` returns Ok.

**Output gate**:
2. `CombVerifier::verify(ctx, augmented_goal, output)` returns Ok.

Translator bug ⇒ output-gate Error, not silent unsoundness.

## 6. Completeness contract

For every input that:
- LKR-verifies against `goal_formula`,
- Uses only LKR ops we support (= all Hughes §11 + Cut + CloseByLemma with
  Strategy B preconditions),

`LKRtoComb::apply` returns `Ok(combinatorial_proof)` such that
`CombVerifier::verify` accepts it against the augmented goal.

The augmented goal is classically equivalent to the original goal (each
`θ ∧ ¬θ` is contradictory); per Hughes Theorem 15.1, this is a valid
witness for the original goal.

## 7. Implementation phases

1. **Skeleton + gates.** `LKRtoComb` class, `input_gate`, `output_gate`.
   Test: empty/trivial programs round-trip; rejected inputs fail.
2. **Tree rebuild.** `lkr_to_tree(prog) → DerivationTree`. Test: simple
   programs (Or + AxiomLit, And + AxiomLits).
3. **Combinatorial-proof state ADT.** `CombProofState` with operations
   (add vertex, add edge, add link, compose fibration). Test: invariants
   maintained.
4. **Per-rule operations.** AxiomLit / One / Or / Exchange / Weakening /
   Contraction. The simpler half. Test: each operation produces a
   CombVerifier-accepted output on a hand-built fixture.
5. **`And` operation.** Both-strong, both-weak, mixed cases. Test on
   `(p ∧ q) ⇒ (q ∧ p)`-style fixtures.
6. **Quantifier operations.** Forall, Exists. Both Case A (uncovered)
   and Case B (added vertex). Test on `∀x.(p(x) ⇒ p(x))` and
   `∃x.(p(x) ⇒ ∀y.p(y))` (paper Fig. 1).
7. **`Cut` operation.** §15 augmentation. Test on programs with one or
   more cuts.
8. **`CloseByLemma`.** Lemma registry + Strategy B check. Test on a
   chain of theorems.
9. **Integration.** End-to-end NDtoLKR → LKRtoComb on the same fixtures
   that exercise NDtoLKR's phases.

Each phase's tests verify the output of that phase's covered rules
under `CombVerifier`. A phase doesn't ship until its tests pass.

## 7.5. Known limitations (post-implementation, 2026-05-17)

After implementation through phase 8 (Cut + CloseByLemma), the
end-to-end pipeline `ND → ND(iota-free) → LKR → CombProof` works for
**quantifier-free** ND proofs (demonstrated in
`test/lkr_to_comb_test.cpp::test_end_to_end_nd_to_comb_self_impl` on
`p → p`).

For ND proofs containing `forall`/`exists` blocks, NDtoLKR emits Cut
formulas that bake in ND's fix-var indices (e.g., `forall x. (¬p(0) ∨
p(0))` where `0` is the ND trace's allocated var for the bound `x`).
LKRtoComb builds the canonical target via `Fograph(augmented_goal)`,
which allocates **fresh** binder vars per occurrence (`next_binder_var`
incrementing from 0). The two var-allocation schemes diverge: a cut
block's inner `∀` gets, say, canonical var 1, but the LKR Forall op
uses eigen 0. The fonet's link check (verifier `verify_fonet`, args
must unify under dualizer) then fails because the link's two source
labels — read from the canonical target — have args with different
fixed-var indices.

**Fix options** (each substantial; deferred):

- **Alpha-rename cut formulas** in `cut_augment` so that bound vars
  match the LKR program's eigens. Requires walking each cut formula
  and substituting; collisions with other formulas need fresh names.
- **Use Fograph's allocation as authoritative** by alpha-renaming the
  LKR program's Forall/Exists eigens to canonical positions. Pre-pass
  over the LKR ops, computing the canonical var for each binder
  occurrence in advance.
- **Extend Fograph** to accept a pre-set var assignment (per-binder
  override). LKRtoComb computes the override map from the LKR
  program's eigens.

The math is unaffected; this is a pure implementation-coupling issue
between two upstream-independent var allocators (ND's trace +
NDtoLKR's `emit_close`, vs. Fograph's `next_binder_var`). Any of the
three fixes above closes it.

## 8. Open questions

- **Modular decomposition during translation.** Adding a binder vertex
  (Forall Case B, Exists Case B) modifies the cograph; the binder's
  *scope* needs to satisfy the "smallest proper strong module" property
  (paper Def. 3.2). Maintaining a live cotree across operations would
  be ideal but adds complexity. Alternative: rebuild the cotree on
  demand using `comb::Cotree`'s constructor (cheap at small sizes).
  Decide when the per-rule code starts hitting binder additions.

- **Eigenvariable identity vs occurrence.** Hughes treats vertices as
  occurrences. Our `comb::CombProof` uses positional indices. Exchange,
  Contraction in particular must reconcile these. For the first
  implementation cut, use positional indices and treat Exchange as a
  no-op when source positions cleanly map.

- **`Cut` + `CloseByLemma` pairing.** Strategy B requires every
  `CloseByLemma` to be preceded by a `Cut` for that lemma's formula.
  `NDtoLKR` always pairs them, but hand-crafted LKR programs may not.
  Should the input gate verify this pairing? Yes — it's a cheap
  structural check and prevents subtle bugs.

## 9. References

- Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236
  — §3 (fograph), §4 (skew bifibration), §5 (fonet), §6 (combinatorial
  proof), §11.1 (per-rule operations), §15 (cut handling), Theorem 15.1.
- `src/proof/COMBINATORIAL_PROOFS.md` — partial design (references
  the deleted ND→LKR translator; this doc supersedes its §5
  per-rule table).
- `src/proof/comb/WALKTHROUGH.md` — worked examples of per-rule
  operations on small LKR programs (Examples A–D). Read alongside
  §4 above.
- `src/proof/comb/comb_proof.h` — receiving `CombProof` type.
- `src/proof/comb/verifier.h` — the output gate (`CombVerifier`).
- `src/proof/translate/ND_TO_LKR_DESIGN.md` — upstream translator's
  output format.
