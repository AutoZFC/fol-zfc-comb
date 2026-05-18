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

#### Rule semantics

Hughes §11.1 base case:

```
─────────  One
 ⊢ 1
```

In our NNF encoding the truth literal `1` is `¬⊥` — `Compound{Not,
Bottom}`. A bare `Bottom` is `0` (unprovable). The LKR op
`One(idx)` is a closing leaf that closes the current goal when
`entries[idx]` is `¬⊥`. The LKRVerifier enforces the shape check.

#### State construction (leaf base case)

For a conclusion sequent `Γ` with `entries[idx] = ¬⊥`:

- `N` — one vertex `u_1` with `kind = VertexKind::One`. No
  `cograph_edges`, no `binding_edges`, no `links`, empty `dualizer`.
- `G(C)` — canonical target's fograph at the position assigned to
  the `¬⊥` entry. By §4.13 below, that position holds a single vertex
  with `kind = VertexKind::One`.
- `f : u_1 ↦ canonical_pos(idx)`.
- Other entries of `Γ` (if any) become *uncovered* in `f` — exactly the
  same treatment as the side entries in `AxiomLit`.

In short: this is the `AxiomLit` base case with one vertex instead of
two and no link.

#### Soundness lemma

We use the same framing as `AxiomLit` (§4.1): the leaf isn't required
to be verifier-accepted *standalone* — only the composed final
`CombProof` is checked by the output gate. The lemma we prove is that
the leaf's constructed source piece is internally consistent and
combines correctly with the surrounding per-rule operations.

**Claim.** `(N_leaf, f_leaf)` constructed above is a well-formed
fonet piece (Def. 5.3 conditions that depend only on the leaf):

1. **Link covering** (Def. 5.3 (i)): every atom-vertex lies in exactly
   one link; binders and `1` are unlinked. `N_leaf` has one vertex
   `u_1` of kind `One` with `in_link[u_1] = 0`. ✓ Matches the
   verifier's switch in `verifier.cpp::verify_fonet` 2A.1.
2. **Dualizer totality** (Def. 5.3 (ii)): every existential-binder var
   has a dualizer key. `N_leaf` has no binders. Vacuous; empty
   dualizer suffices.
3. **Binder scope** (Def. 3.2): vacuous, no binders.
4. **No induced bimatching** (Def. 5.3 (iii)): the leap graph
   contribution from the leaf is empty (no links added). Vacuous.

The skew-bifibration conditions (`f` a skew fibration on cograph
edges, ordinary fibration on binding edges) are checked on the *final*
composed `CombProof` after all per-rule operations have run. The leaf
contributes one source vertex with no edges, fibrated to the canonical
position of `entries[idx]`. The surrounding rules — `And`/`Cut` cross-
edges, `Forall`/`Exists` binder additions, the label-derived binding
post-pass — are what discharge the skew/fibration conditions globally,
exactly as for `AxiomLit`'s atom vertices.

**Consequence.** A `walk` whose derivation tree's leaves are all
`AxiomLit` or `One` (or `CloseByLemma` with valid registry entries),
composed with the existing per-rule operations, produces a
`CombProof` accepted by `CombVerifier` against the §15-augmented
goal — completing the Theorem A obligation for the `One` row.

#### Completeness scope

**Claim.** For every accepted LKR program whose closing leaf op is
`One(idx)`, the §11.1 walk produces an `Ok(cp)` that
`CombVerifier` accepts.

**Proof.** LKRVerifier accepts `One(idx)` only when
`entries[idx] = ¬⊥`. The Fograph extension (next subsection)
ensures the canonical target has a `VertexKind::One` vertex at
`canonical_pos(idx)`. The leaf builder constructs `(N, G, f)` as
above. By the soundness lemma, the resulting `CombProof` is verifier-
accepted. ∎

The rest of the proof tree (linear and branching rules above the leaf)
inherits the existing per-rule completeness. The leaf is a drop-in
replacement for `AxiomLit` from `walk`'s perspective.

#### Infrastructure: Fograph extension for `⊥` / `¬⊥`  (§13)

`src/proof/comb/fograph.cpp::build` currently asserts on any compound
whose op isn't `And`, `Or`, or `Not(predicate)`. To support `One` we
add one case:

```
if (c.op == Op::Not) {
    if (c.left->is_compound() &&
        c.left->as_compound().op == Op::Bottom) {
        // ¬⊥ ↦ one vertex with kind = One.
        size_t id = out.labels.size();
        VertexLabel lbl;
        lbl.kind = VertexKind::One;
        out.labels.push_back(std::move(lbl));
        return {id};
    }
    // existing ¬predicate handling.
}
```

`Bottom` alone (without enclosing `Not`) is unprovable — we assert
rather than build a vertex for it, because it never appears in a
verified LKR sequent (LKRVerifier rejects programs that don't close).

`labels_equal` in `verifier.cpp` already returns `true` for two `One`
vertices (kind-only comparison) — no change needed there.

#### Position counting

`count_vertices` (the helper in `cut_augment.cpp`,
`sequent_replay.cpp`, and `walk.cpp`) returns `1` for any
`Compound{Not, _}`. This is already correct for `¬predicate` (one
atom vertex) and remains correct for `¬⊥` (one `One` vertex). No
changes needed.

For bare `Bottom`, the current code returns `0` (falls through). We'll
add an assertion `Compound{Bottom}` paths shouldn't be reachable,
mirroring the Fograph builder's stance.

#### Test plan

Targeted tests at the layers where `One` is reachable:

1. **`fograph_one_vertex`** + **`fograph_one_in_disjunction`** — direct
   Fograph construction: `¬⊥` produces a single `VertexKind::One`
   vertex; in larger formulas, it sits as a leaf with no incident
   cograph edges (under `∨`) or with cograph edges from enclosing
   `∧` (handled identically to atom positions).
2. **`lkr_to_comb_one_minimal`** — LKR `[One(0)]` on goal `¬⊥`.
   Smallest possible exercise of the leaf builder.
3. **`lkr_to_comb_one_with_sibling`** — LKR `[Or(0); One(1)]` on goal
   `p ∨ ¬⊥`. Exercises the One leaf alongside sibling sequent
   entries (which become uncovered in source).

#### End-to-end via NDtoLKR: not currently reachable

`One` is emitted by `emit_close` (only) when one of the two closing
entries is `¬⊥` (the `is_top_literal` check). Tracing NDtoLKR shows
this never fires for the supported ND rule set:

- `BottomElim`'s `emit_close` pair is `(NNF(formula), NNF(¬formula))`
  from the wrapped `NotElim`, neither of which is `¬⊥` for any
  reasonable proof.
- A step with formula exactly `⊥` would put `¬⊥` in
  `step_to_neg_idx`, but the only such steps (`not_elim`) are
  classified as no-emit, so they don't generate flat-step cuts.
- `assume _|_` followed by `not_intro` is rejected by
  `translate_block_not` (which requires `NotIntro.bottom` to be a
  `NotElim`).
- Goals containing `¬⊥` cause `⊥` to appear in negated cut formulas
  via NNF, which the Fograph builder asserts on (bare `⊥` is `0` and
  is unprovable).

The `One` leaf builder is therefore complete for **hand-crafted LKR
programs** (Phase 2 covered above) but currently unreachable through
the full ND pipeline. Lifting this requires either:

- Extending `translate_block_not` to accept `NotIntro` over a direct
  `Assume _|_` (so `not_intro (assume _|_)` translates to `¬⊥`), or
- Extending Fograph + the per-rule operations to handle bare `⊥` as
  an unprovable sentinel (so `⊥`-containing intermediates can pass
  through structurally).

Both are out of scope for Phase 2; track as a NDtoLKR enhancement.

#### Implementation order

1. Add the Fograph `¬⊥` case + targeted Fograph tests.
2. Add `walk.cpp::build_leaf_one` and wire it into `walk_recursive`'s
   leaf dispatch (parallel to `build_leaf_axiom_lit`) + the two
   `lkr_to_comb_one_*` tests.

The walk leaf builder is ~15 lines (build a 1-vertex source, no edges,
fibration of `[entry_positions[idx][0]]`). No changes to per-rule
linear or branching code. COMPLETENESS.md row "One" flips to ✓ once
the LKR layer is covered; an NDtoLKR-emission obligation is added as
a separate row tracking the enhancement above.

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

## 7.5. Quantifier var-mismatch — resolved (2026-05-18)

The pipeline `ND → ND(iota-free) → LKR → CombProof` now handles
quantified goals end-to-end. The first quantified test
(`test/lkr_to_comb_test.cpp::test_end_to_end_nd_to_comb_forall_self_impl`,
goal `forall x. (p(x) → p(x))`) passes.

Two coupled fixes were needed; both are math-grounded rather than
patches around the verifier.

### Fix 1 — alpha-rename pre-pass (Option B from the original design)

Module: `src/proof/translate/lkr_to_comb/alpha_rename.{h,cpp}`.

NDtoLKR emits `Forall(eigen=K)` where `K` is ND's trace fix-var, and
emits cut formulas whose atom args contain `Fixed(K_outer)` for any
outer-Forall fix-var still in scope. Independently, Fograph allocates
fresh binder vars in pre-order over the §15-augmented goal. The two
allocators are disjoint, so the LKR program's eigens generally don't
match Fograph's. After running cut_augment / sequent_replay / Fograph
on the original program, the pre-pass:

1. computes `binder_pos` for each `Forall` op as
   `entry_positions[i][principal][0]`;
2. reads `canonical_var = Fograph_target.labels[binder_pos].var`;
3. records `eigen → canonical_var` in a rename map;
4. rewrites the program: `Forall.eigen` to `canonical_var`, and every
   `Term::fixed(old)` inside `Cut.cut_formula` / `Weakening.formula`
   to `Term::fixed(new)`. The rewrite is a *simultaneous*
   substitution (one-pass tree walk) — chained single substitutions
   clobber themselves whenever the map is a permutation
   (e.g. `{0→1, 1→0}`).

`Exists`'s witness `TermRef` resolves through `term_env`, which
inherits the renamed `Forall` eigen automatically.

Fograph's allocation order depends only on the augmented goal's
structure, not on its atom args, so the canonical_var at any position
is the same whether computed against the original or the renamed
program. That's what makes the pre-pass well-defined.

### Fix 2 — derive source binding edges from labels (Hughes Def. 3.1)

Module: `src/proof/translate/lkr_to_comb/walk.cpp` (`derive_binding_edges`
post-pass).

Once vars align, a second issue surfaces: the verifier's unique-lift
binding fibration check fails on source atoms that reference an outer
binder's var but live in cut blocks rather than the outer Forall's
principal body. The previous code added source binding edges inside
each rule (`rule_forall`: edges to `P` only; `rule_exists`: same), so
atoms in *carried-over* sequent entries that share the binder var got
no source binding edge to the binder vertex.

The math is unambiguous: in a fograph (Def. 3.1) — and hence in a
fonet (Def. 5.3), which is a linked fograph — binding edges are
**derived** from labels: `(b, a)` is a binding edge iff `b` is a binder
with var `v` and `a` is an atom whose args contain `Fixed(v)`.
Fograph's own `add_binding_edges` builds the target this way. The
source must follow the same recipe.

Implementation: `rule_forall` and `rule_exists` no longer construct
binding edges; a single post-pass `derive_binding_edges` at the end of
`walk` clears `source.binding_edges` and rebuilds them by scanning
source vertices (labels resolved via `target.labels[fibration[v]]`).
This is the single source of truth and matches Hughes' definition
verbatim.

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
