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

#### Rule semantics

`Weakening(φ)`: append `φ` to the sequent.
Hughes §11.1 W-case operation:

- `G(C) = G(H) + G(φ)` — the target extends.
- `N` is unchanged.
- `f' = ι ∘ f` where `ι : G(H) ↪ G(C)` is the canonical injection.
- The new `G(φ)` vertices are *uncovered* in `f`.

LKRVerifier accepts `Weakening(φ)` unconditionally (any formula can be
weakened in).

#### The §15-mismatch (why this isn't free)

§15 cut handling absorbs `Cut(θ)` into the augmented goal by adding
`(θ ∧ ¬θ)` — a **contradiction**. `goal ∨ (θ ∧ ¬θ)` is classically
equivalent to `goal`, so proving the augmented form witnesses `goal`.

Weakening would naively add `∨ φ` to the augmented goal. But
`goal ∨ φ` is **not** classically equivalent to `goal` when `φ` isn't
contradictory: `goal ∨ φ` can be valid while `goal` isn't (e.g.,
take `φ ≡ ¬goal`, then `goal ∨ φ` is the excluded middle).

So a CombProof of `goal ∨ φ` doesn't generally witness `goal`. The
§15 trick can't be reused for Weakening as-is.

#### Two cases by usage pattern

**Case A — scaffolding Weakening (supported).** The weakened entry
is never referenced by a subsequent LKR op. Concretely: no later op's
position field (`principal`, `lit_a`/`lit_b`, `idx`, `i`/`j`, or any
element of `left_partition`) targets a sequent index originating from
this Weakening, and no And/Cut split-by-partition routes such an index
to a subsequent op.

In this case, the source has **no vertices** fibrating to `G(φ)`'s
positions. We can leave `G(φ)` out of the augmented goal entirely:
the canonical target is built from `goal_nnf ∨ ⋁(θ ∧ ¬θ)` (no `φ`),
and `walk` treats the Weakening op as a no-op (the fonet just doesn't
cover the weakened entry — the entry's positions are an empty vector
in `sequent_replay`).

This is the current implementation. It's sound: the CombProof
witnesses `goal_nnf ∨ ⋁(θ ∧ ¬θ)`, which is `goal_nnf` classically.

**Case B — load-bearing Weakening (out of scope).** A subsequent op
references the weakened entry. To handle this, the canonical target
must include `G(φ)`'s positions. But then the augmented goal includes
`φ` as a non-contradictory disjunct, and the CombProof witnesses a
**classically weaker** statement than `goal_nnf`. The pipeline's
soundness contract ("CombProof witnesses the user's `goal_formula`")
breaks.

We could support load-bearing Weakening by changing the contract —
the CombProof would witness `goal_formula ∨ ⋁ ψ_j` for the load-
bearing weakening formulas. The user's effective claim weakens.
For the current scope (classical FOL proof libraries where the
user's claim is their actual theorem), this isn't useful: a proof of
`theorem ∨ ψ` for irrelevant `ψ` is just `theorem` with extra
junk that doesn't help prove `theorem` itself.

#### State construction (Case A)

- `N` unchanged.
- `f` unchanged (no new fibration targets in `G(φ)` since `G(φ)`
  isn't in the canonical target).
- Per-rule effect on `walk`: return child unchanged.

#### Soundness lemma (Case A)

**Claim.** When all Weakening ops in `P` are scaffolding (Case A),
the CombProof produced by `walk` is a valid CombProof of
`goal_nnf ∨ ⋁(θ ∧ ¬θ)`, which is classically equivalent to
`goal_nnf`.

**Proof.** The CombProof's source has no vertices fibrating to any
weakened entry's positions (precondition of Case A: no later op
references those entries, so AxiomLit / Forall / etc. never assigns
source vertices there). The fonet, fibrations, and links are
independent of Weakening's existence. The output gate
(`CombVerifier::verify(ctx, augmented_goal, cp)`) accepts. ∎

#### Detection of load-bearing Weakening

Static check on the LKR program. For each `Weakening` op at position
`i`, track the set of sequent indices it introduces. Each subsequent
op's position fields are checked against this set; if any match (and
the entry hasn't been Contracted away), the Weakening is load-bearing.

The check piggybacks on `sequent_replay`'s structure: weakened
entries have empty position vectors. Any later op reading an empty
position vector is using a load-bearing weakening.

Implementation strategy:
- Add an input-gate check `weakening_is_scaffolding(P)` that walks
  the program, tracking weakened-entry origins through And/Cut
  splits, and verifies no non-weakening op references them.
- Reject with a clear error pointing at the load-bearing reference
  if the check fails.

For the current scope, this gate-level check is the right discipline:
load-bearing Weakening shouldn't happen in NDtoLKR output (which
doesn't emit Weakening at all) or in well-formed hand-crafted LKR
programs. The gate catches misuse cleanly.

#### Completeness scope

Theorem A's "every LKR-accepted `Q`" obligation is narrowed: we
guarantee completeness only for LKR programs whose Weakening ops are
scaffolding. Load-bearing Weakening is rejected at the input gate.

This narrowing is **necessary**, not a defect: the §15 framework can
keep cuts but cannot uniformly keep weakenings without changing the
proven statement. Supporting load-bearing Weakening would require a
different soundness contract.

#### Test plan

1. **`weakening_scaffolding_passes`** — hand-crafted LKR program with
   a Weakening of unused `ψ`. Closes via AxiomLit on goal atoms only;
   the weakened entry is uncovered.
2. **`weakening_load_bearing_rejected`** — hand-crafted LKR program
   that Weakens in `ψ` and then references it (e.g., `AxiomLit` on
   the weakened entry's position). Input gate should reject with a
   clear error.
3. (Optional) **`weakening_in_branching`** — Weakening followed by
   And or Cut, where the weakened entry routes into a subgoal's
   complement. Verifies the gate's tracking through branching ops.

#### Implementation order

1. Add the input-gate check `weakening_is_scaffolding` to
   `input_gate.{h,cpp}`. Walks the program, tracks weakened entries
   through op effects, fires error if a non-Weakening op references
   one.
2. Add the two/three tests above.
3. `walk` and `sequent_replay` are already correct for Case A — no
   changes needed.
4. Update the obligation table row for Weakening from "partial" to
   "✓ done (scaffolding)" with a footnote pointing here.

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

#### Rule semantics

Strategy B (Hughes §15 endorsed extension): the closing op
`CloseByLemma(L)` must be preceded by `Cut(φ_L)` such that LEFT's
last entry is `φ_L_nnf` and the lemma `L` was previously verified
standalone, registered in `lemma_registry` as a `comb::CombProof`
of `φ_L_nnf`. The closing op pastes that proof into the current
LEFT subgoal.

LKRVerifier accepts `CloseByLemma(L)` whenever entries[last] resolves
to the lemma's formula in NNF.

#### Setup notation

Let:

- `L_proof = (N_L, T_L, f_L)` — the lemma's CombProof, with
  `T_L = G(φ_L_nnf)`. Vertex IDs are pre-order from Fograph's
  standalone build of `φ_L_nnf`.
- `T = G(augmented_goal)` — the outer canonical target.
- `σ_pos : [0, |T_L|) → [0, |T|)` — position remap. For each lemma
  target position `i`, the outer-canonical position is
  `σ_pos(i) = entry_positions.back()[i]` (LEFT's last entry's
  positions, in the same pre-order). Bijective onto the slice of `T`
  occupied by the cut formula.
- `V^∃_L, V^∀_L ⊆ T_L` — lemma's existential/universal binder vertex
  sets (Fograph-allocated when building `L_proof`).
- `var_L(b)` — for binder vertex `b ∈ T_L`, the lemma-canonical var
  `T_L.labels[b].var` (a `var_index`).
- `var_O(b)` — for binder vertex `b ∈ T_L`, the outer-canonical var
  at the position-remapped vertex: `T.labels[σ_pos(b)].var`.

#### State construction (leaf)

The pasted CombProof `cp = (N_L, T, f')`:

- `target` ← `T` (the shared outer canonical target).
- `source.num_vertex` ← `|N_L|` (lemma vertex count unchanged).
- `source.cograph_edges, source.binding_edges, source.links` ←
  inherited from `N_L` (vertex indices unchanged because the source
  vertex set is unchanged).
- `fibration[v]` ← `σ_pos(f_L(v))` for each `v ∈ V_{N_L}`.
- `source.dualizer` ← `σ_remap(δ_L)`, defined below.

#### Dualizer remap (`σ_remap`)

Define the var renaming `σ : var_index → var_index` on lemma binder
vars:

```
σ(v) = var_O(b)   where b ∈ T_L is the unique binder vertex with var_L(b) = v
```

Fograph allocates one var per binder occurrence, so `σ` is well-defined
on `{var_L(b) : b binder in T_L}`. Outside that domain, `σ` is the
identity (atom args may contain Fixed terms that aren't binder vars —
e.g., free fix-vars from outer scopes; those pass through).

Extend `σ` to terms:

```
σ_T(Fixed(v))      = Fixed(σ(v))      if v ∈ dom(σ),  else Fixed(v)
σ_T(Gen(k))        = Gen(k)            (Gen never names a binder var directly)
σ_T(Description t) = (not encountered — comb pipeline is description-free)
```

Then for each lemma dualizer entry `(x_L, t_L)`:

```
σ_remap(δ_L) := { (σ(x_L), σ_T(t_L))   :   (x_L, t_L) ∈ δ_L }
```

#### Soundness lemma

**Claim.** `cp` is a valid CombProof of `T` (when composed with the
preceding `Cut(φ_L)`).

**Proof.**

1. *Fonet conditions on `N_L`* — unchanged from `L_proof`'s
   well-formedness (link covering, dualizer totality, scope,
   bimatching). The source's vertex set, edges, and links are
   bitwise inherited. The dualizer needs separate justification — see
   step 2.

2. *Dualizer totality and key correctness.* `δ_L` is total on `V^∃_L`
   (`L_proof` verifies). After `σ_remap`:
   - For each `x_L ∈ V^∃_L`'s var, `σ(x_L)` is the outer-canonical
     var at the position-remapped binder vertex. By Fograph's
     definition, the binder kind (∃ vs ∀) is preserved by structural
     isomorphism of `T_L` with its slice in `T` — they're built from
     the same `φ_L_nnf` formula. So `σ(x_L)` is an outer existential
     binder var; `δ' := σ_remap(δ_L)` has the right key type.
   - Source labels (via fibration) are read from `T`. The existential
     binder vars in `source` are exactly `{var_O(b) : b ∈ V^∃_L}` =
     `σ(V^∃_L's vars)`. So `δ'`'s key set covers source existentials
     exactly. Totality preserved.

3. *Dualizer image values.* `δ_L`'s image terms reference universal
   binder vars of `T_L` (verifier check 2B.2). After `σ_T`, those
   references become outer universal binder vars. The atom labels on
   source (read from `T` via fibration) also use outer-canonical vars.
   So the link check `apply_dualizer_to_args(l1.args, δ') ==
   apply_dualizer_to_args(l2.args, δ')` holds because:

   - `l1.args, l2.args` are outer-canonical (from `T`).
   - The lemma's link check held in lemma-canonical:
     `apply_δ_L(l1_L.args) == apply_δ_L(l2_L.args)`.
   - `T_L`'s atom labels at lemma positions `i` are σ-related to
     `T`'s atom labels at `σ_pos(i)` (the structural iso of the slice
     extends to atom args via σ_T). So the renamed equation holds.

4. *Skew/binding fibration.* The post-pass `derive_binding_edges`
   rebuilds source binding edges by scanning source labels (which are
   outer-canonical). The structural iso `T_L ↔ T.slice(σ_pos)` plus
   `δ_L`'s validity in lemma-canonical implies `δ'`'s validity in
   outer-canonical. ∎

#### Precondition

`σ_pos` is the position remap given by `entry_positions.back()`. For
this to be coherent, the lemma's vertex labels must be σ-compatible
with the outer target at the remapped positions:

- Same vertex count: `|T_L| == |σ_pos|` (already checked).
- Same kind sequence: for every `i`, `T_L.labels[i].kind ==
  T.labels[σ_pos(i)].kind` (binder ↔ binder, atom ↔ atom, one ↔ one).
- Same atom polarity + predicate: for atoms, `pred` and `negated`
  must match.

If any of these fails, the lemma's formula doesn't equal `φ_L_nnf`
in the sense Fograph requires — that's a registry corruption or a
mismatched cut formula, and is an error.

#### Completeness scope

After this spec lands, `CloseByLemma` handles **every** lemma whose
`CombProof` verifies standalone — including those with non-empty
dualizer (quantified lemmas). The previous "first-cut limitation"
(reject lemmas with non-empty dualizer) is lifted.

#### Test plan

Three tests, ordered by ascending dualizer complexity:

1. **`close_by_lemma_empty_dualizer`** — regression: the existing
   `cut_with_lemma` test (lemma = `p → p`, no quantifiers) must keep
   passing. Empty dualizer ⇒ remap is a no-op.

2. **`close_by_lemma_with_forall_lemma`** — lemma is `∀x.(p(x) → p(x))`.
   Its CombProof has one universal binder; dualizer is empty (no
   existentials in `¬¬p ∨ p` direction), so this exercises the
   binder-kind-preservation check without exercising dualizer
   substitution. Cut on `∀x.(p(x) → p(x))` + CloseByLemma.

3. **`close_by_lemma_with_exists_lemma`** — lemma is
   `∃x.(p(x) ∨ ¬p(x))`. Its CombProof has one existential binder
   with a non-empty dualizer (some witness term). Cut + CloseByLemma
   must remap the dualizer key (lemma existential var → outer
   existential var) and any binder-var refs in the image term.

#### Implementation order

1. Extend `build_leaf_close_by_lemma`:
   - Build `σ` by scanning `lemma_cp.target.labels` for binders and
     pairing with `cc.canonical_target.labels[lemma_target_positions[i]]`.
   - Verify the label-shape preconditions (kind/pred/negated parity)
     during the scan; error if any fails.
   - Remove the "non-empty dualizer rejected" early return.
   - Build `δ'` by iterating `lemma_cp.source.dualizer` and applying
     `σ` to keys (lookup in `σ` table) and `σ_T` to values (single
     `is_fixed` + lookup, mirroring `alpha_rename.cpp`'s
     `rewrite_term_simultaneous`).
2. Add the three tests in `lkr_to_comb_test.cpp` (smallest first).
3. Flip the `CloseByLemma` row in COMPLETENESS.md §4.1 from
   "partial" to "✓ done".

No changes to per-rule linear/branching code. The remap is local to
the leaf builder.

#### Why this matters

This is the row that unlocks **modular theorem reuse**: each proved
theorem registers its CombProof, and downstream proofs cite it via
`CloseByLemma` without re-translating. Without dualizer remap, only
quantifier-free theorems are reusable — which excludes most theorems
of practical interest (any `∀x.P(x)` or `∃x.P(x)` lemma).

### 4.12 Lemma composition by LKR-level inlining (Strategy A)

#### Why this section exists

`CloseByLemma` (§4.11) provides Strategy B: paste a lemma's standalone
`CombProof` into the outer fonet at the cut formula's position. The
math is clean but requires the lemma's `CombProof.target` to equal
`G(φ_L_nnf)` exactly. Lemmas built via the full ND→Comb pipeline
target their *§15-augmented* goal (with extra positions for the
lemma's internal cuts), so Strategy B only handles Cut-free lemmas.

Cut-elimination at the combinatorial-proof level is open (Hughes §17).
Without it, we have no algorithm to convert a cut-bearing lemma proof
into a Cut-free one.

But §15 itself supplies the answer. §15 **keeps cuts** and witnesses
the augmented goal. If we inline a lemma's LKR program at the outer's
`CloseByLemma` point, *the lemma's cuts become outer cuts in the
combined LKR program*. The outer's augmentation then includes the
lemma's cut blocks naturally, and the lemma's source fibrates into
the combined augmented target without any composition gymnastics.

This is the "keep cuts under composition" principle, expressed at the
LKR layer where it has a direct realization.

#### Rule semantics

Given outer LKR program $P$ and a lemma registry mapping
$\text{name} \mapsto P_L$ (each $P_L$ LKR-verifies against $\varphi_L$),
`inline_lemmas(P, \text{lemmas})` returns a combined program $P'$ with
every `CloseByLemma` op replaced by the corresponding lemma's LKR ops.
$P'$ LKR-verifies against the outer goal; `LKRtoComb` then handles it
uniformly via `alpha_rename + cut_augment + walk`.

After inlining, the dispatch table in `walk_recursive` never sees a
`CloseByLemma` op. Strategy B's per-leaf builder
(`build_leaf_close_by_lemma`) is retained as a safety net (errors
clearly if a `CloseByLemma` somehow survives).

#### Splicing operation

At each `CloseByLemma(L)` in the outer's op stream:

1. Look up $P_L$ in the registry. (Error if not found.)
2. **Compute splice offset** $k$. The top open goal at the
   `CloseByLemma` point is $[\text{outer-stuff}_0, \ldots,
   \text{outer-stuff}_{k-1}, \varphi_{L\text{-nnf}}]$ (size $k+1$).
   $\varphi_{L\text{-nnf}}$ is at position $k = \text{size} - 1$.
   $P_L$'s op #0 expects to operate on the singleton sequent
   $[\varphi_{L\text{-nnf}}]$ (position 0); we shift all of $P_L$'s
   position references by $+k$.
3. **Allocate fresh eigens** $\rho : V_{P_L}^{\text{eigen}} \to \mathbb{N}$
   for each Forall eigen in $P_L$, drawn from a fresh range above any
   var used in $P$ or any earlier splice. This preserves LKR's
   freshness condition; alpha-rename later re-canonicalizes them.
4. **Compute per-op offset map** for $P_L$. Position offsets are
   *per-goal* on the LKR open-goals stack and change only on
   branching ops:
   - **And**: pop, push RIGHT (offset = parent), push LEFT (offset = **0**).
     Justification: LEFT subgoal's entries are $\text{sorted}(L) \cup
     \{\text{LEFT}\_\phi\}$ where $L$ is the partition; the partition
     contains only lemma indices (outer-stuff isn't in $L$), so
     outer-stuff goes to RIGHT and LEFT has no outer-stuff prefix.
   - **Cut**: pop, push RIGHT (offset = parent), push LEFT (offset = parent).
     Both subgoals inherit the parent's outer-stuff prefix.
   - **Linear ops** (Or, Forall, Exists, Weakening, Contraction, Exchange):
     offset unchanged.
   - **Closing ops** (AxiomLit, One, nested CloseByLemma): pop.
5. **Rewrite each $P_L$ op** with its computed offset:
   - `principal, lit_a, lit_b, idx, i, j`: add offset.
   - `And.left_partition`: add offset to each element.
   - `Forall.eigen`: apply $\rho$.
   - `Cut.cut_formula`, `Weakening.formula`: walk the `FormulaHandle`
     substituting `Fixed(v) → Fixed(ρ(v))` for $v \in \text{dom}(\rho)$
     (one-pass simultaneous substitution, like `alpha_rename.cpp`).
   - `Exists.witness.idx` (a `TermRef`): add the combined-program op
     index of the corresponding spliced Forall op (computed via a
     per-splice index map).
   - Nested `CloseByLemma`: recursively splice (lemmas may reference
     other lemmas).
6. Append rewritten ops to the output program.

#### Soundness

**Claim.** If $P$ LKR-verifies against $\psi$ (with `CloseByLemma` resolved
against `lemmas`) and each $P_L \in \text{lemmas}$ LKR-verifies against
$\varphi_L$, then `inline_lemmas(P, \text{lemmas})` LKR-verifies against
$\psi$.

**Proof sketch.**

At each splice point, the top goal is $[\text{outer-stuff} \ldots, \varphi_L]$.
$P_L$'s ops, when run with offset $k$, operate on this goal as if it
were $[\varphi_L]$ — the outer-stuff entries are "weakening" $P_L$
doesn't touch. Each $P_L$ op's effect on the LKR sequent:

- **Or, Forall, Exists, Exchange, Weakening, Contraction**: act on
  one entry at offset $k + p$ (for $P_L$-local index $p$); other
  entries (outer-stuff) untouched. ✓
- **And, Cut**: split the sequent; LEFT/RIGHT subgoals defined by
  partition + appended entries. By the analysis in step 4 above,
  the per-subgoal offsets keep position references coherent.
- **AxiomLit, One**: close the top goal. The outer-stuff entries
  are popped along with the goal — they were never "used", but
  closing requires only that *some* atomic-literal pair (or
  truth-literal) exists in the entries, and $P_L$'s closer points to
  the lemma's atoms at offset $k + p$. ✓

Eigen rename $\rho$ ensures Forall freshness: $P_L$'s eigens, after
rename, don't appear in outer's sequents (because $\rho$'s range is
above all existing vars). LKRVerifier accepts. ✓

`Cut.cut_formula` rewriting: the formula handle is rewritten so its
free Fixed terms use renamed eigens. The cut's emitted entries
(${\theta\_\text{nnf}}$ on LEFT, $\neg\theta\_\text{nnf}$ on RIGHT)
inherit these renamed vars consistently. ✓

The combined $P'$ verifies. The output (a verified LKR program) goes
through alpha-rename + cut_augment + walk normally. ∎

#### Completeness

**Claim.** For every $P$ accepted by LKRVerifier against $\psi$
(modulo the registry providing every referenced lemma), `inline_lemmas`
returns Ok.

**Proof.** Splicing is total: every `CloseByLemma` finds its lemma
(registry precondition), the offset and rename data are computable
from the LKR program structure, and recursive splicing terminates
because the registry is acyclic. ∎

#### Trade-off (the only one)

Size: $|P'| = |P| + \sum_{\text{use}} |P_L|$. Multiplicative in lemma
reuse. The combined augmented goal grows accordingly: each lemma use
contributes a copy of the lemma's cut blocks.

This is no worse than the worst-case bound for cut-elimination in
classical sequent calculus (Gentzen's `Hauptsatz` gives super-
exponential blowup in the worst case; polynomial for common cases).
We're getting the same asymptotic complexity via the much simpler
"keep cuts" route.

For deep lemma chains (lemma A uses lemma B uses lemma C...), the
blowup is multiplicative in the depth. If this becomes a problem, two
optimizations are available without changing the math:

- **Deduplication of identical cut blocks** in the augmented goal:
  $(\theta \wedge \neg\theta)$ appearing multiple times can be
  classically collapsed (each disjunct is contradictory and adds no
  information). Saves Fograph vertex count.
- **Cut-free fast path (Strategy B)**: when a lemma's `LKR` program
  has no Cut ops, `lemma.CombProof.target = G(\varphi_L)` exactly,
  and the leaf-builder pasting in §4.11 can be used instead of
  inlining. The dispatcher picks based on a one-line check on
  `lemma_program.has_any_cut`.

For our current scope (classical FOL, modest proof libraries), the
naive Strategy A is sufficient.

#### Test plan

1. **`inline_simple_lemma`** — regression: existing
   `cut_with_lemma` test reformulated to use Strategy A. Lemma is a
   single-step `[Or, AxiomLit]` program; inlining splices it in
   place of `CloseByLemma`.
2. **`inline_lemma_with_internal_cut`** — the case Strategy B
   couldn't handle. Lemma is a non-trivial proof (e.g., produced by
   NDtoLKR for `forall x. (p(x) -> p(x))`) that contains its own
   Cut ops. Inlined into an outer proof, the cuts propagate into
   the outer's augmented goal naturally.
3. **`inline_lemma_chain`** — lemma A uses lemma B uses ... a
   chain. Recursive splicing should produce a correct combined
   program. Optional, defer if the first two pass cleanly.

#### Implementation order

1. New module `lemma_inliner.{h,cpp}` (~150 LOC).
2. Change `LKRtoComb`'s registry type from
   `LemmaCombProofs` (name → CombProof) to `LemmaPrograms`
   (name → LKR program).
3. Wire `inline_lemmas` into `LKRtoComb::apply` before alpha_rename.
4. Update existing tests to construct the registry with LKR programs.
5. Add the new tests above.
6. The leaf builder `build_leaf_close_by_lemma` (§4.11) becomes
   dead code in the normal path but stays as a safety net for
   unspliced `CloseByLemma` (returns a clear error).

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
