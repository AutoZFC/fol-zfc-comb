# LKR → Comb F2: Paper-Faithful Per-Hypothesis Target Architecture

Status: spec draft. Implementation not started.

This doc specifies the migration of `LKRtoComb` from the current shared
canonical target (`G(augmented_goal)` for every subproof) to Hughes
2019's per-hypothesis target architecture. The motivation is the C.2
singleton-binder failure surfaced in axiom_rewrap Phase 6 (see
`LKR_TO_COMB_DESIGN.md §8`), which is a symptom of the deeper
architectural deviation, not a localized bug.

## 0. Status

| Item                       | State |
|----------------------------|-------|
| Math spec                  | draft (this doc) |
| Migration plan             | draft (this doc) |
| Implementation             | not started |
| Validating tests           | Phase 6 Tests 4 + 5 in `axiom_rewrap_test.cpp` (currently `#if 0`) |

## 1. The deviation

Hughes 2019 §11.1 defines each per-rule operation against
**per-hypothesis targets**:

- Each hypothesis sequent `H_i = Γ_i, ϕ_i` has its own target
  `G(H_i) = G(Γ_i) + G(ϕ_i)` (parallel composition of each entry's
  fograph).
- The input to a rule is a CombProof `f_i : K_i → G(H_i)`.
- The output is a CombProof `g : K → G(C)` against the conclusion's
  target `G(C)`, with `z_i : G(H_i) → G(C)` the canonical injective
  homomorphism that embeds each hypothesis target into the conclusion's.

In that framework, the preimages used by the ∧-rule and the §15 Cut —
`P_i = f_i^{-1}(V_{G(ϕ_i)})` — are **automatically portions** (Def 10.3:
closed under adjacency and binding) of the source `K_i`. This is the
content of Lemma 11.2's "routine verification". Fusion at portions
(Def 10.4) is therefore well-defined and preserves fograph legality
(Def 3.2: every binder's scope is its smallest proper strong module).

The current `LKRtoComb` instead uses **one shared canonical target** —
`G(augmented_goal)` — for every subproof. Every per-rule operation's
fibration goes into the same target. This was a shortcut that simplified
§15 cut accumulation (one running goal vs. local target-augmentation
at each cut node) but breaks the invariants Hughes's per-rule
construction relies on:

- `V_{G(ϕ_i)}` is a set of positions embedded inside a larger fograph,
  not a portion of `G(H_i)`.
- The preimage `f_i^{-1}(V_{G(ϕ_i)})` in the source `K_i` is no longer
  automatically a portion (adjacency / binding closure is no longer
  guaranteed by skew bifibration into the smaller `G(H_i)`).
- `rule_and` / `rule_cut` then fuse at non-portions, producing source
  graphs whose binders' strong-module scopes are smeared across the
  fusion boundary.
- CombVerifier (correctly enforcing Def 3.2 via Lemma 10.20's C.2
  decomposition) catches the violation and rejects.

The C.2 dump in the axiom_rewrap Phase 6 investigation showed the exact
shape: two binders + their shared atom forming a K₃ triangle. In K₃ the
only strong modules are singletons and the full set; neither
`{binder, atom}` pair is a strong module, so neither binder has a legal
scope.

## 2. F2 — what the paper actually says

### 2.1 Target propagation

Every node in the LKR derivation tree carries its own **conclusion target**:

```
walk_node : DerivationTree.Node → CombProof(K, G(node.sequent), f)
```

The target is built from the node's conclusion sequent:

```
G(sequent = [ψ_1, …, ψ_k])  :=  G(ψ_1) + G(ψ_2) + … + G(ψ_k)
                                  ─────── parallel composition ───────
```

For leaf nodes (closing ops), the target is built directly. For
internal nodes, the target is determined by the rule and constructed
from the child(ren)'s target(s) plus the rule's structural addition.

### 2.2 Per-rule operations (verbatim from Hughes §11.1)

For each rule, the inputs are CombProof(s) against hypothesis target(s)
`G(H_i)`; the output is a CombProof against the conclusion target
`G(C)`. `z_i : G(H_i) → G(C)` is the canonical injective graph
homomorphism that embeds each hypothesis target into the conclusion's.

**AxiomLit α**: target `G(C) = •α + •ᾱ`. Source `K = {u_α, u_ᾱ}` with
one link.

**One**: target `G(C) = •1`. Source `K = {u_1}`, no link.

**Or (∨)**: hypothesis `H = Γ, ϕ, θ`, conclusion `C = Γ, ϕ ∨ θ`.
`G(H) = G(C)` (parallel re-association is a no-op in cograph terms).
`g = f`.

**Exchange (X)**: hypothesis `H = Γ, ϕ, θ, Δ`, conclusion
`C = Γ, θ, ϕ, Δ`. `x : G(H) → G(C)` is the canonical isomorphism.
`g = x ∘ f`.

**Weakening (W)**: hypothesis `H = Γ`, conclusion `C = Γ, ϕ`.
`w : G(H) → G(C)` is the canonical injection. `g = w ∘ f`.

**Forall (∀)**: hypothesis `H = Γ, ϕ`, conclusion `C = Γ, ∀x ϕ`.
`a : G(H) → G(C)` is canonical. `G(H) = G(Γ) + G(ϕ)`.
- If `f^{-1}(V_{G(ϕ)}) = ∅`: `g = a ∘ f`.
- Else: `g : •x + K → G(C)` extends `a ∘ f` mapping `•x` to the
  unique x-binder in `G(C)`. Source becomes `•x + K` (parallel
  composition with the binder vertex).

**Exists (∃)**: hypothesis `H = Γ, ϕ{x ↦ t}`, conclusion `C = Γ, ∃x ϕ`.
`e : G(H) → G(C)` is canonical. `G(H) = G(Γ) + G(ϕ{x ↦ t})`.
`P = f_s^{-1}(V_{G(ϕ{x ↦ t})})`.
- If `P = ∅`: `g_s = e ∘ f`.
- Else: `K_s^+` extends `K_s` with vertex `v` and edges from `v` to
  every vertex in `P`. `g_s : K_s^+ → G(C)` extends `e ∘ f` mapping
  `v` to the x-binder in `G(C)`.

**And (∧)**: hypotheses `H_1 = Γ_1, ϕ_1` and `H_2 = Γ_2, ϕ_2`,
conclusion `C = Γ_1, Γ_2, ϕ_1 ∧ ϕ_2`. `z_i : G(H_i) → G(C)` are
canonical injections. `G(H_i) = G(Γ_i) + G(ϕ_i)`.
`P_i = f_i^{-1}(V_{G(ϕ_i)})`. `f_i` is **strong** iff `P_i ≠ ∅`.
- Both strong, or both weak: `K = fusion(K_1, K_2)` at portions
  `P_1, P_2` (Def 10.4: union + cross-edges between every pair).
  `g = z_1 ∘ f_1 ∪ z_2 ∘ f_2`.
- Mixed (one weak `f_w`, one strong `f_s`): keep the weak side alone:
  `g : K_w → G(C) = z_w ∘ f_w`.

**Cut (§15)**: like And, but the conclusion target is *augmented* with
the cut formula `θ ∧ ¬θ` as a new disjunct of the running goal. See §3
of this doc for the local augmentation.

**Contraction (C)**: see Hughes p.28 for the duplicator construction.
Not needed for end-to-end ZFC; punt unless required.

**CloseByLemma**: see `LKR_TO_COMB_DESIGN.md §4.11`. Strategy A
inlining renders this op invisible to the walk; no per-rule handler
needs to change for F2.

### 2.3 Why portion-closure holds automatically

In `G(H_i) = G(Γ_i) + G(ϕ_i)`, the vertex set `V_{G(ϕ_i)}` is one half
of a top-level parallel composition. It is:

- **Adjacency-closed**: no cograph edges cross a `+` composition.
  Vertices in `V_{G(ϕ_i)}` have edges only to other vertices in
  `V_{G(ϕ_i)}`, never to `V_{G(Γ_i)}`.
- **Binding-closed**: binders in `G(ϕ_i)` have binding edges only to
  atoms inside their (formula-level) scope, which is in `V_{G(ϕ_i)}`.

The skew bifibration `f_i : K_i → G(H_i)` then guarantees the preimage
`f_i^{-1}(V_{G(ϕ_i)})` is also a portion in `K_i` (closure under
adjacency follows from the fibration condition on cograph edges;
binding closure follows from the same condition on binding edges).

This is Hughes's Lemma 11.2's "routine verification". With per-hypothesis
targets, fusion at the preimages is fusion at portions — Def 10.4
applies cleanly and produces a valid fograph (Lemma 10.5).

## 3. §15 cuts under F2

Hughes §11 (the per-rule framework) is cut-free. §15 adds cuts as an
extension; the augmented goal `(goal ∨ ⋁(θ_i ∧ ¬θ_i))` is the witness
target for a proof with cuts.

Under F2, cut augmentation happens **locally at each cut node**, not as
a global accumulator:

**Cut(θ)**: hypotheses `H_L = Γ_L, θ` and `H_R = Γ_R, ¬θ`, conclusion
`C = Γ_L, Γ_R`. Define the **augmented conclusion**
`C' = Γ_L, Γ_R, (θ ∧ ¬θ)`. The cut node's target is `G(C')`.
- Left subproof's target is `G(H_L) = G(Γ_L) + G(θ)`.
- Right subproof's target is `G(H_R) = G(Γ_R) + G(¬θ)`.
- Embed each via `z_i : G(H_i) → G(C')` where the `θ` and `¬θ` portions
  fuse into the new `(θ ∧ ¬θ)` summand.
- Apply the ∧-rule fusion at `P_L = f_L^{-1}(V_{G(θ)})` and
  `P_R = f_R^{-1}(V_{G(¬θ)})`.

The final root proof's target is the augmented goal — same as today's
contract — but now built compositionally rather than via a shared
canonical accumulator built up front.

The current `cut_augment.cpp` pre-pass is **removed**. Its job
(building the §15-augmented canonical target and tracking cut positions
in it) is replaced by per-cut local augmentation, which falls out of
the same machinery as `rule_and`.

## 4. Architecture

```
                  Program<lkr::Instr>
                          │
                          ▼
                ┌───────────────────┐
                │   input gate      │  LKRVerifier; reject if input
                │                   │  doesn't verify.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   tree rebuild    │  Reconstruct branching tree
                │                   │  (unchanged from current).
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   walk            │  Recursive bottom-up:
                │                   │  each call returns
                │                   │  (CombProof, G(sequent)).
                │                   │  Per-rule operations build
                │                   │  conclusion target from
                │                   │  child(ren)'s target +
                │                   │  rule's structural addition.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   output gate     │  CombVerifier against the
                │                   │  root's target (= the
                │                   │  augmented goal, built
                │                   │  compositionally).
                └─────────┬─────────┘
                          ▼
                    comb::CombProof
```

Key infrastructure changes:

- **`Fograph::build_from_sequent(entries)`** — new utility that
  constructs `G(ψ_1) + G(ψ_2) + …` for a sequent. Used at leaf nodes
  to build the initial target and inside per-rule operations to
  construct `G(C)`.
- **`WalkState`** — refactored to be a per-node return value, not a
  global mutable. Each node returns `{ source, target, fibration }`.
- **`cut_augment.cpp`** — removed (the running-goal accumulator is gone).
- **`alpha_rename.cpp`** — re-evaluated. The current pre-pass aligns
  LKR `Forall.eigen` to the shared target's binder vars. Under F2,
  each binder's var lives in its conclusion target, allocated when the
  per-rule operation builds it. The alignment becomes per-rule
  (potentially simpler) or is replaced by direct var management.
- **`derive_binding_edges` post-pass** — kept; the source's binding
  edges are derived from labels regardless of target architecture.

## 5. Soundness contract

**Input gate (unchanged)**:
`LKRVerifier::verify(ctx, goal_formula, input) = Ok`.

**Output gate (unchanged externally)**:
`CombVerifier::verify(ctx, augmented_goal, output) = Ok`.

Translator bug ⇒ output-gate Error. Same gate-enforcement story.

The internal invariant strengthened by F2: every intermediate
`walk_node`'s return value is a valid CombProof against its conclusion
target (per Lemma 11.2). This makes the per-rule operations
locally-checkable; CombVerifier acceptance at the root is no longer
the only safety net.

## 6. Completeness contract

For every input that LKR-verifies, F2's `walk` produces an `Ok(cp)`
such that `CombVerifier::verify` accepts `cp` against the augmented
goal. This is the same Theorem A as the current architecture, but
now provable by the paper's Lemma 11.2 directly (one rule at a time)
rather than relying on the shared-target invariants we've been
accidentally maintaining.

**Coverage gained.** F2 handles wrapped goals with nested quantifiers
(the axiom_rewrap Phase 6 blocker) by construction — there's no
"cotree limit" anymore, because the per-rule operations preserve Def 3.2
locally and CombVerifier's C.2 check never finds a non-singleton
binder.

## 7. Implementation

There's no live system to migrate — `LKRtoComb` is one translator with
one external contract. The work is a direct rewrite. Steps, in the
natural order of dependency (any deviation from this order is fine
since the type checker will force consistency):

1. **`Fograph::build_from_sequent(entries) → Fograph`** — pure utility
   that constructs `G(ψ_1) + G(ψ_2) + …` for a sequent.
2. **`walk_recursive` signature change** — each call returns
   `(source, target, fibration)` against the per-hypothesis target,
   not against a shared accumulator. `WalkContext` loses
   `canonical_target` (and any field that only existed to support the
   shared target).
3. **Per-rule handlers** — rewrite each to take child target(s) and
   produce the conclusion target locally per Hughes §11.1 (§2.2 of
   this doc). Order: leaves first (`AxiomLit`, `One`,
   `CloseByLemma`-leaf fallback), then linear (`Or`, `Exchange`,
   `Weakening`, `Contraction`), then `Forall` / `Exists`, then `And`,
   then `Cut`.
4. **`cut_augment.cpp` deletion** — `rule_cut` builds its conclusion
   target with the `(θ ∧ ¬θ)` augmentation locally. The global
   accumulator is gone.
5. **`alpha_rename.cpp` re-evaluation** — per `[[open question §10]]`,
   probably deletable. Decide by trying to remove it and seeing if
   tests fail; if they do, identify the remaining need and either keep
   it or replace it with a local per-rule binder-var allocation.
6. **Test gate**: full suite (8 targets) green AND the two Phase 6
   `#if 0`-disabled tests pass after flip:
   - `test_integration_nested_forall_axiom`
   - `test_integration_zfc_eq_refl`
   If those don't pass, the diagnosis was incomplete — investigate.
7. **Docs**: update `LKR_TO_COMB_DESIGN.md` to mark its §3–§4 as
   superseded by this doc. Update `COMPLETENESS.md §4.1` Forall /
   Exists / And / Cut rows with F2 implementation references and
   promote §4.3 (axiom_rewrap row) to done.

## 8. Test plan

Completeness gates for declaring F2 done:

1. **Regression** — every test in `lkr_to_comb_test.cpp`,
   `nd_to_lkr_test.cpp`, `comb_test.cpp`, `axiom_rewrap_test.cpp`
   still passes.
2. **Nested-quantifier validation** — `test_integration_nested_forall_axiom`
   (proves the C.2 limit is gone for synthetic cases).
3. **ZFC end-to-end** — `test_integration_zfc_eq_refl` (proves real
   ZFC theorems flow through; promotes COMPLETENESS §4.3 axiom_rewrap
   row to done).

Stretch (post-F2, separate obligation): run all theorems in
`zfc/basics/ordered_pair.fol.proof` and `functions.fol.proof` through
the full pipeline.

## 9. Edge cases

- **Empty Γ**: `G(C) = G(ϕ)` for a singleton-conclusion. Per-hypothesis
  target is just `G(ϕ)`. Builds correctly.
- **CloseByLemma**: invisible after Strategy A inlining (lemma_inliner
  pre-pass). The post-inline LKR program contains no `CloseByLemma`
  ops, so no special handling in F2.
- **Alpha-rename interaction**: the current pre-pass aligns LKR's
  `Forall.eigen` to canonical binder vars in the shared target. Under
  F2, binder vars are allocated when the per-rule operation constructs
  its conclusion target — the alignment becomes a local operation in
  `rule_forall` / `rule_exists`, possibly simplifying or eliminating
  the pre-pass.
- **Mixed strong/weak in And/Cut**: handled per Hughes — the weak side
  is dropped, only the strong side's CombProof maps into `G(C)`.
- **Fograph construction depth**: deeply nested formulas may produce
  large targets. Same as today; no change.

## 10. Open questions

- **Alpha-rename obsolescence**: can the current alpha-rename pre-pass
  be removed entirely under F2, since binder vars are allocated by the
  per-rule operations directly? Decide during Phase C.
- **Composition with axiom_rewrap's wrap**: the wrapped goal
  `H → φ` is a top-level implication. NDtoLKR emits it as a sequent
  with a final `Or` over `(¬H, φ)` (after NNF). The F2 walk should
  handle this with no special treatment, but verify during Phase E.
- **Cost**: F2 builds many small intermediate targets (one per node)
  vs. one big shared target. Estimated overhead ≈ proportional to
  total source vertex count — should be a small constant per source
  vertex. Measure during Phase E.
- **Migration ordering**: §7 phases A → F are sequential. Phases B and
  C could potentially be interleaved per-rule (refactor one rule
  end-to-end, then the next). Decide once we see how invasive Phase C
  is for the first rule.

## 11. References

- Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236
  — §3 (fographs, Def 3.1, Def 3.2), §10.1.1 (fusion, Def 10.3,
  Def 10.4, Lemma 10.5), §11.1 (per-rule operations, Lemma 11.2),
  §15 (cuts).
- `LKR_TO_COMB_DESIGN.md` — current (shared-target) architecture. This
  doc supersedes its §3 (Architecture) and §4 (Per-rule operations)
  once F2 lands.
- `COMPLETENESS.md §4.1` — Forall / Exists / And / Cut rows are
  re-audited as part of F2 Phase F.
- `axiom_rewrap_test.cpp` — Phase 6 Tests 4 + 5 are the validation
  gate for F2 success.
