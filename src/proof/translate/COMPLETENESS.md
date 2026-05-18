# Completeness — sound + complete translations end-to-end

Pipeline:

```
ND  ──iota_elim──▶  ND(iota-free)  ──NDtoLKR──▶  LKR  ──LKRtoComb──▶  CombProof
                                                            (≤§11 + §15)
```

This document states the completeness theorems we owe and tracks the
per-rule obligations needed to discharge them. Each row in the
obligation tables links to a math spec, the implementation, and the
test that closes the obligation.

## 0. Framework

Two ambient results from Hughes 2019, *First-order proofs without
syntax*, arXiv 1906.11236:

- **Theorem 6.4** — combinatorial proofs are sound and complete for
  classical first-order validity: a formula φ is classically valid iff
  it has a combinatorial proof `(N, G(φ), f)`.
- **Theorem 15.1** — *cut* combinatorial proofs (combinatorial proofs
  of `φ ∨ ⋁ (θ_i ∧ ¬θ_i)`) are sound and complete for the same.

The combinatorial proof system itself is not our concern; we trust
`CombVerifier` to enforce Def. 5.3 (fonet) + Def. 4.1 (skew bifibration)
+ Hughes §15 augmentation.

**What's ours to prove**: each translator emits well-formed output for
every accepted input. Composed with the ambient theorems, this lifts to
end-to-end completeness.

## 1. Soundness — already discharged

Each translator runs the downstream verifier on its own output before
returning (`OutputGate`). A translator bug therefore manifests as a
boundary `Error`, never as silent unsoundness in the combinatorial
proof object.

```
NDtoLKR.apply        ⊢ LKRVerifier(φ, output) = Ok
LKRtoComb.apply      ⊢ CombVerifier(augment_§15(φ), output) = Ok
iota_elim.apply      ⊢ NDVerifier(φ, output) = Ok  (iota-free)
```

No further proof needed.

## 2. Completeness — what we owe

### Theorem A (LKR → Comb)

For every formula φ and every `Q : Program<lkr::Instr>` with
`LKRVerifier(φ, Q) = Ok`,

```
LKRtoComb(φ, Q) = Ok(cp)   with   CombVerifier(augment_§15(φ), cp) = Ok.
```

**Proof method.** Induction on the derivation tree built by
`tree.cpp::rebuild_tree`. Each node's case is closed by the per-rule
math spec listed in §4.x of `LKR_TO_COMB_DESIGN.md`:

- **Leaf cases** (AxiomLit, One, CloseByLemma) — base combinatorial
  proofs of the closed sequent.
- **Linear cases** (Exchange, Weakening, Contraction, Or, Forall,
  Exists) — apply the §11.1 per-rule operation to the child's CombProof.
- **Branching cases** (And, Cut) — fuse children's CombProofs per
  §11.1 ∧-rule (Cut uses the same fusion, augmenting the running goal
  per §15).

The shared canonical target `Fograph(augment_§15(φ))` ensures Cut- and
Weakening-introduced entries have stable positions; the alpha-rename
pre-pass (LKR_TO_COMB_DESIGN.md §7.5) ensures LKR Forall eigens match
Fograph's canonical binder vars; the label-derived binding-edge
post-pass (§7.5) ensures source binding edges follow Hughes Def. 3.1.

### Theorem B (ND → LKR)

For every formula φ and every iota-free `P : Program<nd::Instr>` with
`NDVerifier(φ, P) = Ok`,

```
NDtoLKR(φ, P) = Ok(Q)   with   LKRVerifier(φ, Q) = Ok.
```

**Proof method.** Structural induction on the block tree built by
`block_tree.cpp::decompose_blocks`. Each block kind is closed by a
dispatch handler emitting the cut-spine pattern:

- `FORALL` block — Cut + Forall + body translation.
- `IMPLIES` block — Cut + Or + body translation.
- `NOT` block — Cut + Exists/Forall + body translation (analogous).
- `EXISTS_ELIM` block — Forall on the witness binder + body.
- `OUTER` block — body translation + final `emit_close` between qed
  slot and step_to_neg_idx[target].

Flat ND ops are translated by `dispatch_close` (one per ND rule).

### Composition (ND → Comb)

For every iota-free `P` with `NDVerifier(φ, P) = Ok`,

```
LKRtoComb(φ, NDtoLKR(φ, P)) = Ok(cp)
with CombVerifier(augment_§15(φ), cp) = Ok.
```

By Theorem A applied to Theorem B's output. Combined with iota-elim's
completeness on its scope (see [LAYER2_LEISENRING_DESIGN.md] and
memory `iota-translator-state-2026-05-17`), the *full* ND → Comb
pipeline (including iota) is complete on the subset (iota-free) ∩
(translator-supported rules).

## 3. Soundness/completeness of the combinatorial witness

`CombVerifier(augment_§15(φ), cp) = Ok` implies `augment_§15(φ)` is
classically valid (Thm 6.4). The augmentation is classically equivalent
to φ (each `θ ∧ ¬θ` is contradictory), so φ is classically valid (Thm
15.1).

So a successful translation chain is a constructive validity witness
for φ — exactly what a proof object should provide.

## 4. Obligation tables

A row is **done** when the math spec exists, the implementation lands,
and a test exercises the rule under the relevant verifier gate.

### 4.1 LKR → Comb (per-rule, Theorem A)

| Rule         | Math spec                          | Implementation                       | Test                                  | Status   |
|--------------|------------------------------------|--------------------------------------|---------------------------------------|----------|
| AxiomLit     | LKR_TO_COMB_DESIGN.md §4.1         | walk.cpp::build_leaf_axiom_lit       | lkr_to_comb_test::self_implication    | ✓ done   |
| One          | LKR_TO_COMB_DESIGN.md §4.2         | walk.cpp::build_leaf_one + fograph.cpp | lkr_to_comb_test::one_minimal/with_sibling, comb_test::builder_one_* | ✓ done   |
| Exchange     | LKR_TO_COMB_DESIGN.md §4.3         | walk.cpp (no-op linear)              | covered by and_commute                | ✓ done   |
| Weakening    | LKR_TO_COMB_DESIGN.md §4.4         | walk.cpp + input_gate.cpp::check_no_load_bearing_weakening | weakening_scaffolding + weakening_load_bearing_rejected | ✓ done   |
| Contraction  | LKR_TO_COMB_DESIGN.md §4.5         | walk.cpp (no-op linear)              | contraction_after_cut                 | ✓ done   |
| Or           | LKR_TO_COMB_DESIGN.md §4.6         | walk.cpp (no-op linear)              | covered by self_implication           | ✓ done   |
| Forall       | LKR_TO_COMB_DESIGN.md §4.7 + §7.5  | walk.cpp::rule_forall                | forall_em + nd_to_comb_forall_self    | ✓ done   |
| Exists       | LKR_TO_COMB_DESIGN.md §4.8 + §7.5  | walk.cpp::rule_exists                | nd_to_comb_forall_self                | ✓ done   |
| And          | LKR_TO_COMB_DESIGN.md §4.9         | walk.cpp::rule_and                   | and_commute                           | ✓ done   |
| Cut          | LKR_TO_COMB_DESIGN.md §4.10 + §15  | walk.cpp::rule_cut + cut_augment     | cut_no_use, cut_with_lemma            | ✓ done   |
| CloseByLemma | LKR_TO_COMB_DESIGN.md §4.12        | lemma_inliner.cpp (Strategy A)       | cut_with_lemma + cut_with_forall_lemma + cut_with_exists_lemma + inline_hand_crafted_cut_lemma + inline_lemma_with_cuts | ✓ done |

**`Weakening`** (✓ done — scope-restricted to scaffolding case).

The spec distinguishes two cases:
- **Scaffolding** (weakened entry never referenced): supported by the
  no-op handler in `walk`. CombProof witnesses `goal_nnf` directly; no
  target augmentation is needed because the source has no vertices in
  `G(φ)`.
- **Load-bearing** (weakened entry used by later ops): out of scope.
  Rejected by the input-gate check `check_no_load_bearing_weakening`
  with a clear diagnostic pointing at the offending position
  reference. The §15 trick doesn't generalize uniformly here:
  `goal ∨ φ` is not classically equivalent to `goal` when `φ`
  isn't contradictory (unlike §15's `(θ ∧ ¬θ)`).

**`CloseByLemma`** (✓ done — Strategy A via `LKR_TO_COMB_DESIGN.md §4.12`).
The lemma registry stores LKR programs (not CombProofs). The
`lemma_inliner` pre-pass splices each lemma's LKR ops into the outer
program at the `CloseByLemma` point; the combined program is then
translated normally (alpha-rename + cut_augment + walk). Lemma cuts
propagate into the outer's augmented goal naturally — no
CombProof-level composition is needed.

Soundness: by gate (combined program LKR-verifies; resulting CombProof
verifies against the combined augmented goal).
Completeness: every registered lemma composes, regardless of internal
cuts or quantifier structure. Verified by `cut_with_lemma`,
`cut_with_forall_lemma`, `cut_with_exists_lemma`, the cut-bearing
`inline_hand_crafted_cut_lemma`, and the NDtoLKR-emitted
`inline_lemma_with_cuts`.

The dual σ remap leaf builder (`build_leaf_close_by_lemma` per §4.11)
is retained as a safety net — it errors clearly if a `CloseByLemma`
op survives the inliner pre-pass.

### 4.2 ND → LKR (per-rule, Theorem B)

Input-gate exclusions (rejected, so not in scope): `IotaElim`, `EqSubst`,
`EqSym` — must be eliminated upstream (`iota_elim` translator).

| ND op                      | Role                                  | Implementation                                   | Status |
|----------------------------|---------------------------------------|--------------------------------------------------|--------|
| Fix                        | opener of FORALL block                | block_tree.cpp / translate_block_forall          | ✓ done |
| Assume                     | opener of IMPLIES or NOT_ block       | block_tree.cpp / translate_block_implies, _not   | ✓ done |
| Let                        | no-emit (inert)                       | classifier in cut_spine.cpp                      | ✓ done |
| Use                        | dispatch_close → CloseByLemma         | cut_spine.cpp::close_use                         | ✓ done |
| SchemaInst                 | dispatch_close → CloseByLemma         | cut_spine.cpp::close_schema_inst                 | ✓ done |
| ForallElim                 | dispatch_close → Exists + emit_close  | cut_spine.cpp::close_forall_elim                 | ✓ done |
| AndIntro / AndElimL / R    | dispatch_close → And + emit_close     | cut_spine.cpp::(anonymous)                       | ✓ done |
| OrIntroL / R / OrElim      | dispatch_close → Or + emit_close      | cut_spine.cpp::(anonymous)                       | ✓ done |
| ImpliesIntro               | closer of IMPLIES block               | cut_spine.cpp::translate_block_implies           | ✓ done |
| ImpliesElim                | dispatch_close                        | cut_spine.cpp::(anonymous)                       | ✓ done |
| NotIntro                   | closer of NOT_ block                  | cut_spine.cpp::translate_block_not               | ✓ done |
| NotElim                    | no-emit (consumed by NotIntro / BottomElim) | classifier                                  | ✓ done |
| BottomElim                 | dispatch_close (via ghost-⊥ pairing)  | cut_spine.cpp::(anonymous)                       | ✓ done |
| IffIntro / IffElimL / R    | dispatch_close                        | cut_spine.cpp::(anonymous)                       | ✓ done |
| ForallIntro                | closer of FORALL block                | cut_spine.cpp::translate_block_forall            | ✓ done |
| ExistsIntro (flat)         | dispatch_close                        | cut_spine.cpp::(anonymous)                       | ✓ done |
| ExistsIntro (block-closer) | closer of EXISTS_ELIM block           | cut_spine.cpp::translate_block_exists_elim       | ✓ done |
| ExistsElim                 | opener of EXISTS_ELIM block           | block_tree.cpp / translate_block_exists_elim     | ✓ done |
| DoubleNegElim              | dispatch_close                        | cut_spine.cpp::(anonymous)                       | ✓ done |
| ExcludedMiddle             | dispatch_close                        | cut_spine.cpp::(anonymous)                       | ✓ done |
| Qed                        | closer of OUTER block                 | cut_spine.cpp::translate_outer                   | ✓ done |
| Peirce                     | dispatch_close → Cut + Or + And + emit_close | cut_spine.cpp::(Peirce branch) + parser keyword | ✓ done |
| ClassicalAbsurd            | closer of CLASSICAL_ABSURD block      | cut_spine.cpp::translate_block_classical_absurd  | ✓ done |

Re-audit this table whenever `cut_spine.cpp` / `block_tree.cpp` change.

### 4.3 Cross-cutting

| Item                          | Spec                              | Status |
|-------------------------------|-----------------------------------|--------|
| Axiom CombProofs (deduction)  | AXIOM_REWRAP_DESIGN.md            | spec done; Phases 1 (TheoremAxiomMap) + 2 (boundary wrap) impl + tests landed; Phases 3–7 open |
| Corpus measurement (isa2fol)  | n/a                               | open   |
| NDtoLKR emission for `One`    | LKR_TO_COMB_DESIGN.md §4.2 (end)  | open   |

The "NDtoLKR emission for `One`" row tracks an enhancement to
`translate_block_not` (or Fograph) so that ND proofs producing the
truth literal `¬⊥` flow end-to-end. The LKR→Comb side is done;
NDtoLKR currently never emits `lkr::One` ops.


The earlier "Cut-free lemma export" row was dissolved by Strategy A
(§4.12): lemma reuse now works regardless of internal cuts.

## 5. Out-of-scope inputs

Inputs that the pipeline rejects at the input gate (and therefore for
which completeness is **not** claimed):

- ND proofs containing iota terms (iota-elim is a separate translator;
  apply it first).
- (Contraction and One are both supported now; the prior version of
  this list excluded them.)
- LKR programs with `CloseByLemma` referencing a lemma whose CombProof
  has a non-empty dualizer (until row CloseByLemma is "done").
- Hand-crafted LKR programs whose `FormulaSource`s are deferred AST
  nodes (`cut_augment.cpp` rejects these).

## 6. References

- Hughes 2019, arXiv 1906.11236.
- `LKR_TO_COMB_DESIGN.md` — per-rule math specs for Theorem A.
- `ND_TO_LKR_DESIGN.md` — per-rule math specs for Theorem B.
- `LAYER2_LEISENRING_DESIGN.md` — iota-elim translator's completeness scope.
