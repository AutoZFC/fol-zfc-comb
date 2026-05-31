# LKR weakening fix — sound, goal-directed, KS1-faithful structural rules

**Status:** LANDED (phases W0–W2 + the LKR→comb path deletion). Companion to
the LKR→KS1 pivot (`memory: project_lkr_ks1_pivot_2026_05_31`). Full suite
green (23/23); only the pre-existing, unrelated `//zfc/naturals` serialization
bug remains red. What shipped: `Weakening{idx}`=drop + new `Duplicate{src}`=copy
in the verifier (rejects the ⊢P fabrication); deriv IR `RWeaken`(drop)/
`RDuplicate`(copy) + validate canary; b0 additive→mult bridge now emits
`RDuplicate`; NDtoLKR And fan-out migrated to `Duplicate`. The direct
LKR→comb fold (`lkr_to_comb/`) + `lkr_weak_elim/` + `input_gate` I-2 were
deleted (route is now LKR→KS1→comb); `comb_checker` ends at `LKRVerifier`.

## 0. The defect

The LKR verifier is **goal-directed**: it seeds `open_goals = [[goal]]` and
each op rewrites the current goal into subgoal(s); a program is accepted when
every goal is closed by an axiom. Soundness of such a checker requires every
op to be a **sound reduction**:

> *(all subgoals valid) ⟹ (the rewritten goal valid)*, where `⊢ Γ` is valid
> iff `⋁Γ` is classically valid (Hughes 2019 §11; HSW 2021 §II-B).

Checking each op against this criterion:

| op | rewrite (goal → subgoal) | sound reduction? |
|----|--------------------------|------------------|
| Or / And / Cut / Exchange / ∀ / ∃ | decompose the goal | ✓ |
| Contraction `Γ,φ,φ → Γ,φ` | merge a duplicate | ✓ (`φ=φ` ⇒ `⋁` unchanged) |
| **Weakening `Γ → Γ,φ` (φ arbitrary)** | **append a formula** | **✗ — needs `⋁(Γ,φ)` valid ⟹ `⋁Γ` valid, false** |

Weakening is the only unsound op. Empirically the verifier accepts a 2-op
"proof" of the non-valid `⊢ P` (`Weakening(¬P); AxiomLit`). The soundness of
the *pipeline* today is rescued downstream (the `lkr_to_comb` InputGate I-2
rejects "load-bearing" weakening; the `weak_elim` pass removes others), **not**
by the verifier. The verifier — the thing we are about to feed into LKR→KS1 —
is not itself a soundness gate.

Root cause: the structural ops are oriented in the **derivation** direction
(Hughes `W : Γ / Γ,φ` reads conclusion-below, so "append" is correct *forward*)
while the verifier runs **backward**. Read backward, Hughes `W` **drops**; the
code appends. The logical ops were already written backward (decompose), so
only the structural ops are inconsistent.

## 1. What NDtoLKR actually needs weakening for

NDtoLKR never weakens in a *fresh* formula. Its only use (`intros.cpp` ×3,
`dispatcher.cpp` ×1) is to **duplicate an existing entry** so the
*multiplicative* `And` (`Γ,φ ∆,θ / Γ,∆,φ∧θ`, partitioned context) can hand a
copy of a shared formula to each branch. Appending a *duplicate* is a sound
reduction (`⋁(Γ,ψ,ψ) = ⋁(Γ,ψ)`), which is why the pipeline is sound in
practice. But "duplicate a present formula" is **contraction read backward**,
not weakening. The two rules were conflated under one op.

(The same conflation lives in `lkr_cut_elim/b0.cpp`: the additive→multiplicative
bridge merges `Γ,Γ → Γ`, which CUT_ELIM_DESIGN §4 correctly calls *contraction*,
but the code emits `RWeaken`. The fix disentangles this too.)

## 2. Corrected rules (all goal-directed, all sound reductions)

Split the conflated op into three honest structural primitives. `idx`/`src`
are positions in the **current goal** (the rule's own conclusion).

| op | rewrite (goal → subgoal) | sound because | HSW rule (derivation dir.) | → KS1 |
|----|--------------------------|----------------|----------------------------|-------|
| `Weakening{idx}` | `Γ,φ → Γ` (drop entry `idx`) | `⋁Γ ⟹ ⋁(Γ,φ)` | `wk : Γ / Γ,φ` read ↑ | `w` |
| `Duplicate{src}` | `Γ,φ → Γ,φ,φ` (append copy of `src`) | `⋁(Γ,φ,φ)=⋁(Γ,φ)` | `ctr : Γ,φ,φ / Γ,φ` read ↑ | `c` |
| `Contraction{i,j}` | `Γ,φ,φ → Γ,φ` (drop `j`, requires `=`) | `⋁(Γ,φ,φ)=⋁(Γ,φ)` | `ctr` read ↓ | `c` |

- `Weakening` flips from append-a-formula to **drop-an-index**. Now sound;
  `⊢P` is rejected (there is nothing to drop that produces an axiom).
- `Duplicate` is **new**. It is what NDtoLKR's And-fan-out uses. Sound.
- `Contraction` (existing merge) is unchanged; it stays for the B0 cut bridge
  and any genuine merge. Both `Duplicate` and `Contraction` map to KS1 `c`
  (they are the two directions of the same contraction).

This makes the verifier internally consistent (every op a sound reduction),
makes the cut-elim IR uniform (no "reversed-W"), and makes the LKR→KS1
translation (HSW Thm 29: `wk→w`, `ctr→c`, permute down) a direct per-op map.

## 3. The KS1 correspondence (why this is the point)

HSW Thm 29 translates a **cut-free** LK1 proof to KS1 by replacing `wk`/`ctr`
with deep-inference `w`/`c` and permuting them into the resource phase Φ2.
With §2's rules the map is mechanical:

```
  LKR Weakening{idx}  ⟶  KS1  w   (S{A} / S{A∨B})
  LKR Duplicate{src}  ⟶  KS1  c   (S{A∨A} / S{A})     [the fan-out copies]
  LKR Contraction{i,j}⟶  KS1  c
  LKR Exchange / Or / And / ∀ / ∃ / Ax / One / Cut(after Stage-3 elim) ⟶ … (later phase)
```

Cut is gone before this point (Stage 3 = HSW Thm 2), so the KS1 image is
cut-free as required.

## 4. Blast radius & phase plan

**W1 — LKR core + verifier (this is the soundness fix).**
- `ops.h`: `Weakening{ size_t idx }`; add `Duplicate{ size_t src }`. Drop the
  `FormulaSource` from `Weakening`.
- `verifier.cpp`: `exec Weakening` = bounds-check + `entries.erase(idx)`;
  `exec Duplicate` = bounds-check + `entries.push_back(entries[src])`.
- `lkr_verifier_test.cpp`: rewrite the two weakening tests to drop-semantics;
  add a test that the old `⊢P` shape is now **rejected**; add a `Duplicate`
  accept test. Keep the build green.

**W2 — propagate to the cut-elim IR + NDtoLKR.**
- `deriv.{h,cpp}`: `RWeaken{ size_t idx; child }` (child = node with `idx`
  removed); add `RDuplicate{ size_t src; child }` (child = node with a copy of
  `src` appended). Update `build`/`emit`.
- `validate.cpp`: RWeaken now child = node − {idx} (child SMALLER); RDuplicate
  child = node + copy (child BIGGER). This is the canary that the 05-27
  reversed-W bug can never recur.
- `b0.cpp`: the additive→mult bridge emits `RContract` (merge `Γ,Γ→Γ`), not
  `RWeaken`. (Disentangles the §1 secondary conflation.)
- `reduce.cpp`: RWeaken/RDuplicate clone + path cases.
- NDtoLKR `intros.cpp` ×3, `dispatcher.cpp`: emit `Duplicate{src}` instead of
  `Weakening{formula}` for And fan-out.
- Downstream on the **retiring** LKR→comb path (`interpret_tree`, `input_gate`
  I-2, `weak_elim`): adapt only enough to compile, or delete where the new
  semantics makes them dead. The InputGate I-2 "load-bearing" check is
  **subsumed** — drop-weakening cannot be load-bearing — so I-2 can go once
  the path is off NDtoLKR's old output. Decide per-file during W2.

**Done criterion (W1+W2):** the full suite is green; the verifier rejects the
`⊢P` weakening shape; NDtoLKR emits `Duplicate` (no append-weakening anywhere);
`validate` enforces RWeaken-drops / RDuplicate-grows. No corpus in the gate.

## 5. References
- Hughes 2019 §11 (LKR rules, hypothesis-above/conclusion-below), §11.1.
- HSW 2021 §VII (Thm 29 LK1→KS1; Thm 2 cut-elim), Fig. 6 (`w`,`c`,`ac`,`m…`).
- `CUT_ELIM_DESIGN.md` §4 (additive→mult = contraction).
- Memory: `project_lkr_ks1_pivot_2026_05_31`,
  `feedback_math_first_discipline`.
