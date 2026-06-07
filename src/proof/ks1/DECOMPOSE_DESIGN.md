# KS1 constructive decomposition (HSW 2021 Thm 17) — design gate

`decompose.cpp` today only **checks** `is_decomposed` and `split`s an
already-decomposed derivation. The corpus cut-free theorems fail here
(`split: not in Thm 17 decomposed form`) because `lkr_to_ks1` emits resource
steps (W / medials / Ac) **interspersed** with linear steps whenever a
weakening/contraction sits deep in the proof. This doc settles, before any
implementation, whether a **constructive** decomposition (reorganize an
arbitrary translated derivation into Φ1-linear ; Φ2-resource) exists for the
exact rules our translation emits.

## Target phase order (top→bottom, `decompose.h`)

Φ1 linear: `Axioms{Ai,Tu,ForallUnit}` → `Linear{Sw}` → `Inst{Ex}`.
Φ2 resource: `Medial{M,MForall,MExists}` → `Contraction{Ac}` → `Weakening{W}`.
`Eqv` (Comm/Assoc/AssocAnd/CommAnd/**DistForall**) is phase-flexible.

Emitted rule set (verified from `lkr_to_ks1.cpp`+`reconcile.cpp`): the above
only. **No** `Mix`, `WForall`, `CForall` — so those pairs need not be considered.

Decomposed ≡ the non-≡ steps are sorted by phase number; so decomposition is a
**stable phase-sort of the step list by adjacent transposition**, where each
transposition must be a *valid derivation rewrite* (replay-preserving).

## The structural lemma (why this is tractable)

`tr` emits a node's own steps AFTER its whole subtree (top-down KS1 = bottom-up
LKR). Hence:

> If step `X` is emitted before step `Y`, then `Y`'s node is not a descendant of
> `X`'s node ⇒ **`c_Y` (Y's context) is disjoint from, or a strict prefix
> (ancestor) of, `c_X`.** Equivalently: the earlier step is always at a
> *deeper-or-disjoint* position than the later one. Never equal, never `c_X ⊂ c_Y`.

## Commutation theorem

For an out-of-phase adjacent pair `(X earlier/deeper, Y later/shallow)`, the
swap `(X;Y) → (Y;X′)` (X′ = X with its context recomputed under Y's
restructuring, + de Bruijn shift if Y crosses a binder over X's redex) is a
valid rewrite **iff Y's premise still matches the formula *before* X ran** — i.e.
**unless X created the material Y's redex depends on.**

Two facts close it:

1. **No rule deletes or duplicates a proper sub-position, except `Ac`** (which
   deletes one copy of an *atom*). So Y relocating X's redex subformula
   (recompute path) is always well-defined — and `Ac` can never delete X's redex,
   since X's redex would have to be strictly inside an atomic literal (none
   exists). ⇒ The path-recompute side is always fine.

2. **The "X created what Y needs" obstruction** can only involve a *creating*
   rule X ∈ {W, Ai, Tu, ForallUnit, M} and a Y that consumes that creation.
   Walking the phase-sort's actual swaps (move higher-phase later / lower-phase
   earlier):
   - linear×linear, resource×linear, medial×contraction, anything×Ex/ForallUnit:
     Y's redex is the *shallow* top connective and pre-exists X (X only changed
     something strictly inside) ⇒ **clean swap** (+ de Bruijn shift under
     `Ex`/`ForallUnit`/`DistForall`; the depth-aware machinery already exists,
     K6.2b).
   - The **one** genuine obstruction: `X = W` (adds inert formula `B`) and
     `Y ∈ {M, Ac}` acting **inside that weakened `B`**. Phase wants `M`/`Ac`(4/3)
     before `W`(5), but `M`/`Ac` *depend on* `B` existing ⇒ the swap is invalid
     (Y's premise absent before X). This is the classic
     **weakening–contraction interaction**, resolved not by permutation but by a
     **weakening-absorption rewrite**: a resource step acting entirely within
     weakened material is absorbed into the weakening — weaken in the
     *post-resource* formula and **delete** the medial/Ac. Always possible
     (weakening admits any formula), and it strictly reduces the step count, so
     it terminates.

## Verdict

**A constructive decomposition EXISTS for the translation's rule set.** It is:

1. **Phase-sort by adjacent transposition.** Every cross-phase swap is a clean
   replay-preserving rewrite (path-recompute + binder de Bruijn shift), by the
   commutation theorem.
2. **Weakening-absorption** for the sole non-commuting class (medial/`Ac` inside
   weakened material): drop the resource step, weaken in its output.
3. `Eqv` steps are carried along (phase-flexible; commute as ≡ relocations,
   `DistForall` with a binder de Bruijn shift).

No pair is *fundamentally* non-commuting; the apparent one is a rewrite, not a
wall. This does **not** change the comb proof (same fonet/fibration) — it is
bridge-enabling, orthogonal to cut-elim/contraction minimality.

## Implementation caveats (for step (b))

- **de Bruijn shifts** when transposing across `Ex`/`ForallUnit`/`DistForall`
  (a step moving under/out of a binder shifts its `f_param`/`t_param` generalized
  indices by ±1). Reuse `lkr_to_ks1`'s depth-aware rebind.
- **Weakening-absorption bookkeeping**: a medial/Ac may act *partly* inside
  weakened material; absorb only the part inside `B`, keep the rest. Detect "redex
  ⊆ a weakened entry" by tracking which entries a `W` introduced.
- **`Ac`-vs-`M` dependency** (need `M` before `Ac`): expected clean (Ac yields an
  atom; M needs ∧-structure) — verify no medial consumes an Ac output.
- **Oracle**: `ks1::check` (permuted derivation replays to the same goal mod ≡) +
  full `CombVerifier` on the corpus cutfree theorems; `is_decomposed` must hold on
  the output so `split` then succeeds.
