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

## CORPUS REVISION (2026-06-09): pairwise swap is INSUFFICIENT

The verdict above is **wrong for the translation's actual output**. After the
Option-A front-end fix, all corpus cut-free theorems produce VALID KS1 and reach
`decompose`, where they get stuck. The constructive bubble (adjacent
transposition + the self-verifying `try_swap`) provably CANNOT decompose them,
for a reason the verdict missed:

**Linear steps thread RESOURCE-built material via Eqv reshapes.** Concretely in
`eq_refl`: a chain of `W`s builds the context `Γ_R` deep in the right conjunct;
~15 `Eqv` steps then reshape `Γ_R∨ψ → ψ∨Γ_R` (the reconcile/CommOr bureaucracy);
finally a `Sw` at the shallow `∧` splits `ψ∨Γ_R` (`B=ψ`, `C=Γ_R`). So:

  `Sw` (linear) ──depends-on──▶ `Eqv` reshapes ──depend-on──▶ `W`s (resource).

The `Sw` is BELOW the Eqvs; the `W`s are ABOVE them. To decompose we must move the
`W`s below the `Sw`. But each reshaping `Eqv` genuinely consumes its `W`'s output
(`try_swap` correctly fails `y-no-match-before-x`), so the `W` is anchored above
its Eqvs and can never reach — let alone pass — the `Sw` by transposition.

This is NOT the "resource inside weakened material" obstruction (that's
resource×resource, intra-Φ2, irrelevant to the boundary). It is a **linear step
transitively consuming resource output** — which no permutation can fix, because
permutation preserves each step's redex-dependency edges.

The boundary blockers observed (ordered_pair, all 4 cut-free theorems):
`W before Sw`, `M before Sw`, `M before Ex` — every one is a linear step whose
redex (directly or via Eqv) depends on resource-built structure. (The many
`Ac before M`, `Ac before MExists`, `W before M` "stuck" reports are intra-Φ2 and
do NOT violate `is_decomposed`.)

### What's actually required: the splitting construction (not permutation)

Decomposed form needs the **weakening-free linear skeleton** `A'` and the deferred
resource phase:
  - Φ1 proves `A'` = `d.bottom` with every weakened disjunct (and contracted
    duplicate) EXCISED — the bare axiom/switch skeleton over the principal
    formulas only.
  - Φ2 weakens those disjuncts back in (top-level `W`) and re-contracts, reaching
    `d.bottom`.

A `Sw` that only threads weakened material has NO counterpart in the skeleton: in
`A'` the context `Γ_R` is absent, so `ψ∨Γ_R` collapses to `ψ` and the switch
DISAPPEARS — its effect is replaced by a top-level weakening of `Γ_R` after the
`∧` is built. This is a step-count-CHANGING rewrite (delete the switch + its
threading Eqvs, add a top-level `W`), which the fixed-length pairwise-swap bubble
cannot express.

**Implementation direction (next):** replace/augment the bubble with an excision
pass. Candidate algorithm: for each resource disjunct `B` introduced by a `W`,
remove `B` from the goal-side and replay the whole derivation on the `B`-free
formulas (linear steps that merely threaded `B` now act on the smaller structure;
the threading `Sw`/Eqvs that become vacuous are dropped), yielding Φ1 over `A'`;
collect the removed `B`s as the Φ2 weakening list. Soundness oracle unchanged:
`ks1::check` on the rebuilt Φ1;Φ2 + full `CombVerifier`. This is the genuine
content of HSW Thm 17 splitting for our rule set; the "permutation + absorption"
verdict only covers the resource×resource tail.

### Landed this session (2026-06-09, sound but insufficient alone)

- `try_swap` Ex branch only engages on genuine binder-crossing
  (`is_prefix(y.ctx, x.ctx)`); disjoint-`x` Ex swaps fall through to the generic
  sentinel path, which handles the now-`gen` witnesses (post-Option-A) instead of
  bailing `Ex-nonfixed-witness`.
- `should_precede` also pushes a flexible `Eqv` before a resource-only step, so an
  Eqv a later linear step depends on does not anchor it behind the boundary
  (self-verified; an Eqv that truly consumes the resource simply stays).
- These cut the spurious no-swap failures and are necessary for the construction
  above, but do NOT by themselves decompose the corpus (the splitting rewrite is
  the missing piece).

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
