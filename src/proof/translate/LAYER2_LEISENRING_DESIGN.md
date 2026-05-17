# Layer 2 — ND-to-ND iota-free translator (Leisenring's ε-elimination)

## Status

Implemented and tested. `src/proof/translate/iota_elim/`. All 8 test
targets pass; iota translator handles its scope cleanly.

## 0. Goal

A sound + complete ND-to-ND translator that takes an ND program
containing iota_elim (and ι-using downstream ops) and produces an
iota-free ND program equivalent under Leisenring's ε-theorem.

- **Sound**: every output verifies under ND.
- **Complete**: every input that verifies under (post-Path-D) ND is
  successfully translated.

This is a test infrastructure tool, not the production LK target. Its
correctness is judged by Leisenring's theorem, not corpus statistics.

## 1. Math

### Hilbert-Bernays 2nd ε-theorem (Leisenring variant)

For ε-free axioms `T'` and ε-free formula `G`:

    T' ⊢_{ND-with-ε} G    iff    T' ⊢_{ND-without-ε} G

The forward direction is constructive: given a derivation of `G`
from `T'` allowing ε-terms, produce one without ε-terms.

**Construction (this is the algorithm)**: each ε-introduction is
replaced by ∃-elimination. The ε-term `ε x. φ(x)`, justified by
`∃x. φ(x)`, becomes a fresh fix-var `w` introduced by `∃-elim` on
that existential. Every downstream occurrence of the ε-term is
replaced by `w`. The `∃-elim` scope must close before its
enclosing scope (LIFO discipline); the scope-closer re-derives the
in-scope result in the parent context.

In our system, ι.B (definite description, treated as ε under Russell-
without-uniqueness) is introduced by `iota_elim ∃x.B(x)`. The
construction replaces `iota_elim ∃x.B(x)` with
`exists_elim ∃x.B(x), w`. Downstream `TermRef`s pointing to that
instruction naturally resolve to the new witness `w`.

### Composition with Path D

Path D (load-time axiom normalization, see `IOTA_ELIM_DESIGN.md`
§ 1) ensures the precondition "axioms are ε-free":
`eliminate_descriptions` is applied to every axiom / claim / schema
at load, replacing static ι with Russell-style ∃-wraps. The goal
formula is similarly ι-free (Path D + standard claim handling).

With Path D, every proof that verifies under ND has ε-free axioms.
Leisenring's theorem then guarantees translation; this module is the
constructive realization.

### Scope of the translator

The translator's domain is exactly proofs that verify under
(post-Path-D) ND.  Proofs that pattern-match the pre-Path-D
iota-bearing axiom shape don't verify post-Path-D — they're outside
Leisenring's scope (they implicitly assume the unique-ε reading that
Path D's Russell-without-uniqueness rejects).

This is why the translator is tested with hand-crafted
`iota_translator_test.cpp` programs and verified by NDVerifierGate
on its outputs, rather than judged by corpus coverage.

## 2. Implementation

```
src/proof/translate/iota_elim/
├── BUILD.bazel
├── iota_inventory.{h,cpp}        ~20 LOC — collect iota_elim sites.
├── elimination_plan.{h,cpp}      ~100 LOC — per-site scope-close index.
├── proof_rewriter.{h,cpp}        ~280 LOC — structural rewrite.
├── nd_verifier_gate.{h,cpp}      ~50 LOC — I-3 + I-4 soundness check.
└── eliminate_iota.{h,cpp}        ~40 LOC — top-level Pass entry point.
```

### 2.1 IotaInventory

Walks the program once, returns the instruction indices where
`nd::IotaElim` appears. Pure.

### 2.2 EliminationPlan

For each iota site, computes the enclosing block-closer's index — the
position just before which the iota's new `exists_elim` scope must
close (LIFO). Two passes:

1. Pair openers (Fix/Assume/ExistsElim) with closers
   (ForallIntro/ImpliesIntro/NotIntro/scope-closing ExistsIntro);
   build `closer_of[opener_idx]`.
2. For each iota site, the deepest open block at its position
   determines the scope-close index. If no scope is open, qed is the
   fallback target.

### 2.3 ProofRewriter

The witness substitution. Walks the original program emitting new
instructions:

1. **Rename `iota_elim` to `exists_elim`**. Preserve the source
   formula StepRef (remapped) and the bind name (becomes the
   witness's source-level name).
2. **Insert scope-closing `exists_intro`** chains before each
   block-closer that has iota scopes to close (LIFO, innermost
   first). The block-closer's body StepRef is overridden to point at
   the chain's tail.
3. **Remap all StepRef / TermRef fields** through `old_to_new` (the
   inserted closers shift subsequent indices).
4. **Rewrite `Program::step_index`** (source-level name → idx).

The rewrite is structurally faithful to Leisenring's construction:
each step in the input has a corresponding step in the output, with
indices shifted to accommodate the inserted scope-closers.

### 2.4 NDVerifierGate

After rewrite, runs two checks:

- **I-3 (iota-free)**: scan output for any `nd::IotaElim`. None
  should remain.
- **I-4 (ND-verifies)**: run `nd::NDVerifier` on the output against
  the goal formula. Any failure is a translator bug surfaced at the
  boundary.

Either failing is a hard error from `EliminateIotaInProof::apply`.

### 2.5 EliminateIotaInProof

The top-level pass. Composes:
`IotaInventory → EliminationPlan → ProofRewriter → NDVerifierGate`.

Pass interface: `Pass<nd::Instr, nd::Instr>` (pure function, no
GlobalContext mutation).

## 3. Soundness contract

For every successful `apply()` call, the output:
- contains no `Term::description` anywhere (I-3),
- verifies under ND against the goal (I-4).

These are checked at the gate; the translator cannot silently emit a
broken proof.

## 4. Completeness contract

For every input that verifies under (post-Path-D) ND, `apply()`
returns Ok. This is Leisenring's theorem applied to our setup.

Demonstrated by:
- `iota_translator_test.cpp` covers iota_elim binding, ι-as-forall_elim-arg,
  ι-as-exists_intro-witness, and nested-iota patterns.
- The corpus tool (`translate_corpus`) with `--show-errors` reports
  no failures bucketed to `eliminate_iota.cpp` on ND-verified iota
  proofs.

## 5. Why earlier drafts were wrong

The drafts that posited a "T-invariant" + "synth_T recursion" were
overcomplicated. They tried to maintain `env[k] derives T(F_k)` for
every original step k, which required synthesizing complex bridging
chains.

The actual Leisenring construction maintains a SIMPLER invariant:
`env[k] derives F_k with each iota term replaced by the corresponding
exists_elim witness`. This is what the witness-substitution rewrite
does. The output is iota-free; it ND-verifies because the original
ND derivation steps (pattern-matching on formula shapes) still go
through with iota → fix-var substituted on both sides.

The T-invariant approach was a misreading. The math is simpler than
I had constructed.

## 6. Composition with NDtoLKR

```
NDtoLKR::apply(in):
    if (in contains eq_subst):
        error "eq_subst deprecated" (see EQ_SUBST_DEPRECATION.md)
    if (in contains iota_elim):
        out = EliminateIotaInProof.apply(in)
        return apply(out)              # recurse on iota-free input
    ... existing LK translation ...
```

After EliminateIotaInProof runs, the rest of NDtoLKR sees only
iota-free programs. The LK side's iota gates (`formula_contains_iota`
on the goal) are satisfied by construction.

## 7. References

- `IOTA_ELIM_DESIGN.md` — Path D's load-time axiom normalization.
- `EQ_SUBST_DEPRECATION.md` — `eq_subst` deprecation policy.
- `ELIMINATE_DESCRIPTIONS.md` — spec for `eliminate_descriptions`.
- Leisenring, *Mathematical Logic and Hilbert's ε-Symbol* (1969) —
  the construction this module realizes.
- Hilbert & Bernays, *Grundlagen der Mathematik II* — 2nd ε-theorem.
