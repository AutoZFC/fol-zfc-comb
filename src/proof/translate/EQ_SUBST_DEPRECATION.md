# `eq_subst` deprecation in translation

## Status

**Deprecated in translation as of 2026-05-17.**

`eq_subst` remains a supported ND rule in `src/proof/nd/` for hand-written
proofs (see `zfc/naturals/naturals.fol.proof`,
`zfc/induction/well_founded.fol.proof`). The ND verifier, parser, lowering,
and runtime continue to handle it.

`eq_subst` is **not** supported anywhere in the translation pipeline:

- `NDtoLKR` rejects any program containing `nd::EqSubst` at the entry
  gate (`src/proof/translate/nd_to_lkr.cpp`, top of
  `NDtoLKR::apply`).
- The structural dispatch tables (`compute_flat_formula`,
  `compute_flat_step_proof_deps`, `close_flat`, the iota-elimination
  `proof_rewriter`) carry stub error arms only to keep
  `std::visit` exhaustive over `nd::Instr`. They should never fire.
- LK and Comb proof systems have no equivalent of `eq_subst` — equality
  reasoning at those layers is handled by other means.

## Why deprecate from translation

`eq_subst` is a Leibniz-substitution rule built into ND for convenience:
from `eq(a, b)` and `φ(a)`, derive `φ(b)`. The rule rewrites the target
formula at the term level — replacing every free occurrence of `a` with
`b`.

This is a meta-level rewrite over arbitrary subformula structure. In LK
and Hughes-2019 combinatorial proofs the equality is treated as a
predicate; reasoning about substitution happens through pure
propositional / quantifier rules, not as a primitive. There is no clean
1:1 translation of `eq_subst` into a fixed LKR realizer — every
substitution would need a custom decomposition over the φ shape.

Rather than implement that decomposition, we elect to:

1. Keep `eq_subst` in ND for the small set of hand-written proofs that
   use it.
2. Reject `eq_subst` at the translation boundary with a clear error.
3. Skip Isabelle-exported proofs that use `eq_subst` during corpus
   measurement (`src/tools/translate_corpus.cpp`).

## Rewriting proofs to avoid eq_subst

A proof using `eq_subst` can typically be rewritten using the basic
equality rules already present in LK / Comb:

- **Term substitution into atomic predicates**: replace
  `eq_subst eq(a, b), P(a, c)` with axiom-style equality reasoning
  (`forall x. forall y. (eq(x, y) -> (P(x, c) -> P(y, c)))`) plus
  `implies_elim`. The corresponding congruence axiom needs to be
  available.
- **Symmetric direction**: `eq_sym eq(a, b)` produces `eq(b, a)`, then
  apply congruence as above.

For Isabelle-exported proofs, this rewrite would have to happen on the
isa2fol side (Rust). For hand-written proofs in `zfc/`, the ND verifier
accepts the primitive `eq_subst` so no rewrite is needed.

## Where this is enforced

```
src/proof/translate/nd_to_lkr.cpp        # Gate at NDtoLKR::apply entry
src/proof/translate/iota_elim/proof_rewriter.cpp  # Stub error arm
src/tools/translate_corpus.cpp           # Skip-and-count in coverage tool
```

ND-side code is unchanged:

```
src/proof/nd/ops.h        # nd::EqSubst struct + nd::Instr variant
src/proof/nd/stack.cpp    # ProofStack::eq_subst implementation
src/proof/nd/verifier.cpp # exec_op dispatch
src/proof/nd/lowering.cpp # Parser/lowering rule
src/runtime/runtime.cpp   # ProofContext::eq_subst wrapper
```
