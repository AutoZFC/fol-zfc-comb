# KS1 Checker — Paper-Faithfulness Audit (2026-05-23)

Audit of `src/proof/ks1/` against Hughes, Straßburger, Wu (2021),
*Combinatorial Proofs and Decomposition Theorems for First-order Logic*
(arXiv:2104.13124). The checker is the soundness gate for KS1 derivations
(Track 2); the bridge to combinatorial proofs (`src/proof/translate/
ks1_to_comb/`) is audited via its `CombVerifier`-pass requirement and is
out of scope here.

**Severity legend** (mirroring `comb/PAPER_AUDIT.md`):
- **CRIT** — soundness gap on inputs within the documented scope.
- **MOD** — soundness gap only outside scope, or completeness gap.
- **MIN** — defensive check missing; correctness preserved on well-formed inputs.
- **STY** — deviation from a paper definition with no correctness impact.

## Scope

KS1 derivations in NNF on the **function-symbol-free fragment** of HSW's term
grammar — same scope as the comb verifier (`comb/PAPER_AUDIT.md` CRIT-1).
Atoms are `t | f | p(t1,…,tn) | p̄(t1,…,tn)`, where the `ti` are variables
(Gen / Fixed only, no functions). Formulas are `core::FormulaHandle` in NNF:
`⊥ = Compound{Bottom}`, `⊤ = ¬⊥ = Compound{Not, Bottom}`, literal = predicate
or `Compound{Not, predicate}`. This is the LKR convention.

## Quick index

| File             | What it checks                                  | Crit | Mod | Min | Sty |
|------------------|-------------------------------------------------|-----:|----:|----:|----:|
| `derivation.h`   | data types (Rule, Step, Derivation, EqRule)     | 0 | 0 | 0 | 0 |
| `checker.cpp`    | per-rule Fig. 6 instances + context navigation  | 0 | 0 | 0 | 0 |
| `decompose.cpp`  | Thm 17 form check + split (Φ1, A', Φ2)          | 0 | 1 | 0 | 1 |
| `equiv.{h,cpp}`  | auxiliary `≡` canonicalizer (propositional)     | 0 | 1 | 0 | 0 |

The remaining items are: `decompose.cpp`'s **MOD DEC-1** (Thm-17 reorganizer
deferred — checker handles only already-decomposed input) and its **STY** on
`phase_of`'s unreachable-default fallback; and **MOD** on `equiv`'s
quantifier-shift incompleteness (auxiliary, not on the soundness path).
`checker.cpp` has no remaining items after the 2026-05-23 fixes (NNF
navigation guard, unit-atom extension, `swap_in_term` precondition assert).

The `equiv` module is **auxiliary**: the checker's `Eqv` rule uses single-
equation-instance matching, not `equiv::canonicalize`. So `equiv`'s
incompleteness on quantifier shifts (documented in its header) is not a
soundness-relevant gap for the KS1 checker.

---

## Context S{·} — paper §V

A deep-inference context `S{·}` is "a formula with exactly one occurrence of
the hole `{·}` in the position of an atom." Plugging `A` into the hole yields
`S{A}`. The hole sits at an atom-position slot — i.e. in NNF, a literal slot.

**Representation.** `Path = std::vector<Dir>` where `Dir ∈ {Left, Right, Down}`
navigates from the formula root through `Compound{And/Or, l, r}` (Left/Right)
or `Quantified{Q, body}` (Down) to the redex root. The redex subformula sits
at the hole's position; the rule's premise pattern matches against it.

**Navigation is restricted to ∧/∨/quantifier nodes** (`is_navigable_binary`):
Left/Right into a `Compound{Not, atom}` or `Compound{Bottom}` is **rejected**,
because the hole would otherwise descend below the atom-position slot and a
rule like `Tu` (which accepts any `A` as redex) could plug a non-literal there
and produce a non-NNF formula. This guard was added in response to the
`code-eval` finding (2026-05-23) and is covered by
`ks1_checker_test::test_context_no_descent_into_not`.

## The 14 rules — Fig. 6 (verified via `pdftotext -layout` p.5)

Each `apply_rule` arm in `checker.cpp` matches its premise shape exactly,
checks any side conditions, then constructs the conclusion per the schema. All
De Bruijn surgery uses the well-tested `core::FormulaBuilder` ops
(`shift_formula`, `instantiate_gen`) plus two small local helpers
(`gen_occurs_free`, `swap_gen`).

### MLS1^X (linear core)

| Rule        | Schema `S{P} / S{Q}`                  | Checker behavior |
|-------------|---------------------------------------|------------------|
| `ForallUnit`| `S{t} / S{∀x.t}`                      | `is_top(P)` required; `Q = ∀.(¬⊥)`. |
| `Ai`        | `S{t} / S{a ∨ ā}`                     | `is_top(P)`; `param = a` must be an atom literal (`is_atom_literal`; includes ⊤/⊥ per paper grammar); `Q = a ∨ dual(a)`. |
| `Tu`        | `S{A} / S{A ∧ t}`                     | Any redex; `Q = A ∧ ⊤`. |
| `Sw`        | `S{A ∧ (B ∨ C)} / S{(A ∧ B) ∨ C}`     | Shape check `And(_, Or(_,_))`; structural rebuild. |
| `Mix`       | `S{A ∧ B} / S{A ∨ B}`                 | Shape `And`; produce `Or(l,r)`. |
| `Ex`        | `S{A[x/t]} / S{∃x.A}`                 | Verifies `instantiate_gen(body, t) == P`; `Q = ∃.body`. |
| `Eqv`       | `S{B} / S{A}`  (`A ≡ B`)              | One eq-(2) instance applied at `P`'s root — see "≡" below. |

### Resource fragment

| Rule        | Schema `S{P} / S{Q}`                  | Checker behavior |
|-------------|---------------------------------------|------------------|
| `W`         | `S{A} / S{A ∨ B}`                     | `Q = Or(P, param)`. |
| `WForall`   | `S{A} / S{∀x.A}` (`x ∉ A`)            | `Q = ∀.(shift(P, 0, +1))` — the shift makes the new binder vacuous, automatically satisfying `x ∉ A`. |
| `Ac`        | `S{a ∨ a} / S{a}`                     | Shape `Or(l, l)` with `l == r` and `is_atom_literal(l)`; `Q = l`. |
| `CForall`   | `S{∀x.∀x.A} / S{∀x.A}`                | Shape `∀.∀.body`; `Q = ∀.(shift(body, 1, -1))` — `shift(_, 1, -1)` maps Gen0→Gen0 (kept), Gen1→Gen0 (merged with kept), Gen≥2→Gen-1 (context). |
| `M`         | `S{(A∧C) ∨ (B∧D)} / S{(A∨B) ∧ (C∨D)}` | Shape `Or(And, And)`; structural rebuild. |
| `MForall`   | `S{(∀x.A) ∨ (∀x.B)} / S{∀x.(A∨B)}`    | Shape `Or(∀, ∀)`; `Q = ∀.(Or(l_body, r_body))`. |
| `MExists`   | `S{(∃x.A) ∨ (∃x.B)} / S{∃x.(A∨B)}`    | Shape `Or(∃, ∃)`; dual of `MForall`. |

## The `≡` rule and eq (2) — paper §II

`≡` is the congruence on rectified formulas generated by the eight equations
of eq (2), verified verbatim against the paper text (`pdftotext` of p.4):

```
  A ∧ B ≡ B ∧ A              (A ∧ B) ∧ C ≡ A ∧ (B ∧ C)
  A ∨ B ≡ B ∨ A              (A ∨ B) ∨ C ≡ A ∨ (B ∨ C)
  ∀x.∀y.A ≡ ∀y.∀x.A          ∀x.(A ∨ B) ≡ (∀x.A) ∨ B    (x not free in B)
  ∃x.∃y.A ≡ ∃y.∃x.A          ∃x.(A ∧ B) ≡ (∃x.A) ∧ B    (x not free in B)
```

**Faithfulness:** the distribution pairing is `∀`-over-`∨` and `∃`-over-`∧`,
forced by the fograph semantics `[[∀x.A]] = •x + [[A]]` (Thm 8). Sanity-
checked against Example 9: `∃x.(px ∨ ∀y.py) ≡ ∃x.∀y.(py ∨ px)`.

**Checker design.** The `Eqv` step carries an `EqRule` + `EqDir`; `apply_eq`
matches the equation's LHS shape at the redex root and constructs the RHS:

| Equation     | LHS (Forward)              | RHS (Forward)              | Side condition |
|--------------|----------------------------|----------------------------|----------------|
| `CommAnd`    | `A ∧ B`                    | `B ∧ A`                    | — |
| `CommOr`     | `A ∨ B`                    | `B ∨ A`                    | — |
| `AssocAnd`   | `(A ∧ B) ∧ C`              | `A ∧ (B ∧ C)`              | — |
| `AssocOr`    | `(A ∨ B) ∨ C`              | `A ∨ (B ∨ C)`              | — |
| `SwapForall` | `∀.∀.body`                 | `∀.∀.swap_gen(body, 0)`    | — |
| `SwapExists` | `∃.∃.body`                 | `∃.∃.swap_gen(body, 0)`    | — |
| `DistForall` | `∀.(A_b ∨ B_b)`            | `(∀.A_b) ∨ shift(B_b,1,-1)`| `Gen0 ∉ B_b` via `gen_occurs_free` |
| `DistExists` | `∃.(A_b ∧ B_b)`            | `(∃.A_b) ∧ shift(B_b,1,-1)`| `Gen0 ∉ B_b` via `gen_occurs_free` |

The Backward direction is the symmetric rewrite (swap LHS/RHS shape; for
distribution, shift the floated operand back under the binder).

**Completeness of `Eqv` as single-equation instances.** `≡` is the congruence
*generated* by the eight equations, so every `A ≡ B` is a finite chain of
single-equation rewrites. The checker requires a derivation to record each
chain step as a separate `Eqv` step; no derivability is lost.

## Decomposition normal form — Thm 17 (`decompose.cpp`)

`is_decomposed(d)` checks: every MLS1^X step precedes every resource-only step
(`Eqv` is in both fragments, so flexible), and the non-≡ phase numbers
`{∀,ai,t}<{s,mix}<{∃}` and `{m,m∀,m∃}<{ac,c∀}<{w,w∀}` are non-decreasing within
each half. `split(fb, d)` returns `(Φ1, A', Φ2)` with `A'` computed by
replaying Φ1. Required input form for the K4/K5 bridge.

- **DEC-1 [MOD].** Decomposition is **checked** but not **constructed**. The
  constructive Thm 17 (rule-permutation via Lemmas 30/31, Appendices A/B) is
  deferred — `split` returns an error on non-decomposed input. For the bridge,
  K6 will arrange that the upstream front-end emits decomposed derivations
  directly; this gap is documented and not blocking.

## Open items

- **MOD — DEC-1** (`decompose.cpp`): Thm 17 decomposed-form is checked, not
  constructed (rule-permutation reorganizer deferred). K6's front-end will be
  arranged to emit decomposed derivations directly.

- **MOD — `equiv.{h,cpp}` quantifier-shift completeness** (auxiliary module
  only; not on the checker's soundness path — `Eqv` rule uses single-equation
  instances, not `equiv::canonicalize`).

- **STY — `decompose.cpp::phase_of` default.** Returns `Weakening` for `Eqv`
  in a path that callers always skip; an unreachable defensive fallback, not
  a correctness concern.

## Closed in 2026-05-23 (commit `0bb6091`)

- **MIN — context navigation into Not.** `is_navigable_binary` rejects
  Left/Right into `Compound{Not,·}`/`Compound{Bottom,·}` so the hole stays in
  atom position (paper §V). Tested by
  `ks1_checker_test::test_context_no_descent_into_not`.
- **MOD — `is_atom_literal` excluded units.** Extended to match HSW's atom
  grammar `a ::= t | f | p | p̄`. Tested by `test_ai_on_top`, `test_ai_on_bot`,
  `test_ac_on_top`.
- **STY — `swap_in_term`'s dead description branch.** Replaced with
  `assert(!t.is_description())` documenting the precondition.
- **MIN — per-resource-rule fibration coverage in `ks1_to_comb`.** Added unit
  tests for `w∀, c∀, m∀, m∃, m`, and a `≡`-in-Φ2 fibration test
  (`test_eqv_in_phi2_fibration`).

## Soundness & completeness verdict (2026-05-23)

### Soundness — YES, within scope

`check(fb, d)` accepts ⟹ every step is a valid Fig. 6 rule instance at its
context ⟹ `d.bottom` is derivable in KS1 from `d.top`. By HSW Thm 16, if
`d.top = t` then `d.bottom` is valid first-order. The argument is per-rule:

- Each `apply_rule` arm matches the rule's exact premise shape, checks any
  side conditions (`Ai`/`Ac` atom-literal; `DistForall`/`DistExists` `x ∉ B`;
  `Ex` `instantiate_gen(body, t) == P`), and constructs the conclusion
  structurally per the schema.
- Context navigation respects atom-position (`is_navigable_binary` rejects
  descent into Not/Bottom), so plugged subformulas keep the formula in NNF.
- `Eqv` applies exactly one eq-(2) instance per step. Each equation is a
  paper-defined ≡-axiom, hence sound. Repeated application composes a `≡`
  chain, which is the congruence itself.

**Scope** = the function-symbol-free fragment (terms are Gen/Fixed only;
descriptions asserted absent in `swap_in_term`, mirroring `comb` precondition).

### Completeness — YES, modulo presentation conventions

Every valid KS1 derivation has an equivalent representation accepted by the
checker:

- **`≡` chains** must be broken into individual eq-(2) steps. Lossless, just
  more verbose.
- **Context paths** must navigate to atom-position; this is what the paper
  also requires. The checker rejects ill-formed (sub-atom) paths.
- **Decomposition form** (for the bridge) must be presented decomposed —
  reorganization deferred (DEC-1).

Within these, every KS1-derivable formula is provable in our representation,
and via HSW Thm 16 the checker accepts a derivation iff one exists for a valid
formula.

### Net

Sound and complete as a verifier of KS1 derivations on the function-symbol-
free fragment, for derivations presented as individual rule instances with
single-equation `≡` steps and decomposed form where required. No remaining
unjustified gaps.

---

## Tests

| File                          | What it covers                                              | Asserts |
|-------------------------------|-------------------------------------------------------------|---------|
| `ks1_equiv_test`              | propositional `≡` canonicalizer (auxiliary)                 | 26 |
| `ks1_checker_test`            | per-rule accept/reject, ≡ equations, context navigation (incl. NNF guard), units (`Ai`/`Ac` on ⊤ and ⊥) | 38 |
| `ks1_validation_test`         | end-to-end decomposed derivations exercising each phase     | 4  |
| `ks1_decompose_test`          | Thm 17 form check + split (Φ1, A', Φ2)                      | 26 |
| `ks1_read_fonet_test`         | bridge K4 — fonet read-off, CombVerifier-validated          | 10 |
| `ks1_bridge_test`             | bridge K5 — full CombProof end-to-end + per-resource-rule fibration (`w, w∀, ac, c∀, m, m∀, m∃, ≡`) | 40 |

The bridge tests close the loop: a decomposed KS1 derivation translates to a
CombProof that passes the independent `CombVerifier` (all four phases).

## References

- HSW 2021, arXiv:2104.13124 (Fig. 6 §V; eq (2) §II; Thm 16/17 §VI).
- `src/proof/translate/KS1_TRACK2_DESIGN.md` — design rationale + bridge.
- `src/proof/translate/CUT_HANDLING_ROADMAP.md` — Track 2 living tracker.
- `src/proof/comb/PAPER_AUDIT.md` — companion audit for the comb verifier.
