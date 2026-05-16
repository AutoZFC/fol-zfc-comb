# Description Elimination: ND-with-iota → LKR-iota-free

This document specifies how definite descriptions (ι terms) introduced
in ND proofs are eliminated when translating to LKR. The motivating
architecture: **ND carries descriptions; LKR and Comb do not**. All
description complexity is localized to this translator pass; LKR/Comb
inherit Hughes 2019's soundness + completeness theorems directly,
because their inputs are standard description-free FOL formulas.

This is currently **forward-looking scope**: the elimination pass and
the proof-translation surgery described here are not yet implemented.
The current ND→LKR translator (`nd_to_lkr.cpp`) does not handle
iota-using ND proofs; running an iota-using ND proof through it is
either rejected or silently wrong (TODO: pick one explicitly).

## 0. Why this architecture

Two equivalent claims justify the split:

1. **Practical**: descriptions touch every comb verifier check. The
   description-aware variants of unification, dualizer application,
   variable scanning, and dependency extraction collectively account
   for the majority of subtle bugs found in the comb verifier. Pushing
   the complexity to one place (the translator) shrinks the surface.

2. **Theoretical**: Hughes' soundness + completeness theorems are
   stated for standard FOL. Extending them to descriptions is research-
   level work. The classical alternative — eliminate descriptions
   before doing the heavy lifting — is **conservativity** (Hilbert-
   Bernays 2nd ε-theorem; Leisenring 1969 for definite descriptions),
   a settled result. Citing rather than re-proving is the cheap path.

## 1. Reading of our ι

Our `iota_elim` rule

    iota_elim h : ∃x. φ(x)  ⊢  φ(ι x. φ(x))

is the **Hilbert ε-axiom** — `ι x. φ(x)` denotes *some* witness of φ
(if any exists; arbitrary element otherwise). It is NOT Russell's
definite description (which would require uniqueness).

Consequence: the elimination uses the simple ∃-translation (no
uniqueness clause). The dual ∀-form arises by polarity flip.

## 2. Formula-level elimination

`eliminate_descriptions : FormulaHandle → FormulaHandle` operates on
**NNF formulas** (polarity is fixed at each leaf):

| occurrence            | rewrite                                    |
|-----------------------|--------------------------------------------|
| `Q(ι x. P(x))`        | `∃ x. (P(x) ∧ Q(x))`                       |
| `¬Q(ι x. P(x))`       | `∀ x. (P(x) → ¬Q(x))`  i.e. `∀ x. (¬P(x) ∨ ¬Q(x))` |

Rules:

1. **Dedup by α-equivalence**: descriptions with α-equivalent bodies
   collapse to a single fresh variable (otherwise multiple occurrences
   could pick different witnesses, losing the "same description = same
   individual" reading).
2. **Hoist to outermost compatible scope**: the fresh existential (or
   universal) is bound at the smallest enclosing position that
   dominates all occurrences and respects existing quantifier scope.
3. **Recurse innermost-first** on nested descriptions: rewrite inner
   ones before outer ones (the outer body changes shape after inner
   substitution).

The output is provably description-free; this is the LKR-side claim.

### Size bound

For an input formula with `K` unique descriptions, `N` total occurrence
sites, and average body size `B`:

    |T(φ)|  =  O(K·B + N + |φ|)

i.e. polynomial. No exponential or super-exponential blowup at the
formula level.

## 3. Proof-level translation

For a successful ND proof `Π_ND : ⊢ φ` containing `iota_elim` sites,
produce an LK proof `Π_LK : ⊢ T(φ)`. Two cases per `iota_elim` site.

### Case A — iota_elim used as a scoped exists_elim

The common case. ND pattern:

    h_ex   = ... : ∃x. φ(x)
    h_iota = iota_elim h_ex             -- φ(ι x. φ(x))
    ... straight-line reasoning using ι x. φ(x) ...
    derive goal G that does NOT mention ι x. φ(x)

LK translation:

    h_ex : ∃x. φ(x)
    exists_elim h_ex opens scope with fresh witness var w:
        h_assume : φ(w)                  -- maps to h_iota
        ... reasoning translated, replacing ι x. φ(x) by w ...
        derive G
    exists_elim closes : G               -- G doesn't mention w, exports cleanly

Step-for-step structural map. **Constant overhead per `iota_elim`
site** (open + close exists_elim brackets). Total cost: O(n) for n
original ND steps.

### Case B — iota term escapes into a sequent used after the scope

If `ψ(ι x. φ(x))` is derived inside the scope but used after closing
the scope (or appears in the final goal), the simple Case A
restructuring fails — the would-be-exported sequent would mention the
witness var, violating eigenvariable discipline.

Fix: also apply `eliminate_descriptions` to the offending formula,
then bridge with three small steps inside the scope:

    ... derive φ(w)                       -- already in scope
    ... derive ψ(w)                       -- translated subproof
    and_intro    : φ(w) ∧ ψ(w)
    exists_intro : ∃x. (φ(x) ∧ ψ(x))      -- iota-free, exports

The exists_elim scope now closes around an iota-free conclusion.

**Overhead per escape site: O(1) additional LK steps.** If the goal
formula itself contains the iota term, the same pattern applies at the
top level: the LK target sequent is `T(goal)`, and the final
exists_intro produces it.

## 4. Algorithmic walkthrough

```
translate_nd_to_lk_eliminating_iota(Π_ND, claim_with_iota):
    target := eliminate_descriptions(NNF(claim_with_iota))
    walk Π_ND bottom-up:
      for each iota_elim site:
        identify the innermost subderivation in which the iota appears
        determine whether the iota escapes this subderivation's conclusion
        if not (Case A):
          rewrite: replace iota_elim with exists_elim, eigenvariable w
          substitute ι x. φ(x) ↦ w throughout the inner subderivation
        if yes (Case B):
          eliminate_descriptions on the escaping formula
          rewrite per Case A, then add the 3-step bridge before closing
    return translated stream
```

The translator does not invoke a separate "ε-substitution" search; it
performs structural surgery, which is why blowup stays polynomial.

## 5. Size bounds and the comb compression

End-to-end size of the persisted artifact (the combinatorial proof):

| stage                          | size relative to original |
|--------------------------------|---------------------------|
| original ND proof              | 1×                        |
| ND-after-iota-elim (LK form)   | 1.5×–4× (Case B overhead) |
| **combinatorial proof**        | **O(\|T(φ)\| · c)**, independent of LK proof size |

where `c` is the contraction multiplier (small constant for typical
proofs). The LK proof's size disappears in the LK→Comb compression
(Hughes Thm 6.2): combinatorial proofs quotient out rule-application
order, cut choices, and naming, so all the bureaucratic bloat from
the iota elimination dissolves.

The Hilbert-Bernays *tower-of-exponentials* worst case applies to the
ε-substitution **method** (combinatorial search over witness
assignments), which we are explicitly **not** using. Skolem-style
restructuring as above stays polynomial.

## 6. Soundness and completeness

**Soundness of translation.** Every ND proof Π_ND : ⊢ φ that the ND
verifier accepts translates to an LK proof Π_LK : ⊢ T(φ) that the LKR
verifier accepts. Proof: structural induction on ND proof tree using
Case A and Case B rewrites as the inductive step. Each case is a
proof-preserving rewrite; the composition preserves provability.

**Completeness of translation.** Every accepted ND proof admits *some*
translation — no ND proof is "stuck." This is the content of the
**Hilbert-Bernays second ε-theorem** (more precisely the description-
elimination variant due to Leisenring 1969). We cite, not re-prove.

**End-to-end system soundness/completeness**:
- A formula φ is provable in ND-with-ι ⇔ T(φ) is provable in LK
  (description-free) ⇔ T(φ) has an accepting combinatorial proof.
- The middle equivalence is the classical eliminability result.
- The right equivalence is Hughes' Theorem (his §11 / §14.3).
- LKR/Comb do not need to extend Hughes' framework; their inputs are
  always in the description-free fragment Hughes' theorems cover.

## 7. Implementation order

1. **`eliminate_descriptions`** in `src/core/formula.cpp` (or near the
   FormulaBuilder). Standalone, testable, pure.
2. **Invariant check** at the entry of `LKRVerifier::verify` and
   `CombVerifier::verify`: walk the goal formula, error if any
   `Term::is_description()` survives. Cheap, makes the contract
   explicit, catches translator bugs early.
3. **Wire `eliminate_descriptions` into the ND→LKR translator** —
   apply to the goal formula before emitting LKR.
4. **Implement Case A** of the proof translation: detect iota_elim
   uses, emit exists_elim wrappers, substitute throughout.
5. **Implement Case B** of the proof translation: detect escape sites,
   rewrite escaping formulas, emit the 3-step bridge.
6. **Tests** at each layer:
   - `eliminate_descriptions` on representative formulas (single,
     multiple, nested occurrences; both polarities).
   - The invariant check rejecting iota-containing inputs to LKR/Comb.
   - The full ND→LK→Comb pipeline on iota-using ND proofs.
7. **Delete the description-aware machinery in `src/proof/comb/`**
   once the invariant check is live and the translator handles all
   ND iota uses. Specifically:
   - `fograph.cpp`: depth-aware description rewrite, description
     recursion in binding-edge detection.
   - `verifier.cpp`: `collect_term_fixed_vars` recursion into
     descriptions; `term_equal_under_dualizer`/`formula_equal_under_dualizer`;
     the on-the-fly δ application inside descriptions.
   - `leap.cpp`: `collect_fixed_vars`'s description case;
     `compute_reach`'s description case; `unify_formula`/`unify_term`'s
     description branches.
   - Corresponding tests in `comb_test.cpp`.

   The description-handling code in `comb/` is preserved for now as
   defense-in-depth, but becomes dead once steps 1–6 are in place.

## 8. References

- Hilbert & Bernays, *Grundlagen der Mathematik II*, second ε-theorem
  (1939). Conservativity of ε over FOL.
- A. C. Leisenring, *Mathematical Logic and Hilbert's ε-Symbol*
  (1969). Description-elimination algorithm.
- Hughes, *First-order proofs without syntax* (arXiv 1906.11236), §6
  (combinatorial proof definition), §11 (soundness/completeness over
  standard FOL), §14 (polynomial-time verification).
