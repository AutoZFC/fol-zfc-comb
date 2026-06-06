# LKR → KS1 (CUT_HANDLING_ROADMAP phase K6)

Construction extracted from HSW 2021 (arXiv:2104.13124) §VII.A (Lemma 20,
MLL1X→MLS1X) and §VIII. This is the front end that turns a **cut-free, lemma-free**
`lkr_cut_elim::Deriv` into a **decomposed** `ks1::Derivation` (t ⟶ goal), which the
existing KS1→comb bridge (`ks1_to_comb::build_comb_proof`) consumes.

LKR is the one-sided sequent calculus LK1 (`src/proof/lkr/ops.h`). A cut-free LKR proof
restricted to `{Ax, One, Or, And, Exchange}` is exactly MLL1X (LK1's linear fragment).
KS1's linear fragment is MLS1X = `{ForallUnit, Ai, Tu, Sw, Mix, Ex, Eqv}`. Lemma 20 is
the translation; K6 implements it phase by phase.

## The sequent–formula correspondence

A sequent `⊢ Γ`, `Γ = A₁,…,Aₙ`, corresponds to the formula `(Γ) = A₁ ∨ ⋯ ∨ Aₙ`
(HSW §II.B), **left-associated**: `(A₁,…,Aₙ) = (…((A₁∨A₂)∨A₃)…)∨Aₙ`. The `∨`-rule
`⊢ Γ,A,B / ⊢ Γ,A∨B` corresponds to grouping the last two disjuncts. The translation of a
proof of `⊢ Γ` is a KS1 derivation `t ⟶ (Γ)`. The ROOT sequent of our input is a single
closed formula `[goal]`, so `(root) = goal` exactly — `ks1::check`'s final-equals-bottom
test is satisfied with no top-level reconciliation.

## KS1 rules used (top-down, premise `S{P}` → conclusion `S{Q}`; `t` = ¬⊥)

- `Ai`   : `S{t}      → S{a ∨ ā}`     (param: positive atom `a`)
- `Tu`   : `S{A}      → S{A ∧ t}`
- `Sw`   : `S{A∧(B∨C)}→ S{(A∧B)∨C}`
- `Mix`  : `S{A∧B}    → S{A∨B}`
- `Eqv`  : an eq-(2) equation at `S` (`CommAnd/Or`, `AssocAnd/Or`, …), one at a time.
- `ForallUnit`/`Ex`  : quantifiers (K6.2, not used in K6.1).

`context` is a `Path` (root→redex) of `Dir::{Left,Right,Down}`. **Composing a
sub-derivation `D` inside a context `c`** = prepend `c` to every step's `context`. This is
the workhorse of the recursion (a proof of a premise is replayed inside an `∧`-branch).

## Recursive translation `tr(d) : steps with t ⟶ (d.conclusion)`

Driven by `d.rule`. `Γ = d.conclusion`. Conventions: results are produced with `(Γ)`
left-associated; an LKR position `p` ⇒ the disjunct at the matching place. Per-rule:

### `RAx{a,b}` — axiom (K6.1; requires `|Γ| = 2`, the pure linear axiom)
`Γ = [φ, ψ]` with `φ,ψ` dual. `(Γ) = φ∨ψ`. Let `α` = the positive one (the other is `ᾱ`).
Emit `[ Ai(α) @ {} ]` (gives `t → α∨ᾱ`) then, if `φ` is the negative one (goal is `ᾱ∨α`),
one `Eqv(CommOr) @ {}`. (A longer `Γ` = axiom-with-weakening; that is resource → K6.3.)

### `ROne{idx}` — truth axiom (K6.1; requires `|Γ| = 1`, `Γ=[1]`, `1 = ¬⊥ = t`)
`(Γ) = t`. Emit `[]` (the derivation is already `t`). Longer `Γ` = with weakening → K6.3.

### `ROr{principal, child}` — disjunction (K6.1)
`child` proves `Γ'` = `Γ` with the disjunct `φ∨ψ` (at `principal`) split into `φ` (at
`principal`) and `ψ` (appended last). `(Γ') = …∨φ∨…∨ψ`; `(Γ) = …∨(φ∨ψ)∨…`. Recurse
`tr(child)` (gives `t ⟶ (Γ')`), then emit `Eqv` steps re-associating/commuting `ψ` (the
last disjunct) next to `φ` and grouping them into `φ∨ψ` at `principal`'s place. (For the
common shape `Γ = [φ∨ψ]` i.e. `principal=0,|Γ|=1`: `child=[φ,ψ]`, `(Γ')=φ∨ψ` already equals
`(Γ)` — zero reconciliation.)

### `RExchange{i,j,child}` — permutation (K6.1)
`(Γ)` and `(child)` differ by swapping two disjuncts: emit `tr(child)` then `Eqv`
(`CommOr`/`AssocOr`) steps realizing the transposition on the disjunction tree.

### `RAnd{principal, left_partition, left, right}` — conjunction (K6.1, the hard case)
`left` proves `Γ_L,φ`, `right` proves `Γ_R,ψ`; node proves `Γ` = the merge of `Γ_L,Γ_R`
with `φ∧ψ` at `principal`. Let `P=(Γ_L)`, `Q=(Γ_R)`. Build `t ⟶ P∨Q∨(φ∧ψ)`:
1. `Tu @ {}`               : `t → t∧t`
2. `tr(left)` under `[Left]`  : `t∧t → (P∨φ)∧t`
3. `tr(right)` under `[Right]`: `(P∨φ)∧t → (P∨φ)∧(Q∨ψ)`
4. `Eqv(CommOr) @ {Right}`    : `→ (P∨φ)∧(ψ∨Q)`
5. `Sw @ {}` (A=P∨φ,B=ψ,C=Q) : `→ ((P∨φ)∧ψ)∨Q`
6. `Eqv(CommOr) @ {Left,Left}`: `→ ((φ∨P)∧ψ)∨Q`
7. `Eqv(CommAnd) @ {Left}`    : `→ (ψ∧(φ∨P))∨Q`
8. `Sw @ {Left}` (A=ψ,B=φ,C=P): `→ ((ψ∧φ)∨P)∨Q`
9. `Eqv(CommAnd) @ {Left,Left}`: `→ ((φ∧ψ)∨P)∨Q`
Then `Eqv` (assoc/comm) to move `(φ∧ψ)` from the front to `principal`'s place in `(Γ)` and
interleave `P`,`Q` to the LKR positions. (`Mix` is needed only when a branch context is
empty — `P` or `Q` absent; handled as a degenerate switch case.)

The switch/`Eqv` steps are fograph-identity (`J A∨B K`, `J A∧B K` only restructure), so the
fonet read off Φ1 is exactly the axiom-linking from the `Ai` steps — the bridge needs no
awareness of the reconciliation.

## Decomposed form

K6.1 emits only MLS1X (linear) rules, so the whole derivation is Φ1 and `ks1::split`
returns `(Φ1, goal, [])` (empty resource phase). Weakening/contraction (Φ2) is K6.3.

## Phasing

- **K6.0** ✓ — skeleton: `⊢ a∨ā` only, validates the integration path end-to-end.
- **K6.1** — propositional linear fragment: `RAx, ROne, ROr, RExchange, RAnd` (this doc).
- **K6.2** — quantifiers: `RForall→ForallUnit` (prefix-by-∀ + `Eqv(DistForall)`, Lemma 20's
  shown case), `RExists→Ex`.
- **K6.3** — resource phase: `RWeaken→W/WForall`, `RContract/RDuplicate→ medials + Ac/CForall`
  (Theorem 29 + Lemmas 25/26); compute the linearized `A'`. The hard part.
- **K6.4** — wire into `comb_checker` after `eliminate_cuts`; corpus coverage.

## Oracle

Every phase is gated end-to-end by `build_comb_proof` → `CombVerifier` (all four phases) on
hand-built cut-free Derivs, plus `ks1::check` as an intermediate gate. `test/lkr_to_ks1_test.cpp`.
