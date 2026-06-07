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
- **K6.2** — quantifiers (single-formula goal, Γ empty): `RForall→ForallUnit` then the child
  under `[Down]` with the eigenvar rebound `fixed(eigen)→gen0`; `RExists→Ex` (isolate the
  instance φ[t] rightmost, `Ex`, reconcile). DONE for the Γ-empty / single-binder case.
  K6.2b: the `Eqv(DistForall)` pull-out for a non-empty context (∀x.((Δ)∨φ) ⟶ (Δ)∨∀x.φ,
  Lemma 20's shown case), nested-binder de Bruijn depth (the eigenvar must shift under inner
  binders — literal `gen0` is only right when the child has no binders below the new one),
  and full comb verification of ∃ via a universal witness (the drinker needs an enclosing ∀).
- **K6.3** — resource phase: `RWeaken→W/WForall`, `RContract/RDuplicate→ medials + Ac/CForall`
  (Theorem 29 + Lemmas 25/26); compute the linearized `A'`. The hard part.
- **K6.4** — wire into `comb_checker` after `eliminate_cuts`; corpus coverage.

## K6.5 — entries-list (the perf rewrite)

The naive `tr` ends every node at `denote(d.conclusion)` *exactly* (left-assoc, in the
LKR sequent's order) and reconciles to that shape with `equiv_steps`/`reorder_steps`. For
wide sequents this is the step-blowup: `eq_iff_eq` = 44540 steps, **93–98% `Eqv`** (assoc/comm
reassociation). The paper treats `≡` as a free congruence; those steps should not exist.

The KS1 checker (`ks1::check`) is **modulo ≡** in two senses that make the order/bracketing of
the sequent disjunction free, so the reassociation never has to be emitted:

1. **AC-tolerant rule matching** — the chain rules (`Sw/Mix/Ac/M/MForall/MExists`) flatten the
   ∧/∨-chain at `context` and pick operands; they find their redex regardless of order or
   bracketing.
2. **Modulo-≡ endpoint** — `check` accepts when `equiv(replay(⊤,steps), goal)`; the *final*
   formula's order/bracketing is free.

Therefore **the sequent's entry order carries no meaning**: rules locate their entries by
identity, never by position, and no `Eqv` is needed to permute/reassociate the disjunction.

### New contract

`tr(d) → (steps, entries)` where `entries : vector<FormulaHandle>` is the sequent's entries as
**opaque subtrees**, in the order they sit in the actual current formula, with the invariant

> `replay(⊤, steps)  ==  denote_leftassoc(entries)`  (by handle).

`entries` is an **order-free bag**: it need NOT match `d.conclusion`'s order. A `∨`-valued entry
(e.g. an `ROr` result `A∨B`) is kept GROUPED as one entry — never flattened — so its boundary
survives (this is the fix to the "entries lose their boundary under `flat_or`" blocker). The
path to `entries[i]` in the n-entry left-assoc tree is `[Left]^(n-1-i)` for `i=0`, else
`[Left]^(n-1-i) ++ [Right]` (empty for n=1).

### Per-rule (order-free)

- `RExchange` — **passthrough**: return `tr(child)` verbatim (0 steps). The permutation is a
  no-op; downstream finds entries by identity.
- `RWeaken` — one `W(φ)@{}` (`F → F∨φ`); `entries = child ++ [φ]`. No reorder.
- `RAx` — `Ai(α)` then `W` each non-pair entry; `entries = [α, ᾱ] ++ others`. No reconcile.
- `RDuplicate` — contract the two equal entries via `M/MForall/MExists` + `Ac` **operand
  selectors** (no reorder/group); `entries` = child with one copy dropped.
- `ROr` — group child's `A`,`B` entries into one `A∨B` entry (the only place a local
  `AssocOr`/`reorder` is still needed, to physically form the subtree); ~free.
- `RAnd` — `Tu` + branch composition + switch sequence (P,Q opaque), then **no** `equiv_steps`
  reconcile — `entries = Γ_L ++ Γ_R ++ [φ∧ψ]` in whatever order the switch leaves them.
- `RForall`/`RExists` — as before, but contexts computed against the child's returned `entries`;
  the `DistForall` pull-out (RForall, non-empty Γ) stays.
- **Root** — `lkr_to_ks1` ends with one `equiv_steps(denote(entries), goal)` guard, bounded by
  goal size (normally a no-op: the single root entry == goal by handle).

Migration is incremental: first the signature change keeping `entries = d.conclusion` order
(behaviour-identical), then each rule relaxed to order-free.

### Status / measured (eq_iff_eq, the worst corpus theorem)

Every rule is now order-free with at most a LOCAL (O(distance)) reorder: `RExchange` (0 steps),
`RWeaken` (1 W), `RAx` (Ai+W, no reconcile), `RExists` (Ex in place). `ROr` and `RDuplicate`
bring the two grouped entries adjacent with a local move (not a full reorder into d.conclusion
order) and `AssocOr`-group; `RDuplicate` then contracts in place with the fixed-context
`contract_at` (touches only `X∨X`, preserving sibling grouping). `RAnd` moves φ/ψ to the rightmost
branch entry (bounded reorder) and reconciles its switch tail `((φ∧ψ)∨P)∨Q` with the
**entry-level** `reassoc_left_steps` (O(#entries) AssocOr rotations, entries opaque), falling
back to `equiv_steps` only if a spine ∨ aliases an entry handle.

| total steps | EQV | by-rule (self) |
|---|---|---|
| 44540 (before) | 43513 | RExchange 15237, RDuplicate 14229, RWeaken 9222, RAnd 3464, RAx 1269 |
| **4761 (now)** | 3734 | RDuplicate 4237 (move 2556 + contract 1681), RAnd 252, RForall 103, RWeaken 92, RAx 36, ROr 33, RExists 8 |

**9.4× fewer steps** (eq_refl 1770→659, the mid theorems ~3000→~700). Corpus unchanged: 19/19 OK
(ordered_pair), 6/7 OK (functions); the cutfree theorems still hit the separate
Thm-17-decompose bridge gap — no new translation errors.

The residual is `RDuplicate`. Its cost splits (diagnostic, gated on `LKR_TO_KS1_STATS`) into the
grouping **move** (2556 — the safe floor) and the **contract** (1681). The move is essentially
irreducible *safely*: contraction needs the two copies grouped as `X∨X`, and grouping two entries
`d` apart costs ~`d`. The operand-select-at-top alternative (`M`/`Ac` with operand indices on the
whole top ∨-chain) would avoid it but is UNSOUND in general — the checker's `M` flattens and
rebuilds the entire top chain, destroying the grouping of sibling ∨-entries (`ROr` results) that a
parent may locate by identity. The only remaining *safe* win is replacing `contract_at`'s
`xx_or_regroup` (assoc/comm for ∨-nested-in-X) with a local flatten + operand-select `Ac`/`M`
inside the already-grouped `X∨X` subterm (safe because X is one opaque entry) — modest, and capped
by the move floor; left for a future session.

## Oracle

Every phase is gated end-to-end by `build_comb_proof` → `CombVerifier` (all four phases) on
hand-built cut-free Derivs, plus `ks1::check` as an intermediate gate. `test/lkr_to_ks1_test.cpp`.
