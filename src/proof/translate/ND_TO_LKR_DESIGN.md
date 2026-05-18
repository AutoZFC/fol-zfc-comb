# ND → LKR Translation: Mathematical Specification

Reference: Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236, §11 + §15.

This document is the source of truth for the `src/proof/translate/nd_to_lkr/`
translator. The C++ implementation is correct iff its emitted output is a
faithful realisation of this spec, in the sense that `LKRVerifier` accepts the
output for every input that ND-verifies and is iota-free and eq_subst-free.

## 0. Status

In design. Translator not yet implemented. This doc replaces the previous
spec (deleted with the old translator in commit `762fb65`); §1–§5 salvage and
re-state the math, §6 makes the four old bug classes impossible by
construction.

## 1. Scope

**Input.** `Program<nd::Instr>` produced by `nd::lower(...)`. Iota-free
(no `IotaElim` after the `EliminateIotaInProof` pass, or no iota by
construction). eq_subst-free (no `EqSubst` or `EqSym`; deprecated per
`EQ_SUBST_DEPRECATION.md`). ND-verifies under `nd::NDVerifier`.

**Output.** `Program<lkr::Instr>` over Hughes §11 (`AxiomLit`, `One`,
`Exchange`, `Weakening`, `Contraction`, `And`, `Or`, `Forall`, `Exists`) +
§15 (`Cut`) + the lemma-as-cut realiser (`CloseByLemma`). No other ops.

**Goal.** `LKRVerifier(ctx, NNF(claim), translate(prog)) = Ok` for every
in-scope input.

**Trust boundary.** The translator is *not trusted*. Soundness rests on
`LKRVerifier` accepting the output. The translator's only obligations:
(a) emit a sequence the verifier accepts (completeness on supported
input); (b) reject out-of-scope inputs with a clear error at the gate
(no silent fall-through).

## 2. Math

### 2.1 Negation normal form

Computed by `FormulaBuilder::to_nnf`:

```
NNF(p)         = p                                  (positive atoms)
NNF(¬p)        = ¬p                                  (negative atoms)
NNF(¬¬φ)       = NNF(φ)
NNF(φ ∧ ψ)     = NNF(φ) ∧ NNF(ψ)
NNF(¬(φ ∧ ψ))  = NNF(¬φ) ∨ NNF(¬ψ)
NNF(φ ∨ ψ)     = NNF(φ) ∨ NNF(ψ)
NNF(¬(φ ∨ ψ))  = NNF(¬φ) ∧ NNF(¬ψ)
NNF(φ → ψ)     = NNF(¬φ) ∨ NNF(ψ)
NNF(¬(φ → ψ))  = NNF(φ) ∧ NNF(¬ψ)
NNF(φ ↔ ψ)     = (NNF(¬φ) ∨ NNF(ψ)) ∧ (NNF(φ) ∨ NNF(¬ψ))
NNF(¬(φ ↔ ψ))  = (NNF(φ) ∧ NNF(¬ψ)) ∨ (NNF(¬φ) ∧ NNF(ψ))
NNF(∀x.φ)      = ∀x. NNF(φ)
NNF(¬∀x.φ)     = ∃x. NNF(¬φ)
NNF(∃x.φ)      = ∃x. NNF(φ)
NNF(¬∃x.φ)     = ∀x. NNF(¬φ)
NNF(⊥)         = ⊥                                  (false)
NNF(¬⊥)        = ¬⊥                                  (top literal, encodes 1)
```

**Atomic literal:** positive atom or its negation. **Dual:** `(α, ᾱ)`
for the same atom α. **Top literal:** `¬⊥` (Hughes §11 rule `One`).

For NNF formulas `a, b`, we write `a ⊥ b` (read: *a and b are
NNF-dual*) when `NNF(¬a) ≡ b` structurally.

### 2.2 LKR sequents

A sequent `⊢ Γ` is provable iff at least one formula in Γ holds
classically. The verifier maintains an open-goals stack; the initial
state is `[[NNF(claim)]]`. Closing ops pop a goal; branching ops (`And`,
`Cut`) push two new goals; linear ops replace the top. Success: empty
stack after the last op.

### 2.3 Cut-spine invariant

The translator implements the standard one-sided ND→LK translation via
classical cut.

**Realiser correspondence.** Each ND step `k` deriving formula `F_k`
under assumptions `A_1, …, A_m` and eigenvariables `[e_1, …, e_p]`
contributes to the LKR proof by being *cut into* the goal. The LKR
sequent at the cut-spine point for `k` has the shape

```
⊢ B, ¬A_1_nnf, …, ¬A_m_nnf, ¬F_1_nnf, …, ¬F_{k-1}_nnf
```

where `B` is the current *goal disjunct* — the conclusion to be proved
for the innermost open sub-block, NNF-normalised. The negation of
each in-scope assumption `A_i` appears in Γ because of the unfolding
done at the `IMPLIES`/`NOT` block opener (§4.3, §4.4); the negation of
each previously-derived `F_j` appears via the per-step `Cut` (§4.6).

This is the **cut-spine invariant**: derived facts are introduced by
classical cut; the *positive* form is proved on `Cut`'s LEFT branch;
the *negative* form is carried into Γ on the RIGHT branch. RIGHT
continues the proof of `B`.

### 2.4 Why cut-spine

- Matches ND's SSA-linear shape (the input is a linear op stream).
- Free sharing: a step's negation appears in Γ once and can be
  referenced as many times as later steps need it.
- The deleted translator used cut-spine and reached ~93% success on
  ND-verified slice — strategy is empirically sound; only its
  realisation needed redesign.

## 3. Translator architecture

```
                   Program<nd::Instr>
                          │
                          ▼
                ┌───────────────────┐
                │   input gate      │  reject IotaElim, EqSubst, EqSym;
                │                   │  reject non-ND-verifying input
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │  block-tree       │  flat stream → nested BlockTree
                │  decompose        │  (OUTER / FORALL / IMPLIES /
                │                   │   NOT / EXISTS_ELIM)
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │  trace formulas   │  NDVerifier::trace_formulas →
                │                   │  F[k] : nd_idx → FormulaHandle
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │  cut-spine driver │  tree-recursive over BlockTree.
                │  (emit ops)       │  Each recursive call owns its
                │                   │  local SequentShadow; no shared
                │                   │  mutable state across siblings.
                └─────────┬─────────┘
                          │
                          ▼
                ┌───────────────────┐
                │   output gate     │  LKRVerifier::verify on the
                │                   │  emitted Program; reject on any
                │                   │  verifier error.
                └─────────┬─────────┘
                          ▼
                  Program<lkr::Instr>
```

### 3.1 Block tree

The flat ND op stream is reorganised into a nested tree (decompose pass):

```
Block ::= OUTER       { body, closer = Qed,           target = qed.derived }
        | FORALL[v]   { body, opener = Fix,           closer = ForallIntro,
                        target = forall_intro.body }
        | IMPLIES[A]  { body, opener = Assume,        closer = ImpliesIntro,
                        target = implies_intro.conclusion }
        | NOT[A]      { body, opener = Assume,        closer = NotIntro,
                        target = not_intro.bottom }
        | EXISTS_ELIM { body, opener = ExistsElim,    closer = ExistsIntro(no-witness),
                        target = exists_intro.body }

BodyItem ::= FlatStep nd_idx | Block
```

Each `FORALL` and `EXISTS_ELIM` block carries its eigenvariable
`Term::fixed(v)`, allocated via `FormulaBuilder::enter_scope()` at
block-open time. Each `IMPLIES`/`NOT` carries the assumption's
parsed `FormulaHandle`.

### 3.2 Per-step formulas

`F[k] = NDVerifier::trace_formulas(ctx, prog)[k]` — the verifier-derived
formula for each ND step. Already implemented as a side channel
(commit `e2ccc9a`).

For block openers/closers, additional formulas:
- IMPLIES/NOT opener: `step_formula[opener] = A` (the assumption).
- EXISTS_ELIM opener with witness `v` on `∃x.φ`:
  `step_formula[opener] = φ[x:=v]`.
- Any sub-block closer: `step_formula[closer]` = the block's *result*
  formula (`∀v.target`, `A→target`, `¬A`, or `∃v.target` respectively).

The translator computes these once and reads them at emission time.

### 3.3 Sequent shadow — local-scope discipline

```
SequentShadow {
    entries        : vector<FormulaHandle>     -- positions are stable WITHIN
                                                  a single recursive call frame
    step_to_neg_idx: map<nd_idx, size_t>       -- position of ¬F_k_nnf for each
                                                  cut-in step visible at this frame
    lkr_term_for   : map<nd_idx, TermRef>      -- ND TermRef → LKR TermRef
                                                  (Forall/ExistsElim eigens)
}
```

**Key discipline: each recursive call owns its own `SequentShadow`.**
The shadow is constructed at the start of the call, mutated during the
call's emission, and discarded at return. No two recursive calls share
a mutable shadow.

When a recursive call needs to branch (multiplicative `And`, `Cut`), it
*constructs* the two child shadows by selecting which of its entries
each child needs and remapping their indices. Each child call gets its
own fresh shadow. The parent's shadow is unaffected.

This eliminates the entire "stale-index after multiplicative-And"
failure mode of the old translator (bug class #4 in the deleted spec).
Position arithmetic is locally tractable because each frame's shadow
is small and changes only via predictable monotonic operations: ops
that mutate-in-place (`Or`, `Forall`, `Exists`), ops that only append
(`Cut`, `Weakening`), ops that swap (`Exchange`). The branching ops
hand off — they do not mutate the parent.

### 3.4 Split planner

Multiplicative `And` and `Cut` partition the parent's non-principal
entries between LEFT and RIGHT children. The translator declares
*what each child needs* — `left_needs : set<nd_idx>` and
`right_needs : set<nd_idx>` — and the split planner derives the
partition:

- Every entry in `left_needs` goes LEFT.
- Every entry in `right_needs` goes RIGHT.
- Entries needed by *neither* go anywhere (default LEFT, by convention).
- An entry in *both* sets requires explicit `Weakening` before the split
  to duplicate it (then one copy goes LEFT, the other RIGHT).

This is the *opposite* of the old translator's API, which took an
opaque `right_only` and silently routed "everything else" to LEFT.
The new API makes both sides' needs explicit, so partition failures
("entry X needed by RIGHT but routed LEFT") become a translator
precondition violation surfaced *before* emission, not a downstream
verifier rejection. Eliminates bug class #3.

### 3.5 Dual-decomposition closer

```
emit_close(shadow, pos_a, pos_b) → vector<lkr::Instr>
```

Pure function. **Precondition:** `shadow.entries[pos_a]` and
`shadow.entries[pos_b]` are NNF-dual (`a ⊥ b`).

**Algorithm:** structural recursion on the shape of `a`.

| `shadow.entries[pos_a]` shape | `shadow.entries[pos_b]` shape | Emission |
|---|---|---|
| atomic literal | atomic literal | `AxiomLit(pos_a, pos_b)` |
| `¬⊥` (top) | (any) | `One(pos_a)` |
| (any) | `¬⊥` (top) | `One(pos_b)` |
| `φ ∨ ψ` | `NNF(¬φ) ∧ NNF(¬ψ)` | `Or(pos_a)`; split planner builds LEFT (needs `{pos_a (=φ), pos_b_left_conjunct}`) + RIGHT (needs `{pos_a_appended (=ψ), pos_b_right_conjunct}`); multiplicative `And(pos_b, partition)`; recurse `emit_close` on each subgoal |
| `φ ∧ ψ` | `NNF(¬φ) ∨ NNF(¬ψ)` | swap roles; recurse with `(pos_b, pos_a)` |
| `∀x.φ` | `∃x.NNF(¬φ)` | allocate fresh eigen `v`; `Forall(pos_a, eigen=v)`; `Exists(pos_b, witness=TermRef↑Forall)`; recurse on the mutated entries (still dual; eigen substitution preserves duality) |
| `∃x.φ` | `∀x.NNF(¬φ)` | swap roles; recurse with `(pos_b, pos_a)` |
| anything else | anything else | precondition violation → error |

**Generic over rule provenance.** `emit_close` never pattern-matches
rule-specific shapes (no "Iff has this expansion" branches). It walks
NNF structure only. Eliminates bug class #1 — the close path cannot
miscount Iff conjuncts because it never names them.

## 4. Per-block translation schemas

Notation. `result_idx` = position in the parent's `SequentShadow.entries`
where the block's *result formula* (NNF) sits when the opener runs.
`qed_slot` = the position the block's body must drive to closure.

### 4.1 OUTER

**Initial state.** `shadow.entries = [NNF(claim)]`, `result_idx = 0`.

`qed_slot := result_idx`. Recurse on body items using the cut-spine
schema (§4.6). After all body items: call `emit_close(qed_slot,
step_to_neg_idx[Qed.derived])`.

### 4.2 FORALL block (body proves `∀v.target` in the parent)

The opener turns `∀v.target_nnf` (at `result_idx`) into `target_nnf[x:=v]`
inside the body's scope.

```
emit Forall(principal=result_idx, eigen=v)
shadow.entries[result_idx] := target_nnf[x:=v]
qed_slot := result_idx
recurse on body items (§4.6)
emit_close(qed_slot, step_to_neg_idx[ForallIntro.body])
```

The eigen `v` is recorded in `shadow.lkr_term_for[Fix.idx]` so flat
steps can resolve ND TermRefs to LKR TermRefs.

### 4.3 IMPLIES block (body proves `A → target` in the parent)

NNF: `NNF(¬A) ∨ NNF(target)`.

```
emit Or(principal=result_idx)
shadow.entries[result_idx]      := NNF(¬A)        -- assumption's negation in scope
shadow.entries.push_back(NNF(target))             -- new qed_slot
shadow.step_to_neg_idx[opener]  := result_idx     -- body refers to A via ¬A's slot
qed_slot := shadow.entries.size() - 1
recurse on body items
emit_close(qed_slot, step_to_neg_idx[ImpliesIntro.conclusion])
```

### 4.4 NOT block (body proves `¬A` in the parent)

NNF: `NNF(¬A)`. The result is already in the right NNF form — no
opener emission needed.

```
shadow.step_to_neg_idx[opener] := result_idx
-- no LKR op emitted at opener
recurse on body items
-- the body's closer is NotIntro.bottom, a NotElim step deriving ⊥
-- from some `negation` and `formula`. Pair their negations directly:
emit_close(step_to_neg_idx[NotElim.negation], step_to_neg_idx[NotElim.formula])
```

### 4.5 EXISTS_ELIM block (body proves something using `∃x.φ`'s witness)

The cut-spine has already processed the underlying `ExistsElim` ND
step at the parent level, putting `∀x.NNF(¬φ)` at some
`neg_exists_idx = step_to_neg_idx[ExistsElim.formula]`. The opener
introduces the eigen `v`:

```
emit Forall(principal=neg_exists_idx, eigen=v)
shadow.entries[neg_exists_idx] := NNF(¬φ)[x:=v]
shadow.step_to_neg_idx[opener] := neg_exists_idx
shadow.lkr_term_for[ExistsElim.idx] := <TermRef↑Forall>
recurse on body items
-- closer is ExistsIntro(no witness); result formula = body's
emit_close(qed_slot_unchanged, step_to_neg_idx[ExistsIntro.body])
```

### 4.6 Flat step: the cut-spine schema

Every flat step `k` that derives a formula `F_k` (`Use`, `SchemaInst`,
`AndIntro`, `AndElim_l/r`, `OrIntro_l/r`, `OrElim`, `ImpliesElim`,
`IffIntro`, `IffElim_l/r`, `ForallElim`, `ExistsIntro` with witness,
`ExcludedMiddle`, `ClassicalAbsurd`, `Peirce`, `DoubleNegElim`,
`BottomElim`):

```
F_k_nnf := NNF(F[k])
emit Cut(F_k_nnf)
-- LEFT child: build child shadow with parent.entries ++ [F_k_nnf]
--             at F_k_idx = parent.entries.size()
left_child  := derive_shadow(parent, append=[F_k_nnf])
close_step_k(left_child, k, F_k_idx)
-- RIGHT child: parent.entries ++ [NNF(¬F_k)]
right_shadow := parent + append [NNF(¬F_k)]
right_shadow.step_to_neg_idx[k] := parent.entries.size()
-- (continue body iteration with right_shadow as the new working shadow)
```

The flat steps that derive *no* propositional content are exceptions:

- **`Fix`**, **`Assume`**, **`Let`** — scope/marker only. No LKR op. The
  block-tree already accounts for `Fix` and `Assume`; `Let` records its
  formula in a side table for later `or_intro_l/r` references.
- **`NotElim`** — derives ⊥ as a "ghost" consumed only by the enclosing
  NOT-block closer or by `BottomElim`. Records its operands' nd_idx;
  emits no LKR op. The consumer (NOT closer or BottomElim) emits the
  closing `emit_close`.

### 4.7 `close_step_k` — LEFT-branch realisers

Each rule's `close` function proves `F_k_nnf` (at `F_k_idx`) from the
LEFT child's sequent (parent's entries plus the cut formula at the
end). Available in Γ: the goal disjunct `B`, the negations of in-scope
assumptions, the negations of earlier cut-in derived facts (`F_j` for
`j < k`).

`i_X := shadow.step_to_neg_idx[X]` denotes the slot of `¬F_X_nnf`.

Below, every emission ends with one or more `emit_close` calls, never
with rule-specific structural moves to close. The LKR ops emitted
beforehand only re-shape the sequent into a form where `emit_close`'s
preconditions hold.

#### `close_use(L)`

`F_k_nnf = NNF(L)` (modulo schema bindings). Emit `CloseByLemma(L)`.
Verifier resolves `L`'s formula against the registry; `NNF(L)` must
appear in the current sequent, which it does (at `F_k_idx`).

#### `close_schema_inst(D)`

As `close_use`, with `bindings = D.bindings`.

#### `close_and_intro(a, b)`

`F_k = A ∧ B`. Split-planner partition: LEFT needs `{i_a}`,
RIGHT needs `{i_b}`. Emit multiplicative `And(F_k_idx, partition)`.
LEFT subgoal pairs `(left_phi = NNF(A))` with `(i_a → NNF(¬A))`;
RIGHT pairs `(right_theta = NNF(B))` with `(i_b → NNF(¬B))`. Each
closed by `emit_close`.

#### `close_and_elim_l(of)` / `close_and_elim_r(of)`

`F_k = A` (resp. B). `i_of` holds `NNF(¬A) ∨ NNF(¬B)`. Emit
`Or(i_of)` — splits to `NNF(¬A)` at `i_of` and `NNF(¬B)` appended.
For `_l`: `emit_close(F_k_idx, i_of)`. For `_r`:
`emit_close(F_k_idx, last_idx)`.

#### `close_or_intro_l(a, b_formula)`

`F_k = A ∨ B`, where A is derived. Emit `Or(F_k_idx)` — splits to
`NNF(A)` at `F_k_idx` and `NNF(B)` appended. Emit
`emit_close(F_k_idx, i_a)`. RIGHT (appended NNF(B)) is unused —
`Weakening` it away, OR leave the goal closed since AxiomLit on
LEFT pair suffices once the recursion completes. (Detail: NN(B)
sits as an extra entry; the LEFT close consumes the goal; the
appended entry is discarded with the goal.)

#### `close_or_intro_r(a_formula, b)`

Symmetric: `Or(F_k_idx)`; `emit_close(last_idx, i_b)`.

#### `close_or_elim(or_formula, ac, bc)`

`F_k = C`. `i_or` holds `NNF(¬A) ∧ NNF(¬B)`. `i_ac` holds
`NNF(A) ∧ NNF(¬C)`. `i_bc` holds `NNF(B) ∧ NNF(¬C)`. `F_k_idx`
holds `NNF(C)`.

Both `i_ac` and `i_bc` reference `NNF(¬C)` which must be paired
against `NNF(C)`. The split planner declares
`left_needs = {i_or, i_ac, F_k_idx}` and
`right_needs = {i_or, i_bc, F_k_idx_dup}` where `F_k_idx_dup` is
a `Weakening`-prepared duplicate. Multiplicative `And(i_or, partition)`.

- LEFT: `NNF(¬A)` (And's left_phi) vs `NNF(A) ∧ NNF(¬C)` at `i_ac`:
  inner `And(i_ac, ...)` splits `i_ac` into `NNF(A)` and `NNF(¬C)`;
  `emit_close(NNF(¬A), NNF(A))` and `emit_close(F_k_idx, NNF(¬C))`.
- RIGHT: symmetric with B.

The duplicate-via-Weakening is the only rule needing prep; the planner
makes this explicit at the call site rather than buried in close logic.

#### `close_implies_elim(impl, ant)`

`F_k = consequent`. `i_impl` holds `NNF(ant) ∧ NNF(¬consequent)`;
`i_ant` holds `NNF(¬ant)`. Split-planner partition:
`left_needs = {i_ant}`, `right_needs = {F_k_idx}`. Multiplicative
`And(i_impl, partition)`.

- LEFT: `NNF(ant)` vs `NNF(¬ant)` at `i_ant` → `emit_close`.
- RIGHT: `NNF(¬consequent)` vs `NNF(consequent)` at `F_k_idx` → `emit_close`.

#### `close_iff_intro(ab, ba)`

`F_k = A ↔ B`. `F_k_nnf = (¬A_nnf ∨ B_nnf) ∧ (A_nnf ∨ ¬B_nnf)`.
`i_ab` holds `NNF(A) ∧ NNF(¬B)`; `i_ba` holds `NNF(B) ∧ NNF(¬A)`.

**Approach: never inspect Iff's NNF expansion directly.** Treat the
cut formula as opaque shape `X ∧ Y`. The split planner partitions:
`left_needs = {i_ab}`, `right_needs = {i_ba}`. Multiplicative
`And(F_k_idx, partition)`.

- LEFT subgoal contains `X = (NNF(¬A) ∨ NNF(B))` and `NNF(A) ∧ NNF(¬B)`.
  Emit `Or(...)` on `X`; emit multiplicative `And` on the conjunction;
  call `emit_close` on each resulting dual pair. The dual-decomposition
  is generic — *we do not need to identify which conjunct is which
  semantically*. The NNF child-children-children walk done by
  `emit_close` matches them up because they ARE dual.
- RIGHT subgoal: same shape with B/A swapped. Same generic close.

This is the fix for old bug class #1: the new close does not
pre-position-match Iff's NNF expansion. `emit_close` handles it
generically.

#### `close_iff_elim_l(iff, a)`

`F_k = B`. `i_iff` holds `NNF(¬F_iff) = (NNF(A) ∧ NNF(¬B)) ∨ (NNF(¬A) ∧ NNF(B))`.
`i_a` holds `NNF(¬A)`.

Emit `Or(i_iff)` → splits to `(NNF(A) ∧ NNF(¬B))` at `i_iff` and
`(NNF(¬A) ∧ NNF(B))` appended. Split-planner:
`left_needs = {i_iff, i_a}`, `right_needs = {appended_idx, F_k_idx}`.
Multiplicative `And` on `i_iff` then closes via `emit_close` on each
side.

#### `close_iff_elim_r(iff, b)`

Symmetric.

#### `close_forall_elim(h, t)`

`F_k = body[x:=t]` where `step_formula[h] = ∀x.body`. `i_h` holds
`∃x.NNF(¬body)`. Emit `Exists(principal=i_h, witness=t_lkr)`;
shadow mutates to `NNF(¬body)[x:=t]` at `i_h`. Call
`emit_close(F_k_idx, i_h)`.

#### `close_exists_intro(body, witness)`

`F_k = ∃x.body`. `i_body` holds `NNF(¬body[x:=witness])`. Emit
`Exists(principal=F_k_idx, witness=t_lkr)`; shadow mutates to
`NNF(body)[x:=witness]` at `F_k_idx`. Call `emit_close(F_k_idx, i_body)`.

#### `close_excluded_middle(let_A)`

`F_k = A ∨ ¬A`. Emit `Or(F_k_idx)` → splits to `NNF(A)` at
`F_k_idx` and `NNF(¬A)` appended. Call `emit_close(F_k_idx, appended_idx)`.
The two entries are NNF-dual by definition — generic close handles them.

#### `close_classical_absurd(bot)`

`F_k = (whatever the absurd ⊥ proves)`. Treats `bot` as a NotElim:
find its `negation` and `formula` operands; pair their negations
directly via `emit_close(step_to_neg_idx[negation], step_to_neg_idx[formula])`.

#### `close_peirce(a_let, b_let)`

Peirce's law: `((A → B) → A) → A`. NNF:
`((¬A ∨ B) ∧ ¬A) ∨ A`.

**Strategy.** Cut on `A` directly (no need for excluded middle as a
separate lemma — the Cut suffices). The LEFT_inner subgoal has `A`
appended; the RIGHT_inner has `¬A`. Each closes against `F_k_nnf`
by structural decomposition.

**Op sequence.**

```
Cut(A)                                  push LEFT_inner [..., F_k_nnf, A], RIGHT_inner [..., F_k_nnf, ¬A]

LEFT_inner:
  Or(f_k_idx)                           F_k_nnf → (¬A∨B)∧¬A at f_k_idx; A appended (call it A_or)
  And(f_k_idx, partition=[A_cut_idx])   split the conjunction. LEFT_sub gets A_cut + (¬A∨B);
                                        RIGHT_sub gets A_or + ¬A.
  LEFT_sub:
    Or(left_phi_idx)                    (¬A∨B) → ¬A at left_phi_idx; B appended
    emit_close(A_cut, ¬A at left_phi_idx)   close (A and ¬A are NNF-dual)
  RIGHT_sub:
    emit_close(A_or, ¬A at right_theta_idx) close

RIGHT_inner:
  Or(f_k_idx)                           F_k_nnf → (¬A∨B)∧¬A at f_k_idx; A appended (A_or)
  emit_close(A_or, ¬A_cut)              close (the second-disjunct A vs the Cut's ¬A)
```

The two `emit_close` calls in LEFT_sub and RIGHT_sub close pairs of
NNF-dual entries: `(A_nnf, NNF(¬A))`. `emit_close` recursively
decomposes if `A` is non-atomic; for atomic `A`, it emits a single
`AxiomLit`.

**Why this works.** Both inner subgoals close because:
- `LEFT_inner`: the Cut introduced an `A` we can pair with the `¬A`
  hidden inside `F_k_nnf`'s `(¬A ∨ B) ∧ ¬A` conjunct. The `And` rule
  multiplicatively splits this conjunction so the `¬A` lands in
  RIGHT_sub, where the `A_or` (second disjunct of F_k_nnf) pairs
  with it. The LEFT_sub has the Cut's `A` and the `(¬A ∨ B)` factor;
  after `Or` split, its `¬A` part pairs with the Cut's `A`.
- `RIGHT_inner`: the Cut introduced a `¬A` we can pair with the
  `A` from F_k_nnf's second disjunct (after `Or` split).

**Soundness.** Each closing `emit_close` call pairs NNF-dual entries
(by construction of A_nnf and NNF(¬A)). The Cut adds an auxiliary
disjunct `(A ∧ ¬A)` to the §15-augmented goal at the LKRtoComb
layer; classically equivalent to the original.

**Test plan.**

1. `peirce_atomic` — Peirce schema with A=p (atomic), B=q. The
   simplest case; `emit_close` calls land at `AxiomLit`.
2. `peirce_complex_A` — A = `p ∨ q` (non-atomic). `emit_close`
   recursively decomposes; verifies the strategy works for any A.
3. (NDtoLKR test): an ND proof using `peirce p q` to derive
   `((p→q)→p)→p`; end-to-end through NDtoLKR.

#### `close_double_neg_elim(of)`

`F_k = A` where `step_formula[of] = ¬¬A`. NNF normalises `¬¬A` to
`NNF(A)`, so `F_k_nnf = NNF(of)` already. `emit_close(F_k_idx, i_of)`
directly — they are duals because... wait, `i_of` holds `NNF(¬¬¬A) = NNF(¬A)`.
And `F_k_idx` holds `NNF(A)`. These ARE dual. Done.

#### `close_bottom_elim(bot)`

`F_k` is some "target_formula" that the classical-absurd ⊥ pulls.
`bot` must be a NotElim; emit `emit_close` on the negations of
NotElim's `negation` and `formula` operands. The `F_k` requirement
is auto-discharged because the verifier accepts that the closing
ops closed *some* goal (the goal containing both ¬F_k and the
contradiction).

Actually: NotElim derives ⊥; BottomElim derives F_k. In the cut-spine
sequent at this `close_bottom_elim` call, we have the goal `F_k_nnf`
and the negations of NotElim's operands. `emit_close` on those two
negations closes via contradiction and discharges the goal — the
verifier accepts because the closing ops applied to *some* sequent
entries.

## 5. Soundness contract

**Input gate** (before any emission):
1. Program ND-verifies (run `NDVerifier::verify` against the goal).
2. Program contains no `IotaElim` (pre-pass invariant violation).
3. Program contains no `EqSubst` or `EqSym` (deprecation violation).

Any failure → `Result::error` with the offending nd_idx and a
clear deprecation pointer where applicable.

**Output gate** (after emission):
4. Emitted `Program<lkr::Instr>` verifies under `LKRVerifier` against
   `NNF(goal)`. Any verifier rejection is a translator bug surfaced
   at the boundary; the translator returns Error rather than silently
   emitting a broken proof.

These gates make the translator non-trusted in the same sense as the
`EliminateIotaInProof` pass.

## 6. What this design makes impossible

The old translator's failure modes, mapped to design elements that
eliminate them:

| Old bug class | Cause | Fix in this design |
|---|---|---|
| #1 — `close_iff_intro` RIGHT-branch swap | Per-rule code pattern-matched Iff's NNF child positions; semantic vs. structural mismatch | `emit_close` recurses generically over NNF structure; never names rule-specific expansions. `close_iff_intro` only emits an `And` split; the close is generic. |
| #2 — `emit_axiom_decomp` called with non-dual entries | Downstream of #1 | Fixed when #1 is fixed; `emit_close` preconditions enforced at every call site (translator panics if the planner emits a non-dual pair, which is a translator bug surfaced immediately). |
| #3 — multiplicative-And partition collisions | Opaque `right_only` API; rules silently routed "everything else" to LEFT | Split planner takes explicit `left_needs` + `right_needs`; partition derived from those, with `Weakening`-prep for both-sides entries. Partition violations are translator-precondition errors, not verifier rejections. |
| #4 — `ts.seq` shadow stale across multiplicative-And | Single mutable shadow patched after splits; cross-cut dependencies silently aliased | Each recursive call owns its own `SequentShadow`; branching ops construct *child* shadows and recurse, never mutate the parent. The "shadow goes stale" failure mode does not exist. |

## 7. Completeness contract

For every input that:
- ND-verifies under `nd::NDVerifier`,
- contains no `IotaElim`, `EqSubst`, `EqSym`,

`NDtoLKR::apply` returns `Ok(program)` such that `LKRVerifier` accepts
`program` against `NNF(goal)`.

This is *not* a corpus claim. It is a claim about the mathematical
construction: every ND rule has a per-rule schema (§4.7) that emits
LKR ops realising the cut-spine invariant (§2.3). Combining the
per-rule schemas under the block-tree structure (§3.1, §4) produces a
well-typed LKR program. Soundness of `LKRVerifier` (Hughes Lemma 11.1)
plus correctness of each per-rule schema gives the completeness claim.

Test demonstration: `test/nd_to_lkr_test.cpp` covers every ND rule
with at least one hand-crafted fixture that exercises the rule's
schema. Each fixture's output is verified by `LKRVerifier`.

## 8. Composition

`NDtoLKR` does *not* call `EliminateIotaInProof` internally. The
caller composes:

```cpp
auto iota_free = EliminateIotaInProof(ctx).apply(in);     // ND → ND (iota-free)
auto lkr_prog  = NDtoLKR(ctx).apply(iota_free.value());   // ND → LKR
LKRVerifier().verify(ctx, goal, lkr_prog.value());        // soundness witness
```

Each Pass is self-contained. The composition matches the Pass<>
discipline used by the iota translator.

## 9. Implementation phases

1. **Skeleton + gates.** `NDtoLKR` Pass class, input gate, output gate,
   `BUILD.bazel`. Test: empty/trivial programs round-trip; rejected
   inputs fail at the right gate.
2. **Block tree.** `decompose_blocks` reorganising flat → nested.
   Test: hand-walk fixtures.
3. **Sequent shadow + split planner.** `SequentShadow` type, planner
   for `And`/`Cut` partition. Test: planner unit tests.
4. **`emit_close`.** Pure dual-decomposition. Test: every NNF shape
   pair (atomic, ∨/∧, ∀/∃, top, mixed).
5. **Cut-spine driver + block schemas.** §4.1–§4.5 wired up. Test:
   trivial body (just a `Use`).
6. **Per-rule closes — lemma uses.** `close_use`, `close_schema_inst`.
   Test: single-use proofs round-trip end-to-end.
7. **Per-rule closes — propositional.** And, Or, Implies, Not,
   BottomElim, Iff. Test: per-rule fixtures.
8. **Per-rule closes — quantifiers.** ForallElim, ExistsIntro.
   (ForallIntro/ExistsElim are block closers, already in phase 5.)
9. **Per-rule closes — classical.** DoubleNegElim, ExcludedMiddle,
   ClassicalAbsurd, Peirce.
10. **Integration.** Compose with `EliminateIotaInProof`; run a few
    ZFC-flavoured proofs end-to-end.

Each phase's tests verify the output of that phase's covered rules
under `LKRVerifier`. A phase doesn't ship until its tests pass.

## 10. References

- Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236
  — §11 (LKR rule set), §15 (Cut endorsement).
- Troelstra-Schwichtenberg 2000, *Basic Proof Theory* §3.5.2 (GS1)
  — LKR-equivalent sequent calculus.
- `src/proof/lkr/ops.h` — the implemented LKR op set the translator
  emits into.
- `src/proof/translate/LAYER2_LEISENRING_DESIGN.md` — the surviving
  iota translator this design composes with.
- `src/proof/translate/EQ_SUBST_DEPRECATION.md` — eq_subst deprecation
  policy enforced at the input gate.
- The deleted SPEC.md from commit `762fb65^` — predecessor design;
  this doc supersedes it.
