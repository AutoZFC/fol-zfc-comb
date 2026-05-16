# ND→LKR Translation: Mathematical Specification

This document specifies the translation from natural-deduction (ND) proofs
to LKR proofs (Hughes 2019 §11 + Cut + CloseByLemma) as a metatheoretic
function on derivation trees. It is the source of truth that the
`src/proof/translate/nd_to_lkr.cpp` translator implements; the C++ code is
correct iff its emitted output is a faithful realization of this spec.

## 0. Scope and outputs

Source: `Program<nd::Instr>`, the linear ND op stream produced by
`nd::lower(...)`. The stream encodes a tree of nested *scopes* opened by
`Fix | Assume | ExistsElim` and closed by
`ForallIntro | ImpliesIntro | NotIntro | ExistsIntro(no-witness) | Qed`.
Between opener and closer is a sequence of *flat* ND ops (the ones that
neither open nor close a scope).

Target: `Program<lkr::Instr>` — a linear LKR op stream over the rules
`AxiomLit | One | CloseByLemma | Exchange | Weakening | Contraction |
And | Or | Forall | Exists | Cut`.

Goal: `LKRVerifier(ctx, NNF(claim), translate(nd_prog))` returns `Ok` for
every well-typed `nd_prog` whose ND verifier accepts.

The translator is **not trusted**. Soundness rests on `LKRVerifier`
accepting the output. The translator's only obligations are:
(a) emit a sequence the verifier accepts (completeness on its supported
input fragment), and (b) reject inputs it does not handle with a clear
error (no silent fall-through to undefined behavior).

## 1. Background: NNF, atomic literals, dualization

Negation-normal form is computed by `FormulaBuilder::to_nnf`:

```
NNF(p)         = p                              (positive atoms)
NNF(¬p)        = ¬p                              (negative atoms)
NNF(¬¬φ)       = NNF(φ)
NNF(φ ∧ ψ)     = NNF(φ) ∧ NNF(ψ)
NNF(¬(φ ∧ ψ))  = NNF(¬φ) ∨ NNF(¬ψ)
NNF(φ ∨ ψ)     = NNF(φ) ∨ NNF(ψ)
NNF(¬(φ ∨ ψ))  = NNF(¬φ) ∧ NNF(¬ψ)
NNF(φ → ψ)     = NNF(¬φ) ∨ NNF(ψ)
NNF(¬(φ → ψ))  = NNF(φ) ∧ NNF(¬ψ)
NNF(φ ↔ ψ)     = (NNF(¬φ) ∨ NNF(ψ)) ∧ (NNF(φ) ∨ NNF(¬ψ))      ⚠
NNF(¬(φ ↔ ψ))  = (NNF(φ) ∧ NNF(¬ψ)) ∨ (NNF(¬φ) ∧ NNF(ψ))      ⚠
NNF(∀x.φ)      = ∀x. NNF(φ)
NNF(¬∀x.φ)     = ∃x. NNF(¬φ)
NNF(∃x.φ)      = ∃x. NNF(φ)
NNF(¬∃x.φ)     = ∀x. NNF(¬φ)
NNF(⊥)         = ⊥
NNF(¬⊥)        = ¬⊥                              ("top literal")
```

The Iff cases are the only ones where the surface order of children does
not directly mirror the dual: in `NNF(A↔B) = (¬A∨B) ∧ (A∨¬B)`, the second
conjunct is `(A∨¬B)` and **not** `(¬B∨A)`. (See bug class #1 below.)

**Atomic literal** = positive atom (predicate or schema-var) or its negation.
**Dual** = `(α, ᾱ)` for the same atom α.
**Top literal** = `¬⊥`.

For NNF formulas a, b, we write `a ⊥ b` (a and b are *NNF-dual*) when
NNF(¬a) = b structurally.

## 2. The LKR sequent and the translation invariant

LKR sequents are right-sided: a sequent `⊢ Γ` is provable iff at least one
formula in Γ holds. The verifier maintains a stack of open sequents; ops
operate on the top. The initial sequent is `⊢ NNF(claim)`.

**Realizer correspondence.** Each ND step k that derives a formula F_k
under assumptions A_1, …, A_m and eigenvariables [e_1, …, e_p] contributes
to the LKR proof by being *cut into* the goal: the LKR sequent at that
point of the cut spine has the shape

    ⊢ B, ¬A_1_nnf, …, ¬A_m_nnf, ¬F_1_nnf, …, ¬F_{k-1}_nnf

where B is the *current goal disjunct* (the conclusion-to-prove for the
innermost open sub-block, NNF-normalized; B is itself one disjunct of the
NNF of the enclosing sub-block's result formula). The negation of every
in-scope assumption A_i appears in Γ via the unfolding done at the
IMPLIES/NOT block opener (§4.4); the negation of every previously-derived
F_j appears in Γ via the per-step Cut (§4.6).

This is the **cut-spine invariant**: derived facts are introduced by
classical cut, with their *positive* form proved on the LEFT branch and
their *negation* carried into Γ on the RIGHT branch. RIGHT continues the
proof of the original goal disjunct B.

## 3. The translator's data structures

### 3.1 Block tree (decompose pass)

The flat ND op stream is reorganized into a *block tree*:

```
Block ::= OUTER       { body : [BodyItem],   closer = Qed,           target = qed.derived }
        | FORALL[v]   { body : [BodyItem],   opener = Fix,           closer = ForallIntro,
                        target = forall_intro.body }
        | IMPLIES[A]  { body : [BodyItem],   opener = Assume,        closer = ImpliesIntro,
                        target = implies_intro.conclusion }
        | NOT[A]      { body : [BodyItem],   opener = Assume,        closer = NotIntro,
                        target = not_intro.bottom }
        | EXISTS_ELIM { body : [BodyItem],   opener = ExistsElim,    closer = ExistsIntro(no-witness),
                        target = exists_intro.body }

BodyItem ::= FlatStep nd_idx | Block
```

Each FORALL and EXISTS_ELIM block carries its eigenvariable (`Term::fixed(v)`),
allocated via `FormulaBuilder::enter_scope()` at block-open time.

### 3.2 Per-step formula tables (compute pass)

Two maps, populated by recursion over the block tree:
- `step_formula : nd_idx → FormulaHandle` — the *raw* (non-NNF) formula
   the ND verifier would assign to step k.
- `step_formula_nnf : nd_idx → FormulaHandle` — `NNF(step_formula[k])`.

Block openers/closers also produce step formulas:
- For an IMPLIES/NOT block with assumption A: `step_formula[opener]` = A.
- For an EXISTS_ELIM block with witness v opened on `∃x.φ`:
  `step_formula[opener] = φ[x:=v]`.
- For any sub-block: `step_formula[closer]` is the block's *result* formula
  (∀v.target, A→target, ¬A, or ∃v.target respectively).

### 3.3 Translator state during emission

```
ts.seq               : [FormulaHandle]              -- shadow of verifier's current sequent
ts.step_to_neg_idx   : nd_idx → size_t              -- index in ts.seq of ¬F_k_nnf for each cut-in step
ts.term_for_idx      : nd_idx → Term                -- ND eigenvars (Fix, ExistsElim's fresh, IotaElim's fresh)
ts.nd_to_lkr_termref : nd_idx → uint32_t            -- maps an ND TermRef to the LKR instr index of the
                                                    --   Forall op that bound the eigen on the LKR side
```

## 4. Per-rule translation schemas

Notation: `Γ` is the rest of the current sequent (the "context"). When a
rule emits multiple LKR ops, they appear in sequential order. `[idx_x]`
in subscript means "located at position idx_x in the current sequent."
Indices are stable under ops that only append (Cut, Weakening, Or in the
verifier's current spec) or only mutate the principal in place (Or
mutates principal, then appends); they shift after multiplicative-And
because LEFT/RIGHT subgoals are reindexed.

### 4.1 Outer translation (translate_block on OUTER)

**Initial state.** `ts.seq = [NNF(claim)]`.

Recursively translate the OUTER block with `result_idx = 0`. After all
body items, emit the *closer* — for OUTER, this means closing
`emit_axiom_decomp(qed_slot=0, step_to_neg_idx[Qed.derived])`.

### 4.2 FORALL block

**At the closer** the block contributes a FORALL formula `∀v.target`. We
must arrange the LKR sequent so that `∀v.target_nnf` sits at some position
`result_idx`, then dispatch the body inside the scope where v is fresh.

**Emit_opener.** Sequent has `∀v.target_nnf` at position `result_idx`.
Emit `Forall(principal=result_idx, eigen=v)`. Sequent mutates:
`ts.seq[result_idx] := target_nnf[x:=Term::fixed(v)]`. This is the new
qed_slot for the body.

**Body.** Recurse on each BodyItem (flat step or sub-block) using the
cut-spine pattern (§4.6).

**Emit_closer.** Pair qed_slot with `step_to_neg_idx[ForallIntro.body]`
via `emit_axiom_decomp` (§5).

### 4.3 IMPLIES block

The block's result formula is `A → target`. Its NNF is `NNF(¬A) ∨ NNF(target)`.

**Emit_opener.** Sequent has `NNF(¬A) ∨ NNF(target_nnf)` at `result_idx`.
Emit `Or(principal=result_idx)`. Sequent mutates: `ts.seq[result_idx] :=
NNF(¬A)` and `ts.seq.push_back(NNF(target_nnf))`.

Set `step_to_neg_idx[opener] = result_idx`. This is the cut-in *from
the implies block's perspective*: subsequent flat steps that depend on
the assumption A see `¬A_nnf` as an entry of Γ at this index.

The new qed_slot is `ts.seq.size() - 1` (the appended target).

**Closer.** As §4.2.

### 4.4 NOT block

The block's result formula is `¬A`. Its NNF is `NNF(¬A)`.

**Emit_opener.** Sequent has `NNF(¬A)` at `result_idx`. **No LKR op emitted.**
Just set `step_to_neg_idx[opener] = result_idx` so flat steps see the
assumption's negation.

**Closer.** The closer's `target` is a `not_elim` step deriving ⊥ from
some `negation` and `formula`. Resolve their `step_to_neg_idx` slots
(call them `i_neg, i_pos` — these are the negations of `negation` and
`formula` themselves, which are `formula` and `negation` respectively
because of double-negation). Pair them via `emit_axiom_decomp`.

### 4.5 EXISTS_ELIM block

The block opens on a derived `∃x.φ`. After Forall on the cut-in `∀x.NNF(¬φ)`
(see §4.6's cut for the underlying ExistsElim step), we have `NNF(¬φ)[x:=v]`
in the sequent — that is the assumption's negation visible to the body.

**Emit_opener.** The cut-in entry `step_to_neg_idx[ee.formula] = neg_exists_idx`
holds `∀x.NNF(¬φ)`. Emit `Forall(principal=neg_exists_idx, eigen=v)`.
Sequent mutates: that entry becomes `NNF(¬φ)[x:=v]`. Set
`step_to_neg_idx[opener] = neg_exists_idx` and bind the LKR TermRef for v.

**Closer.** The closer is `ExistsIntro(body)` with no witness; its result
formula equals the body's. Pair qed_slot with `step_to_neg_idx[body]`
via `emit_axiom_decomp`.

### 4.6 Flat step: the cut-spine schema

Every flat step k that produces a *derived* formula (Use, ForallElim,
ImpliesElim, AndIntro, AndElim_l/r, IffIntro, IffElim_l/r, OrIntro_l/r,
OrElim, ExistsIntro-with-witness, ExcludedMiddle, BottomElim, SchemaInst)
is translated by:

```
1. snapshot := ts.seq                          -- pre-cut state
2. emit Cut(F_k_nnf)
3. ts.seq.push_back(F_k_nnf)                   -- shadow LEFT subgoal
4. F_k_idx := ts.seq.size() - 1
5. close(F_k_idx)                              -- §4.7: realize F_k from Γ ∪ {F_k_nnf}
6. ts.seq := snapshot ++ [neg_F_k_nnf]         -- shadow RIGHT subgoal
7. step_to_neg_idx[k] := ts.seq.size() - 1
```

`Let` and `NotElim` are exceptions:
- `Let` derives nothing the proof can branch on; it just records
  `step_formula_nnf[k]` so later ops (e.g., `or_intro` referencing the
  let-bound disjunct) can read it. **No LKR op is emitted.**
- `NotElim` produces ⊥ as a "ghost" — it is consumed only by `BottomElim`
  or by a `NOT` block closer. It records `step_formula_nnf[k] = ⊥` and
  emits no LKR op. (`BottomElim` looks back through the StepRef chain
  to find the originating NotElim and pulls its operands.)

### 4.7 The `close` schemas (LEFT-branch realizers)

Each `close_X` proves `F_k_nnf` from Γ, where Γ contains: the current
goal disjunct B (positive); the negations of all in-scope assumptions
(A_i appears as `¬A_i_nnf`); the negations of all earlier cut-in derived
facts (F_j appears as `¬F_j_nnf`); and the `F_k_nnf` we just cut.

Below, `i_X` denotes `step_to_neg_idx[X]` — the position in ts.seq where
the negation of step X lives.

#### close_use(L)
Closes by appealing to a previously-verified theorem L.

```
emit CloseByLemma(L)        -- the verifier checks that NNF(L) is in Γ ∪ {F_k_nnf}.
```

Soundness: F_k_nnf = NNF(L), so NNF(L) ∈ {F_k_nnf} ⊂ Γ ∪ {F_k_nnf}.

#### close_schema_inst(D)
As above, with `bindings = D.bindings`.

#### close_forall_elim(h, t)
F_k = body[x:=t] where step_formula[h] = ∀x.body. The negation
`¬F_h_nnf = ∃x.NNF(¬body)` sits at i_h.

```
emit Exists(principal=i_h, witness=t_lkr)
   -- mutates ts.seq[i_h] := NNF(¬body)[x:=t]
emit_axiom_decomp(F_k_idx, i_h)
   -- pairs body[x:=t]_NNF with NNF(¬body)[x:=t] = NNF(¬(body[x:=t])) — duals
```

#### close_implies_elim(impl, ant)
F_k = consequent. `¬F_impl_nnf = NNF(antecedent) ∧ NNF(¬consequent)` at
i_impl. `¬F_ant_nnf = NNF(¬antecedent)` at i_ant.

```
multiplicative-And on i_impl with right_only = {F_k_idx}:
  LEFT  : pair (i_ant ↦ NNF(¬ant))                  vs  left_phi (= NNF(ant))
  RIGHT : pair (F_k_idx ↦ NNF(consequent) = F_k)    vs  right_theta (= NNF(¬consequent))
emit_axiom_decomp on each
```

#### close_and_intro(a, b)
F_k = A ∧ B. ¬F_a at i_a, ¬F_b at i_b.

```
multiplicative-And on F_k_idx with right_only = {i_b}:
  LEFT  : pair (left_phi = NNF(A))    vs  (i_a ↦ NNF(¬A))
  RIGHT : pair (right_theta = NNF(B)) vs  (i_b ↦ NNF(¬B))
```

#### close_and_elim_l(of)
F_k = A. ¬F_of_nnf = NNF(¬A) ∨ NNF(¬B) at i_of.

```
emit Or(i_of)                  -- ts.seq[i_of] := NNF(¬A); push NNF(¬B)
emit_axiom_decomp(F_k_idx, i_of)
```

#### close_and_elim_r(of)
F_k = B. ¬F_of_nnf at i_of.

```
emit Or(i_of)                  -- ts.seq[i_of] := NNF(¬A); push NNF(¬B); negB_idx = end
emit_axiom_decomp(F_k_idx, negB_idx)
```

#### close_or_intro_l(a, b_formula)
F_k = A ∨ B (where A is derived = a, B is just a formula). i_a at the
negation of a.

```
emit Or(F_k_idx)               -- ts.seq[F_k_idx] := NNF(A); push NNF(B)
emit_axiom_decomp(F_k_idx, i_a)
```

#### close_or_intro_r(a_formula, b)
Symmetric.

#### close_or_elim(or_formula, ac, bc)
F_k = C. `¬F_or_nnf = NNF(¬A) ∧ NNF(¬B)` at i_or.
`¬F_ac_nnf = NNF(A) ∧ NNF(¬C)` at i_ac. `¬F_bc_nnf = NNF(B) ∧ NNF(¬C)`
at i_bc.

This is the only flat step that requires *Contraction* (or the equivalent
Weakening trick) before its multiplicative split: F_k must appear on
both subgoals of the outer And on i_or, but multiplicative-And routes each
non-principal entry to exactly one side.

```
emit Weakening(NNF(C))         -- duplicate F_k at end (current implementation;
                                   morally a Contraction-prep)
F_k_dup_idx := end
multiplicative-And on i_or with right_only = {i_bc, F_k_dup_idx}:
  LEFT  : pair NNF(¬A) (left_phi)     with NNF(A) inside i_ac (multiplicative-And inner step)
  RIGHT : pair NNF(¬B) (right_theta)  with NNF(B) inside i_bc (multiplicative-And inner step)
  inside each: pair NNF(¬C) inside i_ac/bc with F_k or F_k_dup
```

#### close_iff_intro(ab, ba)
F_k_nnf = (NNF(¬A)∨NNF(B)) ∧ (NNF(A)∨NNF(¬B))   ← from §1's Iff rule.

`¬F_ab_nnf = NNF(A) ∧ NNF(¬B)` at i_ab.
`¬F_ba_nnf = NNF(B) ∧ NNF(¬A)` at i_ba.

```
multiplicative-And on F_k_idx with right_only = {i_ba}:
  LEFT  : F_k_idx ↦ left_phi = (NNF(¬A) ∨ NNF(B));  i_ab keeps NNF(A) ∧ NNF(¬B).
            emit Or(left_phi_idx) → split into NNF(¬A) and NNF(B)
            multiplicative-And on i_ab with right_only = {idx_of(NNF(B))}:
              LEFT  : pair NNF(A) (and's left_phi) with NNF(¬A)
              RIGHT : pair NNF(¬B) (and's right_theta) with NNF(B)
  RIGHT : F_k_idx ↦ right_theta = (NNF(A) ∨ NNF(¬B));  i_ba keeps NNF(B) ∧ NNF(¬A).
            emit Or(right_theta_idx) → split into NNF(A) and NNF(¬B)
            multiplicative-And on i_ba with right_only = {idx_of(NNF(¬B))}:
              LEFT  : pair NNF(B) (and's left_phi) with NNF(¬B)              ⚠  BUG #1 site
              RIGHT : pair NNF(¬A) (and's right_theta) with NNF(A)           ⚠  BUG #1 site
```

**The current C++ code at line 968-986 incorrectly assumes the right_theta
of F_k is `(NNF(¬B) ∨ NNF(A))` — i.e., it names `psi.left = negB` and
`psi.right = A_nnf`. With the actual NNF being `(NNF(A) ∨ NNF(¬B))`,
this swaps the roles and the inner emit_axiom_decomp pairs `B` with `A`
and `¬A` with `¬B`, neither of which is a dual (unless A = B by coincidence).**
This bug accounts for the bulk of the 19 "atomic literals not dual"
rejections. See §6 bug class #1.

#### close_iff_elim_l(iff, a)
F_k = B. `¬F_iff_nnf = (NNF(A) ∧ NNF(¬B)) ∨ (NNF(¬A) ∧ NNF(B))` at i_iff.
`¬F_a_nnf = NNF(¬A)` at i_a.

```
emit Or(i_iff)                 -- ts.seq[i_iff] := NNF(A) ∧ NNF(¬B); push (NNF(¬A) ∧ NNF(B))
multiplicative-And on i_iff with right_only = {F_k_idx}:
  LEFT  : pair NNF(A) (left_phi)   with NNF(¬A) at i_a
  RIGHT : pair NNF(¬B) (right_theta) with NNF(B) at F_k_idx
```

#### close_iff_elim_r(iff, b)
Symmetric to elim_l, but acts on the *appended* `(NNF(¬A) ∧ NNF(B))`.

#### close_exists_intro(body, witness)
F_k_nnf = ∃x.NNF(body). i_body = NNF(¬body).

```
ts.seq[F_k_idx] := body_nnf    -- the ts.seq's record of F_k_nnf was the cut formula;
                                   we relabel it as the body for the next step
emit Exists(principal=F_k_idx, witness=witness_lkr)
emit_axiom_decomp(F_k_idx, i_body)
```

(Note: the current implementation overwrites `ts.seq[F_k_idx]` BEFORE
emitting the Exists. This is suspect — see bug class #4 discussion.)

#### close_excluded_middle (LEM as a derived rule)
F_k = A ∨ ¬A (where A is the let-bound formula; F_k_nnf = NNF(A) ∨ NNF(¬A)
which is the dual pair).

```
emit Or(F_k_idx)               -- ts.seq[F_k_idx] := NNF(A); push NNF(¬A)
emit_axiom_decomp(F_k_idx, psi_idx)
```

#### close_bottom_elim(bot)
`bot` is required to be a NotElim step — i.e., a "structural ⊥" derived
from contradictory premises. Find its `negation` and `formula` operands
in the ND stream; their negations live at i_neg, i_pos.

```
emit_axiom_decomp(i_neg, i_pos)
```

(F_k itself is the "target_formula" of bottom_elim — semantically, the
sequent already contains `¬F_k_nnf` somewhere, but bottom_elim closes
by classical absurdity rather than by mentioning F_k.)

## 5. The structural-decomposition schema (`emit_axiom_decomp`)

`emit_axiom_decomp(a_idx, b_idx)` is the only primitive that *closes* a
goal by structural recursion through dual NNF formulas. **Precondition:**
`ts.seq[a_idx]` and `ts.seq[b_idx]` are NNF formulas with `a ⊥ b`
(i.e., NNF(¬a) = b structurally).

By induction on the structure of `a`:

- **Atomic literal vs atomic literal.** Emit `AxiomLit(a_idx, b_idx)`.
  Precondition guarantees they are the same atom in opposite polarity.
- **Top literal `¬⊥` on either side.** Emit `One(idx)`. Provable by §11 One.
- **`a = φ ∨ ψ`, `b = NNF(¬φ) ∧ NNF(¬ψ)`.**
  ```
  emit Or(a_idx)                       -- ts.seq[a_idx] := φ; push ψ
  multiplicative-And on b_idx with right_only = {ψ_idx}:
    LEFT  : recurse(remap(a_idx), left_phi)         -- pair φ vs NNF(¬φ)
    RIGHT : recurse(remap(ψ_idx), right_theta)       -- pair ψ vs NNF(¬ψ)
  ```
- **`a = φ ∧ ψ`, `b = NNF(¬φ) ∨ NNF(¬ψ)`.** Swap roles; recurse with `(b, a)`.
- **`a = ∀x.φ`, `b = ∃x.NNF(¬φ)`.**
  ```
  allocate fresh eigen v
  emit Forall(principal=a_idx, eigen=v)            -- ts.seq[a_idx] := φ[x:=v]
  emit Exists(principal=b_idx, witness=TermRef(↑Forall.idx))
                                                    -- ts.seq[b_idx] := NNF(¬φ)[x:=v]
  recurse(a_idx, b_idx)
  ```
- **`a = ∃x.φ`, `b = ∀x.NNF(¬φ)`.** Swap roles; recurse with `(b, a)`.

Any other shape pair is a precondition violation.

## 6. Identified bug classes (concrete)

### Bug class #1 — close_iff_intro RIGHT-branch variable naming
`close_iff_intro` reads the right conjunct of `NNF(F_k)` as if it were
`(¬B ∨ A)` (matching its inline comment). The actual NNF is `(A ∨ ¬B)`.
The variables `negB`/`A_nnf` are swapped from their intended roles, so
the inner `emit_axiom_decomp` call pairs `(B, A)` and `(¬A, ¬B)` — only
dual when A ≡ B. Concrete failure: `eq_refl` h5 = iff_intro h2, h4 where
`h2_concl = h4_concl = elem(z, x) → elem(z, x)`, the iff's two sides happen
to be equal so the wrong pairing yields `(elem, elem)` and `(¬elem, ¬elem)`
— both same-polarity pairs of the same atom → "atomic literals not dual."

This is the single largest bug (≈19 of 29 rejections), as iff_intro is
used wherever extensionality patterns produce `eq(...)` via `iff_elim`.

### Bug class #2 — emit_axiom_decomp called with non-dual formulas
The remaining `axiom_decomp` errors at lines 680 (`a is ∨ but b is not ∧`)
and 749 (`a is ∃ but b is not ∀`) indicate the precondition `a ⊥ b` was
not satisfied by the caller. Inspection of `pair_eq_b` and `compose_assoc`
shows these proofs rely on `iff_intro`/`iff_elim` patterns whose translator
emissions pair entries that are *almost* dual but for the close_iff_intro
RIGHT-branch swap propagating through subsequent ops. These are believed
to share root cause with #1; verify after #1 is fixed.

### Bug class #3 — multiplicative-And partition collisions
`close_or_elim` (1 rejection: `pair_first_eq`) emits `Weakening(F_k)` to
duplicate the F_k entry, then partitions both copies across LEFT/RIGHT.
But the multiplicative-And split also has to route every *other* in-scope
entry (notably the negations of earlier cut-ins, indexed by
`step_to_neg_idx`). The `right_only` set passed to `build_and_split`
includes only `{i_bc, F_k_dup_idx}`. If an `i_ac` happens to equal the
F_k_dup_idx or any other index in right_only, or if i_ac is needed on the
RIGHT side for an inner reference, the partition fails: "index N is not in
the LEFT subgoal partition."

Root cause: the per-rule `close_X` decides routing for a *fixed handful* of
"interesting" entries, but the multiplicative-And split silently routes
*everything else* to LEFT. Any entry that LEFT references via
`split.left_at(...)` must be in left_partition; any entry RIGHT references
must NOT be (must be in `right_only`). The current API requires each rule
to know, by introspection, which `step_to_neg_idx` entries each side will
need — an obligation the rules don't reliably discharge.

### Bug class #4 — ts.seq mirror going stale
The translator maintains `ts.seq` to mirror the verifier's current sequent.
After a multiplicative-And split, `ts.seq` is replaced with `split.left_seq`
or `split.right_seq` — an explicit re-snapshot. But `step_to_neg_idx`
values were computed before the split and now refer to indices in the
*unsplit* sequent. After the split, these indices may:
 (a) point to the wrong entry in left_seq/right_seq (because split's
     `left_remap`/`right_remap` translate them, but only if explicitly
     looked up via `split.left_at()`/`split.right_at()`);
 (b) point past the end of the new seq;
 (c) silently still resolve to a valid-looking entry that is not the one
     the proof intended.

This invariant violation is the *vehicle* by which #2 and #3 manifest. The
current code addresses it by per-rule explicit `split.left_at()` / `split.right_at()`
calls, but only for the entries each rule explicitly knows about. Cross-cut
dependencies (e.g., a flat step in a deeper block whose `step_to_neg_idx`
points into an outer cut's RIGHT subgoal) are not protected.

### Bug class #5 — test-harness loading order (NOT a translator bug)
The 6 `use: unknown axiom/theorem 'X'` rejections come from
`test/nd_to_lkr_corpus_test.cpp`: the corpus test calls `try_translate_one`
on each parsed proof in source order, but the translator's
`compute_flat_formula` resolves Use's name against `ctx` *at translate
time*. If a proof references an earlier-in-file claim that hasn't been
registered yet (because we're translating before executing), Use fails.
The harness's existing `for (parsed : pr.proofs) rt.execute_proof(parsed);`
loop ensures registration, but only AFTER it runs to completion — and it
silently swallows errors from individual proofs, so a proof that depends
on a later proof can still hit unresolved Use. Fix at the harness level,
not the translator.

## 7. What the redesign should make impossible

A redesign of the translator should, by construction, eliminate:

1. **Bug class #1 by design.** No per-rule code should pattern-match the
   *child positions* of an Iff's NNF expansion. The translator should
   either work on a richer IR that names the iff's two conjuncts
   semantically, or recurse generically over NNF structure rather than
   inlining iff-specific shapes.

2. **Bug class #4 by design.** The `ts.seq + step_to_neg_idx` shadow
   should not be the load-bearing source of truth. Either:
   - replace it with an algebraic representation (e.g., named entries
     keyed by their *contents* or by stable abstract identifiers, with
     a "where am I now?" lookup at use time), or
   - structure the translation as a tree-recursion that does not need
     a flat shadow at all (each LEFT branch builds its own local
     sequent representation; the parent's sequent is restored on return
     by *replaying* a snapshot, not by patching indices).

3. **Bug class #3 by design.** Multiplicative-And partition decisions
   should be derivable from the *set of indices each subgoal needs to
   reference*, not from an opaque `right_only` parameter that the rule
   author manually maintains. A central "split planner" that takes the
   LEFT-side and RIGHT-side reference sets and computes the partition
   automatically would close this class.

4. **Bug class #2** is downstream of #1 and #4 and falls out for free.

(Bug class #5 is fixed in the harness, independently of the translator
design.)

## 8. Open questions for the redesign

- **Is Cut the right primitive at every flat step?** The current cut-spine
  pattern is uniform but produces deep proof trees (one Cut per ND step).
  An alternative: only Cut when the derived formula is actually needed by
  a later step; otherwise use direct structural moves. Trade-off: less
  proof-output bloat vs. more bookkeeping in the translator.

- **Should `emit_axiom_decomp` be a separate IR-level pass?** Currently
  it's called inline by every close_X. Lifting it to a post-pass that
  consumes a "close this goal by dual-decomposition of these two entries"
  marker would let close_X be purely declarative.

- **Eigenvariable allocation: builder vs. translator-local?** Eigens are
  allocated via `FormulaBuilder::enter_scope()`, which mutates a global
  scope counter. This couples the translator to the builder's scope
  state. A translator-local fresh-name supply would decouple them.

- **Should the block tree be the primary IR?** `decompose_blocks` already
  produces a tree; the translation could be expressed as a structural
  fold over it, eliminating the linear ND op stream from the translator's
  active concerns entirely.
