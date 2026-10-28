# Stage 2 Phase 7: eliminations as demands

> **Status.** Draft 2026-10-27. Supersedes the uncommitted drafts
> `SCOPE_AND_BOTTOM_DESIGN.md` and `../lkr_compress/LKR_COMPRESS_DESIGN.md`.
> Refines [CUT_MINIMAL_DESIGN.md] §1.2–§1.4, §5, §6 and
> [DEMAND_THROUGH_COMBINING.md] §1. The LKR verifier is unchanged; every
> change is in Stage 2. Math first: spec here, tests (RED), then impl.

Notation: X' is NNF(X), X̄ is NNF(¬X). For a sequent S, S[p] is its entry
at position p. τ(S, s, T, π) translates ND step s into LKR ops that close
S, where T is the target and π the demand path (§1.3–§1.4).

## 0. Problem statement

CUT_MINIMAL §1.5 owes completeness: every input that passes the input
gate translates. CUT_MINIMAL §1.2 states the intended cut census: cuts at
combining eliminations, on the major premise only. A bug-catcher run on
schema-unfolded isa2fol proofs located the gaps below. G4 to G6 were found
by case analysis of the rules, not by inputs.

- **G1. ∀-detour.** `forall_elim` of a `forall_intro` result. The INSTANCE
  path (`dispatcher.cpp:587–607`) expects ∀x.φ at the target, but under
  DEMAND §1.1 the target already holds φ[t]'.
- **G2. Eigenvariables.** A FORALL or EXISTS_ELIM block's LKR eigenvariable
  is its ND variable, a de Bruijn level, so sibling blocks share it. Trace
  formulas enter the shadow verbatim. A block translated inside a sibling
  at the same level fails the freshness check, and under INSTANCE the
  body's formulas still mention the level instead of t.
- **G3. ⊥ results.** NotElim has no case as a step (variant 14 falls
  through, `dispatcher.cpp:629`), and the closers accept only a NotElim as
  `bottom` (`dispatcher.cpp:773`).
- **G4. Closers under demand.** NotIntro and ClassicalAbsurd drop the
  demand path (`dispatcher.cpp:462–474`).
- **G5. Re-quantifying ∃E closer.** `ProofStack::exists_intro` without a
  witness concludes C when the witness v does not occur in the body's C,
  and ∃x.C[v↦x] when it does. Stage 2 assumes C.
- **G6. Formula-level availability.** `ProofStack::is_derived` is keyed by
  formula, and closing a scope erases only formulas whose dependencies
  include it. A step inside a closed block therefore stays referenceable
  when its formula does not depend on the block. The referenced step's own
  derivation may still use the closed block's assumption (when the same
  formula was also derived elsewhere with fewer dependencies) or its
  variable (as a vacuous ∀E term or ∃I witness). Recursive descent then
  meets a hypothesis or binder that was never bound.

**Size.** The combining elims cut on every operand, not only the major
premise, and close each operand against its dual. The major premise is
translated against the target NNF(major); when it is a hypothesis, that is
one more identity. Per `implies_elim(h: A→B, a: A)` with h a hypothesis:
2 Cuts and identities of sizes |A→B|, |A|, |B| (each Θ(size) ops after
η-expansion). The Gentzen image of the same step, →L on h, has no cut and
one identity of size |B|, at the end of the elimination track.

## 1. Definitions

### 1.1 Blocks, hypotheses, binders

`ProofIndex` derives these once from the block tree (§6.1):

- block(s): the block whose body holds s. An opener belongs to its own
  block; a closer belongs to the parent of the block it closes.
- **Hypothesis steps**: Assume and ExistsElim openers. **Binder steps**:
  Fix and ExistsElim openers. lvl(b) = trace.term_env[b].
- scope(s): the binder steps of the blocks enclosing s, including s itself
  when s is an ExistsElim opener (its formula φ[v] mentions v).
- **Operand position** p(C, X) of operand X of consumer C: B when C is the
  closer of B and X = target(B); parent(B) when C is the ExistsElim opener
  of B and X its `formula`; block(C) otherwise.
- **FH(s)**, the free hypotheses and binders of s's derivation: {s} for a
  hypothesis step; for a closer of B, FH(target(B)) minus B's hypothesis
  or binder (for the ∃E closer, also ∪ FH(opener.formula)); for ∀E and
  ∃I(witness), ∪ FH(operands) ∪ {binder of the term}; otherwise
  ∪ FH(operands). Let payloads are not operands.

### 1.2 Term environment and fresh eigenvariables

σ maps binder steps to TermBindings {lkr_ref, value}: the TermRef of the
LKR Forall that bound the value, and the value. σ is part of the sequent
state, so each branch has its own.

Reading a trace formula: ⟦s⟧σ = step_env[s][lvl(b) := σ(b).value for b ∈
scope(s) bound in σ], a simultaneous substitution of fixed variables.

**Rule S0.** No emitter reads `trace.step_env` directly; every formula
read goes through ⟦·⟧σ (`FormulaReader`).

**Eigenvariables.** Every emitted Forall uses a variable fresh from the
translation's FormulaBuilder counter, which starts above
`trace.next_free_var`. σ values are therefore LKR variables, disjoint from
every ND level, and composing single-variable substitutions computes ⟦·⟧σ
exactly.

**Lemma S1 (freshness).** Every Forall's eigenvariable occurs in no
sequent entry. *Proof.* The counter never repeats a variable, and entries
contain only ND levels and previously allocated variables. □

Static per-binder eigenvariables (the earlier draft) need a freshness
argument that fails under re-entry of a block (§2.4); fresh variables need
none.

### 1.3 Targets

T is `pos p` (S[p] holds the NNF of the demanded result) or `none` (the
demanded result is ⊥, whose NNF 0 is the unit of ∨, so it needs no
position). On entry to τ: a target whose entry is 0 becomes none, and a
target whose entry is 1 (¬⊥) is closed by `One` without translating s.

### 1.4 Demands

Every elimination is a demand on its major premise:

| ND step | demand pushed onto the major premise |
|---|---|
| `and_elim_l/r(of)` | AndL / AndR |
| `forall_elim(f, t)` | Instance(σ(t)) |
| `implies_elim(impl, ant)` | Modus(ant) |
| `iff_elim_l(iff, a)` / `_r(iff, b)` | IffModus(a, L) / IffModus(b, R) |
| `not_elim(neg, formula)` | Refute(formula) |
| `or_elim(or, ac, bc)` | Cases(ac, bc) |
| `exists_intro(body)` closing ∃E block B | Witness(B), on B's opener.formula |
| `double_neg_elim(of)` | nothing: NNF(¬¬A) = A' |

A **minor** is a step or a hypothesis: Modus, IffModus and Refute carry
Step(m) or Hyp(h). The demanded result apply(F, π) peels F along π:
Instance → φ[t]; AndL/R → a conjunct; Modus, IffModus → the consequent;
Refute → ⊥ (and ends π); Cases(ac, bc) → C; Witness(B) → B's result.

**Contract (extends DEMAND §1.1).** On entry to τ(S, s, T, π):
T = pos p with S[p] = (apply(⟦s⟧σ, π))', or T = none with
apply(⟦s⟧σ, π) = ⊥. The emitted ops close S.

A path is **step-free** when it carries no Step minor, Cases or Witness,
and **projection-only** when it has only Instance, AndL and AndR.
Duplicating a step-free path into two branches duplicates no translation.

### 1.5 Dual slots

The sequent maps each bound hypothesis h to a slot {pos | none,
pending}: S[pos] is h̄ with `pending` applied, and none means h̄ = 0.
`pending` is empty except for closers (§2.3). Hypotheses are assumption
and ∃E-opener steps, projections of split hypotheses (§2.8), shared steps
(§5.2), and local hypotheses introduced by Cases, EM and let-cuts.

## 2. The translation

### 2.1 Dispatch

τ(S, s, T, π), after normalizing T:

1. s is bound as a hypothesis in S: the leaf rule (§2.4).
2. s is an elimination: push its demand (§1.4) and translate the major
   premise. OrElim pushes Cases only under a step-free π; otherwise
   let-cut (§2.5).
3. s is an introduction: the right rule under ε, the redex rule when the
   head of π is s's own elimination (§2.2), otherwise let-cut.
4. s is a closer: §2.3. Use/SchemaInst (tests that bypass Stage 1): Cut on
   the lemma, CloseByLemma on the left, the leaf rule on the right.

### 2.2 Introductions

Right rules (π = ε), unchanged except ForallIntro's fresh eigenvariable:
AndIntro and IffIntro split T (§2.6); OrIntroL/R, ImpliesIntro use Or;
ForallIntro uses Forall{T, fresh u} and σ[fix] := u; ExistsIntro uses
Exists{T, σ(t)}; ExcludedMiddle and Peirce are fixed skeletons, Peirce now
in any context.

Redexes (the head of π is s's own elimination; π' is π's tail):

| producer | head | rule |
|---|---|---|
| AndIntro(a, b) | AndL / AndR | τ(a or b, T, π') |
| ForallIntro(body) | Instance(t) | σ[fix] := t; enter; τ(body, T, π') |
| ImpliesIntro(c) | Modus(m) | bind(assume, m); enter; τ(c, T, π') |
| NotIntro(⊥) | Refute(m) | bind(assume, m); enter; τ(⊥-step, none, ε) |
| IffIntro(ab, ba) | IffModus(m, L/R) | τ(ab or ba, T, Modus(m) :: π') |
| OrIntroL(a) / R(b) | Cases(ac, bc) | τ(ac or bc, T, Modus(Step a or b) :: π') |
| ExistsIntro(b, t) | Witness(B) | σ[ee] := σ(t); bind(ee, Step b); cont(B, T, π') |
| ExcludedMiddle(A∨¬A) | Cases(ac, bc) | Cut(A'): left h¬ = A', τ(bc, T, Modus(h¬) :: π'); right h = Ā, τ(ac, T, Modus(h) :: π') |

- **bind(h, Step m)**: Cut(⟦h⟧σ'). LEFT: τ(m, appended, ε). RIGHT:
  slot(h) := appended. This is a let-cut on the minor.
- **bind(h, Hyp k)**: slot(h) := slot(k). No op.
- **enter(B)**: the block-entry hook (share mode, §5.2).
- **cont(B, T, π)**: enter(B), then τ(target(B), T, π), or, when B's
  closer re-quantifies (G5), the ExistsIntro rule for body = target(B)
  with witness σ(ee).

**Lemma S2 (∀-detour, G1).** Prawitz's ∀E(∀I_v(Π), t) ▷ Π[t/v]. Under
σ' = σ[fix ↦ t], ⟦s⟧σ' = ⟦s⟧σ[v := t] for every step s of the block, so
the recursion translates Π[t/v]. v is not free in Π's open hypotheses, and
by S1 no eigenvariable equals t. The target holds (apply(ψ[t], π'))' as
the contract requires. No Cut.

### 2.3 Closers

| closer | π | rule |
|---|---|---|
| ImpliesIntro | ε | right rule: Or{T}; slot(assume) := T; enter; τ(c, appended, ε) |
| NotIntro, ClassicalAbsurd | ε | slot(assume) := T (none when T is none); enter; τ(⊥-step, none, ε) |
| NotIntro | Refute(m) | redex (§2.2) |
| NotIntro, ClassicalAbsurd | projection-only, ≠ ε | slot(assume) := {T, pending π}; enter; τ(⊥-step, none, ε) |
| NotIntro, ClassicalAbsurd | otherwise | let-cut |
| BottomElim | any | τ(⊥-step, none, ε) |

**Lemma D1.** If slot(h) has pending π ≠ ε (projection-only), every
reference to h arrives with ε or Refute(m) as its normalized path.
*Proof.* Projections apply only to a ∀ or ∧ head modulo ¬¬. For
ClassicalAbsurd, h = ¬R and π applies to R, so R is ∀ or ∧ modulo ¬¬ and
h is a single negation of it modulo ¬¬. The only elimination of a negation
is Refute. NotIntro is the same with h = A, R = ¬A, A ≡ ¬X. □

The pending leaf rule (§2.4) is Prawitz's permutation of ⊥_c and ¬I over
an elimination. It duplicates π into every use of h, so it requires a
projection-only π (§2.7).

### 2.4 Leaves: left rules on the dual

leaf(S, h, T, π) with slot(h) = {d, pending q}:

- q = ε: apply(S, d, π, T) below.
- q ≠ ε, π = ε: apply(S, T, q, pos d). T holds h' = NNF(¬R), the dual of
  the closer's result R, and d holds (apply(R, q))'.
- q ≠ ε, π = Refute(m): τ(S, m, pos d, q).
- slot none: π = ε means T holds 1 (closed on entry); π = Refute(m) means
  τ(S, m, none, ε).

apply(S, d, π, T), where S[d] is F̄ for the formula F that π eliminates:

| head of π | S[d] | ops | then |
|---|---|---|---|
| ε, T = pos p | F̄ | identity(p, d) | |
| ε, T = none | 1 | One{d} | |
| Instance(t) | ∃x.φ̄ | Exists{d, t} | S[d] = φ̄[t] |
| AndL / AndR | Ā ∨ B̄ | Or{d} | d := Ā / appended B̄ |
| Modus(m) | A' ∧ B̄ | And{d} | LEFT minor(m, A'); RIGHT B̄ |
| IffModus(m, L) | (A'∧B̄) ∨ (B'∧Ā) | Or{d}, And on the 1st clause | LEFT minor(m, A'); RIGHT B̄ |
| IffModus(m, R) | same | Or{d}, And on the 2nd clause | LEFT minor(m, B'); RIGHT Ā |
| Refute(m) | A' | | minor(m, d), T = none |
| Cases(ac, bc) | Ā ∧ B̄ | And{d}, T to both | LEFT τ(ac, T, Modus(h_A) :: π'); RIGHT τ(bc, T, Modus(h_B) :: π') |
| Witness(B) | ∀x.φ̄ | Forall{d, fresh u} | σ[ee] := u; slot(ee) := d; cont(B, T, π') |

minor(Step m, q) = τ(S, m, pos q, ε); minor(Hyp k, q) = identity(q,
slot(k)). h_A and h_B are local hypotheses at the And's appended
positions.

**Copy rule.** The left rules rewrite S[d] in place. If d is among the
positions the rest of the task needs (§2.6), apply them to a Duplicate of
d.

**Re-entry.** A Witness continuation carries π' into B's body, and π' may
hold minors of later steps that reach B's closer again. B is then entered
twice on one branch: S1 keeps it sound, and the inner entry shadows σ(ee)
and slot(ee) only on its own branch.

### 2.5 Let-cut

let_cut(S, s, T, π): Cut(⟦s⟧σ). LEFT: τ(s, appended, ε). RIGHT: a local
hypothesis with its slot at the appended s̄; apply(·, π, T). The cut
formula is the result of a non-normal point (an intro or ⊥_c conclusion
consumed by an elimination it does not match), and the cut is its LK image.

### 2.6 Context routing at multiplicative splits

LKR's And is multiplicative: each non-principal entry goes to one premise.
For each split the translator knows both premise tasks, and **needs(task)**
is the set of positions the task can touch: its target, the slots of
FH(s) ∪ FH(π) (FH(π) collects the minors' FH, Hyp minors, Cases branches
and Witness continuations), and for a leaf task its dual. The split
duplicates the entries both premises need, sends each needed entry to its
premise, and sends all other entries to RIGHT, which keeps
`left_partition` minimal. Every And in Stage 2 goes through this one rule:
AndIntro, IffIntro, the Modus, IffModus and Cases left rules, the
identity's ∨/∧ case, and Peirce.

**Lemma R.** Translating a task binds or reads only hypotheses in its FH
or ones it binds itself, so every referenced slot survives routing. A
violation is reported as "hypothesis has no slot in this branch" (a
translator bug).

### 2.7 Principle P

Stage 2 reduces a non-normal point in place when the reduction is local and
duplicates no translation by construction; otherwise it emits a let-cut.
Every rule above is an instance:

- Reduced: ∀ (substitute a term), ∧ (select), ∨ at OrIntro (select a
  case), → or ¬ with a Hyp minor (alias), ⊥_c and ¬I under projection-only
  paths (pending), Witness (single continuation), Cases with a step-free
  tail (the tail is duplicated, no translation is).
- Let-cut: → and ¬ with a Step minor (substituting the minor's derivation
  duplicates it once per use of the assumption), ∃ at ExistsIntro (the
  instance), Cases with a step-carrying tail, ⊥_c and ¬I under other paths,
  Peirce under Modus.

### 2.8 Projected hypotheses

The left rules of §2.4 rewrite a copy of the dual at every use. For a
conjunction H that is used only through its conjuncts this repeats work.
H̄ = Ā ∨ B̄ modulo ¬¬, so a use of a conjunct at depth k re-applies k Ors to
a fresh copy of H̄.

∨ is invertible in one-sided LK, so applying Or to H̄ loses nothing. When
every reachable reference to H is `and_elim_l`, `and_elim_r` or
`double_neg_elim`, H's block entry (before the share-mode cuts) applies Or
to H̄ once. Each projection step is bound to its own part, recursively for
parts that are themselves only projected. This is the asynchronous phase of
focusing, restricted to the ∨s the proof actually projects.

- `ProofIndex` computes the parts as `Component`s: the steps that denote a
  part (a projection and its ¬¬-aliases) and its left and right halves.
- The projection steps become hypotheses. FH(s) = {s}, the closer of H's
  block binds them, and I-4 places them in H's block.
- Routing (§2.6) then duplicates the conjuncts a premise needs, not H.
- Projections are never shared (§5.2). Let-binding one would cut on its
  formula and close a full identity of the conjunct.
- An H that is also used whole (as a minor, or against a target) is not
  split; its projections peel as in §2.4.
- If H̄'s position is aliased by another hypothesis' slot (bind of a
  Hyp minor), the split applies to a Duplicate of it.

Stage 1's facts prelude H = ((F₁ ∧ F₂) ∧ …) ∧ Fₙ is only projected. Without
the split, a use of fact F_k costs n−k Ors. With it, all uses together cost
n−1 Ors per entry of H's block.

## 3. Coverage

Rows: producer. Columns: head of the normalized path. "type" means ND
typing excludes the cell; ¬¬ normalization leaves NotIntro as the only
introduction that can meet a foreign head.

| producer | ε | own elimination | other heads | T = none |
|---|---|---|---|---|
| AndIntro | split | AndL/R: select | type | via select |
| OrIntroL/R | Or | Cases: select | type | via select |
| ImpliesIntro | Or + slot | Modus: bind | type | via Modus |
| IffIntro | split | IffModus: forward | type | via forward |
| ForallIntro | Forall | Instance: σ | type | via Instance |
| ExistsIntro(t) | Exists | Witness: σ + bind | type | via Witness |
| ExcludedMiddle | Or + identity | Cases: Cut(A') | type | via Cases |
| Peirce | skeleton | Modus: let-cut | type | via let-cut |
| NotIntro | slot | Refute: bind | pending or let-cut | ⊥ via Refute |
| ClassicalAbsurd | slot | | pending or let-cut | slot none |
| BottomElim | ⊥ | | ⊥ (path ignored) | ⊥ |
| eliminations | push | push | push | push |
| ∃E closer | push Witness | push | push | push |
| Assume, ExistsElim, shared | leaf | leaf | leaf | leaf |
| Use, SchemaInst | Cut + leaf | Cut + leaf | Cut + leaf | Cut + leaf |
| Let, Fix, Qed | not recursion targets | | | |
| EqSym, IotaElim | rejected at the input gate (I-1, I-2) | | | |

Every left-rule row of §2.4 matches its head to the dual's shape by
typing: the eliminated formula's main connective (modulo ¬¬) fixes F̄'s.

## 4. Input contract I-4 (G6)

**I-4 (lexical availability).** For every consumer C reachable from Qed
and every operand X of C, each hypothesis and binder in FH(X) belongs to a
block that encloses p(C, X).

Under I-4 every slot and σ binding the translation reads is bound on the
branch. A translation context always contains the lexical chain of the
step being translated, since recursion enters a block only through its
closer. I-4 accepts a step referenced from outside its closed block when
its derivation needs nothing from that block, for example a fact chain or
a lemma use. It rejects exactly G6's two cases, which ProofIndex reports
as "I-4 violation". Lemma: under I-4, ⟦s⟧σ meets no unbound binder's
level in step_env[s].

Normalizing a G6 input to I-4 is an ND→ND pass and is out of scope here:
replay `ProofStack`'s per-formula dependencies to relink each reference to
a derivation valid at C, and replace vacuous out-of-scope terms. This
phase rejects such input at the boundary instead of failing inside the
recursion.

## 5. Size

### 5.1 Census (unshared mode)

Cuts are emitted only by bind with a Step minor (→, ¬ and ∃ redexes), by
let-cuts (§2.5), by EM under Cases, and by Use/SchemaInst. A proof without
intro–elimination pairs, ⊥_c or ¬I under foreign eliminations, EM case
splits, or lemma uses translates with **no cut**. CUT_MINIMAL §1.2's
census was "one cut per combining elimination".

Identities occur at the end of a leaf's path against a
target (the minimal formula of the elimination track), in the EM and
Peirce skeletons, for Hyp minors at a hypothesis, and for pending
references with ε paths. With HEAD's rules, `implies_elim(h: A→B, a)`
with h a hypothesis costs 2 Cuts and identities of sizes |A→B|, |A|, |B|.
Here it costs no Cut, one And on a copy of h̄, and an identity of size |B|
only at the track's end. The iff, or, not and exists eliminations change
in the same way.

### 5.2 Share mode

CUT_MINIMAL §1.4 unfolds shared steps: a step reached along N reference
paths is translated N times, O(2^d) in reuse depth d. Share mode
(`Options::share`, off by default) let-binds them instead:

- cut_block(k): the innermost block enclosing p(C, k) for every reachable
  referrer C of k.
- shared(B): the steps k with cut_block(k) = B and at least two reachable
  references counted with multiplicity, excluding hypotheses (including
  §2.8's projections), Use/SchemaInst (already leaves) and Let/Fix.
- enter(B), at each entry of B (OUTER first), for k ∈ shared(B) in program
  order: if ⟦k⟧σ = ⊥, τ(S, k, none, ε) closes B's whole sequent and ends
  B's translation. Otherwise Cut(⟦k⟧σ); LEFT τ(k, appended, ε); RIGHT
  slot(k) := appended.

References to k after the entry are leaves (§2.1 rule 1). If a reference
reaches k where its cut block was not entered, k is simply translated in
place: an I-4-accepted escaped reference, or a derivation translated
outside its lexical blocks. Routing (§2.6) then expands k to k's own FH.

**Lemma L1.** In share mode every reachable step is translated at most
once per entry of its cut block, and every block is entered at most once
per translation of its closer. The translation is linear in the ND program
plus the per-rule peels, splits and identities. *Proof.* Unshared non-leaf
steps have one reference. Step-free tails are the only duplicated paths.
Let-cuts translate s once. Induction from OUTER over blocks. □

## 6. Code architecture

The point of the restructure is that each concept has one owner.

### 6.1 Abstractions

- **`ProofIndex`** (`proof_index.{h,cpp}`, immutable). Built once from the
  program, the trace and the block tree. Answers block(s), the opener,
  closer and target of a block, binder levels, scope(s), FH(s) and the
  free set of a block body, `requantifies(closer)`, `is_bottom`, the
  projection `Component`s of a hypothesis (§2.8), and in share mode
  shared(B). Validates I-4 during construction. Replaces
  `CloserToOpener` and the scattered `trace` lookups.
- **`FormulaReader`** (`formula_reader.{h,cpp}`). ⟦s⟧σ, the only reader of
  `trace.step_env` (Rule S0). Substitutes σ over scope(s) and checks the
  I-4 lemma.
- **`SequentShadow`** (`sequent_shadow.{h,cpp}`, a class). The goal is an
  `lkr_build::Sequent` (src/proof/lkr_build/COMPACT_LKR_DESIGN.md §3),
  whose every rule also emits the matching LKR op, so the shadow cannot
  drift from the verifier. SequentShadow adds slots (HypId → DualSlot) and
  σ (`TermEnv`), draws eigenvariables from the FormulaBuilder, and after
  `and_rule(principal, left_needs, right_needs)` or `cut_rule(formula)`
  (both consume the shadow and return a `Split` of two `Premise`s with
  position remaps) gives each premise the slots whose entries moved to
  it. One `and_rule` replaces the five hand-written splits
  (`emit_and_split_local`, `emit_and_intro`, `emit_iff_intro`, the
  identity, Peirce).
- **`Demand`, `DemandPath`, `Minor`, `Target`, `HypId`** (`demand.h`).
  `DemandPath` is a value type with `head`, `push`, `pop`, `for_each`,
  `step_free`, `projection_only`. `HypId` is a typed id: an ND step
  (assumption, ∃E opener, projection, shared step) or a local hypothesis.
  No strings anywhere.
- **`Dispatcher`** (`dispatcher.{h,cpp}`, `intros.cpp`, `leaves.cpp`). One
  class whose public surface is `translate_proof`. The translation is
  goal-directed: a rule decomposes its goal and schedules work on its
  premises on an explicit agenda (`TranslateWork`, `ExistsIntroWork`,
  `EnterWork`, `LeftRulesWork`), LEFT before RIGHT because LKR ops are in
  preorder. No rule translates a premise by a direct call, so the C++ call
  depth does not grow with the derivation. Members follow §2: `translate`
  (normalization and dispatch, one overloaded `on(op, Task)` per ND op),
  `closer`, `lemma`, `let_cut`, `bind`, `split_projections`, `leaf`, the
  left rules (`run(LeftRulesWork)`, `modus`, `cases`, `minor`, `refute`)
  and routing (`need`).
- **The identity** (`SequentShadow::identity`, implemented by
  `lkr_build::expand_identity` with its own goal stack for the same
  reason). The dispatcher writes to an `lkr_build::OpSink`: `LkrSink`
  expands each identity, `CompactSink` records it as one `Identity`
  instruction (COMPACT_LKR_DESIGN.md).
- **`NDtoLKR`**: `NDtoLKR(ctx, goal, Options = {})` with
  `Options{bool share = false}`. Gates and pass discipline unchanged.
  `NDtoCompactLKR` runs the same translation into a `CompactSink`; its
  output gate verifies the expansion.

### 6.2 Removed

- `intros.h`, `projections.{h,cpp}`: the IntroResult and RecurseDescriptor
  indirections, now Dispatcher members.
- `combining.{h,cpp}`, `structural.{h,cpp}`: descriptor modules that no
  production code calls; only their own tests did.
- `dispatcher::translate_step` (free function) and `dispatcher::Ctx`.
- `emit_contradiction_close`, the three `emit_*_elim_full` emitters,
  `apply_path_and_close`: subsumed by the left rules.

Their unit tests go with them. Their cases move to end-to-end tests
through `NDtoLKR`: OutputGate acceptance by LKRVerifier is the soundness
witness (CUT_MINIMAL §1.5).

### 6.3 Extension points

- A new elimination is a `Demand` variant, one row of left rules
  (`run(LeftRulesWork)`) and one redex row.
- A new ND→ND normalization (G6 relink) slots in before `ProofIndex`.
- The routing (§2.6) and `HypId` let a later pass add hypotheses without
  touching the split rule.
- Linear β-redexes (an assumption used once) can be reduced by
  substitution instead of bind; the decision point is `bind`.

## 7. Tests (RED first)

New `test/nd_to_lkr_demands_test.cpp`. Each case runs NDtoLKR on ND text
and asserts OutputGate acceptance, in both share modes:

- **G1/G2:** the ∀-detour t1, t3 (no Cut in t1's output), sibling-level
  reuse, nested ∀I under two Instances, a Witness level reused by a
  sibling `fix`.
- **G3:** A→⊥ by not_elim, consumed by implies_elim and bottom_elim; assume
  ⊥ then bottom_elim; ⊥ from implies_elim, or_elim, exists_elim and
  iff_elim_l feeding not_intro; classical_absurd concluding ⊥.
- **G4:** classical_absurd concluding ∀x.φ then forall_elim, concluding
  A∧B then and_elim_l, concluding A→B then implies_elim (let-cut);
  not_intro of ¬¬∀x.φ then double_neg_elim and forall_elim.
- **G5:** an ∃E block whose body mentions the witness, under ε and
  consumed by a second exists_elim.
- **G6:** a reference into a closed block that I-4 accepts (a lemma use),
  and one it rejects (a closed block's assumption reached through a
  formula derived twice).
- **Redexes:** each row of §2.2.
- **Census:** modus ponens, or_elim and exists_elim on hypotheses emit no
  Cut, and a normal proof emits no Cut.
- **Share:** a chain of k steps each referenced twice is linear in k in
  share mode and 2^k unshared; a shared ⊥ step closes its block.
- **Projections (§2.8):** uses of a deep conjunct cost O(1) each; through
  ¬¬, of an ∃E witness, of an aliased slot; a hypothesis also used whole
  is not split.
- **Depth:** a 100,000-step chain translates on the default stack.

Existing suites: `nd_to_lkr_test` unchanged. `cut_minimal_dispatcher_test`
and `cut_minimal_demand_through_combining_test` keep their ND proofs and
switch to the pass API.

## 8. Acceptance

1. §7 green; every existing translation test green.
2. `../COMPLETENESS.md` §4.2 rewritten for this dispatcher (it still
   describes the deleted `cut_spine.cpp`).
3. Bug-catcher: re-run the isa2fol sample. Rejections other than I-4 and
   resource limits are bugs to locate. I-4 rejections are reported apart:
   they are §4's contract boundary, not translator bugs.
