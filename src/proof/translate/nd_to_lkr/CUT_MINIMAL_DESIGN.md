# Stage 2: cut-minimal NDtoLKR — design doc

> **Status.** Phase 0 spec, user-approved 2026-05-24. Four design
> decisions baked in: (1) file layout split by phase, (2) classical-op
> split (ExcludedMiddle/Peirce → Phase 1, DoubleNegElim → Phase 2,
> ClassicalAbsurd → Phase 4), (3) NotElim policy (α): no-emit, always,
> (4) result-visibility invariant binds across Phases 1–3 (see §1.4).
> Phase 1 (introductions) detail inline; Phases 2–5 stubbed and filled
> in as we reach them.
>
> **2026-10-27:** Phase 7 ([ELIMINATION_DEMANDS_DESIGN.md]) supersedes the
> combining-elim, closer and ForallIntro-under-INSTANCE parts of §1.2–§1.4,
> §5.1.7, §6.2–§6.3 and §7.1: every elimination is a demand, cuts are
> emitted only at non-normal points, and eigenvariables are fresh per
> Forall.

## 1. Theorem and obligation

### 1.1 Controlling theorem (Prawitz ND↔LK correspondence)

For classical first-order natural deduction and the one-sided right-handed
classical sequent calculus LK (= LKR, paper-pure §11 + §15 Cut), there is
a translation function

```
  τ : ND-derivation(Γ ⊢ φ)  ⟶  LK-derivation(⊢ Γ̄, φ_nnf)
```

(where `Γ̄ = { NNF(¬H) : H ∈ Γ }` is the dualisation of the assumption
context into the one-sided right sequent) such that:

- **(Soundness.)** if τ(Π) is a valid LK derivation, then ⊢ Γ̄, φ_nnf is
  classically valid; together with NNF preservation of provability this
  gives Γ ⊢ φ.
- **(Completeness.)** every ND derivation has an LK image under τ.

The translation is defined inductively on the ND derivation tree:

| ND rule family       | LK image                                       |
|----------------------|------------------------------------------------|
| introductions        | corresponding right rule (∧R, ∨R, ∀R, ∃R, …)   |
| projection elims     | structural decomposition of the producer's image|
| combining elims      | Cut on the major premise                       |
| structural (fix, assume, ∃-elim scope, qed) | sequent threading; no logical content |

### 1.2 Cut-minimal claim (what Stage 2 delivers)

τ as defined above introduces Cut **only at combining-elim sites**. The
existing NDtoLKR pass (which is what we are replacing in place) instead
emits one Cut per ND step — a uniform "cut spine" that is correct but
needlessly cut-heavy. Stage 2 reorganises the translation to emit cuts
only where the math actually demands them, namely:

```
  implies_elim   (modus ponens)         → Cut(major = A→B)
  or_elim        (case analysis)        → Cut(major = A∨B)
  exists_elim    (witness elimination)  → Cut(major = ∃x.φ)
  not_elim       (contradiction)        → NO CUT (policy α; see §1.4)
```

`not_elim` is the only "combining elim" by data-flow shape that does
**not** emit a Cut. The contradiction it witnesses is closed
structurally at the enclosing closer (NOT-block end / BottomElim /
CLASSICAL_ABSURD) via `emit_close` on the two operand-formula positions
in the sequent. The result-visibility invariant (§1.4) guarantees those
positions exist.

Everything else emits cut-free LKR. The boundary contract that justifies
this stronger guarantee:

- **Stage 1 (already landed)** delivers a Program<nd::Instr> with no
  `Use`, no `SchemaInst`, no `IotaElim`, no `EqSym`. So no
  citation cuts and no equality cuts reach Stage 2. The only ops that
  remain are the structural, intro, projection-elim, combining-elim, and
  classical families.
- **Stage 3 (LKR cut-elim Hauptsatz)** discharges the residual
  combining-elim cuts. The fewer cuts Stage 2 emits, the smaller Stage 3's
  job.

### 1.3 Result-visibility invariant (policy α hard rule)

**Invariant.** Every Phase 1–3 per-op emitter, when it emits LKR ops for
an ND step k with derived formula F_k, must leave **NNF(F_k) visible at
the sequent position the consumer expects** — where "the consumer" is
whichever ND step references step k as one of its operands.

This is the inductive obligation that makes the (α) NotElim policy
sound: NotElim's two operands (the `negation` step and the `formula`
step) have their NNFs in the sequent at the closer's site, dual to each
other, and `emit_close` closes structurally — no Cut needed.

The invariant has three concrete manifestations:

- **Introductions** (Phase 1): when an intro op emits an LKR right rule
  on principal `f_k_idx`, the rule decomposes NNF(F_k) into its
  immediate sub-formulas at adjacent positions (Or, Forall, Exists) or
  into two new subgoals (And, IffIntro). Recursive descent on premises
  sees the decomposed structure and continues.
- **Projection elims** (Phase 2): a projection elim of step k (whose
  producer derives a compound F_producer) leaves NNF(F_k) visible at
  `f_k_idx` by emitting the *demand-driven* decomposition of
  F_producer's translation. (Detailed in Phase 2.)
- **Combining elims** (Phase 3): when implies/or/exists_elim emits a
  Cut(major), the RIGHT branch carries NNF(¬major) into Γ — but the
  emitter also must arrange that NNF(F_k) (= the combining elim's
  derived formula) ends up at the appropriate position on RIGHT for
  downstream consumers. (Detailed in Phase 3.)

**Violation = translator bug.** If a Phase 1–3 emitter cannot satisfy
this invariant for some input shape, the spec is incomplete and the
fallback is *not* "emit a Cut anyway." The fallback is "fix the spec":
identify the missing case mathematically and extend the emitter. This
keeps the (α) policy as a hard invariant rather than a default with
silent overrides.

### 1.4 Translator architecture: recursive descent on the derivation tree

The (α) NotElim policy + the "cuts only on combining elims" claim
together force a different control flow from the existing cut-spine
translator. The mathematical reason: the existing translator's
per-step Cut is BOTH a cut-elim work-item AND the SHARING MECHANISM
for downstream consumers of step k (they find `NNF(¬F_k)` in the
sequent via `step_to_neg_idx[k]` and close against it). Removing the
per-step Cut breaks sharing — downstream consumers have no way to
reference k's result without re-deriving it.

**Decision (2026-05-24): unfold shares via recursive descent.** Each ND
step referenced N times in the derivation DAG is re-translated N times
in the LK tree. The LK proof's size is O(2^reuse_depth) worst case but
its cut count is strictly bounded by the number of combining elims.
This realizes the Prawitz correspondence on the *unfolded* derivation
tree — the cleanest mathematical reading.

**Control flow.** The dispatcher (Phase 5) is a recursive function:

```
translate_step(step_idx, shadow_state, position_for_F_k) -> emits LKR ops:
   op = program[step_idx]
   case INTROduction:
     emit one LKR right rule on `position_for_F_k`
     return post-state shadow(s) and per-premise position(s)
     for each premise step:
       recurse with the appropriate shadow + position
   case PROJection_elim:
     decompose the producer's translation demand-drivenly
     recurse into producer with the demanded shape
   case COMBining_elim:
     emit Cut(F_major), recurse on LEFT with major-only,
     recurse on RIGHT with NNF(¬F_major) carried + body to translate
   case STRUCTural (Assume, Fix, ExistsElim opener, Qed, Let):
     emit nothing; bind scope state into shadow if relevant
     leaf cases (Assume, Fix) close the current goal via the in-scope
     assumption's dual / eigenvar's binding
```

The recursion bottoms out at:
- **`Assume`**: the assumed formula is in the sequent as `NNF(A)` (placed
  by the enclosing IMPLIES/NOT/CLASSICAL_ABSURD intro's emission); the
  current goal `F_k` (= `NNF(A)` for an Assume-derived step) is closed
  against the dual `NNF(¬A)` (the principal entry of the enclosing
  intro) via AxiomLit / `emit_close`.
- **`Fix`**: not a derivation step; referenced only as a TermRef. The
  enclosing ForallIntro emitter binds `shadow.lkr_term_for[fix_idx]`.
- **`Use` / `SchemaInst` / `IotaElim` / `EqSym`**: cannot
  occur — Stage 1's input gate guarantees their absence.

**Per-op emitter contract** (Phases 1–3): each emitter handles ONE op,
emits the corresponding LKR rule(s), updates the shadow, and returns
per-premise positions for the dispatcher to recurse into. NO recursion
inside the emitter — the dispatcher owns control flow. This makes
Phase 1–3 unit-testable in isolation.

**Block tree's reduced role.** The block_tree still captures SCOPE
structure (which assumptions, eigenvars are in scope at each point),
but its WALK semantics change: the dispatcher walks the derivation
tree starting from `qed.derived`, not the block tree. The block_tree
serves as a precomputed map `step_idx → enclosing_block_kind` so
emitters can recover scope context (e.g., "this Assume step belongs to
which IMPLIES block").

### 1.5 Soundness/completeness contracts (boundary discipline)

- **Input contract** (enforced by InputGate, reused as-is): no
  IotaElim, no EqSym, NDVerifier accepts the input against the
  caller-supplied goal.
- **Output contract** (enforced by OutputGate, reused as-is): the
  emitted Program<lkr::Instr> verifies under LKRVerifier against
  NNF(goal). This is the **sole** soundness witness for Stage 2;
  translator-internal invariants (sequent shadow consistency, block-tree
  shape, etc.) are bug-finding heuristics, not soundness arguments.
- **Completeness obligation.** For every well-formed input (= NDVerifies
  against the goal), the translator must succeed. The corpus is **not**
  the completeness witness; the mathematical inductive argument over the
  ND derivation tree is.

## 2. Stage 1 → Stage 2 boundary (input contract recap)

From `nd_internalize::apply` (`src/proof/translate/nd_internalize/apply.h`):

```
  ApplyResult {
    proof:        Program<nd::Instr>   // NDVerifier-accepted
    wrapped_goal: SentenceHandle       // = H → φ or just φ
    facts:        vector<SentenceHandle>
  }
```

`facts.empty()` is the identity case: `wrapped_goal = φ` and the proof
has no `Assume(H)` prelude. Otherwise the prelude is `Assume(H); and_elim
chain; …` and the body proves φ. Either way:

- **no `Use` ops** anywhere in the body
- **no `SchemaInst` ops**
- **no `IotaElim`, `EqSym`** (Stage 1's output gate enforces)

This is the proof Stage 2's `apply` consumes.

## 3. Reuse plan for existing `nd_to_lkr/` infrastructure (file layout split-by-phase)

The hard-cutover deletes `cut_spine.{h,cpp}` and introduces four
per-phase emitter files plus a thin dispatcher. The rest is reused with
at most cosmetic edits:

| File                       | Disposition                                       |
|----------------------------|---------------------------------------------------|
| `input_gate.{h,cpp}`       | **KEEP.** I-1/I-2/I-3 checks unchanged.           |
| `block_tree.{h,cpp}`       | **KEEP, role reduced.** Block decomposition still computes scope-nesting structure, but the dispatcher no longer *walks* the block tree linearly. Instead, the block_tree becomes a precomputed `step_idx → enclosing_block_kind` lookup that emitters consult for scope context. |
| `sequent_shadow.h`         | **KEEP.** The shadow model (verifier-mirror, no soundness role) is correct for cut-minimal too. Cut-minimal recursion clones shadows per branch (an LKR right rule that splits into two subgoals returns two shadow successors). |
| `emit_close.{h,cpp}`       | **KEEP.** Dual-decomposition closer is generic over rule provenance; reused by every intro/projection emitter that bottoms out at AxiomLit, and by Phase 4's NOT/BottomElim/CLASSICAL_ABSURD closers (α policy). |
| `output_gate.{h,cpp}`      | **KEEP.** LKRVerifier acceptance gate unchanged. |
| `cut_spine.{h,cpp}`        | **DELETE in Phase 5.** Replaced by the split-by-phase emitters below + the new recursive dispatcher. |
| `intros.{h,cpp}`           | **NEW, Phase 1.** Emitters for and/or/implies/forall/exists/iff_intro + ExcludedMiddle + Peirce. Per-op contract: emit one LKR right rule, mutate the shadow, return per-premise position(s) for the dispatcher to recurse into. |
| `projections.{h,cpp}`      | **NEW, Phase 2.** Emitters for and_elim_l/r, forall_elim, iff_elim_l/r, DoubleNegElim. Demand-driven: recurses into the producer with the demanded shape. |
| `combining.{h,cpp}`        | **NEW, Phase 3.** Emitters for implies/or/exists_elim (the only Cut sites). Each emits Cut(major) + carries the recursion into LEFT (major-only) and RIGHT (with NNF(¬major)). |
| `structural.{h,cpp}`       | **NEW, Phase 4.** Leaf-case translations for Assume / Fix / ExistsElim (no logical emission; scope state binding); block-closer logic for NOT / BottomElim / CLASSICAL_ABSURD (emit_close on operand positions). |
| `dispatcher.{h,cpp}`       | **NEW, Phase 5.** Recursive `translate_step` function. Routes by op-family to intros/projections/combining/structural emitters. Initiates the recursion at `qed.derived`. |
| `nd_to_lkr.{h,cpp}`        | **MINOR.** Pass header / apply signature stays; implementation calls dispatcher. |

The Q4 hard-cutover precedent from Stage 1: deletion of `cut_spine.{h,cpp}`
happens in one commit at Phase 5, after Phases 1–4 are independently
green on per-rule unit tests.

## 4. Phase decomposition (user-approved)

| Phase | Subject                            | Output                                              |
|-------|------------------------------------|------------------------------------------------------|
| 1     | introductions                      | `intros.{h,cpp}`: and/or/implies/forall/exists/not/iff_intro + bottom_elim + ExcludedMiddle + Peirce |
| 2     | projection elims                   | `projections.{h,cpp}`: and_elim_l/r, forall_elim, iff_elim_l/r, DoubleNegElim — cut-free, demand-driven |
| 3     | combining elims (Cut sites)        | `combining.{h,cpp}`: implies/or/exists_elim — Cut(major). NotElim NOT in scope (α). |
| 4     | structural ops + closers           | `structural.{h,cpp}`: assume/fix/ExistsElim-scope/Qed threading; ClassicalAbsurd block; NOT/BottomElim closers via emit_close (α). |
| 5     | dispatcher + hard cutover          | `dispatcher.{h,cpp}`: wire everything; delete `cut_spine.{h,cpp}`; ZFC parity smoke. |

Each phase: spec → unit tests → impl → green → commit. Per-phase
mathematical detail is added to this doc as the phase opens.

## 5. Phase 1 — introductions (cut-free right rules)

### 5.0 Per-op emitter contract (recursive-descent dispatch)

Each Phase 1 emitter is invoked by the Phase 5 dispatcher when an
intro op is reached during recursive descent on the derivation tree.
The dispatcher arranges the inputs:

```
PRE:  shadow.entries[f_k_idx] = NNF(F_k), where F_k is the intro's
      result formula. The dispatcher computes f_k_idx based on the
      enclosing right-rule's prior emission (e.g., outer And split's
      LEFT-subgoal-tail position).

ACTION: emit ≥1 LKR right-rule op(s) into `out`, mutate `shadow` (or
      return per-branch shadows for branching rules), and return
      per-premise positions for the dispatcher to recurse into.

POST: F_k's NNF structure has been decomposed by the right rule; the
      premise formula(s) live at the returned position(s) ready for
      recursive translation.

NO RECURSION INSIDE THE EMITTER. The dispatcher owns control flow.
```

For non-branching intros (Or, Forall, Exists, single shadow returned).
For branching intros (And, IffIntro), two shadows are returned. The
dispatcher recurses into each in turn.

### 5.1 Per-op mathematical translation

Let `S = shadow.entries` at the point an intro op fires; `f_k_idx` is the
sequent position where the intro's *result* must land. For each op, "the
rule" is stated as a sequent-level transformation; the resulting LKR op
stream realises that transformation. The emitter's return value lists
the per-premise positions the dispatcher will recurse into.

#### 5.1.1 `AndIntro(a, b)` — result `A ∧ B`

LKR's `And` is multiplicative: `Γ,φ` AND `Δ,θ ⊢ Γ,Δ,φ∧θ`. The
translator must choose a partition (Γ, Δ) of the parent's non-principal
entries. For cut-minimal recursive descent, both premises (π_a and
π_b) may need *all* of the outer scope's accumulated entries
(assumption duals, eigenvar bindings, etc.) — so a clean partition is
not generally possible.

**Strategy: full-context duplication.** Before emitting `And`, emit one
`Weakening{γ_i}` per non-principal entry `γ_i` in the parent shadow,
appending duplicates. Then `And{principal = f_k_idx, right_needs = …}`
where `right_needs = [n .. 2n-1]` (the indices of the duplicated
copies). LEFT receives the original entries + A; RIGHT receives the
duplicate copies + B. Both branches see the full context.

```
  S, …, A∧B, …      (parent, n+1 entries, principal at f_k_idx)
   ↓ Weakening × n  (duplicate each non-principal γ_i)
  S, …, A∧B, …, S'    (2n+1 entries, S' = duplicates of S)
   ↓ And{principal=f_k_idx, right_needs=[duplicate-indices]}
  LEFT: S, A      ∥    RIGHT: S', B
```

Both `S` and `S'` are formula-equivalent to the parent's non-principal
context. The cost is n Weakening ops per And-branching intro (and per
IffIntro, which uses And under the hood). Polynomial in proof size.

The dispatcher then recursively translates π_a under LEFT and π_b
under RIGHT. The emitter returns `(left_shadow, right_shadow,
left_premise_idx, right_premise_idx, position_a_in_left,
position_b_in_right)` for the dispatcher to use.

> The existing `emit_and_split` helper takes a `right_needs` parameter
> matching this design. It is reusable verbatim; the new caller
> computes `right_needs` as the full-duplicate index set.

#### 5.1.2 `OrIntroL(a, b_formula)` — result `A ∨ B`

```
  S, …, A∨B, …    ↦    S, …, A, B, …
```

LKR emission: `Or{principal = f_k_idx}`. Then continue with π_a, which
proves A (now at the original f_k_idx position; B is appended at the end
of the sequent and discarded via Weakening at close-time, or just left
present — Weakening is admissible).

Symmetric for `OrIntroR(a_formula, b)`. The Let-bound side (the formula
that isn't derived) is a payload; the LKR Or rule doesn't care which
disjunct is derived since both are exposed in the sequent.

#### 5.1.3 `ImpliesIntro(conclusion)` — result `A → B`

Result is `A → B` whose NNF is `¬A_nnf ∨ B_nnf`. The block-tree wraps
ImpliesIntro into an IMPLIES block opened by `Assume(A)`.

```
  S, …, A→B, …
    = S, …, ¬A_nnf ∨ B_nnf, …
    ↦  S, …, ¬A_nnf, B_nnf, …      (LKR Or)
```

After `Or{principal = f_k_idx}`, the sequent has `¬A_nnf` and `B_nnf`
adjacent. The IMPLIES block's body then proves B under assumption A; in
the LKR side, every use of A in the body closes against the `¬A_nnf`
literal (via AxiomLit if A is atomic, via recursive `emit_close` if A is
compound).

LKR emission: `Or{principal = f_k_idx}` + recursive translation of the
body.

#### 5.1.4 `NotIntro(bottom)` — result `¬A` (NOT-block closer; deferred to Phase 4)

`NotIntro` is the **closer** of a NOT block opened by `Assume(A)`. The
block-opening Weakening of NNF(A) and the closer's `emit_close` between
NNF(A) and the principal NNF(¬A) live in Phase 4 (structural). Phase 1
does not implement NotIntro — the block-tree walk hands NOT blocks
directly to Phase 4's structural emitter.

The (α) result-visibility invariant: at the closer, the sequent must
have NNF(A) (placed by the Assume opener) and NNF(¬A) (the outer goal's
principal entry) so `emit_close` discharges via AxiomLit (atomic) or
structural recursion (compound).

#### 5.1.5 `BottomElim(bottom, target_formula)` — result = target_formula (closer; deferred to Phase 4)

`BottomElim` is a flat op but its semantics are closer-shaped: it
discharges a contradiction (via `bottom` = a NotElim ghost) and
"weakens in" a target formula. Specified in Phase 4 alongside the NOT
closer because the LKR machinery is identical (emit_close between
NotElim's operand NNFs).

#### 5.1.6 `IffIntro(ab, ba)` — result `A ↔ B`

NNF(A ↔ B) = (¬A_nnf ∨ B_nnf) ∧ (¬B_nnf ∨ A_nnf). The IffIntro takes
two subderivations: one of A → B (the ab step), one of B → A (the ba
step).

```
  S, …, A↔B, …    ↦    S, …, ¬A∨B, …  ∥  S, …, ¬B∨A, …    (LKR And)
                  ↦    S, …, ¬A, B, …  ∥  S, …, ¬B, A, …   (LKR Or on each)
```

LKR emission: `And{principal = f_k_idx, …}` then `Or` on each subgoal,
then recursive translation of π_{ab} and π_{ba}.

#### 5.1.7 `ForallIntro(body)` — result `∀x.φ`

The FORALL block opens with `Fix(v)`; ForallIntro's body step holds
φ[v]. The eigenvariable `v` is recorded by the block tree.

```
  S, …, ∀x.φ, …    ↦    S, …, φ[x:=v], …     (LKR Forall, with eigen = v)
```

LKR emission: `Forall{principal = f_k_idx, eigen = v}` + recursive
translation of the body.

The verifier's side condition (eigen not free in Γ) is automatic by ND's
Fix discipline — `v` is fresh in the ND scope, hence not free in any
prior ND step's formula, hence not free in S.

#### 5.1.8 `ExistsIntro(body, witness?)` — result `∃x.φ`

Two forms:

- **With witness t** (`witness = some(t_ref)`): direct rule.
  ```
    S, …, ∃x.φ, …    ↦    S, …, φ[x:=t], …    (LKR Exists)
  ```
  LKR emission: `Exists{principal = f_k_idx, witness = t_ref_lkr}` +
  recursive translation of body. `t_ref_lkr` is the LKR TermRef recorded
  by the corresponding LKR Forall op (via `shadow.lkr_term_for`).

- **Without witness** (`witness = nullopt`): the closer of an
  EXISTS_ELIM block. Handled by Phase 4's structural treatment.

#### 5.1.9 `ExcludedMiddle(formula_let)` — result `A ∨ ¬A`

Classical primitive, intro-flavoured (no premise; produces a tautology).
The Let-bound `formula_let` step holds A's formula. Goal entry is
`A ∨ ¬A` at f_k_idx with NNF `A_nnf ∨ ¬A_nnf` (NNF of the disjunct A
and its NNF dual).

```
  S, …, A∨¬A, …    ↦    S, …, A, ¬A, …       (LKR Or on the principal)
                  ↦    S, …, dual-literals close via AxiomLit / emit_close
```

LKR emission: `Or{principal = f_k_idx}` (exposes A_nnf and ¬A_nnf
adjacent), then `emit_close(f_k_idx, end_idx)` to close via the dual
pair. No premise translation; ExcludedMiddle is a cut-free closed proof.

#### 5.1.10 `Peirce(a_let, b_let)` — result `((A→B)→A) → A`

Classical primitive. The Let-bound a/b steps hold A and B respectively.
NNF(((A→B)→A) → A) = ¬((¬A∨B)→A) ∨ A = (¬A∨B)∧¬A ∨ A — i.e., a
compound. Cut-free LKR proof of Peirce's law is a fixed skeleton (Or
to expose the outer disjuncts, And to split the conjunct on the
remaining side, AxiomLit-close all branches).

Detailed emission worked out in Phase 1 impl; the skeleton is uniform
in A and B.

### 5.2 Phase 1 unit-test surface

For each op in §5.1.1 – §5.1.10 (except §5.1.4 NotIntro and §5.1.5
BottomElim, both deferred to Phase 4), a minimal test:

- Construct a synthetic 1-rule ND program that fires *only* that intro op
  in a small surrounding context.
- Call the Phase 1 emitter against a fresh `SequentShadow`.
- Assert: (a) returned LKR ops match the expected shape; (b) `LKRVerifier`
  accepts the result against the expected NNF sequent.

Test file: `test/cut_minimal_intros_test.cpp` (new).

### 5.3 Phase 1 deliverable

A new `intros.{h,cpp}` exposing one emitter per intro op:

```c++
namespace logic::proof::translate::nd_to_lkr::intros {

util::ResultStatus emit_and_intro       (Ctx&, const nd::AndIntro&,       SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_or_intro_l      (Ctx&, const nd::OrIntroL&,       SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_or_intro_r      (Ctx&, const nd::OrIntroR&,       SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_implies_intro   (Ctx&, const nd::ImpliesIntro&,   SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_iff_intro       (Ctx&, const nd::IffIntro&,       SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_forall_intro    (Ctx&, const nd::ForallIntro&,    SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_exists_intro    (Ctx&, const nd::ExistsIntro&,    SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_excluded_middle (Ctx&, const nd::ExcludedMiddle&, SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);
util::ResultStatus emit_peirce          (Ctx&, const nd::Peirce&,         SequentShadow&, size_t f_k_idx, std::vector<lkr::Instr>& out);

// NotIntro and BottomElim are NOT in Phase 1 — they're block closers
// and live in Phase 4 (structural.{h,cpp}).

}  // namespace …::intros
```

`Ctx` is the per-phase context struct (passes GlobalContext +
FormulaBuilder; details fixed during Phase 1 impl).

The Phase 5 dispatcher routes by op-family to these. No cuts emitted
from any of them. Each must satisfy the (α) result-visibility invariant:
after emission, NNF(F_k_intro) is visible at the appropriate sequent
position for downstream consumers.

## 6. Phases 2–5 (stubs, filled in per-phase)

### 6.1 Phase 2 — projection elims (demand-driven, descriptor-only)

**Math.** Per Prawitz, projection elims are absorbed into the producer's
translation: when `and_elim_l(h_ab)` asks for A, the dispatcher recurses
on `h_ab` with the **demand** "give me your A out of A∧B." If h_ab is
`and_intro(h_a, h_b)`, the demand short-circuits to recursing on h_a
(the and_intro contributes nothing). If h_ab is another projection elim,
the demand promotes transitively. If h_ab bottoms out at Stage 1's
prelude `Assume(F)`, the demand pinpoints which sub-formula of F closes
against which assumed dual. If h_ab is a combining elim, the demand
propagates into each branch.

**Demand variant** (six cases):

```
Demand =
  | NONE                       // default — produce the full F_k
  | AND_LEFT                   // and_elim_l: give me the left conjunct of F_k
  | AND_RIGHT                  // and_elim_r: give me the right conjunct
  | IFF_LEFT                   // iff_elim_l: give me the forward direction A→B
  | IFF_RIGHT                  // iff_elim_r: give me the reverse direction B→A
  | DOUBLE_NEG                 // double_neg_elim: strip ¬¬, give me the inner
  | INSTANCE(t)                // forall_elim with witness term t
```

**Phase 2 contract.** Each projection-elim emitter:

```
PRE:    op is the projection elim ND op.
        shadow.entries[f_k_idx] = NNF(F_k), where F_k is the elim's
        result (= the sub-formula of the producer's full formula).
ACTION: emit ZERO LKR ops. (The math lives in demand consumption,
        which is Phase 5's dispatcher + demand-aware Phase 1.)
POST:   return a RecurseDescriptor{
            producer_step_idx: the elim's `of` (or `formula` for
                               forall_elim, or `iff`+side for iff_elim),
            target_pos:        f_k_idx (where F_k still lives),
            demand:            the projection's Demand variant
        }.
```

Phase 5 consumes the descriptor: when the dispatcher follows the
recurse target, it passes `demand` to the producer's emitter. Demand-
aware Phase 1 emitters then short-circuit (or substitute, for
INSTANCE(t)) accordingly.

**Phase 2 emitters** (in `projections.{h,cpp}`):

```c++
emit_and_elim_l(...)      → demand = AND_LEFT
emit_and_elim_r(...)      → demand = AND_RIGHT
emit_iff_elim_l(...)      → demand = IFF_LEFT
emit_iff_elim_r(...)      → demand = IFF_RIGHT
emit_double_neg_elim(...) → demand = DOUBLE_NEG
emit_forall_elim(...)     → demand = INSTANCE(t)  // t resolved from op
```

**Phase 2 tests.** Unit-level assertions on the returned
RecurseDescriptor's fields. End-to-end LKRVerifier acceptance is
exercised at Phase 5 (when demand consumption lands). The descriptor
tests catch API errors but not semantic correctness — the latter is
witnessed by Phase 5's integration tests.

**Why "data-only" Phase 2 is the right cut.** The math says projection
elims contribute *nothing* to the LK proof — they're annotations that
re-shape the recursion. Putting demand-consumption math here would
require Phase 1 retrofits + leaf-case (Assume/Fix) handling + a
minimal dispatcher, which is most of Phase 5 in disguise. The cleaner
boundary keeps Phase 2 thin and lets Phase 5 carry the integration.

### 6.2 Phase 3 — combining elims (Cut sites, descriptor-only)

**Math.** Each combining elim emits Cut on its major premise; the LEFT
branch proves the major (recurse on major-step); the RIGHT branch
carries NNF(¬major) and closes the surrounding goal using the
combining-elim's other operands. For implies_elim, the RIGHT branch
involves a second Cut on the antecedent; for or_elim, the structure
is yet more involved (three Cuts plus a nested ∧-split pattern).

The full closure-emission math is non-trivial and lives at Phase 5 (where
the dispatcher integrates Phases 1-4 and orchestrates the recursion).
Phase 3's mathematical contribution is to identify the combining-elim
structure and project each op into a descriptor naming its major +
minor step references.

**CombineSite descriptors** (one per combining-elim op type):

```
ImpliesElimSite  { impl_step: StepRef, ant_step: StepRef, target_pos: size_t }
OrElimSite       { or_formula_step: StepRef, ac_step: StepRef, bc_step: StepRef, target_pos: size_t }
ExistsElimSite   { formula_step: StepRef, target_pos: size_t }
                                       // scope handling integrates with Phase 4
```

**NotElim is NOT in Phase 3** (per α policy: NotElim is no-emit, closer
handled in Phase 4).

**Phase 3 contract.** Each emitter:

```
PRE:    op is the combining-elim ND op. shadow.entries[target_pos]
        contains the combining elim's result formula NNF (= the
        consumer's expected position).
ACTION: emit ZERO LKR ops. (Cut + And + AxiomLit emission lives in
        Phase 5.)
POST:   return the appropriate CombineSite descriptor.
```

**Why data-only Phase 3.** Same rationale as Phase 2: the
combining-elim's actual LKR realization requires the dispatcher (which
recurses on the named major + minor steps with proper shadow threading)
and demand-aware Phase 1 emitters. Putting that machinery in Phase 3
would pull most of Phase 5 in. Cleaner: Phase 3 ships descriptors,
Phase 5 integrates.

**Phase 3 emitters** (in `combining.{h,cpp}`):

```c++
emit_implies_elim(op, shadow, target_pos) → ImpliesElimSite
emit_or_elim(op, shadow, target_pos)      → OrElimSite
emit_exists_elim(op, shadow, target_pos)  → ExistsElimSite
```

**Phase 3 tests.** Unit-level: descriptor field-mapping per op
variant. End-to-end LKRVerifier acceptance at Phase 5.

### 6.3 Phase 4 — structural (Fix, Assume, ExistsElim, Qed; closers; descriptor-only)

**Math.** Phase 4 captures the scope-manipulation and closer machinery
that the dispatcher (Phase 5) needs to thread the block-tree's
structure. Same data-only convention as Phases 2 and 3: emitters
project the op into a descriptor; Phase 5 consumes.

**Per-op contracts** (all descriptor-only; no LKR ops emitted):

**Openers** (scope-manipulators):

```
AssumeOpenSite   { assume_step: StepRef, formula: FormulaHandle }
   Sets up an assumption scope. The enclosing IMPLIES/NOT/
   CLASSICAL_ABSURD intro emitter places NNF(¬formula) at a
   specific principal position; Phase 5 records assume_step →
   that position so references to the assumption (= leaf cases)
   can close against the dual.

FixOpenSite      { fix_step: StepRef, eigen: var_index }
   Records the eigenvariable bound by Fix. Phase 5 inserts
   shadow.lkr_term_for[fix_step.idx] = {lkr_ref, Term::fixed(eigen)}.
   The trace's term_env[fix_step.idx] provides the eigen.

ExistsElimOpenSite { exists_elim_step: StepRef,
                     formula_step:   StepRef,
                     eigen:          var_index }
   Records the EXISTS_ELIM block opener. Phase 5 emits the
   combining-elim Cut on the existential (per Phase 3
   ExistsElimSite) and binds the eigen for the body.
```

**Closers** (emit_close drivers per α policy):

```
NotIntroCloseSite      { not_intro_step: StepRef,
                         neg_step:       StepRef,
                         formula_step:   StepRef }
   NOT-block closer. Phase 5 emits emit_close on the LKR sequent
   positions of NNF(F_neg_step) and NNF(F_formula_step) — by the
   result-visibility invariant, both are visible after the body's
   translation.

BottomElimCloseSite    { bottom_elim_step: StepRef,
                         neg_step:         StepRef,
                         formula_step:     StepRef,
                         target_formula:   StepRef }
   ⊥-elim: discharges a contradiction (via the NotElim ghost at
   bottom_elim_step.bottom) and the surrounding goal needs
   target_formula. Phase 5 emits emit_close on the operands.

ClassicalAbsurdCloseSite { absurd_step: StepRef,
                           neg_step:    StepRef,
                           formula_step: StepRef }
   CLASSICAL_ABSURD-block closer (assume ¬A, derive ⊥, conclude A).
   Mechanically identical to NotIntro at the LKR level — emit_close
   on the operands.
```

**Leaf case** (Assume reference in recursive descent):

```
AssumeLeafSite { assume_step: StepRef, target_pos: size_t }
   When the recursion lands on a reference to an Assume step (e.g.,
   the body of an IMPLIES block uses the assumed A in modus
   ponens), the dispatcher emits emit_close between target_pos
   (where the consumer expected A) and the previously-recorded
   dual position (where NNF(¬A) lives).
```

**Entry point**:

```
QedSite { qed_step: StepRef, derived_step: StepRef }
   The OUTER block's Qed. derived_step is the proof's conclusion —
   the dispatcher's recursive-descent entry point.
```

**NotElim is NOT in Phase 4 either** (per α policy: no-emit, always).
It's a "ghost" op consumed by the enclosing closer's descriptor (its
operands feed the NotIntro/BottomElim/ClassicalAbsurd close sites).

**Phase 4 tests.** Unit-level: each emitter's descriptor field-mapping
+ closer ops' NotElim-operand extraction (the closer's `bottom` field
points to a NotElim step in the program; the emitter dereferences and
extracts operands).

### 6.4 Phase 5 — apply orchestrator + hard cutover

- Replace `cut_spine.{h,cpp}` in place with a new dispatcher that calls
  the Phase 1–4 emitters by op family.
- Delete the old "Cut per FlatStep" code.
- Output gate (LKRVerifier) unchanged.
- ZFC parity smoke: cut-minimal NDtoLKR on Stage 1's output produces
  LKRVerifier-accepted LKR with strictly fewer cuts than the old
  translator.

## 7. Design decisions (resolved 2026-05-24)

All four open questions are settled:

### 7.1 NotElim policy → (α) no-emit, always

NotElim emits nothing. Its consumer (NOT-block closer / BottomElim /
CLASSICAL_ABSURD closer) closes the contradiction via `emit_close`
between the operand-formula positions in the sequent. The
result-visibility invariant (§1.4) is the inductive obligation that
makes this sound and complete — every Phase 1–3 emitter must leave its
result formula visible in the sequent at the position the consumer
expects.

### 7.2 Classical ops → split

- `ExcludedMiddle`, `Peirce`: **Phase 1** (intro-family). They produce a
  tautology with no premise; LKR realises them via fixed cut-free
  skeletons (e.g., excluded_middle of A: Or-decompose A∨¬A into
  adjacent A and ¬A, AxiomLit-close).
- `DoubleNegElim`: **Phase 2** (projection-elim family). Takes ¬¬A and
  produces A; LKR realises by a fixed cut-free skeleton on ¬¬A's
  derivation.
- `ClassicalAbsurd`: **Phase 4** (structural). It's the closer of a
  CLASSICAL_ABSURD block opened by `Assume(¬A)`.

### 7.3 File layout → split by phase

Phase 1 lives in `intros.{h,cpp}`, Phase 2 in `projections.{h,cpp}`,
Phase 3 in `combining.{h,cpp}`, Phase 4 in `structural.{h,cpp}`, Phase 5
introduces `dispatcher.{h,cpp}` and deletes `cut_spine.{h,cpp}`.

### 7.4 No other pre-Phase-1 gates

Existing sequent shadow kept. LKRVerifier output gate is the soundness
witness. Per-phase test files are added as each phase opens.

## 8. Risks and non-goals

- **Non-goal.** "Make the LKR program cut-free." That's Stage 3's job
  (Hauptsatz). Stage 2 is "cut-minimal," not "cut-free."
- **Non-goal.** Performance optimisation of the translator. Correctness
  + completeness first.
- **Non-goal.** Bounding LKR proof size. The recursive-descent unfolding
  of shared ND steps is worst-case exponential in reuse depth (§1.5).
  Acceptable because (a) the math is cleanest this way, (b) Stage 3
  receives fewer cuts to eliminate, and (c) corpus blowup is a
  post-implementation concern, not a design driver.
- **Risk.** ZFC proofs with deep step-reuse may produce LKR programs too
  large to materialize. If that becomes a real blocker, the response is
  to *strengthen Stage 1* — Stage 1 could expose more reuse-via-lemma,
  cutting reuse at the ND level so Stage 2's tree is naturally smaller.
  Stage 2 itself stays mathematically pure.
- **Risk.** Cut-minimal translation of projection elims requires
  demand-driven analysis (Phase 2). The recursive descent makes this
  natural — the dispatcher recurses into the producer with the demanded
  shape — but the *demand calculation* needs careful spec'ing in Phase 2.
- **Risk.** Classical ops (DoubleNegElim etc.) are well-defined in LK
  but their cut-minimal translation needs care. Phase 2 (DoubleNegElim)
  and Phase 1 (ExcludedMiddle, Peirce) specify per-op.

---

End of Phase 0 draft. Phases 1–5 to be elaborated as we reach them,
math-first per phase.
