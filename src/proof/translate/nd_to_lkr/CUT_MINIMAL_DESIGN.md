# Stage 2: cut-minimal NDtoLKR — design doc

> **Status.** Phase 0 spec, user-approved 2026-05-24. Four design
> decisions baked in: (1) file layout split by phase, (2) classical-op
> split (ExcludedMiddle/Peirce → Phase 1, DoubleNegElim → Phase 2,
> ClassicalAbsurd → Phase 4), (3) NotElim policy (α): no-emit, always,
> (4) result-visibility invariant binds across Phases 1–3 (see §1.4).
> Phase 1 (introductions) detail inline; Phases 2–5 stubbed and filled
> in as we reach them.

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
  `Use`, no `SchemaInst`, no `IotaElim`, no `EqSubst/EqSym`. So no
  citation cuts and no equality cuts reach Stage 2. The only ops that
  remain are the structural, intro, projection-elim, combining-elim, and
  classical families.
- **Stage 3 (LKR cut-elim Hauptsatz)** discharges the residual
  combining-elim cuts. The fewer cuts Stage 2 emits, the smaller Stage 3's
  job.

### 1.4 Result-visibility invariant (policy α hard rule)

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
  on principal `f_k_idx`, the entry at `f_k_idx` becomes NNF(F_k_intro)
  or is decomposed into NNF(F_k_intro)'s top-level structure (e.g., Or
  exposes both disjuncts adjacent). Recursive translation of premises
  proceeds with the structure exposed.
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

### 1.5 Soundness/completeness contracts (boundary discipline)

- **Input contract** (enforced by InputGate, reused as-is): no
  IotaElim, no EqSubst/EqSym, NDVerifier accepts the input against the
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
- **no `IotaElim`, `EqSubst`, `EqSym`** (Stage 1's output gate enforces)

This is the proof Stage 2's `apply` consumes.

## 3. Reuse plan for existing `nd_to_lkr/` infrastructure (file layout split-by-phase)

The hard-cutover deletes `cut_spine.{h,cpp}` and introduces four
per-phase emitter files plus a thin dispatcher. The rest is reused with
at most cosmetic edits:

| File                       | Disposition                                       |
|----------------------------|---------------------------------------------------|
| `input_gate.{h,cpp}`       | **KEEP.** I-1/I-2/I-3 checks unchanged.           |
| `block_tree.{h,cpp}`       | **KEEP.** OUTER/FORALL/IMPLIES/NOT/CLASSICAL_ABSURD/EXISTS_ELIM decomposition is exactly the scope structure Stage 2 needs. |
| `sequent_shadow.h`         | **KEEP.** The shadow model (verifier-mirror, no soundness role) is correct for cut-minimal too. |
| `emit_close.{h,cpp}`       | **KEEP.** Dual-decomposition closer is generic over rule provenance; reused by every intro/projection emitter that bottoms out at AxiomLit, and by Phase 4's NOT/BottomElim/CLASSICAL_ABSURD closers (α policy). |
| `output_gate.{h,cpp}`      | **KEEP.** LKRVerifier acceptance gate unchanged. |
| `cut_spine.{h,cpp}`        | **DELETE in Phase 5.** Replaced by the split-by-phase emitters below. |
| `intros.{h,cpp}`           | **NEW, Phase 1.** Emitters for and/or/implies/forall/exists/not/iff_intro + bottom_elim + ExcludedMiddle + Peirce. |
| `projections.{h,cpp}`      | **NEW, Phase 2.** Emitters for and_elim_l/r, forall_elim, iff_elim_l/r, DoubleNegElim. |
| `combining.{h,cpp}`        | **NEW, Phase 3.** Emitters for implies/or/exists_elim (Cut sites). |
| `structural.{h,cpp}`       | **NEW, Phase 4.** Block-opener/closer threading (Assume/Fix/ExistsElim/Qed) + ClassicalAbsurd block + NOT/BottomElim closers (α: emit_close, no Cut). |
| `dispatcher.{h,cpp}`       | **NEW, Phase 5.** Thin op-family dispatcher; orchestrates the block-tree walk and routes each FlatStep to intros/projections/combining and each block opener/closer to structural. |
| `nd_to_lkr.{h,cpp}`        | **MINOR.** The Pass header / apply signature stays; the implementation calls dispatcher. |

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

### 5.1 Per-op mathematical translation

Let `S = shadow.entries` at the point an intro op fires; `f_k_idx` is the
sequent position where the intro's *result* must land (typically the
goal-side position for that subderivation).

For each op, "the rule" is stated as a sequent-level transformation; the
resulting LKR op stream realises that transformation.

#### 5.1.1 `AndIntro(a, b)` — result `A ∧ B`

```
  S, …, A∧B, …    ↦    S, …, A, …    ∥    S, …, B, …
```

LKR emission: `And{principal = f_k_idx, left_partition = …}`. The
multiplicative split is determined by which sequent entries each
subderivation needs (Stage 2 will compute this from the block tree's
data flow; the existing `emit_and_split` helper in `cut_spine.cpp` is
reusable verbatim).

The two subgoals are then proved by recursively translating π_a and π_b.

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

### 6.1 Phase 2 — projection elims

Open math question: Prawitz's correspondence makes projection elims
cut-free by **demand-driven translation** — when an `and_elim_l` asks
its producer for the A out of A∧B, the producer's translation is
parameterized so it exposes A directly rather than producing A∧B and
then cutting. This may require a two-pass strategy (data-flow analysis,
then emission) rather than the current one-pass block-tree walk.

To be specified before Phase 2 opens.

### 6.2 Phase 3 — combining elims (Cut sites)

ND `implies_elim(A→B, A) ⊢ B`. LKR:

```
  S, …, B, …    ↦    Cut(A→B):
                       LEFT:  S, …, B, …, A→B   (prove A→B)
                       RIGHT: S, …, B, …, ¬(A→B) = A_nnf ∧ ¬B_nnf
```

The RIGHT branch then ∧-splits to two subgoals: one with A_nnf adjacent
to B (closes via A's prior derivation), one with ¬B_nnf adjacent to B
(closes by AxiomLit).

To be specified in detail before Phase 3 opens.

### 6.3 Phase 4 — structural (assume, fix, ExistsElim, Qed, classical)

Threads the block-tree's scope structure into the per-op dispatcher.

Includes the open NotElim / BottomElim closer questions from §5.1.4 and
§5.1.5, plus the classical-block treatment (CLASSICAL_ABSURD,
DoubleNegElim, ExcludedMiddle, Peirce).

To be specified before Phase 4 opens.

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
- **Risk.** Cut-minimal translation of projection elims requires
  demand-driven analysis (Phase 2). If we discover this needs the full
  ND derivation tree's data-flow rather than the linear instr stream,
  Phase 2's design may require an additional precomputation pass before
  Phase 2's per-op emitters run.
- **Risk.** Classical ops (DoubleNegElim etc.) are well-defined in LK
  but their cut-minimal translation needs care. Phase 4 specifies.

---

End of Phase 0 draft. Phases 1–5 to be elaborated as we reach them,
math-first per phase.
