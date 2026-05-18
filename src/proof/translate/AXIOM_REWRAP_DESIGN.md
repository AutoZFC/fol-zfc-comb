# Axiom Rewrap (ND → ND): Mathematical Specification

Status: spec draft. Implementation not started.

This translator discharges the "axiom CombProofs" obligation
(COMPLETENESS.md §4.3). It runs the deduction theorem at the ND layer:
given an ND proof `P` of `φ` that references axioms `A_1, …, A_n`, it
emits an axiom-free ND proof `P'` of `H → φ` where
`H := A_1 ∧ … ∧ A_n`. The downstream `NDtoLKR → LKRtoComb` chain then
produces a `CombProof` of (the §15-augmentation of) `H → φ` — a
classical-validity witness that is `φ` under the assumed axioms.

## 0. Status

| Item                       | State |
|----------------------------|-------|
| Math spec                  | draft (this doc) |
| Implementation             | not started |
| Tests                      | not written |
| Pipeline-position decision | proposed: after `iota_elim`, before `NDtoLKR` |
| Doc home                   | `src/proof/translate/AXIOM_REWRAP_DESIGN.md` |

## 1. Scope

**Input.** An iota-free ND program `P` proving sentence `φ`, plus a
`TheoremAxiomMap` listing, for every theorem `T` cited by `P`, the
transitive axiom closure `axioms(T)` (computed when `T` itself was
translated).

**Output.** An ND program `P'` proving sentence `H → φ`, with

```
axioms(P) := {A : Use(A) ∈ P, A is an axiom}
           ∪ {SchemaInst(A, _) ∈ P, A is a schema axiom}
           ∪ ⋃_{T ∈ theorems(P)} axioms(T)

H        := A_1 ∧ A_2 ∧ … ∧ A_n     where A_1, …, A_n = sort_lex(axioms(P))
                                    left-associated:  (((A_1 ∧ A_2) ∧ A_3) … ∧ A_n)
```

`P'` contains **no** `Use(A)` or `SchemaInst(A, _)` for any axiom `A`.
It may still contain `Use(T)` for theorems `T` — those resolve at
LKR/Comb time via the lemma registry, where `T`'s entry proves
`H_T → T` (by induction).

**Out of scope.** Iota terms (apply `iota_elim` first). Non-classical
extensions (no LL/IL support). `axioms(P) = ∅` ⇒ rewrap is a no-op (P
is already an axiom-free proof of φ; pass through unchanged).

## 2. Math

### 2.1 Deduction theorem (the move)

Classical FOL deduction theorem: `Γ ∪ {A} ⊢ φ ⇔ Γ ⊢ A → φ`. Iterating
over `Γ = ∅` and `A_1, …, A_n`:

```
{A_1, …, A_n} ⊢ φ   ⇔   ⊢ (A_1 ∧ … ∧ A_n) → φ
```

(Use conjunction once, not curried: a single `assume h: H` and a single
`implies_intro` at the end. Cheaper than `n` nested assumes; the proof
size hit is in extracting `A_i` from `h`, not in the wrap.)

The proof of the `⇒` direction is constructive — exhibit a derivation
of `H → φ` from a derivation of `φ` using `{A_i}`:

```
assume h: H
h_A_1 = and_elim chain on h    # cached, used at every Use(A_1) site
h_A_2 = and_elim chain on h
…
h_A_n = and_elim chain on h
<body of P, with each Use(A_i) replaced by h_A_i>
qed_step                      # body's final step, deriving φ
implies_intro qed_step         # discharges h:H, yields H → φ
qed final                      # final = H → φ
```

This is exactly what `axiom_rewrap.apply` produces.

### 2.2 Transitive axiom closure

`P` may cite theorems via `Use(T)`. Each cited `T` was itself wrapped
earlier in the build, so its registered lemma form is `H_T → T` (not
`T`). To make `Use(T)` produce `T` in `P'`'s derivation, we need to
modus-ponens against `H_T`. That requires the axioms in `H_T` to be in
scope in `P'`. Hence:

```
axioms(P) := direct_axioms(P) ∪ ⋃_{T ∈ theorems(P)} axioms(T)
```

The `TheoremAxiomMap` (built incrementally as theorems translate) gives
`axioms(T)` for each cited `T`. Computing `axioms(P)` is one pass over
`P.instrs`.

### 2.3 Theorem citations: unwrap macro

For each `Use(T)` in `P` where `T` has wrapped form `H_T → T`:

```
# Replace the single Use(T) op with:
h_T_wrapped = use T                # binds H_T → T
h_axioms_for_T = <and_intro chain over {h_A_i : A_i ∈ axioms(T)}>
h_T = implies_elim h_T_wrapped, h_axioms_for_T
```

`h_T` now binds `T`'s formula. Any downstream step that referenced the
original `Use(T)`'s `StepRef` is rewritten to reference `h_T`'s index.

If `axioms(T) = ∅` (rare; the theorem is a tautology), the unwrap
collapses to `h_T = use T` directly — `H_T = ⊤` doesn't appear in our
encoding; that case is handled by the no-op short-circuit (§1 last
para). For uniformity in the rewrap, treat empty-antecedent theorems
as un-wrapped at registration.

### 2.4 Schemas (out of scope — handled upstream)

Schema instantiation (`nd::SchemaInst`) is eliminated by a separate
upstream ND→ND inline pass, analogous to `iota_elim`. By the time
`axiom_rewrap` runs, the proof contains no `SchemaInst` ops — every
schema use has already been replaced by the equivalent
`Use(schema_definition) + ForallElim` chain inlined at the call site.

The pipeline (full):
```
ND  ──iota_elim──▶  ND(ι-free)  ──schema_elim──▶  ND(ι-free, schema-free)
                                                            │
                                                            ▼
                                                     axiom_rewrap
                                                            │
                                                            ▼
                                                  NDtoLKR  →  LKRtoComb
```

`axiom_rewrap`'s input gate rejects any surviving `SchemaInst` with a
clear pointer to the upstream `schema_elim` pass. The wrap then treats
schema-definition axioms as ordinary axioms — they sit in `H` once,
and downstream `ForallElim`s on the cached extract handle each (now
explicit) instantiation site.

### 2.5 Canonical form

Two equivalent rewraps of the same `(P, axioms(P))` must produce the
same ND program (reproducibility, deterministic CombProof artifacts).
Hence:

- **Order**: `A_1, …, A_n` are `axioms(P)` sorted lex by axiom name.
- **Association**: left-associated conjunction `(((A_1 ∧ A_2) ∧ A_3) … )`.
  Extraction of `A_i` (`1 ≤ i ≤ n`) from `h: H` is the chain
  `and_elim_l^(n−i) ∘ and_elim_r^(if i < n then 1 else 0)` (formal
  index formula: see §4.5). For `n = 1`, `h_A_1 = h` directly (no
  extraction needed; `H = A_1`).

## 3. Architecture

### 3.1 Pipeline position

```
ND  ──iota_elim──▶  ND(iota-free)  ──axiom_rewrap──▶  ND(axiom-free)
                                                            │
                                                            ▼
                                                       NDtoLKR
                                                            │
                                                            ▼
                                                       LKR
                                                            │
                                                            ▼
                                                       LKRtoComb
                                                            │
                                                            ▼
                                                       CombProof of (H → φ)
```

Axiom rewrap runs **after** `iota_elim` because iota terms can appear
inside axiom bodies; the rewrap needs to embed those bodies into `H`
already-iota-free. It runs **before** `NDtoLKR` so the downstream
chain sees a clean (axiom-free, iota-free) ND proof and the proof's
goal as `H → φ`.

### 3.2 `TheoremAxiomMap`

```cpp
struct TheoremAxiomMap {
    // theorem name → sorted list of axiom names in axioms(T)
    std::unordered_map<std::string, std::vector<std::string>> map;
};
```

Populated incrementally by the runtime/proof_checker as theorems are
translated:

1. Before translating theorem `T`, compute `axioms(P_T)` from `P_T` and
   `map` (the recursive closure).
2. After successful translation, insert `map[T.name] = axioms(P_T)`.

Bazel's `fol_proof` dependency DAG guarantees acyclicity, so a single
topological pass per build suffices.

### 3.3 Pass shape

```cpp
namespace logic::proof::translate::axiom_rewrap {

struct RewrapResult {
    Program<nd::Instr> proof;       // proves H → φ (no axiom Use/SchemaInst)
    FormulaHandle      wrapped_goal; // H → φ
    std::vector<std::string> axioms; // axioms(P), lex-sorted (defines H)
};

class AxiomRewrap {
public:
    AxiomRewrap(GlobalContext& ctx,
                FormulaHandle goal_formula,    // original φ
                const TheoremAxiomMap& theorem_axioms);
    util::Result<RewrapResult> apply(const Program<nd::Instr>& in);
};

}
```

`apply` is total on iota-free ND programs that the ND verifier accepts.
It can fail (return Error) only if:
- An axiom referenced by `Use`/`SchemaInst` is not registered in
  `GlobalContext` (caller bug; identical to what NDVerifier rejects).
- A theorem referenced by `Use(T)` has no entry in `TheoremAxiomMap`
  (build-system bug; theorem was cited before its own translation).

### 3.4 Rewrap algorithm

**Pass 1 — analysis** (single linear scan over `in.instrs`):
- Reject any `SchemaInst` (input-gate; see §2.4 — schema elimination is
  upstream).
- Collect `direct_axioms = {name : Use(name)}` whose `name` resolves to
  an axiom in `GlobalContext`.
- Collect `cited_theorems = {name : Use(name)}` whose `name` resolves
  to a theorem.
- Compute
  `axioms(P) = direct_axioms ∪ ⋃_{T ∈ cited_theorems} theorem_axioms[T]`.
- Sort `axioms(P)` lex; emit canonical `H` formula handle.

**Pass 2 — emit** (build a new `Program<nd::Instr>` from scratch):
1. Emit `Assume(h_index, H)` — opens an assumption scope on `H`.
2. For each `A_i` in canonical order (lex), emit the extraction chain
   that lands `A_i` on the stack; record `(A_i.name → StepRef)` in a
   `axiom_step_table`.
3. Walk `in.instrs` in order. For each op:
   - `Use(A)` where `A ∈ direct_axioms`: drop the op; record
     `(in-StepRef → axiom_step_table[A])` in a `step_remap` table.
   - `Use(T)` where `T ∈ cited_theorems`: emit unwrap macro (§2.3):
     `Use(T)` followed by an `and_intro` chain over
     `{axiom_step_table[A_i] : A_i ∈ theorem_axioms[T]}`, then
     `implies_elim`. Record StepRef remap.
   - Any other op: emit a structural copy with all internal StepRef /
     TermRef fields rewritten through `step_remap`.
4. After the input's `Qed` op, emit `ImpliesIntro(<qed-target's
   remapped StepRef>)`, then a new `Qed` referencing that index. Close
   the assumption scope.

**StepRef remapping** is mechanical: each op's `StepRef` fields are
looked up in `step_remap` (identity if absent). Insertion of new ops
shifts indices; the remap table tracks the shift. Implementation
detail, not a math concern.

**TermRef remapping**: `Fix`-bound `TermRef`s are not relocated by the
rewrap (the body's `fix` ops emit unchanged), so identity remap
suffices for terms.

## 4. Per-op rewrap schema

For each ND op kind, what `axiom_rewrap` emits:

| Input op                       | Rewrap output                                             |
|--------------------------------|-----------------------------------------------------------|
| `Use(A)` — `A` axiom           | (drop, alias to `axiom_step_table[A]`)                    |
| `Use(T)` — `T` theorem         | `Use(T) ; <and_intro chain> ; ImpliesElim`                |
| `SchemaInst(_, _)`             | (input-gate reject: schema_elim runs upstream; see §2.4)  |
| `Assume`, `Let`, `Fix`         | structural copy                                           |
| `AndIntro`, `AndElimL/R`       | structural copy                                           |
| `OrIntroL/R`, `OrElim`         | structural copy                                           |
| `ImpliesIntro`, `ImpliesElim`  | structural copy                                           |
| `NotIntro`, `NotElim`          | structural copy                                           |
| `BottomElim`                   | structural copy                                           |
| `IffIntro`, `IffElimL/R`       | structural copy                                           |
| `ForallIntro`, `ForallElim`    | structural copy                                           |
| `ExistsIntro`, `ExistsElim`    | structural copy                                           |
| `DoubleNegElim`, `ExcludedMiddle`, `ClassicalAbsurd`, `Peirce` | structural copy |
| `IotaElim`                     | (input-gate reject: must be iota-free; iota_elim runs first) |
| `EqSubst`, `EqSym`             | (input-gate reject: deprecated; see EQ_SUBST_DEPRECATION) |
| `Qed`                          | replaced by `ImpliesIntro + Qed` at the end (§3.4 step 4) |

### 4.5 Extraction chain (concrete formula)

`H = (((A_1 ∧ A_2) ∧ A_3) ∧ … ∧ A_n)`. To extract `A_i` from `h: H`:

```
h_n     := h                                      # H itself
h_{k-1} := and_elim_l h_k    for k = n, n-1, …, 2 # peel off rightmost
                                                  # leaves prefix (((A_1 … ∧ A_{k-1}))
A_i extraction:
    if i == n:  h_A_n  := and_elim_r h_n
    else:       h_A_i  := and_elim_r h_{i+1}      # h_{i+1} = (… ∧ A_i ∧ A_{i+1}) → l-side is (… ∧ A_i)
                                                  # so A_i = and_elim_r ∘ and_elim_l chain
```

Concretely, for `n = 4`:
```
h_4 = h
h_3 = and_elim_l h_4    # (A_1 ∧ A_2) ∧ A_3
h_2 = and_elim_l h_3    # A_1 ∧ A_2
h_1 = and_elim_l h_2    # A_1   ← bound

h_A_4 = and_elim_r h_4  # A_4
h_A_3 = and_elim_r h_3  # A_3
h_A_2 = and_elim_r h_2  # A_2
h_A_1 = h_1             # A_1 (no further elim)
```

`n` `and_elim_l` ops + (`n − 1`) `and_elim_r` ops = `2n − 1` extraction
ops. Linear in axiom count; once per proof.

Edge cases:
- `n = 1`: `H = A_1`, `h_A_1 = h` directly. No `and_elim` ops emitted.
- `n = 0`: rewrap is a no-op (§1). `P' = P`, `wrapped_goal = φ`.

## 5. Soundness contract

**Theorem (axiom_rewrap soundness).** If
- `NDVerifier(φ, P) = Ok` against `GlobalContext` `ctx` (axioms + theorems registered),
- for every theorem `T` cited by `P`, `theorem_axioms[T]` is the
  transitive axiom closure of `T`'s wrapped proof,

then `axiom_rewrap.apply(P)` returns `Ok((P', H → φ, axioms(P)))` with
`NDVerifier(H → φ, P') = Ok` against `ctx' = ctx \ axioms(P)` (i.e.,
the same context with the wrapped axioms hidden — `P'` does not reference
them).

**Proof sketch.** Induction on `in.instrs` walk in pass 2.

- *Boundary wrap (assume + extracts + implies_intro)*: classical ND
  deduction theorem. The verifier's `assume` rule opens a scope with
  `H` on the assumption stack; `implies_intro` discharges it,
  producing `H → φ` from `φ`. Soundness is the standard ND
  meta-theorem.
- *`Use(A)` drop with alias*: any downstream reference to `Use(A)`'s
  StepRef formerly produced `A`; now it dereferences `axiom_step_table[A]`,
  which holds the same formula `A` (built by the extraction chain).
  The verifier sees the same formula at the same logical position.
- *`SchemaInst(A, σ)` → ForallElim chain*: ND's `SchemaInst` and
  `ForallElim` produce the same instantiated formula (`SchemaInst` is
  sugar). Replacement is verifier-equivalent.
- *`Use(T)` unwrap macro*: `Use(T)` in `P'` now binds `H_T → T` (the
  wrapped form, per the registry post-rewrap). The `and_intro` chain
  builds `H_T` from the cached `axiom_step_table` extracts (well-typed:
  `axioms(T) ⊆ axioms(P)` by definition). `implies_elim` yields `T`.
  Downstream references see `T`, matching the original `Use(T)`'s
  contribution.
- *Other ops*: structural copy; verifier behavior unchanged modulo
  StepRef remap (which is a bijection on the body's step indices,
  shifted by the prelude size).

The composition of these local preservations gives the global theorem. ∎

**Soundness gate.** `axiom_rewrap.apply` runs `NDVerifier(H → φ, P')`
on its output before returning Ok. A translator bug surfaces as a
boundary `Error`, never as a silently-unsound proof.

## 6. Completeness contract

**Theorem (axiom_rewrap completeness).** For every ND program `P` that
the input gate accepts (NDVerifier passes; iota-free; theorem
registry complete), `axiom_rewrap.apply(P)` returns `Ok(_)`.

**Proof.** The rewrap is total:
- Axiom-set computation terminates in one pass (proofs are finite).
- Transitive theorem closure terminates because the theorem
  dependency graph is acyclic (Bazel `fol_proof` rule enforces).
- Per-op emission is exhaustive over the ND `Instr` variant; every
  op kind has an emission rule in §4 (or an input-gate rejection,
  enumerated and total).
- StepRef remap is a function: every input StepRef has exactly one
  output StepRef (drop-with-alias is still a function on remap keys).

The output verifies by §5 soundness. ∎

## 7. Implementation phases

Each phase ships when its tests pass; nothing later starts until the
prior phase is green. Per `feedback_math_first_discipline`.

1. **TheoremAxiomMap + closure**.
   `src/proof/translate/axiom_rewrap/theorem_axioms.{h,cpp}`.
   API: `compute_transitive_axioms(program, registry) → vector<string>`.
   Tests: direct-only, one-theorem-dep, chained-theorem-dep, empty.
2. **Boundary wrap (no axiom-use body)**.
   Handle the `n = 0` and `n = 1` cases. Emit assume + extract +
   implies_intro skeleton. Tests: tautology proofs, single-axiom
   trivial proofs.
3. **Per-op structural copy + StepRef remap**.
   Emission for every non-Use ND op. Tests: a proof that uses no
   axioms but has every other op kind — output should be identical
   modulo prelude/postlude.
4. **`Use(A)` axiom drop**.
   Implement axiom_step_table + drop-with-alias for direct axiom Use.
   Tests: single-axiom multi-use, two-axiom mixed uses.
5. **`Use(T)` theorem unwrap macro**.
   Implement and_intro chain + implies_elim. Tests: theorem-uses-
   axiom, theorem-uses-theorem.
   (Former "Phase 5: SchemaInst expansion" removed — see §2.4; schemas
   are eliminated by an upstream ND→ND inline pass, so axiom_rewrap
   never sees SchemaInst ops.)
6. **End-to-end pipeline integration**.
   Wire axiom_rewrap between iota_elim and NDtoLKR in the build flow.
   Tests: minimal (1 axiom), two-axiom (extraction chain through pipeline),
   single-quantifier-nesting axiom. Verify each end-to-end CombProof
   under CombVerifier against the wrapped goal.

   **Known limitation (downstream, NOT axiom_rewrap):** when the wrapped
   goal has 2-level nested quantifiers on each side of the implication
   (e.g. `(∀x.∀y.r(x,y)) → ∀a.∀b.r(a,b)`, or anything wrapping ZFC
   axioms like `extensionality`), LKRtoComb's CombVerifier rejects with
   "is_fonet: C.2 expected a singleton binder, got part of size 2". This
   is the `LKR_TO_COMB_DESIGN.md §8` cotree-decomposition issue; the fix
   belongs in LKRtoComb's binder handling. axiom_rewrap's NDVerifier
   output gate accepts these inputs, and NDtoLKR processes them — only
   the final CombProof construction trips.

   Tests for the failing shapes are kept in `#if 0` blocks in
   `test/axiom_rewrap_test.cpp` (Phase 6 Tests 4 and 5) for easy
   re-enablement once the downstream limitation is addressed.

## 8. Test plan

Unit tests live in `test/axiom_rewrap_test.cpp` (new file). Integration
tests live in `test/lkr_to_comb_test.cpp` (extend existing fixture).

1. **`empty_axiom_set`** — proof of a propositional tautology (e.g.,
   `p → p` via `assume p; qed`). Rewrap is identity. `H` not constructed.
2. **`single_axiom_used_once`** — proof of `Q` from `axiom A: P → Q`
   and `axiom P_holds: P`. Wait — actually this needs two axioms. Use:
   `axiom A_to_B: A → B; claim derive_B (with A in scope... no).`
   Better fixture: `axiom A_true: A; claim A`. Trivial but exercises
   the wrap. Expected: `wrapped_goal = A → A`, prelude of one assume.
3. **`single_axiom_used_many_times`** — proof of `φ ∧ φ` from `axiom
   φ: ...`. Body uses `Use(φ)` twice; output uses `axiom_step_table[φ]`
   twice. Validates the cache.
4. **`multiple_axioms_lex_sort`** — proof using axioms `b_ax`, `a_ax`,
   `c_ax` in source order; output's `H` is `(a_ax ∧ b_ax) ∧ c_ax`.
5. **`schema_inst_rejected_at_input_gate`** — proof contains
   `SchemaInst`. `apply` returns Error pointing at the upstream
   `schema_elim` pass; nothing is emitted. (Schema expansion is not
   `axiom_rewrap`'s job; see §2.4.)
6. **`theorem_use_with_axioms`** — theorem `T` proved earlier from
   axiom `A`; current proof uses `T`. Output's `H` includes `A` (from
   the transitive closure); output emits unwrap macro at the
   `Use(T)` site.
7. **`theorem_chain`** — `T_2 uses T_1 uses A`. Wrapping `T_2`'s
   proof must include `A` in `H_{T_2}`.
8. **`ndverifier_gate_catches_bug`** — synthetic test where the
   emission is deliberately broken; output gate must reject.
9. **`end_to_end_zfc_singleton_in_pair`** — translate
   `singleton_in_pair` from `zfc/basics/ordered_pair.fol.proof`
   end-to-end through `iota_elim → axiom_rewrap → NDtoLKR →
   LKRtoComb`; assert `CombVerifier` accepts the output against the
   wrapped goal.

## 9. Edge cases

- **`axioms(P) = ∅`**: no-op short-circuit (§1, §4.5). `wrapped_goal
  = φ`, `P' = P`. Caller must handle the "no rewrap occurred" case
  (e.g., COMPLETENESS.md framing notes the CombProof witnesses `φ`
  directly).
- **Axiom referenced inside an `Assume` scope**: rewrap is transparent
  to scope nesting. The `axiom_step_table` entries are bound at the
  outer (post-`Assume H`) scope, so they're in scope everywhere in
  the body.
- **Fresh axiom name collision** with `h` / `h_A_i` shadowing: ND
  StepRefs are indices, not names. No source-level names are emitted
  by the rewrap; users never see them. No collision risk.
- **Theorem citing an unproven theorem** (forward reference): not
  possible — `TheoremAxiomMap` is built in topological order.
  Forward-ref attempts surface as missing keys in `theorem_axioms`
  during pass 1.
- **Schemas**: out of scope, handled upstream — `axiom_rewrap`'s input
  gate rejects any surviving `SchemaInst` (§2.4).

## 10. Open questions

- **Empty antecedent caching across theorems** — theorems with
  `axioms(T) = ∅` (rare; pure tautologies) are not wrapped. Their
  registry entries hold the unwrapped LKR program. The `Use(T)` rule
  must check `axioms(T)` and skip the unwrap macro when empty.
  Decided: handled by §2.3's last paragraph; not actually open, but
  flag here in case the implementation surfaces friction.
- **Canonical conjunction shape for `H`** — left-associated lex-sorted
  chosen (§2.5). Alternative: balanced binary tree (constant-depth
  extraction). Reject for now; the linear extraction chain runs once
  per proof, so depth doesn't matter for runtime. Revisit only if
  CombProof size becomes the bottleneck.
- **Goal mutation vs separate output goal** — `apply` returns a new
  `wrapped_goal` formula handle, separate from the input `φ`. The
  user-facing claim text remains `φ`; downstream pipeline stages
  receive `H → φ` as the goal. The runtime/proof_checker layer must
  understand this contract (the CombProof witnesses `H → φ`, which
  certifies `φ` under the trusted axioms). Documented here; no API
  ambiguity.

## 11. References

- `src/proof/translate/COMPLETENESS.md` §4.3 row "Axiom CombProofs" —
  the obligation this doc discharges.
- `src/proof/translate/IOTA_ELIM_DESIGN.md` — sibling ND→ND translator;
  reference for architecture style (axiom-normalization, pass shape).
- `src/proof/translate/LKR_TO_COMB_DESIGN.md` §4.11–§4.12 — `CloseByLemma`
  + lemma inlining; the downstream consumer of theorem registry
  entries that this translator produces wrapped forms for.
- `src/proof/nd/ops.h` — ND op variant; per-op rewrap table in §4
  enumerates every variant case.
- `src/proof/nd/verifier.h` — output gate.
- Mendelson, *Introduction to Mathematical Logic*, §2.4 — deduction
  theorem for first-order logic.
