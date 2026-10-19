# ι elimination: load-time axiom normalization + proof-level pass

Status: design document. No implementation yet. Companion to
`ELIMINATE_DESCRIPTIONS.md`, which specifies the formula rewrite both
pieces of this design build on.

## 0. Two-piece architecture

ι elimination is split across two stages with disjoint responsibilities:

| Stage | When | What |
|---|---|---|
| **Axiom normalization** | At axiom load (registration time) | Apply `eliminate_descriptions` to any axiom/claim whose formula contains ι. Store the ι-free form. |
| **Proof-level pass** | At translation time | Translate user proofs containing `iota_elim` into ι-free ND proofs. |

Static ι (in axioms and goals) is handled at load time; dynamic ι (in
proofs, via `iota_elim`) is handled at translation time. The two stages
do not interact: by the time the proof-level pass runs, every axiom and
goal it sees is already ι-free.

This is a translator-level architecture — **ND's rule set is unchanged,
the ι term type is unchanged, the `iota_elim` rule is unchanged.**

## 1. Mathematical contract

### Soundness theorem (settled math)

**Hilbert-Bernays 2nd ε-theorem (Leisenring variant).** For any theory
`T` whose axioms are ι-free and any ι-free formula `G`:

    T ⊢_{ND-with-ι} G   iff   T ⊢_{ND-without-ι} G

The proof-level pass is the constructive witness of the forward
direction.

The theorem requires ι-free axioms; the axiom-normalization stage
ensures that requirement is always satisfied before the proof-level
pass runs.

### Why we normalize axioms instead of carrying ι through

The reverse-direction obstacle in axiom translation: for an axiom
`A = ∀x⃗. (Q ↔ R(ι.B, v))`, the translated form
`T(A) = ∀x⃗. (Q ↔ ∃u. (B(u) ∧ R(u, v)))` is provable from `A` only with
an auxiliary uniqueness lemma. Without uniqueness, `A` and `T(A)` are
inequivalent — under Hilbert ε's term-functionality reading, `A` is
strictly stronger.

Three responses:
1. **Treat `A` as the stronger statement** — requires uniqueness lemmas
   per axiom, partial completeness.
2. **Push to source** — require isa2fol to emit ι-free axioms.
3. **Normalize at load** — interpret static ι in axioms as Russell-
   without-uniqueness shorthand, identical to how we already handle
   goal-side ι.

Option 3 is what we already do for goals (see
`eliminate_descriptions(to_nnf(claim_root))` in
`nd_to_lkr.cpp:1211`); extending the same treatment to axioms is the
symmetric completion.

### The interpretation split

- **ι in static input (axioms, goals)**: Russell-without-uniqueness
  reading. `Q(ι.B)` *means* `∃x. (B(x) ∧ Q(x))`. Existence-presumption
  applies (axiom is sound iff `∃x.B(x)` holds in the theory; for ZF
  this is verified by extensionality + the standard ZF axioms).
- **ι introduced by `iota_elim` in proofs**: Hilbert ε reading.
  `ι.B` is a definite term denoting some witness of `B`, and the
  proof-level pass eliminates it via substitution under an
  `exists_elim` scope.

These two readings coexist without contradiction because they apply to
different objects (static formulas vs. derivation-internal terms). The
existing goal-side rewrite already makes this split.

### Why axiom normalization suffices (topological-order argument)

The pipeline processes a `.fol.def`/`.fol.proof` pair in dependency
order: axioms first, then each claim+proof in the order they appear
(which must already be a topological order of theorem dependencies,
since each proof can only `use` axioms or previously-proven
theorems). Combined with Path D's load-time and translation-time
normalization, this gives:

| Object class       | When ι is eliminated                                  | When registered in ctx |
|--------------------|-------------------------------------------------------|------------------------|
| Axioms             | At load (formula rewrite)                             | After normalization    |
| Claims             | At load (formula rewrite)                             | After normalization    |
| Theorems' formulas | At load (same as claims — they're the proof's goal)   | After proof verifies   |
| Theorems' proofs   | At proof translation (Layer 2 handles user iota_elim) | (proofs aren't stored in ctx) |

The consequence: **by the time any proof runs, every formula it can
reach via `use` is ι-free.** Axioms have been normalized; earlier
theorems' formulas are also normalized (their claims were normalized
at load). Layer 2 therefore never encounters ι via a `use` step —
only via the user's own `iota_elim` instructions.

This is what makes Path D's surface area small: Layer 2 has exactly
one source of ι to handle, the user's `iota_elim`. All the
machinery the previous design needed for axiom-embedded ι becomes
unnecessary.

The end state: ctx contains exclusively ι-free formulas. The
translated proof IR is ι-free. LKR and Comb see ι-free input
throughout. The system as a whole is description-free after
translation.

### Invariants

| ID  | Invariant                                                                              | Enforced by                |
|-----|----------------------------------------------------------------------------------------|----------------------------|
| I-1 | Every axiom in `ctx` has an ι-free formula                                              | axiom normalization at load |
| I-2 | The translator's input goal is ι-free                                                  | goal-side `eliminate_descriptions` (existing) |
| I-3 | Output `Program<nd::Instr>` contains zero `Term::description` anywhere                 | post-pass scan             |
| I-4 | Output ND-verifies against the (ι-free) goal                                            | NDVerifierGate             |
| I-5 | Every `iota_elim` in the input is replaced by an `exists_elim` in the output           | rewriter mechanics         |
| I-6 | The proof-level pass is stateless and pure (per `Pass<>` contract)                     | pass discipline            |

**I-3 ∧ I-4 ⇒ soundness for the proof-level pass** (Leisenring + the
ι-free axioms guaranteed by I-1).

### Where soundness can fail and what catches it

- Bad rewrite               → ND verifier rejects (I-4).
- Residual ι in output      → post-pass scan rejects (I-3).
- Bad axiom normalization   → load-time pre-condition: rewrite is
                              syntactic and idempotent; correctness
                              of `eliminate_descriptions` is tested
                              independently.
- Existence-presumption gap → load-time warning lists axiom-ι bodies;
                              user verifies satisfiability in theory.

No "operationally trusted" steps. No reverse-direction uniqueness
hidden anywhere.

## 2. Architecture overview

```
                                  ┌────────────────────────┐
       Source axioms              │  GlobalContext + ctx   │
       (may contain ι)   ─────►   │  - normalized axioms   │
                                  │  - normalized claims   │
                                  └───────────┬────────────┘
                                              │ (load-time normalization)
                                              │
                                              ▼
                          ┌─────────────────────────────────┐
                          │  AxiomNormalizer (load-time)    │
                          │  eliminate_descriptions on each │
                          │  axiom / claim before register  │
                          └─────────────────────────────────┘

                          ┌─────────────────────────────────┐
   Program<nd::Instr>     │   EliminateIotaInProof          │   Program<nd::Instr>
   (may have user ι)  ──► │   (Pass<nd::Instr, nd::Instr>)  │ ──► (ι-free)
                          └────────┬────────────────────────┘
                                   │
                ┌──────────────────┼─────────────────────────┐
                ▼                  ▼                         ▼
        ┌──────────────┐   ┌─────────────────┐      ┌────────────────┐
        │IotaInventory │──►│EliminationPlan  │─────►│ProofRewriter   │
        │(analysis)    │   │(planning)       │      │(execution)     │
        └──────────────┘   └─────────────────┘      └────────┬───────┘
                                                             │
                                                             ▼
                                                    ┌──────────────────┐
                                                    │  NDVerifierGate  │
                                                    │  (validation)    │
                                                    └──────────────────┘
```

Each box: one class, one responsibility. No shared mutable state. The
proof-level pass is pure: no GlobalContext mutation visible from
outside.

Composes with the existing pipeline:

```
Source ──[load + AxiomNormalizer]──► ctx (ι-free axioms)
                                       │
Program<nd::Instr> ──[EliminateIotaInProof]──► Program<nd::Instr> ──[NDtoLKR]──► Program<lkr::Instr>
   (may have user ι)                              (ι-free)                       (LKR, ι-free)
```

## 3. C++ interfaces

All new code in `namespace logic::proof::translate::iota_elim`, except
for axiom normalization which belongs in the loading path.

### 3.1 Axiom normalization (load-time)

Lives in `src/runtime/` or `src/core/global_context.cpp`, wherever
axiom registration is centralized. Single function:

```cpp
// src/core/axiom_normalize.h
namespace logic {

// Apply eliminate_descriptions to a sentence's formula. Idempotent.
// Returns the original sentence handle if no ι present.
SentenceHandle normalize_iota_in_sentence(
    FormulaBuilder& builder,
    SentenceHandle  s);

// Hook into the axiom registration path: called once per axiom or
// claim before it enters ctx. Logs a warning listing each ι body
// that gets normalized (for user audit of existence-presumption).
void normalize_and_register_axiom(
    GlobalContext& ctx,
    const std::string& name,
    SentenceHandle raw_axiom);

}  // namespace logic
```

Two trade-offs settled:
- **Always normalize, not opt-in**: idempotent and cheap. Surprising
  for users only if they expected Hilbert-ε reading of axiom ι, which
  the design explicitly rejects (see §1).
- **Log, don't fail**: existence-presumption is a theory concern, not
  a load-time error. We surface it for audit.

### 3.2 Top-level pass (proof-level)

```cpp
// src/proof/translate/iota_elim/eliminate_iota.h
class EliminateIotaInProof : public Pass<nd::Instr, nd::Instr> {
public:
    explicit EliminateIotaInProof(GlobalContext& ctx);

    util::Result<Program<nd::Instr>> apply(
        const Program<nd::Instr>& in) override;

private:
    GlobalContext& ctx_;
};
```

No `LemmaRegistry`, no `AxiomTranslationCache`, no
`AxiomTranslator`. The pass has exactly one dependency: read-only
access to `ctx` for resolving theorem references that survive the
substitution.

NDtoLKR integration:
```cpp
if (has_iota(in)) {
    EliminateIotaInProof elim(*ctx_);
    TRY_ASSIGN(out, elim.apply(in));
    return apply(out);   // recurse on ι-free input
}
```

### 3.3 IotaInventory — analysis layer

```cpp
// src/proof/translate/iota_elim/iota_inventory.h
class IotaInventory {
public:
    struct Site {
        FormulaHandle           body;                  // identity by interning
        std::vector<uint32_t>   use_steps;             // proof steps mentioning ι.B
        std::vector<uint32_t>   iota_elim_steps;       // iota_elim instructions producing ι.B
    };

    static IotaInventory build(const Program<nd::Instr>& prog);

    const std::map<FormulaHandle, Site>& sites() const;

    // Innermost-first order: ι.B' where B' contains ι comes AFTER its
    // inner ones. (Should not arise in practice for proof-derived ι
    // after axiom normalization, but the ordering remains for safety.)
    std::vector<FormulaHandle> processing_order() const;
};
```

Note: the inventory no longer needs to track `axiom_uses` because
axioms are ι-free at this point. The site information is purely about
user-introduced ι via `iota_elim`.

### 3.4 EliminationPlan — planning that fails early

```cpp
// src/proof/translate/iota_elim/elimination_plan.h
struct ScopeRange { uint32_t first; uint32_t last_inclusive; };

class EliminationPlan {
public:
    struct Action {
        FormulaHandle  body;
        ScopeRange     scope;                  // [first_use, last_use]
        std::string    witness_name;           // fresh symbolic name
        uint32_t       primary_iota_elim_idx;  // the introducing iota_elim
        std::vector<uint32_t> redundant_iota_elims;  // dropped or merged
    };

    static util::Result<EliminationPlan> compute(
        const IotaInventory& inv,
        const Program<nd::Instr>& prog);

    const std::vector<Action>& actions() const;   // innermost-first
};
```

The planner has only one job: for each ι site, decide the scope and
witness name. It cannot fail for any reason other than malformed
input (e.g., an `iota_elim` whose source ∃ isn't derived) — the
axiom-translation complexity is gone.

### 3.5 ProofRewriter — purely syntactic execution

```cpp
// src/proof/translate/iota_elim/proof_rewriter.h
class ProofRewriter {
public:
    static Program<nd::Instr> apply(
        const Program<nd::Instr>& in,
        const EliminationPlan&    plan,
        FormulaBuilder&           builder);

private:
    static Program<nd::Instr> rewrite_iota_elim_to_exists_elim(
        const Program<nd::Instr>&, const EliminationPlan::Action&);
    static Program<nd::Instr> substitute_iota_in_scope(
        const Program<nd::Instr>&, FormulaHandle iota_body,
        const std::string& witness_name, ScopeRange scope);
    static Program<nd::Instr> drop_redundant_iota_elims(
        const Program<nd::Instr>&, const EliminationPlan::Action&);
};
```

### 3.6 NDVerifierGate — the safety net

```cpp
// src/proof/translate/iota_elim/nd_verifier_gate.h
class NDVerifierGate {
public:
    static util::ResultStatus verify(
        const Program<nd::Instr>& rewritten,
        FormulaHandle             original_goal,
        const GlobalContext&      ctx);

private:
    static util::ResultStatus check_iota_free(const Program<nd::Instr>&);
    static util::ResultStatus check_nd_valid(
        const Program<nd::Instr>&, FormulaHandle, const GlobalContext&);
};
```

Two independent checks (I-3 and I-4). Either failing is a translator
bug surfaced at the boundary.

## 4. Edge cases (verified by code inspection)

### Edge cases that already work

| # | Case | Handled by |
|---|---|---|
| 1 | Axiom-ι body with outer-quantified variables (`∀A,B. Q(ιu.R(A,B,u))`) | `shift_term` in `elim_in_pred` (`formula.cpp:971`) |
| 2 | Nested ι in ι body (`P(ιu.Q(u, ιv.R(v)))`) | `elim_in_desc_body` recursion (`formula.cpp:962`) |
| 3 | ι in equation predicates (`eq(ι.B, t)`) | `eq` is a 2-place predicate; same machinery |
| 4 | ι in multiple args of one predicate (`eq(ι.A, ι.B)`) | first-ι picked, recursive call peels rest |
| 5 | Negative occurrence (`¬Q(ι.B)`) | NNF dual in `elim_in_pred:985` |
| 6 | `@def(P)` annotations | predicate preserved; only ι args rewritten |
| 7 | Idempotency on ι-free formulas | dispatcher passes through unchanged |
| 8 | Multiple `iota_elim` of same body | planner merges scopes / drops redundants |
| 9 | User `iota_elim` body with fixed vars from outer scope | existing `description_body_accessible` check |
| 10 | `@def`-marked axioms | `@def` shape preserved by normalization |

### Edge case 11 (schema-parameter ι args): confirmed gap, design adjustment specified

Schema axioms in bridge.fol.def carry ι inside schema-parameter args:

```
schema ArithSimp_2enat_diff_split [P(1)]:
    forall a. forall b. (P((iota _v0. Arith_2ediff(a, b, _v0))) <-> ...)
```

Internally: `∀a. ∀b. SchemaVar{id=0, args=[Term::description(...)]} ↔ ...`.

The previous (reverted) `elim_desc_dispatch` in `src/core/formula.cpp`
passed SchemaVar through unchanged:

```cpp
if (f.is_schema_var()) {
    return negate ? b.make_not(h) : h;   // ι in args NOT eliminated
}
```

So as-was, axiom-normalization would leave ι in SchemaVar args
untouched, and the instantiated formula at proof time would still
contain ι — defeating Path D.

**Resolution**: when re-introducing `eliminate_descriptions`, extend
the SchemaVar arm to apply the Russell rewrite to ι args, mirroring
`elim_in_pred`'s treatment of concrete predicates:

```
SchemaVar{id, args=[..., ι.B, ...]}
    ↦  ∃x. (B(x) ∧ SchemaVar{id, args=[..., x, ...]})   (positive polarity)
    ↦  ∀x. (¬B(x) ∨ SchemaVar{id, args=[..., x, ...]})  (negative polarity)
```

De Bruijn discipline: replace the ι arg with `Gen(0)` (new ∃-bound
var); shift other args up by 1 via `shift_term`; recursively peel any
remaining ι in other args (matches `elim_in_pred`'s recursive call at
`formula.cpp:995`).

Soundness at instantiation: at use-time, `bindings[id]` provides the
schema-parameter's body. After substitution, `Gen(0)` resolves to the
new ∃-bound variable. Result: `∃x. (B(x) ∧ instantiated-P(x))` —
identical to the Russell rewrite of `P(ι.B)`. The schema-instantiation
machinery (`instantiate_schema` in `formula.cpp:588`) already recurses
into description bodies via `instantiate_schema_in_term`, so the
rewrite composes cleanly.

This is a small addition to `elim_desc_dispatch` (~20 LOC), captured
in the implementation sequencing in §8.

### Other edge cases for awareness (not blockers)

| # | Case | Concern |
|---|---|---|
| 12 | Axiom whose ι body is unsatisfiable in the theory | Existence-presumption gap. Mitigation: load-time warning lists ι bodies; user audits. |
| 13 | Axiom-graph cycles (axiom A's ι body references ι from axiom B) | Normalize in load order (dependencies-first by `include` graph; already the existing discipline). |

## 5. Testing strategy

| Test                              | Surface                                | Validates                                              |
|-----------------------------------|----------------------------------------|--------------------------------------------------------|
| `axiom_normalize_test`            | `normalize_iota_in_sentence` in isolation | All edge cases 1-7 above                               |
| `iota_inventory_test`             | IotaInventory in isolation             | Site detection, body grouping, depth ordering          |
| `elimination_plan_test`           | EliminationPlan                        | Scope determination, witness naming, redundancy        |
| `proof_rewriter_test`             | ProofRewriter with synthetic plans     | Pure mechanical correctness                            |
| `eliminate_iota_corpus_test`      | Full pass on a curated bellwether set  | End-to-end on hand-picked real inputs                  |
| `schema_iota_test`                | Edge case 11                           | Schema instantiation composes with normalized form     |
| `translate_corpus --only-iota`    | The whole pipeline against bridge.fol.proof | Gate: bellwether 100% + ≥80% corpus before claiming done |

The corpus gate target rises from 30% (the old Path-1 estimate) to
≥80% because the design is now complete — failures should be rare and
attributable to non-iota issues (e.g., the EqSym
`close_flat` gap we already know about).

## 6. What this design deliberately rejects

- **AxiomTranslator with T(A) derivation**. Would require uniqueness
  lemmas per axiom and produce only partial completeness. Replaced by
  load-time normalization.
- **Per-step T-rewrite (Architecture B)**. Heavier than necessary;
  load-time normalization achieves the same end result with less
  code.
- **Operationally trusted shadow axioms in ctx**. No "trust me" facts
  introduced anywhere.
- **Coupling iota elimination to LKR translation**. The two passes
  compose; LKR translation doesn't know iota exists.
- **One big function with phase-based dispatch**. Each layer is one
  class with one responsibility; testable in isolation.

## 7. File layout

```
src/core/
└── axiom_normalize.h/cpp           # ~80 LOC, load-time normalization

src/proof/translate/iota_elim/
├── BUILD.bazel
├── eliminate_iota.h                # Public pass interface
├── eliminate_iota.cpp              # ~60 LOC: orchestration only
├── iota_inventory.h/cpp            # ~150 LOC
├── elimination_plan.h/cpp          # ~120 LOC
├── proof_rewriter.h/cpp            # ~180 LOC (mechanical surgery)
└── nd_verifier_gate.h/cpp          # ~50 LOC

test/
├── axiom_normalize_test.cpp        # Edge cases 1-10
├── schema_iota_test.cpp            # Edge case 11
test/iota_elim/
├── BUILD.bazel
├── iota_inventory_test.cpp
├── elimination_plan_test.cpp
├── proof_rewriter_test.cpp
└── eliminate_iota_corpus_test.cpp
```

Total estimated: ~640 LOC across 7 files for new translator code, plus
~360 LOC re-introduced for `eliminate_descriptions` and its SchemaVar
extension (`src/core/formula.{h,cpp}`, ported from the reverted
commit `007b5e2` with the §4 edge-case-11 fix applied). Grand total
~1000 LOC. Compare to ~1100 LOC for the previous Path 1 design and
1127 LOC for the deleted phase-based implementation. Path D is *both
simpler and more complete* than the alternatives.

## 8. Sequencing

Prerequisite work (none of this exists at the current branch HEAD;
`eliminate_descriptions` was reverted with the prior iota work and
needs re-introduction):

0a. **Re-introduce `eliminate_descriptions`** in `src/core/formula.cpp`
    + declaration in `src/core/formula.h`. Port from the reverted
    commit `007b5e2` (~341 LOC). Spec already exists at
    `src/proof/translate/ELIMINATE_DESCRIPTIONS.md`.
0b. **Extend `elim_desc_dispatch` to handle SchemaVar args** (edge
    case 11). Add Russell rewrite for SchemaVar with ι args, ~20 LOC.
    Test on both single-ι-arg and multi-ι-arg schema bodies, plus
    nested-quantifier cases.

Main work:

1. **Implement axiom normalization** at the load path, with the
   warning emission. Add `axiom_normalize_test` covering edge cases
   1-10 and the SchemaVar extension from 0b.
2. **Pick the bellwether set**: ~20 proofs hand-picked from the prior
   corpus run's failure buckets. Commit as `BELLWETHER.txt`.
3. **Implement the proof-level pass** layer by layer:
   `IotaInventory → EliminationPlan → ProofRewriter →
   NDVerifierGate → top-level pass`. Test each layer in isolation.
4. **Wire into NDtoLKR**, run the full corpus, hit the bellwether +
   80% gate.

## 9. References

- Hilbert & Bernays, *Grundlagen der Mathematik II*, second ε-theorem.
- A. C. Leisenring, *Mathematical Logic and Hilbert's ε-Symbol* (1969).
- `src/proof/translate/ELIMINATE_DESCRIPTIONS.md` — formula-rewrite
  spec.
- `src/proof/translate/SPEC.md` — Hughes 2019 LK translation spec.
- `src/proof/translate/pass.h` — `Pass<FromInstr, ToInstr>` interface.
