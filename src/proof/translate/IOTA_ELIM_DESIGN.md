# ND-with-ι → ND-without-ι translator: design

Status: design document. No implementation yet. Supersedes
`WHOLE_PROOF_ELIM_DESIGN.md` (deleted as part of the revert that brought
the branch back to `d0302e3`). Companion to `ELIMINATE_DESCRIPTIONS.md`,
which specifies the goal-level formula rewrite this translator builds on.

## 0. Scope and architectural commitment

The translator is a **proof-level transformation**, not a verifier or
proof-system change. It takes an ND-with-ι proof of an ι-free goal and
produces an ND-without-ι proof of the same goal, suitable to hand to the
existing `NDtoLKR` translator. The downstream LKR and Comb verifiers see
only ι-free input, exactly as their interfaces already require.

ND's rule set is untouched. The introduction rule for ι remains the
single `iota_elim` rule (Hilbert ε critical axiom in proof form). No
new ND rules, no semantic changes to existing rules.

## 1. Mathematical contract

### The theorem we realize

**Hilbert-Bernays 2nd ε-theorem (Leisenring variant).** For any theory
`T` and any ι-free formula `G`:

    T ⊢_{ND-with-ι} G   iff   T ⊢_{ND-without-ι} G

The translator is the constructive witness of the forward direction.

The theorem assumes `T`'s axioms are ι-free. Our corpus (isa2fol's
bridge) has axiom-embedded ι. Section 4 handles this by deriving an
ι-free counterpart `T(A)` for each axiom-with-ι, using auxiliary
**existence** and **uniqueness** lemmas from the theory. Those
derivations live in the theory itself — no metatheoretic trust.

### Invariants the translator maintains

| ID  | Invariant                                                                              | Enforced by                |
|-----|----------------------------------------------------------------------------------------|----------------------------|
| I-1 | Output `Program<nd::Instr>` contains zero `Term::description` anywhere                 | post-pass scan             |
| I-2 | Output ND-verifies against the original (ι-free) goal                                  | NDVerifierGate             |
| I-3 | Every `iota_elim` in the input is replaced by an `exists_elim` in the output           | rewriter mechanics         |
| I-4 | Every axiom-use whose instantiated formula contains ι is redirected to a registered ι-free theorem `T(A)` | redirection table          |
| I-5 | `T(A)` is itself an ND-without-ι theorem derived from `A` + existence + uniqueness lemmas | AxiomTranslator's own gate |
| I-6 | The translator is stateless and pure (per `Pass<>` contract); no GlobalContext mutation visible from outside | pass discipline            |

**I-1 ∧ I-2 ⇒ soundness**: if the output is ι-free and ND-verifies,
then by Leisenring it's a valid ι-free witness of the goal.

### Where soundness can fail and what catches it

- Bad rewrite           → ND verifier rejects (I-2 fires).
- Missing lemma         → planning phase rejects with a specific error.
- Bad axiom translation → AxiomTranslator's ND verification rejects.
- Residual ι            → post-pass scan rejects (I-1 fires).

No "operationally trusted" steps. Every equivalence claim is either a
derivable ND step or caught by a verifier.

## 2. Architecture overview

```
                                   ┌────────────────────────┐
                                   │  GlobalContext + ctx   │
                                   │  - axioms              │
                                   │  - existence lemmas    │
                                   │  - uniqueness lemmas   │
                                   └───────────┬────────────┘
                                               │ (read-only)
   Program<nd::Instr>          ┌───────────────▼────────────────┐    Program<nd::Instr>
   (ND-with-ι)        ─────►   │      EliminateIotaInProof      │   ─────►  (ND-without-ι)
                               │           (Pass)               │
                               └────────┬───────────────────────┘
                                        │
                ┌───────────────────────┼──────────────────────────┐
                │                       │                          │
                ▼                       ▼                          ▼
        ┌──────────────┐   ┌─────────────────┐         ┌────────────────┐
        │IotaInventory │   │EliminationPlan  │         │AxiomTranslator │
        │(analysis)    │──►│(planning)       │         │(per-axiom)     │
        └──────────────┘   └────────┬────────┘         └────────────────┘
                                    │                          ▲
                                    ▼                          │
                           ┌──────────────────┐                │
                           │  ProofRewriter   │────────────────┘
                           │  (execution)     │ (resolves T(A) via cache)
                           └──────────────────┘
                                    │
                                    ▼
                           ┌──────────────────┐
                           │  NDVerifierGate  │
                           │  (validation)    │
                           └──────────────────┘
```

Each box: one class, one responsibility. Communication via plain data
structures; no shared mutable state.

Composes with the existing pipeline:

```
Program<nd::Instr>  ──[EliminateIotaInProof]──►  Program<nd::Instr>  ──[NDtoLKR]──►  Program<lkr::Instr>
   (may have ι)                                     (ι-free)                          (LKR, ι-free)
```

## 3. C++ interfaces

All in `namespace logic::proof::translate::iota_elim`. Separate from the
NDtoLKR machinery to keep concerns isolated.

### 3.1 Top-level pass (public surface)

```cpp
// src/proof/translate/iota_elim/eliminate_iota.h
class EliminateIotaInProof : public Pass<nd::Instr, nd::Instr> {
public:
    EliminateIotaInProof(GlobalContext& ctx,
                         const LemmaRegistry& lemmas,
                         AxiomTranslationCache& cache);

    util::Result<Program<nd::Instr>> apply(
        const Program<nd::Instr>& in) override;

private:
    GlobalContext&         ctx_;
    const LemmaRegistry&   lemmas_;
    AxiomTranslationCache& cache_;
};
```

NDtoLKR's integration point shrinks to ~6 lines:

```cpp
if (has_iota(in)) {
    EliminateIotaInProof elim(*ctx_, lemmas_, cache_);
    TRY_ASSIGN(out, elim.apply(in));
    return apply(out);   // recurse on ι-free input
}
```

### 3.2 LemmaRegistry — preconditions decoupled from algorithm

```cpp
// src/proof/translate/iota_elim/lemma_registry.h
struct LemmaRef {
    std::string             theorem_name;
    SentenceHandle          formula;
    std::vector<var_index>  free_var_pattern;   // for forall_elim chain
};

class LemmaRegistry {
public:
    static LemmaRegistry build(const GlobalContext& ctx);

    // Existence:  ∀x⃗. ∃u. B(x⃗, u)
    std::optional<LemmaRef> existence_for(FormulaHandle body) const;

    // Uniqueness: ∀x⃗, u, u'. (B(x⃗,u) ∧ B(x⃗,u') → u = u')
    std::optional<LemmaRef> uniqueness_for(FormulaHandle body) const;

private:
    std::map<FormulaHandle, LemmaRef> existence_by_body_;
    std::map<FormulaHandle, LemmaRef> uniqueness_by_body_;
};
```

Testable with a fake; lets us audit lemma availability separately.

### 3.3 IotaInventory — pure analysis

```cpp
// src/proof/translate/iota_elim/iota_inventory.h
class IotaInventory {
public:
    struct Site {
        FormulaHandle           body;                  // identity by interning
        std::vector<uint32_t>   use_steps;             // proof steps mentioning ι.B
        std::optional<uint32_t> existing_iota_elim;    // if introduced by iota_elim
        std::vector<uint32_t>   axiom_uses;            // `use axiom_X` steps with ι.B
    };

    static IotaInventory build(const Program<nd::Instr>& prog,
                                const GlobalContext& ctx);

    const std::map<FormulaHandle, Site>& sites() const;

    // Innermost-first order: ι terms whose bodies contain other ι come AFTER
    // their inner ones.
    std::vector<FormulaHandle> processing_order() const;
};
```

Reusable for metrics and diagnostics independent of rewriting.

### 3.4 EliminationPlan — planning that can fail early

```cpp
// src/proof/translate/iota_elim/elimination_plan.h
struct ScopeRange { uint32_t first; uint32_t last_inclusive; };

class EliminationPlan {
public:
    struct Action {
        FormulaHandle  body;
        ScopeRange     scope;
        std::string    witness_name;

        struct UseExisting    { uint32_t iota_elim_idx; };
        struct InsertFromLemma { LemmaRef existence_lemma; uint32_t insert_at; };
        std::variant<UseExisting, InsertFromLemma> source;

        // Axiom uses needing redirection: (step_idx, T(A)_theorem_name)
        std::vector<std::pair<uint32_t, std::string>> axiom_redirections;
    };

    static util::Result<EliminationPlan> compute(
        const IotaInventory&    inv,
        const LemmaRegistry&    lemmas,
        AxiomTranslationCache&  cache,        // may trigger axiom translations
        const GlobalContext&    ctx);

    const std::vector<Action>& actions() const;   // execution order
};
```

Dry-run mode: compute the plan and report **what would be needed**
without rewriting. Surfaces missing-lemma errors actionably and lets us
measure corpus reachability without implementing the rewriter.

### 3.5 AxiomTranslator + cache

```cpp
// src/proof/translate/iota_elim/axiom_translator.h
class AxiomTranslator {
public:
    struct Result {
        std::string           theorem_name;
        SentenceHandle        translated;          // T(A), iota-free
        Program<nd::Instr>    proof;               // proof of T(A), iota-free after recursion
    };

    AxiomTranslator(GlobalContext& ctx,
                    const LemmaRegistry& lemmas,
                    AxiomTranslationCache& cache);

    util::Result<Result> translate(SentenceHandle axiom);

private:
    AxiomShape classify_shape(SentenceHandle axiom) const;
    util::Result<Program<nd::Instr>> emit_proof_template(
        SentenceHandle axiom, const AxiomShape& shape);

    GlobalContext&            ctx_;
    const LemmaRegistry&      lemmas_;
    AxiomTranslationCache&    cache_;
    std::set<SentenceHandle>  in_flight_;          // cycle detection
};

class AxiomTranslationCache {
public:
    std::optional<AxiomTranslator::Result> lookup(SentenceHandle axiom);
    void store(SentenceHandle axiom, AxiomTranslator::Result result);

private:
    std::map<SentenceHandle, AxiomTranslator::Result> by_axiom_;
};
```

Each axiom translated once; cache reused across user proofs.

### 3.6 ProofRewriter — purely syntactic execution

```cpp
// src/proof/translate/iota_elim/proof_rewriter.h
class ProofRewriter {
public:
    static Program<nd::Instr> apply(
        const Program<nd::Instr>& in,
        const EliminationPlan&    plan,
        FormulaBuilder&           builder);

private:
    static Program<nd::Instr> insert_existence_iota_elim(...);
    static Program<nd::Instr> rewrite_iota_elim_to_exists_elim(...);
    static Program<nd::Instr> substitute_in_scope(...);
    static Program<nd::Instr> redirect_axiom_uses(...);
};
```

Trivially testable: given a synthetic plan, produces a deterministic
output. Doesn't think about whether the plan is *right* — that's the
planner's responsibility.

### 3.7 NDVerifierGate — the final safety net

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

Two independent checks (I-1 and I-2). Either failing is a translator
bug surfaced at the boundary, not at LKR time.

## 4. Axiom translation: from `A` to `T(A)` as a derived theorem

For an axiom `A = ∀x⃗. (Q(x⃗) ↔ R(ιu.B(x⃗,u), x⃗))`, the target form is
`T(A) = ∀x⃗. (Q(x⃗) ↔ ∃u. (B(x⃗,u) ∧ R(u, x⃗)))`.

`T(A)` is derived (not assumed) from:
- `A`                                  — the original axiom
- `E = ∀x⃗. ∃u. B(x⃗, u)`               — existence lemma for `B`
- `U = ∀x⃗, u, u'. (B(x⃗,u) ∧ B(x⃗,u') → u = u')`  — uniqueness lemma for `B`

### Proof template (ND-with-ι; recursively translated)

```
fix x⃗
h_ex   = forall_elim E, x⃗               -- ∃u. B(x⃗, u)
h_b    = iota_elim h_ex                  -- B(x⃗, ι.B)
h_a    = forall_elim A, x⃗                -- Q(x⃗) ↔ R(ι.B, x⃗)
h_u    = forall_elim U, x⃗                -- ∀u,u'. (B(x⃗,u) ∧ B(x⃗,u') → u=u')

-- forward: Q(x⃗) → ∃u. (B(x⃗,u) ∧ R(u, x⃗))
h_q    = assume Q(x⃗)
h_r    = iff_elim_l h_a, h_q             -- R(ι.B, x⃗)
h_conj = and_intro h_b, h_r              -- B(x⃗, ι.B) ∧ R(ι.B, x⃗)
h_exi  = exists_intro h_conj             -- ∃u. (B(x⃗,u) ∧ R(u,x⃗))
h_fwd  = implies_intro h_exi

-- reverse: ∃u. (B(x⃗,u) ∧ R(u, x⃗)) → Q(x⃗)
h_assu = assume ∃u. (B(x⃗,u) ∧ R(u, x⃗))
h_w    = exists_elim h_assu              -- fix w; B(x⃗,w) ∧ R(w, x⃗)
h_bw   = and_elim_l h_w
h_rw   = and_elim_r h_w
h_pair = and_intro h_bw, h_b             -- B(x⃗,w) ∧ B(x⃗, ι.B)
h_u_w  = forall_elim h_u, w
h_u_wi = forall_elim h_u_w, ι.B
h_eq   = implies_elim h_u_wi, h_pair     -- w = ι.B
h_riota= eq_subst h_eq, h_rw             -- R(ι.B, x⃗)
h_q_bk = iff_elim_r h_a, h_riota         -- Q(x⃗)
... close exists_elim, implies_intro

iff_intro h_fwd, h_rev
forall_intro x⃗
qed
```

The template parameterizes on the shape `(Q, B, R, arity)`. Multiple
templates cover the small set of axiom shapes appearing in the corpus
(single-ι; multiple-ι at same level; nested ι in body of outer ι). The
classifier `AxiomTranslator::classify_shape` picks the right template.

### Recursion termination

`AxiomTranslator::translate(A)` emits a proof of `T(A)` that contains
ι. That proof is fed back through `EliminateIotaInProof::apply` to make
it ι-free before being registered as a theorem.

**Termination invariant**:
- Each invocation of `EliminateIotaInProof` processes a finite multiset
  of unique ι bodies.
- Each axiom-translation proof has a bounded, statically-known number
  of ι sites (≤ k for a shape with k embedded ι in the axiom).
- The cache short-circuits repeated translations of the same axiom.
- An `in_flight_` set in `AxiomTranslator` detects cycles and refuses
  to recurse on an axiom currently being translated. (Cycles shouldn't
  arise in well-formed inputs; the check is defense-in-depth.)

**Bound**: recursion depth ≤ max nesting depth of ι in the axiom
graph — typically 0 or 1 for ZF, never deeper than the longest chain
of axiom-mentions-axiom-with-ι.

## 5. Testing strategy

| Test                              | Surface                                | Validates                                              |
|-----------------------------------|----------------------------------------|--------------------------------------------------------|
| `iota_inventory_test`             | IotaInventory in isolation             | Site detection, body grouping, depth ordering          |
| `axiom_translator_test`           | AxiomTranslator with fake LemmaRegistry | T(A) construction per shape; cycle detection           |
| `elimination_plan_test`           | EliminationPlan dry-run                | Missing-lemma errors; ordering invariants              |
| `proof_rewriter_test`             | ProofRewriter with synthetic plans     | Pure mechanical correctness                            |
| `eliminate_iota_corpus_test`      | Full pass on a curated bellwether set  | End-to-end on hand-picked real inputs                  |
| `translate_corpus --only-iota`    | The whole pipeline against bridge.fol.proof | Gate: bellwether 100% + ≥30% corpus before claiming done |

The corpus gate matters most. Per the user's standing feedback, we
measure against the real corpus EARLY and don't claim "done" on
unit-test success alone.

## 6. What this design deliberately rejects

- **One big function with phase-based dispatch** (the prior approach).
  Phases were if/else chains over instruction shapes; adding a shape
  required understanding the entire dispatcher. Replaced by uniform
  `IotaInventory → Plan → Rewrite`.
- **State mutation across pass calls**. The `Pass` contract is pure;
  cache and lemma registry are explicit parameters, not hidden globals.
- **Operationally trusted shadow axioms in ctx**. Layer-3
  `AxiomTranslator` emits proofs that ND-verify. Nothing in ctx
  becomes a "trust me" fact.
- **Coupling iota elimination to LKR translation**. They're separate
  passes that compose. LKR translation doesn't know iota exists.

## 7. File layout

```
src/proof/translate/iota_elim/
├── BUILD.bazel
├── eliminate_iota.h           # Public pass interface
├── eliminate_iota.cpp         # ~80 LOC: orchestration only
├── lemma_registry.h/cpp       # ~150 LOC
├── iota_inventory.h/cpp       # ~200 LOC
├── elimination_plan.h/cpp     # ~150 LOC
├── axiom_translator.h/cpp     # ~300 LOC (templates + cache)
├── proof_rewriter.h/cpp       # ~200 LOC (mechanical surgery)
└── nd_verifier_gate.h/cpp     # ~50 LOC

test/iota_elim/
├── BUILD.bazel
├── iota_inventory_test.cpp
├── axiom_translator_test.cpp
├── elimination_plan_test.cpp
├── proof_rewriter_test.cpp
└── eliminate_iota_corpus_test.cpp
```

Total estimated: ~1100 LOC across 8 files. The prior approach was
1127 LOC in one file. Same volume, composable, testable in isolation,
each module's invariant locally checkable.

## 8. Sequencing

1. **Survey lemma availability**: walk bridge.fol.def, list every
   axiom-embedded ι body; check the registry for matching existence
   and uniqueness lemmas. Report what's missing. This is the
   feasibility gate before any code.
2. **Pick the bellwether set**: ~20 proofs hand-picked from the prior
   corpus run's failure buckets. Commit as `BELLWETHER.txt`.
3. **Implement layer by layer**, tests at each layer:
   `LemmaRegistry → IotaInventory → EliminationPlan` (dry-run gate;
   re-run corpus to measure planner coverage) → `AxiomTranslator` →
   `ProofRewriter` → `NDVerifierGate` → top-level pass.
4. **Wire into NDtoLKR**, run the full corpus, hit the bellwether +
   30% gate.

## 9. References

- Hilbert & Bernays, *Grundlagen der Mathematik II*, second ε-theorem.
- A. C. Leisenring, *Mathematical Logic and Hilbert's ε-Symbol* (1969).
- `src/proof/translate/ELIMINATE_DESCRIPTIONS.md` — companion spec for
  the goal-level formula rewrite.
- `src/proof/translate/SPEC.md` — Hughes 2019 LK translation spec.
- `src/proof/translate/pass.h` — the `Pass<FromInstr, ToInstr>`
  interface this design plugs into.
