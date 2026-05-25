# Stage 2 Phase 6: demand propagation through combining elims

> **Status.** Draft 2026-05-26. Refines [CUT_MINIMAL_DESIGN.md] §5d / §5e.
> Math-first per [[math-first-discipline]]: spec here, tests in
> `test/cut_minimal_demand_through_combining_test.cpp`, then impl, then
> obligation flip.

## 0. Problem statement

The four combining-elim emitters built in Phase 5d / 5e —
`emit_implies_elim_full`, `emit_iff_elim_full`, `emit_or_elim_full`,
`emit_exists_elim_full` — accept a `target_pos` but no `DemandPath`. The
dispatcher silently drops `norm_path` at the call site
(`dispatcher.cpp:419-447`):

```
} else if constexpr (std::is_same_v<T, nd::IffElimL>) {
    return emit_iff_elim_full(dcc, std::move(shadow), op,
        /*is_left=*/true, target_pos, out);   // norm_path discarded
}
```

The emitters then close their internal "result-side" sequent against
`target_pos` (or use raw `AxiomLit{target_pos, psi_pos}`) under the
assumption that `target_pos`'s content equals NNF(φ), where φ is the
combining-elim's own result-formula. This holds when the upstream
consumer passed `DemandNone` — but when an upstream `forall_elim` or
`and_elim_l/r` has prepended a non-trivial demand, the consumer has
already pre-rewritten `target_pos`'s content to the
*demand-decomposed* shape NNF(apply_path(φ, norm_path)), while the
emitter still produces the un-decomposed dual ¬NNF(φ) on its
result-side.

The mismatch manifests as `emit_close`'s "a is X, b is Y" precondition
violation and as `AxiomLit`'s "indices do not point to atomic
literals" / "literals are not duals" — exactly the ZFC ordered_pair
failures (18/19 at nd_to_lkr).

## 1. Controlling theorem (demand-aware closure)

### 1.1 Contract on `translate_step(target_pos, norm_path)`

Let `S` be a combining-elim step with result-formula φ. Let `apply_path`
be the NNF-level decomposition induced by a DemandPath:

```
apply_path(φ, ε)                       = φ
apply_path(∀x.ψ, Instance(t) :: π)     = apply_path(ψ[x:=t], π)
apply_path(ψ ∧ θ,  AndLeft :: π)       = apply_path(ψ, π)
apply_path(ψ ∧ θ,  AndRight :: π)      = apply_path(θ, π)
apply_path(¬¬ψ,    DoubleNeg :: π)     = apply_path(ψ, π)
apply_path(ψ ↔ θ,  IffLeft :: π)       = ⊥  -- never reached (see §1.4)
```

(`apply_path` is total on the demand kinds promoted by projection elims
that are LEGAL upstream of a combining-elim. AndLeft/Right on an
iff-resulting step is illegal — see §1.4.)

**Precondition** (upstream consumer guarantee): on entry to
`translate_step`,
```
shadow.entries[target_pos] = NNF( apply_path(φ, norm_path) )
```

**Postcondition** (emitter obligation): the LKR program appended to
`out` extends `shadow` into a verifying derivation whose end-sequent
contains both `shadow.entries[target_pos]` and its NNF-dual at some
emitter-allocated position.

### 1.2 Soundness invariant for the dual-side construction

For each combining-elim, the emitter's construction produces an
internal "result-side" entry whose content is NNF(¬φ) — the
*un-decomposed* dual. To match the consumer's demand-peeled
`target_pos`, the emitter must apply the same `DemandPath` decomposition
in the LKR-dual direction on that internal entry.

The LKR rules implementing demand decomposition on the negative side:

| DemandPath step | NNF-neg shape | LKR rule emitted | Result shape |
|---|---|---|---|
| `Instance(t, lkr_ref)` | ∃x.NNF(¬ψ) | `Exists{principal, witness=lkr_ref}` | NNF(¬ψ)[x:=t] |
| `AndLeft` | NNF(¬ψ) ∨ NNF(¬θ) | `Or{principal}`, keep LEFT child | NNF(¬ψ) |
| `AndRight` | NNF(¬ψ) ∨ NNF(¬θ) | `Or{principal}`, advance to RIGHT child | NNF(¬θ) |
| `DoubleNeg` | NNF(ψ) | no-op | NNF(ψ) |

These are exactly the rules already encoded in `apply_path_and_close`
(dispatcher.cpp:75-132) for the `nd::Use` / `nd::SchemaInst` / `nd::Assume`
/ `nd::ExistsElim` leaves. The combining-elim fix reuses this helper.

### 1.3 The fix, per family

For each emitter, identify every closure call site that pairs
`target_pos` (the consumer's view) with an internal dual entry, and
route through `apply_path_and_close` instead of `emit_close`/`AxiomLit`.
Closure sites that pair *operand-vs-operand-dual* (not touching
`target_pos`) keep their existing `emit_close` calls with empty
`DemandPath` — they see structurally-dual pairs by construction.

| Emitter | Target-touching close sites | Operand-only close sites |
|---|---|---|
| `emit_implies_elim_full` | RIGHT-of-And close [psi=¬B vs target_pos] | LEFT-of-And close [phi=A vs neg_ant=¬A] |
| `emit_iff_elim_full` (IFF_L) | RIGHT-of-And close [psi=¬B vs target_pos] | LEFT-of-And close [phi=A vs cut_op_idx=¬A] |
| `emit_iff_elim_full` (IFF_R) | LEFT-of-And close [phi=¬A vs target_pos] | RIGHT-of-And close [psi=B vs cut_op_idx=¬B] |
| `emit_or_elim_full` | Both inner-RIGHT closes [¬C vs target_pos copy] | Both inner-LEFT closes [A/B vs ¬A/¬B] |
| `emit_exists_elim_full` | Forwarded recursion on `op.body` (a closer) | — |

### 1.4 Excluded combinations

`DemandIffLeft` / `DemandIffRight` are produced by the dead projection
emitters `projections::emit_iff_elim_l/r` (Phase 2); the dispatcher
routes IFF_ELIM directly to combining (Phase 5e.6) and never recurses
through those descriptors. The combining-elim fix therefore does not
need to handle IFF demand steps.

If a future projection refactor reintroduces IFF demands above a
combining-elim, the existing `apply_path_and_close` already handles
them (treats them as Or-decomposition on the negative side) — the
combining-elim fix inherits that for free.

## 2. Subgoal-local position remap

The combining-elim And-splits (`emit_and_split_local`) remap parent
positions to child-shadow positions. The fix must:
- Compute `target_pos_in_subgoal = split.{left,right}_remap.at(target_pos)`.
- Pass `target_pos_in_subgoal` (not raw `target_pos`) into
  `apply_path_and_close`.

Existing emitters already compute these remaps; the fix just routes the
remapped index through `apply_path_and_close`.

## 3. Empty-path equivalence (no-regression invariant)

When `norm_path` is empty (the Phase 5d/5e baseline), the chain loop in
`apply_path_and_close` is empty, and the call reduces to `emit_close`
on the same arguments. Hence:

> **Lemma (empty-path).** For empty `norm_path`, the fixed combining-elim
> emitter is observationally equivalent to its Phase 5e baseline.

This pins the existing 12 E2E dispatcher tests as a regression suite
(no test changes needed).

For `emit_implies_elim_full` specifically, the LEFT-of-And close is
*also* upgraded from raw `AxiomLit{0,1}` to `emit_close` to drop the
atomicity assumption on the antecedent A. This is a strict
generalization (literals close via the same AxiomLit base case inside
`emit_close`) — no regression.

## 4. Proof obligation matrix

For each combining-elim × each demand kind, a representative test that
exercises the closure path under that demand.

| Test ID | Combining-elim | Demand | Sketch |
|---|---|---|---|
| `T-IE-N` | implies_elim | NONE | Existing: `Test 10` baseline. |
| `T-IE-I` | implies_elim | INSTANCE | `((∀x.P(x)) → (∀y.Q(y))), (∀x.P(x)) ⊢ Q(c)` via forall_elim of the impl's consequent. |
| `T-IE-AL` | implies_elim | ANDLEFT | `(P → (A ∧ B)), P ⊢ A` via and_elim_l. |
| `T-IL-N` | iff_elim_l | NONE | Existing baseline. |
| `T-IL-I` | iff_elim_l | INSTANCE | `(P ↔ ∀x.Q(x)), P ⊢ Q(c)` — eq_symmetric-shaped. |
| `T-IL-AL` | iff_elim_l | ANDLEFT | `(P ↔ (A ∧ B)), P ⊢ A`. |
| `T-IR-I` | iff_elim_r | INSTANCE | `(∀x.Q(x) ↔ P), P ⊢ Q(c)`. |
| `T-OE-I` | or_elim | INSTANCE | `(A ∨ B), (A → ∀x.P(x)), (B → ∀x.P(x)) ⊢ P(c)`. |
| `T-EE-I` | exists_elim | INSTANCE | `(∃y.∀x.P(x,y)) ⊢ P(c, witness)`. |
| `T-ZFC` | integration | — | `eq_symmetric` from ZFC ordered_pair compiles end-to-end. |

(`T-IE-AR`, `T-IL-AR`, `T-IR-{N,AL,AR}` are symmetric mirrors; one
representative per family is enough for the spec gate. Add if a bug
surfaces.)

## 5. Acceptance

The fix is accepted when:
1. All tests in `test/cut_minimal_demand_through_combining_test.cpp`
   pass (sound, complete on the spec matrix).
2. Existing `cut_minimal_*_test` suites stay green (no regression).
3. `comb_checker zfc/basics/ordered_pair.fol.def
   zfc/basics/ordered_pair.fol.proof zfc/basics/axioms.fol.def`
   reaches ≥ historical parity (≥ 6/19 OK; aim 19/19).

Per [[math-first-discipline]]: tests land first (RED), then impl
(GREEN), then obligation flip in a follow-up commit.
