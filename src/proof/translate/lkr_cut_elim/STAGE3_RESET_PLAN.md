# Stage 3 reset plan

**Status:** Steps 0–3 SHIPPED; Step 4 PARTIAL (B1 non-principal axiom/ROne +
B1 **principal axiom**); B0 now wired into `eliminate_cuts`; Step 4 remainder
+ 5 PENDING. The "reversed-W design question" that blocked the principal case
is RESOLVED: the 2026-05-31 weakening fix (`Weakening{idx}`=drop) makes the IR
uniform, so B1-principal grafts the surviving premise by drop+rotate. Back-end
now targets KS1 (`memory: project_lkr_ks1_pivot_2026_05_31`); Stage 3 itself
(LKR→LKR cut-elim) is unchanged by that pivot.
**Companion to:** `CUT_ELIM_DESIGN.md` (the math — unchanged by this plan).

## Progress log

| Step | What | Status | Commits |
|------|------|--------|---------|
| 0 | Delete reduce.{h,cpp}, reduce_test.cpp, BUILD entries | ✅ shipped | `b2e2557` |
| 1 | `Deriv::validate` — per-rule structural invariants, wired into `build()` | ✅ shipped | `a3db47a` |
| 2 | `additive_to_multiplicative` — B0 as a real pre-pass | ✅ shipped | `8ac3dd1` |
| 3 | `eliminate_cuts` worklist driver on (degree, topmost) | ✅ shipped | `5df5ca1` |
| 4 — B1 non-principal | RAx / ROne where cut formula isn't an axiom literal | ✅ shipped | `b4068a5` |
| 4 — B1 principal axiom | RAx where cut formula IS an axiom literal | ✅ shipped (drop+rotate graft) |
| 4 — B1 principal ROne | ROne where cut formula IS the truth literal | ⏳ pending |
| 4 — B2 ∧ vs ∨ | both orientations → two lower-degree cuts + reorder | ✅ shipped |
| 4 — B2 ∀ vs ∃ | needs B3 capture-avoiding subst | ⏳ pending |
| 4 — B3 capture-avoiding subst | needed by B2's ∀/∃ case | ⏳ pending |
| 4 — B4 permutation | cut not principal in one premise | ⏳ pending |
| 4 — B5 structural | W dead-cut, C duplication, X | ⏳ blocked* |
| 5 — Stage A | RLemma inlining | ⏳ pending |

\* "Blocked" = the reduction needs careful re-derivation against the IR's
verifier-direction conventions. The original engine got these wrong (the
05-27 audit). I am not landing them until the math is worked out
case-by-case against the IR convention — not the standard sequent-calc
convention the spec uses.

## The remaining design question (per case)

The IR is verifier-directed: `node.concl` is the verifier's top BEFORE
the rule fires; `child.concl` is the top AFTER. Different rules go
different directions relative to standard sequent calc:

- **Or** in IR: node has fewer entries (with disjunction); child has more
  (decomposed). Matches standard reading "node = conclusion, child =
  premise."
- **W** in IR: node has fewer entries; child has more (with added).
  REVERSED from standard W reading. In our IR, W going down *grows* the
  sequent.

Consequence: a reduction like dead-cut-W ("discard the other premise and
weaken") needs reframing in our IR. The standard reading puts W *below*
the cut in the proof tree (W's conclusion is the cut's premise side);
our IR reverses this. The old code's `try_dead_cut_W` got this wrong
(05-27 audit) by looking at `cut.left`'s top rule rather than walking
deeper into `left`'s subtree to find the W whose `added` IS the cut
formula at the principal slot.

Each remaining §5 case needs the same care: write down the reduction in
the IR's convention before coding it; do not transliterate from the
spec's standard-calc presentation. The case files (e.g., a future `b1.cpp`,
`b5.cpp`) should each open with that re-derivation as a comment so
future authors don't repeat the conversion in their head.

## Suggested next session

1. Pick ONE case to re-derive end-to-end (B1 principal axiom is the
   smallest non-trivial). Write the re-derivation as comments in
   `b1_principal.cpp`. Test (hand-built + a syllogism that surfaces the
   case after B0).
2. Then B5 W dead-cut (find the W deep in the cut-side subtree whose
   added is the cut formula at the cut slot; use its child as the base
   for the reduced subtree).
3. Then B5 contraction (the spec's duplication move — also needs care).
4. Then B2 (which needs B3 — capture-avoiding subst is a substantial
   sub-pass on its own).
5. Then B4 (permutation past unary/binary rules).
6. Then Stage A (lemma inlining).

Each case ships as its own commit per the math-first discipline:
spec-paragraph-as-comment → test → impl → green → commit.



## 1. Diagnosis (short)

The current `reduce.{h,cpp}` is the *third* attempt at LKR cut-elimination.
The spec (`CUT_ELIM_DESIGN.md` §7) explicitly opens by deleting the first
two as "engineering hacks". The third has regressed into the same shape:

- `reduce_cut` (reduce.cpp:624) is a chain of `try_*` functions that
  pattern-match individual cut configurations — same architecture as the
  `walk_reduce` / `try_strict_axiom_cut` / `try_linear_atom_cut` it was
  meant to replace, only with more cases.
- The foundational §4 step (additive→multiplicative + |Γ|·Contraction)
  was never built as a pre-pass. It was inlined as a helper
  (`wrap_with_weakenings`) *inside* the B2 ∧/∨ principal case. So every
  later "principal" case re-invents the bridge.
- The driver (reduce.cpp:702) is post-order child-first. The spec's
  measure (§5.1) is *topmost cut of maximal degree* via a worklist. Post-
  order can permute a cut past one of ≥ degree — exactly what the
  termination proof forbids — and misses reductions that only fire after
  permutation.
- `Deriv` carries implicit conventions (e.g. "for RWeaken, `child` is the
  POST-W sequent — bigger — and `node` is PRE-W — smaller"). Nothing in
  the type system or in test scaffolding enforces this. The 05-27 corpus
  bug (`try_dead_cut_W` assumed the opposite) was inevitable: tests hand-
  build Derivs and freely pick whichever convention they happen to want;
  the corpus exposes the mismatch because corpus Derivs come from
  `build()`.

The cost: each session adds a case or two, gets green unit tests on hand-
built Derivs, commits. Green doesn't mean correct under realistic inputs,
because the tests don't exercise the foundational issues. We are
polishing mortar on a cracked foundation.

## 2. Hard scope

**In scope.** Everything inside `src/proof/translate/lkr_cut_elim/` plus
`test/reduce_test.cpp` and `test/deriv_test.cpp`. The goal of the reset
is a Stage 3 engine that satisfies the §8 round-trip property *on its own
terms* — `LKRVerifier`-accepted input → cut-free, `LKRVerifier`-accepted
output, same end-sequent — independent of any downstream consumer.

**Out of scope (do not touch under this plan).**

- `lkr_weak_elim/` (Stage 4) — 100% unrelated to Stage 3 per user
  directive. Its DESIGN.md and code may mention `eliminate_cuts` in
  comments; those comments are stale-once-deleted but the code does not
  call into Stage 3. Leave it alone.
- `lkr_to_comb/` and `comb_checker.cpp` — downstream of Stage 3. The
  current `comb_checker` does not wire Stage 3 (the call site is
  commented out). Do not re-wire as part of this reset. Wire-up is a
  separate decision after Stage 3 is done.
- `CUT_ELIM_DESIGN.md` — the math is fine. This plan does not amend it.
- `CUT_HANDLING_ROADMAP.md` and `lkr_to_comb/CUT_S15_DESIGN.md` mention
  `eliminate_cuts` in prose; doc-only references, no code action needed.

## 3. Step 0 — delete the garbage

This is a clean slate, not a refactor. The current `reduce.*` cannot be
rescued in place because the foundational ordering is wrong (cases were
built before B0 / driver / convention enforcement).

**Delete:**

```
src/proof/translate/lkr_cut_elim/reduce.cpp    (745 lines)
src/proof/translate/lkr_cut_elim/reduce.h      (90 lines)
test/reduce_test.cpp                           (~960 lines)
```

**Edit:**

- `src/proof/translate/lkr_cut_elim/BUILD.bazel` — remove the `reduce`
  `cc_library` target. Keep the `deriv` target.
- `test/BUILD.bazel` — remove the `reduce_test` entry (line 281
  references `//src/proof/translate/lkr_cut_elim:reduce`).

**Keep (the framework — explicitly preserved on 2026-05-23):**

```
src/proof/translate/lkr_cut_elim/deriv.{h,cpp}     — sequent-carrying tree, build, emit
src/proof/translate/lkr_cut_elim/CUT_ELIM_DESIGN.md — the spec
test/deriv_test.cpp                                 — exercises the framework
```

**Exit criterion for Step 0.** `bazel test //test:all_tests` is green
with no Stage 3 reduce engine present.

## 4. Step 1 — type / enforce Deriv conventions

The root cause of the soundness bug is that `Deriv` lets every author
invent their own convention for what each rule's `child.conclusion` should
look like relative to `node.conclusion`. Two corrective sub-steps:

**1a. `Deriv::validate(d)` — structural invariants per rule.** A pure
function that walks a Deriv and asserts, for every node:

- `RWeaken{added, child}`: `child->conclusion = node->conclusion ++ {added}`
  (child = post-W = bigger). This is the convention `build()` uses; it
  becomes the *only* legal convention.
- `RContract{i, j, child}`: positional invariant per the spec.
- `RExchange{i, j, child}`: child has positions `i`/`j` swapped.
- `RAnd{principal, left_partition, left, right}`: principal at last;
  partition partitions `[0..|Γ|)`; `left->conclusion` and
  `right->conclusion` match the partition.
- `ROr{principal, child}`, `RForall`, `RExists`, `RCut`, `RAx`, `ROne`,
  `RLemma`: analogous, each per the spec.

Returns `util::Result<void>` with a precise diagnostic on mismatch.

**1b. Tests build Derivs *through* `build()` from LKR programs, not by
hand.** Hand-built Derivs are permitted only for unit-testing primitive
reductions; even then they must pass `Deriv::validate` at the top of the
test. No exceptions.

**Exit criterion for Step 1.**

- `Deriv::validate` exists, is called automatically inside `build()` and
  at the top of every Stage 3 unit test.
- `test/deriv_invariants_test.cpp` exists and exhaustively round-trips
  small LKR programs through `build() → validate`.
- The previously-implicit convention is now a typed/validated invariant.
  Future reductions that violate it fail loudly, locally, at test time.

## 5. Step 2 — B0 as an honest pre-pass

Per spec §4: every additive Cut becomes mult-Cut + |Γ|·Contraction *up
front*. After B0 runs, every cut in the tree is multiplicative; the
later case work has one simpler shape to handle.

**Surface.** A single function `additive_to_multiplicative(d) -> Deriv`
in a new `b0.{h,cpp}`. It walks the tree once. For each `RCut{φ, left,
right}` where `left.conclusion = right.conclusion = Γ ++ {φ_or_φ̄}`, it
emits `mult_cut(left, right)` (concl = `Γ ++ Γ`) followed by |Γ|
`RContract` ops collapsing the duplicated `Γ`. The `wrap_with_weakenings`
gymnastics inside the old B2 are *deleted* — they were B0's job done in
the wrong place.

**Exit criterion for Step 2.**

- `additive_to_multiplicative` is total on validated Derivs.
- `test/b0_test.cpp`: for any `LKRVerifier`-accepted input,
  `emit(b0(build(p))) LKRVerifier`-accepts the same goal; every `RCut`
  in the output is multiplicative.
- No later case may invoke `wrap_with_weakenings`-like glue. The bridge
  is paid for, once, by B0.

## 6. Step 3 — worklist driver on `(degree, rank)`

Per spec §5.1, §5.6: pick a *topmost cut of maximal degree*, reduce it,
repeat. The proof of termination is only valid under this measure.
Post-order is not a substitute.

**Surface.** `eliminate_cuts(builder, d) -> Result<Deriv>`. Internally:

1. Build a worklist of all `RCut` nodes with `(degree, rank, path)`.
2. Pop the entry with maximal `degree`, breaking ties by `rank` (lowest
   first — topmost), breaking further ties by path.
3. Dispatch by case on the chosen cut's left/right last-rule pair (the
   §5 case table). Replace the subtree with the reduction's output.
4. Re-validate the tree.
5. Recompute the worklist (cheaply — only the modified subtree's cuts
   need to be re-classified).
6. Loop until empty.

No case is allowed to recurse into a higher-degree cut. The driver
enforces this by selection; the cases themselves only emit cuts of
strictly smaller degree (5.2 / 5.3) or move the cut at fixed degree
strictly up (5.4 / 5.5).

**Exit criterion for Step 3.**

- The driver exists, with no case-specific logic.
- A scaffold `dispatch_case(left_rule, right_rule)` returns
  `not_implemented` for every case (cases land in Step 4).
- A termination test: handcrafted Deriv with N nested cuts of strictly
  decreasing degree terminates in N steps. (Not yet a soundness test —
  case bodies are stubs.)

## 7. Step 4 — case reductions on multiplicative input

Now and only now, fill in the §5 cases. Each case is a function whose
input is a *multiplicative* `RCut` (B0 has run) on a *validated* Deriv
(Step 1 enforced), invoked by the worklist (Step 3 enforced).

Order — strictly by what the math forces, not by what looks tractable:

- **B1 — axiom cases (§5.2).** Base case of the induction: cut against
  `RAx` or `ROne` with the cut formula principal. Reduces to the other
  premise weakened/exchanged appropriately.
- **B2 — principal logical (§5.3).** Cut formula principal in both
  premises. Two sub-cases: ∧ vs ∨ (two smaller cuts), ∀ vs ∃ (substitute
  the witness through the universal premise, then one smaller cut at
  lower degree). Both consume B1 inductively.
- **B3 — capture-avoiding substitution (§6).** Needed by ∀/∃ in B2. A
  substitution pass on a sub-Deriv that α-renames bound variables under
  conflict. Tested in isolation before B2's ∀/∃ subcase relies on it.
- **B4 — permutation (§5.4).** Cut formula not principal in one
  premise's last rule. Permute the cut above the rule. Strictly lowers
  rank at fixed degree.
- **B5 — structural (§5.5).** W dead-cut (other premise is discarded;
  weaken the survivor). C duplication (duplicate the other premise, cut
  twice, then contract). X (trivial permute).

Each landing pattern: spec the case in one paragraph against §5.X →
write the test (handcrafted Deriv + validate + reduce + check cut-free
sub-result + re-verify) → implement → green → commit. No case lands
without its test, and no test passes `validate` by hand-building in a
non-canonical convention.

**Exit criterion for Step 4.** `eliminate_cuts` is total: for any
`LKRVerifier`-accepted input p, `eliminate_cuts(build(p))` returns
without `not_implemented`, the output is cut-free, and `emit + LKRVerifier`
accepts the same end-sequent.

## 8. Step 5 — Stage A (lemma inlining)

Per spec §3. Process theorems in dependency order; cache each one's
cut-free, lemma-free proof; replace `RLemma{L}` closing `⊢ Γ, φ_L` by
splicing L's cached proof with `Γ` as inert context.

This is *strictly downstream of Step 4*: Stage A relies on Stage B
having already cut-eliminated each theorem before it can be inlined.
Implementing Stage A before Step 4 finishes would be premature.

**Exit criterion for Step 5.** `eliminate_cuts` additionally has no
`RLemma` nodes in the output. Round-trip property §8 holds for proofs
that cite proven theorems.

## 9. Out-of-scope but flagged for future decisions

- Spec §7a (axiom cuts are irreducible). This remains true after the
  reset. Whether to reformulate goals to push axioms to leaves is a
  separate, *pipeline-level* decision tracked under
  `[[pipeline-three-stages-2026-05-23]]`'s Stage 1 (which is already
  shipped). No action required as part of this reset.
- Stage 4 (Weakening-elim). Independent of this plan. The user has
  flagged it for separate review.
- Wire-up of Stage 3 into `comb_checker`. Deferred until Step 4's exit
  criterion is met.

## 10. Done criterion for the reset as a whole

1. The current `reduce.{h,cpp}` and `test/reduce_test.cpp` are gone.
2. `Deriv::validate` exists and is invoked everywhere a Deriv is built
   or hand-constructed.
3. `additive_to_multiplicative` is a real pre-pass; no later case
   contains additive→multiplicative glue.
4. The driver is worklist-based on `(degree, rank)`, never selecting
   a non-topmost or non-maximal-degree cut.
5. Every §5 case is implemented and tested in isolation, with tests
   that go through `build()` rather than hand-construction.
6. `eliminate_cuts` satisfies §8 round-trip on its own test corpus
   (LKR programs constructed via Runtime + parser, not via the ZFC
   theorem corpus).
7. ZFC corpus runs are explicitly *not* in the done criterion. They
   are post-hoc bug-catchers per `[[corpus-is-test-not-design-driver]]`.

## 11. What I will *not* do under this plan

- Add cases ahead of Steps 1–3. Foundation first.
- Justify any case, ordering, or scope decision by "the corpus exercises
  X." That is the violation the hard rule forbids.
- Touch Stage 4 or any downstream consumer.
- Amend `CUT_ELIM_DESIGN.md`. The math is right; the implementation
  drifted.
- Wire `eliminate_cuts` into `comb_checker` as part of this reset.
