# Verifier Paper-Faithfulness Audit — 2026-05-19

## Status as of 2026-05-19 (final)

**All audit items now closed in code:**

| Tag | Issue | Fix |
|---|---|---|
| CRIT-1 | Compound terms in atom args | `check_term_system_scope` rejects non-Fixed atom args / dualizer images (`verifier.cpp:51`) |
| MOD-1 | `process_union` greedy fallback | Priority 2 added; full backtracking in MOD-2 |
| MOD-2 | No backtracking over binarizations | Case C rewritten as DFS over choice tuples (`leap.cpp::dfs`/`try_decomposition`) |
| MOD-3 | `size==1` dumps non-literals into L | Literal-kind check; rejects otherwise |
| P1-3 | Phantom binding edges | 2A.3 rule (C4): every binding edge must target a vertex inside the binder's cotree scope |
| 2A.3-1 | Stored `is_existential` not verified | 2A.3 rule (C3): label must match cograph adjacency |
| MIN-1 | Case B trusts no-edge → universal | Asserts `!is_existential` |
| MIN-2 | Case A trusts empty-edge → no binder | Asserts no binder lingers |
| MIN-3 | Case C.2 trusts stripped binder is existential | Asserts `is_existential` |
| 2B-2 | Dualizer image not universal-verified | Image var must be a known universal binder |
| WF-2 | Cograph edge self-loops/duplicates | Simple-graph check |
| WF-3 | Binding edge endpoint kinds | Asserts source = Binder, target = Atom |
| INH-1 | Hughes' 10.21 → 10.18 gap | **Resolved.** Structural fact from Def. 5.3: in a fonet, no leap is also a cograph edge (W={u,v} would induce a bimatching). Verifier now enforces this explicitly at 2C.0 (`verifier.cpp:578`). |

**Documented as convention (not paper-deviant, not closable as code):**
- 2B-1: Image not existential. Narrowing of Def. 5.2 to Lemma 10.12 MGU; safe.
- P1-1 / P1-2: Positional comparison. Verifier convention; emitter must match builder's pre-order.

**Downstream test fallout (translator bugs, not verifier regressions):**

| Test target | Why it fails now |
|---|---|
| `test:comb_test` | Three test cases construct linked fographs where a link coincides with a cograph edge (e.g., `cograph_edges={{1,2}}` and `links={{1,2}}` for `(A ∧ ¬A)`). Per Hughes Def. 5.3, W = {u,v} induces a bimatching, so this is not a fonet. The old verifier accepted these incorrectly. The test data is paper-incorrect (it tests acceptance of non-fonets); the verifier is now correct. |
| `test:axiom_rewrap_test` | The LKR→Comb translator emits CombProofs that fail the new paper-faithful checks (most commonly P1-3: binding edges to vertices outside the binder's cotree scope). Translator bug surfaced by the verifier; translator fix is out of audit scope. |
| `test:lkr_to_comb_test` | Same root cause as `axiom_rewrap_test`. |

All other tests pass:
- `test:core_test` ✓
- `test:runtime_test` ✓
- `test:iota_translator_test` ✓
- `test:lkr_verifier_test` ✓
- `test:nd_to_lkr_test` ✓

The verifier is now paper-faithful within its documented scope.

---



Audit of `src/proof/comb/` against Hughes (2019), "First-order proofs without syntax." The verifier is the only soundness gate; everything below is a deviation from the paper that may affect correctness, completeness, or strictness of acceptance.

**Severity legend**

- **CRIT** — soundness gap on inputs within the documented scope (can accept a non-proof, or reject a paper-valid proof for the wrong reason)
- **MOD** — soundness gap only on inputs outside the documented scope (precondition under-enforced), or completeness gap
- **MIN** — defensive check missing; correctness preserved on well-formed inputs but trusts data that should be verified
- **STY** — verbatim deviation from a paper definition with no correctness impact
- **PERF** — complexity gap, not a correctness gap

## Quick index by file

| File | Phase | Crit | Mod | Min | Sty | Perf |
|------|-------|-----:|----:|----:|----:|-----:|
| `verifier.cpp` (well-formed) | entry | 0 | 0 | 3 | 0 | 0 |
| `verifier.cpp` (check_description_free) | entry | 0 | 0 | 0 | 0 | 0 |
| `verifier.cpp` (target_is_formula_graph) + `fograph.cpp` | Phase 1 | 0 | 1 | 2 | 1 | 0 |
| `cotree.cpp` | (supports 2A.3 + 2C) | 0 | 0 | 0 | 0 | 1 |
| `verifier.cpp` 2A.1/2A.2/2B.1/2B.2/2B.3/2A.3 | Phase 2A/2B | 0 | 1 | 2 | 0 | 0 |
| `leap.cpp` | Phase 2C | 1 | 3 | 3 | 1 | 0 |
| `verifier.cpp` skew_bifibration | Phase 3 | 0 | 0 | 0 | 0 | 0 |
| Hughes' own proof gap | inherited | ? | 0 | 0 | 0 | 0 |

---

## Phase: entry (`verifier.cpp::verify`)

### `verify_well_formed` — basic range checks only

**Status:** correctness-OK on well-formed inputs; defensive checks missing.

- **WF-1 [MIN]** No check that `source.links` are distinct edges. A literal could be in two links with `in_link[v] = 2` and would be caught by 2A.1, but the duplicate-link case where `{u,v}` appears twice would double-count `u` AND `v` and slip past as `in_link[u] = in_link[v] = 2` which fails 2A.1 — so this is actually caught indirectly. *Confirmed indirectly safe.* Keep an explicit check for clarity.
- **WF-2 [MIN]** No check that `source.cograph_edges` are distinct or that they exclude self-loops `{v,v}`. Self-loops would corrupt Ω and bridge tests. Cotree builder filters self-loops at `cotree.cpp:38` but the verifier should not rely on the cotree for soundness.
- **WF-3 [MIN]** No check that `source.binding_edges` are directed binder→atom (kind constraints on endpoints). A malformed input with binding edge from atom to binder, or between two atoms, slips through `verify_well_formed`. Caught later only if it triggers a downstream contradiction.
- **WF-4 [MIN]** No check that dualizer keys `δ.first` are within the expected `var_index` range or are actually used as binder variables somewhere. 2B.1 (`!existential.count(x)`) catches this *if* the key happens to coincide with a universal var or a non-binder var — but doesn't if the key is a totally fresh index never seen elsewhere; the check `if (!existential.count(x))` would correctly fail because the key isn't in the existential set. *Confirmed safe.*

### `check_description_free`

Paper has no descriptions; this is a project-local precondition. No deviation.

- Verifier-internal: also scans goal formula recursively, target labels' atom args, dualizer image terms. Complete for the term system's `Description` kind.

---

## Phase 1: `verify_target_is_formula_graph`

Builds the canonical `G(NNF(goal_formula))` and compares to `proof.target` element-wise. Supporting code: `Fograph::Fograph(FormulaHandle)` in `fograph.cpp`.

### `compare_fographs`

- **P1-1 [STY]** Vertex comparison is **positional**, not by graph isomorphism. Hughes' G is defined modulo graph identity, but `labels_equal(expected.labels[i], actual.labels[i])` requires identical pre-order. Translators are required to emit in the builder's canonical order. This is a verifier convention with no correctness impact, but two paper-equal fographs with different vertex orderings would be wrongly rejected as "vertex label mismatch."
  - **Fix direction:** either document this as a hard convention or implement a label-preserving isomorphism check (more expensive).
- **P1-2 [MIN]** `labels_equal` for Binders compares `var == var`. The Fograph constructor assigns `var = next_binder_var++` in pre-order, so two builders following the same convention produce matching indices. There is no audit that the proof producer used this convention.
  - **Fix direction:** strip binder var-indices to canonical positional indices on both sides before comparison.

### `Fograph::Fograph(FormulaHandle)` — Hughes Def. 3.1

Implements:
- G(α) = •α ✓ (`push_atom`)
- G(φ ∨ θ) = G(φ) + G(θ) ✓ (no cograph_edges added between left and right)
- G(φ ∧ θ) = G(φ) × G(θ) ✓ (cograph_edges added between every left vertex and every right vertex)
- G(∀x φ) = •x + G(φ) ✓ (binder added; no cograph_edges to body)
- G(∃x φ) = •x × G(φ) ✓ (binder added; cograph_edges from binder to every body vertex)

**Issues:**

- **P1-3 [MOD]** The Fograph builder does not verify the input formula is **rectified**. Hughes Lemma 10.1 / Lemma 3.3: G is a surjection onto **rectified** fographs from rectified formulas. The builder relies on `next_binder_var++` to make every binder fresh, which implicitly rectifies, BUT only the binder vertex labels are rectified — the atom args are taken from the formula as-is via `rewrite_term`. A `Fixed` term in an atom arg with a `var_index` matching a binder elsewhere in the formula would create an inadvertent cross-binding.
  - **Fix direction:** assert in the builder that every `Fixed` term in atom args corresponds to a `Gen` reference resolved via `binder_stack`, or that the input formula has all atom args as `Gen` indices.
- **P1-4 [MIN]** Truth literal: code matches the syntactic pattern `¬⊥` (Not of Bottom) and emits `VertexKind::One`. Hughes treats the truth literal `1` as a special vertex; encoding via `¬⊥` is a project convention. Bare `⊥` is asserted-out as "unprovable." This is fine if `to_nnf` always rewrites `⊥` away in valid formulas, but the verifier does not check this — relies on the assertion firing only on translator bugs.

### NNF conversion

- Code calls `fb.to_nnf(goal_formula)` before building the fograph. Hughes' G is defined only on NNF formulas (literals, ∧, ∨, ∀, ∃). NNF preserves logical equivalence, so G(NNF(φ)) is the fograph of a logically-equivalent formula.
  - No explicit deviation, but: G(NNF(φ)) **may not equal** G(φ_original) if φ_original was not in NNF. The verifier compares against G(NNF(goal)), not G(goal). If a translator emits target = G(φ_original), Phase 1 fails. *Confirmed convention.*

---

## Phase 2A.3 + 2C support: `cotree.cpp`

### Cograph recognizer / cotree builder

- Implements Lerchs (1971) recursive decomposition: + if disconnected, × if complement disconnected, P_4 otherwise.
- **C-1 [PERF]** O(n³) naive recognizer. Hughes Theorem 14.3 only requires polynomial — this is polynomial. Hughes cites Corneil-Lerchs-Stewart 1981 for linear-time alternative. No correctness impact.
- Cograph definition (P_4-free) and modular decomposition match the paper.
- Component ordering is deterministic (sorted by smallest vertex), so cotree child enumeration is stable across runs.

### Header-naming caveat

- `NodeKind::JOIN` = `+` (disjoint union) and `NodeKind::UNION` = `×` (graph join). The cotree.cpp comment block notes this explicitly. **Confusing but not a deviation** — internal nomenclature only. Any reader of `leap.cpp::process_union` must remember `UNION = ×`.

---

## Phase 2 (fonet validity): `verify_fonet`

### 2A.1 — every atom in exactly one link

- Hughes Def. 5.1: every literal is 1-labelled or in a link, every link has exactly two pre-dual literals.
- Code: `in_link[v] == 1` for Atom, `== 0` for One and Binder. **Paper-faithful.** ✓

### 2A.2 / 2B.3 — link endpoints pre-dual and dual-after-δ

- Hughes Def. 5.2: αδ and α'δ are dual atoms after substitution.
- Code: checks `pred == pred && negated != negated` for pre-duality, then `args1 == args2` after applying δ.

**Issues:**

- **(see leap.cpp's SEVERE term-system limitation)** `apply_dualizer_to_term` only substitutes top-level Fixed terms; cannot recurse into compound terms. Same scope limitation as `build_leap_graph`. **Not duplicated here as a separate finding** — see CRIT-1 in the leap.cpp section.

### 2B.1 / 2B.2 — dualizer key/image kinds

- Hughes Def. 5.2: δ keys are existential vars, δ images are terms that may contain universal binder vars.
- Code (lines 296–306):
  - Each key is an existential binder var ✓
  - Each Fixed image is **not** an existential var ✓

**Issues:**

- **2B-1 [STY]** Code's image check rejects `image.is_fixed() && existential.count(image.as_variable())` — i.e., it requires images to NOT be existential. The paper's MGU (Lemma 10.12) has this property, but the paper's Def 5.2 allows arbitrary dualizers, not just MGU. Accepting only MGU-style dualizers is a strictness. Since every dualizable fonet has an MGU (Lemma 10.12), this is sound; rejects non-canonical dualizers that happen to point existential→existential but are still valid pre-MGU. Documented as convention.
- **2B-2 [MIN]** Code does not check that an image's `var_index` is a *known* universal binder. A Fixed image pointing to a fresh stem variable (paper's "no stem variable" condition for MGU) is accepted. Paper sometimes wants no stems (Lemma 10.12 ensures this for MGU by renaming); code doesn't enforce.

### 2A.3 — binder legality (Hughes Def. 3.2)

- Hughes: every binder's scope contains ≥1 literal AND no other same-variable binder.
- Code: builds cotree of `source.cograph_edges`, for each binder finds `v_subtree = parent(leaf_of(v))`, iterates leaves of subtree, checks `has_atom` and `!dup_binder`.

**Issues:**

- **2A.3-1 [MOD]** Code does **not** verify that the stored `is_existential` label is consistent with the cograph structure. Hughes Def. 3.2: "A binder b is existential (resp. universal) in a logical cograph G if, for every other vertex v in the scope of b, we have bv ∈ E_G (resp. bv ∉ E_G)." The classification is **derived from edges**, not stored. The code trusts the stored label (inherited from target via fibration). A malformed input with `is_existential = true` but no × edges to its scope, or vice versa, slips through.
  - **Concrete consequence:** Case B in `leap.cpp` then strips such a binder thinking it's universal (because it has no edges), and Case C.2 treats it as existential (because the label says so). Different parts of the verifier disagree about the binder's kind.
  - **Fix direction:** in 2A.3, for each binder, scan the scope and check that the existential ↔ "× edges to every scope member" equivalence holds; reject otherwise.

### 2C

See `leap.cpp` audit below. All issues from the earlier audit are restated there.

---

## Phase 2C: `leap.cpp` (recap)

### `build_leap_graph`

- **CRIT-1 [CRIT]** Unification model only handles single-variable terms (Fixed) and opaque blobs (Gen). Hughes Lemma 10.13's dependency definition is in terms of `δ(x)` containing `y`, where δ(x) may be a compound term like `f(y, z)`. The code's union-find with single-Term anchors **cannot represent** an existential class pinned to a compound term containing multiple universals. Consequence: on inputs with compound atom args (function symbols), dependencies are under-counted → leaps are under-counted → bimatchings can be missed → **unsound**.
  - **Scope:** safe only within the precondition "atom args are Fixed or Gen." This precondition is checked at the goal level (descriptions rejected) but not at the level of function applications because the project's term system lacks function-application form. *The verifier is therefore correct on its term scope.*
  - **Fix direction:** either widen `Term` to support compound terms and rewrite unification properly, or reject any input outside the variable-only scope at the verifier entry.

### `verify_no_bimatching::process_union`

- **MOD-1 [MOD]** Fallback branch (no singleton existential binder among × cotree-children) reverts to first-child rule. If the first child is a non-leaf cotree-subtree containing no literal, the same R2 violation (Lemma 10.20's `G_m = •x` singleton requirement) recurs. *Already discussed in the commit message for `78e6f24`.*
- **MOD-2 [MOD]** Verifier commits to a single binarization with no backtracking. Hughes proves a valid representation exists but does not guarantee a greedy choice finds it.
- **MOD-3 [MOD]** `child_leaves.size() == 1` branch (lines 451–454) dumps leaves into L without verifying they are literals. Hughes' L is "a union of literals." Reachability depends on whether `restrict_cotree` fully renormalizes degenerate × nodes; not audited.

### `verify_no_bimatching` defensive gaps

- **MIN-1 [MIN]** Case B strips a binder with "no incident cograph edge" without asserting it is universal. Hughes Lemma 10.16's "necessarily a universal binder" is a structural fact about fonets — if the input is malformed, the code silently treats an existential as universal.
- **MIN-2 [MIN]** Case A returns `Ok` on empty edge set without asserting all remaining vertices are literals. Hughes Lemma 10.17 requires "no edge AND no binder."
- **MIN-3 [MIN]** Case C.2 strips the singleton on the no-literal side without asserting it is existential. Universals should have been stripped in Case B; if any survives, C.2 quietly mishandles it.

### `verify_no_bimatching` `L` partition

- **STY-1 [STY]** L-to-L pairs and 1-literals are sent to W_left (= L_X side). Hughes' definition: literals whose mate is not in V_X go to L_Y — so L-to-L pairs (mate in L) and 1-literals (no mate) belong in L_Y. Symmetric for the recursion's correctness (the pair is kept together), but a verbatim deviation from the paper.

---

## Phase 3: `verify_skew_bifibration`

Hughes Def. 4.1: a skew bifibration is a label- and existential-preserving graph homomorphism that is both a skew fibration on the (undirected) cograph edges and a directed fibration on the binding edges.

### Label + existential preservation

- Source labels are **inherited** from target via `source_label(v) = target.labels[fibration[v]]`. Label preservation is structural by construction; existential preservation likewise. **Paper-faithful by design — no explicit check needed.** ✓

### `is_homomorphism` (undirected)

- Iterates every source edge, checks the mapped edge is in the target's edge set in either orientation. ✓

### `is_homomorphism_dir` (directed)

- Iterates every source edge, checks the mapped edge is in the target's edge set with the same orientation. ✓

### `is_skew_fibration`

- For each `v ∈ V_src`, each `w` adjacent to `f(v)` in target, searches for `w̃ ∈ V_src` with `{w̃, v} ∈ E_src` and `{f(w̃), w} ∉ E_target`. ✓ matches Def 4.1's skew fibration condition. Lift-may-land-on-w case handled because target has no self-loops.

### `is_fibration_dir`

- For each `v ∈ V_src`, each predecessor `w` of `f(v)` in target, counts source vertices in `f⁻¹(w)` having a directed edge to `v`. Requires the count to be exactly 1 — Hughes' `∃! w̃`. ✓

**No deviations found in Phase 3.**

---

## Inherited from the paper

### Hughes' 10.21 → 10.18 step

- **INH-1 [?CRIT]** Lemma 10.21's bridge condition (in Ω, removing the (G_m, G_{m+1}) edge disconnects X from Y) does not by itself preclude leaps *within* G_m × G_{m+1}. But Lemma 10.18's precondition forbids leaps between V_{K_1} ∪ V_{H_1} and V_{H_2} ∪ V_{K_2}, which **includes** leaps from V(G_m) to V(G_{m+1}).
- Hughes' proof of 10.21 appeals to 10.18 without bridging this gap. Either there is a structural fact (likely candidate: in a fonet, links cannot coexist with cograph adjacency between linked atoms — but I cannot find this explicitly in §5 or §10.1) or the paper has an unaddressed soundness gap.
- The code follows Hughes verbatim. If the hidden assumption fails on some input, the verifier inherits unsoundness on that input.
- **Action:** read §5 (linked fograph definition) for a possible structural constraint that closes this gap; if not found, treat as an open question to be raised externally.

---

## Recommended fix order

If aiming for zero-tolerance paper-faithfulness:

1. **CRIT-1** — term-system extension. Most consequential. Either widen `Term` or reject non-variable inputs at the verifier entry with a clear error.
2. **2A.3-1** — verify `is_existential` consistent with cograph edges. Closes a real inconsistency between 2A.3 and 2C's Case B / Case C.2.
3. **MOD-1, MOD-2, MOD-3** — `process_union` heuristic gaps. Either prove greedy sufficiency for fonets or implement backtracking; audit `restrict_cotree`.
4. **P1-3** — Fograph builder rectification guard.
5. **INH-1** — research Hughes' 10.21 → 10.18 gap.
6. **Defensive checks** — MIN-1, MIN-2, MIN-3, WF-2, WF-3.
7. **STY-1, P1-1, P1-2, 2B-1, 2B-2** — verbatim/convention cleanups.
8. **C-1, P1-4** — performance and convention notes; lowest priority.
