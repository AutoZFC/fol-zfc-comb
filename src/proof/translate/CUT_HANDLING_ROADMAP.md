# Roadmap: a complete & sound cut-handling path to combinatorial proofs

**Goal.** One *complete and sound* translation from our proofs (ND → LKR →
Comb) into combinatorial proofs. We are NOT committed to a single
construction — we only need one route that always works. The obstacle is
**cuts** (NDtoLKR emits them from modus ponens, `eq_subst`, and lemma
citations). The cut-free fold (`interpret_tree`, paper-exact Hughes §11.1)
already works; the open question is purely how to discharge cuts.

This document tracks **two parallel tracks**, each a route to that goal.

---

## Established facts (the theory we are standing on)

- Combinatorial proofs (FOCPs) are **sound and complete** for first-order
  logic (Hughes 2019 [§15 paper]). So a comb proof of any valid theorem
  *exists*.
- A **cut-free** proof translates to a comb proof directly and faithfully.
  Our `interpret_tree` does this today.
- Therefore the only thing standing between us and a complete pipeline is
  removing/representing cuts.
- **Cut elimination always exists** (Gentzen Hauptsatz) — terminates, sound,
  same theorem. Worst-case non-elementary blowup is the only risk.
- **KS1** (Hughes–Straßburger–Wu, LICS 2021, arXiv:2104.13124) is a
  deep-inference system that is sound+complete (Thm 16) and whose
  **cut-free** fragment maps onto comb proofs almost mechanically (Thm 19,
  via the decomposition theorem). KS1 is itself cut-free — so it does NOT
  remove the need for cut elimination; it relocates it into deep inference.
- **Native §15 cuts** (no elimination) is the third option. We pushed it
  this session (absorb-at-binder, see `lkr_to_comb/CUT_S15_DESIGN.md`):
  scoping is solved, but a cut used at *multiple instantiations* (a
  contraction on the cut) is unsolved and has no reference construction —
  the §15 inventors chose cut-elimination instead. **§15 is PARKED**, not a
  track. See "Native §15 status" below.

Bottom line: **both tracks ultimately discharge cuts** (Track 1 in the
sequent calculus, Track 2 in deep inference). They are complementary, not
redundant — Track 1 is the near-term guaranteed win; Track 2 is the
principled long-term foundation with the cleanest comb correspondence.

---

## Track 1 — Cut elimination (LKR Hauptsatz) → existing cut-free fold

**Idea.** Eliminate every `Cut` op in the LKR program, producing a cut-free
LKR proof of the same goal, then run the existing `interpret_tree` fold.
Guaranteed complete and sound by Gentzen + the cut-free fold's correctness.

**Why this is the near-term bet.** The endpoint is *known to exist*; the
cut-free fold already works; only the elimination procedure is missing.

**Current state (updated 2026-05-21 after writing the round-trip test).**
- `test/lkr_cut_elim_test.cpp` now exists: round-trip property (output is
  cut-free AND re-verifies under `LKRVerifier` against the same goal) on
  programs produced by the *real* NDtoLKR translator. **All 5 cases fail
  today** — and the failure is NOT the `:441` And case. It is that
  `eliminate_cuts` only reduces atom-cuts and dead-cuts, and NDtoLKR emits
  almost none of those. Measured reductions: `control_cut_free` (a bare
  `use`) 3→2 cuts; `implies_elim`/`iff_elim_r`/`and_intro` 6→6;
  `or_elim` 8→8.
- **Root cause — the cut-spine shape.** NDtoLKR (`cut_spine.cpp`) emits a
  right-leaning *cut spine*: every derived flat step F_k becomes
  `Cut(F_k)` where LEFT proves F_k (via `CloseByLemma`, or an `emit_close`
  spine of `Forall`/`Exists`/`Or`/`And`/`AxiomLit`) and RIGHT carries
  `¬F_k` forward to the next step. So the cuts are **logical cuts on
  compound formulas** and **CloseByLemma cuts** — exactly the two cases
  `walk_reduce` does NOT implement. `cut_elim.cpp`'s header *describes*
  logical reduction + permutation, but `walk_reduce` only has
  `try_strict_axiom_cut`, `try_linear_atom_cut`, dead-cut, else-preserve.
  There is no ∧/∨/∀/∃ logical reduction and no CloseByLemma handling.
- **Real gap list (supersedes the old one):**
  1. CloseByLemma-cut handling (the dominant shape) — inline the lemma's
     proof, or reduce natively. `lemma_inliner` already exists in
     `lkr_to_comb/` and may be reusable.
  2. Logical-cut reduction for ∀/∃ (eigenvar→witness substitution) and
     ∧/∨/→ (principal-rule matching), incl. permutation when the cut
     formula isn't yet principal.
  3. The `:441` multiplicative-And split bookkeeping (real, but only one
     of several missing pieces, not the headline).
- Still **NOT wired** into `lkr_to_comb.cpp` (dead `#include`).

**Open design fork (decide before the big impl).**
- **A. Inline-then-Gentzen.** Inline `CloseByLemma` first (reuse
  `lemma_inliner`) so every cut is a logical cut between two structural
  derivations, then implement textbook Gentzen ∧/∨/∀/∃ reductions + the
  And split. Pro: well-understood, reuses inliner. Con: inlining can blow
  up size; full Gentzen + permutation is a lot of careful code.
- **B. Native cut-spine collapse.** Exploit NDtoLKR's specific shape (each
  `Cut(F_k)`: LEFT derives F_k, RIGHT consumes `¬F_k`) and splice LEFT's
  derivation into RIGHT's single use-site. Pro: matches the producer,
  likely bounded cost when each step is used once. Con: relies on the
  shape invariant; a derived step reused at multiple instantiations is a
  **contraction-on-the-cut** — the exact wall §15 hit. First measure
  whether NDtoLKR ever contracts a cut on the corpus.

**Next actions.**
- [x] Write `test/lkr_cut_elim_test.cpp` (round-trip property). DONE — red,
      pinning the gap above.
- [ ] DECIDE the design fork (A vs B), informed by: does NDtoLKR contract
      cuts (reuse a derived step) on the real corpus? If never, B is
      bounded and clean; if it does, that reuse IS the §15 contraction
      problem and A (or Track 2/KS1) is needed.
- [ ] Implement the chosen route rule-by-rule under the math-first
      discipline (one reduction → its test goes green → commit), starting
      with the CloseByLemma cut (the most common).
- [ ] Fix the `:441` And split as part of the ∧ logical-cut work.
- [ ] Re-wire `lkr_to_comb::apply`: try `eliminate_cuts` → `fold_cut_free`
      (interpret_tree). Keep §15 fold + walk as ordered fallbacks.
- [ ] Run the corpus; measure coverage + blowup cost.

**Risks.** Non-elementary blowup on deep proofs (the eq/extensionality
proofs that already fail at the dualizer are the likely stressors). Eigen-
variable freshness during substitution (the old B.2 class — keep it in
mind). Termination is guaranteed; only cost is at risk.

**Done-criteria.** `eliminate_cuts` is total (or fails only on shapes
NDtoLKR never emits), tested, wired; the corpus translates end-to-end with
acceptable cost.

---

## Track 2 — Full KS proof system (deep inference) → comb via decomposition

**Idea.** Build the deep-inference system **KS1** and the KS1↔comb bridge
from HSW 2021 (Thm 17 decomposition + Thm 19 correspondence). This gives
the cleanest, theory-aligned translation to comb proofs and an explicit,
phase-separated account of contraction — exactly the structure the comb
proof's skew fibration wants.

**Why this is the long-term bet.** Deep-inference phases map 1:1 onto
comb-proof structure: the multiplicative-linear core (MLS1^X) builds the
fonet + links + dualizer; the contraction/weakening phase IS the skew
fibration (many-to-one + skew). Sequent calculus mixes these, which is the
source of our cut/contraction pain. This is the framework the inventors
moved to.

**Honest scope.** KS1 is **cut-free**. So Track 2 still needs cuts gone —
either by consuming cut-free input (Track 1's output, or normal proofs) or
by deep-inference cut-elimination (HSW cite [22],[34], not in scope here).
Track 2's payoff is the *clean comb correspondence and contraction account*,
not a way to avoid cut elimination.

**Current state.** Spec done; nothing built yet. The full KS1 system, the
decomposition normal form, and the Thm 19 bridge construction are extracted
from the paper into **`KS1_TRACK2_DESIGN.md`** (read it first for Track 2).
We have the comb-proof data structures (fonet, skew bifibration, dualizer,
`collapse_binder_duplicators`) which ARE the KS1↔comb target; no KS1 system,
no translator. The bridge is now pinned down: decompose (Thm 17), read the
fonet off the linear core Φ1 (`ai`-pairs = links, `∃`-instances = dualizer;
Thm 33), read the skew bifibration off the resource phase Φ2's induced vertex
map (Lemma 41).

**Next actions** (phases K1–K6 in `KS1_TRACK2_DESIGN.md §7`):
- [x] Read HSW 2021 §VII–X; extract the KS1→comb construction + decomposition.
      → `KS1_TRACK2_DESIGN.md` (§5 Thm 17, §6 Thm 19, §8 reuse map).
- [x] Spec KS1 (Fig. 6): rules + `≡` + context `S{·}`. → `KS1_TRACK2_DESIGN.md`
      §1–4. (One open item: the *non-rectified* `c∀` schema is OCR-uncertain;
      the rectified `c̃∀` used by the bridge is authoritative — §4.2 ⚠.)
- [~] K1: KS1 formula view (units `t`/`f`, reuse `core::FormulaHandle` NNF) +
      `≡`. DONE: `≡` *propositional* fragment (assoc+comm of ∧/∨) as a
      canonicalizer — `src/proof/ks1/equiv.{h,cpp}`, `test/ks1_equiv_test`
      (26 assertions, green; committed ff68631). NOT via fograph equality
      (K1 finding). TODO: quantifier-shift equations (binder swap,
      mini-scoping) + context `S{·}` (folded into K2 where it's consumed).
- [ ] K2: KS1 derivation + per-rule checker, independent of comb. Replay
      Fig. 7's decomposed example; sound/complete sanity (Thm 16).
- [ ] K3: decomposition-form checker + split into `(Φ1, A', Φ2)` (require
      decomposed input; defer the reorganizer).
- [ ] K4: fonet read-off (Thm 33) — links from `ai`, dualizer from `∃`;
      validate against `CombVerifier` on Fig. 4's examples.
- [ ] K5: skew-bifibration read-off (Lemma 41) — induced vertex map → assemble
      `CombProof`; end-to-end `CombVerifier` pass.
- [ ] K6: front end (ND→KS1 / LKR→KS1 / consume Track 1's cut-free LKR);
      measure corpus coverage. (Cuts must be gone before the comb read-off.)

**Risks.** Largest engineering surface (a whole new proof system + bridge).
Still depends on cut handling upstream. Reading the full HSW construction is
a prerequisite and may reveal subtleties (the paper's ρφ variable-renaming,
the medial/instantiation phase ordering).

**Done-criteria.** KS1 checker + KS1→comb bridge that reproduces comb proofs
for the corpus (fed cut-free inputs), with the decomposition giving the
contraction account that native §15 lacked.

---

## Native §15 status (PARKED — not a track)

This session's absorb-at-binder work (`lkr_to_comb/CUT_S15_DESIGN.md`,
memory `project-absorb-at-binder-2026-05-21`) made native §15 cuts work for
closed + single-instantiation first-order cuts (ordered_pair 0→6/19). The
remaining failure is **contraction-of-cut** (one cut existential forced to
two distinct goal vars → no dualizer; HSW's decomposition says contraction
must be a separate fibration phase, not in the linear core). There is no
reference construction for native §15-with-contraction, and the field chose
cut-elimination instead — so we PARK §15 rather than chase completeness on
it. The working absorb path stays in as a fast path / fallback (it cannot
regress; walk is below it).

The §15 contraction *lesson* feeds both tracks: contraction = many-to-one
fibration + binder collapse (we already have `collapse_binder_duplicators`);
keep the linear/dualizer core contraction-free with distinct vars per use.

---

## Decision rationale (why two tracks, not one)

- **Track 1** has a *known endpoint* (Gentzen guarantees it) and reuses the
  working fold — fastest route to a complete pipeline. Its only risk is cost
  (blowup), which we can measure.
- **Track 2** has the *cleanest theory* and the right structural account of
  contraction, but the biggest build and still needs cut handling. It is the
  durable foundation and the place the literature has settled.
- Running both: Track 1 likely lands a complete pipeline sooner; Track 2's
  reading + KS1 build de-risks the long term and could consume Track 1's
  cut-free output. They share the cut-elimination dependency, so progress on
  elimination helps both.

---

## References

- Hughes, Straßburger, Wu. *Combinatorial Proofs and Decomposition Theorems
  for First-order Logic.* LICS 2021. arXiv:2104.13124. (KS1, decomposition
  Thm 17, bridge Thm 19.) Memory: `reference-hsw-decomposition-2021`.
- Hughes 2019 — first-order combinatorial proofs + §15 native cuts.
- `src/proof/translate/lkr_to_comb/CUT_S15_DESIGN.md` — native §15 / absorb.
- `src/proof/translate/lkr_to_comb/PAPER_EXACT_DESIGN.md` — the cut-free fold.
- `src/proof/lkr/PAPER_AUDIT.md`, `src/proof/comb/PAPER_AUDIT.md`.
- `src/proof/translate/lkr_cut_elim/cut_elim.{h,cpp}` — Track 1 code.
- Memory: `project-absorb-at-binder-2026-05-21`,
  `project-native-s15-cut-2026-05-20`.

<!-- Living doc: update the [ ] checklists and "Current state" as the two
     tracks progress. -->
