# LKR cut-elimination — rigorous design (Gentzen Hauptsatz)

**Status:** spec. Replaces the ad-hoc `walk_reduce` in `cut_elim.cpp`
(`try_strict_axiom_cut` / `try_linear_atom_cut` / dead-cut), which
pattern-matches three accidental shapes and handles neither logical cuts
nor `CloseByLemma`. This document specifies the *complete* procedure as the
classical sequent Hauptsatz, by cases, with a termination measure.

## 0. Why the sequent side (settled)

The target LKR is **classical** (one-sided, multi-conclusion — Hughes 2019
§11). Classical-ness there is *structural* (multiple formulas on the right),
so **classical cut-elimination is Gentzen-standard and well-behaved**, and
**complete for classical FOL**. The earlier ND-normalization idea is clean
only intuitionistically (classical ND normalization needs control operators
and loses the subformula property at ∨/∃+RAA); it cannot be classically
complete without that machinery. So cuts are discharged here, on the
sequent, with no fragment restriction. NDtoLKR already emits the classical
ND rules (`DoubleNegElim`, `ExcludedMiddle`, `Peirce`, `ClassicalAbsurd`)
into LKR; nothing about them needs special cut-elim treatment.

## 1. The calculus LKR (formal)

Sequents are finite **sequences** of NNF formulas; `⊢ Γ` is provable iff
`⋁Γ` is classically valid; the empty sequent is unprovable. **De Morgan
dual** `φ̄` (NNF): `ᾱ`/`α` for atoms; `φ∧ψ ↔ φ̄∨ψ̄`; `φ∨ψ ↔ φ̄∧ψ̄`;
`∀x.φ ↔ ∃x.φ̄`; `∃x.φ ↔ ∀x.φ̄`; `⊥ ↔ 1`. `φ̄̄ = φ`.

Rules (premises above ⟹ conclusion below; each sound forward):

```
                                   ─────────── (Ax)            ───────── (1)
                                    ⊢ Γ, α, ᾱ                   ⊢ Γ, 1
  ⊢ Γ                ⊢ Γ, φ, φ              ⊢ Γ (i,j swapped)
 ─────── (W)        ──────────── (C)       ───────────────── (X)
  ⊢ Γ, φ              ⊢ Γ, φ                 ⊢ Γ

  ⊢ Γ₁, φ   ⊢ Γ₂, ψ   (Γ₁⊎Γ₂=Γ)         ⊢ Γ, φ, ψ            ⊢ Γ, φ[x:=a]  (a∉FV(Γ))
 ───────────────────────────── (∧)     ──────────── (∨)      ───────────────────────── (∀)
        ⊢ Γ, φ∧ψ                         ⊢ Γ, φ∨ψ                 ⊢ Γ, ∀x.φ

  ⊢ Γ, φ[x:=t]
 ────────────── (∃)
  ⊢ Γ, ∃x.φ
```

Extensions to eliminate:

```
  ⊢ Γ, φ    ⊢ Γ, φ̄                  φ_L a proven theorem/axiom, φ_L ∈ Γ
 ──────────────────── (Cut, additive)   ──────────────────────────────── (CloseByLemma)
        ⊢ Γ                                        ⊢ Γ
```

(Ax) and (1) **fold in weakening** (arbitrary `Γ`); this is the paper's
"axiom + weakenings" and matters for the structural cases below.

## 2. Theorem

> **Hauptsatz (LKR).** Every LKR proof of `⊢ φ` using (Cut) and
> (CloseByLemma) can be transformed into a proof of `⊢ φ` using only the
> §11 rules — no (Cut), no (CloseByLemma). The transformation terminates.

Proof = three stages, each a terminating rewrite preserving the end-sequent.

## 3. Stage A — lemma elimination (CloseByLemma → splice + weaken)

Theorems form an **acyclic** dependency graph (each is verified before it
is cited). Process in topological order; cache each theorem's cut-free,
lemma-free proof.

To eliminate `CloseByLemma(L)` closing `⊢ Γ, φ_L`: `L`'s cached proof is a
§11 derivation of `⊢ φ_L`. **Replay it with `Γ` as inert extra context** —
every sequent in the spliced derivation carries `Γ` prepended; no rule
inspects `Γ` (logical rules act on their principal; (∀) freshness still
holds because `Γ`'s variables are passive — rectify if needed, §6); axioms
close ignoring `Γ`. The replayed derivation concludes `⊢ Γ, φ_L`. This is
exactly a derivation, no Cut introduced.

After Stage A the only remaining non-§11 rule is (Cut).

## 4. Stage B0 — additive Cut → multiplicative Cut + Contraction

LKR's (Cut) is additive (shared `Γ`). Gentzen's reductions are cleanest on
the **multiplicative** cut. They are interderivable:

```
  ⊢ Γ, φ   ⊢ Γ, φ̄                       ⊢ Γ, φ   ⊢ Γ, φ̄
 ──────────────── (additive)   ≡        ──────────────── (mult-Cut)   then  C×|Γ|
       ⊢ Γ                                  ⊢ Γ, Γ          ───────────────────────
                                                                      ⊢ Γ
```

Rewrite each additive (Cut) to `mult-Cut` followed by `|Γ|` contractions.
Now all cuts are multiplicative `⊢ Γ,φ   ⊢ Δ,φ̄ ⟹ ⊢ Γ,Δ`. The introduced
contractions are handled by the structural case §5.5 — *this is deliberate*:
it is exactly where contraction-against-cut is paid for, rigorously.

## 5. Stage B — Gentzen cut-elimination (multiplicative)

### 5.1 Measure

- **degree** `d(φ)` = structural complexity (logical depth) of the cut
  formula. `d(Cut) = d(φ)` of its cut formula.
- **rank/level** = combined height of the two immediate subderivations.

Pick a **topmost** cut of **maximal degree** `δ` (no cut of degree ≥ δ
above it). Reduce it by the case below. The well-order is the multiset of
cut-degrees under `>`; each step replaces a degree-`δ` cut by cuts of
degree `< δ` (principal/axiom) or moves it up at fixed degree while strictly
lowering rank (permutation/structural). Lexicographic `(δ, rank)`
terminates (Gentzen). Cost: worst-case non-elementary (the only risk; not
correctness).

### 5.2 Axiom cases (incl. atomic cut)

One premise is (Ax)/(1) with the cut formula principal:
- left `= ⊢ Γ, α, ᾱ` cut on `α` against right `⊢ Δ, ᾱ`: the conclusion
  `⊢ Γ, Δ, ᾱ`... — concretely, the cut against an axiom is removed by
  replacing the cut with the *other* premise, weakened/exchanged to the
  multiplicative conclusion. (The axiom contributes only context.)
- cut on `1` against any premise: drop, weaken. Symmetric for `φ̄`.

### 5.3 Principal logical cases (cut formula principal in BOTH premises)

Because the right cut formula is the dual `φ̄`, the two last rules are always
a dual pair:

**∧ vs ∨** — `φ = β∧γ`. left ends in (∧): `⊢ Γ₁,β` , `⊢ Γ₂,γ`
(`Γ₁⊎Γ₂=Γ`). right ends in (∨) on `φ̄ = β̄∨γ̄`: `⊢ Δ, β̄, γ̄`. Reduce to
two smaller cuts:
```
cut β :  ⊢ Γ₁,β    ⊢ Δ,β̄,γ̄   ⟹  ⊢ Γ₁,Δ,γ̄
cut γ :  ⊢ Γ₂,γ    ⊢ Γ₁,Δ,γ̄  ⟹  ⊢ Γ₁,Γ₂,Δ = ⊢ Γ,Δ
```
`d(β),d(γ) < d(β∧γ)`. ✓. (∨ vs ∧ is symmetric.)

**∀ vs ∃** — `φ = ∀x.β`. left ends in (∀) with eigenvar `a` (`a∉FV(Γ)`):
`⊢ Γ, β[x:=a]`. right ends in (∃) on `φ̄ = ∃x.β̄` with witness `t`:
`⊢ Δ, β̄[x:=t]`. Reduce: **substitute `a:=t` throughout the left
subderivation** (sound: `a` fresh, `Γ` fixed), giving `⊢ Γ, β[x:=t]`; then
```
cut β[x:=t] :  ⊢ Γ,β[x:=t]   ⊢ Δ,β̄[x:=t]   ⟹  ⊢ Γ,Δ
```
`d(β[x:=t]) = d(β) < d(∀x.β)`. ✓. Capture-avoidance: §6. (∃ vs ∀
symmetric.)

### 5.4 Permutation (commutative) cases

Cut formula **not principal** in one premise's last rule `R` (it is a side
formula of `R`). Permute the cut *above* `R`:
- `R` unary (∨, ∀, ∃, W, C, X on a non-cut formula): apply the cut to `R`'s
  premise, then re-apply `R`. Eigenvariable conditions preserved (the cut
  introduces only `Δ`'s formulas; rectify if `R=∀` and capture threatens).
- `R` binary (∧): the cut formula sits in exactly one premise of the (∧)
  split (the partition determines which); permute the cut into that premise,
  leave the other premise untouched, then re-apply (∧).
- `R` = a cut above: handled by the "topmost maximal-degree" choice (we
  never permute a cut past a cut of `≥` degree).

Each permutation strictly lowers rank at fixed degree.

### 5.5 Structural cases (where contraction is paid — the §15 wall, dissolved)

- **Weakening (dead cut).** Cut formula `φ` on a premise was introduced by
  (W): that premise is `⊢ Γ,φ` from `⊢ Γ`. Then the cut is *dead* — discard
  the **other** premise and weaken: `⊢ Γ ⟹ ⊢ Γ,Δ` by (W). The cut vanishes.
- **Contraction.** Cut formula `φ̄` on the right was produced by (C):
  `⊢ Δ,φ̄,φ̄ ⟹ ⊢ Δ,φ̄`. **Duplicate** the left premise `⊢ Γ,φ` and cut
  twice:
  ```
  cut φ : ⊢ Γ,φ   ⊢ Δ,φ̄,φ̄  ⟹  ⊢ Γ,Δ,φ̄
  cut φ : ⊢ Γ,φ   ⊢ Γ,Δ,φ̄  ⟹  ⊢ Γ,Γ,Δ   then C×|Γ| ⟹ ⊢ Γ,Δ
  ```
  This duplication is the **entire** content of "contraction-on-the-cut".
  In the sequent calculus it is sound, terminating (rank decreases; the two
  new cuts are pushed up and reduced), and standard. The §15 *native* path
  hit a wall here only because a **combinatorial proof** must represent the
  duplication as a skew fibration (a separate phase, HSW Thm 17) — a
  *representation* constraint, absent in the sequent calculus. **LKR cut-
  elimination therefore has no contraction wall.** This is the decisive
  reason the sequent side completes where §15-native did not.
- **Exchange.** Permute trivially.

### 5.6 Termination

By §5.1: every case either lowers the cut degree (5.2/5.3) or, at fixed
degree, strictly lowers rank (5.4/5.5). The contraction case duplicates
subderivations (size blowup) but the duplicated cuts are of the *same*
degree and pushed strictly upward, so the lexicographic measure still
descends. Gentzen's well-ordering ⟹ termination. Output is cut-free.

## 6. Eigenvariables & capture-avoidance (the B.2 hazard)

The (∀/∃) principal reduction and the (∀) permutation substitute terms into
subderivations. Substitution must be **capture-avoiding**: before
substituting `a:=t`, ensure the subderivation is **rectified** (bound
variables distinct from `FV(t)` and from each other) — Hughes Def 10.10
freshness, the precise condition the old `walk.cpp` B.2 bug violated.
Implement substitution on the proof term with on-the-fly α-renaming, or
rectify the whole subderivation first. This is a *correctness* obligation,
tested by re-verification (§8).

## 7. Implementation realization

Operate on the `DerivationTree` (`rebuild_tree`), not the flat stream:

1. Stage A: a `lemma_inliner` over the tree (reuse / adapt
   `lkr_to_comb/lemma_inliner`), dependency-ordered, caching cut-free
   proofs; replay-with-inert-context realized by prepending `Γ` to every
   spliced sequent's context bookkeeping.
2. Stage B0: rewrite each additive `Cut` node to `mult-Cut` + `Contraction`
   nodes.
3. Stage B: `reduce_cut(node)` = the §5 case analysis as tree rewrites,
   driven by a worklist that always selects a topmost maximal-degree cut.
   Each case returns a new subtree; substitution uses the §6 capture-
   avoiding substitution.
4. Flatten to a fresh §11 LKR program; re-run `LKRVerifier` (defense in
   depth) and feed `interpret_tree`.

The current `walk_reduce`, `try_strict_axiom_cut`, `try_linear_atom_cut`,
and the `ShiftPoint`/`SeqTracker` position-shifting machinery are
**deleted** — they are the "engineering hacks" this design replaces.
Positional bookkeeping is subsumed by operating on the typed tree with
explicit context partitions, not raw index arithmetic.

## 7a. Scope boundary — cuts on non-logical axioms are irreducible

A `Cut(F)` whose left premise closes by `CloseByLemma(F)` where `F` is a
**non-logical theory axiom** (not a proven theorem) is **irreducible**: the
§11 rules have the subformula property and cannot reintroduce `F`'s content,
and there is no proof of `F` to inline. This is the standard residue of
Gentzen's *extended* Hauptsatz (cuts on non-logical axioms remain). Three
consequences:

1. **Proven-theorem** `CloseByLemma` → Stage A inlines its cut-free proof;
   the surrounding cut becomes logical and is eliminated by Stage B.
2. **Logical** cuts (no axiom dependence) → fully eliminated by Stage B.
3. **Axiom** cuts → NOT eliminable here. To make an axiom-citing proof
   cut-free, the axioms must enter as *leaves* — i.e. reformulate the goal
   to the implication form `⊢ ¬A₁,…,¬Aₙ, T` (`⋀Aᵢ → T`) so each `Aᵢ` is a
   weakened-in hypothesis consumed by structural rules. **This reformulation
   is a wire-up concern, NOT part of cut-elimination**, and is decided
   separately (it changes the goal the comb proof is *of*).

**Therefore the reduction engine's correctness gate is pure logical cuts**
(e.g. `⊢ P→P` via `Cut(P)`) and proven-theorem inlining — not the
axiom-citing corpus shapes, which require (3) first.

## 8. Soundness test (the obligation)

`test/lkr_cut_elim_test.cpp` (already written, currently red) is the
round-trip property: for an LKR program `p` that `LKRVerifier`-accepts
against goal `G`, `eliminate_cuts(p)` (a) contains no `Cut` and no
`CloseByLemma`, and (b) `LKRVerifier`-accepts against the same `G`. Each
stage/case lands its own focused test under the math-first discipline
(spec → red test → impl → green → commit).

## 9. Phase plan

- **A** lemma inlining (replay-with-context) + its test.
- **B0** additive→multiplicative + contraction; test.
- **B1** axiom/atomic cases. **B2** ∧/∨ principal. **B3** ∀/∃ principal
  (+ §6 capture-avoidance). **B4** permutation cases. **B5** structural
  (W dead-cut, C duplication, X).
- **B6** termination harness (degree/rank worklist) + corpus as a *gate*
  only (never a design driver).
- **Wire-up**: route `lkr_to_comb::apply` cut-bearing branch through
  `eliminate_cuts → interpret_tree`.

## References

Gentzen 1934 (Hauptsatz, LK); Troelstra & Schwichtenberg, *Basic Proof
Theory* (cut-elimination by degree/rank induction); Hughes 2019 §11/§15;
HSW 2021 (decomposition Thm 17 — why *comb* representation needs a separate
contraction phase, i.e. why §15-native stalled). Memory:
`nd-normalization-track1-2026-05-21` (superseded by this — sequent side),
`reference-hsw-decomposition-2021`.
