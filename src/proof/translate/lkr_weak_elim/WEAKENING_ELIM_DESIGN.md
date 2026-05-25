# LKR Weakening-elimination — rigorous design

**Status:** spec. Stage 4 of the pipeline (cf. `[[pipeline-three-stages]]`),
running AFTER Stage 3 (`lkr_cut_elim/CUT_ELIM_DESIGN.md`) and BEFORE
`lkr_to_comb`. Eliminates all standalone `RWeaken` ops from a LKR
derivation, producing a W-free LKR proof of the same end-sequent.

## 0. Why a separate stage

After Stage 2's NDtoLKR (combining-elim) lands, several ZFC theorems hit
`lkr_to_comb`'s InputGate I-2 (`input_gate.cpp` §I-2): a Weakening op is
*load-bearing* (its appended entry is later referenced by And, Or,
Cut, …). I-2 is a representation constraint of the §15 combinatorial
proof framework — a fonet vertex cannot stand in for a weakening-derived
formula slot. The corpus signature is uniform:

```
LKRtoComb InputGate: I-2 violation — load-bearing Weakening at op #X
(And): left_partition[k]=Y references a weakening-derived entry.
```

Stage 3 (cut-elim) does NOT address this: §5.5 W-case handles only
*Cut-against-W* (dead cut), not standalone W. Stage 4's mandate: rewrite
the LKR proof to be W-free.

**Math fact:** Weakening is admissible in classical sequent calculus.
Every LK proof using `(W)` can be rewritten into an equivalent LK proof
that doesn't, by permuting W upward to the leaves and folding it into the
"axiom + weakenings" convention of `(Ax)` and `(1)`. This is standard
(Troelstra & Schwichtenberg §3.4); we mechanize it on the Deriv IR
from `lkr_cut_elim/deriv.h`.

This stage is disjoint from Stage 3:
- Stage 3 eliminates `RCut` and `RLemma`.
- Stage 4 eliminates `RWeaken`.
The two passes commute on inputs where Stage 3 does not introduce new W's
(it doesn't — see §5.5 in `CUT_ELIM_DESIGN.md`: dead-cut DELETES W; the
principal cases use the W-bridge for additive↔multiplicative conversion
internally, but those W's are local to the bridge and absorb at the
recursive reduce on `mcut`'s output, which lands cut-free at the leaves
of the bridge — and the leaves are RAx, which absorb W trivially per
§4.1 below).

## 1. The calculus (cross-reference)

Cross-link: `CUT_ELIM_DESIGN.md` §1 defines LKR's one-sided sequent
rules. Key facts re-stated here:

- `(Ax)` and `(1)` already **fold in weakening**: they close `⊢ Γ, α, ᾱ`
  for any `Γ`, and `⊢ Γ, 1` for any `Γ`. This is the *axiom convention*.
- `(CloseByLemma)` closes `⊢ Γ` whenever the lemma's NNF appears
  somewhere in `Γ` — also a "lemma + weakenings" convention.
- `(W)`: `⊢ Γ ⟹ ⊢ Γ, φ`. The verifier reads forward (appends `φ` to
  the top sequent); the IR's `RWeaken`'s `node.conclusion = Γ` (smaller)
  and `child.conclusion = Γ + φ` (bigger) — i.e. the child carries the
  post-W sequent (`[[stage3-math-findings-2026-05-26]]` finding #1).

## 2. Theorem

> **W-elimination Theorem (LKR).** Every LKR derivation `D` of `⊢ Γ`
> using rules from §1 + `(W)` can be transformed into a derivation `D'`
> of `⊢ Γ` using only the §1 rules — no `(W)`. The transformation
> terminates.

Proof sketch (constructive): induction on the size of `D`. At each
`RWeaken` node, perform one of the case reductions (§4) that either
absorbs the W at a leaf, replaces W with no-op (entry coincides with an
already-present formula by the W-tolerance of axiom conventions), or
permutes the W *upward* in the LK tree (= deeper in the IR) past the
rule above it. Each permutation step strictly decreases the W-permutation
measure (§5).

The transformation is sound: each reduction preserves verifier
acceptance of the surrounding subtree (defense-in-depth re-verified at
emit time, §8).

## 3. Procedure overview

Top-level driver `eliminate_weakenings(builder, root) -> DerivPtr`:

```
for each node N in post-order:
    recursively reduce N's children first
    if N is RWeaken:
        apply one of the §4 reductions; this may replace N with a
        non-W rule whose subtree contains the W "absorbed" into a
        deeper position (eventually a leaf)
    else:
        leave N alone
```

Each `RWeaken` is reduced eagerly. After children are reduced (W-free
below), the W at N is permuted into one child (or absorbed at a leaf
if N's child is already a leaf). The driver re-enters reduction on the
permuted W's new position until it lands at a leaf.

## 4. Case analysis

Notation: `W` = the current `RWeaken{added: φ, child: C}` node.
`N.conclusion = Γ` (smaller; without φ). `C.conclusion = Γ + φ` (bigger;
the W'd formula at position `|Γ|`).

### 4.1 W at a leaf — absorb (axiom convention)

If `C.rule` is a closing rule (`RAx`, `ROne`, `RLemma`):

- `C = RAx{a, b}` with `C.conclusion = Γ + φ`. The Ax-convention closes
  any sequent with a dual literal pair. `a, b` index positions in
  `C.conclusion`; since `Γ ⊆ C.conclusion`, the same Ax with the same
  `(a, b)` closes `Γ + φ` directly — but our W is REMOVING φ from the
  conclusion. So we replace W with a new `RAx{a, b}` whose conclusion
  is `Γ` (= W's conclusion). This works IFF neither `a` nor `b` equals
  `|Γ|` (= φ's position): if one of them did, the original Ax was using
  φ as part of its dual pair, and removing φ breaks the axiom.

  Two sub-cases for `C = RAx{a, b}`:
  - **Non-principal in φ:** `a, b < |Γ|`. Replace W with
    `RAx{a, b}` on conclusion `Γ`. ✓
  - **Principal in φ:** `a == |Γ|` or `b == |Γ|`. Then φ is one of the
    Ax's dual literals. The dual `ᾱ` (where α = φ) sits at the other
    position in Γ. So Γ contains both α and ᾱ — but wait, φ = α was
    introduced by W and is *not* in Γ. This case is *spurious*: the
    "axiom" was actually closing using a W'd formula, which means the
    surrounding context Γ does NOT close on its own. In a sound LKR
    program this case shouldn't appear at the top of an absorb attempt
    — but if it does, we cannot eliminate the W; report it irreducible
    and bail. (In practice the producers — NDtoLKR, lkr_cut_elim — only
    emit principal-W axioms via `try_axiom_cut_principal`, which builds
    `RWeaken{added, clone(other_premise)}` where the W is followed by a
    non-leaf subtree. So principal-at-leaf doesn't arise from the
    pipeline.)

- `C = ROne{idx}`. The (1) convention closes any sequent where
  `entries[idx] = ¬⊥`. If `idx < |Γ|`, the ¬⊥ is in Γ; replace W with
  `ROne{idx}` on conclusion `Γ`. If `idx == |Γ|`, the W'd entry was the
  ¬⊥ — spurious like the principal-Ax case; report irreducible.

- `C = RLemma{target, source_name}`. The lemma-convention closes when
  the lemma's NNF appears in the sequent. `RLemma` doesn't reference any
  specific position; it scans the sequent (`verifier.cpp` line 183-185).
  If the lemma's NNF is `φ`, the lemma was using the W'd entry — the
  closure depends on it; mark irreducible. Otherwise the lemma's NNF is
  in Γ already; replace W with `RLemma{target, source_name}` on Γ. To
  distinguish: re-NNF the target sentence and compare to `φ`.

### 4.2 W above unary rules — permute past inner rule

The inner rule `R` is unary (one child), and its sequent transformation
is local (doesn't reference φ's position by definition of "non-principal
in φ"). Form:

```
Γ                    after permutation:    Γ
| W(φ)                                     | R'(adjusted)
Γ+φ                                        Γ'
| R                                        | W(φ)
Γ'+φ-ish                                   Γ'+φ-ish
```

In all cases, R's *principal position* (if any) must be `< |Γ|` (not at
`|Γ|`, where φ sits). The W-principal case (R operates on the W'd entry)
is handled separately in §4.3.

#### 4.2.1 `R = ROr{p, child}` (p < |Γ|)

ROr's effect: replace `entries[p]` (= ϕ∨ψ) with `ϕ`, append `ψ`.

- **Before**: `child.conclusion = Γ' + φ + ψ` where `Γ'` is Γ with
  `[p] → ϕ`. Verifier order: W appends φ first, then Or appends ψ —
  hence φ at position `|Γ|` and ψ at position `|Γ|+1`.
- **After**: ROr fires first on Γ → conclusion `Γ' + ψ`. Then W appends
  φ → conclusion `Γ' + ψ + φ`. The new order is `ψ` then `φ`.

The original `child.conclusion` had `[..., φ, ψ]` at the tail, but the
permuted result has `[..., ψ, φ]`. To make the original child's ops
type-check on the new ordering, we need ONE `RExchange` at the inner
position to restore the original order. Equivalent and simpler: just
rewrite the inner child to expect the new order — but that requires
adjusting all downstream position references in the subtree, which is
brittle.

**Resolution:** insert an `RExchange{|Γ|+1, |Γ|+2}` (well, with adjusted
indices for the actual sequent size) between the new W and the original
child. The exchange swaps the trailing `(ψ, φ)` to `(φ, ψ)`, restoring
the original child's expected sequent. The exchange is structural, not
a W, so it doesn't reintroduce a W-elim obligation.

Result IR:
```
RWeaken{φ, ROr{p, child}}       →       ROr{p, RWeaken{φ, RExchange{|Γ|, |Γ|+1, child}}}
```

(Indices computed relative to the inner node's conclusion size.)

#### 4.2.2 `R = RForall{p, eigen, child}` (p < |Γ|)

RForall's effect: replace `entries[p]` (= ∀x.β) with `β[x:=eigen]`. Same
size sequent; position p preserved.

- **Before**: `child.conclusion = Γ'' + φ` where `Γ''` is Γ with
  `[p] → β[x:=eigen]`. φ at position `|Γ|`.
- **After**: Forall fires first on Γ → conclusion `Γ''`. Then W appends
  φ → conclusion `Γ'' + φ`. Same sequent as before. ✓

No exchange needed. **Capture obligation:** the original Forall required
`eigen ∉ FV(Γ)` (Hughes Def 10.10 freshness). After permutation, the
new Forall fires on Γ before φ is introduced; the freshness condition
shrinks to `eigen ∉ FV(Γ)`, which is implied by the original (Γ ⊆ Γ+φ).
So if the original passed freshness, the permuted does too. ✓

Result IR:
```
RWeaken{φ, RForall{p, eigen, child}}    →    RForall{p, eigen, RWeaken{φ, child}}
```

But there is a *separate* obligation: if `eigen ∈ FV(φ)`, then in the
permuted form, the W introduces φ AFTER Forall fires — the eigen is now
in the inner sequent, and adding φ (which mentions eigen) is fine
*verifier-wise* (W doesn't have a freshness condition). But this means
the eigen could clash with downstream rules if they expect the eigen to
be fresh in the rest of the proof. Since the permuted W is structurally
deeper than the Forall in IR, the downstream of W is the inner child
which is *under* Forall in the original — so the eigen scope is already
extended over child. No new clash. ✓

#### 4.2.3 `R = RExists{p, witness, child}` (p < |Γ|)

Symmetric to RForall. Witness is a closed term (in the SSA term env),
so no eigenvar-style scoping concern. Permutation is direct:
```
RWeaken{φ, RExists{p, w, child}}    →    RExists{p, w, RWeaken{φ, child}}
```

#### 4.2.4 `R = RExchange{i, j, child}` (i, j < |Γ|)

Exchange swaps two positions in Γ. φ at `|Γ|` is untouched. Permutation
is direct:
```
RWeaken{φ, RExchange{i, j, child}}  →   RExchange{i, j, RWeaken{φ, child}}
```

If `i == |Γ|` or `j == |Γ|`: the exchange involves φ. This means the
W'd entry is being moved to a position in Γ. Two sub-cases:
- **Non-trivial use:** the exchange is followed by ops that reference
  the moved position; the W is load-bearing through a different index.
  Permute by swapping the W's `added` formula's apparent slot.
  Equivalently: re-emit the W at the swapped position. Operationally,
  the cleanest realization is to keep the W where it is and let the
  exchange "fall through" — but this fails because the IR has W at
  fixed position `|Γ|`. Reify by rewriting the W's added formula as the
  formula at the swapped position after the exchange would have run.
  Concretely: if `j == |Γ|`, the new W'd position is `i`; emit
  `RExchange{i, j=|Γ|, child}` BEFORE the W. No — the layering breaks.

  **Simpler resolution:** detect this case and TRY to eliminate the
  Exchange first by rewriting downstream position references in
  child. If that's too invasive, leave the W in place and report
  partial reduction (the I-2 check may still pass if no AND/OR/CUT
  later references the W'd slot through any chain of exchanges; the
  marks tracking in `input_gate.cpp` propagates through Exchange
  swaps).

For the initial Stage 4 implementation, **only handle `i, j < |Γ|`**
and report irreducible for the W-involving case. ZFC corpus is a
post-hoc gate (per `[[corpus-is-test-not-design-driver]]`), and the
math leaves both cases sound — the latter is just harder mechanics.

#### 4.2.5 `R = RContract{i, j, child}` (i, j < |Γ|)

Contract removes the duplicate at position `j` (preserves position `i`).
φ at `|Γ|` is untouched. Permutation:
```
RWeaken{φ, RContract{i, j, child}}  →   RContract{i, j, RWeaken{φ, child}}
```

If `i == |Γ|` or `j == |Γ|`: the contraction involves the W'd entry.
For the contract-preserving case (`i == |Γ|`): φ is the kept entry; the
other duplicate at `j < |Γ|` was in Γ. Permuted form: skip the W
entirely (φ is already in Γ at position `j`, so we don't need to W it
in). For `j == |Γ|`: φ is the dropped duplicate; permuted form is
trivial — just skip the W (child sees Γ already minus φ).

These W-vs-Contract interactions reduce W's, not just permute. Treat in
a separate sub-case from the general unary permutation.

#### 4.2.6 `R = RWeaken{ψ, child}` (W above W)

Two stacked Ws. Both add to the tail. Permutation: pick either order.
Conventional: leave outer-W as-is, recurse on inner-W. (The outer-W's
inner sequent is the outer-W-conclusion + φ; after recursing on
inner-W, that inner-W is gone, and outer-W proceeds.) No structural
swap necessary.

### 4.3 W's added formula is principal in inner R — decompose-then-W

If R's principal position equals `|Γ|` (= φ's slot), R is operating on
the W'd formula. This means φ = R's principal-shaped formula. Cases:

#### 4.3.1 `R = ROr{|Γ|, child}` with W'd φ = ϕ∨ψ

The Or decomposes the W'd ∨. The child's conclusion is `Γ + ϕ + ψ`
(verifier replaces position `|Γ|` with ϕ, appends ψ). Permuted form:
introduce ϕ and ψ as two W's, skipping the Or entirely. New IR:
```
RWeaken{φ=ϕ∨ψ, ROr{|Γ|, child}}   →   RWeaken{ϕ, RWeaken{ψ, child}}
```
(`child.conclusion` unchanged: `Γ + ϕ + ψ`.) Now we have two stacked
W's; recurse on each.

#### 4.3.2 `R = RForall{|Γ|, eigen, child}` with W'd φ = ∀x.β

The Forall instantiates the W'd ∀ at eigen. Child's conclusion is
`Γ + β[x:=eigen]`. Permuted: skip Forall, W in β[x:=eigen] directly:
```
RWeaken{φ=∀x.β, RForall{|Γ|, eigen, child}}  →  RWeaken{β[x:=eigen], child}
```
(child.conclusion unchanged.) **Capture obligation:** verify
`eigen ∉ FV(Γ)`. Same as the original Forall required; satisfied by
construction since the original verifier accepted it.

#### 4.3.3 `R = RExists{|Γ|, witness, child}` with W'd φ = ∃x.β

Symmetric. Permuted:
```
RWeaken{φ=∃x.β, RExists{|Γ|, w, child}}  →  RWeaken{β[x:=w], child}
```

#### 4.3.4 `R = RAnd{|Γ|, partition, left, right}` with W'd φ = ϕ∧ψ

The And splits via the W'd ∧. LEFT child has `(sorted partition) + ϕ`;
RIGHT has `(complement) + ψ`. The partition picks formulas from Γ — but
the W'd ∧ contributed NO content other than itself; LEFT and RIGHT
each need their own ϕ/ψ at a fresh slot. Permuted: replace LEFT with
`RWeaken{ϕ, LEFT_child}` and RIGHT with `RWeaken{ψ, RIGHT_child}`,
keeping the And's structural partition over Γ only — but now there's
no ∧ to split. So the And rule itself disappears.

But the IR's RAnd requires a principal ∧ — we can't just delete it.
Instead, replace the whole `RWeaken{ϕ∧ψ, RAnd{...}}` with **two
independent W's** on the *original conclusion Γ*, where each child of
the And becomes a top-level proof:

This doesn't quite work in the IR shape — RAnd is a binary split that
combines the two sides into a single ∧ conclusion. Without a real ∧
formula in Γ, we can't apply RAnd.

**Resolution:** this case is a *spurious And on a W-introduced ∧*. The
W introduced ϕ∧ψ as part of Γ-padding; the And decomposed it
immediately. The decomposition is "free" in that neither side needed
to PROVE ϕ or ψ in the W'd-only sense — but the LEFT and RIGHT children
were constructed assuming `(partition) + ϕ` and `(complement) + ψ`. To
preserve the proof: the W'd ∧ is never "really used" if neither LEFT
nor RIGHT recursively references the appended `LEFT_phi` or
`RIGHT_psi`. If they do reference them, the W's load-bearing-ness
percolates into the children and continues to be problematic.

The fix: recursively apply Stage 4 to LEFT and RIGHT. Inside LEFT (with
conclusion `(partition) + ϕ`), the new W'd entry is at the end. If
LEFT's proof never references it, eliminating it is trivial (entry
unused). If LEFT references it via downstream Or/And/etc., we recurse
the W-elim through LEFT in the same way.

**Implementation strategy:** detect this case, push the W INTO each
child of the And (W'd into LEFT with formula ϕ at LEFT's tail; W'd into
RIGHT with formula ψ at RIGHT's tail), and remove the outer And. But
without an And there's no ∧ at the top — Γ alone is the conclusion.

The cleanest formulation: this case **does not arise from well-formed
Stage-3 / NDtoLKR output**. Stage 2's combining-elim and Stage 3's
reductions don't synthesize W'd compound formulas that are immediately
And-decomposed; the corpus failures are about `partition[k] = (W-derived
atomic side formula)`, not principal compounds. Mark §4.3.4 as
**out-of-scope for the initial impl**; if a future producer needs it,
extend the spec.

### 4.4 W above binary rules — permute past one side

Inner rule is binary (RAnd, RCut). Two children. The W'd formula must
go to ONE child only (since both children share the OUTER conclusion
in some additive way, but the inner partition routes Γ's entries to
LEFT or RIGHT).

#### 4.4.1 `R = RAnd{p, partition, left, right}` with p < |Γ| (W non-principal)

The And splits `Γ + φ` into:
- LEFT_concl = `sorted(partition_with_φ_slot) + ϕ_left`
- RIGHT_concl = `complement_without_φ_slot + ψ_right`

where the W'd `φ` at position `|Γ|` lives in EITHER `partition`'s LEFT
side OR the complement's RIGHT side — depending on whether the original
proof included `|Γ|` in `partition`.

**This is the exact corpus failure pattern** (Peirce + ZFC ordered_pair
load-bearing-W). The InputGate I-2 flags this when `|Γ| ∈ partition`.

Permuted form: the And should fire on Γ alone (with the W'd entry
removed from partition). The And splits Γ via the partition restricted
to indices < |Γ|. After And, the side that originally got the W'd
entry gets a fresh `RWeaken{φ, …}` on top.

Concretely, let `in_left = (|Γ| ∈ partition)`. Then:

- **Permuted partition**: `partition'` = `partition \ {|Γ|}` (drop the
  W-position from partition). All other indices retained.
- **New LEFT child**: if `in_left`, wrap `left` in
  `RWeaken{φ, child=left}`; the W's appended slot becomes position
  `(|sorted(partition')| + 1)` in LEFT's pre-And conclusion — adjust
  upstream LEFT child's expectation of where φ sits. (Since `left`
  was built expecting φ at position `|partition| + (in_left ? 0 : ...)`
  — careful index-arithmetic; spec leaves this to the impl.)
- **New RIGHT child**: if `!in_left`, wrap `right` in `RWeaken{φ, child=right}`.

Result IR:
```
RWeaken{φ, RAnd{p, partition, left, right}}
    →
RAnd{
    p,
    partition',
    in_left  ? RWeaken{φ, left}  : left,
    in_left  ? right             : RWeaken{φ, right}
}
```

Index re-mapping inside `left` / `right` is needed because removing
`|Γ|` from partition shifts the index of `φ` in LEFT's conclusion. The
W's added formula sits at LEFT's TAIL (after the original partition
contents), so the index shift is mechanical: φ's new position in LEFT
is `|sorted(partition')|` (one less than before, since `|Γ|` was the
largest index and got dropped).

#### 4.4.2 `R = RCut{cut_formula, left, right}`

Stage 4 runs AFTER Stage 3, so the input has no `RCut`. This case is
unreachable; assert and bail.

If wire-up runs Stage 4 BEFORE Stage 3 (e.g., for debugging): the W is
non-principal in the Cut (the Cut's principal is the cut formula at the
*last* slot of each premise — which is NOT the W'd `|Γ|` since the cut
formula is added after Cut fires, not before). So W permutes into BOTH
LEFT and RIGHT (additive Cut shares Γ; the W'd entry is part of Γ).

Result IR (if needed):
```
RWeaken{φ, RCut{f, left, right}}
    →
RCut{f, RWeaken{φ, left}, RWeaken{φ, right}}
```

(Note: additive Cut means BOTH children's conclusions are `Γ + φ + f`
resp. `Γ + φ + ¬f`. The W'd `φ` must travel to both — duplicating the
W. This duplicates work, but each W is independently eliminable.)

### 4.5 Summary table

| W's child rule R | Action | Note |
|---|---|---|
| `RAx` non-principal-in-φ | Absorb: replace with `RAx{a,b}` on Γ | §4.1 |
| `RAx` principal-in-φ | Irreducible (shouldn't arise from pipeline) | §4.1 |
| `ROne{idx}`, idx < |Γ| | Absorb: replace with `ROne{idx}` on Γ | §4.1 |
| `ROne{idx}`, idx = |Γ| | Irreducible | §4.1 |
| `RLemma`, NNF ≠ φ in Γ | Absorb: replace with `RLemma` on Γ | §4.1 |
| `RLemma`, NNF = φ | Irreducible | §4.1 |
| `ROr{p, …}`, p < |Γ| | Permute with `RExchange` to fix order | §4.2.1 |
| `RForall{p, …}`, p < |Γ| | Permute directly | §4.2.2 |
| `RExists{p, …}`, p < |Γ| | Permute directly | §4.2.3 |
| `RExchange{i,j,…}`, i,j < |Γ| | Permute directly | §4.2.4 |
| `RContract{i,j,…}`, i,j < |Γ| | Permute directly | §4.2.5 |
| `RWeaken{ψ, …}` (W over W) | Recurse on inner | §4.2.6 |
| Same as above with W-principal | Decompose-then-W | §4.3 |
| `RAnd{p, part, L, R}`, p < |Γ| | Permute into one side | §4.4.1 |
| `RCut{…}` | Unreachable (post Stage 3) | §4.4.2 |

## 5. Termination

Measure: `(#W ops, max depth from leaf of any W)` lex order.

- Absorb cases (§4.1): `#W` decreases. ✓
- Permute cases (§4.2, §4.4): `#W` constant; depth from leaf decreases
  by 1 for the permuted W. ✓
- Decompose-then-W (§4.3): one W becomes one or two W's that are at
  the same or DEEPER position in IR (closer to leaves). `#W` may
  increase by 1 (§4.3.1, §4.3.4), but the depth-from-leaf strictly
  decreases for the new W's (they sit deeper than the original).
  Termination still holds because at fixed depth, the recursion
  bottoms out at §4.1 absorb cases.

Standard `(W-count, max-depth)` lex order; or equivalently, the
multiset-of-W-depths under a well-founded order.

## 6. Eigenvariable & capture concerns

Permuting W past Forall (§4.2.2): the Forall's freshness condition
`eigen ∉ FV(Γ)` is preserved (Γ ⊆ Γ+φ implies the freshness in the
larger sequent restricts to the smaller).

Decompose-then-W on Forall (§4.3.2) requires substituting `x := eigen`
into the W'd body. Capture-avoidance: the W'd formula β might mention
eigen via embedding (e.g., a previous Forall's eigen reused). Since
`eigen` is introduced by the original Forall, and the substituted body
`β[x:=eigen]` is well-formed by construction (the verifier already
accepted it).

No new α-renaming machinery beyond what Stage 3 §6 already provides
in `lkr_cut_elim/reduce.cpp::substitute_in_deriv` — Stage 4 only
performs LOCAL transformations on the W node and its immediate child;
it does NOT recursively substitute into subderivations.

## 7. Implementation

`src/proof/translate/lkr_weak_elim/`:
- `reduce.h` — exports `eliminate_weakenings(builder, root) -> DerivPtr`.
- `reduce.cpp` — case analysis from §4, dispatched on `W.child->rule`.

Reuses `lkr_cut_elim/deriv.h` for the Deriv IR (build/emit/`clone`,
`substitute_in_deriv`). The driver mirrors Stage 3's `eliminate_cuts`
structure (post-order recurse + per-node reduction attempt).

Helper signatures (mirroring Stage 3):

```cpp
util::Result<DerivPtr> eliminate_weakenings(
    FormulaBuilder& builder, const Deriv& root);

// Attempt one reduction step on a RWeaken node. Returns nullptr if no
// case fires (irreducible at this node). Otherwise returns the
// rewritten subtree (which may itself contain RWeaken nodes — caller
// recurses).
DerivPtr try_reduce_weakening(FormulaBuilder& builder, const Deriv& w_node);
```

`reduce.cpp` dispatches:
```cpp
if (std::get_if<RAx>(&child->rule)) return absorb_ax(...);
if (std::get_if<ROne>(&child->rule)) return absorb_one(...);
if (std::get_if<RLemma>(&child->rule)) return absorb_lemma(...);
if (std::get_if<ROr>(&child->rule)) return permute_or(...);
// ... etc.
```

Each case is a focused tree rewrite; the rewritten subtree is returned
fresh (no in-place mutation; `clone` semantics throughout).

## 8. Soundness obligation

Test `test/weak_elim_test.cpp`: for each Deriv `D` that
`LKRVerifier`-accepts against goal `G`, `eliminate_weakenings(D)`
(a) contains no `RWeaken`, (b) `LKRVerifier`-accepts against `G`.

Per `[[math-first-discipline]]`: spec → RED test → impl → GREEN → commit.
Each §4 case lands its own focused test; the §4.5 table is the test
matrix.

The round-trip property `emit(eliminate_weakenings(D))` ⊨ `G` is the
ultimate gate. After Stage 3 + Stage 4 + wire-up, the ZFC ordered_pair
parity gate is: 19/19 cuts AND no W-rejections at I-2.

## 9. Phase plan

- **W1** §4.1 leaf absorption (RAx non-principal, ROne, RLemma).
  Smoke test + spec verification.
- **W2** §4.2 unary permutation (Or, Forall, Exists, Exchange,
  Contract, W-over-W). One focused test per inner rule.
- **W3** §4.4.1 RAnd permutation. The corpus-failure case; gates
  ZFC parity.
- **W4** Driver `eliminate_weakenings` + termination harness.
- **W5** Wire-up: `lkr_to_comb` runs `eliminate_cuts` (Stage 3) then
  `eliminate_weakenings` (Stage 4) before `interpret_tree`.
- **W6** §4.3 decompose-then-W cases (only if a producer needs them
  — corpus is a post-hoc gate, not a driver).

## 10. References

Troelstra & Schwichtenberg, *Basic Proof Theory* §3.4 (weakening
admissibility); Hughes 2019 §11 (axiom + weakening convention);
`src/proof/translate/lkr_cut_elim/CUT_ELIM_DESIGN.md` §5.5 (Cut-vs-W
dead-cut, already handled by Stage 3); `lkr_to_comb/LKR_TO_COMB_DESIGN.md`
§4.4 (Case B: load-bearing W rejected); InputGate I-2
(`src/proof/translate/lkr_to_comb/input_gate.cpp` §I-2).
