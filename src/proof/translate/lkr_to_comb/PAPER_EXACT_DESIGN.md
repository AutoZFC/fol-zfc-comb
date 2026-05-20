# Paper-exact LKR→Comb translator (Hughes §11.1)

This is a from-scratch reimplementation of the LKR→Comb translation that
follows Hughes (2019) §11.1 **exactly**: each cut-free LKR rule is
interpreted as a local operation on combinatorial proofs, folded
bottom-up over the LKR derivation tree. Lemma 11.2 guarantees each step
produces a well-defined combinatorial proof, so the result is correct by
construction.

It runs **in parallel** with the legacy `walk.cpp` global construction
until P8, then replaces it for the cut-free path.

**Scope:** cut-free LKR (Hughes §11's nine rules). `Cut` and
`CloseByLemma` (§15 extensions) are out of scope for this effort.

## Representation

A node of the derivation tree proves its **conclusion sequent** Γ. We
carry the combinatorial proof of Γ as:

```
struct NodeProof {
    comb::Fograph        target;     // G(Φ(Γ)), Φ(Γ) = φ1 ∨ … ∨ φn
    comb::Fonet          source;     // the fonet N
    std::vector<size_t>  fibration;  // f : V_source → V_target
};
```

`Φ(Γ)` is the right-associated ∨ of the sequent entries (Hughes §11
intro). Because `∨ = +`, `G(Φ(Γ)) = G(φ1) + … + G(φn)`: the disjoint
union of the per-entry fographs, laid out in sequent order, with no
cograph edges between entries and binding edges internal to each entry.

## Bottom-up fold

`rebuild_tree` (tree.cpp) already turns the LKR op-stream into a
`DerivationTree`. We fold it:

- **LeafNode** (AxiomLit / One): base combinatorial proof (P1).
- **LinearNode** (Or, Exchange, Weakening, Forall, Exists): one operation
  on the single child's NodeProof.
- **BranchingNode** (And): combine the two children's NodeProofs.

The op's **conclusion sequent** is `sequent_before[op_idx]` from
`replay_sequents`; the children's conclusions are the op's hypotheses.
Each operation builds the conclusion target `G(Φ(Γ))` and maps the
child source(s) into it via the canonical homomorphism for that rule.

## The canonical homomorphisms (Hughes §11.1)

Each rule relates `G(H)` (hypothesis) and `G(C)` (conclusion) by a
canonical vertex map. Going bottom-up the map is applied to the child's
fibration image:

| Rule | G(H) vs G(C) | map | source change |
|---|---|---|---|
| Or | `G(H) = G(C)` (∨ = + assoc.) | identity | none (`g = f`) |
| Exchange | reorder φ,θ blocks | iso (permutation) | relabel f via the permutation |
| Weakening | `G(C) = G(H) + G(φ)` | injection | none; new target vtxs uncovered |
| Forall | `G(C) = G(H-Γ) + (•x + G(φ))` | injection + new `•x` | add `•x` to source iff `f⁻¹(V_φ)≠∅`, map to the x-binder |
| Exists | `G(C) = G(Γ) + (•x × G(φ))` | injection + new `•x` | add binder vtx, edges to `P=f⁻¹(V_{φ{x↦t}})`, map to x-binder |
| And | `G(C) = G(Γ1)+G(Γ2)+(G(φ1)×G(φ2))` | two injections | fusion of K1,K2 at P1,P2 |
| Contraction | `G(C) = G(Γ)+G(φ)` (one copy) | surjection (φ,φ'→φ) | collapse duplicators |

Exact index arithmetic for each map is specified in that rule's phase.

## Invariant maintained at every node

After each operation, `NodeProof` must satisfy the Def. 6.1 conditions
that the verifier checks — so we can (and do, in tests) run `CombVerifier`
against `G(Φ(Γ))` at every node:

1. `target == G(Φ(Γ))` (Phase 1).
2. `source` is a fonet (Phase 2): linked, legal+rectified binders,
   dualizer, no induced bimatching.
3. `fibration` is a skew bifibration (Phase 3).

Building each operation to preserve these (Lemma 11.2) is the proof
obligation discharged per phase.

## Files

- `interpret_tree.{h,cpp}` — NodeProof, the fold, per-rule operations.
- `comb_build.{h,cpp}` — CombProof builder helpers: `build_sequent_fograph`,
  canonical homomorphism constructors, fibration composition.
- Reused: `tree.cpp` (rebuild_tree), `sequent_replay.cpp` (conclusion
  sequents), `input_gate`/`output_gate`, the comb verifier.
- Replaced at P8 (cut-free path): `walk.cpp`, `build_target.cpp`,
  `cut_augment.cpp`, `alpha_rename.cpp`.

## Phases

P0 scaffolding · P1 leaves · P2 Or/Exchange · P3 Weakening · P4 Forall ·
P5 Exists · P6 And · P7 Contraction · P8 cut-free end-to-end + retire walk.
