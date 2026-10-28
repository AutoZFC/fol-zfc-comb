# Compact LKR: the identity as one instruction

> A builder library for LKR programs (the sequent mirror, the identity) and
> a compact IR in which an identity is a single instruction, with its
> expansion to LKR. The LKR verifier, `lkr::Instr` and Stage 3 are
> unchanged. Math first: spec here, tests (RED), then impl.

Notation: X' is NNF(X), X̄ is NNF(¬X). For a sequent S, S[p] is its entry at
position p. |A|∨∧ is the number of binary connectives of A, |A|Q its
quantifier occurrences, |A|lit its literal occurrences (A as a tree).

## 0. Problem

LKR closes a goal only on a pair of dual literals (AxiomLit) or on 1 (One).
The identity ⊢ Γ, A, Ā on a compound A is therefore η-expanded: an Or and
an And per binary connective, a Forall and an Exists per quantifier, an
AxiomLit per literal, 2|A|∨∧ + 2|A|Q + |A|lit ops.

**Lemma M (the expansion is minimal).** Let A contain no 1 or 0 and no
predicate symbol twice. Every LKR proof of ⊢ A, Ā without CloseByLemma
has at least |A|lit AxiomLit leaves. *Proof.* Trace a literal occurrence ℓ
of the end sequent up the proof; a Cut formula is never an ancestor of an
end-sequent occurrence. Suppose no ancestor of ℓ is closed by an AxiomLit.
Renaming ℓ and its ancestors to a fresh predicate q keeps every rule
valid, so the renamed proof proves the end sequent with ℓ replaced by q.
That sequent is not valid: A is read-once without constants, so some
interpretation makes the sequent's value depend on ℓ, and q can be
interpreted against it. So every one of the 2|A|lit occurrences has an
ancestor in an AxiomLit, and an AxiomLit closes two. □ Each leaf also
needs the connectives above it decomposed on both sides, and a proof tree
cannot share a subproof between branches.

So no LKR program spells the identity shorter. The expansion is, however,
a function of the sequent, the two positions and the eigenvariables it
introduces. A consumer that needs a proof's content but not its atomic form,
such as storage or a prover choosing moves, can record the identity as one
instruction and expand it on demand.

Goals:

- **C1.** A compact IR: LKR ops plus Identity(a, b, e).
- **C2.** Its meaning is its expansion E (§2), the one producer of atomic
  identity ops.
- **C3.** The LKR verifier, `lkr::Instr` and Stage 3 are unchanged. A
  compact program is trusted only through E's output passing LKRVerifier.
- **C4.** A producer writes either form through one interface, and the
  forms agree: E(compact) = atomic, op for op (Theorem E1).
- **C5.** The sequent mirror and the identity are a library for any LKR
  producer, not translator internals.

## 1. The identity X

X(S, a, b, e) closes S on entries a ≠ b, emitting in preorder. One goal
(S, a, b) at a time:

1. S[a] = 1: One(a). S[b] = 1: One(b).
2. S[a] and S[b] literals: AxiomLit(a, b).
3. Orient: if S[a] is a ∧ or an ∃, swap a and b.
4. S[a] = φ ∨ ψ, S[b] = β1 ∧ β2 with φ̄ = β1 and ψ̄ = β2 (straight) or
   φ̄ = β2 and ψ̄ = β1 (swapped): Or(a), so φ stays at a and ψ is appended;
   then And(b) with β1's partner LEFT and β2's partner RIGHT (copies first
   when a partner is needed on both sides, §3). Recurse LEFT, then RIGHT.
5. S[a] = ∀v.φ, S[b] = ∃v.ψ: Forall(a) with the next eigenvariable u, then
   Exists(b) with u's TermRef; recurse on (a, b).
6. Otherwise X fails: the entries are not duals.

**Eigenvariables.** The k-th Forall X emits takes e + k (k from 0). Each
step of 4 and 5 consumes one node of S[a] and one of S[b], so X emits at
most |S[a]|Q Foralls, and exactly |S[a]|Q when the entries are duals.
`identity_eigens(A)` = |A|Q, the count a producer reserves.

## 2. The compact IR and its expansion E

```
CompactInstr = lkr::Instr | Identity{a, b, e}
```

Identity(a, b, e) closes the current goal. A TermRef in a compact program
names a Forall by its compact index. A producer chooses e as it chooses a
Forall's eigenvariable: e, …, e + |S[a]|Q − 1 must be fresh for the whole
program, so the verifier's freshness check holds wherever X uses them.

**E(C).** Replay C against the open-goals stack seeded with [NNF(goal)],
mirroring LKRVerifier's transition for every op (§3 Sequent). An lkr op is
written through, with an Exists witness renamed from its compact index to
the index of the Forall it produced. An Identity is written as X(S, a, b, e).

**Input gate.** E rejects:

- an op with no open goal, or goals left open at the end;
- an op its Sequent rule rejects (§3): a position out of range, a
  principal of the wrong shape, One on an entry that is not 1, Contraction
  of unequal entries, an And partition that is not distinct, in range and
  principal-free;
- an Exists whose witness is not an earlier Forall;
- a Cut whose formula is a deferred AST. Compact producers hold resolved
  formulas; resolving names belongs to the verifier.
- an Identity on which X fails.

Whether AxiomLit's literals are duals, whether CloseByLemma's formula is
present, and the eigenvariable condition stay LKRVerifier's checks.

**Theorem E1 (agreement).** Run a producer twice on the same input, once
through CompactSink (output C) and once through LkrSink (output P), where
the producer reads the sink only through `next_ref()` and passes its
values only into Exists witnesses. Then E(C) = P.

*Proof.* The runs make the same rule calls with the same positions,
formulas and eigenvariables, except that witness TermRefs differ by the
map from compact to expanded indices. Both reserve |S[a]|Q eigenvariables
at each identity from the same supply. By induction on C: before each
instruction, E's mirror equals the producer's sequent, because both apply
the same transitions of §3 to the same arguments. A producer's
needs-based And is a sequence of Duplicates followed by the raw And, and E
replays exactly those ops. So E writes each lkr op as P does, with
witnesses renamed by the map, and expands each Identity to the ops
LkrSink wrote at that point: the same X on the same S, a, b, e. □

**Theorem E2 (trust).** E is not trusted. Its output is accepted only when
LKRVerifier verifies it, so an error in E yields a rejected program, never
an unsound one.

## 3. Code

Library `src/proof/lkr_build/` (namespace `logic::proof::lkr_build`):

| unit | contents |
|---|---|
| `nnf_shapes.h` | shape predicates on NNF formulas (moved from `nd_to_lkr`) |
| `sequent.{h,cpp}` | `TermBinding`; `Sequent`, the mirror of the verifier's current goal, with one method per LKR rule; `Premise`, `Split` |
| `op_sink.{h,cpp}` | `OpSink` (`next_ref`, `emit`, `identity`); `LkrSink` writes LKR and expands identities; `CompactSink` writes compact LKR |
| `identity.{h,cpp}` | `identity_eigens`, `expand_identity` (X) |
| `compact.h` | `Identity`, `CompactInstr` |
| `expand.{h,cpp}` | `ExpandIdentities : Pass<CompactInstr, lkr::Instr>` (E) |

`Sequent` mirrors LKRVerifier's transition for every op (Exchange,
Weakening, Duplicate, Contraction, Or, Forall, Exists, And, Cut and the
closing ops). Each method checks the positions and shapes it needs, applies
the transition and writes the op. Branching rules consume the sequent and
return a `Split`, whose `moved[p]` tells where parent entry p went. Two And
entry points: `and_split(principal, left_partition)` is the raw op;
`and_rule(principal, left_needs, right_needs)` first duplicates the entries
both sides need (the copy goes RIGHT) and then calls `and_split`. Cut
follows the verifier: LEFT gets φ', RIGHT gets NNF(¬φ').

The library never allocates eigenvariables: `forall_rule` takes its
eigenvariable, `identity` takes e. Producers allocate. The translator draws
both from its FormulaBuilder, reserving `identity_eigens(S[a])` before an
identity, so its other eigenvariables are the same with either sink.

Translator `nd_to_lkr`:

- `SequentShadow` = `lkr_build::Sequent` + dual slots + σ. It forwards the
  rules, allocates eigenvariables for Forall and identities, and after And
  or Cut gives each premise the slots whose entries moved to it, and σ.
- `emit_close.{h,cpp}` and `nnf_shapes.h` move into the library.
  `TermBinding` moves too.
- `Dispatcher` writes to an `OpSink&`.
- `NDtoLKR` keeps its contract: LKR out, verified. `NDtoCompactLKR` emits
  compact LKR, and its output gate verifies E of it. Both run one shared
  translate routine.

## 4. Tests

- `lkr_build_test`:
  - Sequent rules, checked by LKRVerifier.
  - X on literals, 1/0, straight and swapped ∨/∧, and nested and mixed
    quantifiers. The eigenvariables are e, e + 1, … and their count is
    `identity_eigens`. Non-duals fail.
  - E on hand-written compact programs, including an Exists whose witness
    E must rename past an expanded identity, and every lkr op.
  - E's input gate rejections, one per bullet of §2.
- `nd_to_lkr_demands_test`: every case also runs NDtoCompactLKR and checks
  E(C) = P op for op (Theorem E1), in both share modes.
- Corpus bug-catcher, after implementation:
  - P is unchanged by the refactor (op-stream hash before and after).
  - E(C) = P on every translated claim.

## 5. Future work

- **Proof search.** An environment builds proofs with `Sequent` and
  `CompactSink`, and checks E of them. Eliding forced moves (invertible
  rules) is a focusing layer above compact LKR under the same
  expand-then-verify discipline.
- **Serialization** of compact programs.
- **Sharing repeated identities.** A tree cannot share subproofs; sharing
  needs references to subproofs parametric in positions and
  eigenvariables in the checked format. That is a checker change, out of
  scope.
- **Other LKR producers** can use `Sequent` instead of their own mirrors.
