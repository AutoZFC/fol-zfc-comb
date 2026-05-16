# LKR → Combinatorial Proof: Detailed Walkthrough

Reference: Hughes 2019, *First-order proofs without syntax*, arXiv 1906.11236, §11.1.

This document explains the LKR-to-combinatorial-proof translation rule by rule, with concrete worked examples. At every step we write down explicitly:

- The **fonet `N`** we have so far (source graph + colouring/links + dualizer).
- The **fograph `G(C)`** we map to (the conclusion sequent's formula graph).
- The **fibration `f : N → G(C)`** (the vertex map).

---

## Notation

- `•α` — an atom-labelled vertex with literal `α` (e.g. `•p`, `•p̄x`).
- `•x` — a binder vertex labelled by variable `x`.
- `+` — disjoint union of cographs (no edges between).
- `×` — join (every vertex on the left adjacent to every vertex on the right).
- `┄┄` — link (a colour class of two pre-dual literals in a fonet).
- `─────` — graph edge (in either source or target).
- `↓` — fibration map from a source vertex to its target vertex.

For the source fonet we use vertex names `u_α`, `v`, etc. For the target fograph we use `•α` notation. The map `f` is given as a list of bindings `u ↦ •α`.

---

## §11.1 rules at a glance

| LKR op | Hypothesis sequent(s) | Conclusion sequent | Effect on `(N, f)` |
|---|---|---|---|
| `AxiomLit(α, ᾱ)` | (none — closing) | `α, ᾱ` | Build `N = {u_α, u_ᾱ}` linked, `f = id` |
| `One(idx)` | (none — closing) | `1` | Build `N = {u_1}` (no link), `f = id` |
| `Or(p)` | `Γ, φ, θ` | `Γ, φ ∨ θ` | `N` and `f` unchanged (graphs equal) |
| `Exchange(i, j)` | `Γ, φ, θ, Δ` | `Γ, θ, φ, Δ` | Compose `f` with canonical iso |
| `Weakening(φ)` | `Γ` | `Γ, φ` | `N` unchanged; `f` composed with injection `G(Γ) ↪ G(Γ) + G(φ)` |
| `Forall(p)` | `Γ, φ` | `Γ, ∀x.φ` | If preimage of `G(φ)` non-empty, add `•x` vertex to `N` mapping to target's new `•x` |
| `Exists(p, t)` | `Γ, φ{x↦t}` | `Γ, ∃x.φ` | If preimage of `G(φ{x↦t})` non-empty, add new vertex `v` to skeleton with edges to that preimage; map `v ↦ •x` |
| `Contraction(i, j)` | `Γ, φ, φ'` | `Γ, φ` | Compose `f` with surjection folding `φ' ↦ φ`, then collapse duplicators (delete one of two preimages of each duplicator outer universal binder) |
| `And(p, partition)` | `Γ_1, φ` and `Γ_2, θ` | `Γ_1, Γ_2, φ ∧ θ` | If both strong (or both weak): fuse `N_1, N_2` at witness portions. If mixed: keep weak side, discard strong |
| `Cut(θ)` | `Γ, θ` and `Γ, ¬θ` | `Γ` (augmented with `θ ∧ ¬θ`) | Same as `And` between θ-portion of left and ¬θ-portion of right; augment running goal |
| `CloseByLemma(L)` | (none — closing) | (any sequent containing `φ_L`) | Push `L`'s pre-built combinatorial proof |

---

## Per-rule operations in detail

### 1. `AxiomLit(α, ᾱ)` — closing, `α, ᾱ`

**Conclusion sequent** `C = α, ᾱ`.

**Build:**
- `N` = two atom-vertices `{u_α, u_ᾱ}` with labels `α` and `ᾱ` respectively. Both vertices share a single colour ⇒ one link `{u_α, u_ᾱ}`.
- `G(C) = •α + •ᾱ` (two atom-vertices, no edge).
- `f = { u_α ↦ •α, u_ᾱ ↦ •ᾱ }`.

```
   N:   u_α ┄┄┄┄┄┄ u_ᾱ        (link, same colour)
         │           │
         ↓           ↓
   G(C): •α          •ᾱ        (no edge)
```

**Fonet check:** linked ✓; dualizer empty (no universal binders) is valid because the link's literals `α` and `ᾱ` are already dual. No induced bimatching (only one link, no leap edges).

---

### 2. `One(idx)` — closing, `1`

**Conclusion** `C = 1` (truth literal alone).

**Build:**
- `N = {u_1}`, single atom-vertex labelled `1`. **No colour** (`1` is not in any link).
- `G(C) = •1`.
- `f = { u_1 ↦ •1 }`.

The minimal fonet (Hughes paper, footnote 11).

---

### 3. `Or(p)` — `Γ, φ, θ ⊢ Γ, φ ∨ θ`

`Φ(H) = (φ_1 ∨ ... ∨ φ_k) ∨ φ ∨ θ` and `Φ(C) = (φ_1 ∨ ... ∨ φ_k) ∨ (φ ∨ θ)`.

As fographs, `+` is associative → **`G(H) = G(C)`** identically.

**Build:** `N` unchanged, `f` unchanged.

This is the cheapest rule: no graph modification at all.

---

### 4. `Exchange(i, j)` — `X` rule

Cograph `+` is commutative → `G(H) = G(C)` modulo a canonical permutation of vertex labels.

**Build:** `N` unchanged. `f' = x ∘ f` where `x : G(H) → G(C)` is the canonical isomorphism (a bijection on vertex sets respecting labels).

If you represent vertices by occurrence-identity rather than positional index, `x = id` and `Exchange` becomes a no-op.

---

### 5. `Weakening(φ)` — `Γ ⊢ Γ, φ`

**Hypothesis:** `f : N → G(H)` where `G(H) = G(Γ)`.

**Conclusion target** `G(C) = G(Γ) + G(φ)` — the new formula's graph is added by disjoint union.

**Build:**
- `N` unchanged.
- Let `w : G(H) ↪ G(C)` be the canonical injection.
- `f' = w ∘ f`.

Effect: the new vertices in `G(φ) ⊂ G(C)` have **no preimage** in `N`. They are "uncovered."

```
Hypothesis:                  Conclusion:
   N                            N                       (unchanged)
   │                            │
   ↓ f                          ↓ f'  =  w ∘ f
   G(Γ)                         G(Γ)        G(φ)
                                            ▲
                                   (no preimage in N)
```

---

### 6. `Forall(p)` — `Γ, φ ⊢ Γ, ∀x.φ`

**Hypothesis:** `f : N → G(H)` where `G(H) = G(Γ) + G(φ)`. Side condition: `x` not free in `Γ`.

**Conclusion target** `G(C) = G(Γ) + (•x + G(φ))`. The `•x` is added with `+` ⇒ universal binder.

Let `a : G(H) ↪ G(C)` be the canonical injection (skipping the new `•x` vertex).

Let `P = f⁻¹(V_{G(φ)})` be the **`φ`-portion** in the source.

**Two cases:**

#### Case A: `P = ∅` (nothing in `N` maps into `G(φ)`)

`G(φ)` was effectively weakened in. Build:
- `N` unchanged.
- `f' = a ∘ f`. The new `•x` in target is uncovered.

#### Case B: `P ≠ ∅`

Add a new vertex `b_x` to the source, labelled by variable `x`. The new source is `•x + N` (disjoint — universal). Build:
- `N' = {b_x} ∪ V_N`, edges of `N` carry over, no new edges (because `+`).
- `f' = (a ∘ f) ∪ { b_x ↦ •x }`.

The added `b_x` is a universal binder vertex in `N'`. Its scope (smallest proper strong module containing it) must contain at least one `x`-literal in `P` ⇒ legal.

---

### 7. `Exists(p, t)` — `Γ, φ{x↦t} ⊢ Γ, ∃x.φ`

**Hypothesis:** `f : N → G(H)` where `G(H) = G(Γ) + G(φ{x↦t})`.

**Conclusion target** `G(C) = G(Γ) + (•x × G(φ))`. The `•x` is added with `×` ⇒ existential, joined to `G(φ)`.

Let `e : G(H) ↪ G(C)` be the canonical injection treating `G(φ{x↦t})` as `G(φ)`.

**Drop labels** of `N`: `N_s` is the skeleton of `N`. Let `f_s : N_s → G(H)`.

Let `P = f_s⁻¹(V_{G(φ{x↦t})})` be the **witness portion** in the skeleton.

**Two cases:**

#### Case A: `P = ∅` (φ was weakened in)

`N` unchanged; `f' = e ∘ f`. The new `•x` is uncovered.

#### Case B: `P ≠ ∅`

Add new vertex `v` to `N_s`, plus edges `{v, w}` for every `w ∈ P`. Call result `N_s'`. Build:
- `f_s' : N_s' → G(C)` extends `e ∘ f_s` with `v ↦ •x`.
- Re-attach labels (inherited from `f_s'` via target labels for `v`, original labels otherwise).

The added edges are required because `•x` in the target is joined to all of `G(φ)` (`×`), so the binding-fibration condition demands `v` to be adjacent to everything mapping into `G(φ)`.

---

### 8. `Contraction(i, j)` — `Γ, φ, φ' ⊢ Γ, φ` with `φ' ≅_α φ`

**Hypothesis:** `f : N → G(H)` where `G(H) = G(Γ) + G(φ) + G(φ')`.

**Conclusion target** `G(C) = G(Γ) + G(φ)`. The two copies of `G(φ)` in the hypothesis fold into one.

Let `c : G(H) ↠ G(C)` be the canonical surjection that folds `G(φ')` onto `G(φ)` vertex-by-vertex (matching corresponding occurrences via the alpha-equivalence).

**Drop labels** of `N`: skeleton `N_s` with `f_s : N_s → G(H)`. Compose: `h = c ∘ f_s : N_s → G(C)`.

**Duplicator collapse.** A **duplicator** is an outer universal binder `b ∈ V_{G(C)}` whose preimage `h⁻¹(b)` has *exactly two* vertices.

For each duplicator `b`:
- `h⁻¹(b) = {v_1, v_2}` ⇒ delete one of them (say `v_2`) from `N_s`.

Let `N_s⁻` be the result. Define `g_s : N_s⁻ → G(C)` as the restriction of `h`. Re-attach canonical labels (each vertex `u ∈ N_s⁻` gets the label of `g_s(u)` in `G(C)`).

**Why duplicator collapse?** Without it, two universal binders in `N_s` would map to the same target binder, putting them in each other's scope and violating fograph well-formedness (footnote 24, Hughes paper).

---

### 9. `And(p, left_partition)` — `Γ_1, φ_1` and `Γ_2, φ_2` ⊢ `Γ_1, Γ_2, φ_1 ∧ φ_2`

**Hypotheses:** `f_i : N_i → G(H_i)` where `G(H_i) = G(Γ_i) + G(φ_i)` for `i = 1, 2`.

**Conclusion target** `G(C) = G(Γ_1) + G(Γ_2) + (G(φ_1) × G(φ_2))`. Note the **join** between the two conjuncts.

Let `z_i : G(H_i) ↪ G(C)` be the canonical injection.

**Witness portions:** `P_i = f_i⁻¹(V_{G(φ_i)})`.

**Strong/weak classification:**
- `f_i` is **strong** if `P_i ≠ ∅`.
- `f_i` is **weak** if `P_i = ∅`.

#### Case A: both strong, or both weak

Build `N` = **fusion** of `N_1` and `N_2` at portions `P_1, P_2`:
- Disjoint union `N_1 ⊔ N_2`.
- Add edge `{v, w}` for every `v ∈ P_1`, `w ∈ P_2`.

The colouring (links) is inherited from both `N_1` and `N_2` separately — they remain disjoint colour classes.

Build map: `g = (z_1 ∘ f_1) ∪ (z_2 ∘ f_2) : N → G(C)`.

The new edges are required because `G(C)` has the join `G(φ_1) × G(φ_2)`, so the skew-fibration condition demands every vertex over `φ_1` be adjacent (in `N`) to every vertex over `φ_2`.

#### Case B: one weak, one strong (say `f_1` weak, `f_2` strong)

Build `N = N_1`. Map `g = z_1 ∘ f_1`.

The strong side's source is **discarded**. Soundness intuition: if `f_1` is weak, then the proof of `Γ_1, φ_1` doesn't actually use `φ_1`, so it's a proof of `Γ_1` alone, which suffices for `Γ_1, Γ_2, φ_1 ∧ φ_2` via weakening.

(This case is asymmetric and worth verifying on a concrete `1 ∧ p` example before relying on it in code.)

---

### 10. `Cut(θ)` — §15

**Hypotheses:** two sub-derivations producing `f_L : N_L → G(Γ ∪ {θ})` and `f_R : N_R → G(Γ ∪ {¬θ})`.

**Strategy (paper §15 / Theorem 15.1):** an *n-cut* combinatorial proof of `Γ` is interpreted as an ordinary combinatorial proof of `Γ ∨ ⋁_i (θ_i ∧ ¬θ_i)`.

**Per-cut operation:**

1. Augment the running goal: each `Cut(θ)` adds a `θ ∧ ¬θ` disjunct at the top level. Maintain the augmented formula `Γ_aug = Γ ∨ ⋁ (θ_i ∧ ¬θ_i)` alongside execution.

2. Apply the `And` rule's operation between the **`θ`-portion of `f_L`** and the **`¬θ`-portion of `f_R`**:
   - Compute `P_L = f_L⁻¹(V_{G(θ)})` and `P_R = f_R⁻¹(V_{G(¬θ)})`.
   - Strong/weak classification on `P_L, P_R`.
   - Fuse (or keep weak side) per the And rule.

3. The result is a combinatorial proof of `Γ ∨ (θ ∧ ¬θ)` (`Or` is identity).

After processing all cuts, the final combinatorial proof is over `Γ_aug`.

---

### 11. `CloseByLemma(L)`

Not a §11.1 rule. Two strategies:

**Strategy A (inline).** Maintain a registry `theorem_proofs : name → CombinatorialProof`. At a `CloseByLemma(L)` op, look up `L`'s combinatorial proof `f_L : N_L → G(φ_L)` and push it as the proof of the current goal.

**Strategy B (cut-via-§15).** Require that `CloseByLemma(L)` is used only as the LEFT closer of a preceding `Cut(φ_L)`. Then `CloseByLemma` returns L's pre-built combinatorial proof for the LEFT subgoal, and the §15 mechanism handles modular composition uniformly.

Recommend Strategy B: preserves modularity without proof-size blowup.

---

# Worked examples

Each example walks through the entire LKR program op-by-op, recording at every step:

- The **fonet `N`** (source graph + links + dualizer).
- The **fograph `G(C)`** (target).
- The **fibration `f : N → G(C)`** (vertex map, written as a list of bindings).

---

## Example A: `p ∨ p̄` (excluded middle)

### LKR program

```
op[0]: Or { principal=0 }
op[1]: AxiomLit { lit_a=0, lit_b=1 }
```

### Verifier trace

```
init:   open_goals = [[ p ∨ p̄ ]]
op[0]:  open_goals = [[ p, p̄ ]]              (Or replaces principal with phi, appends psi)
op[1]:  open_goals = []                       (AxiomLit closes)
```

### Translation tree (bottom-up)

```
        Or(0)              ← op[0]
          │
       AxiomLit(0,1)       ← op[1]   (leaf)
```

### Step 1: process leaf `AxiomLit(0,1)` (sequent `[p, p̄]`)

**Build:**
- `N₁`:
  - vertices: `{ u_p, u_p̄ }`
  - labels: `u_p : p`, `u_p̄ : p̄`
  - edges: ∅
  - links: one link, `{u_p, u_p̄}` (single colour shared by both)
- `G(C₁) = G([p, p̄]) = •p + •p̄`:
  - vertices: `{ •p, •p̄ }`
  - edges: ∅
- `f₁ = { u_p ↦ •p, u_p̄ ↦ •p̄ }`

```
   N₁:    u_p ┄┄┄┄┄ u_p̄         (linked)
           │          │
           ↓          ↓
   G(C₁): •p          •p̄         (no edge)
```

### Step 2: process `Or(0)` (transforms `[p, p̄]` ↦ `[p ∨ p̄]`)

**Operation:** graphs are equal as fographs (`+` associative). `f` and `N` unchanged.

**Build:**
- `N₂ = N₁` (unchanged)
- `G(C₂) = G([p ∨ p̄]) = •p + •p̄ = G(C₁)`
- `f₂ = f₁ = { u_p ↦ •p, u_p̄ ↦ •p̄ }`

### Final result

```
   N (fonet):   u_p ┄┄┄┄┄ u_p̄
                 │          │
                 ↓          ↓
   G(p ∨ p̄):    •p          •p̄
```

- **Fonet `N`**: 2 vertices, 1 link `{u_p, u_p̄}`, no edges, empty dualizer.
- **Fograph `G(p ∨ p̄)`**: 2 vertices, no edges.
- **Fibration `f`**: identity bijection on vertex sets.

### Verification

- Fonet: linked (every literal in a link) ✓; dualizer empty (no universal binders) — link's atoms `p` and `p̄` are already dual ✓; no induced bimatching ✓.
- Skew bifibration: identity on graphs is trivially label-preserving, a directed-graph fibration on the (empty) binding graph, and a skew fibration on the cograph ✓.

---

## Example B: `(p ∧ q) ⇒ (q ∧ p)`

NNF: `¬(p ∧ q) ∨ (q ∧ p)` = `(p̄ ∨ q̄) ∨ (q ∧ p)`.

### Goal fograph

```
G((p̄ ∨ q̄) ∨ (q ∧ p)) = •p̄ + •q̄ + (•q × •p)

   •p̄        •q̄        •q ─────── •p
                       (∧-edge)
```

### LKR program

```
op[0]: Or { principal=0 }
op[1]: Or { principal=0 }
op[2]: And { principal=2, left_partition=[1] }
op[3]: AxiomLit { lit_a=0, lit_b=1 }       (LEFT subgoal closer)
op[4]: AxiomLit { lit_a=0, lit_b=1 }       (RIGHT subgoal closer)
```

### Verifier trace

```
init:   [[ (p̄ ∨ q̄) ∨ (q ∧ p) ]]
op[0]:  [[ (p̄ ∨ q̄), (q ∧ p) ]]
op[1]:  [[ p̄, q̄, (q ∧ p) ]]
op[2]:  pop [p̄, q̄, (q∧p)],
         push RIGHT = [p̄, p],
         push LEFT  = [q̄, q]
        stack: [ [p̄, p], [q̄, q] ]   (top is [q̄, q])
op[3]:  close [q̄, q]   stack: [ [p̄, p] ]
op[4]:  close [p̄, p]   stack: []
```

(Partition `[1]` sends entry-1 = `q̄` to LEFT alongside `φ = q`; entry-0 = `p̄` goes to RIGHT alongside `θ = p`.)

### Translation tree

```
                Or(0)                 ← op[0]
                  │
                Or(0)                 ← op[1]
                  │
              And(2, [1])             ← op[2]
              /         \
       AxiomLit(0,1)   AxiomLit(0,1)
       on [q̄, q]       on [p̄, p]
       ← op[3]         ← op[4]
```

### Step 1: leaf `AxiomLit(0,1)` on `[q̄, q]` (LEFT, op[3])

**Build:**
- `N_L`: `{ u_q̄, u_q }`, link `{u_q̄, u_q}`, no edges.
- `G(H_L) = •q̄ + •q`.
- `f_L = { u_q̄ ↦ •q̄, u_q ↦ •q }`.

```
   N_L:     u_q̄ ┄┄┄┄┄ u_q       (link 1)
             │           │
             ↓           ↓
   G(H_L):  •q̄          •q       (no edge)
```

### Step 2: leaf `AxiomLit(0,1)` on `[p̄, p]` (RIGHT, op[4])

**Build:**
- `N_R`: `{ u_p̄, u_p }`, link `{u_p̄, u_p}` (a *separate* link from `N_L`'s — different colour class), no edges.
- `G(H_R) = •p̄ + •p`.
- `f_R = { u_p̄ ↦ •p̄, u_p ↦ •p }`.

```
   N_R:     u_p̄ ┄┄┄┄┄ u_p       (link 2)
             │           │
             ↓           ↓
   G(H_R):  •p̄          •p
```

### Step 3: `And(2, [1])` consumes `f_L`, `f_R`, produces proof of `[p̄, q̄, q ∧ p]`

**Hypotheses unpacked:**
- LEFT: `H_L = [q̄, q]`, so `Γ_1 = [q̄]`, `φ_1 = q`.
- RIGHT: `H_R = [p̄, p]`, so `Γ_2 = [p̄]`, `φ_2 = p`.

**Conclusion target** `G(C₃) = G([p̄, q̄, q ∧ p]) = •p̄ + •q̄ + (•q × •p)`:
```
   •p̄        •q̄        •q ───── •p
```

**Witness portions:**
- `P_L = f_L⁻¹(V_{G(q)}) = f_L⁻¹({•q}) = { u_q }` ⇒ non-empty ⇒ **strong**.
- `P_R = f_R⁻¹(V_{G(p)}) = f_R⁻¹({•p}) = { u_p }` ⇒ non-empty ⇒ **strong**.

Both strong ⇒ **fuse** at `P_L, P_R`.

**Fusion:**
- Vertex set: `{u_q̄, u_q, u_p̄, u_p}` (disjoint union).
- Edges of `N_L` ∪ edges of `N_R` ∪ `P_L × P_R` = ∅ ∪ ∅ ∪ `{ {u_q, u_p} }` = `{ {u_q, u_p} }`.
- Links: `{u_q̄, u_q}` (from `N_L`) and `{u_p̄, u_p}` (from `N_R`) — kept as two separate colour classes.
- Dualizer: empty (still no universal binders).

**Map:** `g = (z_L ∘ f_L) ∪ (z_R ∘ f_R)` where `z_L, z_R` inject into `G(C₃)`. Concretely:
```
g = { u_q̄ ↦ •q̄, u_q ↦ •q, u_p̄ ↦ •p̄, u_p ↦ •p }
```

**State after And:**

```
   N₃:     u_q̄ ┄┄┄┄┄ u_q ─────── u_p ┄┄┄┄┄ u_p̄
            link 1       (∧-edge)      link 2
             │            │            │            │
             ↓            ↓            ↓            ↓
   G(C₃):   •q̄           •q ────── •p             •p̄
                          (∧-edge)
```

- Fonet `N₃`: 4 vertices, 2 links `{u_q̄, u_q}` and `{u_p̄, u_p}`, 1 edge `{u_q, u_p}`, empty dualizer.
- Fograph `G(C₃)`: 4 vertices, 1 edge `{•q, •p}`.
- Fibration `f₃ = g`: as listed above.

### Step 4: `Or(0)` (op[1]) — `[p̄, q̄, q ∧ p] ↦ [(p̄ ∨ q̄), q ∧ p]`

Graphs equal (`+` associativity). No change.

**State:**
- `N₄ = N₃` unchanged.
- `G(C₄) = G([(p̄ ∨ q̄), q ∧ p]) = •p̄ + •q̄ + (•q × •p) = G(C₃)`.
- `f₄ = f₃`.

### Step 5: `Or(0)` (op[0]) — `[(p̄ ∨ q̄), q ∧ p] ↦ [(p̄ ∨ q̄) ∨ (q ∧ p)]`

Graphs equal. No change.

**State:**
- `N₅ = N₄` unchanged.
- `G(C₅) = G([(p̄ ∨ q̄) ∨ (q ∧ p)]) = same fograph`.
- `f₅ = f₄`.

### Final result

```
   N (fonet):
                u_q̄ ┄┄┄┄┄┄ u_q ─────── u_p ┄┄┄┄┄┄ u_p̄
                 link 1       (edge)         link 2

                  │            │            │            │
                  ↓            ↓            ↓            ↓

   G((p̄ ∨ q̄) ∨ (q ∧ p)):
                •q̄           •q ─────── •p             •p̄
                              (∧-edge)
```

- **Fonet `N`**: 4 vertices `{u_q̄, u_q, u_p̄, u_p}`, 2 links, 1 edge `{u_q, u_p}`, empty dualizer.
- **Fograph `G((p̄ ∨ q̄) ∨ (q ∧ p))`**: 4 vertices `{•q̄, •q, •p̄, •p}`, 1 edge `{•q, •p}`.
- **Fibration `f`**: `{ u_q̄ ↦ •q̄, u_q ↦ •q, u_p ↦ •p, u_p̄ ↦ •p̄ }`.

### Verification

**Fonet:**
- Linked: every literal in a link ✓.
- Dualizer: empty (no universal binders); link 1's atoms `q̄, q` are dual ✓, link 2's atoms `p̄, p` are dual ✓.
- Leap graph: no dependencies (no universal binders); 2 link edges in leap graph.
- Induced bimatching: only `N`-edge is `{u_q, u_p}`, which is not a link, so no `W` can induce a matching in both `N` and the leap graph simultaneously ✓.

**Skew bifibration:**
- Label-preserving ✓.
- Binding fibration: empty graphs both sides ✓.
- Skew fibration on cographs: target edge `{•q, •p}` lifts: source edge `{u_q, u_p}` connects `f⁻¹(•q)` and `f⁻¹(•p)`. ✓ (No edge in target without an analog in source.)

✓ Combinatorial proof.

---

## Example C: `∀x. (px ⇒ px)` (smallest quantifier example)

NNF: `∀x. (p̄x ∨ px)`.

### Goal fograph

```
G(∀x. (p̄x ∨ px)):

   •x        •p̄x       •px
   
   (•x is a universal binder, no edge to its scope literals because of '+')
   (•p̄x and •px have no edge between them either, because of '∨')
```

Wait — `G(∀x. (p̄x ∨ px)) = •x + G(p̄x ∨ px) = •x + •p̄x + •px`. All three vertices, no edges.

### LKR program

```
op[0]: Forall { principal=0, eigen=0 }     // fix x as eigen f_0
op[1]: Or     { principal=0 }
op[2]: AxiomLit { lit_a=0, lit_b=1 }
```

### Verifier trace

```
init:    [[ ∀x. (p̄x ∨ px) ]]
op[0]:   [[ p̄(f_0) ∨ p(f_0) ]]            (instantiate body with eigenvariable f_0)
op[1]:   [[ p̄(f_0), p(f_0) ]]
op[2]:   []
```

### Translation tree

```
       Forall(0, eigen=0)         ← op[0]
            │
          Or(0)                    ← op[1]
            │
       AxiomLit(0, 1)              ← op[2]
       on [p̄(f_0), p(f_0)]
```

### Step 1: leaf `AxiomLit(0,1)` on `[p̄(f_0), p(f_0)]`

**Build:**
- `N₁`: `{ u_p̄, u_p }`, link `{u_p̄, u_p}`, no edges.
  - `u_p̄` labelled `p̄(f_0)` (atom with the fixed-variable argument).
  - `u_p` labelled `p(f_0)`.
- `G(H₁) = •p̄(f_0) + •p(f_0)`.
- `f₁ = { u_p̄ ↦ •p̄(f_0), u_p ↦ •p(f_0) }`.

```
   N₁:     u_{p̄(f_0)} ┄┄┄┄┄ u_{p(f_0)}     (link)
              │                  │
              ↓                  ↓
   G(H₁):  •p̄(f_0)              •p(f_0)
```

### Step 2: `Or(0)` (op[1]) — graphs equal, no change.

`N₂ = N₁`, `G(C₂) = G(H₁) = G([p̄(f_0) ∨ p(f_0)])` (same vertices), `f₂ = f₁`.

### Step 3: `Forall(0, eigen=0)` (op[0]) — `[p̄(f_0) ∨ p(f_0)] ↦ [∀x. (p̄x ∨ px)]`

**Conclusion target** `G(C₃) = •x + G(p̄x ∨ px)`. The `•x` is added with `+` ⇒ universal.

But — we need to be careful about the literal labels. The hypothesis target has atoms with the eigenvariable `f_0`; the conclusion target has atoms with the bound variable `x`. The `Forall` operation effectively re-labels: replace every occurrence of `f_0` with `x` in the source's atom labels.

Equivalently: the source's literals had been labelled with the eigenvariable to make the freshness check work in LKR; in the combinatorial-proof world, we re-label them with `x` (which is the bound variable in the target's binder vertex `•x`).

**Witness-portion check:**
- `P = f₂⁻¹(V_{G(p̄x ∨ px)}) = { u_p̄, u_p }` ⇒ non-empty ⇒ **Case B** of Forall.

**Build:**
- Add new vertex `b_x` to `N`, labelled by variable `x`.
- New source `N₃`: `{ b_x, u_p̄, u_p }`. Edges: ∅ (since `+` adds disjointly).
  - Re-label: `u_p̄ : p̄x`, `u_p : px` (eigen `f_0` ↦ bound `x`).
- Links: `{u_p̄, u_p}` (still valid since after re-labelling these are still pre-dual).
- Dualizer: now `b_x` is a universal binder. Dualizer must assign it a term. The simplest valid choice: `δ(x) = x` (identity term). Verify the link: `p̄x{x↦x} = p̄x` and `px{x↦x} = px` are dual ✓.

**Map:**
```
f₃ = { b_x ↦ •x, u_p̄ ↦ •p̄x, u_p ↦ •px }
```

**State:**
```
   N₃:    b_x        u_{p̄x} ┄┄┄┄ u_{px}      (link, no edges)
           │            │           │
           ↓            ↓           ↓
   G(C₃): •x         •p̄x         •px           (no edges; universal binder + body)
```

### Final result

- **Fonet `N`**: 3 vertices `{b_x, u_p̄x, u_px}`, 1 link `{u_p̄x, u_px}`, no edges, dualizer `δ(x) = x`.
- **Fograph `G(∀x. (p̄x ∨ px))`**: 3 vertices `{•x, •p̄x, •px}`, no edges.
- **Fibration `f`**: `{ b_x ↦ •x, u_p̄x ↦ •p̄x, u_px ↦ •px }`.

### Verification

**Fonet:**
- Linked ✓ (`b_x` is a binder, not a literal; literals `u_p̄x` and `u_px` are linked).
- Dualizer `δ(x) = x` works: link's literals become `p̄x, px` which are dual ✓.
- Dependencies: `(•x_existential, •y_universal)` pairs — there's no existential in `N`, so no dependencies, no leaps beyond the link.
- No induced bimatching ✓.

**Skew bifibration:**
- Label-preserving ✓.
- Binding fibration: `b_x` binds `u_p̄x` and `u_px` in `N` (binder-to-literals directed edges). `•x` binds `•p̄x` and `•px` in `G(C)`. The map preserves these directed edges ✓.
- Skew fibration on cograph: no edges in either graph ⇒ trivially ✓.

✓ Combinatorial proof.

---

## Example D: `∃x.(p̄x ⇒ ∀y. py)` (the paper's flagship)

NNF: `∃x.(p̄x ∨ ∀y. py)`.

### Goal fograph

```
G(∃x.(p̄x ∨ ∀y. py)) = •x × ( •p̄x + (•y + •py) )
                    = •x × ( •p̄x + •y + •py )

           ┌────── •p̄x
   •x ─────┼────── •y
           └────── •py
```

`•x` is existential (joined to its scope by `×`); `•y` is universal (separate from `•py`).

### LKR program

The straightforward strategy: peel `∃` (with witness `f_0` from a fresh variable introduced by `Forall` somewhere else? — or use a Cut, or use the symmetry trick).

The cleanest LKR program here uses a `Forall` to fix `y` first, then `Exists` with witness `f_0` (the y-eigen) for `∃x`:

Actually — this is subtle. In LKR (one-sided right), to prove `∃x.(p̄x ∨ ∀y. py)` we need to instantiate `∃x` with some witness. A standard LK proof of this uses Contraction + two ∃-instantiations to make this work; for our walkthrough, the cleanest version:

```
op[0]: Exists { principal=0, witness=<y-eigen> }
       Wait — y-eigen doesn't exist yet.
```

Actually we need a Cut. Here's a clean derivation:

```
init:   [ ∃x.(p̄x ∨ ∀y. py) ]

Step a: Cut(p̄(f_0)) ?  — no, we need to introduce f_0 via Forall first.
```

Let me redo: the cleanest LK proof uses **Contraction**. We weaken-then-instantiate twice.

```
op[0]: Weakening { formula = ∃x.(p̄x ∨ ∀y. py) }
       → [ ∃x.(p̄x ∨ ∀y. py), ∃x.(p̄x ∨ ∀y. py) ]   (two copies)

op[1]: Exists { principal=0, witness=<a placeholder term> }
```

This is getting complicated and witness-term-dependent. For the walkthrough's purposes, I'll **skip the LKR derivation** and just describe the resulting combinatorial proof shape, since the main goal is to show the combinatorial output, not the specific LKR ops.

### Final combinatorial proof (matches paper Fig. 1)

```
   N (fonet):

       b_x ┄┄┄┄┄┄┄┄┄┄ b_y                  (dependency: leap edge)
        │              │
        ▼              ▼
       u_{p̄x} ┄┄┄┄┄┄ u_{py}                (link)


   Map f:

       b_x      u_{p̄x}      b_y      u_{py}
        │         │           │         │
        ↓         ↓           ↓         ↓
       •x        •p̄x         •y       •py


   G(∃x.(p̄x ∨ ∀y. py)):

           ┌────── •p̄x
       •x ─┼────── •y
           └────── •py

       (•x — •p̄x edge; •x — •y edge; •x — •py edge; nothing else)
```

- **Fonet `N`**: 4 vertices `{b_x, b_y, u_p̄x, u_py}`. 1 link `{u_p̄x, u_py}`. Edges: `{b_x, u_p̄x}`, `{b_x, u_py}` (because `b_x` is existential, joined to the body's literals via `×`); plus `{b_x, b_y}` (the binder-to-binder edge in the binding graph for `b_y` ∈ scope of `b_x`). Dualizer: `δ(y) = x`. Dependency `{b_x, b_y}` is a leap edge.

- **Fograph `G(∃x.(p̄x ∨ ∀y. py))`**: 4 vertices `{•x, •p̄x, •y, •py}`. Edges from `•x` to each of the other three (because `×`); no edges among the other three.

- **Fibration `f`**: `{ b_x ↦ •x, b_y ↦ •y, u_p̄x ↦ •p̄x, u_py ↦ •py }`.

### Verification

**Fonet:**
- Linked: ✓.
- Dualizer `δ(y) = x` makes the link's atoms dual: `p̄x{y↦x} = p̄x`, `py{y↦x} = px`, dual ✓.
- Dependency `{b_x, b_y}`: every dualizer must contain `x` in `δ(y)` to dualize the link, so `(b_x, b_y)` is a dependency ⇒ a leap.
- Leap graph: link `{u_p̄x, u_py}` plus leap edge `{b_x, b_y}`.
- No induced bimatching: any 2-vertex set inducing a matching in both must have a link AND a leap edge between the same pair, which doesn't exist ✓.

**Skew bifibration:**
- Label-preserving ✓.
- Binding fibration: `b_x → u_p̄x`, `b_x → u_py` in `N`'s binding graph; `•x → •p̄x`, `•x → •py` in `G(C)`'s. ✓ (uniqueness preserved). Similarly `b_y → u_py`, `•y → •py` ✓.
- Skew fibration on cograph: every edge in `G(C)` is between `•x` and a body vertex. In `N`, `b_x` is connected to its body literals; `b_y` is not connected to `u_p̄x` directly but the skew condition only requires *existence* of a non-creating lift, which holds.

✓ Combinatorial proof.

---

## Summary table — what gets built at each step

For Example B `(p ∧ q) ⇒ (q ∧ p)`:

| Step | Op | Fonet `N` | Edges | Links | Fograph `G(C)` | Edges | Fibration `f` |
|---|---|---|---|---|---|---|---|
| 1 | `AxiomLit` (LEFT leaf) | `{u_q̄, u_q}` | ∅ | `{u_q̄, u_q}` | `•q̄ + •q` | ∅ | `u_q̄↦•q̄, u_q↦•q` |
| 2 | `AxiomLit` (RIGHT leaf) | `{u_p̄, u_p}` | ∅ | `{u_p̄, u_p}` | `•p̄ + •p` | ∅ | `u_p̄↦•p̄, u_p↦•p` |
| 3 | `And(2, [1])` | `{u_q̄, u_q, u_p̄, u_p}` | `{u_q,u_p}` | `{u_q̄,u_q}, {u_p̄,u_p}` | `•p̄ + •q̄ + (•q × •p)` | `{•q,•p}` | identity |
| 4 | `Or` | (unchanged) | (unchanged) | (unchanged) | (unchanged) | (unchanged) | (unchanged) |
| 5 | `Or` | (unchanged) | (unchanged) | (unchanged) | (unchanged) | (unchanged) | (unchanged) |

---

## Implementation contract per step

The translator's stack frames hold the triple `(N, G(C), f)`. Each frame represents one open subgoal's combinatorial proof.

**Stack invariants at each op-step:**

- **Closing op** (`AxiomLit`, `One`, `CloseByLemma`): pushes a new triple.
- **Linear op** (`Exchange`, `Weakening`, `Or`, `Forall`, `Exists`, `Contraction`): replaces the top frame's triple with the per-rule transformed one.
- **Branching op** (`And`, `Cut`): pops two frames, fuses, pushes one. (For `Cut`, also augment the running goal formula with `θ ∧ ¬θ`.)

**At end:** stack has exactly one frame, the combinatorial proof of the (possibly augmented) goal.

---

## What's left to clarify before coding

1. **Modular decomposition / cotree** for the source fonet. Every binder needs scope (smallest proper strong module containing it). For the target, scope is computable from the formula AST. For the source, we need to either (a) recompute the cotree at every step, or (b) maintain it incrementally as ops modify `N`.

2. **`And` weak/strong asymmetry**. Verify on a concrete example like `1 ∧ p` (where `f_1` is weak — proves `[1]` via `One` axiom — and `f_2` is strong — proves `[p̄, p]` via `AxiomLit`).

3. **Exists witness handling.** When the witness is a fixed-variable from an outer `Forall`, the new vertex `v` plus its edges to `P` create the dependency that produces a leap in the fonet. Need to verify this matches Hughes' dualizer/dependency definition.

4. **Cut + CloseByLemma interaction.** Decide on Strategy B (cut-via-§15) and add a verifier check that `CloseByLemma(L)` ops are paired with a preceding `Cut(φ_L)`.

---

*Status: design walkthrough. No code in `src/proof/comb/` yet.*
