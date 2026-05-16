#pragma once

// Leap graph + bimatching-freeness — Hughes 2019, §5 / §10.21-10.22 / §14.
//
// This is Phase 2C of CombVerifier::verify_fonet: confirming the fonet N
// has *no induced bimatching* (paper Def. 5.3). Direct search over vertex
// subsets is exponential; the paper instead verifies the property by
// *decomposing* N down to axioms (Lemma 10.22), which is polynomial
// (Lemma 14.2 / Theorem 14.3).
//
// Two ingredients:
//
//   (1) build_leap_graph — assemble L_N, the leap graph (paper §5).
//   (2) verify_no_bimatching — the recursive fusion/quantification
//       decomposition driven by Lemma 10.21.
//
// Both are declared here; the implementations live in leap.cpp.

#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/cotree.h"

#include "src/core/formula.h"
#include "src/util/error.h"

namespace logic::proof::comb {

// build_leap_graph — construct the leap graph L_N of the fonet (paper §5).
//
//   A *leap* is a *link* or a *dependency*:
//     - links    : the pre-dual literal pairs, already in source.links.
//     - dependency {•x, •y} : •x existential, •y universal, such that
//                  *every* dualizer maps x to a term containing y.
//
//   L_N = (V_N, links ∪ dependencies).
//
//   Dependencies via the MGU (Lemma 14.1). The links impose a unification
//   problem: for each link {α₁, α₂} the argument tuples must become equal
//   under the dualizer. Let σ be the most general unifier over the
//   *existential* variables. Then
//
//       {x, y} is a dependency   ⟺   y ∈ vars(σ(x))
//
//   — because σ is itself a dualizer, and every dualizer is an instance
//   σ∘ρ with ρ touching only existentials, so a universal y in σ(x)
//   survives into every dualizer's image of x. Note this means the
//   *stored* dualizer (source.dualizer) cannot be used — it may be more
//   specific than the MGU; the MGU must be recomputed from the links.
//
//   In the general first-order case σ can blow up exponentially and
//   Lemma 14.1 keeps it in triangular form. Our Term language has no
//   function symbols (only variables and opaque descriptions), so the
//   MGU collapses to a union-find over existential variables: each class
//   carries at most one rigid value (a universal var or a description),
//   and σ(x) is that rigid (or x itself if unconstrained).
//
//   Precondition: 2B has already confirmed a dualizer exists, so
//   unification should not fail; an error here indicates an inconsistent
//   link set.
util::Result<Edges> build_leap_graph(const CombProof& proof);

// verify_no_bimatching — confirm N has no induced bimatching, by the
// decomposition of Lemma 10.21 / 10.22 (paper §14).
//
//   A set W induces a *bimatching* when it induces a matching in *both*
//   the cograph (V_N, E_N) and the leap graph L_N. Rather than search
//   for W, we attempt to decompose N into axioms:
//
//     is_fonet(N):
//       - N has no edges        → N must be a union of literal-axioms.
//       - N has a binder in no  → that binder is universal; delete it
//         edge                    and recurse (Lemma 10.16).
//       - else (non-universal,  → decompose via the Ω construction:
//         ≥1 edge)
//
//   Ω construction (Lemma 10.21). Read the cograph off the cotree as
//       G = (G₁×G₂) + (G₃×G₄) + … + (G_{n-1}×Gₙ) + L
//   (L a union of lone literals). Ω has the parts Gᵢ as vertices, with
//   GᵢGⱼ ∈ E(Ω) iff N has an edge *or a leap* between V(Gᵢ) and V(Gⱼ).
//   Z = {G₁G₂, G₃G₄, …} is a 1-factor of Ω; N is a fonet ⟹ Z is the
//   *unique* 1-factor ⟺ some Z-edge G_m G_{m+1} is a *bridge* of Ω. A
//   second 1-factor would yield leaps inducing a bimatching — so "find a
//   bridge in Z" *is* the no-bimatching test at this level.
//
//   Splitting at the bridge gives G = K₁ + (G_m × G_{m+1}) + K₂, and:
//     - G_m and G_{m+1} both contain a literal → N is a *fusion*;
//       recurse on K₁+G_m and G_{m+1}+K₂.
//     - otherwise one part is a lone binder •x → N is an *existential
//       quantification*; delete •x and recurse.
//
//   The cotree is taken by reference because 2A.3 already built it.
util::ResultStatus verify_no_bimatching(const CombProof& proof,
                                        const Cotree&    cotree,
                                        const Edges&     leap_edges);

}  // namespace logic::proof::comb
