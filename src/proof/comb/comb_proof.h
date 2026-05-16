#pragma once

// Combinatorial proof — Hughes 2019, "First-order proofs without syntax".
//
// A combinatorial proof of a formula φ is a triple (N, G, f):
//   - G is the fograph G(φ) of the formula (paper §3, Def. 3.1).
//   - N is a fonet (paper §5, Def. 5.3) — a linked fograph equipped with
//     a dualizer and free of induced bimatchings.
//   - f : V_N → V_G is a skew bifibration (paper §4, Def. 4.1) — a vertex
//     map that is a skew fibration on the underlying cographs and an
//     ordinary directed fibration on the binding graphs.
//
// This header is data-only: types and ctors. Verification (fonet validity,
// skew bifibration conditions) and construction (formula → fograph) live
// in companion translation units.

#include "src/core/formula.h"

#include <cstddef>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace logic::proof::comb {

using Edge = std::pair<size_t, size_t>;
using Edges = std::vector<Edge>;

// Vertex kinds in a fograph (paper §3): atom-labelled, variable-labelled
// (binder), or the truth literal 1. Each occurrence of an atom or
// quantifier in φ becomes one vertex of G(φ).
enum class VertexKind {
    Atom,    // a predicate occurrence: pred(t1,...,tn) or its dual
    Binder,  // a quantifier occurrence: ∀x or ∃x
    One,     // the truth literal (encoded as ¬⊥)
};

// VertexLabel — full label data for a single vertex.
//
// The fields are kind-tagged: only the subset relevant to `kind` is
// meaningful. Using a flat record (rather than std::variant) keeps the
// verifier loops cache-friendly and the indexing arithmetic simple.
struct VertexLabel {
    VertexKind kind{};

    // Atom: which predicate, polarity, and term arguments. Pre-duality
    // between two atom-vertices means same `pred`, opposite `negated`,
    // and `args` related by the fonet's dualizer (Def. 5.2).
    PredicateHandle   pred{};
    bool              negated{false};
    std::vector<Term> args{};

    // Binder: which variable this binder introduces, and whether it is
    // existential (×-joined to its scope) or universal (+-disjoint from
    // its scope). The classification is derivable from the cograph but
    // is cached here because every dualizer/leap/scope check needs it.
    var_index var{};
    bool      is_existential{false};
};

// Fograph — the graph of a formula φ (paper §3).
//
// Two graphs over a common vertex set:
//   - cograph_edges: undirected, encode the modular (∧/∨) structure.
//                    Edge {u,v} iff u and v are joined by a × in the
//                    cotree of φ. Used by the skew-fibration condition.
//   - binding_edges: directed (binder → literal). Edge (b, ℓ) iff binder
//                    b binds the variable inside literal ℓ. Used by the
//                    ordinary (unique-lift) fibration condition.
//
// Both are needed: a skew bifibration imposes different constraints on
// each. Merging them would lose the skew/ordinary asymmetry.
struct Fograph {
    std::vector<VertexLabel>               labels{};
    Edges                                  cograph_edges{};
    Edges                                  binding_edges{};

    // The formula whose graph this is. Two formulas can share a fograph
    // (Lemma 10.1: equal modulo ∧/∨ commutativity/associativity and
    // adjacent same-quantifier swaps), so the original handle is
    // retained for user-facing verification and serialization.
    FormulaHandle source_formula{};

    size_t num_vertex() const { return labels.size(); }

    Fograph() = default;
    // Build G(formula) per paper Def. 3.1. PRECONDITION: `formula` is
    // description-free; descriptions are eliminated by the translator
    // before reaching the comb layer (see translate/ELIMINATE_DESCRIPTIONS.md).
    explicit Fograph(FormulaHandle const& formula);
};

// Fonet — a linked fograph with dualizer (paper §5, Def. 5.3).
//
// Stored label-free. The paper itself drops source labels (§4 after
// Def. 4.1: "We identify a skew bifibration with its skeleton. No
// information is lost since the source labels can be lifted from the
// target."). When labels are needed, look them up via the fibration:
//
//     source_label(v) = target.labels[fibration[v]]
//
// This avoids redundant data and the soundness landmine of the
// stored source labels going out of sync with target.labels[fibration[v]].
//
// Fonet-specific structural data:
//   - cograph_edges: undirected, the source's modular structure.
//                    Subject to the skew-fibration condition w.r.t. target.
//   - binding_edges: directed (binder → literal), the source's binding
//                    structure. Subject to the ordinary (unique-lift)
//                    fibration condition w.r.t. target.
//   - links: 2-element colour classes pairing pre-dual literal vertices.
//            Every literal must be in exactly one link (or be the truth
//            literal 1, which is unlinked).
//   - dualizer: a substitution δ from each existential-binder variable
//               (the prover's witnesses) to a term, such that for every
//               link {u, v} the atoms (looked up via the fibration)
//               become identical after applying δ — their predicates
//               being already pre-dual. The dualizer's image terms may
//               contain universal-binder variables.
//
// Validity (Def. 5.3) requires the dualizer to exist and the linked
// fograph's leap graph to admit no induced bimatching. Those checks
// live in the verifier.
struct Fonet {
    size_t                                 num_vertex{0};
    Edges                                  cograph_edges{};
    Edges                                  binding_edges{};
    Edges                                  links{};
    std::unordered_map<var_index, Term>    dualizer{};
};

// CombProof — a combinatorial proof of `proved_formula`.
//
// `target` is the fograph G(proved_formula). `source` is a fonet whose
// vertices are mapped into `target` by `fibration`: for each i in
// [0, source.num_vertex), fibration[i] is an index into target.labels.
// Total on V_source by construction; image may be a strict subset of
// V_target (uncovered vertices arise from weakening — paper §11.1, W).
//
// Source vertex labels are not stored; derive them via source_label().
//
// A combinatorial proof is a self-contained witness: every soundness
// condition is checkable in polynomial time from the data below. The
// `last_used` set records lemma references that the upstream LKR proof
// (the one this combinatorial proof was translated from) consulted; the
// runner reads this to populate the proof-dependency graph after a
// successful verify.
class CombProof {
public:
    std::string         claim_name{};   // matches NDProgram/LKRProgram for runner dispatch
    Fonet               source{};       // the fonet N
    Fograph             target{};       // the fograph G(target.source_formula)
    std::vector<size_t> fibration{};    // f : V_source → V_target, length == source.num_vertex

    // Lemma names referenced by the upstream proof this artefact was built
    // from. Propagated through the LKR→Comb translator from the LKR
    // verifier's last_used_names. Read by ProofRunner via the verifier's
    // last_used_names() override.
    std::unordered_set<std::string> last_used{};

    // Derived source vertex label (paper §4): labels are inherited from
    // the target via the fibration. Always the single source of truth.
    const VertexLabel& source_label(size_t v) const {
        return target.labels[fibration[v]];
    }
};

}  // namespace logic::proof::comb
