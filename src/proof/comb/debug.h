#pragma once

// Debug formatters for combinatorial-proof structures.
//
// Pure diagnostics: every function returns a string, takes its input by
// const reference, and never mutates. Safe to call from any context. Not
// included in normal verification or translation; intended for use from
// tests, ad-hoc dumps, or env-var-guarded error messages.
//
// Format conventions:
//   - Terms:      "f<n>" for Fixed(n), "g<n>" for Generalized(n), "<desc>" otherwise.
//   - Predicates: "<name>/<arity>" with optional "~" prefix for negated.
//   - Vertices:   "v<index>" — index into Fograph::labels or Fonet vertex space.
//   - Binders:    "∃f<var>" / "∀f<var>".
//   - Links:      "{<a>,<b>}".
//
// Output is plain ASCII (the ∃/∀ glyphs are the only non-ASCII chars,
// matching how the verifier and walk diagnostics already print).

#include "src/proof/comb/comb_proof.h"

#include <string>

namespace logic::proof::comb::debug {

// ----- Atomic formatters -----

std::string format_term(const Term& t);
std::string format_args(const std::vector<Term>& args);
std::string format_predicate(const VertexLabel& lbl);    // "<name>/<arity>" or "~<name>/<arity>"
std::string format_vertex_label(const VertexLabel& lbl); // kind-dependent

// ----- Structure dumps -----
//
// Each returns a multi-line string ending in '\n', or "" if the input
// section is empty (e.g. dump_links on a fonet with zero links).

// Full target (Fograph): labels per vertex, cograph edges, binding edges.
std::string dump_target(const Fograph& target);

// Source vertices with their derived labels and fibration positions.
// Use this to spot duplicates: two source vertices that fibrate to the
// same target position will share var labels.
std::string dump_source_vertices(const Fonet& source,
                                 const Fograph& target,
                                 const std::vector<size_t>& fibration);

// Source structural data: cograph edges, binding edges.
std::string dump_source_structure(const Fonet& source);

// Every link: endpoints' vertex indices and their derived labels.
std::string dump_links(const Fonet& source,
                       const Fograph& target,
                       const std::vector<size_t>& fibration);

// Stored dualizer: key → value.
std::string dump_dualizer(const Fonet& source);

// Combined dump of everything in a CombProof. Use for env-var-guarded
// error messages or hand-investigation of a failing case.
std::string dump_proof(const CombProof& cp);

}  // namespace logic::proof::comb::debug
