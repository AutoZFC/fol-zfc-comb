#pragma once

// Multi-system proof framework — shared IR foundation.
//
// This header declares the system-agnostic skeleton on which per-system
// instruction sets are built. It introduces:
//
//   * Strongly-typed identifier newtypes (StepRef, TermRef, AxiomRef,
//     SchemaRef, ScopeName) — the IR's vocabulary for cross-references.
//   * OpHeader — the per-instruction metadata every op carries.
//   * SchemaInstData — the cross-system payload for schema instantiation.
//   * Program<Instr> — a typed program: linear instructions, claim name,
//     precomputed step-name index.
//   * Proof — the umbrella variant: a Program parameterised by which
//     proof-system it targets.
//
// Per-system Op enums and Instr variants live in:
//   src/proof/nd/ops.h    (Phase 3)
//   src/proof/lkr/ops.h   (Phase 5)
//
// Mathematical principle: a proof is a term in a sum type. Each constructor
// (each rule) has its own arity and signature. The IR records that structure
// faithfully — proof-internal identifiers are integers (StepRef/TermRef are
// instr-index newtypes); identifiers that cross the runtime boundary into
// GlobalContext stay as strings (axiom/schema names) because they reference
// the theory's named registries. The one remaining string class — ScopeName
// inside a deferred formula AST — is a parser artifact, not an IR-level
// identifier (see Option A in design discussion).

#include "../parser/parser.h"     // SchemaBinding (parser-side struct, reused as-is)
#include "../util/error.h"        // util::SourceLocation

#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace logic::proof {

// ---------------------------------------------------------------------------
// Identifier newtypes
// ---------------------------------------------------------------------------
// Distinct C++ types over the same underlying representation prevent
// accidental confusion between "step index" and "term index" (both uint32_t,
// but referring to different verifier-side environments) and between axiom
// names and schema names (both std::string, but distinct registries on
// GlobalContext).
//
// All five are aggregates so they can be brace-initialised; equality and
// hashing are explicit so the types can be used in unordered_maps when
// needed by future passes.

// Reference to a previously-bound step. The value is the index of the
// instruction whose execution bound the step. Verifier resolves k to
// step_env[k].
struct StepRef {
    uint32_t idx;
    bool operator==(const StepRef&) const = default;
};

// Reference to a previously-bound term. The value is the index of the
// instruction that introduced the term (Fix, ExistsElim w/ binding,
// IotaElim w/ binding, ForallR, ExistsL).
struct TermRef {
    uint32_t idx;
    bool operator==(const TermRef&) const = default;
};

// Reference to an axiom or proven theorem in GlobalContext.
// Resolution: ctx.find_axiom(name) ?? ctx.find_theorem(name).
struct AxiomRef {
    std::string name;
    bool operator==(const AxiomRef&) const = default;
};

// Reference to a schema in GlobalContext. Resolution: ctx.find_schema(name).
struct SchemaRef {
    std::string name;
    bool operator==(const SchemaRef&) const = default;
};

// A scope-bound variable name as it appears inside a deferred formula AST
// payload (Assume / Let / Cut formulas). This is the *one* place where IR
// internals carry strings: the verifier resolves these names against a
// runtime name->TermRef table built up by Fix/ExistsElim/IotaElim. See
// the Option A discussion in the design conversation for why this carve-out
// is deliberate.
struct ScopeName {
    std::string name;
    bool operator==(const ScopeName&) const = default;
};

// ---------------------------------------------------------------------------
// Per-instruction metadata
// ---------------------------------------------------------------------------
// Every op struct embeds an OpHeader as its first member. This keeps the
// per-op types as aggregates (no inheritance) while ensuring loc is uniformly
// available for diagnostics.
//
// Note: there is no `result` field. The result of instruction at index k is
// referenced as StepRef{k} (or TermRef{k} for term-binding ops). Position is
// canonical identity.

struct OpHeader {
    util::SourceLocation loc{};
};

// ---------------------------------------------------------------------------
// Schema instantiation payload — shared across systems
// ---------------------------------------------------------------------------
// Schema instantiation is a theory-level operation: both ND and LKR can
// invoke it, with identical payload semantics. Each system's SchemaInst
// op-struct holds a SchemaInstData by composition (not inheritance).
//
// Lowering converts the source-level schema variable name in each
// SchemaBinding to its positional index against the SchemaDefinition's
// var_names array. The lambda body remains a deferred AST.

struct SchemaInstData {
    SchemaRef schema;
    std::vector<SchemaBinding> bindings;
};

// ---------------------------------------------------------------------------
// Program — typed instruction stream
// ---------------------------------------------------------------------------
// A Program is a finite, linear sequence of instructions plus the claim it
// targets. step_index is a precomputed map from source-level step name
// (e.g. "h7") to the producing instruction's index, populated by the
// lowering pass. Verifiers and passes consult step_index when resolving
// named operands; instr-internal references already use StepRef/TermRef
// indices and do not need the map.
//
// Memory: contiguous vector<Instr> + small hashmap; nothing per-step heap-
// allocated beyond what the op variant itself owns.
//
// Compute: linear traversal; O(1) operand resolution via instruction index.

template <typename Instr>
struct Program {
    std::string claim_name;
    std::vector<Instr> instrs;
    std::unordered_map<std::string, uint32_t> step_index;
};

// ---------------------------------------------------------------------------
// System tag
// ---------------------------------------------------------------------------
// The Proof umbrella variant (which holds NDProgram or LKRProgram) lives in
// src/proof/proof.h, since it requires complete per-system Instr types and
// would force this foundation header to pull in every system's ops header.
// The system tag enum, by contrast, is system-agnostic and lives here so
// ProofRunner / dispatchers can index by it without including the ops.

enum class System : uint8_t {
    ND  = 0,
    LKR = 1,
};

// Number of supported systems. Used by ProofRunner to size its verifier
// array. Update when adding a new System tag.
inline constexpr size_t kNumSystems = 2;

}  // namespace logic::proof

// ---------------------------------------------------------------------------
// std::hash specialisations
// ---------------------------------------------------------------------------
// These let StepRef/TermRef/AxiomRef/SchemaRef/ScopeName participate in
// unordered_set / unordered_map without per-callsite functor boilerplate.

namespace std {

template <> struct hash<logic::proof::StepRef> {
    size_t operator()(const logic::proof::StepRef& r) const noexcept {
        return std::hash<uint32_t>{}(r.idx);
    }
};

template <> struct hash<logic::proof::TermRef> {
    size_t operator()(const logic::proof::TermRef& r) const noexcept {
        return std::hash<uint32_t>{}(r.idx);
    }
};

template <> struct hash<logic::proof::AxiomRef> {
    size_t operator()(const logic::proof::AxiomRef& r) const noexcept {
        return std::hash<std::string>{}(r.name);
    }
};

template <> struct hash<logic::proof::SchemaRef> {
    size_t operator()(const logic::proof::SchemaRef& r) const noexcept {
        return std::hash<std::string>{}(r.name);
    }
};

template <> struct hash<logic::proof::ScopeName> {
    size_t operator()(const logic::proof::ScopeName& r) const noexcept {
        return std::hash<std::string>{}(r.name);
    }
};

}  // namespace std
