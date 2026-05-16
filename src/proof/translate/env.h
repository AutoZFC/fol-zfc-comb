#pragma once

// Env — abstract sequent state for the ND→LKR translator.
//
// See SPEC.md for the translation specification.
//
// Design principle: address sequent entries by *identity* (SequentEntry),
// not by position. The Env owns the entries→positions map and is the only
// place position arithmetic happens. Per-rule emitters declare what they
// need (left_needs / right_needs); the Env decides the partition. After
// any mutation, a SequentEntry that is still in scope continues to resolve
// to the entry's new position; a SequentEntry that has been popped or
// routed to the other side of an And split returns Error from
// `position_of` rather than silently aliasing some other entry.
//
// Why identity-keyed rather than position-keyed: position arithmetic is
// fragile under any operation that re-indexes the sequent. Multiplicative
// And renumbers entries; Or replaces the principal in place but appends ψ;
// Cut duplicates the goal across two branches. A position-keyed shadow
// state must be re-mapped at every mutation — an obligation that is
// silent when violated, producing downstream errors many ops away. The
// Env makes "entry has been popped or split off" a first-class observable
// (`position_of` returns Error) so that bug class is impossible by
// construction, not by careful coding.

#include "src/core/formula.h"
#include "src/util/error.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

namespace logic::proof::translate {

// SequentEntry — opaque handle to a sequent entry. Stable across Env
// mutations that re-bind an entry's contents (Or, Forall, Exists) and
// preserved by the additive Cut. After multiplicative-And, only entries
// routed to the same side as the SequentEntry remain valid in the child
// Env on that side.
struct SequentEntry {
    uint64_t id{0};

    bool operator==(const SequentEntry& o) const noexcept { return id == o.id; }
    bool operator!=(const SequentEntry& o) const noexcept { return id != o.id; }
    bool operator<(const SequentEntry& o)  const noexcept { return id <  o.id; }
};

}  // namespace logic::proof::translate

namespace std {
template <> struct hash<logic::proof::translate::SequentEntry> {
    size_t operator()(logic::proof::translate::SequentEntry e) const noexcept {
        return std::hash<uint64_t>{}(e.id);
    }
};
}  // namespace std

namespace logic::proof::translate {

// EigenSupply — fresh-eigenvariable factory. Wraps FormulaBuilder's scope
// counter so the lowerer can ask for fresh eigens without reaching into
// the builder directly.
class EigenSupply {
public:
    explicit EigenSupply(FormulaBuilder& b) : b_(b) {}
    var_index fresh()       { return b_.enter_scope(); }
    Term      fresh_term()  { return Term::fixed(fresh()); }
private:
    FormulaBuilder& b_;
};

class Env;
struct EnvCutResult;
struct EnvAndResult;

// Env — the abstract sequent.
//
// Construction: default ctor creates an empty Env with a fresh id-counter;
// copies (used internally by apply_cut and apply_and) share the counter
// so SequentEntry IDs minted in any child remain globally unique within
// the same translation.
class Env {
public:
    Env();
    Env(const Env&)            = default;
    Env(Env&&) noexcept        = default;
    Env& operator=(const Env&) = default;
    Env& operator=(Env&&) noexcept = default;

    // === Construction ===

    // Seed the Env with NNF(claim). Returns the SequentEntry of the
    // initial entry. Must only be called on an empty Env.
    SequentEntry seed(FormulaHandle f);

    // Append a new entry (mirrors verifier-side Cut and Weakening's
    // "push to the end" semantics). Returns the new SequentEntry.
    SequentEntry push(FormulaHandle f);

    // === Lookup ===

    size_t size() const noexcept { return entries_.size(); }
    bool   empty() const noexcept { return entries_.empty(); }

    // Position of `e` in the current sequent. Error if `e` is not in
    // this Env (popped, routed elsewhere by And, or never minted).
    util::Result<size_t> position_of(SequentEntry e) const;

    // Formula at `e`. Error if `e` is not in this Env.
    util::Result<FormulaHandle> formula_at(SequentEntry e) const;

    // SequentEntry currently at position `pos`. Error if pos is out of
    // range. Used by emit_close to address the new φ/ψ entries that
    // the apply_or mutator returns (which already exposes them via the
    // returned SequentEntry — this method is for diagnostics).
    util::Result<SequentEntry> entry_at(size_t pos) const;

    // === Verifier-mirroring mutators (no branching) ===

    // Or: principal must currently hold (φ ∨ ψ). Mutates principal in
    // place to φ; appends ψ at the end. principal's SequentEntry stays
    // valid and now points to φ. Returns the new SequentEntry for ψ.
    util::Result<SequentEntry> apply_or(SequentEntry principal);

    // Forall: principal must hold ∀x.φ. Mutates principal to
    // φ[x:=Term::fixed(eigen)].
    util::ResultStatus apply_forall(SequentEntry principal,
                                     var_index   eigen,
                                     FormulaBuilder& builder);

    // Exists: principal must hold ∃x.φ. Mutates principal to
    // φ[x:=witness].
    util::ResultStatus apply_exists(SequentEntry principal,
                                     Term        witness,
                                     FormulaBuilder& builder);

    // === Branching mutators (return new Env(s)) ===

    // Cut: both children inherit all parent entries with the same
    // SequentEntry IDs and same positions; LEFT gets +φ; RIGHT gets +¬φ
    // (NNF-normalized). The phi argument is required to already be in
    // NNF — Env does not normalize.
    EnvCutResult apply_cut(FormulaHandle phi_nnf, FormulaBuilder& builder) const;

    // And: principal must hold (φ ∧ ψ). Splits into LEFT (entries in
    // left_partition + φ) and RIGHT (entries NOT in left_partition + ψ).
    //
    // The partition is computed from the caller's declared dependencies:
    //   * `left_needs` and `right_needs` must be disjoint.
    //   * Each declared entry must currently be in this Env, and ≠ principal.
    //   * Entries in neither set default to LEFT.
    //
    // (If a rule needs an entry on both sides, it must Weaken first to
    // create a fresh handle — Weakening produces a new SequentEntry that
    // is independent of the original.)
    util::Result<EnvAndResult> apply_and(
        SequentEntry                          principal,
        const std::set<SequentEntry>&         left_needs,
        const std::set<SequentEntry>&         right_needs) const;

private:
    std::vector<FormulaHandle>               entries_;     // index = position
    std::vector<SequentEntry>                pos_to_id_;   // index = position
    std::unordered_map<SequentEntry, size_t> id_to_pos_;

    // Mints a globally unique SequentEntry ID via a process-static
    // counter, so IDs never collide across Env instances or branches.
    static SequentEntry mint_id();
    void rebuild_index();
};

// Defined after Env so the Env-typed members are complete.
struct EnvCutResult {
    Env          left;            // Γ ∪ {φ}
    Env          right;           // Γ ∪ {¬φ}
    SequentEntry left_phi;        // φ (in left)
    SequentEntry right_neg_phi;   // ¬φ (in right, NNF-normalized)
};

struct EnvAndResult {
    Env                  left;             // entries in left_partition + φ
    Env                  right;            // entries NOT in left_partition + ψ
    SequentEntry         left_phi;
    SequentEntry         right_psi;
    std::vector<size_t>  left_partition;   // for lkr::And.left_partition (sorted)
};

}  // namespace logic::proof::translate
