#pragma once

// Internal types shared between nd_to_lkr.cpp and close_flat.cpp.
//
// These are translator-implementation types — not public API. They live
// in `logic::proof::translate::detail` so neither file has to expose
// them outside the translator unit.
//
// Splitting rationale: close_flat is the dispatch table for ND op →
// LKR-emission realizers (one lambda per op variant). It pulls in lkr/nd
// op variants, env/emit_close, and schema_resolve. Keeping it in the
// main translator file makes that file harder to navigate; extracting
// it leaves nd_to_lkr.cpp focused on Phase A (decompose + formulas +
// deps planning) and the Phase B orchestrator (translate_block).

#include "env.h"

#include "src/core/formula.h"
#include "src/util/error.h"
#include "src/proof/ir.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <unordered_map>
#include <variant>
#include <vector>

namespace logic::proof::translate::detail {

// =========================================================================
// Block tree
// =========================================================================
// An ND derivation is a tree of nested scopes. Each scope opens with one
// of {Fix, Assume, ExistsElim} and closes with one of {ForallIntro,
// ImpliesIntro, NotIntro, ExistsIntro-no-witness, Qed}.

enum class BlockKind {
    OUTER,
    FORALL,
    IMPLIES,
    NOT,
    EXISTS_ELIM,
};

struct Block;
struct FlatStep { uint32_t nd_idx; };
using BodyItem = std::variant<FlatStep, std::unique_ptr<Block>>;

struct Block {
    BlockKind kind{BlockKind::OUTER};

    uint32_t opener_idx{0};
    uint32_t closer_idx{0};
    uint32_t close_target_idx{0};

    Term eigen_term{};
    FormulaHandle assumption_raw{};
    StepRef       exists_formula_step{};

    // OUTER = 0; each nested block = parent.depth + 1. Doubles as the
    // scope bit for the ScopeDeps bitset used by cut hoisting.
    int depth{0};

    std::vector<BodyItem> body;
};

// =========================================================================
// Step formula tables (Phase A → Phase B)
// =========================================================================
using StepFormulaMap = std::unordered_map<uint32_t, FormulaHandle>;

// =========================================================================
// ScopeDeps — bitset over block depths a derived formula depends on.
// =========================================================================
// Mirrors ND's ScopeDeps. A flat-step cut may be hoisted to its host
// block — the deepest ancestor of the step's defining block whose depth
// equals step_deps.deepest(). Steps with empty deps host at OUTER and
// are available everywhere; steps that depend on a fix-var or assumption
// stay no shallower than the introducing block.
struct ScopeDeps {
    uint64_t bits{0};

    // Maximum supported scope depth. Beyond this, from_bit reports
    // overflow via overflows() so the translator can fail loudly rather
    // than silently dropping bits.
    static constexpr int kMaxDepth = 63;

    static ScopeDeps from_bit(int i) {
        ScopeDeps d;
        if (i >= 0 && i <= kMaxDepth) d.bits = 1ULL << i;
        return d;
    }
    static bool overflows(int i) { return i < 0 || i > kMaxDepth; }

    bool empty() const { return bits == 0; }
    int  deepest() const {
        return bits == 0 ? -1 : (63 - __builtin_clzll(bits));
    }
    ScopeDeps  operator|(ScopeDeps o) const  { return ScopeDeps{bits | o.bits}; }
    ScopeDeps& operator|=(ScopeDeps o)       { bits |= o.bits; return *this; }
    void       clear(int i) {
        if (i >= 0 && i <= kMaxDepth) bits &= ~(1ULL << i);
    }
};
inline ScopeDeps discharge(ScopeDeps d, int i) { d.clear(i); return d; }

// =========================================================================
// Deps plan (Phase A → Phase B)
// =========================================================================
// DepsPlan tells Phase B, for each block, which flat-step Cuts and which
// sub-block recursions to emit on that block's RIGHT-of-cut continuation,
// in order. Hosting decisions are made by Phase A based on scope deps.

struct FlatEvent     { uint32_t flat_idx{}; };
struct SubBlockEvent { const Block* sub_block{}; };
using  EmissionEvent = std::variant<FlatEvent, SubBlockEvent>;

struct DepsPlan {
    std::unordered_map<uint32_t, ScopeDeps>                       step_deps;
    std::unordered_map<uint32_t, const Block*>                    host_block;
    std::unordered_map<const Block*, std::vector<EmissionEvent>>  events;
};

// =========================================================================
// Lowering context (Phase B internal)
// =========================================================================
// LowerCtx — context threaded through the lowering pass. Holds the
// shared GlobalContext / FormulaBuilder, the eigenvar supply, the
// step→formula maps (raw and NNF), the index-translation tables, the
// pre-computed deps plan, and the LKR output buffer that close_flat
// and emit_close append to. All members are references; LowerCtx never
// owns any of them.
struct LowerCtx {
    GlobalContext&                          ctx;
    FormulaBuilder&                         builder;
    EigenSupply&                            eigens;
    StepFormulaMap&                         step_formula;
    StepFormulaMap&                         step_formula_nnf;
    std::unordered_map<uint32_t, Term>&     term_for_idx;
    std::unordered_map<uint32_t, uint32_t>& nd_to_lkr_termref;
    const DepsPlan&                         plan;
    Program<lkr::Instr>&                    out;
};

// step_to_neg: for each ND step k that has been "cut in" on the current
// branch, its negation entry is at step_to_neg[k]. close_flat reads
// this; translate_flat_step writes it after each Cut.
using StepNegMap = std::unordered_map<uint32_t, SequentEntry>;

// =========================================================================
// LEFT-branch realizer for a flat step (close_flat.cpp)
// =========================================================================
// Closes the goal sequent `env` ∪ {F_k_nnf} under the LEFT-of-cut child
// produced by translate_flat_step. Each ND-rule branch declares its
// dependency entries via step_to_neg; emit_close handles the structural
// closure.
util::ResultStatus close_flat(LowerCtx&                 lc,
                              Env&                      env,
                              uint32_t                  k,
                              const Program<nd::Instr>& in,
                              SequentEntry              F_k_entry,
                              const StepNegMap&         step_to_neg);

}  // namespace logic::proof::translate::detail
