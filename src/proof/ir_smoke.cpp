// Phase 1 smoke test: forces the IR header through the compiler so that
// header-only types and std::hash specialisations are validated. Removed
// or replaced once Phase 3 (ND verifier) gives the IR a real consumer.

#include "ir.h"

#include <type_traits>
#include <unordered_map>
#include <unordered_set>

namespace logic::proof {

// Newtypes are aggregates and equality-comparable.
static_assert(std::is_aggregate_v<StepRef>);
static_assert(std::is_aggregate_v<TermRef>);
static_assert(std::is_aggregate_v<AxiomRef>);
static_assert(std::is_aggregate_v<SchemaRef>);
static_assert(std::is_aggregate_v<ScopeName>);

static_assert(StepRef{1} == StepRef{1});
static_assert(StepRef{1} != StepRef{2});
static_assert(TermRef{0} == TermRef{0});

// std::hash specialisations are usable.
[[maybe_unused]] inline void smoke_hashing() {
    std::unordered_set<StepRef>      s_step;
    std::unordered_set<TermRef>      s_term;
    std::unordered_map<AxiomRef, int> m_axiom;
    std::unordered_map<SchemaRef, int> m_schema;
    std::unordered_map<ScopeName, int> m_scope;
    s_step.insert(StepRef{0});
    s_term.insert(TermRef{0});
    m_axiom[AxiomRef{"x"}] = 0;
    m_schema[SchemaRef{"y"}] = 0;
    m_scope[ScopeName{"z"}] = 0;
}

// Program<Instr> instantiates with arbitrary Instr types. This is checked
// once a real per-system Instr lands; for now exercise the template with a
// trivial dummy.
namespace {
struct DummyInstr {};
[[maybe_unused]] inline void smoke_program_template() {
    Program<DummyInstr> p;
    p.claim_name = "claim";
    p.instrs.emplace_back();
    p.step_index["h0"] = 0;
}
}  // namespace

}  // namespace logic::proof
