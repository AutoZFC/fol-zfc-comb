#include "nd_to_lkr.h"

#include "block_tree.h"
#include "cut_spine.h"
#include "input_gate.h"
#include "output_gate.h"

#include "src/proof/nd/verifier.h"

namespace logic::proof::translate::nd_to_lkr {

// NOTE (Phase 5e.5, 2026-05-24): the production Pass still uses the
// cut_spine model. The new cut-minimal dispatcher (dispatcher.{h,cpp})
// is implemented and validated by test/cut_minimal_dispatcher_test
// against intro / projection-elim / combining-elim / closer / leaf
// paths, but it does not yet compose demands across forall_elim +
// projection_elim chains (e.g., (forall x. P∧Q) → P via forall_elim +
// and_elim_l). Composing demands requires a Demand-stack refactor
// that's deferred to a follow-up. Until then, the legacy
// cut_spine-based translator remains the production translator —
// it handles every input the test suite exercises.
util::Result<Program<lkr::Instr>> NDtoLKR::apply(
    const Program<nd::Instr>& in)
{
    // 1. Input gate.
    TRY(InputGate::verify(ctx_, goal_, in));

    // 2. Trace per-step formulas + term bindings (re-runs ND verifier as
    //    a side channel). next_free_var tells us how high the trace's
    //    private builder allocated, so we can start our builder above it
    //    and avoid clashes with trace's fix vars.
    nd::NDVerifier tracer;
    TRY_ASSIGN(trace, tracer.trace_full(ctx_, in));

    // 3. Block-tree decomposition.
    TRY_ASSIGN(root, decompose_blocks(in));

    // 4. NNF the goal, with a builder whose var counter starts above any
    //    var the trace used. New eigens we allocate are then guaranteed
    //    fresh w.r.t. trace formulas.
    FormulaBuilder builder(ctx_);
    while (builder.depth() < trace.next_free_var) builder.enter_scope();
    FormulaHandle goal_nnf = builder.to_nnf(goal_);

    // 5. Cut-spine driver emits LKR ops.
    CutSpineContext cc{ctx_, builder, in, trace};
    TRY_ASSIGN(ops, translate_outer(cc, *root, goal_nnf));

    // 6. Assemble the LKRProgram.
    Program<lkr::Instr> out;
    out.claim_name = in.claim_name;
    out.instrs     = std::move(ops);
    // step_index is unused by LKRVerifier (LKR refers to instrs by
    // position, not by source-level step names). Leave empty.

    // 7. Output gate. Translator-emitted bug → boundary error.
    TRY(OutputGate::verify(ctx_, goal_, out));

    return out;
}

}  // namespace logic::proof::translate::nd_to_lkr
