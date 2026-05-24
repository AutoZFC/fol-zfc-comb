#include "nd_to_lkr.h"

#include "block_tree.h"
#include "demand.h"
#include "dispatcher.h"
#include "input_gate.h"
#include "output_gate.h"
#include "sequent_shadow.h"

#include "src/proof/nd/verifier.h"

#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

util::Result<StepRef> find_qed_derived(const Program<nd::Instr>& prog) {
    for (const auto& instr : prog.instrs) {
        if (auto* qed = std::get_if<nd::Qed>(&instr)) {
            return qed->derived;
        }
    }
    return MAKE_ERROR << "NDtoLKR: no Qed in program";
}

}  // namespace

util::Result<Program<lkr::Instr>> NDtoLKR::apply(
    const Program<nd::Instr>& in)
{
    // 1. Input gate.
    TRY(InputGate::verify(ctx_, goal_, in));

    // 2. Trace per-step formulas + term bindings.
    nd::NDVerifier tracer;
    TRY_ASSIGN(trace, tracer.trace_full(ctx_, in));

    // 3. Block-tree decomposition + closer→opener map.
    TRY_ASSIGN(root, decompose_blocks(in));
    auto closer_to_opener = dispatcher::build_closer_to_opener(*root);

    // 4. NNF the goal, with a builder whose var counter is above any
    //    var the trace used.
    FormulaBuilder builder(ctx_);
    while (builder.depth() < trace.next_free_var) builder.enter_scope();
    FormulaHandle goal_nnf = builder.to_nnf(goal_);

    // 5. Dispatcher entry: shadow with NNF(goal) at index 0; recurse
    //    from Qed.derived with an empty demand chain.
    SequentShadow shadow;
    shadow.entries.push_back(goal_nnf);
    TRY_ASSIGN(qed_derived, find_qed_derived(in));

    dispatcher::Ctx dcc{ctx_, builder, in, trace, closer_to_opener};
    std::vector<lkr::Instr> emitted;
    TRY(dispatcher::translate_step(
        dcc, std::move(shadow), qed_derived,
        /*target_pos=*/0, DemandPath{}, emitted));

    // 6. Assemble the LKRProgram.
    Program<lkr::Instr> out;
    out.claim_name = in.claim_name;
    out.instrs     = std::move(emitted);

    // 7. Output gate. Translator-emitted bug → boundary error.
    TRY(OutputGate::verify(ctx_, goal_, out));

    return out;
}

}  // namespace logic::proof::translate::nd_to_lkr
