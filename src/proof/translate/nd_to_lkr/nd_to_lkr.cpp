#include "nd_to_lkr.h"

#include "dispatcher.h"
#include "formula_reader.h"
#include "input_gate.h"
#include "output_gate.h"
#include "proof_index.h"

#include "src/proof/lkr_build/expand.h"
#include "src/proof/lkr_build/op_sink.h"
#include "src/proof/nd/verifier.h"

namespace logic::proof::translate::nd_to_lkr {

namespace {

// Gates the input and translates it into `sink`.
util::ResultStatus translate(GlobalContext& ctx, FormulaHandle goal,
                             const Options& options,
                             const Program<nd::Instr>& in, OpSink& sink)
{
    TRY(InputGate::verify(ctx, goal, in));

    nd::NDVerifier tracer;
    TRY_ASSIGN(trace, tracer.trace_full(ctx, in));

    TRY_ASSIGN(index, ProofIndex::build(in, trace, options.share));

    // Eigenvariables start above every ND level, so they are fresh (§1.2).
    FormulaBuilder builder(ctx);
    while (builder.depth() < trace.next_free_var) builder.enter_scope();
    FormulaReader reader(index, trace, builder);

    Dispatcher dispatcher(index, reader, builder, sink);
    return dispatcher.translate_proof(builder.to_nnf(goal));
}

}  // namespace

util::Result<Program<lkr::Instr>> NDtoLKR::apply(
    const Program<nd::Instr>& in)
{
    Program<lkr::Instr> out;
    out.claim_name = in.claim_name;
    lkr_build::LkrSink sink(out.instrs);
    TRY(translate(ctx_, goal_, options_, in, sink));

    TRY(OutputGate::verify(ctx_, goal_, out));
    return out;
}

util::Result<Program<lkr_build::CompactInstr>> NDtoCompactLKR::apply(
    const Program<nd::Instr>& in)
{
    Program<lkr_build::CompactInstr> out;
    out.claim_name = in.claim_name;
    lkr_build::CompactSink sink(out.instrs);
    TRY(translate(ctx_, goal_, options_, in, sink));

    TRY_ASSIGN(expanded, lkr_build::ExpandIdentities(ctx_, goal_).apply(out));
    TRY(OutputGate::verify(ctx_, goal_, expanded));
    return out;
}

}  // namespace logic::proof::translate::nd_to_lkr
