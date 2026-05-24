#include "src/proof/translate/nd_internalize/apply.h"

#include "src/proof/nd/verifier.h"
#include "src/proof/translate/nd_internalize/body.h"
#include "src/proof/translate/nd_internalize/prelude.h"
#include "src/proof/translate/nd_internalize/schema_macro.h"

namespace logic::proof::translate::nd_internalize {

util::Result<ApplyResult>
apply(GlobalContext&            ctx,
      const Program<nd::Instr>& input,
      FormulaHandle             goal,
      const TheoremFactsMap&    theorem_facts)
{
    // Phases 2/3 — schema macro.
    auto sm = schema_macro(ctx, input);
    if (!sm.ok()) {
        return MAKE_ERROR
            << "nd_internalize::apply: schema_macro failed: "
            << sm.error().to_string();
    }

    // Phase 1 — facts closure on the schema-macroed body.
    auto fc = compute_transitive_facts(sm.value().proof, ctx, theorem_facts);
    if (!fc.ok()) {
        return MAKE_ERROR
            << "nd_internalize::apply: compute_transitive_facts failed: "
            << fc.error().to_string();
    }
    std::vector<SentenceHandle> facts = std::move(fc).unwrap();

    // Phase 4 — prelude builder.
    auto pre = emit_prelude(ctx, facts);
    if (!pre.ok()) {
        return MAKE_ERROR
            << "nd_internalize::apply: emit_prelude failed: "
            << pre.error().to_string();
    }
    const uint32_t prelude_len =
        static_cast<uint32_t>(pre.value().instrs.size());

    // Phase 5 — body emit with remap.
    auto bd = emit_body_with_remap(
        sm.value().proof, pre.value().fact_step_table, prelude_len);
    if (!bd.ok()) {
        return MAKE_ERROR
            << "nd_internalize::apply: emit_body_with_remap failed: "
            << bd.error().to_string();
    }

    // Stitch the final program: prelude + body + postlude.
    ApplyResult result;
    result.proof.claim_name = input.claim_name;
    result.proof.instrs.reserve(
        pre.value().instrs.size() + bd.value().instrs.size() + 2);
    for (auto& op : pre.value().instrs) result.proof.instrs.push_back(op);
    for (auto& op : bd.value().instrs)  result.proof.instrs.push_back(op);

    FormulaBuilder builder(ctx);
    if (facts.empty()) {
        // Identity case: wrapped_goal = original φ. The body's
        // qed_target already derives φ; just close with a Qed.
        result.wrapped_goal = ctx.add_sentence(Sentence(goal));
        nd::Qed q{}; q.derived = bd.value().qed_target;
        result.proof.instrs.emplace_back(nd::Instr{std::move(q)});
    } else {
        // Wrap: emit ImpliesIntro on the body's qed_target, then Qed.
        nd::ImpliesIntro ii{};
        ii.conclusion = bd.value().qed_target;
        const uint32_t ii_idx =
            static_cast<uint32_t>(result.proof.instrs.size());
        result.proof.instrs.emplace_back(nd::Instr{std::move(ii)});

        nd::Qed q{}; q.derived = StepRef{ii_idx};
        result.proof.instrs.emplace_back(nd::Instr{std::move(q)});

        FormulaHandle Hphi =
            builder.make_implies(pre.value().H.get().root(), goal);
        result.wrapped_goal = ctx.add_sentence(Sentence(Hphi));
    }

    // Output gate. Translator bugs surface here as a boundary Error;
    // a silently-unsound Stage 1 output is therefore impossible.
    {
        nd::NDVerifier v;
        Proof p{};
        p.system = System::ND;
        p.body   = result.proof;
        auto vr = v.verify(ctx, result.wrapped_goal.get().root(), p);
        if (!vr.ok()) {
            return MAKE_ERROR
                << "nd_internalize::apply: output gate (NDVerifier) "
                   "rejected wrapped proof: "
                << vr.error().to_string();
        }
    }

    result.facts = std::move(facts);
    return result;
}

}  // namespace logic::proof::translate::nd_internalize
