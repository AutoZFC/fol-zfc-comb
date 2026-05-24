#include "src/proof/translate/nd_internalize/prelude.h"

namespace logic::proof::translate::nd_internalize {

namespace {

// Left-fold facts[0].formula ∧ facts[1].formula ∧ … ∧ facts[n-1].formula.
// Caller must check facts non-empty.
FormulaHandle build_left_assoc_conjunction(
    FormulaBuilder& builder,
    const std::vector<SentenceHandle>& facts)
{
    FormulaHandle h = facts[0].get().root();
    for (size_t i = 1; i < facts.size(); ++i) {
        h = builder.make_and(h, facts[i].get().root());
    }
    return h;
}

}  // namespace

util::Result<PreludeResult>
emit_prelude(GlobalContext& ctx,
             const std::vector<SentenceHandle>& sorted_facts)
{
    PreludeResult result;
    const size_t n = sorted_facts.size();

    if (n == 0) {
        // Identity case: caller short-circuits the entire wrap (no H,
        // wrapped_goal = original φ).
        return result;
    }

    FormulaBuilder builder(ctx);
    FormulaHandle H_formula = build_left_assoc_conjunction(builder, sorted_facts);
    result.H = ctx.add_sentence(Sentence(H_formula));

    // [0] Assume(H) — translator-synthesized; supply formula via
    // `resolved` so no AST parsing happens.
    nd::Assume assume_op{};
    assume_op.resolved = H_formula;
    result.instrs.emplace_back(nd::Instr{std::move(assume_op)});
    const StepRef h_step = StepRef{0};

    if (n == 1) {
        // H = φ_{F₁}; h_{F₁} = the Assume's step itself, no extraction.
        result.fact_step_table[sorted_facts[0]] = h_step;
        return result;
    }

    // h_steps[k] = StepRef of h_k (the prefix conjunction of first k facts).
    //   h_n = StepRef{0}  (the Assume).
    //   h_{k-1} = AndElimL(h_k) for k = n down to 2.
    // So h_steps[0] = h_n, h_steps[1] = h_{n-1}, …, h_steps[n-1] = h_1.
    std::vector<StepRef> h_steps;
    h_steps.reserve(n);
    h_steps.push_back(h_step);

    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimL op{};
        op.of = h_steps[i];
        uint32_t idx = static_cast<uint32_t>(result.instrs.size());
        result.instrs.emplace_back(nd::Instr{std::move(op)});
        h_steps.push_back(StepRef{idx});
    }
    // After this loop: result.instrs has 1 + (n-1) = n ops.
    // h_steps[n-1] is h_1 = the single fact φ_{F₁}.

    // Now AndElimR's: for each h_k (k = n down to 2), AndElimR(h_k) =
    // φ_{F_k}. Walk h_steps in order: h_steps[0] = h_n → φ_{F_n}, …,
    // h_steps[n-2] = h_2 → φ_{F_2}. (h_steps[n-1] = h_1 is φ_{F_1}
    // already; no extraction needed.)
    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimR op{};
        op.of = h_steps[i];
        uint32_t idx = static_cast<uint32_t>(result.instrs.size());
        result.instrs.emplace_back(nd::Instr{std::move(op)});
        // h_steps[i] = h_{n-i}; its AndElimR gives φ_{F_{n-i}}.
        result.fact_step_table[sorted_facts[n - 1 - i]] = StepRef{idx};
    }

    // F₁'s extract is h_1 itself (the final AndElimL).
    result.fact_step_table[sorted_facts[0]] = h_steps[n - 1];

    return result;
}

}  // namespace logic::proof::translate::nd_internalize
