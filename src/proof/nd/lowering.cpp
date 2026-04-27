#include "lowering.h"

#include "ops.h"

#include "../../util/error.h"

#include <string>
#include <unordered_map>

namespace logic::proof::nd {

namespace {

// Helper used during lowering: track names produced by Fix / ExistsElim /
// IotaElim that subsequent ops can reference as term arguments (e.g.
// `forall_elim h1, x` where `x` was introduced by `fix x`).
struct LowerCtx {
    std::unordered_map<std::string, uint32_t> step_name_to_idx;
    std::unordered_map<std::string, uint32_t> term_name_to_idx;

    util::Result<StepRef> resolve_step(const std::string& name, const char* op) const {
        auto it = step_name_to_idx.find(name);
        if (it == step_name_to_idx.end())
            return MAKE_ERROR << op << ": unknown step '" << name << "'";
        return StepRef{it->second};
    }
    util::Result<TermRef> resolve_term(const std::string& name, const char* op) const {
        auto it = term_name_to_idx.find(name);
        if (it == term_name_to_idx.end())
            return MAKE_ERROR << op << ": unknown term '" << name << "'";
        return TermRef{it->second};
    }
};

// Lower a Kind::Rule step. Today's runtime dispatches by rule_name string;
// this produces the corresponding nd::Op struct.
util::Result<Instr> lower_rule(const ParsedProofStep& step, LowerCtx& lc) {
    const std::string& rule = step.rule_name;
    const auto& args = step.args;

    auto need_args = [&](size_t n) -> util::ResultStatus {
        if (args.size() != n)
            return MAKE_ERROR << rule << ": expected " << n << " arg(s), got " << args.size();
        return util::Ok();
    };
    auto need_arg_range = [&](size_t lo, size_t hi) -> util::ResultStatus {
        if (args.size() < lo || args.size() > hi)
            return MAKE_ERROR << rule << ": expected " << lo << "-" << hi
                              << " arg(s), got " << args.size();
        return util::Ok();
    };

    // Conjunction
    if (rule == "and_intro") {
        TRY(need_args(2));
        TRY_ASSIGN(a, lc.resolve_step(args[0], "and_intro"));
        TRY_ASSIGN(b, lc.resolve_step(args[1], "and_intro"));
        return Instr{AndIntro{{}, a, b}};
    }
    if (rule == "and_elim_l") {
        TRY(need_args(1));
        TRY_ASSIGN(of, lc.resolve_step(args[0], "and_elim_l"));
        return Instr{AndElimL{{}, of}};
    }
    if (rule == "and_elim_r") {
        TRY(need_args(1));
        TRY_ASSIGN(of, lc.resolve_step(args[0], "and_elim_r"));
        return Instr{AndElimR{{}, of}};
    }

    // Disjunction
    if (rule == "or_intro_l") {
        TRY(need_args(2));
        TRY_ASSIGN(a, lc.resolve_step(args[0], "or_intro_l"));
        TRY_ASSIGN(b, lc.resolve_step(args[1], "or_intro_l"));
        return Instr{OrIntroL{{}, a, b}};
    }
    if (rule == "or_intro_r") {
        TRY(need_args(2));
        TRY_ASSIGN(a, lc.resolve_step(args[0], "or_intro_r"));
        TRY_ASSIGN(b, lc.resolve_step(args[1], "or_intro_r"));
        return Instr{OrIntroR{{}, a, b}};
    }
    if (rule == "or_elim") {
        TRY(need_args(3));
        TRY_ASSIGN(o,  lc.resolve_step(args[0], "or_elim"));
        TRY_ASSIGN(ac, lc.resolve_step(args[1], "or_elim"));
        TRY_ASSIGN(bc, lc.resolve_step(args[2], "or_elim"));
        return Instr{OrElim{{}, o, ac, bc}};
    }

    // Implication
    if (rule == "implies_intro") {
        TRY(need_args(1));
        TRY_ASSIGN(c, lc.resolve_step(args[0], "implies_intro"));
        return Instr{ImpliesIntro{{}, c}};
    }
    if (rule == "implies_elim") {
        TRY(need_args(2));
        TRY_ASSIGN(impl, lc.resolve_step(args[0], "implies_elim"));
        TRY_ASSIGN(ant,  lc.resolve_step(args[1], "implies_elim"));
        return Instr{ImpliesElim{{}, impl, ant}};
    }

    // Negation
    if (rule == "not_intro") {
        TRY(need_args(1));
        TRY_ASSIGN(b, lc.resolve_step(args[0], "not_intro"));
        return Instr{NotIntro{{}, b}};
    }
    if (rule == "not_elim") {
        TRY(need_args(2));
        TRY_ASSIGN(neg, lc.resolve_step(args[0], "not_elim"));
        TRY_ASSIGN(f,   lc.resolve_step(args[1], "not_elim"));
        return Instr{NotElim{{}, neg, f}};
    }

    // Bottom
    if (rule == "bottom_elim") {
        TRY(need_args(2));
        TRY_ASSIGN(b, lc.resolve_step(args[0], "bottom_elim"));
        TRY_ASSIGN(f, lc.resolve_step(args[1], "bottom_elim"));
        return Instr{BottomElim{{}, b, f}};
    }

    // Biconditional
    if (rule == "iff_intro") {
        TRY(need_args(2));
        TRY_ASSIGN(ab, lc.resolve_step(args[0], "iff_intro"));
        TRY_ASSIGN(ba, lc.resolve_step(args[1], "iff_intro"));
        return Instr{IffIntro{{}, ab, ba}};
    }
    if (rule == "iff_elim_l") {
        TRY(need_args(2));
        TRY_ASSIGN(iff, lc.resolve_step(args[0], "iff_elim_l"));
        TRY_ASSIGN(a,   lc.resolve_step(args[1], "iff_elim_l"));
        return Instr{IffElimL{{}, iff, a}};
    }
    if (rule == "iff_elim_r") {
        TRY(need_args(2));
        TRY_ASSIGN(iff, lc.resolve_step(args[0], "iff_elim_r"));
        TRY_ASSIGN(b,   lc.resolve_step(args[1], "iff_elim_r"));
        return Instr{IffElimR{{}, iff, b}};
    }

    // Quantifiers
    if (rule == "forall_intro") {
        TRY(need_args(1));
        TRY_ASSIGN(body, lc.resolve_step(args[0], "forall_intro"));
        return Instr{ForallIntro{{}, body}};
    }
    if (rule == "forall_elim") {
        TRY(need_args(2));
        TRY_ASSIGN(f, lc.resolve_step(args[0], "forall_elim"));
        TRY_ASSIGN(t, lc.resolve_term(args[1], "forall_elim"));
        return Instr{ForallElim{{}, f, t}};
    }
    if (rule == "exists_intro") {
        TRY(need_arg_range(1, 2));
        TRY_ASSIGN(body, lc.resolve_step(args[0], "exists_intro"));
        std::optional<TermRef> w;
        if (args.size() == 2) {
            TRY_ASSIGN(t, lc.resolve_term(args[1], "exists_intro"));
            w = t;
        }
        return Instr{ExistsIntro{{}, body, w}};
    }
    if (rule == "exists_elim") {
        TRY(need_arg_range(1, 2));
        TRY_ASSIGN(f, lc.resolve_step(args[0], "exists_elim"));
        std::optional<ScopeName> bind;
        if (args.size() == 2) bind = ScopeName{args[1]};
        return Instr{ExistsElim{{}, f, bind}};
    }

    // Equality
    if (rule == "eq_subst") {
        TRY(need_args(2));
        TRY_ASSIGN(eq,     lc.resolve_step(args[0], "eq_subst"));
        TRY_ASSIGN(target, lc.resolve_step(args[1], "eq_subst"));
        return Instr{EqSubst{{}, eq, target}};
    }
    if (rule == "eq_sym") {
        TRY(need_args(1));
        TRY_ASSIGN(eq, lc.resolve_step(args[0], "eq_sym"));
        return Instr{EqSym{{}, eq}};
    }

    // Classical
    if (rule == "double_neg_elim") {
        TRY(need_args(1));
        TRY_ASSIGN(of, lc.resolve_step(args[0], "double_neg_elim"));
        return Instr{DoubleNegElim{{}, of}};
    }
    if (rule == "excluded_middle") {
        TRY(need_args(1));
        TRY_ASSIGN(f, lc.resolve_step(args[0], "excluded_middle"));
        return Instr{ExcludedMiddle{{}, f}};
    }
    if (rule == "classical_absurd") {
        TRY(need_args(1));
        TRY_ASSIGN(b, lc.resolve_step(args[0], "classical_absurd"));
        return Instr{ClassicalAbsurd{{}, b}};
    }
    if (rule == "peirce") {
        TRY(need_args(2));
        TRY_ASSIGN(a, lc.resolve_step(args[0], "peirce"));
        TRY_ASSIGN(b, lc.resolve_step(args[1], "peirce"));
        return Instr{Peirce{{}, a, b}};
    }

    // Iota
    if (rule == "iota_elim") {
        TRY(need_arg_range(1, 2));
        TRY_ASSIGN(f, lc.resolve_step(args[0], "iota_elim"));
        std::optional<ScopeName> bind;
        if (args.size() == 2) bind = ScopeName{args[1]};
        return Instr{IotaElim{{}, f, bind}};
    }

    return MAKE_ERROR << "unknown rule: " << rule;
}

}  // namespace

util::Result<NDProgram> lower(const ParsedProof& parsed) {
    NDProgram prog;
    prog.claim_name = parsed.claim_name;
    prog.instrs.reserve(parsed.steps.size());

    LowerCtx lc;

    for (size_t i = 0; i < parsed.steps.size(); ++i) {
        const auto& step = parsed.steps[i];
        const uint32_t idx = static_cast<uint32_t>(prog.instrs.size());

        Instr instr;
        switch (step.kind) {
            case ParsedProofStep::Kind::Fix: {
                if (step.args.empty())
                    return MAKE_ERROR << "step " << (i + 1) << ": fix requires variable name";
                ScopeName name{step.args[0]};
                instr = Fix{{}, std::move(name)};
                lc.term_name_to_idx[step.args[0]] = idx;
                break;
            }

            case ParsedProofStep::Kind::Assume: {
                if (!step.formula_ast)
                    return MAKE_ERROR << "step " << (i + 1) << ": assume requires formula";
                instr = Assume{{}, step.formula_ast};
                break;
            }

            case ParsedProofStep::Kind::Let: {
                if (!step.formula_ast)
                    return MAKE_ERROR << "step " << (i + 1) << ": let requires formula";
                instr = Let{{}, step.formula_ast};
                break;
            }

            case ParsedProofStep::Kind::Use: {
                instr = Use{{}, AxiomRef{step.rule_name}};
                break;
            }

            case ParsedProofStep::Kind::Rule: {
                auto r = lower_rule(step, lc);
                if (!r.ok())
                    return MAKE_ERROR << "step " << (i + 1) << ": " << r.error().to_string();
                instr = std::move(r).unwrap();
                // Side-effect: name-binding ops register their term names so
                // subsequent rule steps can resolve them. exists_elim and
                // iota_elim with a second arg both bind a term.
                if ((step.rule_name == "exists_elim" || step.rule_name == "iota_elim")
                    && step.args.size() == 2) {
                    lc.term_name_to_idx[step.args[1]] = idx;
                }
                break;
            }

            case ParsedProofStep::Kind::SchemaInst: {
                SchemaInstData data{SchemaRef{step.rule_name}, step.schema_bindings};
                instr = SchemaInst{{}, std::move(data)};
                break;
            }

            case ParsedProofStep::Kind::Qed: {
                if (step.args.empty())
                    return MAKE_ERROR << "step " << (i + 1) << ": qed requires step name";
                auto r = lc.resolve_step(step.args[0], "qed");
                if (!r.ok())
                    return MAKE_ERROR << "step " << (i + 1) << ": " << r.error().to_string();
                instr = Qed{{}, r.value()};
                break;
            }
        }

        prog.instrs.push_back(std::move(instr));

        if (!step.result_name.empty()) {
            lc.step_name_to_idx[step.result_name] = idx;
            prog.step_index[step.result_name] = idx;
        }
    }

    return prog;
}

}  // namespace logic::proof::nd
