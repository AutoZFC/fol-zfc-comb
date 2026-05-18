#include "src/proof/translate/axiom_rewrap/axiom_rewrap.h"

#include "src/proof/nd/verifier.h"
#include "src/proof/translate/pass.h"   // overloaded

#include <utility>
#include <variant>

namespace logic::proof::translate::axiom_rewrap {

namespace {

// Shift every StepRef and TermRef field in `instr` by `k`.
// Mirrors iota_elim/proof_rewriter.cpp::rewrite_refs but with a uniform
// additive shift (no index map). Exhaustive on the nd::Instr variant.
nd::Instr shift_refs(const nd::Instr& instr, uint32_t k) {
    auto S = [k](StepRef r) { return StepRef{r.idx + k}; };
    auto T = [k](TermRef r) { return TermRef{r.idx + k}; };

    return std::visit(overloaded{
        [&](const nd::Fix& op)        -> nd::Instr { return nd::Instr{op}; },
        [&](const nd::Assume& op)     -> nd::Instr { return nd::Instr{op}; },
        [&](const nd::Let& op)        -> nd::Instr { return nd::Instr{op}; },
        [&](const nd::Use& op)        -> nd::Instr { return nd::Instr{op}; },
        [&](const nd::SchemaInst& op) -> nd::Instr { return nd::Instr{op}; },

        [&](const nd::AndIntro& op) -> nd::Instr {
            nd::AndIntro o = op; o.a = S(op.a); o.b = S(op.b);
            return nd::Instr{o};
        },
        [&](const nd::AndElimL& op) -> nd::Instr {
            nd::AndElimL o = op; o.of = S(op.of); return nd::Instr{o};
        },
        [&](const nd::AndElimR& op) -> nd::Instr {
            nd::AndElimR o = op; o.of = S(op.of); return nd::Instr{o};
        },

        [&](const nd::OrIntroL& op) -> nd::Instr {
            nd::OrIntroL o = op; o.a = S(op.a); o.b_formula = S(op.b_formula);
            return nd::Instr{o};
        },
        [&](const nd::OrIntroR& op) -> nd::Instr {
            nd::OrIntroR o = op; o.a_formula = S(op.a_formula); o.b = S(op.b);
            return nd::Instr{o};
        },
        [&](const nd::OrElim& op) -> nd::Instr {
            nd::OrElim o = op;
            o.or_formula = S(op.or_formula);
            o.ac = S(op.ac);
            o.bc = S(op.bc);
            return nd::Instr{o};
        },

        [&](const nd::ImpliesIntro& op) -> nd::Instr {
            nd::ImpliesIntro o = op; o.conclusion = S(op.conclusion);
            return nd::Instr{o};
        },
        [&](const nd::ImpliesElim& op) -> nd::Instr {
            nd::ImpliesElim o = op; o.impl = S(op.impl); o.ant = S(op.ant);
            return nd::Instr{o};
        },

        [&](const nd::NotIntro& op) -> nd::Instr {
            nd::NotIntro o = op; o.bottom = S(op.bottom); return nd::Instr{o};
        },
        [&](const nd::NotElim& op) -> nd::Instr {
            nd::NotElim o = op; o.negation = S(op.negation); o.formula = S(op.formula);
            return nd::Instr{o};
        },
        [&](const nd::BottomElim& op) -> nd::Instr {
            nd::BottomElim o = op; o.bottom = S(op.bottom);
            o.target_formula = S(op.target_formula);
            return nd::Instr{o};
        },

        [&](const nd::IffIntro& op) -> nd::Instr {
            nd::IffIntro o = op; o.ab = S(op.ab); o.ba = S(op.ba);
            return nd::Instr{o};
        },
        [&](const nd::IffElimL& op) -> nd::Instr {
            nd::IffElimL o = op; o.iff = S(op.iff); o.a = S(op.a);
            return nd::Instr{o};
        },
        [&](const nd::IffElimR& op) -> nd::Instr {
            nd::IffElimR o = op; o.iff = S(op.iff); o.b = S(op.b);
            return nd::Instr{o};
        },

        [&](const nd::ForallIntro& op) -> nd::Instr {
            nd::ForallIntro o = op; o.body = S(op.body); return nd::Instr{o};
        },
        [&](const nd::ForallElim& op) -> nd::Instr {
            nd::ForallElim o = op; o.formula = S(op.formula); o.term = T(op.term);
            return nd::Instr{o};
        },

        [&](const nd::ExistsIntro& op) -> nd::Instr {
            nd::ExistsIntro o = op; o.body = S(op.body);
            if (op.witness.has_value()) o.witness = T(*op.witness);
            return nd::Instr{o};
        },
        [&](const nd::ExistsElim& op) -> nd::Instr {
            nd::ExistsElim o = op; o.formula = S(op.formula);
            return nd::Instr{o};
        },

        [&](const nd::EqSubst& op) -> nd::Instr {
            nd::EqSubst o = op; o.eq_formula = S(op.eq_formula);
            o.target = S(op.target);
            return nd::Instr{o};
        },
        [&](const nd::EqSym& op) -> nd::Instr {
            nd::EqSym o = op; o.eq_formula = S(op.eq_formula);
            return nd::Instr{o};
        },

        [&](const nd::DoubleNegElim& op) -> nd::Instr {
            nd::DoubleNegElim o = op; o.of = S(op.of); return nd::Instr{o};
        },
        [&](const nd::ExcludedMiddle& op) -> nd::Instr {
            nd::ExcludedMiddle o = op; o.formula_let = S(op.formula_let);
            return nd::Instr{o};
        },
        [&](const nd::ClassicalAbsurd& op) -> nd::Instr {
            nd::ClassicalAbsurd o = op; o.bottom = S(op.bottom);
            return nd::Instr{o};
        },
        [&](const nd::Peirce& op) -> nd::Instr {
            nd::Peirce o = op; o.a_let = S(op.a_let); o.b_let = S(op.b_let);
            return nd::Instr{o};
        },

        [&](const nd::IotaElim& op) -> nd::Instr {
            // Input gate would normally reject iota_elim (pipeline runs
            // iota_elim translator upstream); shift defensively in case
            // axiom_rewrap is called on a non-iota-free input. The
            // downstream NDVerifier will catch the iota presence if it
            // matters semantically.
            nd::IotaElim o = op; o.exists_formula = S(op.exists_formula);
            return nd::Instr{o};
        },
        [&](const nd::Qed& op) -> nd::Instr {
            nd::Qed o = op; o.derived = S(op.derived); return nd::Instr{o};
        },
    }, instr);
}

// Locate the Qed op (expected to be the terminating op at program tail).
// Returns its index in prog.instrs.
util::Result<uint32_t> find_qed(const Program<nd::Instr>& prog) {
    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        if (std::holds_alternative<nd::Qed>(prog.instrs[i])) {
            return i;
        }
    }
    return MAKE_ERROR << "axiom_rewrap: input program has no Qed op";
}

// Build H = (((A_1 ∧ A_2) ∧ A_3) … ∧ A_n) left-associated.
// `axiom_names` is lex-sorted by caller.
FormulaHandle build_conjunction(GlobalContext& ctx,
                                FormulaBuilder& builder,
                                const std::vector<std::string>& axiom_names) {
    FormulaHandle h = ctx.find_axiom(axiom_names[0]).value().get().root();
    for (size_t i = 1; i < axiom_names.size(); ++i) {
        FormulaHandle a_i =
            ctx.find_axiom(axiom_names[i]).value().get().root();
        h = builder.make_and(h, a_i);
    }
    return h;
}

}  // namespace

util::Result<RewrapResult> AxiomRewrap::apply(const Program<nd::Instr>& in) {
    auto axioms_r = compute_transitive_axioms(in, ctx_, theorem_axioms_);
    if (!axioms_r.ok()) return axioms_r.error();
    std::vector<std::string> axioms = std::move(axioms_r).unwrap();

    // n = 0: identity pass-through.
    if (axioms.empty()) {
        return RewrapResult{
            in,            // copy
            goal_,
            std::move(axioms),
        };
    }

    // Build H and wrapped goal.
    FormulaBuilder builder(ctx_);
    FormulaHandle H        = build_conjunction(ctx_, builder, axioms);
    FormulaHandle wrapped  = builder.make_implies(H, goal_);

    // Find the input's Qed.
    auto qed_r = find_qed(in);
    if (!qed_r.ok()) return qed_r.error();
    uint32_t qed_idx = qed_r.value();
    const auto& qed_op = std::get<nd::Qed>(in.instrs[qed_idx]);
    StepRef proved_step = qed_op.derived;

    // Build wrapped program. Layout:
    //   [0]                 Assume(H)             ← prelude (size 1)
    //   [1 .. qed_idx]      body shifted by 1     (input's pre-Qed ops)
    //   [qed_idx + 1 ..]    body shifted by 1     (any post-Qed ops, rare)
    //   [N]                 ImpliesIntro(...)     ← postlude
    //   [N + 1]             Qed(...)
    constexpr uint32_t kPrelude = 1;  // Phase 2: no extracts yet

    Program<nd::Instr> out;
    out.claim_name = in.claim_name;
    out.instrs.reserve(in.instrs.size() + 2);  // -1 Qed dropped + 2 added

    // Prelude: synthetic Assume(H).
    nd::Assume assume_h{};
    assume_h.resolved = H;
    out.instrs.push_back(nd::Instr{assume_h});

    // Body: copy all input instrs except Qed, shifted by kPrelude.
    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        if (i == qed_idx) continue;
        out.instrs.push_back(shift_refs(in.instrs[i], kPrelude));
    }

    // Postlude: ImpliesIntro on the proved step, then Qed.
    uint32_t impl_intro_idx = static_cast<uint32_t>(out.instrs.size());
    nd::ImpliesIntro impl{};
    impl.conclusion = StepRef{proved_step.idx + kPrelude};
    out.instrs.push_back(nd::Instr{impl});

    nd::Qed qed{};
    qed.derived = StepRef{impl_intro_idx};
    out.instrs.push_back(nd::Instr{qed});

    // Rebuild step_index: each named entry shifts by kPrelude; the Qed
    // entry (if any) is dropped. The synthetic ops carry no source name.
    for (const auto& [name, idx] : in.step_index) {
        if (idx == qed_idx) continue;
        out.step_index[name] = idx + kPrelude;
    }

    // Output gate: NDVerifier must accept the wrapped output against the
    // wrapped goal.
    {
        nd::NDVerifier verifier;
        Proof p{};
        p.system = System::ND;
        p.body   = out;  // copy into the variant
        auto vr = verifier.verify(ctx_, wrapped, p);
        if (!vr.ok()) {
            return MAKE_ERROR
                << "axiom_rewrap: NDVerifier rejected wrapped output: "
                << vr.error().message();
        }
    }

    return RewrapResult{
        std::move(out),
        wrapped,
        std::move(axioms),
    };
}

}  // namespace logic::proof::translate::axiom_rewrap
