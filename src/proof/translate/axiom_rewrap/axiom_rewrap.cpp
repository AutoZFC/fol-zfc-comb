#include "src/proof/translate/axiom_rewrap/axiom_rewrap.h"

#include "src/proof/nd/verifier.h"
#include "src/proof/translate/pass.h"   // overloaded

#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace logic::proof::translate::axiom_rewrap {

namespace {

constexpr uint32_t kInvalid = static_cast<uint32_t>(-1);

// Remap every StepRef and TermRef field in `instr` through `remap`.
// `remap[i]` is the new index for input instr-index `i`. StepRefs and
// TermRefs share the same index space (both keyed by the instr that
// bound them — Fix/ExistsElim/IotaElim for terms, all other ops for
// steps), so a single table covers both. Exhaustive on the nd::Instr
// variant — adding a new op kind here is a compile error.
nd::Instr remap_refs(const nd::Instr& instr, const std::vector<uint32_t>& remap) {
    auto S = [&](StepRef r) { return StepRef{remap[r.idx]}; };
    auto T = [&](TermRef r) { return TermRef{remap[r.idx]}; };

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
            nd::IotaElim o = op; o.exists_formula = S(op.exists_formula);
            return nd::Instr{o};
        },
        [&](const nd::Qed& op) -> nd::Instr {
            nd::Qed o = op; o.derived = S(op.derived); return nd::Instr{o};
        },
    }, instr);
}

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

// Emit the prelude: synthetic Assume(H) followed by the and_elim chain
// that lands each axiom on its own step. Populates `axiom_step_table`
// mapping axiom name → StepRef in the output.
//
// Layout (n = |axioms|, H is left-associated lex-sorted conjunction):
//   [0]                     Assume(H)                                       ← binds h = H
//   [1 .. n-1]              AndElimL of h, then of prev result, …          ← (n-1) ops, peel left
//                                                                            h_2 = (((A_1∧A_2)∧A_3)∧…∧A_{n-1})
//                                                                            h_{n-1} = (A_1∧A_2)
//                                                                            h_1 = A_1                        ← bound at index n-1
//   [n .. 2n-2]             AndElimR of h, of h_2, …, of h_{n-1}            ← (n-1) ops, extract A_n, …, A_2
//   axiom_step_table[A_1] = StepRef{n-1}        (= h_1 directly)
//   axiom_step_table[A_k] = AndElimR's index for k = 2..n
//
// n = 1: prelude is just [Assume]; axiom_step_table[A_1] = StepRef{0}.
// n = 0: caller short-circuits before reaching here.
void emit_prelude(GlobalContext& /*ctx*/,
                  const std::vector<std::string>& axioms,
                  FormulaHandle H,
                  Program<nd::Instr>& out,
                  std::unordered_map<std::string, StepRef>& axiom_step_table) {
    nd::Assume assume_h{};
    assume_h.resolved = H;
    out.instrs.push_back(nd::Instr{assume_h});
    StepRef h_step{0};

    const size_t n = axioms.size();
    if (n == 1) {
        axiom_step_table[axioms[0]] = h_step;
        return;
    }

    // h_steps[i] is the StepRef binding h_{n-i}:
    //   h_steps[0]   = h_n   = h
    //   h_steps[1]   = h_{n-1}
    //   …
    //   h_steps[n-1] = h_1 = A_1
    std::vector<StepRef> h_steps;
    h_steps.reserve(n);
    h_steps.push_back(h_step);

    // (n-1) AndElimL ops, building h_{n-1} … h_1.
    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimL op{};
        op.of = h_steps[i];
        uint32_t idx = static_cast<uint32_t>(out.instrs.size());
        out.instrs.push_back(nd::Instr{op});
        h_steps.push_back(StepRef{idx});
    }

    // (n-1) AndElimR ops, extracting A_n, A_{n-1}, …, A_2.
    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimR op{};
        op.of = h_steps[i];        // h_{n-i} = (((A_1∧…∧A_{n-i-1}) ∧ A_{n-i}))
        uint32_t idx = static_cast<uint32_t>(out.instrs.size());
        out.instrs.push_back(nd::Instr{op});
        axiom_step_table[axioms[n - 1 - i]] = StepRef{idx};
    }

    // A_1 = h_1.
    axiom_step_table[axioms[0]] = h_steps[n - 1];
}

}  // namespace

util::Result<RewrapResult> AxiomRewrap::apply(const Program<nd::Instr>& in) {
    auto axioms_r = compute_transitive_axioms(in, ctx_, theorem_axioms_);
    if (!axioms_r.ok()) return axioms_r.error();
    std::vector<std::string> axioms = std::move(axioms_r).unwrap();

    // n = 0: identity pass-through.
    if (axioms.empty()) {
        return RewrapResult{in, goal_, std::move(axioms)};
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

    Program<nd::Instr> out;
    out.claim_name = in.claim_name;
    out.instrs.reserve(in.instrs.size() + 2 * axioms.size());

    // ===== Prelude: Assume(H) + and_elim chain =====
    std::unordered_map<std::string, StepRef> axiom_step_table;
    emit_prelude(ctx_, axioms, H, out, axiom_step_table);

    // ===== Body: copy with remap; drop direct axiom Uses =====
    //
    // step_remap[input_idx] is the output StepRef.idx for an input op's
    // result. For dropped Use(A), the entry points at axiom_step_table[A]'s
    // StepRef so downstream refs alias the cached extract. For all other
    // ops, the entry is the op's new instr index in `out`.
    std::vector<uint32_t> step_remap(in.instrs.size(), kInvalid);

    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        if (i == qed_idx) continue;   // original Qed is replaced by postlude

        // Drop direct-axiom Use ops: alias to the cached extract.
        // Theorem Use ops are kept verbatim (Phase 6 will wrap them).
        if (const auto* u = std::get_if<nd::Use>(&in.instrs[i])) {
            if (ctx_.find_axiom(u->axiom.name).has_value()) {
                step_remap[i] = axiom_step_table.at(u->axiom.name).idx;
                continue;
            }
        }

        uint32_t out_idx = static_cast<uint32_t>(out.instrs.size());
        step_remap[i] = out_idx;
        out.instrs.push_back(remap_refs(in.instrs[i], step_remap));
    }

    // ===== Postlude: ImpliesIntro + Qed =====
    uint32_t impl_intro_idx = static_cast<uint32_t>(out.instrs.size());
    nd::ImpliesIntro impl{};
    impl.conclusion = StepRef{step_remap[proved_step.idx]};
    out.instrs.push_back(nd::Instr{impl});

    nd::Qed qed{};
    qed.derived = StepRef{impl_intro_idx};
    out.instrs.push_back(nd::Instr{qed});

    // step_index: source-level step names map to new instr indices via
    // step_remap. The synthetic prelude/postlude ops carry no source
    // name; the dropped Qed entry is omitted. Use-aliased entries point
    // at the cached extract.
    for (const auto& [name, idx] : in.step_index) {
        if (idx == qed_idx) continue;
        uint32_t new_idx = step_remap[idx];
        if (new_idx != kInvalid) {
            out.step_index[name] = new_idx;
        }
    }

    // Output gate: NDVerifier must accept the wrapped output against H → φ.
    {
        nd::NDVerifier verifier;
        Proof p{};
        p.system = System::ND;
        p.body   = out;
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
