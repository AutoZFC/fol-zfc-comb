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

// Look up a fact's formula. Both axioms and theorems live in the
// runtime context; for facts that name a theorem, the formula is the
// theorem's claim (φ_T), unchanged.
FormulaHandle find_fact_formula(GlobalContext& ctx, const std::string& name) {
    if (auto ax = ctx.find_axiom(name); ax.has_value()) {
        return ax.value().get().root();
    }
    if (auto th = ctx.find_theorem(name); th.has_value()) {
        return th.value().get().root();
    }
    // Unreachable for facts validated by compute_transitive_facts.
    return FormulaHandle{};
}

// Build H = (((φ_F_1 ∧ φ_F_2) ∧ φ_F_3) … ∧ φ_F_n) left-associated.
// `fact_names` is lex-sorted by caller. F_i can be either an axiom or
// a theorem name; the corresponding formula is looked up uniformly.
FormulaHandle build_conjunction(GlobalContext& ctx,
                                FormulaBuilder& builder,
                                const std::vector<std::string>& fact_names) {
    FormulaHandle h = find_fact_formula(ctx, fact_names[0]);
    for (size_t i = 1; i < fact_names.size(); ++i) {
        h = builder.make_and(h, find_fact_formula(ctx, fact_names[i]));
    }
    return h;
}

// Emit the prelude: synthetic Assume(H) followed by the and_elim chain
// that lands each fact on its own step. Populates `fact_step_table`
// mapping fact name (axiom or theorem) → StepRef in the output.
//
// Layout (n = |facts|, H is left-associated lex-sorted conjunction):
//   [0]                     Assume(H)                                       ← binds h = H
//   [1 .. n-1]              AndElimL of h, then of prev result, …          ← (n-1) ops, peel left
//                                                                            h_{n-1} = (φ_1∧…∧φ_{n-1})
//                                                                            h_1     = φ_1                  ← bound at index n-1
//   [n .. 2n-2]             AndElimR of h, of h_2, …, of h_{n-1}            ← (n-1) ops, extract φ_n, …, φ_2
//   fact_step_table[F_1] = StepRef{n-1}        (= h_1 directly)
//   fact_step_table[F_k] = AndElimR's index for k = 2..n
//
// n = 1: prelude is just [Assume]; fact_step_table[F_1] = StepRef{0}.
// n = 0: caller short-circuits before reaching here.
void emit_prelude(GlobalContext& /*ctx*/,
                  const std::vector<std::string>& facts,
                  FormulaHandle H,
                  Program<nd::Instr>& out,
                  std::unordered_map<std::string, StepRef>& fact_step_table) {
    nd::Assume assume_h{};
    assume_h.resolved = H;
    out.instrs.push_back(nd::Instr{assume_h});
    StepRef h_step{0};

    const size_t n = facts.size();
    if (n == 1) {
        fact_step_table[facts[0]] = h_step;
        return;
    }

    std::vector<StepRef> h_steps;
    h_steps.reserve(n);
    h_steps.push_back(h_step);

    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimL op{};
        op.of = h_steps[i];
        uint32_t idx = static_cast<uint32_t>(out.instrs.size());
        out.instrs.push_back(nd::Instr{op});
        h_steps.push_back(StepRef{idx});
    }

    for (size_t i = 0; i + 1 < n; ++i) {
        nd::AndElimR op{};
        op.of = h_steps[i];
        uint32_t idx = static_cast<uint32_t>(out.instrs.size());
        out.instrs.push_back(nd::Instr{op});
        fact_step_table[facts[n - 1 - i]] = StepRef{idx};
    }

    fact_step_table[facts[0]] = h_steps[n - 1];
}

}  // namespace

util::Result<RewrapResult> AxiomRewrap::apply(const Program<nd::Instr>& in) {
    auto facts_r = compute_transitive_facts(in, ctx_, theorem_facts_);
    if (!facts_r.ok()) return facts_r.error();
    std::vector<std::string> facts = std::move(facts_r).unwrap();

    // n = 0: identity pass-through.
    if (facts.empty()) {
        return RewrapResult{in, goal_, std::move(facts)};
    }

    // Build H and wrapped goal.
    FormulaBuilder builder(ctx_);
    FormulaHandle H        = build_conjunction(ctx_, builder, facts);
    FormulaHandle wrapped  = builder.make_implies(H, goal_);

    // Find the input's Qed.
    auto qed_r = find_qed(in);
    if (!qed_r.ok()) return qed_r.error();
    uint32_t qed_idx = qed_r.value();
    const auto& qed_op = std::get<nd::Qed>(in.instrs[qed_idx]);
    StepRef proved_step = qed_op.derived;

    Program<nd::Instr> out;
    out.claim_name = in.claim_name;
    out.instrs.reserve(in.instrs.size() + 2 * facts.size());

    // ===== Prelude: Assume(H) + and_elim chain =====
    std::unordered_map<std::string, StepRef> fact_step_table;
    emit_prelude(ctx_, facts, H, out, fact_step_table);

    // ===== Body: copy with remap; drop every Use op uniformly =====
    //
    // step_remap[input_idx] is the output StepRef.idx for an input op's
    // result. Every Use(F) — axiom or theorem alike — is dropped and
    // aliased to the cached extract h_F from the prelude.
    std::vector<uint32_t> step_remap(in.instrs.size(), kInvalid);

    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        if (i == qed_idx) continue;   // original Qed is replaced by postlude

        if (const auto* u = std::get_if<nd::Use>(&in.instrs[i])) {
            auto it = fact_step_table.find(u->axiom.name);
            if (it == fact_step_table.end()) {
                // compute_transitive_facts should have validated every
                // cited fact; defensive error.
                return MAKE_ERROR
                    << "axiom_rewrap: Use('" << u->axiom.name
                    << "') has no entry in fact_step_table (transitive "
                       "facts computation skipped it?)";
            }
            step_remap[i] = it->second.idx;
            continue;
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
        std::move(facts),
    };
}

}  // namespace logic::proof::translate::axiom_rewrap
