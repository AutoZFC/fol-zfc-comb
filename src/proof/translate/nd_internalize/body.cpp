#include "src/proof/translate/nd_internalize/body.h"

#include "src/proof/translate/pass.h"   // overloaded { } visitor helper

#include <variant>

namespace logic::proof::translate::nd_internalize {

namespace {

constexpr uint32_t kInvalid = static_cast<uint32_t>(-1);

// Exhaustive StepRef / TermRef rewriter; same shape as the helper in
// schema_macro.cpp. Adding a new ND op variant without updating this
// visitor is a compile error.
//
// Duplicate of schema_macro.cpp's private remap_refs by design (math-
// first phase boundary: Phase 5 is local to body emission). The two
// will be unified into a shared internal helper as part of the post-
// Stage-1 cleanup once axiom_rewrap is deleted.
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
            nd::AndIntro o = op; o.a = S(op.a); o.b = S(op.b); return nd::Instr{o};
        },
        [&](const nd::AndElimL& op) -> nd::Instr { nd::AndElimL o = op; o.of = S(op.of); return nd::Instr{o}; },
        [&](const nd::AndElimR& op) -> nd::Instr { nd::AndElimR o = op; o.of = S(op.of); return nd::Instr{o}; },

        [&](const nd::OrIntroL& op) -> nd::Instr {
            nd::OrIntroL o = op; o.a = S(op.a); o.b_formula = S(op.b_formula); return nd::Instr{o};
        },
        [&](const nd::OrIntroR& op) -> nd::Instr {
            nd::OrIntroR o = op; o.a_formula = S(op.a_formula); o.b = S(op.b); return nd::Instr{o};
        },
        [&](const nd::OrElim& op) -> nd::Instr {
            nd::OrElim o = op; o.or_formula = S(op.or_formula); o.ac = S(op.ac); o.bc = S(op.bc);
            return nd::Instr{o};
        },

        [&](const nd::ImpliesIntro& op) -> nd::Instr {
            nd::ImpliesIntro o = op; o.conclusion = S(op.conclusion); return nd::Instr{o};
        },
        [&](const nd::ImpliesElim& op) -> nd::Instr {
            nd::ImpliesElim o = op; o.impl = S(op.impl); o.ant = S(op.ant); return nd::Instr{o};
        },

        [&](const nd::NotIntro& op) -> nd::Instr {
            nd::NotIntro o = op; o.bottom = S(op.bottom); return nd::Instr{o};
        },
        [&](const nd::NotElim& op) -> nd::Instr {
            nd::NotElim o = op; o.negation = S(op.negation); o.formula = S(op.formula); return nd::Instr{o};
        },
        [&](const nd::BottomElim& op) -> nd::Instr {
            nd::BottomElim o = op; o.bottom = S(op.bottom); o.target_formula = S(op.target_formula);
            return nd::Instr{o};
        },

        [&](const nd::IffIntro& op) -> nd::Instr {
            nd::IffIntro o = op; o.ab = S(op.ab); o.ba = S(op.ba); return nd::Instr{o};
        },
        [&](const nd::IffElimL& op) -> nd::Instr {
            nd::IffElimL o = op; o.iff = S(op.iff); o.a = S(op.a); return nd::Instr{o};
        },
        [&](const nd::IffElimR& op) -> nd::Instr {
            nd::IffElimR o = op; o.iff = S(op.iff); o.b = S(op.b); return nd::Instr{o};
        },

        [&](const nd::ForallIntro& op) -> nd::Instr {
            nd::ForallIntro o = op; o.body = S(op.body); return nd::Instr{o};
        },
        [&](const nd::ForallElim& op) -> nd::Instr {
            nd::ForallElim o = op; o.formula = S(op.formula); o.term = T(op.term); return nd::Instr{o};
        },

        [&](const nd::ExistsIntro& op) -> nd::Instr {
            nd::ExistsIntro o = op; o.body = S(op.body);
            if (op.witness.has_value()) o.witness = T(*op.witness);
            return nd::Instr{o};
        },
        [&](const nd::ExistsElim& op) -> nd::Instr {
            nd::ExistsElim o = op; o.formula = S(op.formula); return nd::Instr{o};
        },

        [&](const nd::EqSubst& op) -> nd::Instr {
            nd::EqSubst o = op; o.eq_formula = S(op.eq_formula); o.target = S(op.target);
            return nd::Instr{o};
        },
        [&](const nd::EqSym& op) -> nd::Instr {
            nd::EqSym o = op; o.eq_formula = S(op.eq_formula); return nd::Instr{o};
        },

        [&](const nd::DoubleNegElim& op)   -> nd::Instr { nd::DoubleNegElim o = op; o.of = S(op.of); return nd::Instr{o}; },
        [&](const nd::ExcludedMiddle& op)  -> nd::Instr { nd::ExcludedMiddle o = op; o.formula_let = S(op.formula_let); return nd::Instr{o}; },
        [&](const nd::ClassicalAbsurd& op) -> nd::Instr { nd::ClassicalAbsurd o = op; o.bottom = S(op.bottom); return nd::Instr{o}; },
        [&](const nd::Peirce& op) -> nd::Instr {
            nd::Peirce o = op; o.a_let = S(op.a_let); o.b_let = S(op.b_let); return nd::Instr{o};
        },

        [&](const nd::IotaElim& op) -> nd::Instr {
            nd::IotaElim o = op; o.exists_formula = S(op.exists_formula); return nd::Instr{o};
        },
        [&](const nd::Qed& op) -> nd::Instr { nd::Qed o = op; o.derived = S(op.derived); return nd::Instr{o}; },
    }, instr);
}

}  // namespace

util::Result<BodyEmitResult>
emit_body_with_remap(
    const Program<nd::Instr>& body,
    const std::unordered_map<SentenceHandle, StepRef, SentenceHandleHash>& table,
    uint32_t prelude_length)
{
    BodyEmitResult result;

    // step_remap[i] = absolute output index where input op `i`'s result
    // lives in the final wrapped program. Two regimes:
    //   - Dropped Use(F): step_remap[i] = table[F].idx (a prelude index)
    //   - Other ops: step_remap[i] = prelude_length + body-local index
    // The dropped Qed has no step_remap entry (its derived field's
    // remapped index is captured in qed_target instead).
    std::vector<uint32_t> step_remap(body.instrs.size(), kInvalid);
    bool qed_seen = false;

    for (uint32_t i = 0; i < body.instrs.size(); ++i) {
        const auto& instr = body.instrs[i];

        // Input-gate: schema macro must have run upstream.
        if (std::holds_alternative<nd::SchemaInst>(instr)) {
            return MAKE_ERROR
                << "emit_body_with_remap: SchemaInst present in body; "
                   "Stage 1's schema_macro must run upstream of body emission";
        }

        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            auto it = table.find(u->axiom.sentence);
            if (it == table.end()) {
                return MAKE_ERROR
                    << "emit_body_with_remap: Use's SentenceHandle absent from "
                       "fact_step_table — caller did not feed the same facts "
                       "list to compute_transitive_facts / emit_prelude as is "
                       "actually referenced in the body";
            }
            step_remap[i] = it->second.idx;
            continue;
        }

        if (const auto* q = std::get_if<nd::Qed>(&instr)) {
            if (qed_seen) {
                return MAKE_ERROR
                    << "emit_body_with_remap: multiple Qed ops in body "
                       "(unexpected — verifier should reject)";
            }
            uint32_t mapped = step_remap[q->derived.idx];
            if (mapped == kInvalid) {
                return MAKE_ERROR
                    << "emit_body_with_remap: Qed.derived references step "
                    << q->derived.idx << " which has no remap entry "
                       "(forward reference or missing prior op)";
            }
            result.qed_target = StepRef{mapped};
            qed_seen = true;
            continue;
        }

        // Generic non-Use, non-Qed: copy with remap.
        uint32_t output_idx = prelude_length +
                              static_cast<uint32_t>(result.instrs.size());
        step_remap[i] = output_idx;
        result.instrs.push_back(remap_refs(instr, step_remap));
    }

    if (!qed_seen) {
        return MAKE_ERROR << "emit_body_with_remap: body has no Qed op";
    }
    return result;
}

}  // namespace logic::proof::translate::nd_internalize
