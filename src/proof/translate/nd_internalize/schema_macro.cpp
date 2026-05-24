#include "src/proof/translate/nd_internalize/schema_macro.h"

#include "src/proof/schema_resolve.h"
#include "src/proof/translate/pass.h"   // overloaded { } visitor helper

#include <algorithm>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <variant>

namespace logic::proof::translate::nd_internalize {

namespace {

constexpr uint32_t kInvalid = static_cast<uint32_t>(-1);

// =========================================================================
// Free-Fixed collection on a FormulaHandle.
// =========================================================================
// Sorted ascending (lex by var_index) for deterministic abstraction
// order. Quantified bodies bind generalized vars (via the inner
// Quantified node's binder); we recurse through quantifier bodies
// because Fixed vars in a body still refer to OUTER fix-scope (the
// quantifier binds a generalized, not a fixed).
void collect_free_fixed(FormulaHandle h, std::set<var_index>& out);

void collect_free_fixed_in_term(const Term& t, std::set<var_index>& out) {
    if (t.is_fixed()) {
        out.insert(t.as_variable());
        return;
    }
    if (t.is_description()) {
        collect_free_fixed(t.as_description().body, out);
    }
}

void collect_free_fixed(FormulaHandle h, std::set<var_index>& out) {
    if (!h.valid()) return;
    const Formula& f = h.get();
    if (f.is_predicate()) {
        for (const Term& t : f.as_predicate().args()) collect_free_fixed_in_term(t, out);
        return;
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.left.valid())  collect_free_fixed(c.left,  out);
        if (c.right.valid()) collect_free_fixed(c.right, out);
        return;
    }
    if (f.is_quantified()) {
        collect_free_fixed(f.as_quantified().body, out);
        return;
    }
    if (f.is_schema_var()) {
        for (const Term& t : f.as_schema_var().args) collect_free_fixed_in_term(t, out);
        return;
    }
    // Sentence wrapper: closed by construction.
}

// =========================================================================
// StepRef / TermRef remap helper.
// =========================================================================
// Exhaustive variant copier; for every ND op, rewrite each StepRef and
// TermRef field through the input→output index table. Adding a new ND
// op kind to nd::Instr without updating this visitor is a compile error.
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

util::Result<SchemaMacroResult>
schema_macro(GlobalContext& ctx, const Program<nd::Instr>& prog)
{
    SchemaMacroResult result;
    result.proof.claim_name = prog.claim_name;
    result.proof.instrs.reserve(prog.instrs.size());

    FormulaBuilder builder(ctx);
    std::unordered_set<SentenceHandle, SentenceHandleHash> seen_facts;

    // Scope state mirroring the verifier's bookkeeping. The simple
    // invariant: each Fix and ExistsElim op opens a FixVarScope via
    // builder.enter_scope; each ForallIntro and ExistsIntro-without-
    // witness closes one via builder.exit_scope. Other ops do not
    // touch builder scope depth.
    std::unordered_map<std::string, Term>     name_table;        // monotonic; overwrite on rebind
    std::unordered_map<var_index, uint32_t>   fix_index_by_var;  // var_index → binding op's OUTPUT index

    // step_remap[input_idx] = output_idx (or kInvalid if not yet emitted).
    // Open-case SchemaInst replacement is 1:(m+1), so this can shift.
    std::vector<uint32_t> step_remap(prog.instrs.size(), kInvalid);

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        const auto& instr = prog.instrs[i];
        const uint32_t out_pos = static_cast<uint32_t>(result.proof.instrs.size());

        // ----- Scope-opening ops: track and copy -----
        if (const auto* fx = std::get_if<nd::Fix>(&instr)) {
            var_index vi = builder.enter_scope();
            fix_index_by_var[vi] = out_pos;
            if (!fx->var_name.name.empty()) {
                name_table[fx->var_name.name] = Term::fixed(vi);
            }
            result.proof.instrs.push_back(instr);
            step_remap[i] = out_pos;
            continue;
        }
        if (const auto* xe = std::get_if<nd::ExistsElim>(&instr)) {
            var_index vi = builder.enter_scope();
            fix_index_by_var[vi] = out_pos;
            if (xe->bind_witness.has_value() && !xe->bind_witness->name.empty()) {
                name_table[xe->bind_witness->name] = Term::fixed(vi);
            }
            nd::ExistsElim copy = *xe;
            copy.formula = StepRef{step_remap[xe->formula.idx]};
            result.proof.instrs.emplace_back(nd::Instr{std::move(copy)});
            step_remap[i] = out_pos;
            continue;
        }

        // ----- Scope-closing ops: exit_scope on Fix-like closes -----
        if (std::holds_alternative<nd::ForallIntro>(instr)) {
            builder.exit_scope();
            nd::Instr remapped = remap_refs(instr, step_remap);
            result.proof.instrs.push_back(std::move(remapped));
            step_remap[i] = out_pos;
            continue;
        }
        if (const auto* ei = std::get_if<nd::ExistsIntro>(&instr)) {
            // Mode 1 (explicit witness) does NOT close a scope; Mode 2
            // (no witness — closes the Exists scope) does.
            if (!ei->witness.has_value()) {
                builder.exit_scope();
            }
            nd::Instr remapped = remap_refs(instr, step_remap);
            result.proof.instrs.push_back(std::move(remapped));
            step_remap[i] = out_pos;
            continue;
        }

        // ----- The SchemaInst case (the work) -----
        if (const auto* si = std::get_if<nd::SchemaInst>(&instr)) {
            auto resolved = resolve_and_instantiate_schema(
                ctx, builder, si->data, name_table, "schema_macro");
            if (!resolved.ok()) {
                return MAKE_ERROR
                    << "schema_macro: SchemaInst binding resolution failed: "
                    << resolved.error().to_string();
            }
            FormulaHandle phi = std::move(resolved).unwrap();

            // Collect free Fixed vars in φᵢ (sorted ascending).
            std::set<var_index> free_set;
            collect_free_fixed(phi, free_set);
            std::vector<var_index> free_fixed(free_set.begin(), free_set.end());

            // Build closed_φ. For the closed case (m=0), closed_φ = φᵢ.
            // For the open case, abstract each Fixed in REVERSE order
            // so that the OUTERMOST Forall in closed_φ corresponds to
            // the FIRST entry in free_fixed (matches the ForallElim
            // chain's instantiation order).
            FormulaHandle closed = phi;
            for (auto it = free_fixed.rbegin(); it != free_fixed.rend(); ++it) {
                closed = builder.abstract_var(closed, *it);
                closed = builder.make_quantified(Op::Forall, closed);
            }

            // Register as a Sentence. SentenceRegistry interns by
            // structure → equivalent instances collapse to one SH.
            SentenceHandle sh = ctx.add_sentence(Sentence(closed));
            if (seen_facts.insert(sh).second) {
                result.synthetic_facts.push_back(sh);
            }

            // Emit Use(SH) + ForallElim chain.
            nd::Use use_op{};
            use_op.h     = si->h;
            use_op.axiom = AxiomRef{sh};
            uint32_t current = static_cast<uint32_t>(result.proof.instrs.size());
            result.proof.instrs.emplace_back(nd::Instr{std::move(use_op)});

            for (var_index vi : free_fixed) {
                auto fix_it = fix_index_by_var.find(vi);
                if (fix_it == fix_index_by_var.end()) {
                    return MAKE_ERROR
                        << "schema_macro: Fixed(" << vi << ") in φᵢ has no "
                           "known binding op in scope (var_index not tracked "
                           "by Fix/ExistsElim walker)";
                }
                nd::ForallElim fe{};
                fe.formula = StepRef{current};
                fe.term    = TermRef{fix_it->second};
                current = static_cast<uint32_t>(result.proof.instrs.size());
                result.proof.instrs.emplace_back(nd::Instr{std::move(fe)});
            }

            // step_remap[i] points to the FINAL step (= the derived φᵢ
            // after all ForallElims, matching the original SchemaInst's
            // result).
            step_remap[i] = current;
            continue;
        }

        // ----- Generic non-scope, non-SchemaInst op: copy with remap -----
        nd::Instr remapped = remap_refs(instr, step_remap);
        result.proof.instrs.push_back(std::move(remapped));
        step_remap[i] = out_pos;
    }

    // Rebuild step_index against output positions.
    for (const auto& [name, idx] : prog.step_index) {
        if (idx < step_remap.size() && step_remap[idx] != kInvalid) {
            result.proof.step_index[name] = step_remap[idx];
        }
    }

    return result;
}

}  // namespace logic::proof::translate::nd_internalize
