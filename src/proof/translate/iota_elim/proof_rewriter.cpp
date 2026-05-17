#include "proof_rewriter.h"

#include "src/proof/translate/pass.h"   // overloaded combinator

#include <algorithm>
#include <map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace logic::proof::translate::iota_elim {

namespace {

using IndexMap = std::vector<uint32_t>;

constexpr uint32_t kInvalidIdx = static_cast<uint32_t>(-1);

util::Result<uint32_t> remap(const IndexMap& m, uint32_t old_idx,
                              const char* op_name)
{
    if (old_idx >= m.size() || m[old_idx] == kInvalidIdx) {
        return MAKE_ERROR << "ProofRewriter::" << op_name
                          << ": dangling ref to old idx " << old_idx;
    }
    return m[old_idx];
}

// Rewrite all StepRef/TermRef fields in `instr` through `m`.
util::Result<nd::Instr> rewrite_refs(const nd::Instr& instr,
                                      const IndexMap& m)
{
    auto S = [&](StepRef r, const char* op) -> util::Result<StepRef> {
        TRY_ASSIGN(ni, remap(m, r.idx, op));
        return StepRef{ni};
    };
    auto T = [&](TermRef r, const char* op) -> util::Result<TermRef> {
        TRY_ASSIGN(ni, remap(m, r.idx, op));
        return TermRef{ni};
    };

    return std::visit(overloaded{
        [&](const nd::Fix& op)         -> util::Result<nd::Instr> { return nd::Instr{op}; },
        [&](const nd::Assume& op)      -> util::Result<nd::Instr> { return nd::Instr{op}; },
        [&](const nd::Let& op)         -> util::Result<nd::Instr> { return nd::Instr{op}; },
        [&](const nd::Use& op)         -> util::Result<nd::Instr> { return nd::Instr{op}; },
        [&](const nd::SchemaInst& op)  -> util::Result<nd::Instr> { return nd::Instr{op}; },

        [&](const nd::AndIntro& op) -> util::Result<nd::Instr> {
            nd::AndIntro o = op;
            TRY_ASSIGN(a, S(op.a, "and_intro")); o.a = a;
            TRY_ASSIGN(b, S(op.b, "and_intro")); o.b = b;
            return nd::Instr{o};
        },
        [&](const nd::AndElimL& op) -> util::Result<nd::Instr> {
            nd::AndElimL o = op;
            TRY_ASSIGN(of, S(op.of, "and_elim_l")); o.of = of;
            return nd::Instr{o};
        },
        [&](const nd::AndElimR& op) -> util::Result<nd::Instr> {
            nd::AndElimR o = op;
            TRY_ASSIGN(of, S(op.of, "and_elim_r")); o.of = of;
            return nd::Instr{o};
        },

        [&](const nd::OrIntroL& op) -> util::Result<nd::Instr> {
            nd::OrIntroL o = op;
            TRY_ASSIGN(a, S(op.a,         "or_intro_l")); o.a = a;
            TRY_ASSIGN(b, S(op.b_formula, "or_intro_l")); o.b_formula = b;
            return nd::Instr{o};
        },
        [&](const nd::OrIntroR& op) -> util::Result<nd::Instr> {
            nd::OrIntroR o = op;
            TRY_ASSIGN(a, S(op.a_formula, "or_intro_r")); o.a_formula = a;
            TRY_ASSIGN(b, S(op.b,         "or_intro_r")); o.b = b;
            return nd::Instr{o};
        },
        [&](const nd::OrElim& op) -> util::Result<nd::Instr> {
            nd::OrElim o = op;
            TRY_ASSIGN(orf, S(op.or_formula, "or_elim")); o.or_formula = orf;
            TRY_ASSIGN(ac,  S(op.ac,         "or_elim")); o.ac = ac;
            TRY_ASSIGN(bc,  S(op.bc,         "or_elim")); o.bc = bc;
            return nd::Instr{o};
        },

        [&](const nd::ImpliesIntro& op) -> util::Result<nd::Instr> {
            nd::ImpliesIntro o = op;
            TRY_ASSIGN(c, S(op.conclusion, "implies_intro")); o.conclusion = c;
            return nd::Instr{o};
        },
        [&](const nd::ImpliesElim& op) -> util::Result<nd::Instr> {
            nd::ImpliesElim o = op;
            TRY_ASSIGN(impl, S(op.impl, "implies_elim")); o.impl = impl;
            TRY_ASSIGN(ant,  S(op.ant,  "implies_elim")); o.ant = ant;
            return nd::Instr{o};
        },

        [&](const nd::NotIntro& op) -> util::Result<nd::Instr> {
            nd::NotIntro o = op;
            TRY_ASSIGN(b, S(op.bottom, "not_intro")); o.bottom = b;
            return nd::Instr{o};
        },
        [&](const nd::NotElim& op) -> util::Result<nd::Instr> {
            nd::NotElim o = op;
            TRY_ASSIGN(n, S(op.negation, "not_elim")); o.negation = n;
            TRY_ASSIGN(f, S(op.formula,  "not_elim")); o.formula = f;
            return nd::Instr{o};
        },
        [&](const nd::BottomElim& op) -> util::Result<nd::Instr> {
            nd::BottomElim o = op;
            TRY_ASSIGN(b, S(op.bottom,          "bottom_elim")); o.bottom = b;
            TRY_ASSIGN(t, S(op.target_formula,  "bottom_elim")); o.target_formula = t;
            return nd::Instr{o};
        },

        [&](const nd::IffIntro& op) -> util::Result<nd::Instr> {
            nd::IffIntro o = op;
            TRY_ASSIGN(ab, S(op.ab, "iff_intro")); o.ab = ab;
            TRY_ASSIGN(ba, S(op.ba, "iff_intro")); o.ba = ba;
            return nd::Instr{o};
        },
        [&](const nd::IffElimL& op) -> util::Result<nd::Instr> {
            nd::IffElimL o = op;
            TRY_ASSIGN(iff, S(op.iff, "iff_elim_l")); o.iff = iff;
            TRY_ASSIGN(a,   S(op.a,   "iff_elim_l")); o.a = a;
            return nd::Instr{o};
        },
        [&](const nd::IffElimR& op) -> util::Result<nd::Instr> {
            nd::IffElimR o = op;
            TRY_ASSIGN(iff, S(op.iff, "iff_elim_r")); o.iff = iff;
            TRY_ASSIGN(b,   S(op.b,   "iff_elim_r")); o.b = b;
            return nd::Instr{o};
        },

        [&](const nd::ForallIntro& op) -> util::Result<nd::Instr> {
            nd::ForallIntro o = op;
            TRY_ASSIGN(b, S(op.body, "forall_intro")); o.body = b;
            return nd::Instr{o};
        },
        [&](const nd::ForallElim& op) -> util::Result<nd::Instr> {
            nd::ForallElim o = op;
            TRY_ASSIGN(f, S(op.formula, "forall_elim")); o.formula = f;
            TRY_ASSIGN(t, T(op.term,    "forall_elim")); o.term = t;
            return nd::Instr{o};
        },

        [&](const nd::ExistsIntro& op) -> util::Result<nd::Instr> {
            nd::ExistsIntro o = op;
            TRY_ASSIGN(b, S(op.body, "exists_intro")); o.body = b;
            if (op.witness.has_value()) {
                TRY_ASSIGN(w, T(*op.witness, "exists_intro"));
                o.witness = w;
            }
            return nd::Instr{o};
        },
        [&](const nd::ExistsElim& op) -> util::Result<nd::Instr> {
            nd::ExistsElim o = op;
            TRY_ASSIGN(f, S(op.formula, "exists_elim")); o.formula = f;
            return nd::Instr{o};
        },

        [&](const nd::EqSubst&) -> util::Result<nd::Instr> {
            // eq_subst is deprecated in translation. NDtoLKR gates programs
            // containing it; this arm exists only to keep std::visit
            // exhaustive.
            return MAKE_ERROR
                << "ProofRewriter::rewrite_refs: eq_subst is deprecated "
                << "(see src/proof/translate/EQ_SUBST_DEPRECATION.md)";
        },
        [&](const nd::EqSym& op) -> util::Result<nd::Instr> {
            nd::EqSym o = op;
            TRY_ASSIGN(e, S(op.eq_formula, "eq_sym")); o.eq_formula = e;
            return nd::Instr{o};
        },

        [&](const nd::DoubleNegElim& op) -> util::Result<nd::Instr> {
            nd::DoubleNegElim o = op;
            TRY_ASSIGN(x, S(op.of, "double_neg_elim")); o.of = x;
            return nd::Instr{o};
        },
        [&](const nd::ExcludedMiddle& op) -> util::Result<nd::Instr> {
            nd::ExcludedMiddle o = op;
            TRY_ASSIGN(x, S(op.formula_let, "excluded_middle")); o.formula_let = x;
            return nd::Instr{o};
        },
        [&](const nd::ClassicalAbsurd& op) -> util::Result<nd::Instr> {
            nd::ClassicalAbsurd o = op;
            TRY_ASSIGN(x, S(op.bottom, "classical_absurd")); o.bottom = x;
            return nd::Instr{o};
        },
        [&](const nd::Peirce& op) -> util::Result<nd::Instr> {
            nd::Peirce o = op;
            TRY_ASSIGN(a, S(op.a_let, "peirce")); o.a_let = a;
            TRY_ASSIGN(b, S(op.b_let, "peirce")); o.b_let = b;
            return nd::Instr{o};
        },

        [&](const nd::IotaElim&) -> util::Result<nd::Instr> {
            // IotaElim is converted to ExistsElim earlier in apply(); this
            // arm should be unreachable in the rewrite pass.
            return MAKE_ERROR
                << "ProofRewriter::rewrite_refs: encountered iota_elim "
                << "(should have been converted to exists_elim)";
        },
        [&](const nd::Qed& op) -> util::Result<nd::Instr> {
            nd::Qed o = op;
            TRY_ASSIGN(d, S(op.derived, "qed")); o.derived = d;
            return nd::Instr{o};
        },
    }, instr);
}

// Override the "body / conclusion / bottom / derived" StepRef on a
// scope-closer or qed instruction to point at the supplied new target.
nd::Instr override_close_target(const nd::Instr& instr, uint32_t new_target) {
    return std::visit(overloaded{
        [&](const nd::ForallIntro& op) -> nd::Instr {
            auto o = op; o.body = StepRef{new_target}; return nd::Instr{o};
        },
        [&](const nd::ImpliesIntro& op) -> nd::Instr {
            auto o = op; o.conclusion = StepRef{new_target}; return nd::Instr{o};
        },
        [&](const nd::NotIntro& op) -> nd::Instr {
            auto o = op; o.bottom = StepRef{new_target}; return nd::Instr{o};
        },
        [&](const nd::ExistsIntro& op) -> nd::Instr {
            // Scope-closing form (no witness) — caller enforces this.
            auto o = op; o.body = StepRef{new_target}; return nd::Instr{o};
        },
        [&](const nd::Qed& op) -> nd::Instr {
            auto o = op; o.derived = StepRef{new_target}; return nd::Instr{o};
        },
        [&](const auto& op) -> nd::Instr {
            return nd::Instr{op};   // shouldn't be called on others
        },
    }, instr);
}

}  // namespace

util::Result<Program<nd::Instr>> ProofRewriter::apply(
    const Program<nd::Instr>& in,
    const EliminationPlan&    plan)
{
    Program<nd::Instr> out;
    out.claim_name = in.claim_name;

    // Group actions by scope_close_idx; within each group, sort by
    // iota_idx descending so the innermost iota's closer fires first.
    std::map<uint32_t, std::vector<uint32_t>> closers_at;
    std::unordered_set<uint32_t> iota_set;
    for (const auto& a : plan.actions()) {
        closers_at[a.scope_close_idx].push_back(a.iota_idx);
        iota_set.insert(a.iota_idx);
    }
    for (auto& [k, v] : closers_at) {
        std::sort(v.begin(), v.end(), std::greater<>());
    }

    IndexMap old_to_new(in.instrs.size(), kInvalidIdx);
    out.instrs.reserve(in.instrs.size() + plan.actions().size());

    for (uint32_t i = 0; i < in.instrs.size(); ++i) {
        const auto& instr = in.instrs[i];

        auto cit = closers_at.find(i);
        bool inserts_closers = (cit != closers_at.end());

        uint32_t chain_prev = kInvalidIdx;
        if (inserts_closers) {
            // Read the original close target from the closer instruction's
            // body field (whichever applies).
            auto orig_target_old = std::visit(overloaded{
                [](const nd::ForallIntro& op)  -> uint32_t { return op.body.idx; },
                [](const nd::ImpliesIntro& op) -> uint32_t { return op.conclusion.idx; },
                [](const nd::NotIntro& op)     -> uint32_t { return op.bottom.idx; },
                [](const nd::ExistsIntro& op)  -> uint32_t { return op.body.idx; },
                [](const nd::Qed& op)          -> uint32_t { return op.derived.idx; },
                [](const auto&)                -> uint32_t { return kInvalidIdx; },
            }, instr);
            if (orig_target_old == kInvalidIdx) {
                return MAKE_ERROR
                    << "ProofRewriter: scope-close site at old idx " << i
                    << " is not a recognized closer (variant index "
                    << instr.index() << ")";
            }
            TRY_ASSIGN(rt, remap(old_to_new, orig_target_old,
                                  "scope_close_target"));
            chain_prev = rt;

            for (uint32_t iota_idx : cit->second) {
                (void)iota_idx;
                nd::ExistsIntro ei{};
                ei.body = StepRef{chain_prev};
                ei.witness = std::nullopt;   // scope-closing form
                out.instrs.emplace_back(std::move(ei));
                chain_prev = static_cast<uint32_t>(out.instrs.size() - 1);
            }
        }

        uint32_t new_idx = static_cast<uint32_t>(out.instrs.size());
        old_to_new[i] = new_idx;

        if (iota_set.count(i)) {
            // Convert iota_elim → exists_elim. Preserve the source
            // formula StepRef (remapped) and the bind name.
            const auto& ie = std::get<nd::IotaElim>(instr);
            TRY_ASSIGN(f, remap(old_to_new, ie.exists_formula.idx,
                                 "iota_elim.exists_formula"));
            nd::ExistsElim ee{};
            ee.h = ie.h;
            ee.formula = StepRef{f};
            ee.bind_witness = ie.bind_iota;
            out.instrs.emplace_back(std::move(ee));
        } else {
            TRY_ASSIGN(rewritten, rewrite_refs(instr, old_to_new));
            if (inserts_closers) {
                rewritten = override_close_target(rewritten, chain_prev);
            }
            out.instrs.emplace_back(std::move(rewritten));
        }
    }

    // Rewrite the source-level step name index.
    for (const auto& [name, old_idx] : in.step_index) {
        if (old_idx < old_to_new.size() && old_to_new[old_idx] != kInvalidIdx) {
            out.step_index[name] = old_to_new[old_idx];
        }
    }

    return out;
}

}  // namespace logic::proof::translate::iota_elim
