#include "verifier.h"

#include "ops.h"

#include "src/core/formula.h"
#include "stack.h"
#include "src/parser/parser.h"
#include "src/util/error.h"

#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

namespace logic::proof::nd {

namespace {

// Per-verify private state. Owns the proof stack, the SSA envs (sparse,
// indexed by instr index), the scope-name table for resolving deferred
// formula ASTs, and the schema context (populated only for schema proofs).
struct Session {
    GlobalContext&       ctx;
    ClassicalProofStack  stack;
    FormulaHandle        goal_formula;
    const NDProgram&     prog;

    // SSA envs. Sized at construction to prog.instrs.size(); slots populated
    // as instrs execute. *_present[i] tracks whether slot i has been bound.
    std::vector<FormulaHandle> step_env;
    std::vector<Term>          term_env;
    std::vector<uint8_t>       step_present;
    std::vector<uint8_t>       term_present;

    // Source-level name -> Term, used by parse_formula_with_vars when
    // resolving deferred formula ASTs. Populated by Fix / ExistsElim /
    // IotaElim with binding.
    std::unordered_map<std::string, Term> name_table;

    // Schema parsing context: empty for claim proofs; populated for schema
    // proofs from the schema's var_names/var_arities.
    std::unordered_map<std::string, size_t> schema_var_map;
    std::unordered_map<std::string, size_t> schema_arity_map;

    // Theorems/axioms consulted via Use.
    std::unordered_set<std::string> used_names;

    bool completed = false;

    Session(GlobalContext& c, FormulaHandle g, const NDProgram& p)
        : ctx(c),
          stack(c),
          goal_formula(g),
          prog(p),
          step_env(p.instrs.size()),
          term_env(p.instrs.size()),
          step_present(p.instrs.size(), 0),
          term_present(p.instrs.size(), 0) {}

    void bind_step(uint32_t idx, FormulaHandle f) {
        step_env[idx] = f;
        step_present[idx] = 1;
    }
    void bind_term(uint32_t idx, Term t) {
        term_env[idx] = t;
        term_present[idx] = 1;
    }

    util::Result<FormulaHandle> resolve_step(StepRef r, const char* op_name) const {
        if (r.idx >= step_env.size() || !step_present[r.idx]) {
            return MAKE_ERROR << op_name << ": step %" << r.idx << " not bound";
        }
        return step_env[r.idx];
    }
    util::Result<Term> resolve_term(TermRef r, const char* op_name) const {
        if (r.idx >= term_env.size() || !term_present[r.idx]) {
            return MAKE_ERROR << op_name << ": term %" << r.idx << " not bound";
        }
        return term_env[r.idx];
    }
};

// Parse a deferred formula AST against the current Session state.
util::Result<FormulaHandle> parse_deferred(Session& s, const ASTNode* ast,
                                           const char* op_name) {
    if (!ast) return MAKE_ERROR << op_name << ": missing formula AST";
    return try_parse_formula_with_vars(
        ast, s.ctx, s.stack.builder(),
        s.name_table, s.schema_var_map, s.schema_arity_map);
}

// Resolve a SchemaInst's bindings at execute time. Schema bindings can
// reference fixed vars (in lambda bodies), so this must run with the
// current Session::name_table populated.
util::Result<FormulaResult> exec_schema_inst(Session& s, const SchemaInstData& data) {
    auto schema = s.ctx.find_schema(data.schema.name);
    if (!schema.has_value())
        return MAKE_ERROR << "schema_inst: unknown schema '" << data.schema.name << "'";
    if (!s.ctx.is_schema_proven(data.schema.name))
        return MAKE_ERROR << "schema_inst: schema '" << data.schema.name << "' not yet proven";

    s.used_names.insert(data.schema.name);

    std::vector<SchemaBind> bindings(schema->var_names.size());
    std::vector<bool>       bound(schema->var_names.size(), false);

    for (const auto& sb : data.bindings) {
        // Locate the schema variable index by name.
        size_t idx = schema->var_names.size();
        for (size_t j = 0; j < schema->var_names.size(); ++j) {
            if (schema->var_names[j] == sb.var_name) { idx = j; break; }
        }
        if (idx >= schema->var_names.size())
            return MAKE_ERROR << "schema_inst: unknown schema variable '" << sb.var_name << "'";
        if (bound[idx])
            return MAKE_ERROR << "schema_inst: duplicate binding for '" << sb.var_name << "'";

        size_t arity = (idx < schema->var_arities.size()) ? schema->var_arities[idx] : 0;

        if (arity == 0) {
            // Formula binding: parse as a concrete formula.
            TRY_ASSIGN(body, try_parse_formula_with_vars(
                sb.formula_ast.get(), s.ctx, s.stack.builder(),
                s.name_table, s.schema_var_map, s.schema_arity_map));
            bindings[idx] = SchemaBind(body);
        } else {
            // Predicate binding: \x. body. Body may reference other schema
            // vars from the *target* schema (so they are recognized as
            // SchemaVars), so we extend the schema_var/arity maps with the
            // target schema's vars before parsing the lambda body.
            auto sv_map = s.schema_var_map;
            auto ar_map = s.schema_arity_map;
            for (size_t j = 0; j < schema->var_names.size(); ++j) {
                if (!sv_map.count(schema->var_names[j])) {
                    sv_map[schema->var_names[j]] = j;
                    if (j < schema->var_arities.size())
                        ar_map[schema->var_names[j]] = schema->var_arities[j];
                }
            }
            // Determine lambda parameter names: explicit, or auto-generated
            // when the binding is a bare predicate name (e.g. P -> \x. P(x)).
            auto lambda_param_names = sb.lambda_params;
            if (lambda_param_names.empty()) {
                for (size_t a = 0; a < arity; ++a)
                    lambda_param_names.push_back("_lam" + std::to_string(a));
            }
            if (lambda_param_names.size() != arity)
                return MAKE_ERROR << "schema_inst: schema var '" << sb.var_name
                                  << "' expects " << arity << " lambda params, got "
                                  << lambda_param_names.size();

            // Allocate fresh fixed vars for the lambda parameters within
            // the formula builder's scope.
            auto lambda_vars = s.name_table;
            std::vector<var_index> param_indices;
            for (const auto& param : lambda_param_names) {
                var_index vi = s.stack.builder().enter_scope();
                lambda_vars[param] = Term::fixed(vi);
                param_indices.push_back(vi);
            }
            auto body_r = try_parse_formula_with_vars(
                sb.formula_ast.get(), s.ctx, s.stack.builder(),
                lambda_vars, sv_map, ar_map);
            for (size_t k = 0; k < arity; ++k) s.stack.builder().exit_scope();
            if (!body_r.ok()) return body_r.error();
            FormulaHandle body = std::move(body_r).unwrap();
            bindings[idx] = SchemaBind(std::move(param_indices), body);
        }
        bound[idx] = true;
    }
    for (size_t j = 0; j < bound.size(); ++j) {
        if (!bound[j])
            return MAKE_ERROR << "schema_inst: missing binding for '" << schema->var_names[j] << "'";
    }
    return s.stack.schema_inst(*schema, bindings);
}

// =========================================================================
// Per-op execution. One overload per nd::Op variant arm. Each arm
// implements the per-op semantic-table contract for ND (see design doc).
// =========================================================================

util::ResultStatus exec_op(Session& s, uint32_t idx, const Fix& op) {
    Term t = s.stack.fix_var();
    s.bind_term(idx, t);
    if (!op.var_name.name.empty()) {
        s.name_table[op.var_name.name] = t;
    }
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const Assume& op) {
    auto f = parse_deferred(s, op.formula.get(), "assume");
    if (!f.ok()) return f.error();
    FormulaHandle h = s.stack.assume(f.value());
    s.bind_step(idx, h);
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const Let& op) {
    auto f = parse_deferred(s, op.formula.get(), "let");
    if (!f.ok()) return f.error();
    s.bind_step(idx, f.value());
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const Use& op) {
    auto found = s.ctx.find_known(op.axiom.name);
    if (!found.has_value()) {
        return MAKE_ERROR << "use: unknown axiom/theorem '" << op.axiom.name << "'";
    }
    s.used_names.insert(op.axiom.name);
    SentenceHandle sent = found.value();
    auto r = s.stack.use_theorem(sent);
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const SchemaInst& op) {
    auto r = exec_schema_inst(s, op.data);
    if (!r.ok()) return r.error();
    auto& fr = r.value();
    if (!fr.ok()) return fr.error();
    s.bind_step(idx, fr.value());
    return util::Ok();
}

#define BIND_BINARY_STEP(OpName, MethodName, ARG_A, ARG_B) \
    util::ResultStatus exec_op(Session& s, uint32_t idx, const OpName& op) { \
        auto a = s.resolve_step(op.ARG_A, #MethodName); if (!a.ok()) return a.error(); \
        auto b = s.resolve_step(op.ARG_B, #MethodName); if (!b.ok()) return b.error(); \
        auto r = s.stack.MethodName(a.value(), b.value()); \
        if (!r.ok()) return r.error(); \
        s.bind_step(idx, r.value()); \
        return util::Ok(); \
    }

#define BIND_UNARY_STEP(OpName, MethodName, ARG) \
    util::ResultStatus exec_op(Session& s, uint32_t idx, const OpName& op) { \
        auto a = s.resolve_step(op.ARG, #MethodName); if (!a.ok()) return a.error(); \
        auto r = s.stack.MethodName(a.value()); \
        if (!r.ok()) return r.error(); \
        s.bind_step(idx, r.value()); \
        return util::Ok(); \
    }

BIND_BINARY_STEP(AndIntro,  and_intro,  a, b)
BIND_UNARY_STEP (AndElimL,  and_elim_l, of)
BIND_UNARY_STEP (AndElimR,  and_elim_r, of)

BIND_BINARY_STEP(OrIntroL,  or_intro_l, a,         b_formula)
BIND_BINARY_STEP(OrIntroR,  or_intro_r, a_formula, b)

util::ResultStatus exec_op(Session& s, uint32_t idx, const OrElim& op) {
    auto orf = s.resolve_step(op.or_formula, "or_elim"); if (!orf.ok()) return orf.error();
    auto ac  = s.resolve_step(op.ac,         "or_elim"); if (!ac.ok())  return ac.error();
    auto bc  = s.resolve_step(op.bc,         "or_elim"); if (!bc.ok())  return bc.error();
    auto r = s.stack.or_elim(orf.value(), ac.value(), bc.value());
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    return util::Ok();
}

BIND_UNARY_STEP (ImpliesIntro, implies_intro, conclusion)
BIND_BINARY_STEP(ImpliesElim,  implies_elim,  impl, ant)

BIND_UNARY_STEP (NotIntro,  not_intro,  bottom)
BIND_BINARY_STEP(NotElim,   not_elim,   negation, formula)
BIND_BINARY_STEP(BottomElim,bottom_elim,bottom,   target_formula)

BIND_BINARY_STEP(IffIntro,  iff_intro,  ab, ba)
BIND_BINARY_STEP(IffElimL,  iff_elim_l, iff, a)
BIND_BINARY_STEP(IffElimR,  iff_elim_r, iff, b)

BIND_UNARY_STEP (ForallIntro, forall_intro, body)

util::ResultStatus exec_op(Session& s, uint32_t idx, const ForallElim& op) {
    auto f = s.resolve_step(op.formula, "forall_elim"); if (!f.ok()) return f.error();
    auto t = s.resolve_term(op.term,    "forall_elim"); if (!t.ok()) return t.error();
    auto r = s.stack.forall_elim(f.value(), t.value());
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const ExistsIntro& op) {
    auto body = s.resolve_step(op.body, "exists_intro"); if (!body.ok()) return body.error();
    std::optional<Term> w;
    if (op.witness.has_value()) {
        auto t = s.resolve_term(op.witness.value(), "exists_intro"); if (!t.ok()) return t.error();
        w = t.value();
    }
    auto r = s.stack.exists_intro(body.value(), w);
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const ExistsElim& op) {
    auto f = s.resolve_step(op.formula, "exists_elim"); if (!f.ok()) return f.error();
    auto r = s.stack.exists_elim(f.value());
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    if (op.bind_witness.has_value()) {
        auto witness_opt = s.stack.last_witness_var();
        if (!witness_opt.has_value()) {
            return MAKE_ERROR << "exists_elim: stack did not produce a witness term";
        }
        s.bind_term(idx, witness_opt.value());
        s.name_table[op.bind_witness->name] = witness_opt.value();
    }
    return util::Ok();
}

BIND_BINARY_STEP(EqSubst, eq_subst, eq_formula, target)
BIND_UNARY_STEP (EqSym,   eq_sym,   eq_formula)

BIND_UNARY_STEP (DoubleNegElim,   double_neg_elim,   of)
BIND_UNARY_STEP (ExcludedMiddle,  excluded_middle,   formula_let)
BIND_UNARY_STEP (ClassicalAbsurd, classical_absurd,  bottom)
BIND_BINARY_STEP(Peirce,          peirce,            a_let, b_let)

util::ResultStatus exec_op(Session& s, uint32_t idx, const IotaElim& op) {
    auto f = s.resolve_step(op.exists_formula, "iota_elim"); if (!f.ok()) return f.error();
    auto r = s.stack.iota_elim(f.value());
    if (!r.ok()) return r.error();
    s.bind_step(idx, r.value());
    if (op.bind_iota.has_value()) {
        auto iota_opt = s.stack.last_iota_term();
        if (!iota_opt.has_value()) {
            return MAKE_ERROR << "iota_elim: stack did not produce an iota term";
        }
        s.bind_term(idx, iota_opt.value());
        s.name_table[op.bind_iota->name] = iota_opt.value();
    }
    return util::Ok();
}

// Qed implements the success predicate Φ for ND:
//   (a) the named step is derived in the current proof state,
//   (b) its scope dependencies are fully discharged (deps_empty),
//   (c) its formula is structurally equal to the goal_formula
//       (= alpha-equivalent under De Bruijn).
util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Qed& op) {
    auto d = s.resolve_step(op.derived, "qed"); if (!d.ok()) return d.error();
    FormulaHandle derived = d.value();
    if (!s.stack.is_derived(derived)) {
        return MAKE_ERROR << "qed: formula not derived: " << derived.get();
    }
    if (!s.stack.deps_empty(derived)) {
        return MAKE_ERROR << "qed: formula has unresolved scope dependencies";
    }
    if (s.goal_formula.valid() && derived != s.goal_formula) {
        return MAKE_ERROR << "qed: derived formula doesn't match goal\n"
                          << "  Expected: " << s.goal_formula.get().to_string() << "\n"
                          << "  Got:      " << derived.get().to_string();
    }
    s.completed = true;
    return util::Ok();
}

#undef BIND_BINARY_STEP
#undef BIND_UNARY_STEP

}  // namespace

util::ResultStatus NDVerifier::verify(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const Proof&   proof)
{
    last_used_.clear();

    if (proof.system != System::ND || !std::holds_alternative<NDProgram>(proof.body)) {
        return MAKE_ERROR << "NDVerifier: proof is not an ND program";
    }
    const NDProgram& prog = std::get<NDProgram>(proof.body);

    Session s(ctx, goal_formula, prog);

    // Schema parsing context: populated only when claim_name names a schema.
    if (auto schema = ctx.find_schema(prog.claim_name)) {
        for (size_t i = 0; i < schema->var_names.size(); ++i) {
            s.schema_var_map[schema->var_names[i]] = i;
            if (i < schema->var_arities.size())
                s.schema_arity_map[schema->var_names[i]] = schema->var_arities[i];
        }
    }

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        const auto& instr = prog.instrs[i];
        auto status = std::visit(
            [&](const auto& op) -> util::ResultStatus { return exec_op(s, i, op); },
            instr);
        if (!status.ok()) {
            return MAKE_ERROR << "instr %" << i << ": " << status.error().to_string();
        }
        if (s.completed) {
            last_used_ = std::move(s.used_names);
            return util::Ok();
        }
    }
    return MAKE_ERROR << "ND proof: missing qed";
}

}  // namespace logic::proof::nd
