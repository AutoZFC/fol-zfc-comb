#include "verifier.h"

#include "literal.h"
#include "ops.h"
#include "sequent.h"

#include "../../core/formula.h"
#include "../../core/scope_utils.h"
#include "../../parser/parser.h"
#include "../../util/error.h"

#include <algorithm>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

namespace logic::proof::lkr {

namespace {

// Per-verify private state.
struct Session {
    GlobalContext&        ctx;
    FormulaBuilder        builder;
    const LKRProgram&     prog;
    FormulaHandle         goal_formula;

    std::vector<SequentRecord> open_goals;

    // SSA term env: TermRef.idx -> Term (set by Forall and Exists ops
    // when they introduce eigenvars; Exists's witness is a TermRef into
    // this env, so eigenvariables introduced earlier can be witnesses
    // for ∃ later — provided the eigenvar is in scope).
    std::vector<Term>     term_env;
    std::vector<uint8_t>  term_present;

    // Source-level scope-name -> Term, for deferred AST resolution
    // (Cut and Weakening formula sources). Empty by default; populated
    // when ND-style scope names appear in the program (rare for LKR).
    std::unordered_map<std::string, Term> name_table;

    // Track introducing-instr's index for each fixed-var, for diagnostic
    // messages. Not used for soundness (freshness check inspects all
    // entries directly).
    std::unordered_map<var_index, uint32_t> var_intro_at;

    std::unordered_set<std::string> used_names;

    Session(GlobalContext& c, FormulaHandle g, const LKRProgram& p)
        : ctx(c), builder(c), prog(p), goal_formula(g),
          term_env(p.instrs.size()),
          term_present(p.instrs.size(), 0) {}

    void bind_term(uint32_t idx, Term t) {
        term_env[idx] = t;
        term_present[idx] = 1;
        if (t.is_fixed()) var_intro_at[t.as_variable()] = idx;
    }

    util::Result<Term> resolve_term(TermRef r, const char* op) const {
        if (r.idx >= term_env.size() || !term_present[r.idx]) {
            return MAKE_ERROR << op << ": term %" << r.idx << " not bound";
        }
        return term_env[r.idx];
    }

    SequentRecord& top() { return open_goals.back(); }
    const SequentRecord& top() const { return open_goals.back(); }

    void replace_top(SequentRecord s) {
        open_goals.pop_back();
        open_goals.push_back(std::move(s));
    }
};

util::ResultStatus require_top(Session& s, const char* op) {
    if (s.open_goals.empty()) {
        return MAKE_ERROR << op << ": no open goal";
    }
    return util::Ok();
}

util::ResultStatus require_idx(const SequentRecord& g, size_t i, const char* op) {
    if (i >= g.entries.size()) {
        return MAKE_ERROR << op << ": entry index " << i
                          << " out of range (size " << g.entries.size() << ")";
    }
    return util::Ok();
}

// Resolve a FormulaSource (AST → parse, or FormulaHandle → use directly).
// Returns the formula in NNF.
util::Result<FormulaHandle> resolve_source_nnf(Session& s, const FormulaSource& src,
                                                const char* op) {
    FormulaHandle raw{};
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        if (!h->valid()) return MAKE_ERROR << op << ": empty FormulaHandle";
        raw = *h;
    } else {
        const auto& ast = std::get<std::shared_ptr<ASTNode>>(src);
        if (!ast) return MAKE_ERROR << op << ": missing formula AST";
        std::unordered_map<std::string, size_t> empty_sv, empty_ar;
        raw = parse_formula_with_vars(ast.get(), s.ctx, s.builder,
                                       s.name_table, empty_sv, empty_ar);
    }
    return s.builder.to_nnf(raw);
}

// =========================================================================
// Per-op execution
// =========================================================================

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const AxiomLit& op) {
    TRY(require_top(s, "axiom_lit"));
    auto& g = s.top();
    TRY(require_idx(g, op.lit_a, "axiom_lit"));
    TRY(require_idx(g, op.lit_b, "axiom_lit"));
    if (op.lit_a == op.lit_b) {
        return MAKE_ERROR << "axiom_lit: lit_a and lit_b must differ";
    }
    if (!is_atomic_literal(g.entries[op.lit_a]) ||
        !is_atomic_literal(g.entries[op.lit_b])) {
        return MAKE_ERROR << "axiom_lit: indices do not point to atomic literals";
    }
    if (!is_dual(g.entries[op.lit_a], g.entries[op.lit_b])) {
        return MAKE_ERROR << "axiom_lit: literals at " << op.lit_a
                          << " and " << op.lit_b << " are not duals";
    }
    s.open_goals.pop_back();
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const AxiomGen& op) {
    TRY(require_top(s, "axiom_gen"));
    auto& g = s.top();
    TRY(require_idx(g, op.a, "axiom_gen"));
    TRY(require_idx(g, op.b, "axiom_gen"));
    if (op.a == op.b) {
        return MAKE_ERROR << "axiom_gen: a and b must differ";
    }
    // NNF dual check: to_nnf(¬entries[a]) should equal entries[b].
    FormulaHandle neg_a = s.builder.make_not(g.entries[op.a]);
    FormulaHandle neg_a_nnf = s.builder.to_nnf(neg_a);
    if (neg_a_nnf != g.entries[op.b]) {
        return MAKE_ERROR << "axiom_gen: entries at " << op.a
                          << " and " << op.b << " are not NNF duals";
    }
    s.open_goals.pop_back();
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const One& op) {
    TRY(require_top(s, "one"));
    auto& g = s.top();
    TRY(require_idx(g, op.idx, "one"));
    if (!is_top_literal(g.entries[op.idx])) {
        return MAKE_ERROR << "one: entry " << op.idx
                          << " is not the top literal ¬⊥";
    }
    s.open_goals.pop_back();
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const UseTheorem& op) {
    TRY(require_top(s, "use_theorem"));
    auto found = s.ctx.find_known(op.axiom.name);
    if (!found.has_value()) {
        return MAKE_ERROR << "use_theorem: unknown axiom/theorem '"
                          << op.axiom.name << "'";
    }
    s.used_names.insert(op.axiom.name);
    FormulaHandle raw = found.value().get().root();
    FormulaHandle nnf = s.builder.to_nnf(raw);
    auto& g = s.top();
    bool found_match = false;
    for (const auto& e : g.entries) {
        if (e == nnf) { found_match = true; break; }
    }
    if (!found_match) {
        return MAKE_ERROR << "use_theorem: theorem '" << op.axiom.name
                          << "' (NNF) is not present in the current goal";
    }
    s.open_goals.pop_back();
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const SchemaInst& op) {
    TRY(require_top(s, "schema_inst"));
    auto schema = s.ctx.find_schema(op.data.schema.name);
    if (!schema.has_value()) {
        return MAKE_ERROR << "schema_inst: unknown schema '"
                          << op.data.schema.name << "'";
    }
    if (!s.ctx.is_schema_proven(op.data.schema.name)) {
        return MAKE_ERROR << "schema_inst: schema '" << op.data.schema.name
                          << "' not yet proven";
    }
    s.used_names.insert(op.data.schema.name);
    std::unordered_map<std::string, size_t> empty_sv, empty_ar;
    std::vector<SchemaBind> bindings(schema->var_names.size());
    std::vector<bool> bound(schema->var_names.size(), false);
    for (const auto& sb : op.data.bindings) {
        size_t idx = schema->var_names.size();
        for (size_t j = 0; j < schema->var_names.size(); ++j) {
            if (schema->var_names[j] == sb.var_name) { idx = j; break; }
        }
        if (idx >= schema->var_names.size())
            return MAKE_ERROR << "schema_inst: unknown schema variable '" << sb.var_name << "'";
        if (bound[idx])
            return MAKE_ERROR << "schema_inst: duplicate binding for '" << sb.var_name << "'";
        size_t arity = (idx < schema->var_arities.size()) ? schema->var_arities[idx] : 0;
        if (arity != 0) {
            return MAKE_ERROR << "schema_inst: arity-N schema bindings not supported in LKR";
        }
        FormulaHandle body = parse_formula_with_vars(
            sb.formula_ast.get(), s.ctx, s.builder, s.name_table, empty_sv, empty_ar);
        bindings[idx] = SchemaBind(body);
        bound[idx] = true;
    }
    for (size_t j = 0; j < bound.size(); ++j) {
        if (!bound[j])
            return MAKE_ERROR << "schema_inst: missing binding for '" << schema->var_names[j] << "'";
    }
    FormulaHandle inst_raw = s.builder.instantiate_schema(schema->body, bindings);
    FormulaHandle inst_nnf = s.builder.to_nnf(inst_raw);
    auto& g = s.top();
    bool found_match = false;
    for (const auto& e : g.entries) {
        if (e == inst_nnf) { found_match = true; break; }
    }
    if (!found_match) {
        return MAKE_ERROR << "schema_inst: instantiated formula (NNF) not present in the current goal";
    }
    s.open_goals.pop_back();
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Exchange& op) {
    TRY(require_top(s, "exchange"));
    auto& g = s.top();
    if (op.i == op.j) return util::Ok();
    TRY(require_idx(g, op.i, "exchange"));
    TRY(require_idx(g, op.j, "exchange"));
    SequentRecord ng = g;
    std::swap(ng.entries[op.i], ng.entries[op.j]);
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Weakening& op) {
    TRY(require_top(s, "weakening"));
    TRY_ASSIGN(f, resolve_source_nnf(s, op.formula, "weakening"));
    SequentRecord ng = s.top();
    ng.entries.push_back(f);
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Contraction& op) {
    TRY(require_top(s, "contraction"));
    auto& g = s.top();
    if (op.i == op.j) return MAKE_ERROR << "contraction: i and j must differ";
    TRY(require_idx(g, op.i, "contraction"));
    TRY(require_idx(g, op.j, "contraction"));
    if (g.entries[op.i] != g.entries[op.j]) {
        return MAKE_ERROR << "contraction: entries[" << op.i
                          << "] != entries[" << op.j << "]";
    }
    SequentRecord ng = g;
    ng.entries.erase(ng.entries.begin() + op.j);
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const And& op) {
    TRY(require_top(s, "and"));
    auto& g = s.top();
    TRY(require_idx(g, op.principal, "and"));
    const Formula& f = g.entries[op.principal].get();
    if (!f.is_compound() || f.as_compound().op != Op::And) {
        return MAKE_ERROR << "and: principal entry is not ϕ ∧ θ";
    }
    FormulaHandle phi = f.as_compound().left;
    FormulaHandle psi = f.as_compound().right;

    // Additive split: both subgoals retain the non-principal entries;
    // LEFT replaces principal with phi, RIGHT replaces with psi.
    SequentRecord left  = g;
    SequentRecord right = g;
    left.entries[op.principal]  = phi;
    right.entries[op.principal] = psi;

    s.open_goals.pop_back();
    s.open_goals.push_back(std::move(right));   // pushed first → deeper
    s.open_goals.push_back(std::move(left));    // pushed last → on top
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Or& op) {
    TRY(require_top(s, "or"));
    auto& g = s.top();
    TRY(require_idx(g, op.principal, "or"));
    const Formula& f = g.entries[op.principal].get();
    if (!f.is_compound() || f.as_compound().op != Op::Or) {
        return MAKE_ERROR << "or: principal entry is not ϕ ∨ θ";
    }
    FormulaHandle phi = f.as_compound().left;
    FormulaHandle psi = f.as_compound().right;
    SequentRecord ng = g;
    // Replace principal with phi, then append psi.
    ng.entries[op.principal] = phi;
    ng.entries.push_back(psi);
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t idx, const Forall& op) {
    TRY(require_top(s, "forall"));
    auto& g = s.top();
    TRY(require_idx(g, op.principal, "forall"));
    const Formula& f = g.entries[op.principal].get();
    if (!f.is_quantified() || f.as_quantified().op != Op::Forall) {
        return MAKE_ERROR << "forall: principal entry is not ∀x.ϕ";
    }
    var_index v = s.builder.enter_scope();
    Term eigen = Term::fixed(v);
    s.bind_term(idx, eigen);

    // Eigenvariable freshness: v must not occur free in any other entry.
    for (size_t k = 0; k < g.entries.size(); ++k) {
        if (k == op.principal) continue;
        if (formula_contains_fixed_var(g.entries[k], v)) {
            return MAKE_ERROR << "forall: eigenvariable f_" << v
                              << " is not fresh in entry[" << k << "]";
        }
    }

    FormulaHandle body = f.as_quantified().body;
    FormulaHandle inst = s.builder.instantiate_quantifier_body(body, eigen);
    SequentRecord ng = g;
    ng.entries[op.principal] = inst;
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Exists& op) {
    TRY(require_top(s, "exists"));
    auto& g = s.top();
    TRY(require_idx(g, op.principal, "exists"));
    const Formula& f = g.entries[op.principal].get();
    if (!f.is_quantified() || f.as_quantified().op != Op::Exists) {
        return MAKE_ERROR << "exists: principal entry is not ∃x.ϕ";
    }
    TRY_ASSIGN(t, s.resolve_term(op.witness, "exists"));
    FormulaHandle body = f.as_quantified().body;
    FormulaHandle inst = s.builder.instantiate_quantifier_body(body, t);
    SequentRecord ng = g;
    ng.entries[op.principal] = inst;
    s.replace_top(std::move(ng));
    return util::Ok();
}

util::ResultStatus exec_op(Session& s, uint32_t /*idx*/, const Cut& op) {
    TRY(require_top(s, "cut"));
    TRY_ASSIGN(phi, resolve_source_nnf(s, op.cut_formula, "cut"));
    FormulaHandle not_phi_raw = s.builder.make_not(phi);
    FormulaHandle not_phi_nnf = s.builder.to_nnf(not_phi_raw);

    // Additive cut: both subgoals retain the full Γ.
    SequentRecord left  = s.top();
    SequentRecord right = s.top();
    left.entries.push_back(phi);
    right.entries.push_back(not_phi_nnf);

    s.open_goals.pop_back();
    s.open_goals.push_back(std::move(right));   // deeper
    s.open_goals.push_back(std::move(left));    // on top
    return util::Ok();
}

}  // namespace

util::ResultStatus LKRVerifier::verify(
    GlobalContext& ctx,
    FormulaHandle  goal_formula,
    const Proof&   proof)
{
    last_used_.clear();

    if (proof.system != System::LKR || !std::holds_alternative<LKRProgram>(proof.body)) {
        return MAKE_ERROR << "LKRVerifier: proof is not an LKR program";
    }
    const LKRProgram& prog = std::get<LKRProgram>(proof.body);

    // Schema proofs are not supported by LKR: a schema body may contain
    // SchemaVar terms whose semantics are theory-level placeholders.
    if (goal_formula.get().has_schema_vars()) {
        return MAKE_ERROR
            << "LKRVerifier: schema proofs are not supported in LKR";
    }

    Session s(ctx, goal_formula, prog);

    // NNF the goal and seed the open-goals stack.
    FormulaHandle goal_nnf = s.builder.to_nnf(goal_formula);
    SequentRecord initial;
    initial.entries.push_back(goal_nnf);
    s.open_goals.push_back(std::move(initial));

    for (uint32_t i = 0; i < prog.instrs.size(); ++i) {
        const auto& instr = prog.instrs[i];
        auto status = std::visit(
            [&](const auto& op) -> util::ResultStatus { return exec_op(s, i, op); },
            instr);
        if (!status.ok()) {
            return MAKE_ERROR << "instr %" << i << ": " << status.error().to_string();
        }
    }

    if (!s.open_goals.empty()) {
        return MAKE_ERROR << "LKRVerifier: " << s.open_goals.size()
                          << " open goal(s) remain after program end";
    }

    last_used_ = std::move(s.used_names);
    return util::Ok();
}

}  // namespace logic::proof::lkr
