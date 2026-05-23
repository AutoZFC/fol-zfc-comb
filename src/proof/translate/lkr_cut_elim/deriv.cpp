#include "src/proof/translate/lkr_cut_elim/deriv.h"

#include "src/proof/lkr/literal.h"

#include <algorithm>
#include <optional>
#include <type_traits>
#include <unordered_map>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

using Seq = std::vector<FormulaHandle>;

// Resolve a FormulaSource to NNF. Our pipeline only produces pre-resolved
// FormulaHandles (translators set them); deferred ASTs would need a parse
// scope we do not have here, so they are rejected.
util::Result<FormulaHandle> source_nnf(
    FormulaBuilder& b, const lkr::FormulaSource& src, const char* op) {
    if (auto* h = std::get_if<FormulaHandle>(&src)) {
        if (!h->valid()) return MAKE_ERROR << op << ": empty FormulaHandle";
        return b.to_nnf(*h);
    }
    return MAKE_ERROR << op << ": deferred-AST FormulaSource unsupported in cut-elim";
}

struct Builder {
    FormulaBuilder&            b;
    const Program<lkr::Instr>& prog;
    std::vector<std::optional<Term>> term_env;  // indexed by original op idx

    Builder(FormulaBuilder& fb, const Program<lkr::Instr>& p)
        : b(fb), prog(p), term_env(p.instrs.size()) {}

    util::Result<DerivPtr> sub(Seq cur, uint32_t& pos) {
        if (pos >= prog.instrs.size())
            return MAKE_ERROR << "build: stream ended mid-tree at " << pos;
        uint32_t idx = pos++;
        const lkr::Instr& instr = prog.instrs[idx];
        auto node = std::make_unique<Deriv>();
        node->conclusion = cur;

        if (auto* op = std::get_if<lkr::AxiomLit>(&instr)) {
            node->rule = RAx{op->lit_a, op->lit_b};
            return node;
        }
        if (auto* op = std::get_if<lkr::One>(&instr)) {
            node->rule = ROne{op->idx};
            return node;
        }
        if (auto* op = std::get_if<lkr::CloseByLemma>(&instr)) {
            node->rule = RLemma{op->target, op->source_name};
            return node;
        }
        if (auto* op = std::get_if<lkr::Exchange>(&instr)) {
            Seq ch = cur;
            if (op->i < ch.size() && op->j < ch.size())
                std::swap(ch[op->i], ch[op->j]);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = RExchange{op->i, op->j, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Weakening>(&instr)) {
            TRY_ASSIGN(f, source_nnf(b, op->formula, "weakening"));
            Seq ch = cur;
            ch.push_back(f);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = RWeaken{f, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Contraction>(&instr)) {
            Seq ch = cur;
            if (op->j < ch.size()) ch.erase(ch.begin() + op->j);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = RContract{op->i, op->j, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::And>(&instr)) {
            if (op->principal >= cur.size())
                return MAKE_ERROR << "build: And principal OOB";
            const Formula& f = cur[op->principal].get();
            if (!f.is_compound() || f.as_compound().op != Op::And)
                return MAKE_ERROR << "build: And principal not ∧";
            FormulaHandle phi = f.as_compound().left;
            FormulaHandle psi = f.as_compound().right;
            std::unordered_map<size_t, bool> in_left;
            for (size_t k : op->left_partition) in_left[k] = true;
            Seq lseq, rseq;
            for (size_t i = 0; i < cur.size(); ++i) {
                if (i == op->principal) continue;
                if (in_left.count(i)) lseq.push_back(cur[i]);
                else                  rseq.push_back(cur[i]);
            }
            lseq.push_back(phi);
            rseq.push_back(psi);
            TRY_ASSIGN(left,  sub(std::move(lseq), pos));
            TRY_ASSIGN(right, sub(std::move(rseq), pos));
            node->rule = RAnd{op->principal, op->left_partition,
                              std::move(left), std::move(right)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Or>(&instr)) {
            if (op->principal >= cur.size())
                return MAKE_ERROR << "build: Or principal OOB";
            const Formula& f = cur[op->principal].get();
            if (!f.is_compound() || f.as_compound().op != Op::Or)
                return MAKE_ERROR << "build: Or principal not ∨";
            Seq ch = cur;
            ch[op->principal] = f.as_compound().left;
            ch.push_back(f.as_compound().right);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = ROr{op->principal, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Forall>(&instr)) {
            if (op->principal >= cur.size())
                return MAKE_ERROR << "build: Forall principal OOB";
            const Formula& f = cur[op->principal].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Forall)
                return MAKE_ERROR << "build: Forall principal not ∀";
            Term eigen = Term::fixed(op->eigen);
            term_env[idx] = eigen;
            Seq ch = cur;
            ch[op->principal] =
                b.instantiate_quantifier_body(f.as_quantified().body, eigen);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = RForall{op->principal, op->eigen, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Exists>(&instr)) {
            if (op->principal >= cur.size())
                return MAKE_ERROR << "build: Exists principal OOB";
            const Formula& f = cur[op->principal].get();
            if (!f.is_quantified() || f.as_quantified().op != Op::Exists)
                return MAKE_ERROR << "build: Exists principal not ∃";
            if (op->witness.idx >= term_env.size() ||
                !term_env[op->witness.idx].has_value())
                return MAKE_ERROR << "build: Exists witness term unbound";
            Term t = *term_env[op->witness.idx];
            Seq ch = cur;
            ch[op->principal] =
                b.instantiate_quantifier_body(f.as_quantified().body, t);
            TRY_ASSIGN(child, sub(std::move(ch), pos));
            node->rule = RExists{op->principal, t, std::move(child)};
            return node;
        }
        if (auto* op = std::get_if<lkr::Cut>(&instr)) {
            TRY_ASSIGN(phi, source_nnf(b, op->cut_formula, "cut"));
            FormulaHandle neg = b.to_nnf(b.make_not(phi));
            Seq lseq = cur; lseq.push_back(phi);
            Seq rseq = cur; rseq.push_back(neg);
            TRY_ASSIGN(left,  sub(std::move(lseq), pos));
            TRY_ASSIGN(right, sub(std::move(rseq), pos));
            node->rule = RCut{phi, std::move(left), std::move(right)};
            return node;
        }
        return MAKE_ERROR << "build: unhandled op";
    }
};

// ----- emit -----

// GCC 13 emits a spurious -Wmaybe-uninitialized for the std::string inside
// the pushed lkr::Instr variant (the diagnostic points into libstdc++'s
// basic_string internals, not our code). The op is fully constructed before
// the push; this is a known compiler false positive, suppressed narrowly.
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

struct Emitter {
    std::vector<lkr::Instr>          out;
    std::unordered_map<var_index, uint32_t> eigen_at;  // eigenvar → emitted idx

    util::ResultStatus walk(const Deriv& d) {
        if (auto* r = std::get_if<RAx>(&d.rule)) {
            lkr::AxiomLit o; o.lit_a = r->a; o.lit_b = r->b;
            out.push_back(lkr::Instr(o));
            return util::Ok();
        }
        if (auto* r = std::get_if<ROne>(&d.rule)) {
            lkr::One o; o.idx = r->idx;
            out.push_back(lkr::Instr(o));
            return util::Ok();
        }
        if (auto* r = std::get_if<RLemma>(&d.rule)) {
            lkr::CloseByLemma o;
            o.target      = r->target;
            o.source_name = r->source_name;
            out.push_back(lkr::Instr(o));
            return util::Ok();
        }
        if (auto* r = std::get_if<RExchange>(&d.rule)) {
            lkr::Exchange o; o.i = r->i; o.j = r->j;
            out.push_back(lkr::Instr(o));
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RWeaken>(&d.rule)) {
            lkr::Weakening o; o.formula = r->added;
            out.push_back(lkr::Instr(o));
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RContract>(&d.rule)) {
            lkr::Contraction o; o.i = r->i; o.j = r->j;
            out.push_back(lkr::Instr(o));
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RAnd>(&d.rule)) {
            lkr::And o; o.principal = r->principal; o.left_partition = r->left_partition;
            out.push_back(lkr::Instr(o));
            TRY(walk(*r->left));
            return walk(*r->right);
        }
        if (auto* r = std::get_if<ROr>(&d.rule)) {
            lkr::Or o; o.principal = r->principal;
            out.push_back(lkr::Instr(o));
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RForall>(&d.rule)) {
            uint32_t idx = static_cast<uint32_t>(out.size());
            lkr::Forall o; o.principal = r->principal; o.eigen = r->eigen;
            out.push_back(lkr::Instr(o));
            eigen_at[r->eigen] = idx;
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RExists>(&d.rule)) {
            if (!r->witness.is_fixed())
                return MAKE_ERROR << "emit: Exists witness is not a fixed var";
            auto it = eigen_at.find(r->witness.as_variable());
            if (it == eigen_at.end())
                return MAKE_ERROR << "emit: Exists witness eigenvar not introduced by an in-scope Forall";
            lkr::Exists o; o.principal = r->principal; o.witness = TermRef{it->second};
            out.push_back(lkr::Instr(o));
            return walk(*r->child);
        }
        if (auto* r = std::get_if<RCut>(&d.rule)) {
            lkr::Cut o; o.cut_formula = r->cut_formula;
            out.push_back(lkr::Instr(o));
            TRY(walk(*r->left));
            return walk(*r->right);
        }
        return MAKE_ERROR << "emit: unhandled rule";
    }
};

#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

}  // namespace

util::Result<DerivPtr> build(
    FormulaBuilder&            builder,
    FormulaHandle              goal_nnf,
    const Program<lkr::Instr>& prog) {
    if (prog.instrs.empty()) return MAKE_ERROR << "build: empty program";
    Builder bld(builder, prog);
    uint32_t pos = 0;
    TRY_ASSIGN(root, bld.sub(Seq{goal_nnf}, pos));
    if (pos != prog.instrs.size())
        return MAKE_ERROR << "build: " << (prog.instrs.size() - pos)
                          << " op(s) unconsumed";
    return root;
}

util::Result<Program<lkr::Instr>> emit(const Deriv& root) {
    Emitter e;
    TRY(e.walk(root));
    Program<lkr::Instr> prog;
    prog.instrs = std::move(e.out);
    return prog;
}

}  // namespace logic::proof::translate::lkr_cut_elim
