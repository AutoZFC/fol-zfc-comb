// Fograph(FormulaHandle) — paper Def. 3.1.
//
// Recursive walk over an NNF formula assembling G(φ):
//   * one Atom vertex per atom occurrence (negated or not),
//   * one Binder vertex per quantifier occurrence,
//   * cograph_edges added by × (from ∧ and from ∃-binders),
//   * binding_edges added in a post-pass (binder → atom-it-binds).
//
// Vertex IDs come out in formula pre-order: each vertex gets the next
// available index at allocation time. The Phase-1 comparison treats
// this layout as canonical — any translator emitting a target fograph
// must follow the same ordering.
//
// Term rewriting: de Bruijn Gen indices in atom args are translated to
// flat Fixed var_indices via the live binder stack. Gen(k) refers to
// the k-th nearest enclosing binder, so Gen(k) ↦ Fixed(stack[size-1-k]).
//
// PRECONDITION: the input formula is description-free. Descriptions
// must be eliminated by the translator (see
// translate/ELIMINATE_DESCRIPTIONS.md) before being passed here.
// CombVerifier::verify enforces this at the boundary; this builder
// asserts it for defense in depth.

#include "src/proof/comb/comb_proof.h"
#include "src/core/formula.h"

#include <cassert>
#include <utility>
#include <vector>

namespace logic::proof::comb {

namespace {

// Translate a single Term: Gen → Fixed via binder stack; Fixed unchanged.
Term rewrite_term(const Term& t, const std::vector<var_index>& stack) {
    if (t.is_generalized()) {
        var_index k = t.as_variable();
        assert(k < stack.size() && "free variable in goal formula");
        return Term::fixed(stack[stack.size() - 1 - k]);
    }
    assert(!t.is_description() &&
           "Fograph builder: description in atom args; eliminate first");
    return t;
}

std::vector<Term> rewrite_args(const std::vector<Term>& args,
                               const std::vector<var_index>& stack) {
    std::vector<Term> out;
    out.reserve(args.size());
    for (const auto& t : args) out.push_back(rewrite_term(t, stack));
    return out;
}

// Push an Atom-labelled vertex; return its id.
size_t push_atom(const PredicateInstance& p,
                 bool negated,
                 const std::vector<var_index>& stack,
                 Fograph& out) {
    size_t id = out.labels.size();
    VertexLabel lbl;
    lbl.kind    = VertexKind::Atom;
    lbl.pred    = p.predicate();
    lbl.negated = negated;
    lbl.args    = rewrite_args(p.args(), stack);
    out.labels.push_back(std::move(lbl));
    return id;
}

// Recursive build. Returns the vertex-id list allocated for this
// subformula, in pre-order. Mutates `out.labels` and `out.cograph_edges`.
// Binding edges are added in a separate post-pass.
std::vector<size_t> build(FormulaHandle           f,
                          std::vector<var_index>& binder_stack,
                          var_index&              next_binder_var,
                          Fograph&                out) {
    const Formula& formula = f.get();

    if (formula.is_predicate()) {
        size_t id = push_atom(formula.as_predicate(), /*negated=*/false,
                              binder_stack, out);
        return {id};
    }

    if (formula.is_compound()) {
        const Compound& c = formula.as_compound();

        if (c.op == Op::Not) {
            assert(c.left->is_predicate() && "Fograph builder: input not in NNF");
            size_t id = push_atom(c.left->as_predicate(), /*negated=*/true,
                                  binder_stack, out);
            return {id};
        }

        if (c.op == Op::And || c.op == Op::Or) {
            auto left_ids  = build(c.left,  binder_stack, next_binder_var, out);
            auto right_ids = build(c.right, binder_stack, next_binder_var, out);

            if (c.op == Op::And) {
                for (size_t l : left_ids) {
                    for (size_t r : right_ids) {
                        out.cograph_edges.push_back({l, r});
                    }
                }
            }
            left_ids.insert(left_ids.end(), right_ids.begin(), right_ids.end());
            return left_ids;
        }

        assert(false && "Fograph builder: non-NNF or unsupported compound");
        return {};
    }

    if (formula.is_quantified()) {
        const Quantified& q   = formula.as_quantified();
        const bool is_exists  = (q.op == Op::Exists);

        var_index v         = next_binder_var++;
        size_t    binder_id = out.labels.size();

        VertexLabel lbl;
        lbl.kind           = VertexKind::Binder;
        lbl.var            = v;
        lbl.is_existential = is_exists;
        out.labels.push_back(std::move(lbl));

        binder_stack.push_back(v);
        auto body_ids = build(q.body, binder_stack, next_binder_var, out);
        binder_stack.pop_back();

        if (is_exists) {
            for (size_t b : body_ids) {
                out.cograph_edges.push_back({binder_id, b});
            }
        }
        body_ids.insert(body_ids.begin(), binder_id);
        return body_ids;
    }

    assert(false && "Fograph builder: unexpected formula kind");
    return {};
}

// True iff `t` references the binder var `v`. Trivial without
// descriptions: Fixed leaves are the only place binder refs appear.
bool term_references_var(const Term& t, var_index v) {
    return t.is_fixed() && t.as_variable() == v;
}

void add_binding_edges(Fograph& out) {
    for (size_t b_id = 0; b_id < out.labels.size(); ++b_id) {
        const VertexLabel& b = out.labels[b_id];
        if (b.kind != VertexKind::Binder) continue;
        for (size_t a_id = 0; a_id < out.labels.size(); ++a_id) {
            const VertexLabel& a = out.labels[a_id];
            if (a.kind != VertexKind::Atom) continue;
            for (const Term& arg : a.args) {
                if (term_references_var(arg, b.var)) {
                    out.binding_edges.push_back({b_id, a_id});
                    break;
                }
            }
        }
    }
}

}  // namespace

Fograph::Fograph(FormulaHandle const& formula)
    : source_formula{formula}
{
    std::vector<var_index> binder_stack;
    var_index              next_binder_var = 0;
    (void)build(formula, binder_stack, next_binder_var, *this);
    add_binding_edges(*this);
}

}  // namespace logic::proof::comb
