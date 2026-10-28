#include "identity.h"

#include "nnf_shapes.h"

#include <unordered_map>
#include <utility>
#include <vector>

namespace logic::proof::lkr_build {

size_t identity_eigens(FormulaHandle a) {
    std::unordered_map<FormulaHandle, size_t> count;
    std::vector<std::pair<FormulaHandle, bool>> stack{{a, false}};
    while (!stack.empty()) {
        auto [h, children_counted] = stack.back();
        stack.pop_back();
        if (count.count(h)) continue;
        const Formula& f = h.get();
        if (f.is_quantified()) {
            FormulaHandle body = f.as_quantified().body;
            if (!children_counted) {
                stack.push_back({h, true});
                stack.push_back({body, false});
                continue;
            }
            count[h] = 1 + count.at(body);
        } else if (has_op(h, Op::And) || has_op(h, Op::Or)) {
            const Compound& c = f.as_compound();
            if (!children_counted) {
                stack.push_back({h, true});
                stack.push_back({c.right, false});
                stack.push_back({c.left, false});
                continue;
            }
            count[h] = count.at(c.left) + count.at(c.right);
        } else {
            count[h] = 0;
        }
    }
    return count.at(a);
}

namespace {

struct Goal {
    Sequent seq;
    size_t  a;
    size_t  b;
};

}  // namespace

util::ResultStatus expand_identity(Sequent seq, size_t a, size_t b,
                                   var_index first_eigen,
                                   FormulaBuilder& builder, OpSink& sink)
{
    // An explicit stack keeps the call depth independent of formula depth.
    var_index next_eigen = first_eigen;
    std::vector<Goal> open;
    open.push_back(Goal{std::move(seq), a, b});
    while (!open.empty()) {
        Goal g = std::move(open.back());
        open.pop_back();
        Sequent& s = g.seq;
        if (g.a >= s.size() || g.b >= s.size() || g.a == g.b) {
            return MAKE_ERROR << "identity: bad positions (a=" << g.a
                              << ", b=" << g.b << ", size=" << s.size() << ")";
        }
        if (is_verum(s.at(g.a))) { TRY(s.one(g.a, sink)); continue; }
        if (is_verum(s.at(g.b))) { TRY(s.one(g.b, sink)); continue; }
        if (is_literal(s.at(g.a)) && is_literal(s.at(g.b))) {
            TRY(s.axiom_lit(g.a, g.b, sink));
            continue;
        }
        if (has_op(s.at(g.a), Op::And) || has_op(s.at(g.a), Op::Exists)) {
            std::swap(g.a, g.b);
        }
        if (has_op(s.at(g.a), Op::Or) && has_op(s.at(g.b), Op::And)) {
            const Compound& disj = s.at(g.a).get().as_compound();
            const Compound& conj = s.at(g.b).get().as_compound();
            bool straight = builder.to_nnf_neg(disj.left) == conj.left &&
                            builder.to_nnf_neg(disj.right) == conj.right;
            bool swapped  = builder.to_nnf_neg(disj.left) == conj.right &&
                            builder.to_nnf_neg(disj.right) == conj.left;
            if (!straight && !swapped) {
                return MAKE_ERROR << "identity: ∨/∧ children not dual "
                                     "under either alignment";
            }
            TRY_ASSIGN(psi, s.or_rule(g.a, sink));
            size_t with_beta1 = straight ? g.a : psi;
            size_t with_beta2 = straight ? psi : g.a;
            TRY_ASSIGN(split, std::move(s).and_rule(
                g.b, {with_beta1}, {with_beta2}, sink));
            open.push_back(Goal{std::move(split.right.seq),
                                *split.right.moved[with_beta2],
                                split.right.added});
            open.push_back(Goal{std::move(split.left.seq),
                                *split.left.moved[with_beta1],
                                split.left.added});
            continue;
        }
        if (has_op(s.at(g.a), Op::Forall) && has_op(s.at(g.b), Op::Exists)) {
            TRY_ASSIGN(eigen, s.forall_rule(g.a, next_eigen++, builder, sink));
            TRY(s.exists_rule(g.b, eigen, builder, sink));
            open.push_back(std::move(g));
            continue;
        }
        return MAKE_ERROR << "identity: entries " << g.a << " and " << g.b
                          << " are not NNF duals: " << s.at(g.a).get()
                          << " vs " << s.at(g.b).get();
    }
    return util::Ok();
}

}  // namespace logic::proof::lkr_build
