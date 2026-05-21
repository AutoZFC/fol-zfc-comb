#include "src/proof/ks1/equiv.h"

#include <algorithm>
#include <vector>

namespace logic::proof::ks1 {

namespace {

// Collect the operands of a maximal `op`-chain rooted at `h`, canonicalizing
// each operand (a subformula whose root op is NOT `op`). This flattens
// associativity: ((A op B) op C) and (A op (B op C)) yield the same operand
// list [Â, B̂, Ĉ].
void collect_operands(FormulaBuilder& fb, FormulaHandle h, Op op,
                      std::vector<FormulaHandle>& out) {
    const Formula& f = h.get();
    if (f.is_compound() && f.as_compound().op == op) {
        collect_operands(fb, f.as_compound().left, op, out);
        collect_operands(fb, f.as_compound().right, op, out);
    } else {
        out.push_back(canonicalize(fb, h));
    }
}

}  // namespace

FormulaHandle canonicalize(FormulaBuilder& fb, FormulaHandle h) {
    const Formula& f = h.get();

    if (f.is_compound()) {
        Op op = f.as_compound().op;
        if (op == Op::And || op == Op::Or) {
            // Flatten associatively, canonicalize operands, then sort by a
            // stable total order (commutativity), then rebuild right-leaning.
            std::vector<FormulaHandle> operands;
            collect_operands(fb, h, op, operands);

            std::sort(operands.begin(), operands.end(),
                      [](FormulaHandle a, FormulaHandle b) {
                          return a.get().to_string() < b.get().to_string();
                      });

            FormulaHandle acc = operands.back();
            for (size_t i = operands.size() - 1; i-- > 0;) {
                acc = (op == Op::And) ? fb.make_and(operands[i], acc)
                                      : fb.make_or(operands[i], acc);
            }
            return acc;
        }
        // Not / Bottom: an NNF literal or unit — already canonical.
        return h;
    }

    if (f.is_quantified()) {
        // Canonicalize under the binder (quantifier-shift equations of eq (2)
        // are not yet applied — see equiv.h scope note).
        const Quantified& q = f.as_quantified();
        return fb.make_quantified(q.op, canonicalize(fb, q.body));
    }

    // PredicateInstance / SchemaVar / SentenceHandle: leaves.
    return h;
}

bool equiv(FormulaBuilder& fb, FormulaHandle a, FormulaHandle b) {
    return canonicalize(fb, a) == canonicalize(fb, b);
}

}  // namespace logic::proof::ks1
