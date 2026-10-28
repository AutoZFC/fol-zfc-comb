#include "sequent_shadow.h"

#include "src/proof/lkr_build/identity.h"
#include "src/proof/lkr_build/nnf_shapes.h"

#include <utility>

namespace logic::proof::translate::nd_to_lkr {

void SequentShadow::bind_dual(HypId h, std::optional<size_t> pos,
                              DemandPath pending) {
    if (pos && lkr_build::is_falsum(seq_.at(*pos))) pos.reset();
    duals_[h] = DualSlot{pos, std::move(pending)};
}

const DualSlot* SequentShadow::dual(HypId h) const {
    auto it = duals_.find(h);
    return it == duals_.end() ? nullptr : &it->second;
}

bool SequentShadow::dual_shared(size_t pos, HypId h) const {
    for (const auto& [other, slot] : duals_) {
        if (!(other == h) && slot.pos == pos) return true;
    }
    return false;
}

util::ResultStatus SequentShadow::identity(size_t a, size_t b,
                                           FormulaBuilder& builder,
                                           OpSink& sink) && {
    if (a >= size()) {
        return MAKE_ERROR << "identity: entry " << a << " out of range (size "
                          << size() << ")";
    }
    var_index first_eigen = builder.depth();
    for (size_t n = lkr_build::identity_eigens(at(a)); n > 0; --n) {
        builder.enter_scope();
    }
    return std::move(seq_).identity(a, b, first_eigen, builder, sink);
}

util::Result<Split> SequentShadow::and_rule(
    size_t principal,
    const std::vector<size_t>& left_needs,
    const std::vector<size_t>& right_needs,
    OpSink& sink) &&
{
    TRY_ASSIGN(split, std::move(seq_).and_rule(principal, left_needs,
                                               right_needs, sink));
    return std::move(*this).distribute(std::move(split));
}

Split SequentShadow::cut_rule(FormulaHandle formula_nnf,
                              FormulaBuilder& builder, OpSink& sink) && {
    lkr_build::Split split =
        std::move(seq_).cut_rule(formula_nnf, builder, sink);
    return std::move(*this).distribute(std::move(split));
}

Split SequentShadow::distribute(lkr_build::Split split) && {
    Split out{Premise{SequentShadow(std::move(split.left.seq)),
                      std::move(split.left.moved), split.left.added},
              Premise{SequentShadow(std::move(split.right.seq)),
                      std::move(split.right.moved), split.right.added}};
    for (auto& [h, slot] : duals_) {
        if (!slot.pos) {
            out.left.shadow.duals_[h]  = slot;
            out.right.shadow.duals_[h] = slot;
            continue;
        }
        if (auto l = out.left.moved[*slot.pos]) {
            out.left.shadow.duals_[h] = DualSlot{*l, slot.pending};
        }
        if (auto r = out.right.moved[*slot.pos]) {
            out.right.shadow.duals_[h] = DualSlot{*r, slot.pending};
        }
    }
    out.left.shadow.terms_  = terms_;
    out.right.shadow.terms_ = std::move(terms_);
    return out;
}

}  // namespace logic::proof::translate::nd_to_lkr
