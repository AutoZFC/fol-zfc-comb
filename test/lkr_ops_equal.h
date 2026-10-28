#pragma once

// Op-for-op equality of LKR programs, the equality of
// COMPACT_LKR_DESIGN.md Theorem E1. OpHeader locations and
// CloseByLemma::source_name are diagnostics and do not take part.

#include "src/proof/lkr/ops.h"

#include <string>
#include <variant>
#include <vector>

namespace lkr_ops_equal {

using namespace logic::proof;

inline bool same_bindings(const std::vector<logic::SchemaBinding>& a,
                          const std::vector<logic::SchemaBinding>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].var_name != b[i].var_name ||
            a[i].formula_ast != b[i].formula_ast ||
            a[i].lambda_params != b[i].lambda_params) {
            return false;
        }
    }
    return true;
}

inline bool same_op(const lkr::Instr& x, const lkr::Instr& y) {
    if (x.index() != y.index()) return false;
    return std::visit([&](const auto& a) -> bool {
        using T = std::decay_t<decltype(a)>;
        const T& b = std::get<T>(y);
        if constexpr (std::is_same_v<T, lkr::AxiomLit>) {
            return a.lit_a == b.lit_a && a.lit_b == b.lit_b;
        } else if constexpr (std::is_same_v<T, lkr::One>) {
            return a.idx == b.idx;
        } else if constexpr (std::is_same_v<T, lkr::CloseByLemma>) {
            if (a.target.index() != b.target.index()) return false;
            if (const auto* ra = std::get_if<AxiomRef>(&a.target)) {
                return *ra == std::get<AxiomRef>(b.target);
            }
            const auto& sa = std::get<SchemaInstData>(a.target);
            const auto& sb = std::get<SchemaInstData>(b.target);
            return sa.schema == sb.schema &&
                   same_bindings(sa.bindings, sb.bindings);
        } else if constexpr (std::is_same_v<T, lkr::Exchange> ||
                             std::is_same_v<T, lkr::Contraction>) {
            return a.i == b.i && a.j == b.j;
        } else if constexpr (std::is_same_v<T, lkr::Weakening>) {
            return a.idx == b.idx;
        } else if constexpr (std::is_same_v<T, lkr::Duplicate>) {
            return a.src == b.src;
        } else if constexpr (std::is_same_v<T, lkr::And>) {
            return a.principal == b.principal &&
                   a.left_partition == b.left_partition;
        } else if constexpr (std::is_same_v<T, lkr::Or>) {
            return a.principal == b.principal;
        } else if constexpr (std::is_same_v<T, lkr::Forall>) {
            return a.principal == b.principal && a.eigen == b.eigen;
        } else if constexpr (std::is_same_v<T, lkr::Exists>) {
            return a.principal == b.principal && a.witness == b.witness;
        } else {
            static_assert(std::is_same_v<T, lkr::Cut>);
            return a.cut_formula == b.cut_formula;
        }
    }, x);
}

// Empty when equal; otherwise where the programs first differ.
inline std::string first_difference(const std::vector<lkr::Instr>& a,
                                    const std::vector<lkr::Instr>& b) {
    size_t n = a.size() < b.size() ? a.size() : b.size();
    for (size_t i = 0; i < n; ++i) {
        if (!same_op(a[i], b[i])) {
            return "op %" + std::to_string(i) + " differs (kinds " +
                   std::to_string(a[i].index()) + " and " +
                   std::to_string(b[i].index()) + ")";
        }
    }
    if (a.size() != b.size()) {
        return "lengths differ: " + std::to_string(a.size()) + " and " +
               std::to_string(b.size());
    }
    return "";
}

}  // namespace lkr_ops_equal
