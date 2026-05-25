#include "src/proof/translate/lkr_cut_elim/reduce.h"

#include "src/proof/translate/lkr_cut_elim/validate.h"

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

DerivPtr clone(const Deriv& d) {
    auto n = std::make_unique<Deriv>();
    n->conclusion = d.conclusion;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAx> ||
                      std::is_same_v<T, ROne> ||
                      std::is_same_v<T, RLemma>) {
            n->rule = r;
        } else if constexpr (std::is_same_v<T, RExchange>) {
            n->rule = RExchange{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RWeaken>) {
            n->rule = RWeaken{r.added, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RContract>) {
            n->rule = RContract{r.i, r.j, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n->rule = RAnd{r.principal, r.left_partition,
                           clone(*r.left), clone(*r.right)};
        } else if constexpr (std::is_same_v<T, ROr>) {
            n->rule = ROr{r.principal, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RForall>) {
            n->rule = RForall{r.principal, r.eigen, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RExists>) {
            n->rule = RExists{r.principal, r.witness, clone(*r.child)};
        } else if constexpr (std::is_same_v<T, RCut>) {
            n->rule = RCut{r.cut_formula, clone(*r.left), clone(*r.right)};
        }
    }, d.rule);
    return n;
}

// --- find max degree across all cuts; track whether any cut exists ---
void scan_cuts(const Deriv& d, std::size_t& max_deg, bool& any) {
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            any = true;
            std::size_t dg = degree(r.cut_formula);
            if (dg > max_deg) max_deg = dg;
            scan_cuts(*r.left, max_deg, any);
            scan_cuts(*r.right, max_deg, any);
        } else if constexpr (std::is_same_v<T, RAnd>) {
            scan_cuts(*r.left, max_deg, any);
            scan_cuts(*r.right, max_deg, any);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            scan_cuts(*r.child, max_deg, any);
        }
    }, d.rule);
}

// --- DFS for a max-degree RCut, stopping at the first one (= topmost) ---
bool find_topmost(const Deriv& d, std::size_t target_deg,
                  CutPath& path_so_far, CutPath& result) {
    return std::visit([&](auto&& r) -> bool {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            if (degree(r.cut_formula) == target_deg) {
                result = path_so_far;
                return true;  // topmost — don't descend further.
            }
            path_so_far.push_back(0);
            if (find_topmost(*r.left,  target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            path_so_far.push_back(1);
            if (find_topmost(*r.right, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        } else if constexpr (std::is_same_v<T, RAnd>) {
            path_so_far.push_back(0);
            if (find_topmost(*r.left,  target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            path_so_far.push_back(1);
            if (find_topmost(*r.right, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            path_so_far.push_back(0);
            if (find_topmost(*r.child, target_deg, path_so_far, result)) return true;
            path_so_far.pop_back();
            return false;
        }
        return false;
    }, d.rule);
}

// --- Read the subtree at a path (no ownership transfer). ---
const Deriv* at_path(const Deriv& tree, const CutPath& path) {
    const Deriv* cur = &tree;
    for (int step : path) {
        const Deriv* next = nullptr;
        std::visit([&](auto&& r) {
            using T = std::decay_t<decltype(r)>;
            if constexpr (std::is_same_v<T, RAnd> || std::is_same_v<T, RCut>) {
                next = (step == 0) ? r.left.get() : r.right.get();
            } else if constexpr (std::is_same_v<T, RExchange> ||
                                 std::is_same_v<T, RWeaken>   ||
                                 std::is_same_v<T, RContract> ||
                                 std::is_same_v<T, ROr>       ||
                                 std::is_same_v<T, RForall>   ||
                                 std::is_same_v<T, RExists>) {
                next = r.child.get();
            }
        }, cur->rule);
        if (!next) return nullptr;
        cur = next;
    }
    return cur;
}

// --- Substitute a new subtree at the given path; returns a fresh tree. ---
util::Result<DerivPtr> substitute_at(const Deriv& tree, const CutPath& path,
                                      DerivPtr new_subtree,
                                      std::size_t depth = 0) {
    if (depth == path.size())
        return util::Result<DerivPtr>(std::move(new_subtree));

    int step = path[depth];
    auto n = std::make_unique<Deriv>();
    n->conclusion = tree.conclusion;

    return std::visit([&](auto&& r) -> util::Result<DerivPtr> {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RAnd>) {
            if (step == 0) {
                TRY_ASSIGN(nl, substitute_at(*r.left, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RAnd{r.principal, r.left_partition,
                               std::move(nl), clone(*r.right)};
            } else {
                TRY_ASSIGN(nr, substitute_at(*r.right, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RAnd{r.principal, r.left_partition,
                               clone(*r.left), std::move(nr)};
            }
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RCut>) {
            if (step == 0) {
                TRY_ASSIGN(nl, substitute_at(*r.left, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RCut{r.cut_formula, std::move(nl), clone(*r.right)};
            } else {
                TRY_ASSIGN(nr, substitute_at(*r.right, path,
                                             std::move(new_subtree), depth + 1));
                n->rule = RCut{r.cut_formula, clone(*r.left), std::move(nr)};
            }
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExchange>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RExchange{r.i, r.j, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RWeaken>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RWeaken{r.added, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RContract>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RContract{r.i, r.j, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, ROr>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = ROr{r.principal, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RForall>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RForall{r.principal, r.eigen, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else if constexpr (std::is_same_v<T, RExists>) {
            TRY_ASSIGN(nc, substitute_at(*r.child, path,
                                         std::move(new_subtree), depth + 1));
            n->rule = RExists{r.principal, r.witness, std::move(nc)};
            return util::Result<DerivPtr>(std::move(n));
        }
        else {
            return MAKE_ERROR << "substitute_at: cannot descend into leaf rule at path";
        }
    }, tree.rule);
}

// --- §5 case dispatch — Step 3 scaffold (all stubs). ---
//
// Given a multiplicative RCut, dispatch by (left.rule, right.rule) per
// the §5 case analysis. Each case is filled in during Step 4. Until
// then, every dispatch returns "not implemented" and the driver gives
// up on this cut (and any below it that would have been unlocked).
util::Result<DerivPtr> dispatch_cut(FormulaBuilder& /*builder*/,
                                     const Deriv& /*cut_node*/,
                                     const RCut& /*cut*/) {
    return MAKE_ERROR << "dispatch_cut: §5 case not yet implemented (Step 4)";
}

}  // namespace

std::size_t degree(FormulaHandle f) {
    if (!f.valid()) return 0;
    const Formula& formula = f.get();
    if (formula.is_predicate() || formula.is_schema_var()) return 0;
    if (formula.is_sentence()) return degree(formula.as_sentence().get().root());
    if (formula.is_compound()) {
        const auto& c = formula.as_compound();
        if (c.op == Op::Bottom) return 0;
        if (c.op == Op::Not) return 1 + degree(c.left);
        // And, Or, Implies, Iff: binary.
        return 1 + std::max(degree(c.left), degree(c.right));
    }
    if (formula.is_quantified()) {
        return 1 + degree(formula.as_quantified().body);
    }
    return 0;
}

std::optional<CutCandidate> find_topmost_max_deg_cut(const Deriv& root) {
    std::size_t max_deg = 0;
    bool any = false;
    scan_cuts(root, max_deg, any);
    if (!any) return std::nullopt;
    CutPath path, result;
    if (!find_topmost(root, max_deg, path, result)) return std::nullopt;
    return CutCandidate{std::move(result), max_deg};
}

util::Result<DerivPtr> eliminate_cuts(FormulaBuilder& builder, const Deriv& root) {
    TRY(validate(root));
    DerivPtr current = clone(root);

    // Worklist loop: find topmost max-degree cut, attempt dispatch,
    // replace on success, give up on stub failure.
    while (true) {
        auto cand = find_topmost_max_deg_cut(*current);
        if (!cand) break;  // no cuts remain.

        const Deriv* cut_node = at_path(*current, cand->path);
        if (!cut_node)
            return MAKE_ERROR << "eliminate_cuts: lost cut node at path";
        const auto* cut = std::get_if<RCut>(&cut_node->rule);
        if (!cut)
            return MAKE_ERROR << "eliminate_cuts: at_path returned non-cut";

        auto reduced = dispatch_cut(builder, *cut_node, *cut);
        if (!reduced.ok()) {
            // Step 3 scaffold: all cases are stubs. Give up.
            break;
        }

        TRY_ASSIGN(new_tree, substitute_at(*current, cand->path,
                                            std::move(reduced).unwrap()));
        current = std::move(new_tree);
        TRY(validate(*current));
    }

    return util::Result<DerivPtr>(std::move(current));
}

}  // namespace logic::proof::translate::lkr_cut_elim
