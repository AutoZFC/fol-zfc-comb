#include "src/proof/translate/lkr_cut_elim/validate.h"

#include "src/core/formula.h"

#include <string>
#include <type_traits>
#include <vector>

namespace logic::proof::translate::lkr_cut_elim {

namespace {

using Seq = std::vector<FormulaHandle>;

struct Validator {
    util::ResultStatus walk(const Deriv& d, const std::string& path) {
        return std::visit([&](auto&& r) -> util::ResultStatus {
            using T = std::decay_t<decltype(r)>;
            const Seq& concl = d.conclusion;

            if constexpr (std::is_same_v<T, RAx>) {
                if (r.a >= concl.size() || r.b >= concl.size())
                    return MAKE_ERROR << path << ": RAx position OOB (a=" << r.a
                                      << ", b=" << r.b << ", |Γ|=" << concl.size() << ")";
                if (r.a == r.b)
                    return MAKE_ERROR << path << ": RAx requires distinct positions (a=b=" << r.a << ")";
                return util::Ok();
            }
            else if constexpr (std::is_same_v<T, ROne>) {
                if (r.idx >= concl.size())
                    return MAKE_ERROR << path << ": ROne idx OOB (idx=" << r.idx
                                      << ", |Γ|=" << concl.size() << ")";
                return util::Ok();
            }
            else if constexpr (std::is_same_v<T, RLemma>) {
                if (concl.empty())
                    return MAKE_ERROR << path << ": RLemma on empty Γ";
                return util::Ok();
            }
            else if constexpr (std::is_same_v<T, RExchange>) {
                if (r.i >= concl.size() || r.j >= concl.size())
                    return MAKE_ERROR << path << ": RExchange position OOB (i=" << r.i
                                      << ", j=" << r.j << ", |Γ|=" << concl.size() << ")";
                if (!r.child)
                    return MAKE_ERROR << path << ": RExchange has null child";
                const Seq& cc = r.child->conclusion;
                if (cc.size() != concl.size())
                    return MAKE_ERROR << path << ": RExchange child size " << cc.size()
                                      << " != node size " << concl.size();
                for (size_t k = 0; k < concl.size(); ++k) {
                    FormulaHandle expected =
                        (k == r.i) ? concl[r.j]
                      : (k == r.j) ? concl[r.i]
                                   : concl[k];
                    if (cc[k] != expected)
                        return MAKE_ERROR << path << ": RExchange child[" << k
                                          << "] != expected";
                }
                return walk(*r.child, path + ".X");
            }
            else if constexpr (std::is_same_v<T, RWeaken>) {
                // Goal-directed W: child = node with position `idx` removed
                // (child SMALLER). This is the canary against the 05-27
                // reversed-W bug — see WEAKENING_FIX_DESIGN.md.
                if (r.idx >= concl.size())
                    return MAKE_ERROR << path << ": RWeaken idx OOB (idx=" << r.idx
                                      << ", |Γ|=" << concl.size() << ")";
                if (!r.child)
                    return MAKE_ERROR << path << ": RWeaken has null child";
                const Seq& cc = r.child->conclusion;
                if (concl.empty() || cc.size() != concl.size() - 1)
                    return MAKE_ERROR << path << ": RWeaken child size " << cc.size()
                                      << " != node size - 1 = "
                                      << (concl.empty() ? std::string("(node empty)")
                                                        : std::to_string(concl.size() - 1))
                                      << " — convention is child = node − {idx}";
                for (size_t k = 0, c = 0; k < concl.size(); ++k) {
                    if (k == r.idx) continue;
                    if (cc[c] != concl[k])
                        return MAKE_ERROR << path << ": RWeaken child[" << c
                                          << "] != node[" << k << "]";
                    ++c;
                }
                return walk(*r.child, path + ".W");
            }
            else if constexpr (std::is_same_v<T, RDuplicate>) {
                // child = node ++ {copy of position src} (child BIGGER).
                if (r.src >= concl.size())
                    return MAKE_ERROR << path << ": RDuplicate src OOB (src=" << r.src
                                      << ", |Γ|=" << concl.size() << ")";
                if (!r.child)
                    return MAKE_ERROR << path << ": RDuplicate has null child";
                const Seq& cc = r.child->conclusion;
                if (cc.size() != concl.size() + 1)
                    return MAKE_ERROR << path << ": RDuplicate child size " << cc.size()
                                      << " != node size + 1 = " << concl.size() + 1;
                for (size_t k = 0; k < concl.size(); ++k) {
                    if (cc[k] != concl[k])
                        return MAKE_ERROR << path << ": RDuplicate child[" << k
                                          << "] != node[" << k << "]";
                }
                if (cc.back() != concl[r.src])
                    return MAKE_ERROR << path << ": RDuplicate child.back() != node[src]";
                return walk(*r.child, path + ".Dup");
            }
            else if constexpr (std::is_same_v<T, RContract>) {
                if (r.i >= concl.size() || r.j >= concl.size())
                    return MAKE_ERROR << path << ": RContract position OOB (i=" << r.i
                                      << ", j=" << r.j << ", |Γ|=" << concl.size() << ")";
                if (r.i == r.j)
                    return MAKE_ERROR << path << ": RContract requires distinct positions (i=j=" << r.i << ")";
                if (concl[r.i] != concl[r.j])
                    return MAKE_ERROR << path << ": RContract requires concl[i] == concl[j]";
                if (!r.child)
                    return MAKE_ERROR << path << ": RContract has null child";
                const Seq& cc = r.child->conclusion;
                if (concl.empty() || cc.size() != concl.size() - 1)
                    return MAKE_ERROR << path << ": RContract child size " << cc.size()
                                      << " != node size - 1 = "
                                      << (concl.empty() ? std::string("(node empty)")
                                                        : std::to_string(concl.size() - 1));
                // Verify child = node with position j removed.
                for (size_t k = 0, c = 0; k < concl.size(); ++k) {
                    if (k == r.j) continue;
                    if (cc[c] != concl[k])
                        return MAKE_ERROR << path << ": RContract child[" << c
                                          << "] != node[" << k << "]";
                    ++c;
                }
                return walk(*r.child, path + ".C");
            }
            else if constexpr (std::is_same_v<T, RAnd>) {
                if (r.principal >= concl.size())
                    return MAKE_ERROR << path << ": RAnd principal OOB (p=" << r.principal
                                      << ", |Γ|=" << concl.size() << ")";
                const Formula& f = concl[r.principal].get();
                if (!f.is_compound() || f.as_compound().op != Op::And)
                    return MAKE_ERROR << path << ": RAnd principal is not ∧";
                if (!r.left || !r.right)
                    return MAKE_ERROR << path << ": RAnd has null child";

                std::vector<bool> in_left(concl.size(), false);
                for (size_t k : r.left_partition) {
                    if (k >= concl.size())
                        return MAKE_ERROR << path << ": RAnd partition entry " << k << " OOB";
                    if (k == r.principal)
                        return MAKE_ERROR << path << ": RAnd partition contains principal";
                    if (in_left[k])
                        return MAKE_ERROR << path << ": RAnd partition has duplicate " << k;
                    in_left[k] = true;
                }

                FormulaHandle phi = f.as_compound().left;
                FormulaHandle psi = f.as_compound().right;
                Seq exp_left, exp_right;
                for (size_t k = 0; k < concl.size(); ++k) {
                    if (k == r.principal) continue;
                    if (in_left[k]) exp_left.push_back(concl[k]);
                    else            exp_right.push_back(concl[k]);
                }
                exp_left.push_back(phi);
                exp_right.push_back(psi);

                if (r.left->conclusion != exp_left)
                    return MAKE_ERROR << path << ": RAnd left.conclusion mismatch";
                if (r.right->conclusion != exp_right)
                    return MAKE_ERROR << path << ": RAnd right.conclusion mismatch";

                TRY(walk(*r.left,  path + ".AndL"));
                return walk(*r.right, path + ".AndR");
            }
            else if constexpr (std::is_same_v<T, ROr>) {
                if (r.principal >= concl.size())
                    return MAKE_ERROR << path << ": ROr principal OOB";
                const Formula& f = concl[r.principal].get();
                if (!f.is_compound() || f.as_compound().op != Op::Or)
                    return MAKE_ERROR << path << ": ROr principal is not ∨";
                if (!r.child)
                    return MAKE_ERROR << path << ": ROr has null child";
                const Seq& cc = r.child->conclusion;
                if (cc.size() != concl.size() + 1)
                    return MAKE_ERROR << path << ": ROr child size " << cc.size()
                                      << " != node size + 1 = " << concl.size() + 1;
                FormulaHandle phi = f.as_compound().left;
                FormulaHandle psi = f.as_compound().right;
                for (size_t k = 0; k < concl.size(); ++k) {
                    FormulaHandle expected = (k == r.principal) ? phi : concl[k];
                    if (cc[k] != expected)
                        return MAKE_ERROR << path << ": ROr child[" << k << "] mismatch";
                }
                if (cc.back() != psi)
                    return MAKE_ERROR << path << ": ROr child.back() != ψ";
                return walk(*r.child, path + ".Or");
            }
            else if constexpr (std::is_same_v<T, RForall>) {
                if (r.principal >= concl.size())
                    return MAKE_ERROR << path << ": RForall principal OOB";
                const Formula& f = concl[r.principal].get();
                if (!f.is_quantified() || f.as_quantified().op != Op::Forall)
                    return MAKE_ERROR << path << ": RForall principal is not ∀";
                if (!r.child)
                    return MAKE_ERROR << path << ": RForall has null child";
                const Seq& cc = r.child->conclusion;
                if (cc.size() != concl.size())
                    return MAKE_ERROR << path << ": RForall child size " << cc.size()
                                      << " != node size " << concl.size();
                for (size_t k = 0; k < concl.size(); ++k) {
                    if (k == r.principal) continue;
                    if (cc[k] != concl[k])
                        return MAKE_ERROR << path << ": RForall child[" << k
                                          << "] != node[" << k << "] at non-principal slot";
                }
                // child[principal] = body[x:=eigen] not re-derived here (FormulaBuilder
                // not in scope). Eigen freshness deferred to LKRVerifier.
                return walk(*r.child, path + ".A");
            }
            else if constexpr (std::is_same_v<T, RExists>) {
                if (r.principal >= concl.size())
                    return MAKE_ERROR << path << ": RExists principal OOB";
                const Formula& f = concl[r.principal].get();
                if (!f.is_quantified() || f.as_quantified().op != Op::Exists)
                    return MAKE_ERROR << path << ": RExists principal is not ∃";
                if (!r.child)
                    return MAKE_ERROR << path << ": RExists has null child";
                const Seq& cc = r.child->conclusion;
                if (cc.size() != concl.size())
                    return MAKE_ERROR << path << ": RExists child size " << cc.size()
                                      << " != node size " << concl.size();
                for (size_t k = 0; k < concl.size(); ++k) {
                    if (k == r.principal) continue;
                    if (cc[k] != concl[k])
                        return MAKE_ERROR << path << ": RExists child[" << k
                                          << "] != node[" << k << "]";
                }
                return walk(*r.child, path + ".E");
            }
            else if constexpr (std::is_same_v<T, RCut>) {
                if (!r.left || !r.right)
                    return MAKE_ERROR << path << ": RCut has null child";
                const Seq& lc = r.left->conclusion;
                const Seq& rc = r.right->conclusion;
                if (lc.empty() || rc.empty())
                    return MAKE_ERROR << path << ": RCut child has empty conclusion";
                if (lc.back() != r.cut_formula)
                    return MAKE_ERROR << path << ": RCut left.back() != cut_formula";

                const size_t gl = lc.size() - 1;
                const size_t gr = rc.size() - 1;
                // Two valid shapes for node.concl:
                //   - Additive:       |node| = gl = gr and Γ_L = Γ_R = node.
                //   - Multiplicative: |node| = gl + gr and node = Γ_L ++ Γ_R.
                // For empty Γ (gl == gr == 0), the two shapes coincide; either
                // check passes vacuously.
                if (concl.size() == gl && gl == gr) {
                    for (size_t k = 0; k < concl.size(); ++k) {
                        if (lc[k] != concl[k] || rc[k] != concl[k])
                            return MAKE_ERROR << path
                                << ": RCut additive: left[" << k
                                << "] or right[" << k << "] != node[" << k << "]";
                    }
                } else if (concl.size() == gl + gr) {
                    for (size_t k = 0; k < gl; ++k) {
                        if (concl[k] != lc[k])
                            return MAKE_ERROR << path
                                << ": RCut mult: node[" << k
                                << "] != left[" << k << "]";
                    }
                    for (size_t k = 0; k < gr; ++k) {
                        if (concl[gl + k] != rc[k])
                            return MAKE_ERROR << path
                                << ": RCut mult: node[" << (gl + k)
                                << "] != right[" << k << "]";
                    }
                } else {
                    return MAKE_ERROR << path
                        << ": RCut shape neither additive nor multiplicative ("
                        << "node=" << concl.size() << ", |Γ_L|=" << gl
                        << ", |Γ_R|=" << gr << ")";
                }
                // right.back() is the NNF dual of cut_formula; equality
                // check requires FormulaBuilder. Deferred to LKRVerifier.
                TRY(walk(*r.left,  path + ".CutL"));
                return walk(*r.right, path + ".CutR");
            }
            else {
                return MAKE_ERROR << path << ": validate: unhandled rule variant";
            }
        }, d.rule);
    }
};

}  // namespace

util::ResultStatus validate(const Deriv& root) {
    Validator v;
    return v.walk(root, "root");
}

}  // namespace logic::proof::translate::lkr_cut_elim
