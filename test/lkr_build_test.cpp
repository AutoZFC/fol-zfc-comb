// lkr_build tests (COMPACT_LKR_DESIGN.md §4). Each scenario runs through both
// sinks: its LKR must verify and E(compact) must equal it (Theorem E1).

#include "lkr_ops_equal.h"

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/lkr_build/compact.h"
#include "src/proof/lkr_build/expand.h"
#include "src/proof/lkr_build/identity.h"
#include "src/proof/lkr_build/op_sink.h"
#include "src/proof/lkr_build/sequent.h"
#include "src/proof/proof.h"
#include "src/runtime/runtime.h"
#include "src/util/error.h"

#include <cstddef>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace logic;
using namespace logic::proof;
namespace lb = logic::proof::lkr_build;

namespace {

int g_passed = 0;
int g_failed = 0;

void fail(const std::string& name, const std::string& why) {
    std::cerr << "FAIL [" << name << "]: " << why << "\n";
    ++g_failed;
}

void check(bool ok, const std::string& name, const std::string& why) {
    if (ok) {
        ++g_passed;
    } else {
        fail(name, why);
    }
}

class Fixture {
public:
    Fixture() {
        auto loaded = rt_.load(
            "axiom ax_all: forall x. P(x)\n"
            "axiom ax_vocab: forall x. forall y. "
            "((Q(x) & R(x, y)) | (p & q & r))\n");
        if (!loaded.ok()) {
            fail("fixture", loaded.error().to_string());
        }
    }

    GlobalContext& ctx() { return rt_.context(); }

    FormulaHandle formula(const std::string& text) {
        return parse_sentence(text, ctx()).get().root();
    }

private:
    Runtime rt_;
};

util::ResultStatus verify(GlobalContext& ctx, FormulaHandle goal,
                          std::vector<lkr::Instr> instrs) {
    LKRProgram prog;
    prog.claim_name = "lkr_build_test";
    prog.instrs = std::move(instrs);
    Proof proof{System::LKR, std::move(prog)};
    lkr::LKRVerifier verifier;
    return verifier.verify(ctx, goal, proof);
}

template <typename Op>
size_t count_ops(const std::vector<lkr::Instr>& instrs) {
    size_t n = 0;
    for (const auto& instr : instrs) n += std::holds_alternative<Op>(instr);
    return n;
}

size_t count_identities(const std::vector<lb::CompactInstr>& instrs) {
    size_t n = 0;
    for (const auto& instr : instrs) {
        n += std::holds_alternative<lb::Identity>(instr);
    }
    return n;
}

using Status = util::ResultStatus;

using Scenario = std::function<Status(
    lb::Sequent seq, FormulaBuilder& builder, lb::OpSink& sink)>;

struct Both {
    bool                            ok{false};
    std::vector<lkr::Instr>         atomic;
    std::vector<lb::CompactInstr>   compact;
};

Both run_both(const std::string& name, Fixture& fx, FormulaHandle goal,
              const Scenario& scenario) {
    Both both;
    {
        FormulaBuilder builder(fx.ctx());
        lb::LkrSink sink(both.atomic);
        lb::Sequent seq(builder.to_nnf(goal));
        auto status = scenario(std::move(seq), builder, sink);
        if (!status.ok()) {
            fail(name, "LkrSink: " + status.error().to_string());
            return both;
        }
    }
    auto verified = verify(fx.ctx(), goal, both.atomic);
    if (!verified.ok()) {
        fail(name, "verify: " + verified.error().to_string());
        return both;
    }
    Program<lb::CompactInstr> compact;
    {
        FormulaBuilder builder(fx.ctx());
        lb::CompactSink sink(compact.instrs);
        lb::Sequent seq(builder.to_nnf(goal));
        auto status = scenario(std::move(seq), builder, sink);
        if (!status.ok()) {
            fail(name, "CompactSink: " + status.error().to_string());
            return both;
        }
    }
    auto expanded = lb::ExpandIdentities(fx.ctx(), goal).apply(compact);
    if (!expanded.ok()) {
        fail(name, "expand: " + expanded.error().to_string());
        return both;
    }
    std::string diff = lkr_ops_equal::first_difference(
        expanded.value().instrs, both.atomic);
    if (!diff.empty()) {
        fail(name, "E(compact) != LKR: " + diff);
        return both;
    }
    both.ok      = true;
    both.compact = std::move(compact.instrs);
    ++g_passed;
    return both;
}

// Sequent rules.

void test_or_axiom() {
    Fixture fx;
    run_both("or_axiom", fx, fx.formula("p -> p"),
        [](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY_ASSIGN(right, s.or_rule(0, k));
            return s.axiom_lit(0, right, k);
        });
}

void test_forall_exists() {
    Fixture fx;
    run_both("forall_exists", fx,
        fx.formula("(forall x. P(x)) -> (forall x. P(x))"),
        [](lb::Sequent s, FormulaBuilder& b, lb::OpSink& k) -> Status {
            TRY_ASSIGN(all, s.or_rule(0, k));
            TRY_ASSIGN(u, s.forall_rule(all, 100, b, k));
            TRY(s.exists_rule(0, u, b, k));
            return s.axiom_lit(0, all, k);
        });
}

void test_and_rule_shares() {
    Fixture fx;
    Both both = run_both("and_rule_shares", fx, fx.formula("p -> (p & p)"),
        [](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY_ASSIGN(conj, s.or_rule(0, k));
            TRY_ASSIGN(split, std::move(s).and_rule(conj, {0}, {0}, k));
            TRY(split.left.seq.axiom_lit(*split.left.moved[0],
                                         split.left.added, k));
            return split.right.seq.axiom_lit(*split.right.moved[0],
                                             split.right.added, k);
        });
    if (both.ok) {
        check(count_ops<lkr::Duplicate>(both.atomic) == 1, "and_rule_shares",
              "expected one Duplicate");
    }
}

void test_and_split() {
    Fixture fx;
    run_both("and_split", fx, fx.formula("(p & q) -> (q & p)"),
        [](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY(s.or_rule(0, k));
            TRY_ASSIGN(nq, s.or_rule(0, k));
            TRY_ASSIGN(split, std::move(s).and_split(1, {nq}, k));
            TRY(split.left.seq.axiom_lit(0, 1, k));
            return split.right.seq.axiom_lit(0, 1, k);
        });
}

void test_cut() {
    Fixture fx;
    FormulaHandle q = fx.formula("q");
    run_both("cut", fx, fx.formula("p -> p"),
        [q](lb::Sequent s, FormulaBuilder& b, lb::OpSink& k) -> Status {
            lb::Split split = std::move(s).cut_rule(q, b, k);
            TRY_ASSIGN(l, split.left.seq.or_rule(0, k));
            TRY(split.left.seq.axiom_lit(0, l, k));
            TRY_ASSIGN(r, split.right.seq.or_rule(0, k));
            return split.right.seq.axiom_lit(0, r, k);
        });
}

void test_structural() {
    Fixture fx;
    run_both("structural", fx, fx.formula("p -> p"),
        [](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY(s.duplicate(0, k));
            TRY(s.contraction(0, 1, k));
            TRY(s.or_rule(0, k));
            TRY(s.exchange(0, 1, k));
            TRY(s.duplicate(0, k));
            TRY(s.weakening(2, k));
            return s.axiom_lit(0, 1, k);
        });
}

void test_one_and_lemma() {
    Fixture fx;
    run_both("one", fx, fx.formula("q | ~_|_"),
        [](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY_ASSIGN(top, s.or_rule(0, k));
            return s.one(top, k);
        });
    auto ax = fx.ctx().find_axiom("ax_all");
    if (!ax.has_value()) {
        fail("close_by_lemma", "ax_all not found");
        return;
    }
    lkr::CloseByLemma close{{}, AxiomRef{ax.value()}, "ax_all"};
    run_both("close_by_lemma", fx, fx.formula("(forall x. P(x)) | q"),
        [close](lb::Sequent s, FormulaBuilder&, lb::OpSink& k) -> Status {
            TRY(s.or_rule(0, k));
            s.close_by_lemma(close, k);
            return util::Ok();
        });
}

void test_rule_errors() {
    Fixture fx;
    FormulaBuilder b(fx.ctx());
    std::vector<lkr::Instr> ops;
    lb::LkrSink k(ops);
    lb::Sequent s(b.to_nnf(fx.formula("p -> p")));
    check(s.or_rule(3, k).is_error(), "or_rule_range", "accepted position 3");
    check(s.forall_rule(0, 1, b, k).is_error(), "forall_shape",
          "accepted ∀ on a ∨");
    check(s.duplicate(1, k).is_error(), "duplicate_range", "accepted 1");
    check(s.weakening(1, k).is_error(), "weakening_range", "accepted 1");
    check(s.axiom_lit(0, 0, k).is_error(), "axiom_same", "accepted a = b");
    check(s.one(0, k).is_error(), "one_shape", "accepted One on ¬p ∨ p");
    lb::Sequent conj(b.to_nnf(fx.formula("p & q")));
    check(lb::Sequent(conj).and_split(0, {0}, k).is_error(), "and_principal",
          "accepted the principal in the partition");
    check(ops.empty(), "rule_errors_emit", "a failed rule wrote an op");
}

// The identity X (§1).

void check_identity(Fixture& fx, const std::string& a_text) {
    FormulaHandle goal = fx.formula("(" + a_text + ") -> (" + a_text + ")");
    for (bool flip : {false, true}) {
        std::string name =
            "identity " + a_text + (flip ? " (b, a)" : " (a, b)");
        size_t expected = 0;
        Both both = run_both(name, fx, goal,
            [flip, &expected](lb::Sequent s, FormulaBuilder& b,
                              lb::OpSink& k) -> Status {
                TRY_ASSIGN(pos, s.or_rule(0, k));
                expected = lb::identity_eigens(s.at(pos));
                return flip ? std::move(s).identity(0, pos, 200, b, k)
                            : std::move(s).identity(pos, 0, 200, b, k);
            });
        if (!both.ok) continue;
        std::vector<var_index> eigens;
        for (const auto& instr : both.atomic) {
            if (auto* f = std::get_if<lkr::Forall>(&instr)) {
                eigens.push_back(f->eigen);
            }
        }
        bool numbered = eigens.size() == expected;
        for (size_t i = 0; numbered && i < eigens.size(); ++i) {
            numbered = eigens[i] == 200 + i;
        }
        check(numbered, name, "eigenvariables are not 200.. in order, or "
                              "their count is not identity_eigens");
        check(count_identities(both.compact) == 1, name,
              "compact program should hold one Identity");
    }
}

void test_identity_shapes() {
    Fixture fx;
    for (const char* a : {
             "p", "~p", "p & q", "p | q", "(p & q) | r", "p -> q", "p <-> q",
             "forall x. P(x)", "exists x. P(x)", "forall x. exists y. R(x, y)",
             "forall x. (P(x) -> exists y. (Q(y) & R(x, y)))",
             "(forall x. P(x)) & (forall x. P(x))", "~_|_", "_|_ | p",
             "(exists x. P(x)) <-> (forall y. Q(y))"}) {
        check_identity(fx, a);
    }
}

void test_identity_swapped() {
    Fixture fx;
    run_both("identity_swapped", fx, fx.formula("(p & q) -> (q & p)"),
        [](lb::Sequent s, FormulaBuilder& b, lb::OpSink& k) -> Status {
            TRY_ASSIGN(pos, s.or_rule(0, k));
            return std::move(s).identity(0, pos, 0, b, k);
        });
}

void test_identity_rejects_non_duals() {
    Fixture fx;
    FormulaBuilder b(fx.ctx());
    std::vector<lkr::Instr> ops;
    lb::LkrSink k(ops);
    lb::Sequent s(b.to_nnf(fx.formula("(p & q) -> (p | q)")));
    auto pos = s.or_rule(0, k);
    check(pos.ok() && std::move(s).identity(0, pos.value(), 0, b, k).is_error(),
          "identity_non_duals", "X accepted ∨ against ∨");
}

void test_identity_eigens() {
    Fixture fx;
    FormulaBuilder b(fx.ctx());
    auto eigens = [&](const char* text) {
        return lb::identity_eigens(b.to_nnf(fx.formula(text)));
    };
    check(eigens("p") == 0, "eigens_p", "p");
    check(eigens("~_|_") == 0, "eigens_top", "¬⊥");
    check(eigens("forall x. P(x)") == 1, "eigens_forall", "∀x.P(x)");
    check(eigens("forall x. exists y. R(x, y)") == 2, "eigens_nested", "∀∃");
    check(eigens("(forall x. P(x)) & (forall x. P(x))") == 2, "eigens_shared",
          "a shared subformula counts per occurrence");
}

// The expansion E (§2).

// The Exists after the identity names its Forall: compact %3, LKR %5.
void test_expand_renames_witness() {
    Fixture fx;
    Both both = run_both("expand_renames_witness", fx, fx.formula(
            "((forall z. P(z)) -> (forall z. P(z))) & "
            "(forall x. (Q(x) -> exists y. Q(y)))"),
        [](lb::Sequent s, FormulaBuilder& b, lb::OpSink& k) -> Status {
            TRY_ASSIGN(split, std::move(s).and_split(0, {}, k));
            lb::Sequent& left = split.left.seq;
            TRY_ASSIGN(all, left.or_rule(0, k));
            TRY(std::move(left).identity(all, 0, 300, b, k));
            lb::Sequent& right = split.right.seq;
            TRY_ASSIGN(x, right.forall_rule(0, 301, b, k));
            TRY_ASSIGN(ex, right.or_rule(0, k));
            TRY(right.exists_rule(ex, x, b, k));
            return right.axiom_lit(0, ex, k);
        });
    if (!both.ok) return;
    const lkr::Exists* compact_ex = nullptr;
    for (const auto& instr : both.compact) {
        if (const auto* op = std::get_if<lkr::Instr>(&instr)) {
            if (const auto* ex = std::get_if<lkr::Exists>(op)) compact_ex = ex;
        }
    }
    const lkr::Exists* atomic_ex = nullptr;
    for (const auto& instr : both.atomic) {
        if (const auto* ex = std::get_if<lkr::Exists>(&instr)) atomic_ex = ex;
    }
    check(compact_ex && atomic_ex && compact_ex->witness.idx == 3 &&
              atomic_ex->witness.idx == 5,
          "expand_renames_witness", "witness indices are not 3 and 5");
}

void expect_rejected(Fixture& fx, const std::string& name, const char* goal,
                     std::vector<lb::CompactInstr> instrs) {
    Program<lb::CompactInstr> prog;
    prog.instrs = std::move(instrs);
    auto out = lb::ExpandIdentities(fx.ctx(), fx.formula(goal)).apply(prog);
    check(out.is_error(), name, "expansion accepted the program");
}

void test_expand_input_gate() {
    Fixture fx;
    using lb::Identity;
    const char* imp = "p -> p";
    const char* swap = "(p & q) -> (q & p)";
    expect_rejected(fx, "gate_after_close", imp,
        {lkr::Or{{}, 0}, lkr::AxiomLit{{}, 0, 1}, lkr::Or{{}, 0}});
    expect_rejected(fx, "gate_left_open", imp, {lkr::Or{{}, 0}});
    expect_rejected(fx, "gate_range", imp, {lkr::Or{{}, 5}});
    expect_rejected(fx, "gate_shape", imp, {lkr::Forall{{}, 0, 7}});
    expect_rejected(fx, "gate_partition_principal", swap,
        {lkr::Or{{}, 0}, lkr::Or{{}, 0}, lkr::And{{}, 1, {1}}});
    expect_rejected(fx, "gate_partition_repeat", swap,
        {lkr::Or{{}, 0}, lkr::Or{{}, 0}, lkr::And{{}, 1, {2, 2}}});
    expect_rejected(fx, "gate_partition_range", swap,
        {lkr::Or{{}, 0}, lkr::Or{{}, 0}, lkr::And{{}, 1, {9}}});
    expect_rejected(fx, "gate_witness", "(forall x. P(x)) -> (forall x. P(x))",
        {lkr::Or{{}, 0}, lkr::Exists{{}, 0, TermRef{0}}});
    expect_rejected(fx, "gate_ast_cut", imp,
        {lkr::Cut{{}, std::shared_ptr<ASTNode>{}}});
    expect_rejected(fx, "gate_identity_shapes", "(p & q) -> (p | q)",
        {lkr::Or{{}, 0}, Identity{{}, 0, 1, 0}});
    expect_rejected(fx, "gate_identity_same", imp,
        {lkr::Or{{}, 0}, Identity{{}, 0, 0, 0}});
    expect_rejected(fx, "gate_identity_range", imp,
        {lkr::Or{{}, 0}, Identity{{}, 0, 7, 0}});
}

}  // namespace

int main() {
    test_or_axiom();
    test_forall_exists();
    test_and_rule_shares();
    test_and_split();
    test_cut();
    test_structural();
    test_one_and_lemma();
    test_rule_errors();
    test_identity_shapes();
    test_identity_swapped();
    test_identity_rejects_non_duals();
    test_identity_eigens();
    test_expand_renames_witness();
    test_expand_input_gate();

    std::cout << "lkr_build_test: " << g_passed << " passed, " << g_failed
              << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
