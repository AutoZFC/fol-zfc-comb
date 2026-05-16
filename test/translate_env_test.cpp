// translate_env_test — unit tests for the Env scaffolding used by the
// ND→LKR translator. See src/proof/translate/SPEC.md.
//
// What we test:
//   * Seed/push give monotonic positions and stable SequentEntry handles.
//   * Or, Forall, Exists mutators correctly mutate the principal in place
//     and (for Or) return the appended ψ entry.
//   * Cut produces two child Envs that inherit all parent entries with
//     identical positions, plus their respective φ / ¬φ at the end.
//   * And produces LEFT/RIGHT child Envs whose entries are routed by
//     left_needs / right_needs declarations; partition disjointness and
//     principal-not-in-needs are enforced.
//   * SequentEntries from one branch of a split are NOT valid in the
//     other (look-up returns Error, not a misleading position).
//
// All tests use the LKR verifier's own conventions for Or/Forall/Exists
// behavior so the Env's mutators stay in lockstep with the verifier.

#include "src/core/formula.h"
#include "src/proof/translate/env.h"

#include <iostream>
#include <set>
#include <string>

using namespace logic;
using namespace logic::proof::translate;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_OK(expr) do { \
    auto _r = (expr); \
    if (_r.ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected Ok, got: " << _r.error().to_string() \
                  << " at " << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_ERR(expr) do { \
    auto _r = (expr); \
    if (_r.is_error()) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " expected error, got Ok at " \
                  << __FILE__ << ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

// Helper: build a few atomic predicates over a single context.
struct Fixture {
    GlobalContext   ctx;
    FormulaBuilder  builder{ctx};

    PredicateHandle pP = ctx.add_predicate("P", 1);
    PredicateHandle pQ = ctx.add_predicate("Q", 1);
    PredicateHandle pR = ctx.add_predicate("R", 1);

    Term v0 = Term::generalized(0);
    Term v1 = Term::generalized(1);

    FormulaHandle P_v0 = builder.predicate(pP, {v0});
    FormulaHandle Q_v0 = builder.predicate(pQ, {v0});
    FormulaHandle R_v0 = builder.predicate(pR, {v0});
    FormulaHandle P_v1 = builder.predicate(pP, {v1});

    FormulaHandle nP_v0 = builder.make_not(P_v0);
    FormulaHandle nQ_v0 = builder.make_not(Q_v0);

    // (P(0) ∨ Q(0))
    FormulaHandle PorQ  = builder.make_or(P_v0, Q_v0);
    // (P(0) ∧ Q(0))
    FormulaHandle PandQ = builder.make_and(P_v0, Q_v0);
};

void test_seed_and_lookup() {
    Fixture f;
    Env env;
    SequentEntry e0 = env.seed(f.P_v0);
    EXPECT(env.size() == 1);

    auto pos = env.position_of(e0);
    EXPECT(pos.ok() && pos.value() == 0);

    auto fml = env.formula_at(e0);
    EXPECT(fml.ok() && fml.value() == f.P_v0);

    SequentEntry e1 = env.push(f.Q_v0);
    EXPECT(env.size() == 2);
    auto pos1 = env.position_of(e1);
    EXPECT(pos1.ok() && pos1.value() == 1);

    EXPECT(e0 != e1);
}

void test_unknown_entry_errors() {
    Fixture f;
    Env env;
    SequentEntry e0 = env.seed(f.P_v0);

    Env other;
    SequentEntry e_other = other.seed(f.Q_v0);

    // e_other is not in env.
    EXPECT_ERR(env.position_of(e_other));
    EXPECT_ERR(env.formula_at(e_other));
    (void)e0;
}

void test_apply_or_keeps_principal_id() {
    Fixture f;
    Env env;
    SequentEntry e_or = env.seed(f.PorQ);    // [PorQ@0]
    SequentEntry e_extra = env.push(f.R_v0); // [PorQ@0, R@1]

    auto psi_r = env.apply_or(e_or);
    EXPECT(psi_r.ok());
    SequentEntry psi = psi_r.value();

    // Principal slot now holds φ = P(0).
    auto fml_phi = env.formula_at(e_or);
    EXPECT(fml_phi.ok() && fml_phi.value() == f.P_v0);
    auto pos_phi = env.position_of(e_or);
    EXPECT(pos_phi.ok() && pos_phi.value() == 0);  // unchanged

    // ψ = Q(0) appended at the end.
    auto fml_psi = env.formula_at(psi);
    EXPECT(fml_psi.ok() && fml_psi.value() == f.Q_v0);
    auto pos_psi = env.position_of(psi);
    EXPECT(pos_psi.ok() && pos_psi.value() == env.size() - 1);

    // Other entries undisturbed.
    auto fml_extra = env.formula_at(e_extra);
    EXPECT(fml_extra.ok() && fml_extra.value() == f.R_v0);
}

void test_apply_or_wrong_op_errors() {
    Fixture f;
    Env env;
    SequentEntry e = env.seed(f.PandQ);   // not an Or
    EXPECT_ERR(env.apply_or(e));
}

void test_apply_forall_in_place() {
    Fixture f;
    Env env;
    // ∀x.P(x): body is P(0) (de Bruijn 0). Building via make_quantified
    // requires the body to use generalized-var 0 which it does.
    FormulaHandle forall_P = f.builder.make_quantified(Op::Forall, f.P_v0);
    SequentEntry e = env.seed(forall_P);

    var_index v_eigen = f.builder.enter_scope();
    EXPECT_OK(env.apply_forall(e, v_eigen, f.builder));

    auto fml = env.formula_at(e);
    EXPECT(fml.ok());
    // The principal now contains P(eigen).
    FormulaHandle expected = f.builder.predicate(
        f.pP, {Term::fixed(v_eigen)});
    EXPECT(fml.ok() && fml.value() == expected);
    auto pos = env.position_of(e);
    EXPECT(pos.ok() && pos.value() == 0);
}

void test_apply_exists_in_place() {
    Fixture f;
    Env env;
    FormulaHandle exists_P = f.builder.make_quantified(Op::Exists, f.P_v0);
    SequentEntry e = env.seed(exists_P);

    var_index v_witness = f.builder.enter_scope();
    Term t = Term::fixed(v_witness);
    EXPECT_OK(env.apply_exists(e, t, f.builder));

    auto fml = env.formula_at(e);
    FormulaHandle expected = f.builder.predicate(f.pP, {t});
    EXPECT(fml.ok() && fml.value() == expected);
}

void test_apply_cut_branches() {
    Fixture f;
    Env parent;
    SequentEntry e0 = parent.seed(f.P_v0);
    SequentEntry e1 = parent.push(f.Q_v0);

    auto cut = parent.apply_cut(f.R_v0, f.builder);

    // LEFT and RIGHT both inherit e0, e1 at same positions.
    auto l_e0 = cut.left.position_of(e0);   EXPECT(l_e0.ok() && l_e0.value() == 0);
    auto l_e1 = cut.left.position_of(e1);   EXPECT(l_e1.ok() && l_e1.value() == 1);
    auto r_e0 = cut.right.position_of(e0);  EXPECT(r_e0.ok() && r_e0.value() == 0);
    auto r_e1 = cut.right.position_of(e1);  EXPECT(r_e1.ok() && r_e1.value() == 1);

    // φ = R(0) at end of LEFT.
    auto l_phi = cut.left.formula_at(cut.left_phi);
    EXPECT(l_phi.ok() && l_phi.value() == f.R_v0);
    EXPECT(cut.left.size() == 3);

    // ¬φ NNF at end of RIGHT.
    auto r_neg = cut.right.formula_at(cut.right_neg_phi);
    EXPECT(r_neg.ok());
    FormulaHandle nnf_neg_R = f.builder.to_nnf(f.builder.make_not(f.R_v0));
    EXPECT(r_neg.ok() && r_neg.value() == nnf_neg_R);
    EXPECT(cut.right.size() == 3);

    // SequentEntries from LEFT are NOT valid in RIGHT and vice versa.
    EXPECT_ERR(cut.right.position_of(cut.left_phi));
    EXPECT_ERR(cut.left.position_of(cut.right_neg_phi));
}

void test_apply_and_routes_by_needs() {
    Fixture f;
    Env env;
    SequentEntry e_extra1 = env.seed(f.P_v1);                 // [P(1)@0]
    SequentEntry e_extra2 = env.push(f.R_v0);                 // [P(1), R(0)]
    SequentEntry e_and    = env.push(f.PandQ);                // [P(1), R(0), P∧Q]
    SequentEntry e_extra3 = env.push(f.nP_v0);                // [P(1), R(0), P∧Q, ¬P(0)]

    auto split = env.apply_and(e_and,
        /*left_needs=*/{e_extra1},
        /*right_needs=*/{e_extra3});
    EXPECT(split.ok());
    if (!split.ok()) return;

    auto& s = split.value();

    // LEFT contains: e_extra1 (declared LEFT), e_extra2 (default LEFT), φ=P(0).
    EXPECT(s.left.size() == 3);
    EXPECT_OK(s.left.position_of(e_extra1));
    EXPECT_OK(s.left.position_of(e_extra2));
    EXPECT_ERR(s.left.position_of(e_extra3));     // routed RIGHT
    EXPECT_ERR(s.left.position_of(e_and));        // consumed
    auto l_phi = s.left.formula_at(s.left_phi);
    EXPECT(l_phi.ok() && l_phi.value() == f.P_v0);

    // RIGHT contains: e_extra3 (declared RIGHT), ψ=Q(0).
    EXPECT(s.right.size() == 2);
    EXPECT_OK(s.right.position_of(e_extra3));
    EXPECT_ERR(s.right.position_of(e_extra1));    // routed LEFT
    EXPECT_ERR(s.right.position_of(e_extra2));    // routed LEFT
    EXPECT_ERR(s.right.position_of(e_and));       // consumed
    auto r_psi = s.right.formula_at(s.right_psi);
    EXPECT(r_psi.ok() && r_psi.value() == f.Q_v0);

    // left_partition lists the original positions routed to LEFT (sorted).
    // e_extra1 was at 0, e_extra2 was at 1. e_and at 2 is principal. e_extra3 at 3 → RIGHT.
    EXPECT(s.left_partition.size() == 2);
    EXPECT(s.left_partition[0] == 0 && s.left_partition[1] == 1);
}

void test_apply_and_disjoint_check() {
    Fixture f;
    Env env;
    SequentEntry e_and = env.seed(f.PandQ);
    SequentEntry e_x   = env.push(f.R_v0);

    EXPECT_ERR(env.apply_and(e_and, {e_x}, {e_x}));     // same on both sides
    EXPECT_ERR(env.apply_and(e_and, {e_and}, {}));      // principal in needs
    EXPECT_ERR(env.apply_and(e_and, {}, {e_and}));      // principal in needs
}

void test_apply_and_wrong_op_errors() {
    Fixture f;
    Env env;
    SequentEntry e = env.seed(f.PorQ);   // not an And
    EXPECT_ERR(env.apply_and(e, {}, {}));
}

void test_id_uniqueness_across_splits() {
    Fixture f;
    Env env;
    SequentEntry e0 = env.seed(f.P_v0);

    auto cut = env.apply_cut(f.Q_v0, f.builder);
    SequentEntry l_extra = cut.left.push(f.R_v0);
    SequentEntry r_extra = cut.right.push(f.R_v0);

    // l_extra and r_extra are independent; their IDs must differ
    // because they were minted from a shared counter.
    EXPECT(l_extra != r_extra);
    // Neither shares an ID with e0 or with the cut's φ/¬φ entries.
    EXPECT(l_extra != e0);
    EXPECT(r_extra != e0);
    EXPECT(l_extra != cut.left_phi);
    EXPECT(r_extra != cut.right_neg_phi);
}

}  // namespace

int main() {
    test_seed_and_lookup();
    test_unknown_entry_errors();
    test_apply_or_keeps_principal_id();
    test_apply_or_wrong_op_errors();
    test_apply_forall_in_place();
    test_apply_exists_in_place();
    test_apply_cut_branches();
    test_apply_and_routes_by_needs();
    test_apply_and_disjoint_check();
    test_apply_and_wrong_op_errors();
    test_id_uniqueness_across_splits();
    std::cout << "translate_env_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
