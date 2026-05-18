// axiom_rewrap Phase 1 tests — compute_transitive_axioms.
//
// Per AXIOM_REWRAP_DESIGN.md §7.1, this phase delivers:
//   compute_transitive_axioms(prog, ctx, theorem_axioms) → vector<string>
//
// The function returns axiom names (lex-sorted, deduplicated) for:
//   - direct Use(A) where ctx resolves A as an axiom
//   - transitive Use(T) where ctx resolves T as a theorem, via
//     theorem_axioms[T]
//
// SchemaInst is out of Phase 1 scope (errors clearly if encountered).

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/axiom_rewrap/theorem_axioms.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::axiom_rewrap::TheoremAxiomMap;
using logic::proof::translate::axiom_rewrap::compute_transitive_axioms;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT_TRUE(expr) do { \
    if (expr) { ++g_passed; } else { \
        std::cerr << "FAIL: " #expr " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

#define EXPECT_EQ(a, b) do { \
    auto _a = (a); auto _b = (b); \
    if (_a == _b) { ++g_passed; } else { \
        std::cerr << "FAIL: " #a " == " #b " at " __FILE__ ":" << __LINE__ \
                  << " (lhs/rhs differ)\n"; \
        ++g_failed; \
    } \
} while (0)

Program<nd::Instr> lower_or_die(const ParsedProof& parsed) {
    auto r = nd::lower(parsed);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

// =========================================================================
// Test 1: empty axiom set
// A proof of `p -> p` via assume/qed uses no axioms.
// =========================================================================
void test_empty_axiom_set() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0]);
    TheoremAxiomMap registry;

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        EXPECT_EQ(r.value().size(), size_t{0});
    }
}

// =========================================================================
// Test 2: single axiom used once
// =========================================================================
void test_single_axiom_used_once() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_true: forall x. p(x)
        claim p_y: forall y. p(y)
        proof p_y:
            fix y
            h = use a_true
            h2 = forall_elim h, y
            h3 = forall_intro h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0]);
    TheoremAxiomMap registry;

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_true"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 3: same axiom used multiple times → dedup
// =========================================================================
void test_same_axiom_used_many_times() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom p_holds: p
        claim p_and_p: p & p
        proof p_and_p:
            h1 = use p_holds
            h2 = use p_holds
            h3 = and_intro h1, h2
            qed h3
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0]);
    TheoremAxiomMap registry;

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"p_holds"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 4: multiple axioms in non-lex source order, output is lex-sorted
// =========================================================================
void test_multiple_axioms_lex_sort() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom c_ax: c_pred
        axiom a_ax: a_pred
        axiom b_ax: b_pred
        claim abc: a_pred & b_pred & c_pred
        proof abc:
            hc = use c_ax
            ha = use a_ax
            hb = use b_ax
            hab = and_intro ha, hb
            habc = and_intro hab, hc
            qed habc
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0]);
    TheoremAxiomMap registry;

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax", "b_ax", "c_ax"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 5: one-theorem transitive dep
// Proof uses theorem T, which itself uses axiom A.
// Closure = {A} (T contributes its axiom set, not T itself).
// =========================================================================
void test_one_theorem_dep() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim t_thm: a_pred
        proof t_thm:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Simulate that t_thm has been translated and its closure is recorded.
    TheoremAxiomMap registry;
    registry.put("t_thm", std::vector<std::string>{"a_ax"});

    // Now a proof that uses t_thm.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t: a_pred
        proof use_t:
            h = use t_thm
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0]);
    // Need to register t_thm as a theorem in ctx (the load above only
    // registers it as a claim with an attached proof; execute_all_proofs
    // would promote it). Manually promote via runtime API.
    auto t_thm_sentence = rt.context().find_claim("t_thm");
    if (!t_thm_sentence.has_value()) {
        std::cerr << "FAIL: t_thm claim not found\n"; ++g_failed; return;
    }
    rt.context().add_theorem("t_thm", t_thm_sentence.value());

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 6: chained theorem deps (T2 uses T1 uses A)
// =========================================================================
void test_chained_theorem_deps() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim t1: a_pred
        proof t1:
            h = use a_ax
            qed h
        claim t2: a_pred
        proof t2:
            h = use t1
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    TheoremAxiomMap registry;
    registry.put("t1", std::vector<std::string>{"a_ax"});
    registry.put("t2", std::vector<std::string>{"a_ax"});  // T2's closure includes A transitively

    // Outer proof using t2.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t2: a_pred
        proof use_t2:
            h = use t2
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0]);
    // Register t1, t2 as theorems.
    auto t1_s = rt.context().find_claim("t1");
    auto t2_s = rt.context().find_claim("t2");
    if (!t1_s || !t2_s) {
        std::cerr << "FAIL: t1/t2 not found\n"; ++g_failed; return;
    }
    rt.context().add_theorem("t1", t1_s.value());
    rt.context().add_theorem("t2", t2_s.value());

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        std::vector<std::string> expected{"a_ax"};
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 7: theorem cited but not in registry → error (caller bug)
// =========================================================================
void test_theorem_not_in_registry_errors() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim t_missing: p
        proof t_missing:
            h = assume p
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse fail: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    // Outer proof citing the unregistered theorem.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_missing: p
        proof use_missing:
            h = use t_missing
            qed h
    )");
    if (!parsed2.ok()) {
        std::cerr << "parse fail: " << parsed2.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0]);
    // Promote t_missing as a theorem in ctx but DO NOT add to registry.
    auto t_s = rt.context().find_claim("t_missing");
    if (!t_s) { std::cerr << "FAIL: claim missing\n"; ++g_failed; return; }
    rt.context().add_theorem("t_missing", t_s.value());

    TheoremAxiomMap registry;  // empty: t_missing not registered

    auto r = compute_transitive_axioms(prog, rt.context(), registry);
    EXPECT_TRUE(r.is_error());
}

}  // namespace

int main() {
    test_empty_axiom_set();
    test_single_axiom_used_once();
    test_same_axiom_used_many_times();
    test_multiple_axioms_lex_sort();
    test_one_theorem_dep();
    test_chained_theorem_deps();
    test_theorem_not_in_registry_errors();

    std::cerr << "axiom_rewrap_test: passed " << g_passed
              << ", failed " << g_failed << "\n";
    return g_failed == 0 ? 0 : 1;
}
