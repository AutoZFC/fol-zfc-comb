// Stage 1 (nd_internalize) Phase 1 tests — compute_transitive_facts.
//
// Spec: src/proof/translate/theorem_facts.h
//
// Covers facts(P) computation on the typed IR:
//   - direct_facts: Use(F).axiom.sentence for axiom and theorem cites
//   - transitive closure via TheoremFactsMap
//   - dedup
//   - lex-sort by SentenceHandle.id() (deterministic order)
//   - input-gate rejection of SchemaInst (Stage 1's schema macro runs
//     upstream of this closure)
//   - missing-theorem-in-map error (build-order bug surfacing)
//
// Phase 1 is shared component, not the Stage 1 pass itself; tests live
// here so the Stage 1 test target owns its full surface as it grows.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/ops.h"
#include "src/proof/proof.h"
#include "src/proof/translate/theorem_facts.h"
#include "src/runtime/runtime.h"

#include <cassert>
#include <iostream>
#include <string>
#include <variant>
#include <vector>

using namespace logic;
using namespace logic::proof;
using logic::proof::translate::TheoremFactsMap;
using logic::proof::translate::compute_transitive_facts;

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

#define EXPECT_ERR(r) do { \
    if (!(r).ok()) { ++g_passed; } else { \
        std::cerr << "FAIL: expected error at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

Program<nd::Instr> lower_or_die(const ParsedProof& parsed, const GlobalContext& ctx) {
    auto r = nd::lower(parsed, ctx);
    if (!r.ok()) {
        std::cerr << "lowering failed: " << r.error().to_string() << "\n";
        std::abort();
    }
    return std::move(r).unwrap();
}

// Build a vector<SentenceHandle> from names by looking each up in ctx,
// then sort by SentenceHandle.id() to match compute_transitive_facts's
// output convention.
std::vector<SentenceHandle> expected_sorted(
    const GlobalContext& ctx, std::initializer_list<const char*> names)
{
    std::vector<SentenceHandle> v;
    for (const char* n : names) {
        auto h = ctx.find_known(n);
        if (!h.has_value()) {
            std::cerr << "expected_sorted: name '" << n << "' not in ctx\n";
            std::abort();
        }
        v.push_back(h.value());
    }
    std::sort(v.begin(), v.end(),
              [](SentenceHandle a, SentenceHandle b) {
                  return a.hash_value() < b.hash_value();
              });
    return v;
}

// =========================================================================
// Test 1: no Use ops → facts(P) = {}
// =========================================================================
void test_empty() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap empty_map;

    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_TRUE(r.ok());
    if (r.ok()) EXPECT_TRUE(r.value().empty());
}

// =========================================================================
// Test 2: single axiom Use
// =========================================================================
void test_single_axiom() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim use_a: a_pred
        proof use_a:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap empty_map;

    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        auto expected = expected_sorted(rt.context(), {"a_ax"});
        EXPECT_EQ(r.value(), expected);
    }
}

// =========================================================================
// Test 3: two distinct axioms — result is lex-sorted by SentenceHandle.id()
// (registration order = source order, so sort is by registration id)
// =========================================================================
void test_two_axioms_sorted() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom b_ax: b_pred
        axiom a_ax: a_pred
        claim use_both: a_pred & b_pred
        proof use_both:
            h1 = use a_ax
            h2 = use b_ax
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap empty_map;

    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        auto expected = expected_sorted(rt.context(), {"a_ax", "b_ax"});
        EXPECT_EQ(r.value(), expected);
        EXPECT_EQ(r.value().size(), size_t{2});
    }
}

// =========================================================================
// Test 4: same axiom used twice in body → deduped to one fact
// =========================================================================
void test_dedup_repeated_use() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim use_a_twice: a_pred & a_pred
        proof use_a_twice:
            h1 = use a_ax
            h2 = use a_ax
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap empty_map;

    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_TRUE(r.ok());
    if (r.ok()) EXPECT_EQ(r.value().size(), size_t{1});
}

// =========================================================================
// Test 5: axiom + theorem mix. T1 cites b_ax and proves c_pred (distinct
// from any axiom body so SH(T1) is a fresh handle). main uses {a_ax, T1}.
// Closure should be {a_ax, b_ax, T1} as three distinct SentenceHandles.
//
// Distinct formulas matter: identity is SentenceHandle (interned by
// structure), so two registered names with identical bodies collapse to
// one fact — by design. The test exercises the three-distinct-facts
// case; the dedup-on-alias case is covered separately.
// =========================================================================
void test_axiom_plus_theorem() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        axiom b_ax: b_pred -> c_pred
        claim t1: c_pred
        proof t1:
            h_b = assume b_pred
            h_impl = use b_ax
            h_c = implies_elim h_impl, h_b
            qed h_c
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    // Promote t1 from claim to theorem.
    auto t1_claim = rt.context().find_claim("t1");
    if (!t1_claim.has_value()) { ++g_failed; return; }
    rt.context().add_theorem("t1", t1_claim.value());

    // Register t1's facts in the map: closure(t1) = {b_ax}.
    TheoremFactsMap known;
    known.put(rt.context().find_known("t1").value(),
              expected_sorted(rt.context(), {"b_ax"}));

    auto parsed2 = rt.load_with_proofs(R"(
        claim use_a_and_t1: a_pred & c_pred
        proof use_a_and_t1:
            h1 = use a_ax
            h2 = use t1
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed2.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    auto r = compute_transitive_facts(prog, rt.context(), known);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        auto expected = expected_sorted(rt.context(), {"a_ax", "b_ax", "t1"});
        EXPECT_EQ(r.value(), expected);
        EXPECT_EQ(r.value().size(), size_t{3});
    }
}

// =========================================================================
// Test 6: theorem chain with distinct formulas at each link.
// a_ax:  a_pred -> b_pred
// t1:    a_pred -> c_pred   (uses a_ax; structurally distinct)
// t2:    a_pred -> d_pred   (uses t1; structurally distinct)
// main uses just t2 — closure should be {a_ax, t1, t2}: 3 distinct SHs.
// =========================================================================
void test_theorem_chain() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred -> b_pred
        axiom b_to_c: b_pred -> c_pred
        axiom c_to_d: c_pred -> d_pred

        claim t1: a_pred -> c_pred
        proof t1:
            h_a = assume a_pred
            h_ab = use a_ax
            h_b = implies_elim h_ab, h_a
            h_bc = use b_to_c
            h_c = implies_elim h_bc, h_b
            h_impl = implies_intro h_c
            qed h_impl

        claim t2: a_pred -> d_pred
        proof t2:
            h_a = assume a_pred
            h_t1 = use t1
            h_c = implies_elim h_t1, h_a
            h_cd = use c_to_d
            h_d = implies_elim h_cd, h_c
            h_impl = implies_intro h_d
            qed h_impl
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    // Promote t1 and t2 as theorems.
    auto t1_c = rt.context().find_claim("t1");
    auto t2_c = rt.context().find_claim("t2");
    if (!t1_c.has_value() || !t2_c.has_value()) { ++g_failed; return; }
    rt.context().add_theorem("t1", t1_c.value());
    rt.context().add_theorem("t2", t2_c.value());

    // Register facts for both (mirrors what the runner installs after
    // each theorem's Stage 1 pass):
    //   facts(t1) = {a_ax, b_to_c}
    //   facts(t2) = {a_ax, b_to_c, c_to_d, t1}    (transitive)
    TheoremFactsMap known;
    SentenceHandle sh_t1 = rt.context().find_known("t1").value();
    SentenceHandle sh_t2 = rt.context().find_known("t2").value();
    known.put(sh_t1, expected_sorted(rt.context(), {"a_ax", "b_to_c"}));
    known.put(sh_t2, expected_sorted(rt.context(), {"a_ax", "b_to_c", "c_to_d", "t1"}));

    // main uses just t2.
    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t2: a_pred -> d_pred
        proof use_t2:
            h = use t2
            qed h
    )");
    if (!parsed2.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    auto r = compute_transitive_facts(prog, rt.context(), known);
    EXPECT_TRUE(r.ok());
    if (r.ok()) {
        auto expected = expected_sorted(rt.context(),
                          {"a_ax", "b_to_c", "c_to_d", "t1", "t2"});
        EXPECT_EQ(r.value(), expected);
        EXPECT_EQ(r.value().size(), size_t{5});
    }
}

// =========================================================================
// Test 7: cited theorem missing from TheoremFactsMap → error
// (build-order bug surfaces here).
// =========================================================================
void test_missing_theorem_errors() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim t_missing: p
        proof t_missing:
            h = assume p
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    auto t_c = rt.context().find_claim("t_missing");
    if (!t_c.has_value()) { ++g_failed; return; }
    rt.context().add_theorem("t_missing", t_c.value());

    auto parsed2 = rt.load_with_proofs(R"(
        claim use_missing: p
        proof use_missing:
            h = use t_missing
            qed h
    )");
    if (!parsed2.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed2.value().proofs[0], rt.context());

    TheoremFactsMap empty_map;       // does NOT contain t_missing
    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_ERR(r);
}

// =========================================================================
// Test 8: SchemaInst in program → input-gate error
// (Stage 1's schema macro must run upstream of this closure).
// =========================================================================
void test_schema_inst_rejected() {
    Runtime rt;
    // Manually construct a Program containing a SchemaInst op so we
    // exercise the input gate without needing a real schema definition.
    Program<nd::Instr> prog;
    prog.claim_name = "synthetic";
    // SchemaInst with default-constructed payload — the closure
    // function inspects only the variant tag.
    nd::SchemaInst si{};
    prog.instrs.push_back(nd::Instr{si});
    nd::Qed q{}; q.derived = StepRef{0};
    prog.instrs.push_back(nd::Instr{q});

    TheoremFactsMap empty_map;
    auto r = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_ERR(r);
}

// =========================================================================
// Test 9: determinism — running compute_transitive_facts twice on the
// same program yields the same ordered vector.
// =========================================================================
void test_lex_sort_determinism() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom b_ax: b_pred
        axiom c_ax: c_pred
        axiom a_ax: a_pred
        claim use_three: (a_pred & b_pred) & c_pred
        proof use_three:
            h_a = use a_ax
            h_b = use b_ax
            h_c = use c_ax
            h_ab = and_intro h_a, h_b
            h_abc = and_intro h_ab, h_c
            qed h_abc
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    TheoremFactsMap empty_map;

    auto r1 = compute_transitive_facts(prog, rt.context(), empty_map);
    auto r2 = compute_transitive_facts(prog, rt.context(), empty_map);
    EXPECT_TRUE(r1.ok());
    EXPECT_TRUE(r2.ok());
    if (r1.ok() && r2.ok()) {
        EXPECT_EQ(r1.value(), r2.value());
        EXPECT_EQ(r1.value().size(), size_t{3});
    }
}

}  // namespace

int main() {
    test_empty();
    test_single_axiom();
    test_two_axioms_sorted();
    test_dedup_repeated_use();
    test_axiom_plus_theorem();
    test_theorem_chain();
    test_missing_theorem_errors();
    test_schema_inst_rejected();
    test_lex_sort_determinism();

    std::cerr << "nd_internalize_test: " << g_passed
              << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
