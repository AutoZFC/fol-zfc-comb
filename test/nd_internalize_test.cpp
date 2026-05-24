// Stage 1 (nd_internalize) tests.
//
// Phase 1 (theorem_facts.h):
//   compute_transitive_facts on the typed IR
//
// Phase 2 (nd_internalize/schema_macro.h):
//   replaces SchemaInst with Use(SH(φᵢ)), closed-instance only
//
// Covers facts(P) computation, schema macro semantics, and the
// soundness checks each phase commits to at its boundary.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_internalize/schema_macro.h"
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
using logic::proof::translate::nd_internalize::SchemaMacroResult;
using logic::proof::translate::nd_internalize::schema_macro;

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

// =========================================================================
// Phase 2 — schema_macro
// =========================================================================
//
// Each Phase 2 test loads a Runtime with the unary_self_impl schema:
//
//   schema unary_self_impl [P(1)]: forall x. (P(x) -> P(x))
//
// The schema is proven once, then per-test we lower a claim's proof
// containing one or more SchemaInst ops and feed the lowered Program
// through schema_macro.

// Set up a Runtime with the unary_self_impl schema proven. Returns the
// SchemaHandle; aborts on setup failure (test fixture, not test
// content).
SchemaHandle setup_unary_self_impl(Runtime& rt) {
    auto parsed = rt.load_with_proofs(R"(
        schema unary_self_impl [P(1)]: forall x. (P(x) -> P(x))

        proof unary_self_impl:
            fix x
            h_assume = assume P(x)
            h_impl = implies_intro h_assume
            h_all = forall_intro h_impl
            qed h_all
    )");
    if (!parsed.ok()) {
        std::cerr << "setup: parse fail: " << parsed.error().to_string() << "\n";
        std::abort();
    }
    auto exec = rt.execute_all_proofs(parsed.value());
    if (!exec.ok()) {
        std::cerr << "setup: execute fail: " << exec.error().to_string() << "\n";
        std::abort();
    }
    return rt.context().find_schema_handle("unary_self_impl").value();
}

// Count Use ops in a program (any AxiomRef target).
size_t count_use(const Program<nd::Instr>& p) {
    size_t n = 0;
    for (const auto& instr : p.instrs)
        if (std::holds_alternative<nd::Use>(instr)) ++n;
    return n;
}

// Count SchemaInst ops in a program.
size_t count_schema_inst(const Program<nd::Instr>& p) {
    size_t n = 0;
    for (const auto& instr : p.instrs)
        if (std::holds_alternative<nd::SchemaInst>(instr)) ++n;
    return n;
}

// =========================================================================
// Phase 2 Test 1: program with no SchemaInst → identity pass-through.
// =========================================================================
void test_macro_no_schemainst() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(r.value().proof.instrs.size(), prog.instrs.size());
    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_TRUE(r.value().synthetic_facts.empty());
}

// =========================================================================
// Phase 2 Test 2: single closed SchemaInst → Use(SH(φᵢ)).
//
//   schema_inst unary_self_impl { P: \y. q(y) }
//     resolves to:  forall x. (q(x) -> q(x))    (closed)
// =========================================================================
void test_macro_single_closed() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_inst: forall x. (q(x) -> q(x))
        proof use_inst:
            h = schema_inst unary_self_impl { P: \y. q(y) }
            qed h
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    EXPECT_EQ(count_schema_inst(prog), size_t{1});

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "schema_macro: " << r.error().to_string() << "\n";
        return;
    }

    // SchemaInst replaced by Use; one synthetic fact registered.
    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(count_use(r.value().proof), size_t{1});
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{1});

    // The synthetic fact's formula must structurally equal the claim
    // goal (instance forall x. (q(x) -> q(x))).
    SentenceHandle sh = r.value().synthetic_facts[0];
    auto claim = rt.context().find_claim("use_inst");
    EXPECT_TRUE(claim.has_value());
    if (claim.has_value()) {
        EXPECT_EQ(sh, claim.value());
    }

    // Use op's AxiomRef.sentence == synthetic_facts[0].
    bool found_use = false;
    for (const auto& instr : r.value().proof.instrs) {
        if (const auto* u = std::get_if<nd::Use>(&instr)) {
            EXPECT_EQ(u->axiom.sentence, sh);
            found_use = true;
            break;
        }
    }
    EXPECT_TRUE(found_use);
}

// =========================================================================
// Phase 2 Test 3: two SchemaInsts with structurally-equal instances →
// FormulaRegistry interns to one SH; synthetic_facts has 1 entry but
// proof has 2 Use ops.
// =========================================================================
void test_macro_two_same_instances_dedup() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_twice: (forall x. (q(x) -> q(x))) & (forall x. (q(x) -> q(x)))
        proof use_twice:
            h1 = schema_inst unary_self_impl { P: \y. q(y) }
            h2 = schema_inst unary_self_impl { P: \y. q(y) }
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    EXPECT_EQ(count_schema_inst(prog), size_t{2});

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(count_use(r.value().proof), size_t{2});
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{1});      // dedup
}

// =========================================================================
// Phase 2 Test 4: two SchemaInsts with structurally-distinct instances
// → two synthetic facts.
//
//   { P: \y. q(y) } → forall x. (q(x) -> q(x))
//   { P: \z. r(z) } → forall x. (r(x) -> r(x))      (distinct)
// =========================================================================
void test_macro_two_distinct_instances() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_two: (forall x. (q(x) -> q(x))) & (forall x. (r(x) -> r(x)))
        proof use_two:
            h1 = schema_inst unary_self_impl { P: \y. q(y) }
            h2 = schema_inst unary_self_impl { P: \z. r(z) }
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(count_use(r.value().proof), size_t{2});
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{2});
    EXPECT_TRUE(r.value().synthetic_facts[0] != r.value().synthetic_facts[1]);
}

// =========================================================================
// Phase 2 Test 5: SchemaInst with binding referencing an outer fix-var
// → Phase 3 deferral error.
//
//   fix a                                          # a : Fixed(0)
//   h = schema_inst unary_self_impl { P: \y. eq(y, a) }
//         lambda body references 'a' → empty-name_table resolution fails.
// =========================================================================
void test_macro_open_instance_defers() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_open: forall a. (eq(a, a) -> eq(a, a))
        proof use_open:
            fix a
            h = schema_inst unary_self_impl { P: \y. eq(y, a) }
            h_all = forall_intro h
            qed h_all
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    EXPECT_EQ(count_schema_inst(prog), size_t{1});

    auto r = schema_macro(rt.context(), prog);
    EXPECT_ERR(r);   // open instance — Phase 3 not implemented
}

// =========================================================================
// Phase 2 Test 6: schema_macro's output passes NDVerifier against the
// claim's goal — operational equivalence between SchemaInst and
// Use(synthetic-instance) is preserved.
// =========================================================================
void test_macro_output_verifies() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_inst: forall x. (q(x) -> q(x))
        proof use_inst:
            h = schema_inst unary_self_impl { P: \y. q(y) }
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    // Verify the macroed proof against the original claim goal.
    auto claim = rt.context().find_claim("use_inst");
    EXPECT_TRUE(claim.has_value());
    if (!claim.has_value()) return;
    FormulaHandle goal = claim.value().get().root();

    nd::NDVerifier v;
    Proof p{};
    p.system = System::ND;
    p.body   = r.value().proof;
    auto vr = v.verify(rt.context(), goal, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify failed: " << vr.error().to_string() << "\n";
    }
}

}  // namespace

int main() {
    // Phase 1: compute_transitive_facts
    test_empty();
    test_single_axiom();
    test_two_axioms_sorted();
    test_dedup_repeated_use();
    test_axiom_plus_theorem();
    test_theorem_chain();
    test_missing_theorem_errors();
    test_schema_inst_rejected();
    test_lex_sort_determinism();

    // Phase 2: schema_macro (closed instances)
    test_macro_no_schemainst();
    test_macro_single_closed();
    test_macro_two_same_instances_dedup();
    test_macro_two_distinct_instances();
    test_macro_open_instance_defers();
    test_macro_output_verifies();

    std::cerr << "nd_internalize_test: " << g_passed
              << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
