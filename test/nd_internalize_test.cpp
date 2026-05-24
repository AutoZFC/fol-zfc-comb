// Stage 1 (nd_internalize) tests.
//
// Phase 1 (theorem_facts.h):
//   compute_transitive_facts on the typed IR
//
// Phase 2/3 (nd_internalize/schema_macro.h):
//   replaces SchemaInst with Use(SH(φᵢ)) (closed) or
//   Use(SH(closed_φ))+ForallElim chain (open instance, Q1b/α)
//
// Phase 4 (nd_internalize/prelude.h):
//   builds the Assume(H) + and_elim chain that opens the wrapped proof

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/nd/ops.h"
#include "src/proof/nd/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_internalize/apply.h"
#include "src/proof/translate/nd_internalize/body.h"
#include "src/proof/translate/nd_internalize/prelude.h"
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
using logic::proof::translate::nd_internalize::PreludeResult;
using logic::proof::translate::nd_internalize::emit_prelude;
using logic::proof::translate::nd_internalize::BodyEmitResult;
using logic::proof::translate::nd_internalize::emit_body_with_remap;
using logic::proof::translate::nd_internalize::ApplyResult;
using logic::proof::translate::nd_internalize::apply;

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
// Phase 3 Test: SchemaInst with binding referencing an outer fix-var.
// Per spec §4 / Q1b option α, schema_macro universally closes the open
// instance and emits a ForallElim chain to re-instantiate at the call
// site.
//
//   fix a                                          # a : Fixed(0)
//   h = schema_inst unary_self_impl { P: \y. eq(y, a) }
//       resolves to:  forall x. (eq(x, Fixed(0)) -> eq(x, Fixed(0)))
//                     ← has 1 free Fixed (Fixed(0) = a)
//   universal closure:
//                     forall v. forall x. (eq(x, v) -> eq(x, v))
//   emitted ops at the SchemaInst position:
//       Use(SH(closure))          ⊢ forall v. forall x. (eq(x, v) -> eq(x, v))
//       ForallElim(use, a)        ⊢ forall x. (eq(x, a) -> eq(x, a))   = φᵢ
// =========================================================================
void test_macro_open_instance_one_fixed() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_open: forall a. (forall x. (eq(x, a) -> eq(x, a)))
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
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "schema_macro: " << r.error().to_string() << "\n";
        return;
    }

    // SchemaInst removed; replaced by Use + 1 ForallElim. So total
    // op count = original + 1.
    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(r.value().proof.instrs.size(), prog.instrs.size() + 1);
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{1});

    // Verify the rewritten proof against the original claim's goal.
    auto claim = rt.context().find_claim("use_open");
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

// =========================================================================
// Phase 3 Test: open instance with TWO free Fixed vars. Universal
// closure must add two outer ∀'s; ForallElim chain has length 2.
// =========================================================================
void test_macro_open_instance_two_fixed() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim use_open2: forall a. forall b.
            (forall x. ((eq(x, a) | eq(x, b)) -> (eq(x, a) | eq(x, b))))
        proof use_open2:
            fix a
            fix b
            h = schema_inst unary_self_impl { P: \y. (eq(y, a) | eq(y, b)) }
            h_all_b = forall_intro h
            h_all_a = forall_intro h_all_b
            qed h_all_a
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "schema_macro: " << r.error().to_string() << "\n";
        return;
    }

    // 1 SchemaInst → 1 Use + 2 ForallElims = 3 ops.
    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(r.value().proof.instrs.size(), prog.instrs.size() + 2);
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{1});

    auto claim = rt.context().find_claim("use_open2");
    if (!claim.has_value()) { ++g_failed; return; }
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

// =========================================================================
// Phase 3 Test: mix of closed and open SchemaInsts in one proof.
// Both replaced correctly; step_remap propagates through subsequent ops.
// =========================================================================
void test_macro_mixed_closed_and_open() {
    Runtime rt;
    setup_unary_self_impl(rt);

    auto parsed = rt.load_with_proofs(R"(
        claim mixed: forall a. ((forall x. (q(x) -> q(x))) & (forall x. (eq(x, a) -> eq(x, a))))
        proof mixed:
            fix a
            h_closed = schema_inst unary_self_impl { P: \y. q(y) }
            h_open   = schema_inst unary_self_impl { P: \y. eq(y, a) }
            h_and = and_intro h_closed, h_open
            h_all = forall_intro h_and
            qed h_all
    )");
    if (!parsed.ok()) {
        std::cerr << "parse: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    Program<nd::Instr> prog = lower_or_die(parsed.value().proofs[0], rt.context());
    EXPECT_EQ(count_schema_inst(prog), size_t{2});

    auto r = schema_macro(rt.context(), prog);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) {
        std::cerr << "schema_macro: " << r.error().to_string() << "\n";
        return;
    }

    // Closed instance: 1:1. Open instance: 1:(1+1) = +1 op. So output
    // has prog.instrs.size() + 1.
    EXPECT_EQ(count_schema_inst(r.value().proof), size_t{0});
    EXPECT_EQ(r.value().proof.instrs.size(), prog.instrs.size() + 1);
    EXPECT_EQ(r.value().synthetic_facts.size(), size_t{2});  // two distinct facts

    auto claim = rt.context().find_claim("mixed");
    if (!claim.has_value()) { ++g_failed; return; }
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

// =========================================================================
// Phase 4 — emit_prelude
// =========================================================================
//
// Helper: register n distinct axioms a0..a_{n-1} on a fresh Runtime
// and return their SentenceHandles in declaration order (which equals
// registration order, which equals SentenceHandle.id() order — so the
// returned vector matches what compute_transitive_facts would hand
// emit_prelude). Uses distinct nullary predicate names so each formula
// is structurally distinct (no aliasing).
std::vector<SentenceHandle> setup_n_axioms(Runtime& rt, size_t n) {
    std::string src;
    for (size_t i = 0; i < n; ++i) {
        src += "axiom a" + std::to_string(i) + ": p" + std::to_string(i) + "\n";
    }
    if (!rt.load(src).ok()) {
        std::cerr << "setup_n_axioms: load failed\n";
        std::abort();
    }
    std::vector<SentenceHandle> out;
    for (size_t i = 0; i < n; ++i) {
        auto sh = rt.context().find_known("a" + std::to_string(i));
        if (!sh.has_value()) { std::cerr << "setup: not found\n"; std::abort(); }
        out.push_back(sh.value());
    }
    return out;
}

// =========================================================================
// Phase 4 Test: n = 0 → empty prelude, invalid H, empty table.
// =========================================================================
void test_prelude_empty() {
    Runtime rt;
    auto r = emit_prelude(rt.context(), {});
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;
    EXPECT_TRUE(r.value().instrs.empty());
    EXPECT_TRUE(!r.value().H.valid());
    EXPECT_TRUE(r.value().fact_step_table.empty());
}

// =========================================================================
// Phase 4 Test: n = 1 → one Assume op; fact's StepRef is {0}.
// H = φ_{F₁} directly (no AND).
// =========================================================================
void test_prelude_n1() {
    Runtime rt;
    auto facts = setup_n_axioms(rt, 1);

    auto r = emit_prelude(rt.context(), facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(r.value().instrs.size(), size_t{1});
    EXPECT_TRUE(std::holds_alternative<nd::Assume>(r.value().instrs[0]));
    EXPECT_TRUE(r.value().H.valid());

    // H's formula equals φ_{F₁}'s formula.
    EXPECT_EQ(r.value().H.get().root(), facts[0].get().root());

    EXPECT_EQ(r.value().fact_step_table.size(), size_t{1});
    EXPECT_EQ(r.value().fact_step_table.at(facts[0]).idx, uint32_t{0});
}

// =========================================================================
// Phase 4 Test: n = 2 → Assume + AndElimL + AndElimR; 3 ops.
//   [0] Assume(H = φ_1 ∧ φ_2)
//   [1] AndElimL(h)         → φ_1   ← F_1 extract (h_1)
//   [2] AndElimR(h)         → φ_2   ← F_2 extract
// =========================================================================
void test_prelude_n2() {
    Runtime rt;
    auto facts = setup_n_axioms(rt, 2);

    auto r = emit_prelude(rt.context(), facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(r.value().instrs.size(), size_t{3});       // 2n - 1
    EXPECT_TRUE(std::holds_alternative<nd::Assume>(r.value().instrs[0]));
    EXPECT_TRUE(std::holds_alternative<nd::AndElimL>(r.value().instrs[1]));
    EXPECT_TRUE(std::holds_alternative<nd::AndElimR>(r.value().instrs[2]));

    // h_1 (= AndElimL of h) at index 1 holds φ_1.
    EXPECT_EQ(r.value().fact_step_table.at(facts[0]).idx, uint32_t{1});
    // AndElimR(h) at index 2 holds φ_2.
    EXPECT_EQ(r.value().fact_step_table.at(facts[1]).idx, uint32_t{2});
}

// =========================================================================
// Phase 4 Test: n = 4 → full chain shape; 7 ops.
//
//   [0] Assume(H = (((φ_1 ∧ φ_2) ∧ φ_3) ∧ φ_4))   = h = h_4
//   [1] AndElimL(h_4)                              = h_3
//   [2] AndElimL(h_3)                              = h_2
//   [3] AndElimL(h_2)                              = h_1 = φ_1   ← F_1 extract
//   [4] AndElimR(h_4)                              = φ_4         ← F_4 extract
//   [5] AndElimR(h_3)                              = φ_3         ← F_3 extract
//   [6] AndElimR(h_2)                              = φ_2         ← F_2 extract
// =========================================================================
void test_prelude_n4_shape_and_table() {
    Runtime rt;
    auto facts = setup_n_axioms(rt, 4);

    auto r = emit_prelude(rt.context(), facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    EXPECT_EQ(r.value().instrs.size(), size_t{7});       // 2n - 1
    EXPECT_TRUE(std::holds_alternative<nd::Assume>(r.value().instrs[0]));
    for (size_t i = 1; i <= 3; ++i) {
        EXPECT_TRUE(std::holds_alternative<nd::AndElimL>(r.value().instrs[i]));
    }
    for (size_t i = 4; i <= 6; ++i) {
        EXPECT_TRUE(std::holds_alternative<nd::AndElimR>(r.value().instrs[i]));
    }

    EXPECT_EQ(r.value().fact_step_table.at(facts[0]).idx, uint32_t{3});
    EXPECT_EQ(r.value().fact_step_table.at(facts[1]).idx, uint32_t{6});
    EXPECT_EQ(r.value().fact_step_table.at(facts[2]).idx, uint32_t{5});
    EXPECT_EQ(r.value().fact_step_table.at(facts[3]).idx, uint32_t{4});
}

// =========================================================================
// Phase 4 Test: AndElimL chain links correctly (each op refers to the
// previous step's index). Concrete check on the n=4 case:
//   AndElimL.of for [1] = StepRef{0}
//   AndElimL.of for [2] = StepRef{1}
//   AndElimL.of for [3] = StepRef{2}
//   AndElimR.of for [4] = StepRef{0}   (h_4)
//   AndElimR.of for [5] = StepRef{1}   (h_3)
//   AndElimR.of for [6] = StepRef{2}   (h_2)
// =========================================================================
void test_prelude_n4_link_indices() {
    Runtime rt;
    auto facts = setup_n_axioms(rt, 4);

    auto r = emit_prelude(rt.context(), facts);
    if (!r.ok()) { ++g_failed; return; }
    const auto& instrs = r.value().instrs;

    auto andl = [&](size_t at, uint32_t of) {
        const auto* op = std::get_if<nd::AndElimL>(&instrs[at]);
        EXPECT_TRUE(op != nullptr);
        if (op) EXPECT_EQ(op->of.idx, of);
    };
    auto andr = [&](size_t at, uint32_t of) {
        const auto* op = std::get_if<nd::AndElimR>(&instrs[at]);
        EXPECT_TRUE(op != nullptr);
        if (op) EXPECT_EQ(op->of.idx, of);
    };
    andl(1, 0); andl(2, 1); andl(3, 2);
    andr(4, 0); andr(5, 1); andr(6, 2);
}

// =========================================================================
// Phase 4 Test: end-to-end — synthesise a tiny proof that uses the
// prelude to derive an axiom from H, then qed. NDVerifier accepts.
// Wrapped goal = H → φ_{F₁} where H = φ_{F₁} ∧ φ_{F₂}.
// =========================================================================
void test_prelude_synthetic_proof_verifies() {
    Runtime rt;
    auto facts = setup_n_axioms(rt, 2);

    auto r = emit_prelude(rt.context(), facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) return;

    // Build a proof: prelude + ImpliesIntro(F_1's extract step) + Qed.
    Program<nd::Instr> prog;
    prog.claim_name = "wrapped_F1";
    for (const auto& op : r.value().instrs) prog.instrs.push_back(op);

    nd::ImpliesIntro ii{};
    ii.conclusion = r.value().fact_step_table.at(facts[0]);
    uint32_t ii_idx = static_cast<uint32_t>(prog.instrs.size());
    prog.instrs.emplace_back(nd::Instr{std::move(ii)});

    nd::Qed q{};
    q.derived = StepRef{ii_idx};
    prog.instrs.emplace_back(nd::Instr{std::move(q)});

    // The wrapped_goal = H → φ_{F₁}.
    FormulaBuilder builder(rt.context());
    FormulaHandle wrapped = builder.make_implies(
        r.value().H.get().root(),
        facts[0].get().root());

    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = prog;
    auto vr = v.verify(rt.context(), wrapped, p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "synthetic-prelude verify failed: " << vr.error().to_string() << "\n";
    }
}

// =========================================================================
// Phase 5 — emit_body_with_remap
// =========================================================================
//
// Run the full Stage 1 sub-pipeline (schema_macro → compute_facts →
// emit_prelude → emit_body) on a synthetic ND proof, then concatenate
// prelude + body + postlude (ImpliesIntro + Qed) and verify under
// NDVerifier against H → φ.
//
// This is the "real" integration shape of Stage 1 minus the apply()
// orchestrator (Phase 6).
struct WrapResult {
    Program<nd::Instr> prog;
    SentenceHandle     wrapped_goal;   // H → φ (or φ if facts empty)
};

util::Result<WrapResult> wrap_or_fail(
    Runtime& rt,
    const Program<nd::Instr>& input_body,
    FormulaHandle goal)
{
    auto& ctx = rt.context();

    // Schema macro (Phases 2/3).
    auto sm = schema_macro(ctx, input_body);
    if (!sm.ok()) return sm.error();

    // Facts closure (Phase 1).
    auto facts_r = compute_transitive_facts(sm.value().proof, ctx, TheoremFactsMap{});
    if (!facts_r.ok()) return facts_r.error();
    auto facts = std::move(facts_r).unwrap();

    // Prelude (Phase 4).
    auto pre = emit_prelude(ctx, facts);
    if (!pre.ok()) return pre.error();
    uint32_t prelude_len = static_cast<uint32_t>(pre.value().instrs.size());

    // Body emit (Phase 5).
    auto bd = emit_body_with_remap(
        sm.value().proof, pre.value().fact_step_table, prelude_len);
    if (!bd.ok()) return bd.error();

    // Stitch: prelude + body + ImpliesIntro + Qed (if facts non-empty).
    WrapResult result;
    result.prog.claim_name = input_body.claim_name + "_wrapped";
    for (auto& op : pre.value().instrs) result.prog.instrs.push_back(op);
    for (auto& op : bd.value().instrs)  result.prog.instrs.push_back(op);

    FormulaBuilder builder(ctx);
    if (facts.empty()) {
        // Identity case: no wrap. wrapped_goal = original φ. Body's qed_target
        // still discharges via a fresh Qed (no ImpliesIntro).
        nd::Qed qedop{};
        qedop.derived = bd.value().qed_target;
        result.prog.instrs.emplace_back(nd::Instr{std::move(qedop)});
        result.wrapped_goal = ctx.add_sentence(Sentence(goal));
    } else {
        nd::ImpliesIntro ii{};
        ii.conclusion = bd.value().qed_target;
        uint32_t ii_idx = static_cast<uint32_t>(result.prog.instrs.size());
        result.prog.instrs.emplace_back(nd::Instr{std::move(ii)});

        nd::Qed qedop{};
        qedop.derived = StepRef{ii_idx};
        result.prog.instrs.emplace_back(nd::Instr{std::move(qedop)});

        FormulaHandle H_to_phi = builder.make_implies(
            pre.value().H.get().root(), goal);
        result.wrapped_goal = ctx.add_sentence(Sentence(H_to_phi));
    }
    return result;
}

// =========================================================================
// Phase 5 Test: no Use ops — body emitter copies through with offset.
// Proof of `p -> p` via assume + implies_intro + qed.
// =========================================================================
void test_body_no_use_passthrough() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> body = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("p_self");
    if (!claim.has_value()) { ++g_failed; return; }
    FormulaHandle goal = claim.value().get().root();

    auto wr = wrap_or_fail(rt, body, goal);
    EXPECT_TRUE(wr.ok());
    if (!wr.ok()) return;

    // Facts empty → identity wrap. wrapped_goal = goal; body unchanged
    // except Qed (which the emitter dropped and we re-emit).
    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = wr.value().prog;
    auto vr = v.verify(rt.context(), wr.value().wrapped_goal.get().root(), p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) {
        std::cerr << "verify: " << vr.error().to_string() << "\n";
    }
}

// =========================================================================
// Phase 5 Test: single axiom Use — Use op dropped, downstream Qed-ref
// aliased to prelude extract; wrapped_goal = a_pred → a_pred verifies.
// =========================================================================
void test_body_single_axiom_use_dropped() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim derive_a: a_pred
        proof derive_a:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> body = lower_or_die(parsed.value().proofs[0], rt.context());
    EXPECT_EQ(body.instrs.size(), size_t{2});  // Use + Qed
    auto claim = rt.context().find_claim("derive_a");
    FormulaHandle goal = claim.value().get().root();

    auto wr = wrap_or_fail(rt, body, goal);
    EXPECT_TRUE(wr.ok());
    if (!wr.ok()) return;

    // Body had one Use + one Qed. After Stage 1:
    //   prelude: 1 op (Assume(H = a_pred))
    //   body: empty (Use dropped, Qed dropped)
    //   postlude: ImpliesIntro + Qed = 2 ops
    // Total: 3 ops.
    EXPECT_EQ(wr.value().prog.instrs.size(), size_t{3});

    // Verify against wrapped_goal = a_pred → a_pred.
    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = wr.value().prog;
    auto vr = v.verify(rt.context(), wr.value().wrapped_goal.get().root(), p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << "verify: " << vr.error().to_string() << "\n";
}

// =========================================================================
// Phase 5 Test: Use consumed by another op — that op's StepRef arg
// must be remapped to the prelude extract.
//   axiom a_ax: a_pred
//   axiom b_ax: b_pred
//   claim ab: a_pred & b_pred
//   proof ab:
//     h1 = use a_ax
//     h2 = use b_ax
//     h_and = and_intro h1, h2    # consumers of dropped Uses
//     qed h_and
// =========================================================================
void test_body_use_consumed_by_andintro() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        axiom b_ax: b_pred
        claim ab: a_pred & b_pred
        proof ab:
            h1 = use a_ax
            h2 = use b_ax
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> body = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("ab");
    FormulaHandle goal = claim.value().get().root();

    auto wr = wrap_or_fail(rt, body, goal);
    EXPECT_TRUE(wr.ok());
    if (!wr.ok()) {
        std::cerr << "wrap: " << wr.error().to_string() << "\n";
        return;
    }

    // Body has 4 ops (Use, Use, AndIntro, Qed). 2 axioms → prelude is
    // 2n-1 = 3 ops. After Stage 1:
    //   prelude: 3 ops (Assume + AndElimL + AndElimR)
    //   body:    1 op  (AndIntro; both Uses dropped, Qed dropped)
    //   postlude: 2 ops (ImpliesIntro + Qed)
    // Total: 6 ops.
    EXPECT_EQ(wr.value().prog.instrs.size(), size_t{6});

    // The AndIntro should be at output index 3 (right after prelude),
    // and its StepRef args should point at prelude extract indices.
    const auto* ai = std::get_if<nd::AndIntro>(&wr.value().prog.instrs[3]);
    EXPECT_TRUE(ai != nullptr);
    if (ai) {
        // Both a and b must point INTO the prelude (idx < 3).
        EXPECT_TRUE(ai->a.idx < 3);
        EXPECT_TRUE(ai->b.idx < 3);
    }

    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = wr.value().prog;
    auto vr = v.verify(rt.context(), wr.value().wrapped_goal.get().root(), p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << "verify: " << vr.error().to_string() << "\n";
}

// =========================================================================
// Phase 5 Test: same axiom used twice → both Use ops drop to the SAME
// prelude extract (dedup at the SentenceHandle level).
// =========================================================================
void test_body_use_dedup_aliases() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim a_and_a: a_pred & a_pred
        proof a_and_a:
            h1 = use a_ax
            h2 = use a_ax
            h_and = and_intro h1, h2
            qed h_and
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> body = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("a_and_a");
    FormulaHandle goal = claim.value().get().root();

    auto wr = wrap_or_fail(rt, body, goal);
    EXPECT_TRUE(wr.ok());
    if (!wr.ok()) return;

    // 1 fact → prelude size = 1 (just Assume). Body: 1 AndIntro.
    // Postlude: 2 (ImpliesIntro + Qed). Total = 4.
    EXPECT_EQ(wr.value().prog.instrs.size(), size_t{4});

    const auto* ai = std::get_if<nd::AndIntro>(&wr.value().prog.instrs[1]);
    EXPECT_TRUE(ai != nullptr);
    if (ai) {
        // Both args alias to the SAME prelude step (the Assume itself,
        // index 0, since for n=1 there's no and_elim chain).
        EXPECT_EQ(ai->a.idx, ai->b.idx);
        EXPECT_EQ(ai->a.idx, uint32_t{0});
    }

    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = wr.value().prog;
    auto vr = v.verify(rt.context(), wr.value().wrapped_goal.get().root(), p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << "verify: " << vr.error().to_string() << "\n";
}

// =========================================================================
// Phase 5 Test: SchemaInst input-gate rejection. emit_body_with_remap
// expects schema_macro to have run upstream — feed it a body that
// still contains SchemaInst → error.
// =========================================================================
void test_body_schema_inst_rejected() {
    Runtime rt;
    Program<nd::Instr> body;
    body.claim_name = "bad";
    nd::SchemaInst si{};
    body.instrs.push_back(nd::Instr{si});
    nd::Qed q{}; q.derived = StepRef{0};
    body.instrs.push_back(nd::Instr{q});

    std::unordered_map<SentenceHandle, StepRef, SentenceHandleHash> empty_table;
    auto r = emit_body_with_remap(body, empty_table, /*prelude_length=*/0);
    EXPECT_ERR(r);
}

// =========================================================================
// Phase 5 Test: Use whose SentenceHandle is missing from the table → error.
// =========================================================================
void test_body_unknown_use_rejected() {
    Runtime rt;
    rt.load("axiom a_ax: a_pred");
    auto sh = rt.context().find_known("a_ax").value();

    Program<nd::Instr> body;
    body.claim_name = "bad";
    nd::Use u{}; u.axiom = AxiomRef{sh}; u.source_name = "a_ax";
    body.instrs.push_back(nd::Instr{u});
    nd::Qed q{}; q.derived = StepRef{0};
    body.instrs.push_back(nd::Instr{q});

    // table is empty — caller's bug.
    std::unordered_map<SentenceHandle, StepRef, SentenceHandleHash> empty_table;
    auto r = emit_body_with_remap(body, empty_table, /*prelude_length=*/0);
    EXPECT_ERR(r);
}

// =========================================================================
// Phase 5 Test: a proof with first-order quantifier work in the body
// — Fix, forall_elim, forall_intro — verifies through the full Stage 1
// sub-pipeline. Exercises TermRef offsetting too.
//   axiom all_p: forall x. p(x)
//   claim derive: forall x. p(x)
//   proof derive:
//     fix y
//     h1 = use all_p
//     h2 = forall_elim h1, y
//     h_all = forall_intro h2
//     qed h_all
// =========================================================================
void test_body_with_quantifiers() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom all_p: forall x. p(x)
        claim derive: forall x. p(x)
        proof derive:
            fix y
            h1 = use all_p
            h2 = forall_elim h1, y
            h_all = forall_intro h2
            qed h_all
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> body = lower_or_die(parsed.value().proofs[0], rt.context());
    auto claim = rt.context().find_claim("derive");
    FormulaHandle goal = claim.value().get().root();

    auto wr = wrap_or_fail(rt, body, goal);
    EXPECT_TRUE(wr.ok());
    if (!wr.ok()) {
        std::cerr << "wrap: " << wr.error().to_string() << "\n";
        return;
    }

    nd::NDVerifier v;
    Proof p{}; p.system = System::ND; p.body = wr.value().prog;
    auto vr = v.verify(rt.context(), wr.value().wrapped_goal.get().root(), p);
    EXPECT_TRUE(vr.ok());
    if (!vr.ok()) std::cerr << "verify: " << vr.error().to_string() << "\n";
}

// =========================================================================
// Phase 6 — apply (end-to-end orchestrator)
// =========================================================================
//
// Identity case (no facts): wrapped_goal == original φ, no
// ImpliesIntro. Output gate accepts.
void test_apply_identity_no_facts() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim p_self: p -> p
        proof p_self:
            h = assume p
            h2 = implies_intro h
            qed h2
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> input = lower_or_die(parsed.value().proofs[0], rt.context());
    FormulaHandle goal = rt.context().find_claim("p_self").value().get().root();

    auto r = apply(rt.context(), input, goal, TheoremFactsMap{});
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << "apply: " << r.error().to_string() << "\n"; return; }

    // facts empty → wrapped_goal's formula equals the original goal.
    EXPECT_TRUE(r.value().facts.empty());
    EXPECT_EQ(r.value().wrapped_goal.get().root(), goal);
}

// =========================================================================
// Single-axiom wrap: facts = {a_ax}, wrapped_goal = a_pred → a_pred.
void test_apply_single_axiom() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim derive_a: a_pred
        proof derive_a:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> input = lower_or_die(parsed.value().proofs[0], rt.context());
    FormulaHandle goal = rt.context().find_claim("derive_a").value().get().root();
    SentenceHandle a_sh = rt.context().find_known("a_ax").value();

    auto r = apply(rt.context(), input, goal, TheoremFactsMap{});
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << "apply: " << r.error().to_string() << "\n"; return; }

    EXPECT_EQ(r.value().facts.size(), size_t{1});
    EXPECT_EQ(r.value().facts[0], a_sh);
    // wrapped_goal's formula is an Implies whose left = a_pred, right = a_pred.
    const auto& f = r.value().wrapped_goal.get().root().get();
    EXPECT_TRUE(f.is_compound());
    if (f.is_compound()) {
        EXPECT_TRUE(f.as_compound().op == Op::Implies);
    }
}

// =========================================================================
// Theorem citation: previously proved t1 (with facts {a_ax}) gets cited
// by a new proof; apply pulls in the transitive closure {a_ax, t1}.
void test_apply_theorem_with_axioms() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        axiom a_ax: a_pred
        claim t1: a_pred
        proof t1:
            h = use a_ax
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    auto t1_claim = rt.context().find_claim("t1").value();
    rt.context().add_theorem("t1", t1_claim);
    SentenceHandle t1_sh = rt.context().find_known("t1").value();
    SentenceHandle a_sh  = rt.context().find_known("a_ax").value();

    // Populate facts(t1) in the map (mirrors what the runner would do
    // after Stage 1 ran on t1's proof itself).
    TheoremFactsMap thm_facts;
    thm_facts.put(t1_sh, {a_sh});

    auto parsed2 = rt.load_with_proofs(R"(
        claim derive_a_via_t1: a_pred
        proof derive_a_via_t1:
            h = use t1
            qed h
    )");
    if (!parsed2.ok()) { ++g_failed; return; }
    Program<nd::Instr> input = lower_or_die(parsed2.value().proofs[0], rt.context());
    // Note: t1 and a_ax share the same formula (a_pred), so they alias
    // to the same SentenceHandle. closure dedups to one fact in this
    // pathological case. wrap structure is still valid.
    FormulaHandle goal = rt.context().find_claim("derive_a_via_t1").value().get().root();

    auto r = apply(rt.context(), input, goal, thm_facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << "apply: " << r.error().to_string() << "\n"; return; }
    // 1 fact (the shared SH).
    EXPECT_EQ(r.value().facts.size(), size_t{1});
}

// =========================================================================
// Theorem chain with structurally-distinct formulas. t2 (cites t1)
// gets wrapped; transitive closure = {a_ax, b_to_c, c_to_d, t1, t2}.
void test_apply_theorem_chain_distinct() {
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
    auto t1_c = rt.context().find_claim("t1").value();
    auto t2_c = rt.context().find_claim("t2").value();
    rt.context().add_theorem("t1", t1_c);
    rt.context().add_theorem("t2", t2_c);

    SentenceHandle sh_a   = rt.context().find_known("a_ax").value();
    SentenceHandle sh_bc  = rt.context().find_known("b_to_c").value();
    SentenceHandle sh_cd  = rt.context().find_known("c_to_d").value();
    SentenceHandle sh_t1  = rt.context().find_known("t1").value();

    TheoremFactsMap thm_facts;
    thm_facts.put(sh_t1, {sh_a, sh_bc});

    auto parsed2 = rt.load_with_proofs(R"(
        claim use_t2: a_pred -> d_pred
        proof use_t2:
            h = use t2
            qed h
    )");
    if (!parsed2.ok()) { ++g_failed; return; }

    // t2's facts in the map.
    SentenceHandle sh_t2 = rt.context().find_known("t2").value();
    thm_facts.put(sh_t2, {sh_a, sh_bc, sh_cd, sh_t1});

    Program<nd::Instr> input = lower_or_die(parsed2.value().proofs[0], rt.context());
    FormulaHandle goal = rt.context().find_claim("use_t2").value().get().root();

    auto r = apply(rt.context(), input, goal, thm_facts);
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << "apply: " << r.error().to_string() << "\n"; return; }
    EXPECT_EQ(r.value().facts.size(), size_t{5});
}

// =========================================================================
// Schema in body: the open-instance ForallElim chain composes through
// apply; wrapped goal verifies.
void test_apply_with_schema() {
    Runtime rt;
    setup_unary_self_impl(rt);
    auto parsed = rt.load_with_proofs(R"(
        claim use_inst: forall x. (q(x) -> q(x))
        proof use_inst:
            h = schema_inst unary_self_impl { P: \y. q(y) }
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }
    Program<nd::Instr> input = lower_or_die(parsed.value().proofs[0], rt.context());
    FormulaHandle goal = rt.context().find_claim("use_inst").value().get().root();

    auto r = apply(rt.context(), input, goal, TheoremFactsMap{});
    EXPECT_TRUE(r.ok());
    if (!r.ok()) { std::cerr << "apply: " << r.error().to_string() << "\n"; return; }
    // The schema instance is the single fact (closed φᵢ = goal itself).
    EXPECT_EQ(r.value().facts.size(), size_t{1});
    EXPECT_EQ(r.value().facts[0].get().root(), goal);
}

// =========================================================================
// Output gate: confirm inner-pass errors propagate. Use the
// compute_transitive_facts missing-theorem error path — a proof cites
// a theorem T, but T is absent from the TheoremFactsMap. apply must
// return an Error naming the responsible sub-pass.
void test_apply_propagates_inner_error() {
    Runtime rt;
    auto parsed = rt.load_with_proofs(R"(
        claim t_missing: p
        proof t_missing:
            h = assume p
            qed h
    )");
    if (!parsed.ok()) { ++g_failed; return; }

    // Promote t_missing as a theorem so the citation in the next proof
    // can lower; but DELIBERATELY omit it from the map.
    auto t_c = rt.context().find_claim("t_missing").value();
    rt.context().add_theorem("t_missing", t_c);

    auto parsed2 = rt.load_with_proofs(R"(
        claim use_missing: p
        proof use_missing:
            h = use t_missing
            qed h
    )");
    if (!parsed2.ok()) { ++g_failed; return; }
    Program<nd::Instr> input = lower_or_die(parsed2.value().proofs[0], rt.context());
    FormulaHandle goal = rt.context().find_claim("use_missing").value().get().root();

    TheoremFactsMap empty_map;        // does NOT contain t_missing
    auto r = apply(rt.context(), input, goal, empty_map);
    EXPECT_ERR(r);
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
    test_macro_output_verifies();

    // Phase 3: schema_macro (open instances — universal closure + ForallElim chain)
    test_macro_open_instance_one_fixed();
    test_macro_open_instance_two_fixed();
    test_macro_mixed_closed_and_open();

    // Phase 4: emit_prelude (Assume(H) + and_elim chain)
    test_prelude_empty();
    test_prelude_n1();
    test_prelude_n2();
    test_prelude_n4_shape_and_table();
    test_prelude_n4_link_indices();
    test_prelude_synthetic_proof_verifies();

    // Phase 5: emit_body_with_remap (drops Use+Qed, offsets others)
    test_body_no_use_passthrough();
    test_body_single_axiom_use_dropped();
    test_body_use_consumed_by_andintro();
    test_body_use_dedup_aliases();
    test_body_schema_inst_rejected();
    test_body_unknown_use_rejected();
    test_body_with_quantifiers();

    // Phase 6: apply (end-to-end orchestrator + output gate)
    test_apply_identity_no_facts();
    test_apply_single_axiom();
    test_apply_theorem_with_axioms();
    test_apply_theorem_chain_distinct();
    test_apply_with_schema();
    test_apply_propagates_inner_error();

    std::cerr << "nd_internalize_test: " << g_passed
              << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
