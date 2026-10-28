// Phase 7 end-to-end tests (ELIMINATION_DEMANDS_DESIGN.md §7). Each case also
// checks that NDtoCompactLKR expands to NDtoLKR's program (Theorem E1).

#include "lkr_ops_equal.h"

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr_build/expand.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <cstddef>
#include <iostream>
#include <string>
#include <variant>

using namespace logic;
using namespace logic::proof;
using logic::proof::lkr_build::ExpandIdentities;
namespace lkr_build = logic::proof::lkr_build;
using logic::proof::translate::nd_to_lkr::NDtoCompactLKR;
using logic::proof::translate::nd_to_lkr::NDtoLKR;
using logic::proof::translate::nd_to_lkr::Options;

namespace {

int g_passed = 0;
int g_failed = 0;

void fail(const std::string& name, const std::string& why) {
    std::cerr << "FAIL [" << name << "]: " << why << "\n";
    ++g_failed;
}

struct Run {
    bool                              ok{false};
    std::string                       error;
    Program<lkr::Instr>               prog;
    Program<lkr_build::CompactInstr>  compact;
};

Run translate(const char* src, const char* claim, Options options) {
    Run run;
    Runtime rt;
    auto parsed = rt.load_with_proofs(src);
    if (!parsed.ok()) {
        run.error = "load: " + parsed.error().to_string();
        return run;
    }
    auto lowered = nd::lower(parsed.value().proofs[0], rt.context());
    if (!lowered.ok()) {
        run.error = "lower: " + lowered.error().to_string();
        return run;
    }
    auto goal = rt.context().find_claim(claim);
    if (!goal.has_value()) {
        run.error = std::string("claim not found: ") + claim;
        return run;
    }
    FormulaHandle goal_formula = goal.value().get().root();
    NDtoLKR pass(rt.context(), goal_formula, options);
    auto out = pass.apply(lowered.value());
    if (!out.ok()) {
        run.error = out.error().to_string();
        return run;
    }
    run.prog = std::move(out).unwrap();

    NDtoCompactLKR compact_pass(rt.context(), goal_formula, options);
    auto compact = compact_pass.apply(lowered.value());
    if (!compact.ok()) {
        run.error = "compact: " + compact.error().to_string();
        return run;
    }
    auto expanded =
        ExpandIdentities(rt.context(), goal_formula).apply(compact.value());
    if (!expanded.ok()) {
        run.error = "expand: " + expanded.error().to_string();
        return run;
    }
    std::string diff = lkr_ops_equal::first_difference(
        expanded.value().instrs, run.prog.instrs);
    if (!diff.empty()) {
        run.error = "E(compact) != LKR: " + diff;
        return run;
    }
    run.compact = std::move(compact).unwrap();
    run.ok = true;
    return run;
}

template <typename Op>
size_t count_ops(const Program<lkr::Instr>& prog) {
    size_t n = 0;
    for (const auto& instr : prog.instrs) {
        if (std::holds_alternative<Op>(instr)) ++n;
    }
    return n;
}

Options unshared() { return Options{}; }
Options shared() { Options o; o.share = true; return o; }

void expect_translates(const char* name, const char* src, const char* claim) {
    for (Options options : {unshared(), shared()}) {
        Run run = translate(src, claim, options);
        std::string mode = options.share ? " (share)" : "";
        if (!run.ok) { fail(name + mode, run.error); continue; }
        ++g_passed;
    }
}

void expect_cuts(const char* name, const char* src, const char* claim,
                 size_t cuts) {
    expect_translates(name, src, claim);
    Run run = translate(src, claim, unshared());
    if (!run.ok) return;
    size_t got = count_ops<lkr::Cut>(run.prog);
    if (got != cuts) {
        fail(name, "expected " + std::to_string(cuts) + " Cut(s), got " +
                   std::to_string(got));
        return;
    }
    ++g_passed;
}

void expect_rejected(const char* name, const char* src, const char* claim,
                     const char* substr) {
    for (Options options : {unshared(), shared()}) {
        Run run = translate(src, claim, options);
        std::string mode = options.share ? " (share)" : "";
        if (run.ok) { fail(name + mode, "expected rejection"); continue; }
        if (run.error.find(substr) == std::string::npos) {
            fail(name + mode, "error lacks '" + std::string(substr) +
                              "': " + run.error);
            continue;
        }
        ++g_passed;
    }
}

// G1: ∀-detour (Lemma S2).

void test_g1_detour() {
    expect_cuts("g1_detour", R"(
        claim t1: forall y. (p(y) -> p(y))
        proof t1:
            fix x
            a = assume p(x)
            i = implies_intro a
            fa = forall_intro i
            fix z
            inst = forall_elim fa, z
            fz = forall_intro inst
            qed fz
    )", "t1", 0);
}

void test_g1_detour_with_body_elims() {
    expect_cuts("g1_detour_with_body_elims", R"(
        claim t3: forall x. (p(x) -> forall y. ((p(y) & (p(y) -> q(y))) -> q(y)))
        proof t3:
            fix u
            h = assume (p(u) & (p(u) -> q(u)))
            hp = and_elim_l h
            hpq = and_elim_r h
            hq = implies_elim hpq, hp
            i = implies_intro hq
            fa = forall_intro i
            fix x
            px = assume p(x)
            fix y
            inst = forall_elim fa, y
            fy = forall_intro inst
            ix = implies_intro fy
            fx = forall_intro ix
            qed fx
    )", "t3", 0);
}

void test_g1_two_instances() {
    expect_cuts("g1_two_instances", R"(
        claim two: forall a. forall b. (r(a, b) -> r(a, b))
        proof two:
            fix x
            fix y
            h = assume r(x, y)
            i = implies_intro h
            fy = forall_intro i
            fx = forall_intro fy
            fix a
            fix b
            ia = forall_elim fx, a
            ib = forall_elim ia, b
            gb = forall_intro ib
            ga = forall_intro gb
            qed ga
    )", "two", 0);
}

void test_g1_instance_then_and_left() {
    expect_cuts("g1_instance_then_and_left", R"(
        axiom all_p: forall x. p(x)
        axiom all_q: forall x. q(x)
        claim inst_and: forall y. p(y)
        proof inst_and:
            fix x
            ap = use all_p
            px = forall_elim ap, x
            aq = use all_q
            qx = forall_elim aq, x
            pq = and_intro px, qx
            fa = forall_intro pq
            fix y
            inst = forall_elim fa, y
            py = and_elim_l inst
            fy = forall_intro py
            qed fy
    )", "inst_and", 1);
}

// G2: fresh eigenvariables.

void test_g2_sibling_fix_reuse() {
    expect_cuts("g2_sibling_fix_reuse", R"(
        claim s3: forall y. (q(y) -> (q(y) & forall x. (p(x) -> p(x))))
        proof s3:
            fix x
            a = assume p(x)
            i = implies_intro a
            fa = forall_intro i
            fix y
            b = assume q(y)
            c = and_intro b, fa
            ib = implies_intro c
            fy = forall_intro ib
            qed fy
    )", "s3", 0);
}

void test_g2_witness_level_reused_by_fix() {
    expect_translates("g2_witness_level_reused_by_fix", R"(
        axiom ex: exists x. p(x)
        claim wr: forall y. (q(y) -> (q(y) & exists x. p(x)))
        proof wr:
            e = use ex
            w = exists_elim e, v
            ei = exists_intro w, v
            cl = exists_intro ei
            fix y
            b = assume q(y)
            c = and_intro b, cl
            ib = implies_intro c
            fy = forall_intro ib
            qed fy
    )", "wr");
}

// G3: ⊥ results.

void test_g3_not_elim_under_implies_intro() {
    expect_translates("g3_not_elim_under_implies_intro", R"(
        claim b1: (~p & p) -> q
        proof b1:
            h = assume (~p & p)
            np = and_elim_l h
            p0 = and_elim_r h
            a = assume p
            bot = not_elim np, a
            f = implies_intro bot
            bot2 = implies_elim f, p0
            qf = let q
            hq = bottom_elim bot2, qf
            r = implies_intro hq
            qed r
    )", "b1");
}

void test_g3_assume_bottom() {
    expect_cuts("g3_assume_bottom", R"(
        claim b2: false -> q
        proof b2:
            h = assume false
            qf = let q
            hq = bottom_elim h, qf
            r = implies_intro hq
            qed r
    )", "b2", 0);
}

void test_g3_bottom_from_implies_elim() {
    expect_cuts("g3_bottom_from_implies_elim", R"(
        claim b3: (p -> false) -> ~p
        proof b3:
            h = assume p -> false
            a = assume p
            bot = implies_elim h, a
            n = not_intro bot
            r = implies_intro n
            qed r
    )", "b3", 0);
}

void test_g3_bottom_from_or_elim() {
    expect_cuts("g3_bottom_from_or_elim", R"(
        claim b4: (p | q) -> ((p -> false) -> ((q -> false) -> false))
        proof b4:
            h = assume p | q
            hp = assume p -> false
            hq = assume q -> false
            bot = or_elim h, hp, hq
            r3 = implies_intro bot
            r2 = implies_intro r3
            r1 = implies_intro r2
            qed r1
    )", "b4", 0);
}

void test_g3_bottom_from_exists_elim() {
    expect_cuts("g3_bottom_from_exists_elim", R"(
        claim b5: (exists x. p(x)) -> ((forall x. ~p(x)) -> false)
        proof b5:
            h = assume exists x. p(x)
            n = assume forall x. ~p(x)
            w = exists_elim h, v
            nv = forall_elim n, v
            bot = not_elim nv, w
            cl = exists_intro bot
            r2 = implies_intro cl
            r1 = implies_intro r2
            qed r1
    )", "b5", 0);
}

void test_g3_bottom_from_iff_elim() {
    expect_cuts("g3_bottom_from_iff_elim", R"(
        claim b6: (p <-> false) -> ~p
        proof b6:
            h = assume p <-> false
            a = assume p
            bot = iff_elim_l h, a
            n = not_intro bot
            r = implies_intro n
            qed r
    )", "b6", 0);
}

void test_g3_bottom_by_projection() {
    expect_cuts("g3_bottom_by_projection", R"(
        claim b7: (forall x. (false & p(x))) -> forall y. q
        proof b7:
            h = assume forall x. (false & p(x))
            fix y
            hy = forall_elim h, y
            bot = and_elim_l hy
            qf = let q
            hq = bottom_elim bot, qf
            fy = forall_intro hq
            r = implies_intro fy
            qed r
    )", "b7", 0);
}

void test_g3_classical_absurd_concluding_bottom() {
    expect_cuts("g3_classical_absurd_concluding_bottom", R"(
        claim b8: (p & ~p) -> false
        proof b8:
            h = assume (p & ~p)
            n = assume ~false
            hp = and_elim_l h
            hn = and_elim_r h
            bot = not_elim hn, hp
            ca = classical_absurd bot
            r = implies_intro ca
            qed r
    )", "b8", 0);
}

// G4: closers under demand.

void test_g4_classical_absurd_then_forall_elim() {
    expect_cuts("g4_classical_absurd_then_forall_elim", R"(
        claim d1: ~~(forall x. p(x)) -> forall y. p(y)
        proof d1:
            h = assume ~~(forall x. p(x))
            n = assume ~(forall x. p(x))
            bot = not_elim h, n
            ca = classical_absurd bot
            fix y
            py = forall_elim ca, y
            fy = forall_intro py
            r = implies_intro fy
            qed r
    )", "d1", 0);
}

void test_g4_classical_absurd_then_and_elim() {
    expect_cuts("g4_classical_absurd_then_and_elim", R"(
        claim d2: ~~(p & q) -> q
        proof d2:
            h = assume ~~(p & q)
            n = assume ~(p & q)
            bot = not_elim h, n
            ca = classical_absurd bot
            hq = and_elim_r ca
            r = implies_intro hq
            qed r
    )", "d2", 0);
}

void test_g4_not_intro_double_negation_then_forall_elim() {
    expect_cuts("g4_not_intro_double_negation_then_forall_elim", R"(
        claim d3: (forall x. p(x)) -> forall y. p(y)
        proof d3:
            h = assume forall x. p(x)
            n = assume ~(forall x. p(x))
            bot = not_elim n, h
            nn = not_intro bot
            dn = double_neg_elim nn
            fix y
            py = forall_elim dn, y
            fy = forall_intro py
            r = implies_intro fy
            qed r
    )", "d3", 0);
}

void test_g4_classical_absurd_then_implies_elim() {
    expect_cuts("g4_classical_absurd_then_implies_elim", R"(
        claim d4: ~~(p -> q) -> (p -> q)
        proof d4:
            h = assume ~~(p -> q)
            a = assume p
            n = assume ~(p -> q)
            bot = not_elim h, n
            ca = classical_absurd bot
            hq = implies_elim ca, a
            ia = implies_intro hq
            r = implies_intro ia
            qed r
    )", "d4", 1);
}

// G5: re-quantifying ∃E closer.

void test_g5_requantifying_exists_elim() {
    expect_cuts("g5_requantifying_exists_elim", R"(
        claim g5: (exists x. p(x)) -> ((forall x. (p(x) -> q(x))) -> exists x. q(x))
        proof g5:
            h = assume exists x. p(x)
            a = assume forall x. (p(x) -> q(x))
            w = exists_elim h, v
            av = forall_elim a, v
            qv = implies_elim av, w
            cl = exists_intro qv
            r2 = implies_intro cl
            r1 = implies_intro r2
            qed r1
    )", "g5", 0);
}

void test_g5_requantified_then_exists_elim() {
    expect_cuts("g5_requantified_then_exists_elim", R"(
        claim g5b: (exists x. p(x)) -> ((forall x. (p(x) -> q(x))) -> exists x. q(x))
        proof g5b:
            h = assume exists x. p(x)
            a = assume forall x. (p(x) -> q(x))
            w = exists_elim h, v
            av = forall_elim a, v
            qv = implies_elim av, w
            cl = exists_intro qv
            w2 = exists_elim cl, u
            e2 = exists_intro w2, u
            cl2 = exists_intro e2
            r2 = implies_intro cl2
            r1 = implies_intro r2
            qed r1
    )", "g5b", 1);
}

// G6 / I-4: references into closed blocks.

void test_g6_escaped_use_accepted() {
    expect_translates("g6_escaped_use_accepted", R"(
        axiom ap: p
        claim g6a: (forall x. (q(x) -> q(x))) & p
        proof g6a:
            fix x
            u = use ap
            a = assume q(x)
            i = implies_intro a
            fa = forall_intro i
            r = and_intro fa, u
            qed r
    )", "g6a");
}

void test_g6_escaped_assumption_rejected() {
    expect_rejected("g6_escaped_assumption_rejected", R"(
        axiom ap: p
        claim g6b: (q -> p) & p
        proof g6b:
            u = use ap
            a = assume q
            c = and_intro u, a
            d = and_elim_l c
            i = implies_intro d
            r = and_intro i, d
            qed r
    )", "g6b", "I-4 violation");
}

// Redexes (§2.2).

void test_redex_modus() {
    expect_cuts("redex_modus", R"(
        claim rm: p -> p
        proof rm:
            h = assume p
            a = assume p
            i = implies_intro a
            m = implies_elim i, h
            r = implies_intro m
            qed r
    )", "rm", 1);
}

void test_redex_refute() {
    expect_cuts("redex_refute", R"(
        claim rr: (p & ~p) -> false
        proof rr:
            h = assume (p & ~p)
            hp = and_elim_l h
            hn = and_elim_r h
            a = assume p
            bot0 = not_elim hn, a
            n = not_intro bot0
            bot = not_elim n, hp
            r = implies_intro bot
            qed r
    )", "rr", 1);
}

void test_redex_cases_or_intro() {
    expect_cuts("redex_cases_or_intro", R"(
        claim rc: p -> (q -> p)
        proof rc:
            h = assume p
            g = assume q
            qf = let q
            o = or_intro_l h, qf
            a1 = assume p
            i1 = implies_intro a1
            a2 = assume q
            i2 = implies_intro h
            c = or_elim o, i1, i2
            ig = implies_intro c
            r = implies_intro ig
            qed r
    )", "rc", 1);
}

void test_redex_witness() {
    expect_cuts("redex_witness", R"(
        claim rw: forall y. (p(y) -> exists x. p(x))
        proof rw:
            fix y
            h = assume p(y)
            e = exists_intro h, y
            w = exists_elim e, v
            ev = exists_intro w, v
            cl = exists_intro ev
            i = implies_intro cl
            fy = forall_intro i
            qed fy
    )", "rw", 1);
}

void test_redex_iff() {
    expect_cuts("redex_iff", R"(
        claim ri: (p -> q) -> ((q -> p) -> (p -> q))
        proof ri:
            hpq = assume p -> q
            hqp = assume q -> p
            hp = assume p
            hiff = iff_intro hpq, hqp
            hq = iff_elim_l hiff, hp
            r3 = implies_intro hq
            r2 = implies_intro r3
            r1 = implies_intro r2
            qed r1
    )", "ri", 0);
}

void test_excluded_middle_case_split() {
    expect_cuts("excluded_middle_case_split", R"(
        claim emc: q -> q
        proof emc:
            hq = assume q
            hl = let p
            em = excluded_middle hl
            a1 = assume p
            i1 = implies_intro hq
            a2 = assume ~p
            i2 = implies_intro hq
            c = or_elim em, i1, i2
            r = implies_intro c
            qed r
    )", "emc", 1);
}

void test_peirce_in_context() {
    expect_cuts("peirce_in_context", R"(
        claim pc: q -> (((p -> r) -> p) -> p)
        proof pc:
            a = assume q
            ha = let p
            hb = let r
            pe = peirce ha, hb
            i = implies_intro pe
            qed i
    )", "pc", 0);
}

// Census (§5.1): eliminations on hypotheses emit no Cut.

void test_census_modus_chain() {
    expect_cuts("census_modus_chain", R"(
        claim mc: (p -> (q -> r)) -> (p -> (q -> r))
        proof mc:
            h = assume p -> (q -> r)
            a = assume p
            b = assume q
            f = implies_elim h, a
            g = implies_elim f, b
            r3 = implies_intro g
            r2 = implies_intro r3
            r1 = implies_intro r2
            qed r1
    )", "mc", 0);
}

void test_census_or_elim_with_blocks() {
    expect_cuts("census_or_elim_with_blocks", R"(
        claim oe: (p | q) -> (q | p)
        proof oe:
            h = assume p | q
            a = assume p
            qf = let q
            o1 = or_intro_r qf, a
            i1 = implies_intro o1
            b = assume q
            pf = let p
            o2 = or_intro_l b, pf
            i2 = implies_intro o2
            c = or_elim h, i1, i2
            r = implies_intro c
            qed r
    )", "oe", 0);
}

void test_census_or_elim_step_free_tail() {
    expect_cuts("census_or_elim_step_free_tail", R"(
        claim of: (p | q) -> ((p -> forall x. r(x)) -> ((q -> forall x. r(x)) -> forall y. r(y)))
        proof of:
            h = assume p | q
            ha = assume p -> forall x. r(x)
            hb = assume q -> forall x. r(x)
            c = or_elim h, ha, hb
            fix y
            ry = forall_elim c, y
            fy = forall_intro ry
            r3 = implies_intro fy
            r2 = implies_intro r3
            r1 = implies_intro r2
            qed r1
    )", "of", 0);
}

void test_or_elim_step_carrying_tail() {
    expect_cuts("or_elim_step_carrying_tail", R"(
        claim ot: (p | q) -> ((p -> (r -> s)) -> ((q -> (r -> s)) -> (r -> s)))
        proof ot:
            h = assume p | q
            ha = assume p -> (r -> s)
            hb = assume q -> (r -> s)
            hr = assume r
            c = or_elim h, ha, hb
            hs = implies_elim c, hr
            r4 = implies_intro hs
            r3 = implies_intro r4
            r2 = implies_intro r3
            r1 = implies_intro r2
            qed r1
    )", "ot", 1);
}

void test_census_exists_elim_on_hypothesis() {
    expect_cuts("census_exists_elim_on_hypothesis", R"(
        claim ee: (exists x. (p(x) & q(x))) -> exists x. q(x)
        proof ee:
            h = assume exists x. (p(x) & q(x))
            w = exists_elim h, v
            qv = and_elim_r w
            e = exists_intro qv, v
            cl = exists_intro e
            r = implies_intro cl
            qed r
    )", "ee", 0);
}

void test_census_iff_elim_on_hypothesis() {
    expect_cuts("census_iff_elim_on_hypothesis", R"(
        claim ie: (p <-> q) -> (q -> p)
        proof ie:
            h = assume p <-> q
            b = assume q
            a = iff_elim_r h, b
            r2 = implies_intro a
            r1 = implies_intro r2
            qed r1
    )", "ie", 0);
}

// Re-entry (§2.4).

void test_witness_reentry() {
    expect_translates("witness_reentry", R"(
        axiom ex: exists x. p(x)
        claim re: a -> a
        proof re:
            h0 = assume a
            e = use ex
            w = exists_elim e, v
            aa = assume a
            ii = implies_intro aa
            c = exists_intro ii
            m = implies_elim c, h0
            x = implies_elim c, m
            r = implies_intro x
            qed r
    )", "re");
}

// Share mode (§5.2).

std::string chain_source(int k) {
    std::string src;
    for (int i = 1; i <= k; ++i) {
        src += "axiom h" + std::to_string(i) + ": (q" + std::to_string(i - 1) +
               " & q" + std::to_string(i - 1) + ") -> q" + std::to_string(i) +
               "\n";
    }
    src += "claim ch: q0 -> q" + std::to_string(k) + "\n";
    src += "proof ch:\n    s0 = assume q0\n";
    for (int i = 1; i <= k; ++i) {
        std::string n = std::to_string(i), p = std::to_string(i - 1);
        src += "    u" + n + " = use h" + n + "\n";
        src += "    c" + n + " = and_intro s" + p + ", s" + p + "\n";
        src += "    s" + n + " = implies_elim u" + n + ", c" + n + "\n";
    }
    src += "    r = implies_intro s" + std::to_string(k) + "\n    qed r\n";
    return src;
}

void test_share_chain_is_linear() {
    size_t shared_size[3];
    size_t unshared_size[3];
    const int ks[3] = {4, 8, 12};
    for (int j = 0; j < 3; ++j) {
        std::string src = chain_source(ks[j]);
        Run s = translate(src.c_str(), "ch", shared());
        Run u = translate(src.c_str(), "ch", unshared());
        if (!s.ok || !u.ok) {
            fail("share_chain_is_linear", s.ok ? u.error : s.error);
            return;
        }
        shared_size[j]   = s.prog.instrs.size();
        unshared_size[j] = u.prog.instrs.size();
    }
    if (shared_size[2] - shared_size[1] != shared_size[1] - shared_size[0]) {
        fail("share_chain_is_linear",
             "shared sizes not linear: " + std::to_string(shared_size[0]) +
             ", " + std::to_string(shared_size[1]) + ", " +
             std::to_string(shared_size[2]));
        return;
    }
    if (unshared_size[1] < 8 * unshared_size[0]) {
        fail("share_chain_is_linear",
             "unshared sizes not exponential: " +
             std::to_string(unshared_size[0]) + ", " +
             std::to_string(unshared_size[1]));
        return;
    }
    ++g_passed;
}

// Projections (§2.8).

std::string conjunct_uses(int n, int m) {
    std::string h = "q1";
    for (int i = 2; i <= n; ++i) h = "(" + h + " & q" + std::to_string(i) + ")";
    std::string goal = "q1";
    for (int i = 1; i < m; ++i) goal = "(" + goal + " & q1)";
    std::string src = "claim cu: " + h + " -> " + goal + "\nproof cu:\n";
    src += "    h = assume " + h + "\n";
    std::string prev = "h";
    for (int i = n; i >= 2; --i) {
        std::string step = "l" + std::to_string(i - 1);
        src += "    " + step + " = and_elim_l " + prev + "\n";
        prev = step;
    }
    std::string acc = prev;
    for (int i = 1; i < m; ++i) {
        std::string step = "c" + std::to_string(i);
        src += "    " + step + " = and_intro " + acc + ", " + prev + "\n";
        acc = step;
    }
    src += "    r = implies_intro " + acc + "\n    qed r\n";
    return src;
}

void test_projection_uses_are_constant() {
    size_t ops[2];
    const int ns[2] = {10, 20};
    for (int j = 0; j < 2; ++j) {
        std::string src = conjunct_uses(ns[j], 8);
        Run run = translate(src.c_str(), "cu", unshared());
        if (!run.ok) { fail("projection_uses_are_constant", run.error); return; }
        ops[j] = run.prog.instrs.size();
    }
    if (ops[1] - ops[0] > 2 * 10) {
        fail("projection_uses_are_constant",
             "10 more conjuncts cost " + std::to_string(ops[1] - ops[0]) +
             " more ops");
        return;
    }
    ++g_passed;
}

void test_projection_through_double_negation() {
    expect_cuts("projection_through_double_negation", R"(
        claim pd: ~~(p & q) -> (q & p)
        proof pd:
            h = assume ~~(p & q)
            d = double_neg_elim h
            a = and_elim_l d
            b = and_elim_r d
            c = and_intro b, a
            r = implies_intro c
            qed r
    )", "pd", 0);
}

void test_projection_of_witness() {
    expect_cuts("projection_of_witness", R"(
        claim pw: (exists x. (p(x) & q(x))) -> exists y. (q(y) & p(y))
        proof pw:
            h = assume exists x. (p(x) & q(x))
            w = exists_elim h, v
            a = and_elim_l w
            b = and_elim_r w
            c = and_intro b, a
            e = exists_intro c, v
            cl = exists_intro e
            r = implies_intro cl
            qed r
    )", "pw", 0);
}

void test_hypothesis_also_used_whole() {
    expect_cuts("hypothesis_also_used_whole", R"(
        claim hw: (p & q) -> (((p & q) -> r) -> (r & p))
        proof hw:
            h = assume p & q
            g = assume (p & q) -> r
            hr = implies_elim g, h
            a = and_elim_l h
            c = and_intro hr, a
            r2 = implies_intro c
            r1 = implies_intro r2
            qed r1
    )", "hw", 0);
}

void test_projection_of_aliased_hypothesis() {
    expect_translates("projection_of_aliased_hypothesis", R"(
        claim pa: s -> s
        proof pa:
            hs = assume s
            hl = let p & q
            em = excluded_middle hl
            a1 = assume p & q
            x1 = and_elim_l a1
            y1 = and_elim_r a1
            z1 = and_intro y1, x1
            i1 = implies_intro hs
            a2 = assume ~(p & q)
            i2 = implies_intro hs
            c = or_elim em, i1, i2
            r = implies_intro c
            qed r
    )", "pa");
}

// 100,000 chained ∧-detours translate on the default stack.
void test_deep_chain() {
    const int n = 100000;
    std::string src = "claim deep: p -> p\nproof deep:\n    s0 = assume p\n";
    for (int i = 1; i <= n; ++i) {
        std::string k = std::to_string(i), p = std::to_string(i - 1);
        src += "    c" + k + " = and_intro s" + p + ", s" + p + "\n";
        src += "    s" + k + " = and_elim_l c" + k + "\n";
    }
    src += "    r = implies_intro s" + std::to_string(n) + "\n    qed r\n";
    Run run = translate(src.c_str(), "deep", unshared());
    if (!run.ok) { fail("deep_chain", run.error); return; }
    ++g_passed;
}

void test_share_bottom_step_closes_block() {
    expect_translates("share_bottom_step_closes_block", R"(
        claim sb: (p & ~p) -> (q & r)
        proof sb:
            h = assume (p & ~p)
            hp = and_elim_l h
            hn = and_elim_r h
            bot = not_elim hn, hp
            qf = let q
            rf = let r
            q1 = bottom_elim bot, qf
            r1 = bottom_elim bot, rf
            c = and_intro q1, r1
            i = implies_intro c
            qed i
    )", "sb");
}

// Compact LKR (COMPACT_LKR_DESIGN.md).

void test_compact_identity_is_one_instruction() {
    Run run = translate(R"(
        claim ci: (p & q) -> (p & q)
        proof ci:
            a = assume (p & q)
            i = implies_intro a
            qed i
    )", "ci", unshared());
    if (!run.ok) { fail("compact_identity", run.error); return; }
    size_t identities = 0;
    for (const auto& instr : run.compact.instrs) {
        identities += std::holds_alternative<lkr_build::Identity>(instr);
    }
    if (run.compact.instrs.size() != 2 || identities != 1 ||
        run.prog.instrs.size() != 5) {
        fail("compact_identity",
             "expected [Or, Identity] expanding to 5 ops; got " +
             std::to_string(run.compact.instrs.size()) + " compact instrs (" +
             std::to_string(identities) + " identities), " +
             std::to_string(run.prog.instrs.size()) + " LKR ops");
        return;
    }
    ++g_passed;
}

}  // namespace

int main() {
    test_g1_detour();
    test_g1_detour_with_body_elims();
    test_g1_two_instances();
    test_g1_instance_then_and_left();

    test_g2_sibling_fix_reuse();
    test_g2_witness_level_reused_by_fix();

    test_g3_not_elim_under_implies_intro();
    test_g3_assume_bottom();
    test_g3_bottom_from_implies_elim();
    test_g3_bottom_from_or_elim();
    test_g3_bottom_from_exists_elim();
    test_g3_bottom_from_iff_elim();
    test_g3_bottom_by_projection();
    test_g3_classical_absurd_concluding_bottom();

    test_g4_classical_absurd_then_forall_elim();
    test_g4_classical_absurd_then_and_elim();
    test_g4_not_intro_double_negation_then_forall_elim();
    test_g4_classical_absurd_then_implies_elim();

    test_g5_requantifying_exists_elim();
    test_g5_requantified_then_exists_elim();

    test_g6_escaped_use_accepted();
    test_g6_escaped_assumption_rejected();

    test_redex_modus();
    test_redex_refute();
    test_redex_cases_or_intro();
    test_redex_witness();
    test_redex_iff();
    test_excluded_middle_case_split();
    test_peirce_in_context();

    test_census_modus_chain();
    test_census_or_elim_with_blocks();
    test_census_or_elim_step_free_tail();
    test_or_elim_step_carrying_tail();
    test_census_exists_elim_on_hypothesis();
    test_census_iff_elim_on_hypothesis();

    test_witness_reentry();

    test_share_chain_is_linear();
    test_share_bottom_step_closes_block();

    test_projection_uses_are_constant();
    test_projection_through_double_negation();
    test_projection_of_witness();
    test_hypothesis_also_used_whole();
    test_projection_of_aliased_hypothesis();

    test_deep_chain();

    test_compact_identity_is_one_instruction();

    std::cout << "nd_to_lkr_demands_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
