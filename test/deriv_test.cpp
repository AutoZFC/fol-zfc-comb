// deriv_test — build/emit round-trip for the sequent-carrying derivation IR
// (lkr_cut_elim/deriv.{h,cpp}), the foundation for Gentzen cut-elimination.
//
// Property (P0): for an LKR program `p` that LKRVerifier accepts against goal
// G, build(p) then emit() yields a program that ALSO verifies against G. No
// reductions yet — this validates that the IR faithfully captures every rule
// (Cut, CloseByLemma, And, Or, Forall, Exists, Weakening, …) and that emit's
// re-linearization (incl. Exists witness → TermRef remapping) is correct.
//
// Inputs are real NDtoLKR cut-spine programs so the round-trip covers the
// shapes the pipeline actually produces.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <iostream>
#include <string>

using namespace logic;
using namespace logic::proof;

namespace {

int g_passed = 0;
int g_failed = 0;

void round_trip(const char* label, const char* src, const char* claim_name) {
    Runtime rt;
    auto parsed = rt.load_with_proofs(src);
    if (!parsed.ok()) {
        std::cerr << "FAIL[" << label << "]: load: " << parsed.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto nd_prog = nd::lower(parsed.value().proofs[0], rt.context());
    if (!nd_prog.ok()) {
        std::cerr << "FAIL[" << label << "]: nd lower: " << nd_prog.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto claim = rt.context().find_claim(claim_name);
    if (!claim.has_value()) {
        std::cerr << "FAIL[" << label << "]: claim not found\n"; ++g_failed; return;
    }
    FormulaHandle goal = claim.value().get().root();

    translate::nd_to_lkr::NDtoLKR pass(rt.context(), goal);
    auto lkr_prog = pass.apply(nd_prog.value());
    if (!lkr_prog.ok()) {
        std::cerr << "FAIL[" << label << "]: nd_to_lkr: " << lkr_prog.error().to_string() << "\n";
        ++g_failed; return;
    }

    FormulaBuilder builder(rt.context());
    FormulaHandle goal_nnf = builder.to_nnf(goal);

    auto deriv = translate::lkr_cut_elim::build(builder, goal_nnf, lkr_prog.value());
    if (!deriv.ok()) {
        std::cerr << "FAIL[" << label << "]: build: " << deriv.error().to_string() << "\n";
        ++g_failed; return;
    }
    auto reemitted = translate::lkr_cut_elim::emit(*deriv.value());
    if (!reemitted.ok()) {
        std::cerr << "FAIL[" << label << "]: emit: " << reemitted.error().to_string() << "\n";
        ++g_failed; return;
    }

    Proof p{System::LKR, std::move(reemitted).unwrap()};
    lkr::LKRVerifier v;
    auto vr = v.verify(rt.context(), goal, p);
    if (!vr.ok()) {
        std::cerr << "FAIL[" << label << "]: re-emitted program does not verify: "
                  << vr.error().to_string() << "\n";
        ++g_failed; return;
    }
    std::cout << "  ok[" << label << "]: build∘emit verifies\n";
    ++g_passed;
}

void test_use_forall() {
    round_trip("use_forall", R"(
        axiom all_p: forall x. p(x)
        claim all_p_again: forall x. p(x)
        proof all_p_again:
            fix x
            h_ax = use all_p
            h_px = forall_elim h_ax, x
            h_fa = forall_intro h_px
            qed h_fa
    )", "all_p_again");
}

void test_implies_elim() {
    round_trip("implies_elim", R"(
        axiom all_p: forall x. p(x)
        axiom all_p_q: forall x. (p(x) -> q(x))
        claim all_q: forall x. q(x)
        proof all_q:
            fix x
            h_pax = use all_p
            h_p = forall_elim h_pax, x
            h_pqax = use all_p_q
            h_pq = forall_elim h_pqax, x
            h_q = implies_elim h_pq, h_p
            h_fa = forall_intro h_q
            qed h_fa
    )", "all_q");
}

void test_and_intro() {
    round_trip("and_intro", R"(
        axiom all_p: forall x. p(x)
        axiom all_q: forall x. q(x)
        claim all_pq: forall x. (p(x) & q(x))
        proof all_pq:
            fix x
            h_p_ax = use all_p
            h_p = forall_elim h_p_ax, x
            h_q_ax = use all_q
            h_q = forall_elim h_q_ax, x
            h_pq = and_intro h_p, h_q
            h_fa = forall_intro h_pq
            qed h_fa
    )", "all_pq");
}

void test_or_elim() {
    round_trip("or_elim", R"(
        axiom all_or: forall x. (p(x) | q(x))
        axiom all_p_r: forall x. (p(x) -> r(x))
        axiom all_q_r: forall x. (q(x) -> r(x))
        claim all_r: forall x. r(x)
        proof all_r:
            fix x
            h_or_ax = use all_or
            h_or = forall_elim h_or_ax, x
            h_pr_ax = use all_p_r
            h_pr = forall_elim h_pr_ax, x
            h_qr_ax = use all_q_r
            h_qr = forall_elim h_qr_ax, x
            h_r = or_elim h_or, h_pr, h_qr
            h_fa = forall_intro h_r
            qed h_fa
    )", "all_r");
}

// --- coalesce_exchanges: collapse RExchange chains to minimal net perms -----
namespace lce = translate::lkr_cut_elim;

lce::DerivPtr mk_ax(const std::vector<FormulaHandle>& conc, size_t a, size_t b) {
    auto d = std::make_unique<lce::Deriv>();
    d->conclusion = conc;
    d->rule = lce::RAx{a, b};
    return d;
}
// node = swap(child, i, j)  (matches validate's RExchange convention).
lce::DerivPtr mk_exch(size_t i, size_t j, lce::DerivPtr child) {
    auto d = std::make_unique<lce::Deriv>();
    d->conclusion = child->conclusion;
    std::swap(d->conclusion[i], d->conclusion[j]);
    d->rule = lce::RExchange{i, j, std::move(child)};
    return d;
}
int count_exch(const lce::Deriv& d) {
    if (auto* r = std::get_if<lce::RExchange>(&d.rule))
        return 1 + count_exch(*r->child);
    return 0;
}
void check(const char* label, bool cond) {
    if (cond) { std::cout << "  ok[" << label << "]\n"; ++g_passed; }
    else { std::cerr << "FAIL[" << label << "]\n"; ++g_failed; }
}

void test_coalesce_minimizes() {
    GlobalContext ctx; FormulaBuilder fb(ctx);
    auto A = fb.predicate(ctx.add_predicate("a", 0), {});
    auto B = fb.predicate(ctx.add_predicate("b", 0), {});
    auto C = fb.predicate(ctx.add_predicate("c", 0), {});
    auto d = mk_ax({A, B, C}, 0, 1);
    d = mk_exch(0, 1, std::move(d));   // [b,a,c]
    d = mk_exch(0, 1, std::move(d));   // [a,b,c]  (round-trip)
    d = mk_exch(1, 2, std::move(d));   // [a,c,b]
    d = mk_exch(0, 1, std::move(d));   // [c,a,b]
    const std::vector<FormulaHandle> target = d->conclusion;
    check("coalesce_before_count", count_exch(*d) == 4);
    lce::coalesce_exchanges(d);
    check("coalesce_conclusion_preserved", d->conclusion == target);
    check("coalesce_minimal", count_exch(*d) == 2);   // [a,b,c]→[c,a,b]: 2 transpositions
    check("coalesce_valid", lce::validate(*d).ok());
}

void test_coalesce_identity_collapses() {
    GlobalContext ctx; FormulaBuilder fb(ctx);
    auto A = fb.predicate(ctx.add_predicate("a", 0), {});
    auto B = fb.predicate(ctx.add_predicate("b", 0), {});
    auto d = mk_ax({A, B}, 0, 1);
    d = mk_exch(0, 1, std::move(d));   // [b,a]
    d = mk_exch(0, 1, std::move(d));   // [a,b]  net identity
    const std::vector<FormulaHandle> target = d->conclusion;
    lce::coalesce_exchanges(d);
    check("identity_no_exchanges", count_exch(*d) == 0);
    check("identity_is_leaf", std::get_if<lce::RAx>(&d->rule) != nullptr);
    check("identity_conclusion_preserved", d->conclusion == target);
}

}  // namespace

int main() {
    test_use_forall();
    test_implies_elim();
    test_and_intro();
    test_or_elim();
    test_coalesce_minimizes();
    test_coalesce_identity_collapses();
    std::cout << "deriv_test: " << g_passed << " passed, " << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
