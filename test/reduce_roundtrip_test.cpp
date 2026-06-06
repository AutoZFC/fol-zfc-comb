// reduce_roundtrip_test — §8 soundness round-trip (CUT_ELIM_DESIGN.md §8).
//
// The structural `validate` deliberately DEFERS the dual / instantiation /
// eigenvar-freshness checks to LKRVerifier (see validate.cpp comments). So a
// reduction can produce a validate-PASSING but semantically-WRONG tree, which
// only emit → LKRVerifier catches. This test is that gate:
//
//   hand-build a Deriv with a CLOSED single-formula goal G and a logical cut
//   → eliminate_cuts → assert cut-free → emit → LKRVerifier accepts against G.
//
// It is the harness for re-implementing the B2/B3/B5 exchange-transparency
// reductions (the project handoff): a reduction that passes `validate` but
// mis-handles duality/instantiation/freshness will fail HERE, not silently.

#include "src/core/formula.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/proof.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/reduce.h"
#include "src/proof/translate/lkr_cut_elim/validate.h"
#include "src/runtime/runtime.h"

#include <iostream>
#include <memory>
#include <string>
#include <type_traits>

using namespace logic;
using namespace logic::proof;
using namespace logic::proof::translate::lkr_cut_elim;

namespace {

int g_passed = 0;
int g_failed = 0;

#define CHECK(cond) do { \
    if (cond) { ++g_passed; } else { \
        std::cerr << "FAIL: " #cond " at " __FILE__ ":" << __LINE__ << "\n"; \
        ++g_failed; \
    } \
} while (0)

FormulaHandle parse_root(GlobalContext& ctx, const std::string& s) {
    return parse_sentence(s, ctx).get().root();
}

size_t count_cuts(const Deriv& d) {
    size_t n = 0;
    std::visit([&](auto&& r) {
        using T = std::decay_t<decltype(r)>;
        if constexpr (std::is_same_v<T, RCut>) {
            n = 1 + count_cuts(*r.left) + count_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RAnd>) {
            n = count_cuts(*r.left) + count_cuts(*r.right);
        } else if constexpr (std::is_same_v<T, RExchange> ||
                             std::is_same_v<T, RWeaken>   ||
                             std::is_same_v<T, RDuplicate>||
                             std::is_same_v<T, RContract> ||
                             std::is_same_v<T, ROr>       ||
                             std::is_same_v<T, RForall>   ||
                             std::is_same_v<T, RExists>) {
            n = count_cuts(*r.child);
        }
    }, d.rule);
    return n;
}

// The §8 gate: eliminate, require cut-free, emit, LKRVerifier-accept vs `goal`.
// `input` must already be a valid Deriv with root conclusion = [to_nnf(goal)].
bool roundtrip(GlobalContext& ctx, FormulaBuilder& b, FormulaHandle goal,
               const Deriv& input) {
    if (auto v = validate(input); !v.ok()) {
        std::cerr << "  input not valid: " << v.error().to_string() << "\n";
        return false;
    }
    FormulaBuilder fb = b;
    auto elim = eliminate_cuts(fb, input);
    if (!elim.ok()) {
        std::cerr << "  eliminate_cuts: " << elim.error().to_string() << "\n";
        return false;
    }
    if (size_t c = count_cuts(*elim.value()); c != 0) {
        std::cerr << "  not cut-free: " << c << " cut(s) remain\n";
        return false;
    }
    auto prog = emit(*elim.value());
    if (!prog.ok()) {
        std::cerr << "  emit: " << prog.error().to_string() << "\n";
        return false;
    }
    Proof pf{System::LKR, prog.value()};
    lkr::LKRVerifier v;
    auto rv = v.verify(ctx, goal, pf);
    if (!rv.ok()) {
        std::cerr << "  LKRVerifier rejected: " << rv.error().to_string() << "\n";
        return false;
    }
    return true;
}

DerivPtr ax(std::vector<FormulaHandle> concl, size_t a, size_t bb) {
    auto d = std::make_unique<Deriv>();
    d->conclusion = std::move(concl);
    d->rule = RAx{a, bb};
    return d;
}

// B1 round-trip: ⊢ P→P (= ¬P∨P) proved with a DEAD cut on Q (Q non-principal
// in both axiom premises). B0 + B1 eliminate it; the output must re-verify.
void test_roundtrip_b1_dead_cut() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle G   = parse_root(ctx, "P -> P");
    FormulaHandle Gn  = b.to_nnf(G);                       // ¬P ∨ P
    FormulaHandle nP  = Gn.get().as_compound().left;
    FormulaHandle P   = Gn.get().as_compound().right;
    FormulaHandle Q   = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle nQ  = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().left;

    // [¬P,P] via additive Cut(Q): both sides close on ¬P/P, Q/¬Q dead.
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {nP, P};
    cut->rule = RCut{Q, ax({nP, P, Q}, 0, 1), ax({nP, P, nQ}, 0, 1)};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Gn};
    root->rule = ROr{0, std::move(cut)};

    CHECK(roundtrip(ctx, b, G, *root));
}

// B3 round-trip: ⊢ ∀y.(P(y)∨¬P(y)) with a cut on ∀x.P(x) (RForall left, RExists
// right). B3 substitutes the ∃-witness through the ∀-subderivation — exercising
// the eigenvar substitution/freshness path that `validate` does NOT check.
void test_roundtrip_b3_forall_exists() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle G    = parse_root(ctx, "forall y. (P(y) | ~P(y))");
    FormulaHandle Gn   = b.to_nnf(G);
    FormulaHandle bodyc = b.instantiate_quantifier_body(Gn.get().as_quantified().body, Term::fixed(0));
    FormulaHandle Pc   = bodyc.get().as_compound().left;    // P(c), c=0
    FormulaHandle nPc  = bodyc.get().as_compound().right;   // ¬P(c)
    FormulaHandle faPx = b.to_nnf(parse_root(ctx, "forall x. P(x)"));
    FormulaHandle Pd   = b.instantiate_quantifier_body(faPx.get().as_quantified().body, Term::fixed(1)); // P(d), d=1
    FormulaHandle exNPx = b.to_nnf(b.make_not(faPx));       // ∃x.¬P(x)

    // cut on ∀x.P(x): left RForall(eigen 1)→[Pc,nPc,P(1)] (RAx); right
    // RExists(witness c=0)→[Pc,nPc,¬P(0)] (RAx).
    auto La = ax({Pc, nPc, Pd}, 0, 1);
    auto L  = std::make_unique<Deriv>();
    L->conclusion = {Pc, nPc, faPx};
    L->rule = RForall{2, 1, std::move(La)};
    auto Ra = ax({Pc, nPc, nPc}, 0, 1);
    auto R  = std::make_unique<Deriv>();
    R->conclusion = {Pc, nPc, exNPx};
    R->rule = RExists{2, Term::fixed(0), std::move(Ra)};
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {Pc, nPc};
    cut->rule = RCut{faPx, std::move(L), std::move(R)};
    auto orN = std::make_unique<Deriv>();
    orN->conclusion = {bodyc};
    orN->rule = ROr{0, std::move(cut)};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Gn};
    root->rule = RForall{0, 0, std::move(orN)};

    CHECK(roundtrip(ctx, b, G, *root));
}

// B2 round-trip: ⊢ ¬A∨(¬B∨(A∨B)) expanded by an ROr-chain to ⊢ ¬A,¬B,A,B,
// then a cut on A∧B (RAnd left / ROr right on the dual). B2 splits it into the
// β/γ cuts; drives to cut-free atoms. Output must re-verify.
void test_roundtrip_b2_and_or() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle A  = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().right;
    FormulaHandle nA = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().left;
    FormulaHandle B  = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;
    FormulaHandle nB = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().left;
    FormulaHandle AandB  = b.to_nnf(b.make_and(A, B));        // A∧B
    FormulaHandle nAornB = b.to_nnf(b.make_not(b.make_and(A, B)));  // ¬A∨¬B
    FormulaHandle AorB   = b.to_nnf(b.make_or(A, B));         // A∨B
    FormulaHandle nBor   = b.to_nnf(b.make_or(nB, AorB));     // ¬B∨(A∨B)
    FormulaHandle G      = b.to_nnf(b.make_or(nA, nBor));     // ¬A∨(¬B∨(A∨B))

    // ∧-premise Lc ⊢ [¬A,¬B,A,B, A∧B]: RAnd{principal 4, left_partition {0}}.
    auto Lb = ax({nA, A}, 0, 1);
    auto Lg = ax({nB, A, B, B}, 0, 2);
    auto Lc = std::make_unique<Deriv>();
    Lc->conclusion = {nA, nB, A, B, AandB};
    Lc->rule = RAnd{4, {0}, std::move(Lb), std::move(Lg)};
    // ∨-premise Rc ⊢ [¬A,¬B,A,B, ¬A∨¬B]: ROr{principal 4} → close on A/¬A.
    auto Rc = std::make_unique<Deriv>();
    Rc->conclusion = {nA, nB, A, B, nAornB};
    Rc->rule = ROr{4, ax({nA, nB, A, B, nA, nB}, 2, 4)};
    // additive Cut(A∧B) on [¬A,¬B,A,B].
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {nA, nB, A, B};
    cut->rule = RCut{AandB, std::move(Lc), std::move(Rc)};
    // ROr-chain expanding G down to [¬A,¬B,A,B].
    auto c2 = std::make_unique<Deriv>();
    c2->conclusion = {nA, nB, AorB};
    c2->rule = ROr{2, std::move(cut)};
    auto c1 = std::make_unique<Deriv>();
    c1->conclusion = {nA, nBor};
    c1->rule = ROr{1, std::move(c2)};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {G};
    root->rule = ROr{0, std::move(c1)};

    CHECK(roundtrip(ctx, b, G, *root));
}

// Cut-free input round-trips unchanged (sanity: build/emit/verify baseline).
void test_roundtrip_cut_free() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle G  = parse_root(ctx, "P -> P");
    FormulaHandle Gn = b.to_nnf(G);
    FormulaHandle nP = Gn.get().as_compound().left;
    FormulaHandle P  = Gn.get().as_compound().right;
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Gn};
    root->rule = ROr{0, ax({nP, P}, 0, 1)};
    CHECK(roundtrip(ctx, b, G, *root));
}

}  // namespace

int main() {
    test_roundtrip_cut_free();
    test_roundtrip_b1_dead_cut();
    test_roundtrip_b2_and_or();
    test_roundtrip_b3_forall_exists();
    std::cout << "reduce_roundtrip_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
