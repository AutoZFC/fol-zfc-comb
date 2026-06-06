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

// B2 UNDER EXCHANGE: the ∧-premise's principal A∧B is produced at position 0
// and an RExchange moves it to the cut slot (last) — the shape NDtoLKR / prior
// permutations produce. B2 must PEEL the exchange to see the ∧. (Red until
// exchange-transparency lands; B2 looks at cut.left->rule = RExchange.)
void test_roundtrip_b2_under_exchange() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle A  = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().right;
    FormulaHandle nA = b.to_nnf(parse_root(ctx, "A -> A")).get().as_compound().left;
    FormulaHandle B  = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().right;
    FormulaHandle nB = b.to_nnf(parse_root(ctx, "B -> B")).get().as_compound().left;
    FormulaHandle AandB  = b.to_nnf(b.make_and(A, B));
    FormulaHandle nAornB = b.to_nnf(b.make_not(b.make_and(A, B)));
    FormulaHandle AorB   = b.to_nnf(b.make_or(A, B));
    FormulaHandle nBor   = b.to_nnf(b.make_or(nB, AorB));
    FormulaHandle G      = b.to_nnf(b.make_or(nA, nBor));

    // RAnd with A∧B at position 0 (principal 0); then exchange 0↔4 to the slot.
    auto Lb = ax({nA, A}, 0, 1);
    auto Lg = ax({nB, A, B, B}, 0, 2);
    auto andN = std::make_unique<Deriv>();
    andN->conclusion = {AandB, nB, A, B, nA};
    andN->rule = RAnd{0, {4}, std::move(Lb), std::move(Lg)};
    auto Lc = std::make_unique<Deriv>();
    Lc->conclusion = {nA, nB, A, B, AandB};            // A∧B exchanged to last
    Lc->rule = RExchange{0, 4, std::move(andN)};
    auto Rc = std::make_unique<Deriv>();
    Rc->conclusion = {nA, nB, A, B, nAornB};
    Rc->rule = ROr{4, ax({nA, nB, A, B, nA, nB}, 2, 4)};
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {nA, nB, A, B};
    cut->rule = RCut{AandB, std::move(Lc), std::move(Rc)};
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

// B3 UNDER EXCHANGE: the ∀-premise's principal ∀x.P(x) is at position 0 and an
// RExchange moves it to the cut slot. B3 must peel + rotate the instantiated
// body from the ∀'s principal position to the cut slot.
void test_roundtrip_b3_under_exchange() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle G    = parse_root(ctx, "forall y. (P(y) | ~P(y))");
    FormulaHandle Gn   = b.to_nnf(G);
    FormulaHandle bodyc = b.instantiate_quantifier_body(Gn.get().as_quantified().body, Term::fixed(0));
    FormulaHandle Pc   = bodyc.get().as_compound().left;
    FormulaHandle nPc  = bodyc.get().as_compound().right;
    FormulaHandle faPx = b.to_nnf(parse_root(ctx, "forall x. P(x)"));
    FormulaHandle Pd   = b.instantiate_quantifier_body(faPx.get().as_quantified().body, Term::fixed(1));
    FormulaHandle exNPx = b.to_nnf(b.make_not(faPx));

    // RForall with ∀x.P(x) at position 0; exchange 0↔2 to the cut slot.
    auto La = ax({Pd, nPc, Pc}, 1, 2);
    auto faN = std::make_unique<Deriv>();
    faN->conclusion = {faPx, nPc, Pc};
    faN->rule = RForall{0, 1, std::move(La)};
    auto L = std::make_unique<Deriv>();
    L->conclusion = {Pc, nPc, faPx};                   // ∀x.P(x) exchanged to last
    L->rule = RExchange{0, 2, std::move(faN)};
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

// B3 with NESTED quantifiers: cut on ∀x.∀w.R(x,w) (degree 2) whose ∀-premise
// is RForall(a) over RForall(b) — so B3's a:=witness substitution must recurse
// (freshen_subst) THROUGH the inner ∀w, renaming its eigenvar. This is the
// shape the corpus pair_eq_a/b reverify-fail on; it exercises the eigenvar
// rectification path that `validate` cannot check.
void test_roundtrip_b3_nested_quantifier() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle G   = parse_root(ctx, "forall y. forall z. (R(y,z) | ~R(y,z))");
    FormulaHandle Gn  = b.to_nnf(G);
    FormulaHandle Gz  = b.instantiate_quantifier_body(Gn.get().as_quantified().body, Term::fixed(0));      // ∀z.(R(0,z)∨¬R(0,z))
    FormulaHandle disj = b.instantiate_quantifier_body(Gz.get().as_quantified().body, Term::fixed(1));      // R(0,1)∨¬R(0,1)
    FormulaHandle Rce = disj.get().as_compound().left;     // R(0,1)
    FormulaHandle nRce = disj.get().as_compound().right;   // ¬R(0,1)
    FormulaHandle faxw = b.to_nnf(parse_root(ctx, "forall x. forall w. R(x,w)"));
    FormulaHandle faw_a = b.instantiate_quantifier_body(faxw.get().as_quantified().body, Term::fixed(2));   // ∀w.R(2,w)
    FormulaHandle Rab = b.instantiate_quantifier_body(faw_a.get().as_quantified().body, Term::fixed(3));    // R(2,3)
    FormulaHandle exxw = b.to_nnf(b.make_not(faxw));        // ∃x.∃w.¬R(x,w)
    FormulaHandle exw_c = b.instantiate_quantifier_body(exxw.get().as_quantified().body, Term::fixed(0));   // ∃w.¬R(0,w)

    // ∀-premise: RForall(a=2) over RForall(b=3) over [Rce,nRce,R(a,b)] RAx.
    auto La = ax({Rce, nRce, Rab}, 0, 1);
    auto Linner = std::make_unique<Deriv>();
    Linner->conclusion = {Rce, nRce, faw_a};
    Linner->rule = RForall{2, 3, std::move(La)};
    auto L = std::make_unique<Deriv>();
    L->conclusion = {Rce, nRce, faxw};
    L->rule = RForall{2, 2, std::move(Linner)};
    // ∃-premise: RExists(c=0) over RExists(e=1) over [Rce,nRce,¬R(c,e)] RAx.
    auto Ra = ax({Rce, nRce, nRce}, 0, 1);
    auto Rinner = std::make_unique<Deriv>();
    Rinner->conclusion = {Rce, nRce, exw_c};
    Rinner->rule = RExists{2, Term::fixed(1), std::move(Ra)};
    auto R = std::make_unique<Deriv>();
    R->conclusion = {Rce, nRce, exxw};
    R->rule = RExists{2, Term::fixed(0), std::move(Rinner)};
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {Rce, nRce};
    cut->rule = RCut{faxw, std::move(L), std::move(R)};
    auto orN = std::make_unique<Deriv>();
    orN->conclusion = {disj};
    orN->rule = ROr{0, std::move(cut)};
    auto zfa = std::make_unique<Deriv>();
    zfa->conclusion = {Gz};
    zfa->rule = RForall{0, 1, std::move(orN)};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {Gn};
    root->rule = RForall{0, 0, std::move(zfa)};

    CHECK(roundtrip(ctx, b, G, *root));
}

// try_b4_cut: an outer cut on ψ=¬P∨P (degree 1) whose left premise ends in a
// LOWER-degree inner cut on Q (degree 0), with ψ a side formula of the inner
// cut. B4 must permute the outer cut past the inner cut into ψ's branch. (No
// §8 coverage existed for this case — it is the one the corpus reverify-fails.)
void test_roundtrip_b4_cut() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle Q  = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle nQ = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().left;
    FormulaHandle psi    = b.to_nnf(b.make_or(nP, P));     // ¬P ∨ P
    FormulaHandle psibar = b.to_nnf(b.make_not(psi));      // P ∧ ¬P
    FormulaHandle QorR   = b.to_nnf(b.make_or(Q, psi));    // Q ∨ (¬P∨P)
    FormulaHandle G      = b.to_nnf(b.make_or(nQ, QorR));  // ¬Q ∨ (Q ∨ (¬P∨P))

    // left = inner cut on Q: [¬Q,Q,ψ] from LA=[¬Q,Q] and LB=[Q,ψ,¬Q] (ψ in Γ_LB).
    auto LA = ax({nQ, Q}, 0, 1);
    auto LB = ax({Q, psi, nQ}, 0, 2);
    auto left = std::make_unique<Deriv>();
    left->conclusion = {nQ, Q, psi};
    left->rule = RCut{Q, std::move(LA), std::move(LB)};
    // right = RAnd on ψ̄=P∧¬P: [¬P,P,ψ̄].
    auto Rb = ax({nP, P}, 0, 1);
    auto Rg = ax({P, nP}, 0, 1);
    auto right = std::make_unique<Deriv>();
    right->conclusion = {nP, P, psibar};
    right->rule = RAnd{2, {0}, std::move(Rb), std::move(Rg)};
    // outer cut on ψ.
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {nQ, Q, nP, P};
    cut->rule = RCut{psi, std::move(left), std::move(right)};
    // ROr-chain expanding G to [¬Q,Q,¬P,P].
    auto c2 = std::make_unique<Deriv>();
    c2->conclusion = {nQ, Q, psi};
    c2->rule = ROr{2, std::move(cut)};
    auto c1 = std::make_unique<Deriv>();
    c1->conclusion = {nQ, QorR};
    c1->rule = ROr{1, std::move(c2)};
    auto root = std::make_unique<Deriv>();
    root->conclusion = {G};
    root->rule = ROr{0, std::move(c1)};

    CHECK(roundtrip(ctx, b, G, *root));
}

// try_b4_cut UNDER EXCHANGE: same as above but the inner θ-cut's ψ is at a
// non-last position and an RExchange moves it to the outer cut slot — so B4
// must peel the exchange to find the θ-cut. (Corpus θ-cuts are exchange-wrapped.)
void test_roundtrip_b4_cut_under_exchange() {
    Runtime rt; rt.load("axiom dummy: forall x. P(x)");
    GlobalContext& ctx = rt.context(); FormulaBuilder b(ctx);
    FormulaHandle P  = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().right;
    FormulaHandle nP = b.to_nnf(parse_root(ctx, "P -> P")).get().as_compound().left;
    FormulaHandle Q  = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().right;
    FormulaHandle nQ = b.to_nnf(parse_root(ctx, "Q -> Q")).get().as_compound().left;
    FormulaHandle psi    = b.to_nnf(b.make_or(nP, P));
    FormulaHandle psibar = b.to_nnf(b.make_not(psi));
    FormulaHandle QorR   = b.to_nnf(b.make_or(Q, psi));
    FormulaHandle G      = b.to_nnf(b.make_or(nQ, QorR));

    // inner θ-cut on Q: node [¬Q, ψ, Q] (ψ at position 1, not last).
    auto LA = ax({nQ, Q}, 0, 1);
    auto LB = ax({psi, Q, nQ}, 1, 2);
    auto tcut = std::make_unique<Deriv>();
    tcut->conclusion = {nQ, psi, Q};
    tcut->rule = RCut{Q, std::move(LA), std::move(LB)};
    // exchange ψ (pos 1) to the cut slot (last).
    auto left = std::make_unique<Deriv>();
    left->conclusion = {nQ, Q, psi};
    left->rule = RExchange{1, 2, std::move(tcut)};
    auto Rb = ax({nP, P}, 0, 1);
    auto Rg = ax({P, nP}, 0, 1);
    auto right = std::make_unique<Deriv>();
    right->conclusion = {nP, P, psibar};
    right->rule = RAnd{2, {0}, std::move(Rb), std::move(Rg)};
    auto cut = std::make_unique<Deriv>();
    cut->conclusion = {nQ, Q, nP, P};
    cut->rule = RCut{psi, std::move(left), std::move(right)};
    auto c2 = std::make_unique<Deriv>();
    c2->conclusion = {nQ, Q, psi};
    c2->rule = ROr{2, std::move(cut)};
    auto c1 = std::make_unique<Deriv>();
    c1->conclusion = {nQ, QorR};
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
    test_roundtrip_b2_under_exchange();
    test_roundtrip_b3_under_exchange();
    test_roundtrip_b3_nested_quantifier();
    test_roundtrip_b4_cut();
    test_roundtrip_b4_cut_under_exchange();
    std::cout << "reduce_roundtrip_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
