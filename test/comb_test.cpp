// Tests for the combinatorial-proof package: cotree primitives + the
// 2A.3 binder-legality check inside CombVerifier::verify_fonet.

#include "src/core/formula.h"
#include "src/proof/comb/comb_proof.h"
#include "src/proof/comb/cotree.h"
#include "src/proof/comb/leap.h"
#include "src/proof/comb/verifier.h"

#include <algorithm>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

using namespace logic;
using namespace logic::proof::comb;

namespace {

int g_passed = 0;
int g_failed = 0;

#define EXPECT(...) do { \
    if (__VA_ARGS__) { ++g_passed; } else { \
        std::cerr << "FAIL: " #__VA_ARGS__ " at " << __FILE__ << ":" << __LINE__ << "\n"; \
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

// =====================================================================
// Cotree primitives
// =====================================================================

std::vector<size_t> collect_leaves(const Cotree& c, size_t node_id) {
    std::vector<size_t> out;
    c.for_each_leaf_in_subtree(node_id, [&](size_t v) { out.push_back(v); });
    std::sort(out.begin(), out.end());
    return out;
}

void test_cotree_empty() {
    Cotree c(0, {});
    EXPECT(c.ok());
    EXPECT(c.num_vertex() == 0);
    EXPECT(c.num_nodes() == 0);
}

void test_cotree_singleton() {
    Cotree c(1, {});
    EXPECT(c.ok());
    EXPECT(c.num_vertex() == 1);
    EXPECT(c.num_nodes() == 1);
    EXPECT(c.node(0).kind == Cotree::NodeKind::LEAF);
    EXPECT(c.node(0).vertex == 0);
    EXPECT(c.parent(0) == 0);             // root self-parent
    EXPECT(c.leaf_of(0) == 0);
}

void test_cotree_k2() {
    // Two vertices joined by an edge: × node (UNION) over two leaves.
    Cotree c(2, {{0, 1}});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::UNION);
    EXPECT(c.node(c.root()).children.size() == 2);
    EXPECT(c.parent(c.leaf_of(0)) == c.root());
    EXPECT(c.parent(c.leaf_of(1)) == c.root());
    EXPECT(collect_leaves(c, c.root()) == std::vector<size_t>{0, 1});
}

void test_cotree_k2_complement() {
    // Two vertices, no edge: + node (JOIN) over two leaves.
    Cotree c(2, {});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::JOIN);
    EXPECT(c.node(c.root()).children.size() == 2);
    EXPECT(collect_leaves(c, c.root()) == std::vector<size_t>{0, 1});
}

void test_cotree_p4_not_cograph() {
    // Path 0-1-2-3: not a cograph (induced P_4).
    Cotree c(4, {{0, 1}, {1, 2}, {2, 3}});
    EXPECT(!c.ok());
}

void test_cotree_2K2() {
    // Two disjoint edges: JOIN over two UNION sub-trees.
    Cotree c(4, {{0, 1}, {2, 3}});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::JOIN);
    EXPECT(c.node(c.root()).children.size() == 2);

    // Both leaves under each child should be 2-element groups.
    auto under_root = collect_leaves(c, c.root());
    EXPECT(under_root == std::vector<size_t>{0, 1, 2, 3});

    // Each binder's "scope" (parent of its leaf) should be the inner ×.
    auto p01 = c.parent(c.leaf_of(0));
    auto p23 = c.parent(c.leaf_of(2));
    EXPECT(p01 != c.root());
    EXPECT(p23 != c.root());
    EXPECT(p01 != p23);
    EXPECT(c.node(p01).kind == Cotree::NodeKind::UNION);
    EXPECT(c.node(p23).kind == Cotree::NodeKind::UNION);
    EXPECT(collect_leaves(c, p01) == std::vector<size_t>{0, 1});
    EXPECT(collect_leaves(c, p23) == std::vector<size_t>{2, 3});
}

void test_cotree_k3_triangle() {
    // Triangle: UNION with three leaf children.
    Cotree c(3, {{0, 1}, {1, 2}, {0, 2}});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::UNION);
    EXPECT(c.node(c.root()).children.size() == 3);
    EXPECT(collect_leaves(c, c.root()) == std::vector<size_t>{0, 1, 2});
}

void test_cotree_self_loop_ignored() {
    // Self-loops should be silently ignored by build_adjacency.
    Cotree c(2, {{0, 0}, {0, 1}, {1, 1}});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::UNION);
}

void test_cotree_duplicate_edge_ok() {
    // Duplicate (and reversed) edges should not break construction.
    Cotree c(2, {{0, 1}, {1, 0}, {0, 1}});
    EXPECT(c.ok());
    EXPECT(c.node(c.root()).kind == Cotree::NodeKind::UNION);
}

// =====================================================================
// verify_fonet — 2A.3 binder legality
// =====================================================================
//
// To exercise 2A.3 we hand-build a minimal CombProof. The earlier
// phase-2 checks (2A.1, 2A.2, 2B.*) must pass before 2A.3 runs, so
// each fixture is constructed to satisfy them trivially:
//
//   * If the source has atoms, they come in dual pairs sharing one
//     predicate, linked together, with empty args (so 2B.3 unifies).
//   * No existential binders ⇒ empty dualizer satisfies 2B.1/2.
//
// `target.labels` is the only place labels live; the fonet derives
// labels via fibration. We use an identity fibration in every test.

struct Fixture {
    GlobalContext   ctx;
    // 0-ary predicate so atoms can be linked without arg-unification.
    PredicateHandle p = ctx.add_predicate("p", 0);

    // Make a Binder VertexLabel with the given variable.
    VertexLabel binder(var_index v, bool existential = false) {
        VertexLabel lbl;
        lbl.kind           = VertexKind::Binder;
        lbl.var            = v;
        lbl.is_existential = existential;
        return lbl;
    }

    VertexLabel atom(bool negated) {
        VertexLabel lbl;
        lbl.kind    = VertexKind::Atom;
        lbl.pred    = p;
        lbl.negated = negated;
        return lbl;
    }
};

// Helper: install identity fibration of length n.
void identity_fibration(CombProof& cp, size_t n) {
    cp.fibration.resize(n);
    for (size_t i = 0; i < n; ++i) cp.fibration[i] = i;
}

// Richer fixture used by 2B-description tests and the leap-graph tests:
// non-zero-ary predicates + helpers for binder / atom-with-args labels.
struct LeapFixture {
    GlobalContext   ctx;
    FormulaBuilder  fb{ctx};
    PredicateHandle p1 = ctx.add_predicate("p", 1);
    PredicateHandle q1 = ctx.add_predicate("q", 1);
    PredicateHandle r3 = ctx.add_predicate("r", 3);

    VertexLabel binder(var_index v, bool existential) {
        VertexLabel lbl;
        lbl.kind           = VertexKind::Binder;
        lbl.var            = v;
        lbl.is_existential = existential;
        return lbl;
    }
    VertexLabel atom(PredicateHandle p, bool negated, std::vector<Term> args) {
        VertexLabel lbl;
        lbl.kind    = VertexKind::Atom;
        lbl.pred    = p;
        lbl.negated = negated;
        lbl.args    = std::move(args);
        return lbl;
    }
};

Edges sorted_leaps(Edges es) {
    for (auto& e : es) if (e.first > e.second) std::swap(e.first, e.second);
    std::sort(es.begin(), es.end());
    return es;
}

CombProof make_leap_proof(size_t n,
                          std::vector<VertexLabel>               labels,
                          std::vector<std::pair<size_t, size_t>> links) {
    CombProof cp;
    cp.source.num_vertex = n;
    cp.source.links      = std::move(links);
    cp.target.labels     = std::move(labels);
    identity_fibration(cp, n);
    return cp;
}

// (legal): one universal binder + a linked atom pair, all in the same
// strong module via no cograph edges (single JOIN root contains all).
void test_2A3_legal_one_binder_two_atoms() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 3;
    cp.source.cograph_edges = {};            // → JOIN over {0, 1, 2}
    cp.source.links         = {{1, 2}};      // both atoms linked

    cp.target.labels = {f.binder(0), f.atom(false), f.atom(true)};
    identity_fibration(cp, 3);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// (C1 fail): two binders, no atoms. Scope of each binder is the root
// module {0, 1} which contains no literal.
void test_2A3_c1_no_literal_in_scope() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 2;
    cp.source.cograph_edges = {};            // → JOIN root over {0, 1}
    cp.target.labels        = {f.binder(0), f.binder(1)};
    identity_fibration(cp, 2);

    CombVerifier v;
    EXPECT_ERR(v.verify_fonet(cp));
}

// (C2 fail): two ∀x binders + linked atom pair, all flat under root.
// Scope of binder 0 contains binder 1 with the same variable.
void test_2A3_c2_duplicate_var_binder_in_scope() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {};            // → JOIN root over {0..3}
    cp.source.links         = {{2, 3}};

    cp.target.labels = {
        f.binder(/*var=*/0),
        f.binder(/*var=*/0),                 // same var ⇒ C2 violation
        f.atom(false),
        f.atom(true),
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_ERR(v.verify_fonet(cp));
}

// (C2 fine when vars differ): two binders with different variables in
// the same scope is allowed; verify it passes.
void test_2A3_distinct_var_binders_in_scope_ok() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {};
    cp.source.links         = {{2, 3}};

    cp.target.labels = {
        f.binder(/*var=*/0),
        f.binder(/*var=*/1),                 // different var ⇒ legal
        f.atom(false),
        f.atom(true),
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// (degenerate): a single-vertex source that's a binder. The binder
// has no proper scope module. Should fail.
void test_2A3_singleton_binder_no_scope() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 1;
    cp.source.cograph_edges = {};
    cp.target.labels        = {f.binder(0)};
    identity_fibration(cp, 1);

    CombVerifier v;
    EXPECT_ERR(v.verify_fonet(cp));
}

// (not a cograph): cograph_edges form an induced P_4 ⇒ cotree
// construction fails, 2A.3 reports it.
void test_2A3_source_not_a_cograph() {
    Fixture f;
    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {{0, 1}, {1, 2}, {2, 3}};  // P_4
    cp.source.links         = {};
    // Labels: four atoms so that 2A.1/2A.2 fail before 2A.3? No —
    // 2A.1 requires every atom in exactly one link. To exercise the
    // cotree-construction error specifically, give all-binder labels.
    cp.target.labels = {
        f.binder(0), f.binder(1), f.binder(2), f.binder(3),
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_ERR(v.verify_fonet(cp));
}

// =====================================================================
// Description-free boundary check (CombVerifier::verify entry)
// =====================================================================
//
// The comb proof system is description-free by contract; the translator
// is responsible for running eliminate_descriptions before calling the
// verifier. CombVerifier::verify rejects any input that violates this
// at the goal-formula / atom-label / dualizer-image surface.

void test_boundary_reject_description_in_goal() {
    GlobalContext   ctx;
    FormulaBuilder  fb(ctx);
    PredicateHandle p1 = ctx.add_predicate("p", 1);
    PredicateHandle q1 = ctx.add_predicate("q", 1);

    // Goal: P(ι w. q(w))
    FormulaHandle desc_body = fb.predicate(q1, {Term::generalized(0)});
    FormulaHandle goal      = fb.predicate(p1, {Term::description(desc_body)});

    logic::proof::Proof p;
    p.system = logic::proof::System::COMB;
    p.body   = CombProof{};

    CombVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

void test_boundary_reject_description_in_label_args() {
    GlobalContext   ctx;
    FormulaBuilder  fb(ctx);
    PredicateHandle p1 = ctx.add_predicate("p", 1);
    PredicateHandle q1 = ctx.add_predicate("q", 1);
    FormulaHandle   goal = fb.predicate(p1, {Term::fixed(0)});   // p(x), no iota

    CombProof cp;
    cp.target.source_formula = goal;
    VertexLabel lbl;
    lbl.kind = VertexKind::Atom;
    lbl.pred = p1;
    lbl.args = {Term::description(fb.predicate(q1, {Term::generalized(0)}))};
    cp.target.labels = {lbl};

    logic::proof::Proof p;
    p.system = logic::proof::System::COMB;
    p.body   = cp;

    CombVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

void test_boundary_reject_description_in_dualizer_image() {
    GlobalContext   ctx;
    FormulaBuilder  fb(ctx);
    PredicateHandle p1 = ctx.add_predicate("p", 1);
    PredicateHandle q1 = ctx.add_predicate("q", 1);
    FormulaHandle   goal = fb.predicate(p1, {Term::fixed(0)});

    CombProof cp;
    cp.target.source_formula = goal;
    cp.source.dualizer = {{0, Term::description(
        fb.predicate(q1, {Term::generalized(0)}))}};

    logic::proof::Proof p;
    p.system = logic::proof::System::COMB;
    p.body   = cp;

    CombVerifier v;
    EXPECT_ERR(v.verify(ctx, goal, p));
}

// =====================================================================
// Fograph(FormulaHandle) — paper Def. 3.1
// =====================================================================

struct BuilderFixture {
    GlobalContext  ctx;
    FormulaBuilder fb{ctx};

    // Names+arities are keys, so "P/0" and "P/1" coexist.
    PredicateHandle P0 = ctx.add_predicate("P", 0);
    PredicateHandle Q0 = ctx.add_predicate("Q", 0);
    PredicateHandle P1 = ctx.add_predicate("P", 1);
    PredicateHandle Q1 = ctx.add_predicate("Q", 1);
    PredicateHandle Q2 = ctx.add_predicate("Q", 2);
    PredicateHandle R2 = ctx.add_predicate("R", 2);

    FormulaHandle pred0(PredicateHandle h)            { return fb.predicate(h, {}); }
    FormulaHandle pred1(PredicateHandle h, Term a)    { return fb.predicate(h, {a}); }
    FormulaHandle pred2(PredicateHandle h, Term a, Term b) { return fb.predicate(h, {a, b}); }
};

// Normalize a list of *undirected* edges for comparison.
std::vector<std::pair<size_t, size_t>>
canonical_unordered(std::vector<std::pair<size_t, size_t>> es) {
    for (auto& e : es) if (e.first > e.second) std::swap(e.first, e.second);
    std::sort(es.begin(), es.end());
    return es;
}

// Normalize a list of *directed* edges for comparison.
std::vector<std::pair<size_t, size_t>>
canonical_directed(std::vector<std::pair<size_t, size_t>> es) {
    std::sort(es.begin(), es.end());
    return es;
}

// --- atom-only cases -------------------------------------------------

void test_builder_atom_zero_ary() {
    BuilderFixture f;
    Fograph g(f.pred0(f.P0));
    EXPECT(g.labels.size() == 1);
    EXPECT(g.labels[0].kind == VertexKind::Atom);
    EXPECT(g.labels[0].pred == f.P0);
    EXPECT(g.labels[0].negated == false);
    EXPECT(g.cograph_edges.empty());
    EXPECT(g.binding_edges.empty());
}

void test_builder_negated_atom() {
    BuilderFixture f;
    Fograph g(f.fb.make_not(f.pred0(f.P0)));
    EXPECT(g.labels.size() == 1);
    EXPECT(g.labels[0].kind == VertexKind::Atom);
    EXPECT(g.labels[0].negated == true);
    EXPECT(g.cograph_edges.empty());
    EXPECT(g.binding_edges.empty());
}

// --- compound cases --------------------------------------------------

void test_builder_and() {
    BuilderFixture f;
    Fograph g(f.fb.make_and(f.pred0(f.P0), f.pred0(f.Q0)));
    EXPECT(g.labels.size() == 2);
    EXPECT(g.labels[0].kind == VertexKind::Atom);
    EXPECT(g.labels[1].kind == VertexKind::Atom);
    EXPECT(canonical_unordered(g.cograph_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}}));
    EXPECT(g.binding_edges.empty());
}

void test_builder_or_no_edges() {
    BuilderFixture f;
    Fograph g(f.fb.make_or(f.pred0(f.P0), f.pred0(f.Q0)));
    EXPECT(g.labels.size() == 2);
    EXPECT(g.cograph_edges.empty());
    EXPECT(g.binding_edges.empty());
}

// --- quantifier cases ------------------------------------------------

void test_builder_forall_unary() {
    BuilderFixture f;
    // ∀x. P(x)
    FormulaHandle body = f.pred1(f.P1, Term::generalized(0));
    Fograph g(f.fb.make_quantified(Op::Forall, body));

    EXPECT(g.labels.size() == 2);
    EXPECT(g.labels[0].kind == VertexKind::Binder);
    EXPECT(g.labels[0].is_existential == false);
    EXPECT(g.labels[1].kind == VertexKind::Atom);
    EXPECT(g.cograph_edges.empty());                    // ∀ = +-disjoint
    EXPECT(canonical_directed(g.binding_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}}));
    // Atom arg points at the binder's var via Fixed.
    EXPECT(g.labels[1].args.size() == 1);
    EXPECT(g.labels[1].args[0].is_fixed());
    EXPECT(g.labels[1].args[0].as_variable() == g.labels[0].var);
}

void test_builder_exists_unary() {
    BuilderFixture f;
    // ∃x. P(x)
    FormulaHandle body = f.pred1(f.P1, Term::generalized(0));
    Fograph g(f.fb.make_quantified(Op::Exists, body));

    EXPECT(g.labels.size() == 2);
    EXPECT(g.labels[0].kind == VertexKind::Binder);
    EXPECT(g.labels[0].is_existential == true);
    EXPECT(canonical_unordered(g.cograph_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}})); // ∃ × body
    EXPECT(canonical_directed(g.binding_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}}));
}

void test_builder_exists_conj() {
    BuilderFixture f;
    // ∃x. (P(x) ∧ Q(x))
    FormulaHandle p_x  = f.pred1(f.P1, Term::generalized(0));
    FormulaHandle q_x  = f.pred1(f.Q1, Term::generalized(0));
    FormulaHandle body = f.fb.make_and(p_x, q_x);
    Fograph g(f.fb.make_quantified(Op::Exists, body));

    EXPECT(g.labels.size() == 3);
    EXPECT(g.labels[0].kind == VertexKind::Binder && g.labels[0].is_existential);
    EXPECT(g.labels[1].kind == VertexKind::Atom);
    EXPECT(g.labels[2].kind == VertexKind::Atom);
    // ∃-binder ×-joins to body (binder-atomP, binder-atomQ),
    // plus ∧ ×-joins the two atoms.
    EXPECT(canonical_unordered(g.cograph_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}, {0, 2}, {1, 2}}));
    EXPECT(canonical_directed(g.binding_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 1}, {0, 2}}));
}

void test_builder_nested_quantifiers() {
    BuilderFixture f;
    // ∀x. ∃y. R(x, y)
    // body of ∃y: R(Gen(1)=x, Gen(0)=y)
    FormulaHandle r      = f.pred2(f.R2, Term::generalized(1), Term::generalized(0));
    FormulaHandle e_body = f.fb.make_quantified(Op::Exists, r);
    Fograph g(f.fb.make_quantified(Op::Forall, e_body));

    // Pre-order: v0 = ∀x, v1 = ∃y, v2 = R.
    EXPECT(g.labels.size() == 3);
    EXPECT(g.labels[0].kind == VertexKind::Binder && !g.labels[0].is_existential);
    EXPECT(g.labels[1].kind == VertexKind::Binder &&  g.labels[1].is_existential);
    EXPECT(g.labels[2].kind == VertexKind::Atom);
    // ∀ adds nothing; ∃y × R-atom = {1, 2}.
    EXPECT(canonical_unordered(g.cograph_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{1, 2}}));
    // ∀x → R (arg 0), ∃y → R (arg 1).
    EXPECT(canonical_directed(g.binding_edges) ==
           (std::vector<std::pair<size_t, size_t>>{{0, 2}, {1, 2}}));
}

// --- description case (the one we worked through by hand) -----------

// --- Phase 1: verify_target_is_formula_graph ------------------------
//
// Round-trip: build the same Fograph the verifier will build, store it
// as cp.target, and confirm Phase 1 passes. Then mutate one piece at a
// time to check each mismatch path.

void test_phase1_roundtrip_simple() {
    BuilderFixture f;
    FormulaHandle phi = f.fb.make_and(f.pred0(f.P0), f.pred0(f.Q0));

    CombProof cp;
    cp.target = Fograph(phi);                  // canonical target

    CombVerifier v;
    EXPECT_OK(v.verify_target_is_formula_graph(f.ctx, phi, cp));
}

void test_phase1_roundtrip_quantified() {
    BuilderFixture f;
    // ∃x. (P(x) ∧ Q(x))
    FormulaHandle p_x  = f.pred1(f.P1, Term::generalized(0));
    FormulaHandle q_x  = f.pred1(f.Q1, Term::generalized(0));
    FormulaHandle body = f.fb.make_and(p_x, q_x);
    FormulaHandle phi  = f.fb.make_quantified(Op::Exists, body);

    CombProof cp;
    cp.target = Fograph(phi);

    CombVerifier v;
    EXPECT_OK(v.verify_target_is_formula_graph(f.ctx, phi, cp));
}

void test_phase1_nnf_normalization() {
    // The verifier's contract is "(NNF-equivalent)". Pass a non-NNF
    // goal; verify normalizes internally and the comparison still passes
    // against a target built from the NNF form.
    BuilderFixture f;
    // P ∧ Q is already NNF. Use ~~P, which to_nnf collapses to P.
    FormulaHandle p   = f.pred0(f.P0);
    FormulaHandle nnp = f.fb.make_not(f.fb.make_not(p));    // ¬¬P (non-NNF)

    // Target is built from the NNF goal (just P).
    CombProof cp;
    cp.target = Fograph(p);

    CombVerifier v;
    EXPECT_OK(v.verify_target_is_formula_graph(f.ctx, nnp, cp));
}

void test_phase1_vertex_count_mismatch() {
    BuilderFixture f;
    FormulaHandle phi = f.pred0(f.P0);                 // expected: 1 vertex

    CombProof cp;
    // Hand-crafted target with too many vertices.
    cp.target.source_formula = phi;
    VertexLabel atom;
    atom.kind = VertexKind::Atom; atom.pred = f.P0; atom.negated = false;
    cp.target.labels = {atom, atom};                   // 2 vertices

    CombVerifier v;
    EXPECT_ERR(v.verify_target_is_formula_graph(f.ctx, phi, cp));
}

void test_phase1_label_mismatch() {
    BuilderFixture f;
    FormulaHandle phi = f.pred0(f.P0);                 // expected: Atom P

    CombProof cp;
    cp.target.source_formula = phi;
    VertexLabel wrong;
    wrong.kind = VertexKind::Atom; wrong.pred = f.Q0; wrong.negated = false;
    cp.target.labels = {wrong};

    CombVerifier v;
    EXPECT_ERR(v.verify_target_is_formula_graph(f.ctx, phi, cp));
}

void test_phase1_edge_mismatch() {
    BuilderFixture f;
    FormulaHandle phi = f.fb.make_and(f.pred0(f.P0), f.pred0(f.Q0));

    CombProof cp;
    cp.target = Fograph(phi);
    cp.target.cograph_edges.clear();                   // drop the × edge

    CombVerifier v;
    EXPECT_ERR(v.verify_target_is_formula_graph(f.ctx, phi, cp));
}

// =====================================================================
// verify_skew_bifibration — paper Def. 4.1
// =====================================================================
//
// verify_skew_bifibration only reads the edge sets, the vertex counts,
// and the fibration — label *content* is irrelevant to it (labels enter
// the picture in phases 1-2). So fixtures here build a CombProof
// directly from raw edge lists; target.labels is just resized to the
// right count so target.num_vertex() is correct.
//
// Order inside verify_skew_bifibration: size check → is_fibration_dir
// (binding graph) → is_skew_fibration (cograph). Tests that want to
// exercise the cograph path keep binding edges empty so the binding
// check passes first.

CombProof make_bifib_proof(size_t src_n, Edges src_cograph, Edges src_binding,
                           size_t tgt_n, Edges tgt_cograph, Edges tgt_binding,
                           std::vector<size_t> fibration) {
    CombProof cp;
    cp.source.num_vertex    = src_n;
    cp.source.cograph_edges = std::move(src_cograph);
    cp.source.binding_edges = std::move(src_binding);
    cp.target.labels.resize(tgt_n);            // content irrelevant here
    cp.target.cograph_edges = std::move(tgt_cograph);
    cp.target.binding_edges = std::move(tgt_binding);
    cp.fibration            = std::move(fibration);
    return cp;
}

// fibration.size() must equal source.num_vertex.
void test_bifib_size_mismatch() {
    CombProof cp = make_bifib_proof(2, {}, {}, 2, {}, {}, /*fibration=*/{0});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// --- cograph / skew-fibration path (no binding edges) ----------------

// Identity on a single cograph edge is a skew bifibration.
void test_bifib_identity_cograph_edge() {
    CombProof cp = make_bifib_proof(2, {{0, 1}}, {}, 2, {{0, 1}}, {}, {0, 1});
    CombVerifier v;
    EXPECT_OK(v.verify_skew_bifibration(cp));
}

// Weakening: a single source vertex maps into a target with an extra
// +-disjoint (edge-free) vertex. Skew fibration allows it — f(v) has no
// target neighbours, so the ∀w condition is vacuous.
void test_bifib_skew_weakening_ok() {
    CombProof cp = make_bifib_proof(1, {}, {}, 2, /*tgt_cograph=*/{}, {}, {0});
    CombVerifier v;
    EXPECT_OK(v.verify_skew_bifibration(cp));
}

// Contraction: source `A ∨ A` (two edge-free vertices) folds onto a
// single target vertex. Both source vertices map to 0.
void test_bifib_contraction_ok() {
    CombProof cp = make_bifib_proof(2, {}, {}, 1, {}, {}, {0, 0});
    CombVerifier v;
    EXPECT_OK(v.verify_skew_bifibration(cp));
}

// Skew fibration fails: f(v)=0 has a target neighbour (1) but v has no
// source neighbour to cover it.
void test_bifib_skew_fail_no_source_neighbour() {
    CombProof cp = make_bifib_proof(1, {}, {}, 2, /*tgt_cograph=*/{{0, 1}}, {},
                                    {0});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// Cograph homomorphism fails: a source cograph edge maps to a target
// non-edge.
void test_bifib_cograph_homomorphism_fail() {
    CombProof cp = make_bifib_proof(2, /*src_cograph=*/{{0, 1}}, {},
                                    2, /*tgt_cograph=*/{}, {}, {0, 1});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// --- binding-graph / ordinary-fibration path -------------------------

// Identity on a single binding edge (binder 0 → literal 1). This is the
// regression test for the predecessor-vs-successor map bug: the binding
// fibration must quantify over edges *into* f(v).
void test_bifib_binding_identity_ok() {
    CombProof cp = make_bifib_proof(2, {}, /*src_binding=*/{{0, 1}},
                                    2, {}, /*tgt_binding=*/{{0, 1}}, {0, 1});
    CombVerifier v;
    EXPECT_OK(v.verify_skew_bifibration(cp));
}

// Binding fibration fails — missing lift: the target binds literal 1
// (edge 0→1) but the source has no binder edge into vertex 1.
void test_bifib_binding_fail_missing_lift() {
    CombProof cp = make_bifib_proof(2, {}, /*src_binding=*/{},
                                    2, {}, /*tgt_binding=*/{{0, 1}}, {0, 1});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// Binding fibration fails — non-unique lift: two source binders (0, 1)
// both map to target binder 0 and both bind source literal 2, which
// maps to target literal 1. The lift of ⟨0,1⟩ is not unique.
void test_bifib_binding_fail_nonunique_lift() {
    CombProof cp = make_bifib_proof(3, {}, /*src_binding=*/{{0, 2}, {1, 2}},
                                    2, {}, /*tgt_binding=*/{{0, 1}},
                                    {0, 0, 1});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// Binding homomorphism fails: a source binding edge maps to a target
// non-edge.
void test_bifib_binding_homomorphism_fail() {
    CombProof cp = make_bifib_proof(2, {}, /*src_binding=*/{{0, 1}},
                                    2, {}, /*tgt_binding=*/{}, {0, 1});
    CombVerifier v;
    EXPECT_ERR(v.verify_skew_bifibration(cp));
}

// --- combined: a real fograph -----------------------------------------

// Identity on G(∃x. P(x)): vertex 0 = ∃-binder, vertex 1 = atom P(x).
// cograph edge {0,1} (∃ ×-joins its body), binding edge 0→1. Identity
// is a skew bifibration.
void test_bifib_full_exists_identity_ok() {
    CombProof cp = make_bifib_proof(2, /*src_cograph=*/{{0, 1}},
                                    /*src_binding=*/{{0, 1}},
                                    2, /*tgt_cograph=*/{{0, 1}},
                                    /*tgt_binding=*/{{0, 1}}, {0, 1});
    CombVerifier v;
    EXPECT_OK(v.verify_skew_bifibration(cp));
}

// =====================================================================
// build_leap_graph — paper §5 (leaps = links ∪ dependencies)
// =====================================================================
//
// The leap graph is an edge set over the *fonet's* vertex indices.
// Dependencies are derived from the MGU of the link argument equations;
// the implementation is a union-find over existential variables.
//
// Fixtures here build labels directly into target.labels with an
// identity fibration, so source_label(v) is just target.labels[v].
// All atom args are post-rewrite (Fixed for binder refs, Description
// optionally) — `build_leap_graph` does not run the fograph rewrite.

// Empty fonet: no vertices, no links → empty leap graph.
void test_leap_empty() {
    CombProof cp;
    cp.source.num_vertex = 0;
    auto r = build_leap_graph(cp);
    EXPECT_OK(r);
    EXPECT(r.value().empty());
}

// A link with no binders: every term is rigid, unification trivially
// succeeds (t == u for matching Fixed terms), no dependencies. The
// link itself is still emitted.
void test_leap_links_no_binders() {
    LeapFixture f;
    auto cp = make_leap_proof(
        /*n=*/2,
        {f.atom(f.p1, false, {Term::fixed(0)}),
         f.atom(f.p1, true,  {Term::fixed(0)})},
        {{0, 1}});
    auto r = build_leap_graph(cp);
    EXPECT_OK(r);
    EXPECT(sorted_leaps(r.value()) == (Edges{{0, 1}}));
}

// Single existential bound by a single universal via one link.
//   vertices: 0 = ∃x, 1 = ∀u, 2 = p(x), 3 = ¬p(u).
//   link {2,3} ⇒ equation x = u ⇒ anchor[class(x)] = Fixed(u).
//   dependency {x, u} → edge {0, 1}.
void test_leap_dependency_simple() {
    LeapFixture f;
    auto cp = make_leap_proof(
        /*n=*/4,
        {
            f.binder(/*var=*/0, /*existential=*/true),
            f.binder(/*var=*/1, /*existential=*/false),
            f.atom(f.p1, false, {Term::fixed(0)}),
            f.atom(f.p1, true,  {Term::fixed(1)}),
        },
        {{2, 3}});
    auto r = build_leap_graph(cp);
    EXPECT_OK(r);
    EXPECT(sorted_leaps(r.value()) == (Edges{{0, 1}, {2, 3}}));
}

// Transitivity through the union-find: two existentials in one class.
//   ∃x (0), ∃y (1), ∀u (2). Link 1: p(x) ~ ¬p(y) ⇒ x = y.
//   Link 2: q(y) ~ ¬q(u) ⇒ y = u. Merged class {x,y,u}, anchor = u.
//   Dependencies: {x,u}, {y,u} → edges {0,2}, {1,2}.
void test_leap_dependency_transitive() {
    LeapFixture f;
    auto cp = make_leap_proof(
        /*n=*/7,
        {
            f.binder(0, true),    // ∃x
            f.binder(1, true),    // ∃y
            f.binder(2, false),   // ∀u
            f.atom(f.p1, false, {Term::fixed(0)}),
            f.atom(f.p1, true,  {Term::fixed(1)}),
            f.atom(f.q1, false, {Term::fixed(1)}),
            f.atom(f.q1, true,  {Term::fixed(2)}),
        },
        {{3, 4}, {5, 6}});
    auto r = build_leap_graph(cp);
    EXPECT_OK(r);
    EXPECT(sorted_leaps(r.value()) ==
           (Edges{{0, 2}, {1, 2}, {3, 4}, {5, 6}}));
}

// An existential constrained only by an equation with itself
// (p(x) ~ ¬p(x)) → no anchor → no dependency.
void test_leap_unconstrained_existential() {
    LeapFixture f;
    auto cp = make_leap_proof(
        /*n=*/3,
        {
            f.binder(0, true),
            f.atom(f.p1, false, {Term::fixed(0)}),
            f.atom(f.p1, true,  {Term::fixed(0)}),
        },
        {{1, 2}});
    auto r = build_leap_graph(cp);
    EXPECT_OK(r);
    EXPECT(sorted_leaps(r.value()) == (Edges{{1, 2}}));
}

// Two distinct rigids forced onto one existential class ⇒ no dualizer.
//   Link 1: p(x) ~ ¬p(u1) ⇒ anchor[x] = Fixed(u1).
//   Link 2: q(x) ~ ¬q(u2) ⇒ set_anchor(x, Fixed(u2)) finds a conflict.
//   build_leap_graph returns an error.
void test_leap_unification_conflict_returns_error() {
    LeapFixture f;
    auto cp = make_leap_proof(
        /*n=*/7,
        {
            f.binder(0, true),    // ∃x
            f.binder(1, false),   // ∀u1
            f.binder(2, false),   // ∀u2
            f.atom(f.p1, false, {Term::fixed(0)}),
            f.atom(f.p1, true,  {Term::fixed(1)}),
            f.atom(f.q1, false, {Term::fixed(0)}),
            f.atom(f.q1, true,  {Term::fixed(2)}),
        },
        {{3, 4}, {5, 6}});
    auto r = build_leap_graph(cp);
    EXPECT_ERR(r);
}

// =====================================================================
// verify_fonet — 2C end-to-end (no induced bimatching)
// =====================================================================
//
// These tests exercise the verify_no_bimatching algorithm end-to-end
// through verify_fonet (which now calls build_leap_graph and then
// verify_no_bimatching). Each test pins one of the recursive cases:
//
//   A   — single literal / union of axioms (Lemma 10.17)
//   B   — universal binder stripping (Lemma 10.16)
//   C.1 — fusion at a bridge (Lemma 10.18)
//   C.2 — existential quantification (Lemmas 10.19/10.20)
//   ¬   — induced bimatching: bridge-in-Z not found, must reject

// Case A: a single truth literal *1. No edges, no binders. Hits Case A
// directly (no recursion needed).
void test_2C_case_A_single_one() {
    LeapFixture f;
    VertexLabel one_lbl;
    one_lbl.kind = VertexKind::One;

    CombProof cp;
    cp.source.num_vertex = 1;
    cp.target.labels     = {one_lbl};
    identity_fibration(cp, 1);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// Case B: ∀x. (p(x) ∧ ¬p(x)). The ∀x binder is +-disjoint from its
// scope (no incident cograph edge), so Case B strips it. The remaining
// W = {atoms} then has cograph edge {1,2} (from ∧) and proceeds via
// Case C.1 fusion (both atoms are literals) → recurses into singletons
// → Case A.
void test_2C_case_B_forall_strip() {
    LeapFixture f;
    CombProof cp;
    cp.source.num_vertex    = 3;
    cp.source.cograph_edges = {{1, 2}};          // ∧ between atoms
    cp.source.links         = {{1, 2}};
    cp.target.labels = {
        f.binder(0, /*existential=*/false),       // ∀x
        f.atom(f.p1, false, {Term::fixed(0)}),    // p(x)
        f.atom(f.p1, true,  {Term::fixed(0)}),    // ¬p(x)
    };
    identity_fibration(cp, 3);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// Case C.2: ∀y. ∃x. (P(x) ∨ ¬P(x)).
// - ∀y is +-disjoint → stripped in Case B.
// - Then ∃x is ×-joined to its scope: Case C decomposes with
//   parts = [{∃x}, {atoms 2, 3}]. Sub-case C.2 (∃x has no literal,
//   atoms side does) strips ∃x, recurses.
// - Recurse on {2, 3}: no cograph edges left (∨ between atoms), Case A.
// δ(x) = y maps the existential to the universal.
void test_2C_case_C2_exists_quantification() {
    LeapFixture f;
    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {{1, 2}, {1, 3}};   // ∃x × {atoms}, no ∧
    cp.source.links         = {{2, 3}};
    cp.source.dualizer      = {{1, Term::fixed(0)}};   // x ↦ y
    cp.target.labels = {
        f.binder(0, /*existential=*/false),        // ∀y
        f.binder(1, /*existential=*/true),         // ∃x
        f.atom(f.p1, false, {Term::fixed(1)}),     // P(x)
        f.atom(f.p1, true,  {Term::fixed(1)}),     // ¬P(x)
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// Case C.1: (A ∧ ¬A) ∨ (B ∧ ¬B). Two disjoint ×-pairs (2K2 cograph),
// no binders. Case C builds parts = [[0], [1], [2], [3]]. The Ω graph
// has edges 0-1 and 2-3 (only, since the leaps are the links which
// coincide with the cograph edges). Bridge (0,1) exists → split into
// W_left, W_right. C.1 fusion: both halves contain literals.
// Recursion through each half eventually hits Case A.
void test_2C_case_C1_fusion() {
    LeapFixture f;
    PredicateHandle p0 = f.ctx.add_predicate("a", 0);
    PredicateHandle q0 = f.ctx.add_predicate("b", 0);

    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {{0, 1}, {2, 3}};   // (A ∧ ¬A) and (B ∧ ¬B)
    cp.source.links         = {{0, 1}, {2, 3}};
    cp.target.labels = {
        f.atom(p0, false, {}),                     // A
        f.atom(p0, true,  {}),                     // ¬A
        f.atom(q0, false, {}),                     // B
        f.atom(q0, true,  {}),                     // ¬B
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// Case C.1 fusion with an L-to-L pair: (A ∧ ¬A) ∨ B ∨ ¬B.
//   - (A ∧ ¬A) contributes cograph edge {0, 1} and link {0, 1}.
//   - B and ¬B are +-disjoint singletons, linked to each other.
// Case C decomposes:
//   parts = [[0], [1]] (from the UNION{0,1} child of root JOIN),
//   L     = [2, 3] (lone literals at root JOIN, link mates *each other*).
// Bridge (0,1) → fusion split. The L-partition step sees mate[2]=3 and
// part_of[3]=-1 (3 is in L, not in any part), so both 2 and 3 fall
// into the "mate in L → W_left" branch and *stay together* on the
// left side. Then recurse on W_left={0,2,3} (Case A) and W_right={1}
// (Case A).
void test_2C_case_C1_fusion_LtoL_pair() {
    LeapFixture f;
    PredicateHandle a0 = f.ctx.add_predicate("a", 0);
    PredicateHandle b0 = f.ctx.add_predicate("b", 0);

    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {{0, 1}};              // only the (A ∧ ¬A) ∧-edge
    cp.source.links         = {{0, 1}, {2, 3}};      // A-¬A, B-¬B (the L-to-L pair)
    cp.target.labels = {
        f.atom(a0, false, {}),   // A
        f.atom(a0, true,  {}),   // ¬A
        f.atom(b0, false, {}),   // B   (lone literal in L)
        f.atom(b0, true,  {}),   // ¬B  (lone literal in L, linked to B)
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_OK(v.verify_fonet(cp));
}

// Bimatching rejection: (A ∧ B) ∨ (¬A ∧ ¬B) with crossing links.
// Cograph structure: 2K2 ({0,1} ∧-pair, {2,3} ∧-pair, ∨-disjoint).
// Links cross the ∨: {0, 2} (A linked to ¬A) and {1, 3} (B linked to ¬B).
// In Case C:
//   parts = [[0], [1], [2], [3]]; n=4.
//   Ω edges: 0-1 (cograph), 2-3 (cograph), 0-2 (link/leap), 1-3 (link/leap).
//   Z = {(0,1), (2,3)}.
//   Removing (0,1): still connected via 0-2-3-1. Not a bridge.
//   Removing (2,3): still connected via 2-0-1-3. Not a bridge.
//   ⇒ no bridge in Z ⇒ induced bimatching exists ⇒ verifier rejects.
void test_2C_bimatching_rejected() {
    LeapFixture f;
    PredicateHandle p0 = f.ctx.add_predicate("a", 0);
    PredicateHandle q0 = f.ctx.add_predicate("b", 0);

    CombProof cp;
    cp.source.num_vertex    = 4;
    cp.source.cograph_edges = {{0, 1}, {2, 3}};   // (A ∧ B) and (¬A ∧ ¬B)
    cp.source.links         = {{0, 2}, {1, 3}};   // crossing pre-dual links
    cp.target.labels = {
        f.atom(p0, false, {}),                     // A
        f.atom(q0, false, {}),                     // B
        f.atom(p0, true,  {}),                     // ¬A
        f.atom(q0, true,  {}),                     // ¬B
    };
    identity_fibration(cp, 4);

    CombVerifier v;
    EXPECT_ERR(v.verify_fonet(cp));
}

}  // namespace

int main() {
    test_cotree_empty();
    test_cotree_singleton();
    test_cotree_k2();
    test_cotree_k2_complement();
    test_cotree_p4_not_cograph();
    test_cotree_2K2();
    test_cotree_k3_triangle();
    test_cotree_self_loop_ignored();
    test_cotree_duplicate_edge_ok();

    test_2A3_legal_one_binder_two_atoms();
    test_2A3_c1_no_literal_in_scope();
    test_2A3_c2_duplicate_var_binder_in_scope();
    test_2A3_distinct_var_binders_in_scope_ok();
    test_2A3_singleton_binder_no_scope();
    test_2A3_source_not_a_cograph();

    test_boundary_reject_description_in_goal();
    test_boundary_reject_description_in_label_args();
    test_boundary_reject_description_in_dualizer_image();

    test_builder_atom_zero_ary();
    test_builder_negated_atom();
    test_builder_and();
    test_builder_or_no_edges();
    test_builder_forall_unary();
    test_builder_exists_unary();
    test_builder_exists_conj();
    test_builder_nested_quantifiers();

    test_phase1_roundtrip_simple();
    test_phase1_roundtrip_quantified();
    test_phase1_nnf_normalization();
    test_phase1_vertex_count_mismatch();
    test_phase1_label_mismatch();
    test_phase1_edge_mismatch();

    test_bifib_size_mismatch();
    test_bifib_identity_cograph_edge();
    test_bifib_skew_weakening_ok();
    test_bifib_contraction_ok();
    test_bifib_skew_fail_no_source_neighbour();
    test_bifib_cograph_homomorphism_fail();
    test_bifib_binding_identity_ok();
    test_bifib_binding_fail_missing_lift();
    test_bifib_binding_fail_nonunique_lift();
    test_bifib_binding_homomorphism_fail();
    test_bifib_full_exists_identity_ok();

    test_leap_empty();
    test_leap_links_no_binders();
    test_leap_dependency_simple();
    test_leap_dependency_transitive();
    test_leap_unconstrained_existential();
    test_leap_unification_conflict_returns_error();

    test_2C_case_A_single_one();
    test_2C_case_B_forall_strip();
    test_2C_case_C2_exists_quantification();
    test_2C_case_C1_fusion();
    test_2C_case_C1_fusion_LtoL_pair();
    test_2C_bimatching_rejected();

    std::cout << "comb_test: " << g_passed << " passed, "
              << g_failed << " failed\n";
    return g_failed == 0 ? 0 : 1;
}
