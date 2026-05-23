#include "src/proof/translate/ks1_to_comb/read_skew.h"

#include "src/proof/ks1/checker.h"
#include "src/proof/ks1/decompose.h"
#include "src/proof/translate/ks1_to_comb/read_fonet.h"

#include <vector>

namespace logic::proof::ks1_to_comb {

using logic::proof::ks1::Derivation;
using logic::proof::ks1::Dir;
using logic::proof::ks1::EqDir;
using logic::proof::ks1::EqRule;
using logic::proof::ks1::Path;
using logic::proof::ks1::Rule;
using logic::proof::ks1::Step;
using util::Result;

namespace {

struct TArg { bool bound; size_t binder_tag; var_index fixed; };

// Mirror node carrying the set of source A'-vertices that have flowed into it
// (empty = weakened-in / uncovered).
struct MNode {
    enum K { One, Atom, And, Or, Forall, Exists } k;
    PredicateHandle pred{};
    bool            neg{false};
    std::vector<TArg> args{};
    size_t          l{0}, r{0};
    size_t          binder_tag{0};
    size_t          child{0};
    std::vector<size_t> src{};   // source A'-vertex indices flowed here
};

struct Arena {
    std::vector<MNode> nodes;
    size_t next_binder{0};
    size_t add(MNode n) { nodes.push_back(std::move(n)); return nodes.size() - 1; }
    size_t bin(MNode::K k, size_t l, size_t r) {
        MNode n{k}; n.l = l; n.r = r; return add(std::move(n));
    }
    size_t quant(MNode::K k, size_t child, size_t bt) {
        MNode n{k}; n.child = child; n.binder_tag = bt; return add(std::move(n));
    }
    size_t fresh_binder() { return next_binder++; }
};

bool is_topf(FormulaHandle h) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == Op::Not && f.as_compound().left.valid() &&
           f.as_compound().left.get().is_compound() &&
           f.as_compound().left.get().as_compound().op == Op::Bottom;
}

// Convert a core formula to the mirror, resolving De Bruijn atom args to binder
// tags via `stack`. If `assign_src`, each One/Atom/binder node gets the next
// pre-order source index (matching comb::Fograph order); else src stays empty.
size_t to_mirror(Arena& a, FormulaHandle h, std::vector<size_t>& stack,
                 bool assign_src, size_t& src_ctr) {
    const Formula& f = h.get();
    if (f.is_predicate()) {
        MNode n{MNode::Atom}; n.pred = f.as_predicate().predicate();
        for (const Term& t : f.as_predicate().args()) {
            if (t.is_generalized())
                n.args.push_back({true, stack[stack.size() - 1 - t.as_variable()], 0});
            else
                n.args.push_back({false, 0, t.as_variable()});
        }
        if (assign_src) n.src.push_back(src_ctr);
        ++src_ctr;
        return a.add(std::move(n));
    }
    if (f.is_compound()) {
        const Compound& c = f.as_compound();
        if (c.op == Op::Not) {
            if (is_topf(h)) { MNode n{MNode::One}; if (assign_src) n.src.push_back(src_ctr); ++src_ctr; return a.add(std::move(n)); }
            // ¬predicate
            MNode n{MNode::Atom}; n.neg = true; n.pred = c.left.get().as_predicate().predicate();
            for (const Term& t : c.left.get().as_predicate().args()) {
                if (t.is_generalized())
                    n.args.push_back({true, stack[stack.size() - 1 - t.as_variable()], 0});
                else
                    n.args.push_back({false, 0, t.as_variable()});
            }
            if (assign_src) n.src.push_back(src_ctr);
            ++src_ctr;
            return a.add(std::move(n));
        }
        size_t l = to_mirror(a, c.left, stack, assign_src, src_ctr);
        size_t r = to_mirror(a, c.right, stack, assign_src, src_ctr);
        return a.bin(c.op == Op::And ? MNode::And : MNode::Or, l, r);
    }
    // quantified
    const Quantified& q = f.as_quantified();
    size_t bt = a.fresh_binder();
    size_t self;
    {
        MNode n{q.op == Op::Forall ? MNode::Forall : MNode::Exists}; n.binder_tag = bt;
        if (assign_src) n.src.push_back(src_ctr);
        ++src_ctr;
        self = a.add(std::move(n));
    }
    stack.push_back(bt);
    size_t child = to_mirror(a, q.body, stack, assign_src, src_ctr);
    stack.pop_back();
    a.nodes[self].child = child;
    return self;
}

// Atoms / units are leaves; navigation only descends into ∧/∨ (Left/Right) or
// a quantifier (Down). See checker.cpp::is_navigable_binary.
bool is_nav_binary(MNode::K k) { return k == MNode::And || k == MNode::Or; }

// Navigate to redex, collecting enclosing binder tags.
Result<size_t> nav(const Arena& a, size_t root, const Path& p, size_t i,
                   std::vector<size_t>& stack) {
    if (i == p.size()) return root;
    const MNode& n = a.nodes[root];
    switch (p[i]) {
        case Dir::Left:
            if (!is_nav_binary(n.k)) return MAKE_ERROR << "skew: Left into non-∧/∨";
            return nav(a, n.l, p, i + 1, stack);
        case Dir::Right:
            if (!is_nav_binary(n.k)) return MAKE_ERROR << "skew: Right into non-∧/∨";
            return nav(a, n.r, p, i + 1, stack);
        case Dir::Down:
            if (n.k != MNode::Forall && n.k != MNode::Exists) return MAKE_ERROR << "skew: Down";
            stack.push_back(n.binder_tag);
            return nav(a, n.child, p, i + 1, stack);
    }
    return MAKE_ERROR << "skew: bad dir";
}

Result<size_t> rewrite(Arena& a, size_t root, const Path& p, size_t i, size_t sub) {
    if (i == p.size()) return sub;
    const MNode n = a.nodes[root];
    if (p[i] == Dir::Down) {
        if (n.k != MNode::Forall && n.k != MNode::Exists) return MAKE_ERROR << "skew: Down";
        auto c = rewrite(a, n.child, p, i + 1, sub);
        if (c.is_error()) return std::move(c).error();
        return a.quant(n.k, c.value(), n.binder_tag);
    }
    if (!is_nav_binary(n.k)) return MAKE_ERROR << "skew: descent into non-∧/∨";
    if (p[i] == Dir::Left) {
        auto c = rewrite(a, n.l, p, i + 1, sub);
        if (c.is_error()) return std::move(c).error();
        return a.bin(n.k, c.value(), n.r);
    }
    auto c = rewrite(a, n.r, p, i + 1, sub);
    if (c.is_error()) return std::move(c).error();
    return a.bin(n.k, n.l, c.value());
}

// Rewrite atom-arg binder references old→new in a subtree (for binder merges).
void rebind(Arena& a, size_t idx, size_t old_bt, size_t new_bt) {
    MNode& n = a.nodes[idx];
    switch (n.k) {
        case MNode::Atom:
            for (TArg& t : n.args) if (t.bound && t.binder_tag == old_bt) t.binder_tag = new_bt;
            return;
        case MNode::And: case MNode::Or: rebind(a, n.l, old_bt, new_bt); rebind(a, n.r, old_bt, new_bt); return;
        case MNode::Forall: case MNode::Exists: rebind(a, n.child, old_bt, new_bt); return;
        case MNode::One: return;
    }
}

std::vector<size_t> merge_src(const std::vector<size_t>& a, const std::vector<size_t>& b) {
    std::vector<size_t> out = a;
    out.insert(out.end(), b.begin(), b.end());
    return out;
}

struct State { Arena a; size_t root; };

util::ResultStatus apply_res(State& st, const Step& s) {
    Arena& a = st.a;
    std::vector<size_t> stack;
    auto rx = nav(a, st.root, s.context, 0, stack);
    if (rx.is_error()) return std::move(rx).error();
    size_t R = rx.value();
    auto put = [&](size_t sub) -> util::ResultStatus {
        auto nr = rewrite(a, st.root, s.context, 0, sub);
        if (nr.is_error()) return std::move(nr).error();
        st.root = nr.value();
        return util::Ok();
    };
    switch (s.rule) {
        case Rule::W: {  // S{A}/S{A∨B}: B weakened-in (empty src)
            if (!s.f_param.valid()) return MAKE_ERROR << "skew: w missing B";
            size_t ctr = 0;  // src not assigned for weakened-in
            size_t b = to_mirror(a, s.f_param, stack, false, ctr);
            return put(a.bin(MNode::Or, R, b));
        }
        case Rule::WForall: {  // S{A}/S{∀x.A}: new uncovered binder
            size_t bt = a.fresh_binder();
            return put(a.quant(MNode::Forall, R, bt));  // new binder node: empty src
        }
        case Rule::Ac: {  // S{a∨a}/S{a}: merge the two atoms' src
            const MNode& n = a.nodes[R];
            if (n.k != MNode::Or) return MAKE_ERROR << "skew: ac not ∨";
            size_t keep = n.l, other = n.r;
            a.nodes[keep].src = merge_src(a.nodes[keep].src, a.nodes[other].src);
            return put(keep);
        }
        case Rule::CForall: {  // S{∀x.∀x.A}/S{∀x.A}: merge two universal binders
            const MNode& n = a.nodes[R];
            if (n.k != MNode::Forall || a.nodes[n.child].k != MNode::Forall)
                return MAKE_ERROR << "skew: c∀ not ∀∀";
            size_t inner = n.child;
            size_t body = a.nodes[inner].child;
            size_t outer_bt = n.binder_tag, inner_bt = a.nodes[inner].binder_tag;
            rebind(a, body, inner_bt, outer_bt);  // inner refs → outer (kept) binder
            size_t merged = a.quant(MNode::Forall, body, outer_bt);
            a.nodes[merged].src = merge_src(n.src, a.nodes[inner].src);
            return put(merged);
        }
        case Rule::M: {  // S{(A∧C)∨(B∧D)}/S{(A∨B)∧(C∨D)}: identity on vertices
            const MNode& n = a.nodes[R];
            if (n.k != MNode::Or || a.nodes[n.l].k != MNode::And || a.nodes[n.r].k != MNode::And)
                return MAKE_ERROR << "skew: m shape";
            size_t A = a.nodes[n.l].l, C = a.nodes[n.l].r, B = a.nodes[n.r].l, D = a.nodes[n.r].r;
            return put(a.bin(MNode::And, a.bin(MNode::Or, A, B), a.bin(MNode::Or, C, D)));
        }
        case Rule::MForall:    // S{(∀x.A)∨(∀x.B)}/S{∀x.(A∨B)}: merge two binders
        case Rule::MExists: {
            MNode::K q = (s.rule == Rule::MForall) ? MNode::Forall : MNode::Exists;
            const MNode& n = a.nodes[R];
            if (n.k != MNode::Or || a.nodes[n.l].k != q || a.nodes[n.r].k != q)
                return MAKE_ERROR << "skew: medial-quant shape";
            size_t lq = n.l, rq = n.r;
            size_t lbt = a.nodes[lq].binder_tag, rbt = a.nodes[rq].binder_tag;
            size_t lbody = a.nodes[lq].child, rbody = a.nodes[rq].child;
            rebind(a, rbody, rbt, lbt);  // right binder refs → kept (left) binder
            size_t merged = a.quant(q, a.bin(MNode::Or, lbody, rbody), lbt);
            a.nodes[merged].src = merge_src(a.nodes[lq].src, a.nodes[rq].src);
            return put(merged);
        }
        case Rule::Eqv: {  // identity on vertices; restructure only
            const MNode n = a.nodes[R];
            auto comm = [&](MNode::K k) -> util::ResultStatus {
                if (n.k != k) return MAKE_ERROR << "skew: ≡ comm";
                return put(a.bin(k, n.r, n.l));
            };
            auto assoc = [&](MNode::K k) -> util::ResultStatus {
                if (s.dir == EqDir::Forward) {
                    if (n.k != k || a.nodes[n.l].k != k) return MAKE_ERROR << "skew: ≡ assoc→";
                    size_t A = a.nodes[n.l].l, B = a.nodes[n.l].r, C = n.r;
                    return put(a.bin(k, A, a.bin(k, B, C)));
                }
                if (n.k != k || a.nodes[n.r].k != k) return MAKE_ERROR << "skew: ≡ assoc←";
                size_t A = n.l, B = a.nodes[n.r].l, C = a.nodes[n.r].r;
                return put(a.bin(k, a.bin(k, A, B), C));
            };
            auto swap = [&](MNode::K q) -> util::ResultStatus {
                if (n.k != q || a.nodes[n.child].k != q) return MAKE_ERROR << "skew: ≡ swap";
                size_t inner = n.child, body = a.nodes[inner].child;
                size_t ib = a.nodes[inner].binder_tag;
                size_t outerNew = a.quant(q, body, n.binder_tag);
                size_t res = a.quant(q, outerNew, ib);
                a.nodes[res].src = n.src;                       // outer keeps src
                a.nodes[outerNew].src = a.nodes[inner].src;     // inner keeps src
                return put(res);
            };
            auto dist = [&](MNode::K q, MNode::K op) -> util::ResultStatus {
                if (s.dir == EqDir::Forward) {
                    if (n.k != q || a.nodes[n.child].k != op) return MAKE_ERROR << "skew: ≡ dist→";
                    size_t A = a.nodes[n.child].l, B = a.nodes[n.child].r;
                    size_t fq = a.quant(q, A, n.binder_tag);
                    a.nodes[fq].src = n.src;
                    return put(a.bin(op, fq, B));
                }
                if (n.k != op || a.nodes[n.l].k != q) return MAKE_ERROR << "skew: ≡ dist←";
                size_t A = a.nodes[n.l].child, B = n.r;
                size_t res = a.quant(q, a.bin(op, A, B), a.nodes[n.l].binder_tag);
                a.nodes[res].src = a.nodes[n.l].src;
                return put(res);
            };
            switch (s.eq) {
                case EqRule::CommAnd: return comm(MNode::And);
                case EqRule::CommOr:  return comm(MNode::Or);
                case EqRule::AssocAnd:return assoc(MNode::And);
                case EqRule::AssocOr: return assoc(MNode::Or);
                case EqRule::SwapForall: return swap(MNode::Forall);
                case EqRule::SwapExists: return swap(MNode::Exists);
                case EqRule::DistForall: return dist(MNode::Forall, MNode::Or);
                case EqRule::DistExists: return dist(MNode::Exists, MNode::And);
            }
            return MAKE_ERROR << "skew: unknown ≡";
        }
        default:
            return MAKE_ERROR << "skew: unsupported resource rule";
    }
}

// Reconstruct B from the mirror in fograph pre-order, assigning each node its
// B-vertex index and recording fibration[src] = that index.
struct Recon {
    FormulaBuilder& fb;
    Arena& a;
    std::vector<size_t> stack;
    size_t next_vertex{0};
    std::vector<size_t> fib;  // source vertex → B vertex (sized to source count)

    FormulaHandle go(size_t idx) {
        MNode& n = a.nodes[idx];
        size_t here = next_vertex;
        auto record = [&]{ for (size_t s : n.src) { if (s >= fib.size()) fib.resize(s + 1, SIZE_MAX); fib[s] = here; } };
        switch (n.k) {
            case MNode::One: ++next_vertex; record(); return fb.make_not(fb.make_bottom());
            case MNode::Atom: {
                ++next_vertex; record();
                std::vector<Term> args;
                for (const TArg& t : n.args) {
                    if (t.bound) {
                        size_t pos = 0;
                        for (size_t i = stack.size(); i-- > 0;) if (stack[i] == t.binder_tag) { pos = stack.size() - 1 - i; break; }
                        args.push_back(Term::generalized(pos));
                    } else args.push_back(Term::fixed(t.fixed));
                }
                FormulaHandle at = fb.predicate(n.pred, std::move(args));
                return n.neg ? fb.make_not(at) : at;
            }
            case MNode::And: { auto l = go(n.l); auto r = go(n.r); return fb.make_and(l, r); }
            case MNode::Or:  { auto l = go(n.l); auto r = go(n.r); return fb.make_or(l, r); }
            case MNode::Forall: case MNode::Exists: {
                ++next_vertex; record();
                size_t bt = n.binder_tag, child = n.child;
                stack.push_back(bt);
                auto body = go(child);
                stack.pop_back();
                return fb.make_quantified(n.k == MNode::Forall ? Op::Forall : Op::Exists, body);
            }
        }
        return fb.make_not(fb.make_bottom());
    }
};

}  // namespace

Result<SkewReadoff> read_skew(FormulaBuilder& fb, const Derivation& phi2) {
    State st;
    std::vector<size_t> stack;
    size_t src_ctr = 0;
    st.root = to_mirror(st.a, phi2.top, stack, /*assign_src=*/true, src_ctr);
    size_t source_count = src_ctr;

    for (const Step& s : phi2.steps) {
        auto r = apply_res(st, s);
        if (r.is_error()) return std::move(r).error();
    }

    Recon rec{fb, st.a};
    rec.fib.assign(source_count, SIZE_MAX);
    FormulaHandle b_rec = rec.go(st.root);

    auto real = logic::proof::ks1::replay(fb, phi2.top, phi2.steps);
    if (real.is_error()) return std::move(real).error();
    if (!(b_rec == real.value()))
        return MAKE_ERROR << "read_skew: reconstruction != Φ2 conclusion";

    for (size_t s = 0; s < rec.fib.size(); ++s)
        if (rec.fib[s] == SIZE_MAX)
            return MAKE_ERROR << "read_skew: source vertex " << s << " has no image (fibration not total)";

    SkewReadoff out;
    out.b = b_rec;
    out.target = comb::Fograph(b_rec);
    out.fibration = std::move(rec.fib);
    return out;
}

Result<comb::CombProof> build_comb_proof(FormulaBuilder& fb, const Derivation& d) {
    auto sp = logic::proof::ks1::split(fb, d);
    if (sp.is_error()) return std::move(sp).error();

    auto fonet = read_fonet(fb, sp.value().phi1);
    if (fonet.is_error()) return std::move(fonet).error();

    auto skew = read_skew(fb, sp.value().phi2);
    if (skew.is_error()) return std::move(skew).error();

    if (fonet.value().fonet.num_vertex != skew.value().fibration.size())
        return MAKE_ERROR << "bridge: fonet/fibration source-size mismatch";

    comb::CombProof cp;
    cp.source    = fonet.value().fonet;
    cp.target    = skew.value().target;
    cp.fibration = skew.value().fibration;
    return cp;
}

}  // namespace logic::proof::ks1_to_comb
