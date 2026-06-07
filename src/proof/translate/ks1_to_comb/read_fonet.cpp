#include "src/proof/translate/ks1_to_comb/read_fonet.h"

#include "src/proof/ks1/checker.h"

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

// ---- tagged mirror tree (occurrence-stable provenance) ---------------
//
// Mirrors A' in NNF; binders and atoms carry stable tags so we can map them to
// fograph pre-order vertices after replay. Children are arena indices.

struct TArg { bool bound; size_t binder_tag; var_index fixed; };

struct TNode {
    enum K { One, Atom, And, Or, Forall, Exists } k;
    // Atom
    PredicateHandle pred{};
    bool            neg{false};
    std::vector<TArg> args{};
    size_t          occ{0};        // stable atom-occurrence tag
    // And/Or
    size_t l{0}, r{0};
    // Forall/Exists
    size_t binder_tag{0};
    size_t child{0};
};

struct Arena {
    std::vector<TNode> nodes;
    size_t next_occ{0};
    size_t next_binder{0};

    size_t add(TNode n) { nodes.push_back(std::move(n)); return nodes.size() - 1; }
    size_t one() { return add(TNode{TNode::One}); }
    size_t atom(PredicateHandle p, bool neg, std::vector<TArg> a) {
        TNode n{TNode::Atom}; n.pred = p; n.neg = neg; n.args = std::move(a);
        n.occ = next_occ++; return add(std::move(n));
    }
    size_t bin(TNode::K k, size_t l, size_t r) {
        TNode n{k}; n.l = l; n.r = r; return add(std::move(n));
    }
    size_t quant(TNode::K k, size_t child, size_t binder_tag) {
        TNode n{k}; n.child = child; n.binder_tag = binder_tag; return add(std::move(n));
    }
    size_t fresh_binder() { return next_binder++; }
};

// Only ∧/∨ are navigable (Left/Right) — atoms and units are leaves. The hole
// must stay in atom position (paper §V); see checker.cpp::is_navigable_binary.
bool is_nav_binary(TNode::K k) { return k == TNode::And || k == TNode::Or; }

// ---- AC-tolerant ∧/∨-chain helpers on the tagged tree --------------------
// Mirror checker.cpp's flatten_chain/build_chain so the bridge can match a
// rule's redex against a flattened canonical chain (tags ride along, since we
// only rearrange / re-wrap existing subtree indices).
void flatten_t(const Arena& a, size_t idx, TNode::K k, std::vector<size_t>& out) {
    const TNode& n = a.nodes[idx];
    if (n.k == k && (k == TNode::And || k == TNode::Or)) {
        flatten_t(a, n.l, k, out);
        flatten_t(a, n.r, k, out);
    } else {
        out.push_back(idx);
    }
}
size_t build_t(Arena& a, TNode::K k, const std::vector<size_t>& ops) {
    size_t acc = ops.back();
    for (size_t i = ops.size() - 1; i-- > 0;) acc = a.bin(k, ops[i], acc);
    return acc;
}
// Does any atom under `idx` reference the universal/existential binder `bt`?
bool refers_binder(const Arena& a, size_t idx, size_t bt) {
    const TNode& n = a.nodes[idx];
    switch (n.k) {
        case TNode::Atom:
            for (const TArg& t : n.args)
                if (t.bound && t.binder_tag == bt) return true;
            return false;
        case TNode::And: case TNode::Or:
            return refers_binder(a, n.l, bt) || refers_binder(a, n.r, bt);
        case TNode::Forall: case TNode::Exists:
            return refers_binder(a, n.child, bt);
        default: return false;
    }
}

// Navigate to the redex index, collecting the enclosing binder-tag stack
// (outermost first) for Gen-resolution.
Result<size_t> nav(const Arena& a, size_t root, const Path& p, size_t i,
                   std::vector<size_t>& stack) {
    if (i == p.size()) return root;
    const TNode& n = a.nodes[root];
    switch (p[i]) {
        case Dir::Left:
            if (!is_nav_binary(n.k))
                return MAKE_ERROR << "read_fonet: Left into non-∧/∨ node";
            return nav(a, n.l, p, i + 1, stack);
        case Dir::Right:
            if (!is_nav_binary(n.k))
                return MAKE_ERROR << "read_fonet: Right into non-∧/∨ node";
            return nav(a, n.r, p, i + 1, stack);
        case Dir::Down:
            if (n.k != TNode::Forall && n.k != TNode::Exists)
                return MAKE_ERROR << "read_fonet: Down into non-quantifier";
            stack.push_back(n.binder_tag);
            return nav(a, n.child, p, i + 1, stack);
    }
    return MAKE_ERROR << "read_fonet: bad dir";
}

// Functional rewrite: rebuild internal nodes along the path; share leaves.
Result<size_t> rewrite(Arena& a, size_t root, const Path& p, size_t i, size_t sub) {
    if (i == p.size()) return sub;
    const TNode n = a.nodes[root];  // copy (vector may reallocate)
    if (p[i] == Dir::Down) {
        if (n.k != TNode::Forall && n.k != TNode::Exists)
            return MAKE_ERROR << "read_fonet: Down into non-quantifier";
        auto c = rewrite(a, n.child, p, i + 1, sub);
        if (c.is_error()) return std::move(c).error();
        return a.quant(n.k, c.value(), n.binder_tag);
    }
    if (!is_nav_binary(n.k))
        return MAKE_ERROR << "read_fonet: descent into non-∧/∨ node";
    if (p[i] == Dir::Left) {
        auto c = rewrite(a, n.l, p, i + 1, sub);
        if (c.is_error()) return std::move(c).error();
        return a.bin(n.k, c.value(), n.r);
    }
    auto c = rewrite(a, n.r, p, i + 1, sub);
    if (c.is_error()) return std::move(c).error();
    return a.bin(n.k, n.l, c.value());
}

// Resolve a core Term to a TArg using the enclosing binder-tag stack.
TArg resolve_term(const Term& t, const std::vector<size_t>& stack) {
    if (t.is_generalized()) {
        var_index k = t.as_variable();
        // Gen(k) = k-th nearest enclosing binder.
        return TArg{true, stack[stack.size() - 1 - k], 0};
    }
    return TArg{false, 0, t.as_variable()};  // Fixed (eigenvar / witness const)
}

// A literal's predicate + polarity + args (resolved).
struct Lit { PredicateHandle pred; bool neg; std::vector<TArg> args; };
Result<Lit> literal_of(FormulaHandle h, const std::vector<size_t>& stack) {
    const Formula& f = h.get();
    bool neg = false;
    FormulaHandle atom = h;
    if (f.is_compound() && f.as_compound().op == Op::Not && f.as_compound().left.valid()) {
        neg = true; atom = f.as_compound().left;
    }
    if (!atom.get().is_predicate())
        return MAKE_ERROR << "read_fonet: ai parameter not an atomic literal";
    const PredicateInstance& pi = atom.get().as_predicate();
    std::vector<TArg> args;
    for (const Term& t : pi.args()) args.push_back(resolve_term(t, stack));
    return Lit{pi.predicate(), neg, std::move(args)};
}

// Provenance accumulated during replay.
struct Prov {
    Arena arena;
    size_t root{0};
    std::vector<std::pair<size_t, size_t>> links;          // ai pairs (occ, occ)
    std::vector<std::pair<size_t, TArg>>   dualizer_raw;    // (exists binder_tag, witness)
};

// Flatten a maximal core-formula `op`-chain into operands.
void flatten_core(FormulaHandle h, Op op, std::vector<FormulaHandle>& out) {
    const Formula& f = h.get();
    if (f.is_compound() && f.as_compound().op == op) {
        flatten_core(f.as_compound().left, op, out);
        flatten_core(f.as_compound().right, op, out);
    } else {
        out.push_back(h);
    }
}

// Does the ∃-body operand `body` (core, Gen0=x at `depth`) denote the same
// formula skeleton as the tagged subtree `tf` (canonical, x-positions hold the
// witness)? Used to pair ∨/∧ operands when canonicalization reordered them, so
// rebind_exists rebinds the right atoms. Checks predicate/polarity/shape (enough
// to disambiguate operands; the modulo-≡ instance check is the soundness gate).
bool aligns(const Arena& a, FormulaHandle body, size_t tf, var_index depth) {
    const Formula& bf = body.get();
    const TNode& tn = a.nodes[tf];
    if (bf.is_predicate())
        return tn.k == TNode::Atom && !tn.neg &&
               tn.pred == bf.as_predicate().predicate() &&
               tn.args.size() == bf.as_predicate().args().size();
    if (bf.is_compound()) {
        const Compound& c = bf.as_compound();
        if (c.op == Op::Not) {
            if (c.left.valid() && c.left.get().is_predicate())
                return tn.k == TNode::Atom && tn.neg &&
                       tn.pred == c.left.get().as_predicate().predicate() &&
                       tn.args.size() == c.left.get().as_predicate().args().size();
            return tn.k == TNode::One;                       // ¬⊥
        }
        if (c.op == Op::And || c.op == Op::Or) {
            TNode::K k = c.op == Op::And ? TNode::And : TNode::Or;
            if (tn.k != k) return false;
            std::vector<FormulaHandle> bops; flatten_core(body, c.op, bops);
            std::vector<size_t> tops; flatten_t(a, tf, k, tops);
            if (bops.size() != tops.size()) return false;
            std::vector<bool> used(tops.size(), false);
            for (FormulaHandle bo : bops) {
                bool m = false;
                for (size_t j = 0; j < tops.size(); ++j)
                    if (!used[j] && aligns(a, bo, tops[j], depth)) { used[j] = true; m = true; break; }
                if (!m) return false;
            }
            return true;
        }
        return false;
    }
    if (bf.is_quantified())
        return (tn.k == TNode::Forall || tn.k == TNode::Exists) &&
               aligns(a, bf.as_quantified().body, tn.child, depth + 1);
    return false;
}

// Co-recurse the ∃ body parameter (core, Gen0 = x) with the redex TF subtree;
// at each atom arg position where the body has Gen(0), rebind the TF atom's arg
// to the new existential binder. ∧/∨ operands are paired modulo ≡ (canonical
// reordering), via `aligns`. Returns error on shape mismatch.
util::ResultStatus rebind_exists(Arena& a, FormulaHandle body, size_t tf,
                                 size_t new_binder, var_index depth) {
    const Formula& bf = body.get();
    TNode& tn = a.nodes[tf];
    if (bf.is_predicate()) {
        if (tn.k != TNode::Atom) return MAKE_ERROR << "read_fonet: ∃ shape mismatch (atom)";
        const auto& pa = bf.as_predicate().args();
        if (pa.size() != tn.args.size()) return MAKE_ERROR << "read_fonet: ∃ arity";
        for (size_t i = 0; i < pa.size(); ++i)
            if (pa[i].is_generalized() && pa[i].as_variable() == depth)
                tn.args[i] = TArg{true, new_binder, 0};   // an x-position
        return util::Ok();
    }
    if (bf.is_compound()) {
        const Compound& c = bf.as_compound();
        if (c.op == Op::Not) {
            if (c.left.valid() && c.left.get().is_predicate()) {
                if (tn.k != TNode::Atom) return MAKE_ERROR << "read_fonet: ∃ shape (¬atom)";
                const auto& pa = c.left.get().as_predicate().args();
                for (size_t i = 0; i < pa.size() && i < tn.args.size(); ++i)
                    if (pa[i].is_generalized() && pa[i].as_variable() == depth)
                        tn.args[i] = TArg{true, new_binder, 0};
                return util::Ok();
            }
            return util::Ok();  // ¬⊥ = One: no args
        }
        if (c.op == Op::And || c.op == Op::Or) {
            TNode::K k = c.op == Op::And ? TNode::And : TNode::Or;
            if (tn.k != k) return MAKE_ERROR << "read_fonet: ∃ shape mismatch (∧/∨)";
            std::vector<FormulaHandle> bops; flatten_core(body, c.op, bops);
            std::vector<size_t> tops; flatten_t(a, tf, k, tops);
            if (bops.size() != tops.size())
                return MAKE_ERROR << "read_fonet: ∃ ∧/∨ arity mismatch";
            std::vector<bool> used(tops.size(), false);
            for (FormulaHandle bo : bops) {                  // pair operands modulo ≡
                size_t pick = SIZE_MAX;
                for (size_t j = 0; j < tops.size(); ++j)
                    if (!used[j] && aligns(a, bo, tops[j], depth)) { pick = j; break; }
                if (pick == SIZE_MAX)
                    return MAKE_ERROR << "read_fonet: ∃ cannot pair ∧/∨ operand";
                used[pick] = true;
                auto r = rebind_exists(a, bo, tops[pick], new_binder, depth);
                if (r.is_error()) return r;
            }
            return util::Ok();
        }
        return util::Ok();
    }
    if (bf.is_quantified()) {
        if (tn.k != TNode::Forall && tn.k != TNode::Exists)
            return MAKE_ERROR << "read_fonet: ∃ shape mismatch (quant)";
        size_t ch = tn.child;
        return rebind_exists(a, bf.as_quantified().body, ch, new_binder, depth + 1);
    }
    return util::Ok();
}

// Apply one MLS1^X step to the provenance tree.
util::ResultStatus apply_tf(Prov& pv, const Step& s) {
    Arena& a = pv.arena;
    std::vector<size_t> stack;
    auto redex = nav(a, pv.root, s.context, 0, stack);
    if (redex.is_error()) return std::move(redex).error();
    size_t R = redex.value();

    auto put = [&](size_t newsub) -> util::ResultStatus {
        auto nr = rewrite(a, pv.root, s.context, 0, newsub);
        if (nr.is_error()) return std::move(nr).error();
        pv.root = nr.value();
        return util::Ok();
    };

    switch (s.rule) {
        case Rule::ForallUnit: {
            if (a.nodes[R].k != TNode::One) return MAKE_ERROR << "read_fonet: ∀ redex not ⊤";
            size_t bt = a.fresh_binder();
            return put(a.quant(TNode::Forall, a.one(), bt));
        }
        case Rule::Ai: {
            if (a.nodes[R].k != TNode::One) return MAKE_ERROR << "read_fonet: ai redex not ⊤";
            auto lit = literal_of(s.f_param, stack);
            if (lit.is_error()) return std::move(lit).error();
            size_t a1 = a.atom(lit.value().pred, lit.value().neg, lit.value().args);
            size_t a2 = a.atom(lit.value().pred, !lit.value().neg, lit.value().args);
            pv.links.emplace_back(a.nodes[a1].occ, a.nodes[a2].occ);
            return put(a.bin(TNode::Or, a1, a2));
        }
        case Rule::Tu:
            return put(a.bin(TNode::And, R, a.one()));
        case Rule::Mix: {       // A∧B → A∨B  (AC: split the ∧-chain at `split`)
            if (a.nodes[R].k != TNode::And) return MAKE_ERROR << "read_fonet: mix redex not ∧";
            std::vector<size_t> conj; flatten_t(a, R, TNode::And, conj);
            size_t k = s.split ? s.split : 1;
            if (k >= conj.size()) return MAKE_ERROR << "read_fonet: mix split out of range";
            size_t A = build_t(a, TNode::And, {conj.begin(), conj.begin() + k});
            size_t B = build_t(a, TNode::And, {conj.begin() + k, conj.end()});
            return put(a.bin(TNode::Or, A, B));
        }
        case Rule::Sw: {        // A∧(B∨C) → (A∧B)∨C  (AC: pick the ∨-operand)
            if (a.nodes[R].k != TNode::And) return MAKE_ERROR << "read_fonet: s redex not a ∧";
            std::vector<size_t> conj; flatten_t(a, R, TNode::And, conj);
            size_t j = SIZE_MAX;
            if (!s.operands.empty()) {
                j = s.operands[0];
                if (j >= conj.size() || a.nodes[conj[j]].k != TNode::Or)
                    return MAKE_ERROR << "read_fonet: s selected ∧-operand not a ∨";
            } else {
                for (size_t i = 0; i < conj.size(); ++i)
                    if (a.nodes[conj[i]].k == TNode::Or) { j = i; break; }
                if (j == SIZE_MAX) return MAKE_ERROR << "read_fonet: s ∧ has no ∨-operand";
            }
            std::vector<size_t> disj; flatten_t(a, conj[j], TNode::Or, disj);
            size_t b = s.split;                               // index of the single B disjunct
            if (b >= disj.size()) return MAKE_ERROR << "read_fonet: s split out of range";
            size_t B = disj[b];
            std::vector<size_t> crest;
            for (size_t i = 0; i < disj.size(); ++i) if (i != b) crest.push_back(disj[i]);
            if (crest.empty()) return MAKE_ERROR << "read_fonet: s ∨ has no C remainder";
            size_t C = build_t(a, TNode::Or, crest);
            std::vector<size_t> rest;
            for (size_t i = 0; i < conj.size(); ++i) if (i != j) rest.push_back(conj[i]);
            if (rest.empty()) return MAKE_ERROR << "read_fonet: s ∧ has no A operand";
            size_t A = build_t(a, TNode::And, rest);
            return put(a.bin(TNode::Or, a.bin(TNode::And, A, B), C));
        }
        case Rule::Ex: {
            if (!s.f_param.valid()) return MAKE_ERROR << "read_fonet: ∃ missing body";
            size_t bt = a.fresh_binder();
            auto rb = rebind_exists(a, s.f_param, R, bt, 0);
            if (rb.is_error()) return rb;
            pv.dualizer_raw.emplace_back(bt, resolve_term(s.t_param, stack));
            return put(a.quant(TNode::Exists, R, bt));
        }
        case Rule::Eqv: {
            const TNode n = a.nodes[R];
            auto comm = [&](TNode::K k) -> util::ResultStatus {
                if (n.k != k) return MAKE_ERROR << "read_fonet: ≡ comm shape";
                return put(a.bin(k, n.r, n.l));
            };
            auto assoc = [&](TNode::K k) -> util::ResultStatus {
                if (s.dir == EqDir::Forward) {
                    if (n.k != k || a.nodes[n.l].k != k) return MAKE_ERROR << "read_fonet: ≡ assoc→";
                    size_t A = a.nodes[n.l].l, B = a.nodes[n.l].r, C = n.r;
                    return put(a.bin(k, A, a.bin(k, B, C)));
                }
                if (n.k != k || a.nodes[n.r].k != k) return MAKE_ERROR << "read_fonet: ≡ assoc←";
                size_t A = n.l, B = a.nodes[n.r].l, C = a.nodes[n.r].r;
                return put(a.bin(k, a.bin(k, A, B), C));
            };
            auto swap = [&](TNode::K q) -> util::ResultStatus {
                if (n.k != q || a.nodes[n.child].k != q) return MAKE_ERROR << "read_fonet: ≡ swap";
                size_t inner = n.child, body = a.nodes[inner].child;
                size_t bx = n.binder_tag, by = a.nodes[inner].binder_tag;
                return put(a.quant(q, a.quant(q, body, bx), by));  // tags follow atoms
            };
            // ∀-over-∨ (q=Forall, op=Or) / ∃-over-∧ (q=Exists, op=And). Forward is
            // AC-tolerant: float every operand of the canonical chain that does
            // not reference the binder (tags are absolute, so no De Bruijn shift).
            auto dist = [&](TNode::K q, TNode::K op) -> util::ResultStatus {
                if (s.dir == EqDir::Forward) {
                    if (n.k != q || a.nodes[n.child].k != op) return MAKE_ERROR << "read_fonet: ≡ dist→";
                    size_t bt = n.binder_tag;
                    std::vector<size_t> ops; flatten_t(a, n.child, op, ops);
                    std::vector<size_t> hasX, floated;
                    for (size_t o : ops) (refers_binder(a, o, bt) ? hasX : floated).push_back(o);
                    if (floated.empty()) return MAKE_ERROR << "read_fonet: ≡ dist→ nothing to float";
                    if (hasX.empty()) return MAKE_ERROR << "read_fonet: ≡ dist→ vacuous binder";
                    std::vector<size_t> chain{a.quant(q, build_t(a, op, hasX), bt)};
                    for (size_t b : floated) chain.push_back(b);
                    return put(build_t(a, op, chain));
                }
                if (n.k != op || a.nodes[n.l].k != q) return MAKE_ERROR << "read_fonet: ≡ dist←";
                size_t A = a.nodes[n.l].child, B = n.r, bt = a.nodes[n.l].binder_tag;
                return put(a.quant(q, a.bin(op, A, B), bt));
            };
            switch (s.eq) {
                case EqRule::CommAnd:    return comm(TNode::And);
                case EqRule::CommOr:     return comm(TNode::Or);
                case EqRule::AssocAnd:   return assoc(TNode::And);
                case EqRule::AssocOr:    return assoc(TNode::Or);
                case EqRule::SwapForall: return swap(TNode::Forall);
                case EqRule::SwapExists: return swap(TNode::Exists);
                case EqRule::DistForall: return dist(TNode::Forall, TNode::Or);
                case EqRule::DistExists: return dist(TNode::Exists, TNode::And);
            }
            return MAKE_ERROR << "read_fonet: unknown ≡ equation";
        }
        default:
            return MAKE_ERROR << "read_fonet: unsupported rule in linear core";
    }
}

// Reconstruct A' from the mirror in fograph pre-order, recording occ→vertex
// and binder_tag→var_index (= binder pre-order rank), exactly mirroring
// comb::Fograph's traversal.
struct Recon {
    FormulaBuilder& fb;
    const Arena& a;
    std::vector<size_t> stack;                       // enclosing binder tags
    size_t next_vertex{0};
    var_index next_binder_var{0};
    std::unordered_map<size_t, size_t> occ_vertex;   // atom occ → vertex idx
    std::unordered_map<size_t, var_index> binder_var;// binder tag → var_index

    FormulaHandle go(size_t idx) {
        const TNode& n = a.nodes[idx];
        switch (n.k) {
            case TNode::One:
                ++next_vertex;
                return fb.make_not(fb.make_bottom());
            case TNode::Atom: {
                occ_vertex[n.occ] = next_vertex++;
                std::vector<Term> args;
                for (const TArg& t : n.args) {
                    if (t.bound) {
                        // Gen(depth) referencing binder t.binder_tag.
                        size_t pos = 0; bool found = false;
                        for (size_t i = stack.size(); i-- > 0;) {
                            if (stack[i] == t.binder_tag) { pos = stack.size() - 1 - i; found = true; break; }
                        }
                        (void)found;
                        args.push_back(Term::generalized(pos));
                    } else {
                        args.push_back(Term::fixed(t.fixed));
                    }
                }
                FormulaHandle atom = fb.predicate(n.pred, std::move(args));
                return n.neg ? fb.make_not(atom) : atom;
            }
            case TNode::And: { auto l = go(n.l); auto r = go(n.r); return fb.make_and(l, r); }
            case TNode::Or:  { auto l = go(n.l); auto r = go(n.r); return fb.make_or(l, r); }
            case TNode::Forall:
            case TNode::Exists: {
                binder_var[n.binder_tag] = next_binder_var++;
                ++next_vertex;
                stack.push_back(n.binder_tag);
                auto body = go(n.child);
                stack.pop_back();
                return fb.make_quantified(n.k == TNode::Forall ? Op::Forall : Op::Exists, body);
            }
        }
        return fb.make_not(fb.make_bottom());  // unreachable
    }
};

}  // namespace

Result<FonetReadoff> read_fonet(FormulaBuilder& fb, const Derivation& phi1) {
    // Precondition: linear core starts at ⊤.
    if (!phi1.top.valid() ||
        !(phi1.top.get().is_compound() && phi1.top.get().as_compound().op == Op::Not &&
          phi1.top.get().as_compound().left.valid() &&
          phi1.top.get().as_compound().left.get().is_compound() &&
          phi1.top.get().as_compound().left.get().as_compound().op == Op::Bottom))
        return MAKE_ERROR << "read_fonet: linear core must start at t (⊤)";

    Prov pv;
    pv.root = pv.arena.one();
    for (const Step& s : phi1.steps) {
        auto r = apply_tf(pv, s);
        if (r.is_error()) return std::move(r).error();
    }

    Recon rec{fb, pv.arena};
    FormulaHandle a_prime_rec = rec.go(pv.root);

    // Cross-check: the mirror reconstructs exactly the real linear-core output.
    auto real = logic::proof::ks1::replay(fb, phi1.top, phi1.steps);
    if (real.is_error()) return std::move(real).error();
    if (!(a_prime_rec == real.value()))
        return MAKE_ERROR << "read_fonet: provenance reconstruction != Φ1 conclusion";

    FonetReadoff out;
    out.a_prime = a_prime_rec;
    out.target  = comb::Fograph(a_prime_rec);

    out.fonet.num_vertex    = out.target.num_vertex();
    out.fonet.cograph_edges = out.target.cograph_edges;
    out.fonet.binding_edges = out.target.binding_edges;
    for (auto& [o1, o2] : pv.links)
        out.fonet.links.push_back({rec.occ_vertex.at(o1), rec.occ_vertex.at(o2)});
    // Fograph assigns binder vars 0..B-1. A bound witness (referencing a
    // universal binder) maps to that binder's var; a free witness (an eigenvar
    // / constant) is offset by B so it stays disjoint from every binder var —
    // otherwise it could collide with the existential var it instantiates,
    // which the verifier (rightly) rejects.
    const var_index B = rec.next_binder_var;
    for (auto& [bt, w] : pv.dualizer_raw) {
        Term img = w.bound ? Term::fixed(rec.binder_var.at(w.binder_tag))
                           : Term::fixed(w.fixed + B);
        out.fonet.dualizer[rec.binder_var.at(bt)] = img;
    }
    return out;
}

}  // namespace logic::proof::ks1_to_comb
