#include "src/proof/translate/lkr_to_ks1/reconcile.h"

#include "src/proof/ks1/checker.h"

#include <algorithm>
#include <string>
#include <vector>

namespace logic::proof::translate::lkr_to_ks1 {

namespace ks1 = logic::proof::ks1;

namespace {

using ks1::Dir;
using ks1::EqDir;
using ks1::EqRule;
using ks1::Path;
using ks1::Step;

bool is_chain(FormulaHandle h, Op op) {
    const Formula& f = h.get();
    return f.is_compound() && f.as_compound().op == op;
}

// Canonicalizer that EMITS the Eqv steps as it rewrites `cur` into
// ks1::canonicalize(cur). Tracks `cur` by replaying each emitted step (so every
// context is computed against the live formula).
struct Canon {
    FormulaBuilder&   fb;
    FormulaHandle     cur;
    std::vector<Step> out;
    bool              ok = true;

    FormulaHandle at(const Path& p) {
        FormulaHandle h = cur;
        for (Dir d : p) {
            const Formula& f = h.get();
            if (f.is_compound())
                h = (d == Dir::Left) ? f.as_compound().left : f.as_compound().right;
            else if (f.is_quantified())
                h = f.as_quantified().body;
        }
        return h;
    }

    void emit(EqRule eq, EqDir dir, Path ctx) {
        if (!ok) return;
        Step s; s.rule = ks1::Rule::Eqv; s.eq = eq; s.dir = dir; s.context = std::move(ctx);
        auto r = ks1::replay(fb, cur, {s});
        if (r.is_error()) { ok = false; return; }
        cur = r.value();
        out.push_back(std::move(s));
    }

    EqRule comm(Op op) { return op == Op::And ? EqRule::CommAnd : EqRule::CommOr; }
    EqRule assoc(Op op) { return op == Op::And ? EqRule::AssocAnd : EqRule::AssocOr; }

    Path child(Path p, Dir d) { p.push_back(d); return p; }

    // Right-associate the `op`-chain at `path` into o1 op (o2 op (… on)) and
    // recursively canonicalize each operand.
    void right_comb(const Path& path, Op op) {
        while (ok && is_chain(at(path), op) && is_chain(at(path).get().as_compound().left, op))
            emit(assoc(op), EqDir::Forward, path);     // (A op B) op C → A op (B op C)
        canon(child(path, Dir::Left));                 // canonicalize first operand
        if (is_chain(at(path), op) && is_chain(at(path).get().as_compound().right, op))
            right_comb(child(path, Dir::Right), op);
        else
            canon(child(path, Dir::Right));            // last operand (or only operand)
    }

    // Selection-sort the right-comb `op`-chain at `path` by to_string ascending
    // (matching ks1::canonicalize's operand order).
    void sort_chain(const Path& path, Op op) {
        std::vector<std::string> keys;
        for (Path p = path; is_chain(at(p), op); p = child(p, Dir::Right))
            keys.push_back(at(p).get().as_compound().left.get().to_string());
        keys.push_back(at(path_after(path, op)).get().to_string());  // last operand
        std::size_t n = keys.size();
        for (std::size_t i = 0; i + 1 < n && ok; ++i) {
            std::size_t m = i;
            for (std::size_t j = i + 1; j < n; ++j)
                if (keys[j] < keys[m]) m = j;
            for (std::size_t j = m; j > i; --j) {        // bubble keys[m] down to i
                swap_adjacent(path, op, j - 1, n);
                std::swap(keys[j - 1], keys[j]);
            }
        }
    }

    // The path to the LAST operand of the right-comb chain rooted at `path`.
    Path path_after(Path path, Op op) {
        while (is_chain(at(path), op)) path = child(path, Dir::Right);
        return path;
    }

    // Swap operands at chain positions j, j+1 (0-indexed) of the right-comb at
    // `path`. n = chain length. Subchain root is path + [Right]^j.
    void swap_adjacent(const Path& path, Op op, std::size_t j, std::size_t n) {
        Path p = path;
        for (std::size_t k = 0; k < j; ++k) p = child(p, Dir::Right);
        if (j + 1 == n - 1) {                            // last pair: oj op o_{j+1}
            emit(comm(op), EqDir::Forward, p);
        } else {                                         // oj op (o_{j+1} op REST)
            emit(assoc(op), EqDir::Backward, p);         // → (oj op o_{j+1}) op REST
            emit(comm(op), EqDir::Forward, child(p, Dir::Left));
            emit(assoc(op), EqDir::Forward, p);          // → o_{j+1} op (oj op REST)
        }
    }

    void canon(const Path& path) {
        if (!ok) return;
        const Formula& f = at(path).get();
        if (f.is_compound() && (f.as_compound().op == Op::And || f.as_compound().op == Op::Or)) {
            Op op = f.as_compound().op;
            right_comb(path, op);
            sort_chain(path, op);
        } else if (f.is_quantified()) {
            canon(child(path, Dir::Down));
        }
        // PredicateInstance / Not-literal / Bottom: already canonical.
    }
};

std::vector<Step> invert(const std::vector<Step>& steps) {
    std::vector<Step> out;
    out.reserve(steps.size());
    for (auto it = steps.rbegin(); it != steps.rend(); ++it) {
        Step s = *it;
        s.dir = (s.dir == EqDir::Forward) ? EqDir::Backward : EqDir::Forward;
        out.push_back(std::move(s));
    }
    return out;
}

util::Result<std::vector<Step>> canon_path(FormulaBuilder& fb, FormulaHandle f) {
    Canon c{fb, f, {}, true};
    c.canon({});
    if (!c.ok)
        return MAKE_ERROR << "equiv_steps: failed to emit canonicalization path";
    return c.out;
}

}  // namespace

namespace {

using ks1::Dir;
using ks1::Path;
using ks1::Step;

bool is_atom_lit(FormulaHandle h) {
    const Formula& f = h.get();
    if (f.is_predicate()) return true;
    if (f.is_compound() && f.as_compound().op == Op::Not)
        return f.as_compound().left.get().is_predicate();   // ¬atom
    return false;
}

ks1::Step rule_at(ks1::Rule r, Path ctx) {
    Step s; s.rule = r; s.context = std::move(ctx); return s;
}

ks1::Step eqv_at(EqRule eq, EqDir dir, Path ctx) {
    Step s; s.rule = ks1::Rule::Eqv; s.eq = eq; s.dir = dir;
    s.context = std::move(ctx); return s;
}

// The fixed regroup (B∨C)∨(B∨C) ⟶ (B∨B)∨(C∨C), with B and C OPAQUE — contexts
// never descend into them (so it is O(1) regardless of |B|,|C|, vs. equiv_steps
// which canonicalizes all leaves). Relative to the regroup root; the caller
// prefixes the surrounding S{·} context. Derivation:
//   (B∨C)∨(B∨C) →Assoc→ B∨(C∨(B∨C)) →Assoc⁻¹@R→ B∨((C∨B)∨C)
//   →Comm@R.L→ B∨((B∨C)∨C) →Assoc@R→ B∨(B∨(C∨C)) →Assoc⁻¹→ (B∨B)∨(C∨C)
std::vector<Step> xx_or_regroup() {
    return {
        eqv_at(EqRule::AssocOr, EqDir::Forward,  {}),
        eqv_at(EqRule::AssocOr, EqDir::Backward, {Dir::Right}),
        eqv_at(EqRule::CommOr,  EqDir::Forward,  {Dir::Right, Dir::Left}),
        eqv_at(EqRule::AssocOr, EqDir::Forward,  {Dir::Right}),
        eqv_at(EqRule::AssocOr, EqDir::Backward, {}),
    };
}

// Emit S{X∨X}/S{X} at context `ctx`. Recurse through X's structure with the
// medial that exposes a ∨ one level down, bottoming out at Ac on literal pairs.
util::Result<std::vector<Step>> contract_at(FormulaBuilder& fb, FormulaHandle x,
                                            Path ctx) {
    std::vector<Step> out;
    auto child = [&](Path c, Dir d) { c.push_back(d); return c; };

    if (is_atom_lit(x)) {                       // a∨a → a
        out.push_back(rule_at(ks1::Rule::Ac, ctx));
        return out;
    }
    const Formula& f = x.get();
    if (f.is_compound() && f.as_compound().op == Op::Or) {
        FormulaHandle B = f.as_compound().left, C = f.as_compound().right;
        // (B∨C)∨(B∨C) ⟶ (B∨B)∨(C∨C) by a local regroup (B,C opaque), then
        // contract each side. O(1) here vs. equiv_steps's leaf-canonicalization.
        for (Step& s : xx_or_regroup()) {
            s.context.insert(s.context.begin(), ctx.begin(), ctx.end());
            out.push_back(std::move(s));
        }
        TRY_ASSIGN(lb, contract_at(fb, B, child(ctx, Dir::Left)));
        TRY_ASSIGN(rb, contract_at(fb, C, child(ctx, Dir::Right)));
        out.insert(out.end(), lb.begin(), lb.end());
        out.insert(out.end(), rb.begin(), rb.end());
        return out;
    }
    if (f.is_compound() && f.as_compound().op == Op::And) {
        FormulaHandle B = f.as_compound().left, C = f.as_compound().right;
        out.push_back(rule_at(ks1::Rule::M, ctx));     // (B∧C)∨(B∧C)→(B∨B)∧(C∨C)
        TRY_ASSIGN(lb, contract_at(fb, B, child(ctx, Dir::Left)));
        TRY_ASSIGN(rb, contract_at(fb, C, child(ctx, Dir::Right)));
        out.insert(out.end(), lb.begin(), lb.end());
        out.insert(out.end(), rb.begin(), rb.end());
        return out;
    }
    if (f.is_quantified()) {
        Op op = f.as_quantified().op;
        out.push_back(rule_at(op == Op::Forall ? ks1::Rule::MForall
                                               : ks1::Rule::MExists, ctx));
        TRY_ASSIGN(bb, contract_at(fb, f.as_quantified().body, child(ctx, Dir::Down)));
        out.insert(out.end(), bb.begin(), bb.end());
        return out;
    }
    return MAKE_ERROR << "contract_steps: unsupported formula shape (⊥/unit?)";
}

// Re-bracket `cur` into the LEFT-associated denote(entries) via AssocOr
// right-rotations, treating handles in `entries` as opaque leaves. Replay-tracked
// so contexts are computed against the live formula.
struct LeftAssoc {
    FormulaBuilder&                   fb;
    const std::vector<FormulaHandle>& entries;
    FormulaHandle                     cur;
    std::vector<Step>                 out;
    bool                              ok = true;

    bool is_entry(FormulaHandle h) const {
        for (FormulaHandle e : entries) if (e == h) return true;
        return false;
    }
    FormulaHandle at(const Path& p) const {
        FormulaHandle h = cur;
        for (Dir d : p) {
            const Formula& f = h.get();
            if (f.is_compound())
                h = (d == Dir::Left) ? f.as_compound().left : f.as_compound().right;
            else if (f.is_quantified())
                h = f.as_quantified().body;
        }
        return h;
    }
    // A ∨ that is part of the sequent spine (i.e. NOT an opaque entry).
    bool spine_or(FormulaHandle h) const {
        const Formula& f = h.get();
        return f.is_compound() && f.as_compound().op == Op::Or && !is_entry(h);
    }
    void rotate(const Path& ctx) {                 // A∨(B∨C) → (A∨B)∨C
        if (!ok) return;
        Step s; s.rule = ks1::Rule::Eqv; s.eq = EqRule::AssocOr;
        s.dir = EqDir::Backward; s.context = ctx;
        auto r = ks1::replay(fb, cur, {s});
        if (r.is_error()) { ok = false; return; }
        cur = r.value();
        out.push_back(std::move(s));
    }
    void run(Path ctx) {
        while (ok) {
            FormulaHandle node = at(ctx);
            if (!spine_or(node)) return;           // opaque entry or non-∨: a leaf
            if (spine_or(node.get().as_compound().right))
                rotate(ctx);                        // pull one element onto the spine
            else
                ctx.push_back(Dir::Left);           // right is a leaf → descend left
        }
    }
};

}  // namespace

util::Result<std::vector<Step>> reassoc_left_steps(
    FormulaBuilder& fb, FormulaHandle cur, const std::vector<FormulaHandle>& entries) {
    if (entries.empty())
        return MAKE_ERROR << "reassoc_left_steps: empty entries";
    LeftAssoc la{fb, entries, cur, {}, true};
    la.run({});
    if (!la.ok)
        return MAKE_ERROR << "reassoc_left_steps: rotation failed";
    FormulaHandle target = entries[0];             // self-check: replay reaches it
    for (std::size_t i = 1; i < entries.size(); ++i) target = fb.make_or(target, entries[i]);
    auto got = ks1::replay(fb, cur, la.out);
    if (got.is_error()) return std::move(got).error();
    if (got.value() != target)
        return MAKE_ERROR << "reassoc_left_steps: did not reach denote(entries)";
    return la.out;
}

util::Result<std::vector<Step>> contract_steps(FormulaBuilder& fb, FormulaHandle x) {
    return contract_at(fb, x, {});
}

namespace {
FormulaHandle denote(FormulaBuilder& fb, const std::vector<FormulaHandle>& g) {
    FormulaHandle acc = g[0];
    for (std::size_t i = 1; i < g.size(); ++i) acc = fb.make_or(acc, g[i]);
    return acc;
}
// Left-to-right spine leaves of `cur`, descending ∨-nodes but STOPPING at any
// handle that is an entry (opaque) — so a ∨-valued entry stays a single leaf.
void spine_order(FormulaHandle cur, const std::vector<FormulaHandle>& entries,
                 std::vector<FormulaHandle>& out) {
    for (FormulaHandle e : entries) if (e == cur) { out.push_back(cur); return; }
    const Formula& f = cur.get();
    if (f.is_compound() && f.as_compound().op == Op::Or) {
        spine_order(f.as_compound().left, entries, out);
        spine_order(f.as_compound().right, entries, out);
    } else {
        out.push_back(cur);
    }
}
}  // namespace

util::Result<std::vector<Step>> reconcile_to(FormulaBuilder& fb, FormulaHandle cur,
                                             const std::vector<FormulaHandle>& entries) {
    if (entries.empty()) return MAKE_ERROR << "reconcile_to: empty entries";
    if (cur == denote(fb, entries)) return std::vector<Step>{};

    // Re-bracket cur to left-assoc in its own spine order, then permute that
    // order into `entries`. Both treat entries as OPAQUE (a ∨-valued entry's
    // boundary survives) and address by HANDLE/position — never by `to_string`.
    // The emitted steps are therefore STRUCTURAL, hence stable under a later
    // eigenvar rebind (an ancestor RForall renames fixed→gen). `equiv_steps`'
    // canon sorts operands by to_string, so its steps would break under that
    // rebind; we deliberately do NOT fall back to it. If the spine order is not a
    // permutation of `entries`, cur ≢ denote(entries) by a NON-propositional
    // difference (a quantifier shift needing DistForall) — the caller's bug to
    // fix, surfaced here rather than papered over.
    std::vector<FormulaHandle> order;
    spine_order(cur, entries, order);
    TRY_ASSIGN(ra, reassoc_left_steps(fb, cur, order));
    TRY_ASSIGN(ro, reorder_steps(fb, order, entries));
    ra.insert(ra.end(), ro.begin(), ro.end());
    return ra;
}

util::Result<std::vector<Step>> reorder_steps(FormulaBuilder& fb,
                                              const std::vector<FormulaHandle>& from,
                                              const std::vector<FormulaHandle>& to) {
    const std::size_t n = from.size();
    if (n != to.size())
        return MAKE_ERROR << "reorder_steps: size mismatch (" << n << " vs "
                          << to.size() << ")";
    if (n <= 1) return std::vector<Step>{};

    // rank[k] = target position (index in `to`) of from[k]; stable on duplicates.
    std::vector<std::size_t> rank(n);
    std::vector<char> used(n, 0);
    for (std::size_t i = 0; i < n; ++i) {
        std::size_t t = 0;
        for (; t < n; ++t) if (!used[t] && to[t] == from[i]) break;
        if (t == n) return MAKE_ERROR << "reorder_steps: `to` is not a "
                                         "permutation of `from` (by handle)";
        rank[i] = t; used[t] = 1;
    }

    // Bubble-sort `rank` ascending; each adjacent swap of positions (p, p+1) in
    // the length-n left-comb emits its local Assoc/Comm steps. The structure
    // stays a length-n left-comb throughout, so contexts depend only on p and n.
    std::vector<Step> out;
    auto mk = [](EqRule eq, EqDir dir, Path ctx) {
        Step s; s.rule = ks1::Rule::Eqv; s.eq = eq; s.dir = dir;
        s.context = std::move(ctx); return s;
    };
    auto swap_at = [&](std::size_t p) {                 // swap entries p, p+1
        Path ctx(n - 2 - p, Dir::Left);                 // node holding {…,p,p+1}
        if (p == 0) {
            out.push_back(mk(EqRule::CommOr, EqDir::Forward, ctx));
        } else {
            Path inner = ctx; inner.push_back(Dir::Right);
            out.push_back(mk(EqRule::AssocOr, EqDir::Forward, ctx));   // (P'∨cp)∨cq → P'∨(cp∨cq)
            out.push_back(mk(EqRule::CommOr, EqDir::Forward, inner));  // cp∨cq → cq∨cp
            out.push_back(mk(EqRule::AssocOr, EqDir::Backward, ctx));  // P'∨(cq∨cp) → (P'∨cq)∨cp
        }
    };
    for (std::size_t i = 0; i + 1 < n; ++i)
        for (std::size_t p = 0; p + 1 < n - i; ++p)
            if (rank[p] > rank[p + 1]) { swap_at(p); std::swap(rank[p], rank[p + 1]); }

    // Self-check: the steps must carry denote(from) to denote(to).
    auto denote = [&](const std::vector<FormulaHandle>& g) {
        FormulaHandle acc = g[0];
        for (std::size_t i = 1; i < g.size(); ++i) acc = fb.make_or(acc, g[i]);
        return acc;
    };
    auto got = ks1::replay(fb, denote(from), out);
    if (got.is_error()) return std::move(got).error();
    if (got.value() != denote(to))
        return MAKE_ERROR << "reorder_steps: replay did not reach denote(to)";
    return out;
}

util::Result<std::vector<Step>> equiv_steps(FormulaBuilder& fb,
                                            FormulaHandle from, FormulaHandle to) {
    if (from == to) return std::vector<Step>{};
    TRY_ASSIGN(s_from, canon_path(fb, from));
    TRY_ASSIGN(s_to, canon_path(fb, to));
    std::vector<Step> steps = std::move(s_from);
    std::vector<Step> back = invert(s_to);
    steps.insert(steps.end(), back.begin(), back.end());

    // Self-check: the produced path must actually carry `from` to `to` (guards
    // against from ≢ to, or a canonicalizer bug, before it reaches ks1::check).
    auto got = ks1::replay(fb, from, steps);
    if (got.is_error()) return std::move(got).error();
    if (got.value() != to)
        return MAKE_ERROR << "equiv_steps: from ≢ to (propositional ≡); cannot reconcile";
    return steps;
}

}  // namespace logic::proof::translate::lkr_to_ks1
