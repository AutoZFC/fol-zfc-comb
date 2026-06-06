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
