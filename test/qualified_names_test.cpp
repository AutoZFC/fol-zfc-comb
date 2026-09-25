// Qualified names: a claim or predicate name may carry dots, a trailing fact index
// and primes (Isabelle's own names, unchanged); a variable may not.

#include "src/runtime/runtime.h"

#include <iostream>
#include <string>

using namespace logic;

static int failures = 0;

static void check(bool ok, const std::string& what) {
    std::cout << (ok ? "PASSED: " : "FAILED: ") << what << "\n";
    if (!ok) ++failures;
}

int main() {
    const std::string text = R"(
axiom Th.ax: forall x. (Th.P(x) -> Th.Q(x))
claim Th.c: forall x. (Th.P(x) -> Th.Q(x))
claim Univ.rank_rls.4: forall x. (Th.P(x) -> Th.Q(x))
claim IFOL.allE': forall x. (Th.P(x) -> Th.Q(x))
claim tight: forall x.(Th.P(x) -> Th.P(x))
claim unspaced_qualified: forall x.Th.P(x)
claim spaced_qualified: forall x. Th.P(x)
claim unspaced_plain: forall x.P(x)
claim spaced_plain: forall x. P(x)

proof Th.c:
    _a = use Th.ax
    qed _a

proof Univ.rank_rls.4:
    _a = use Th.c
    qed _a

proof IFOL.allE':
    _a = use Univ.rank_rls.4
    qed _a

proof tight:
    fix x
    _h = assume Th.P(x)
    _i = implies_intro _h
    _g = forall_intro _i
    qed _g

proof unspaced_qualified: UNPROVED
proof spaced_qualified: UNPROVED
proof unspaced_plain: UNPROVED
proof spaced_plain: UNPROVED
)";
    Runtime rt;
    auto parsed = rt.load_with_proofs(text);
    check(parsed.ok(), "qualified claim, axiom, predicate and use names parse");
    if (!parsed.ok()) {
        std::cout << parsed.error() << "\n";
        return 1;
    }
    auto run = rt.execute_all_proofs(parsed.value());
    check(run.ok(), "the proofs execute");
    for (const char* name : {"Th.c", "Univ.rank_rls.4", "IFOL.allE'", "tight"}) {
        check(rt.context().find_theorem(name).has_value(), std::string("proved: ") + name);
    }
    auto same = [&](const char* a, const char* b) {
        auto x = rt.context().find_claim(a), y = rt.context().find_claim(b);
        return x.has_value() && y.has_value() && *x == *y;
    };
    check(same("unspaced_qualified", "spaced_qualified"),
          "forall x.Th.P(x) is forall x. Th.P(x): the binder's dot ends the variable");
    check(same("unspaced_plain", "spaced_plain"),
          "forall x.P(x) still means forall x. P(x)");
    return failures == 0 ? 0 : 1;
}
