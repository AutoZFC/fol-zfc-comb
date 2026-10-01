// Schema names may be qualified, and a schema is citable only once its own proof has checked;
// an UNPROVED schema is citable but its citers depend on it, as on an UNPROVED claim.

#include "src/runtime/runtime.h"

#include <iostream>
#include <string>

using namespace logic;

static int failures = 0;

static void check(bool ok, const std::string& what) {
    std::cout << (ok ? "PASSED: " : "FAILED: ") << what << "\n";
    if (!ok) ++failures;
}

static bool runs(Runtime& rt, const std::string& text) {
    auto parsed = rt.load_with_proofs(text);
    if (!parsed.ok()) {
        std::cout << "  parse: " << parsed.error() << "\n";
        return false;
    }
    auto run = rt.execute_all_proofs(parsed.value());
    if (!run.ok()) std::cout << "  run: " << run.error() << "\n";
    return run.ok();
}

int main() {
    {
        Runtime rt;
        check(runs(rt, R"(
schema IFOL.conj_cong [A(0), B(0)]: (A -> (B -> A))
proof IFOL.conj_cong:
    h1 = assume A
    h2 = assume B
    h3 = implies_intro h1
    h4 = implies_intro h3
    qed h4
claim Th.cite: forall x. (P(x) -> (Q(x) -> P(x)))
proof Th.cite:
    fix x
    h = schema_inst IFOL.conj_cong { A: P(x), B: Q(x) }
    g = forall_intro h
    qed g
)"), "a qualified schema name is declared, proved and cited");
        check(rt.context().is_schema_proven("IFOL.conj_cong"), "the qualified schema is proven");
        check(rt.context().find_theorem("Th.cite").has_value(), "its citer is proved");
    }
    {
        Runtime rt;
        check(!runs(rt, R"(
schema bad [A(0), B(0)]: (A -> B)
proof bad:
    h1 = assume A
    h2 = implies_intro h1
    qed h2
)"), "a schema proof that does not derive its body fails");
        check(!rt.context().is_schema_proven("bad"), "a failed schema proof leaves the schema unproven");
    }
    {
        Runtime rt;
        check(!runs(rt, R"(
schema loop [A(0), B(0)]: (A -> B)
proof loop:
    h = schema_inst loop { A: A, B: B }
    qed h
)"), "a schema proof cannot cite the schema it proves");
        check(!rt.context().is_schema_proven("loop"), "a self-citing schema stays unproven");
    }
    {
        Runtime rt;
        check(runs(rt, R"(
schema assumed [A(0), B(0)]: (A -> B)
proof assumed: UNPROVED
claim c: forall x. (P(x) -> Q(x))
proof c:
    fix x
    h = schema_inst assumed { A: P(x), B: Q(x) }
    g = forall_intro h
    qed g
)"), "an UNPROVED schema is citable");
        check(rt.context().is_schema_unproved("assumed"), "an UNPROVED schema is recorded as unproved");
        auto deps = rt.proof_deps().find("c");
        check(deps != rt.proof_deps().end() && deps->second.count("assumed") == 1,
              "a citer of an UNPROVED schema records it as a dependency");
    }
    {
        Runtime rt;
        check(!runs(rt, R"(
schema both [A(0)]: (A -> A)
claim both: forall x. (P(x) -> P(x))
proof both:
    h1 = assume A
    h2 = implies_intro h1
    qed h2
)"), "a proof whose name is both a claim and a schema is refused");
    }
    return failures == 0 ? 0 : 1;
}
