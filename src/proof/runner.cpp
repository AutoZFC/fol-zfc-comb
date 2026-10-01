#include "runner.h"

#include "comb/verifier.h"
#include "lkr/verifier.h"
#include "nd/verifier.h"

#include "src/util/error.h"

#include <string>
#include <variant>

namespace logic::proof {

namespace {

// Pull the claim_name out of a Proof regardless of which body variant
// it carries. NDProgram, LKRProgram, and comb::CombProof all expose
// .claim_name as a std::string.
std::string claim_name_of(const Proof& p) {
    return std::visit(
        [](const auto& body) -> std::string { return body.claim_name; },
        p.body);
}

}  // namespace

ProofRunner::ProofRunner(GlobalContext& ctx) : ctx_(ctx) {
    register_verifier(std::make_unique<nd::NDVerifier>());
    register_verifier(std::make_unique<lkr::LKRVerifier>());
    register_verifier(std::make_unique<comb::CombVerifier>());
}

void ProofRunner::register_verifier(std::unique_ptr<Verifier> v) {
    if (!v) return;
    System s = v->system();
    verifiers_[static_cast<size_t>(s)] = std::move(v);
}

util::ResultStatus ProofRunner::verify(const Proof& proof) {
    last_used_.clear();

    const std::string claim_name = claim_name_of(proof);

    // A schema is marked proven only after its proof checks (below). Marking it
    // first let a failed proof, or one citing the schema itself, leave it proven.
    const bool names_schema = ctx_.find_schema(claim_name).has_value();
    if (names_schema && (ctx_.find_claim(claim_name) || ctx_.find_known(claim_name))) {
        return MAKE_ERROR << "verify: '" << claim_name
                          << "' names both a schema and a claim or axiom";
    }

    // Resolve the goal formula. Three cases, in priority order:
    //   1. find_claim — a declared, not-yet-proven claim.
    //   2. find_known — already-proven theorem (re-prove is idempotent).
    //   3. find_schema — proving a schema's body.
    SentenceHandle goal_sentence{};
    FormulaHandle  goal_formula{};
    if (auto claim = ctx_.find_claim(claim_name)) {
        goal_sentence = claim.value();
        goal_formula  = goal_sentence.get().root();
    } else if (auto known = ctx_.find_known(claim_name)) {
        goal_sentence = known.value();
        goal_formula  = goal_sentence.get().root();
    } else if (auto schema = ctx_.find_schema(claim_name)) {
        goal_formula = schema->body;
    } else {
        return MAKE_ERROR << "verify: unknown claim or schema '"
                          << claim_name << "'";
    }

    // Dispatch.
    const size_t sys_idx = static_cast<size_t>(proof.system);
    if (sys_idx >= verifiers_.size() || !verifiers_[sys_idx]) {
        return MAKE_ERROR << "verify: no verifier registered for system "
                          << sys_idx;
    }
    Verifier* v = verifiers_[sys_idx].get();
    if (v->system() != proof.system) {
        return MAKE_ERROR << "verify: verifier slot mismatch (slot says "
                          << static_cast<int>(v->system())
                          << ", proof tags " << static_cast<int>(proof.system)
                          << ")";
    }

    auto status = v->verify(ctx_, goal_formula, proof);
    if (!status.ok()) {
        return MAKE_ERROR << "verifying '" << claim_name << "': "
                          << status.error().to_string();
    }

    // Register on success, against the dispatcher-resolved goal. This is the
    // only theorem- and schema-registration site in the proof flow.
    if (goal_sentence.valid()) {
        ctx_.add_theorem(claim_name, goal_sentence);
    } else if (names_schema) {
        ctx_.mark_schema_proven(claim_name);
    }

    last_used_ = v->last_used_names();
    return util::Ok();
}

}  // namespace logic::proof
