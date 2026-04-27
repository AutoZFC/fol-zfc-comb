#include "runner.h"

#include "lkr/verifier.h"
#include "nd/verifier.h"

#include "../util/error.h"

#include <string>
#include <variant>

namespace logic::proof {

namespace {

// Pull the claim_name out of a Proof regardless of which Program variant
// it carries. Both NDProgram and LKRProgram have a `claim_name` field.
std::string claim_name_of(const Proof& p) {
    return std::visit(
        [](const auto& prog) -> std::string { return prog.claim_name; },
        p.body);
}

}  // namespace

ProofRunner::ProofRunner(GlobalContext& ctx) : ctx_(ctx) {
    register_verifier(std::make_unique<nd::NDVerifier>());
    register_verifier(std::make_unique<lkr::LKRVerifier>());
}

void ProofRunner::register_verifier(std::unique_ptr<Verifier> v) {
    if (!v) return;
    System s = v->system();
    verifiers_[static_cast<size_t>(s)] = std::move(v);
}

util::ResultStatus ProofRunner::verify(const Proof& proof) {
    last_used_.clear();

    const std::string claim_name = claim_name_of(proof);

    // Schema axiomatic mark: if claim_name names a schema, that schema is
    // taken as proven (its body is an axiom). This fires unconditionally,
    // matching pre-IR runtime semantics.
    if (ctx_.find_schema(claim_name).has_value()) {
        ctx_.mark_schema_proven(claim_name);
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

    // Register on success. Schema proofs were already marked above;
    // claim/known proofs add the theorem now, against the dispatcher-
    // resolved SentenceHandle. This is the only theorem-registration
    // site in the proof flow.
    if (goal_sentence.valid()) {
        ctx_.add_theorem(claim_name, goal_sentence);
    }

    last_used_ = v->last_used_names();
    return util::Ok();
}

}  // namespace logic::proof
