// comb_checker — runs the ND → iota_elim → nd_internalize →
// NDtoLKR pipeline per theorem, then verifies the resulting LKR
// program, and reports per-theorem success/failure.
//
// The direct LKR→combinatorial-proof path has been retired (the future
// route is LKR→KS1→comb); this tool now ends at LKR verification.
//
// CLI:
//   comb_checker <header.fol.def> <proof.fol.proof>
//                [dep_header.fol.def ...] [-- dep_proof.fol.proof ...]
//
// Dependency .fol.proof files are processed through the same pipeline
// (in argv order) so their theorems' axioms/wrapped-forms register in
// the maps that the main file's theorems consult. Without this, any
// theorem that cites an upstream theorem cascades a compute_axioms
// failure even though the citation is well-formed at the ND level.
//
// Final summary covers ALL processed proof files (main + deps).
// Exit 0 if every theorem ends-at-ok or is marked `unproved`.

#include "src/library/library.h"
#include "src/parser/parser.h"
#include "src/proof/lkr/verifier.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/proof.h"
#include "src/proof/translate/iota_elim/eliminate_iota.h"
#include "src/proof/translate/nd_internalize/apply.h"
#include "src/proof/translate/nd_to_lkr/nd_to_lkr.h"
#include "src/proof/translate/theorem_facts.h"
#include "src/runtime/runtime.h"

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

using namespace logic;
using namespace logic::proof;
namespace tr  = logic::proof::translate;
namespace ni  = logic::proof::translate::nd_internalize;
namespace ie  = logic::proof::translate::iota_elim;
namespace ntl = logic::proof::translate::nd_to_lkr;

namespace {

struct StageResult {
    std::string file;         // proof file containing this theorem
    std::string claim;
    std::string stage;        // "ok", "unproved-marker", or first failing stage
    std::string detail;
};

std::string load_headers(Runtime& rt,
                          const std::vector<std::string>& dep_header_paths) {
    for (const auto& dep : dep_header_paths) {
        if (dep.size() >= 8 && dep.substr(dep.size() - 8) == ".fol.lib") {
            auto s = rt.load_library(dep);
            if (!s.ok()) return "load_library(" + dep + "): " + s.error().to_string();
            continue;
        }
        auto r = rt.load_file_recursive(dep);
        if (!r.ok()) return "load_file(" + dep + "): " + r.error().to_string();
        auto e = rt.execute_all_proofs(r.value());
        if (!e.ok()) return "execute_all_proofs(" + dep + "): " + e.error().to_string();
    }
    return "";
}

// Process every theorem in `proof_path` through the ND → nd_internalize →
// NDtoLKR pipeline, then verify the resulting LKR program. Populates
// `theorem_facts` in-place so subsequent files see this file's results.
void process_proof_file(
    Runtime&                  rt,
    const std::string&        proof_path,
    tr::TheoremFactsMap&      theorem_facts,
    std::vector<StageResult>& results)
{
    std::ifstream proof_file(proof_path);
    if (!proof_file.is_open()) {
        results.push_back({proof_path, "<file>", "open_failed", "cannot open"});
        return;
    }
    std::stringstream buffer; buffer << proof_file.rdbuf();
    std::string parse_err;
    ParseResult parsed = try_parse_with_proofs(
        buffer.str(), rt.context(), &parse_err);
    if (!parse_err.empty()) {
        results.push_back({proof_path, "<file>", "parse_failed", parse_err});
        return;
    }

    for (const auto& parsed_proof : parsed.proofs) {
        const std::string& name = parsed_proof.claim_name;
        if (parsed_proof.unproved) {
            results.push_back({proof_path, name, "unproved-marker", ""});
            continue;
        }

        std::string first_stage, first_detail;
        auto fail = [&](const std::string& s, const std::string& d) {
            if (first_stage.empty()) { first_stage = s; first_detail = d; }
        };

        try {

        auto lower_r = nd::lower(parsed_proof, rt.context());
        if (!lower_r.ok()) {
            results.push_back({proof_path, name, "nd_lower",
                              lower_r.error().to_string()});
            continue;
        }
        Program<nd::Instr> prog = std::move(lower_r).unwrap();

        if (auto e = rt.execute_proof(parsed_proof); !e.ok()) {
            results.push_back({proof_path, name, "nd_execute",
                              e.error().to_string()});
            continue;
        }

        auto claim_opt = rt.context().find_claim(name);
        if (!claim_opt.has_value()) {
            results.push_back({proof_path, name, "find_claim", ""});
            continue;
        }
        FormulaHandle goal = claim_opt.value().get().root();

        if (ie::EliminateIotaInProof::program_contains_iota(prog)) {
            ie::EliminateIotaInProof ipass(rt.context(), goal);
            auto r = ipass.apply(prog);
            if (!r.ok()) {
                results.push_back({proof_path, name, "iota_elim",
                                  r.error().to_string()});
                continue;
            }
            prog = std::move(r).unwrap();
        }

        // Stage 1 (nd_internalize::apply): runs schema_macro,
        // compute_transitive_facts, emit_prelude, emit_body_with_remap,
        // and the NDVerifier output gate in one orchestrated pass.
        auto ni_r = ni::apply(rt.context(), prog, goal, theorem_facts);
        if (!ni_r.ok()) {
            fail("nd_internalize", ni_r.error().to_string());
            results.push_back({proof_path, name, first_stage, first_detail});
            continue;
        }

        // Register this theorem's facts under its own SentenceHandle so
        // any subsequent citer's compute_transitive_facts can find them.
        auto sh_self = rt.context().find_known(name);
        if (sh_self.has_value()) {
            theorem_facts.put(sh_self.value(), ni_r.value().facts);
        }

        FormulaHandle wrapped_goal = ni_r.value().wrapped_goal.get().root();

        ntl::NDtoLKR ndl(rt.context(), wrapped_goal);
        auto lkr_r = ndl.apply(ni_r.value().proof);
        if (!lkr_r.ok()) {
            fail("nd_to_lkr", lkr_r.error().to_string());
            results.push_back({proof_path, name, first_stage, first_detail});
            continue;
        }

        // The direct LKR→comb path is retired. End at LKR verification:
        // verify the NDtoLKR output against the wrapped goal.
        Proof pf{System::LKR, lkr_r.value()};
        lkr::LKRVerifier v;
        auto verify_r = v.verify(rt.context(), wrapped_goal, pf);
        if (!verify_r.ok()) {
            fail("lkr_verify", verify_r.error().to_string());
            results.push_back({proof_path, name, first_stage, first_detail});
            continue;
        }
        results.push_back({proof_path, name, "ok", ""});

        } catch (const std::exception& ex) {
            results.push_back({proof_path, name, "exception", ex.what()});
        } catch (...) {
            results.push_back({proof_path, name, "exception", "unknown"});
        }
    }
}

}  // namespace

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: comb_checker <header.fol.def> <proof.fol.proof> "
                     "[dep_header.fol.def ...] [-- dep_proof.fol.proof ...]\n";
        return 2;
    }
    std::string header_path = argv[1];
    std::string proof_path  = argv[2];

    std::vector<std::string> dep_headers;
    std::vector<std::string> dep_proofs;
    bool after_sep = false;
    for (int i = 3; i < argc; ++i) {
        if (std::string(argv[i]) == "--") { after_sep = true; continue; }
        (after_sep ? dep_proofs : dep_headers).push_back(argv[i]);
    }

    Runtime rt;
    if (auto err = load_headers(rt, dep_headers); !err.empty()) {
        std::cerr << "ERROR: " << err << "\n";
        return 1;
    }

    auto header_r = rt.load_file_recursive(header_path);
    if (!header_r.ok()) {
        std::cerr << "ERROR: load header " << header_path << ": "
                  << header_r.error().to_string() << "\n";
        return 1;
    }
    if (auto e = rt.execute_all_proofs(header_r.value()); !e.ok()) {
        std::cerr << "ERROR: execute header includes: "
                  << e.error().to_string() << "\n";
        return 1;
    }

    tr::TheoremFactsMap   theorem_facts;
    std::vector<StageResult> results;

    // Process dep proofs first (in argv order — caller is responsible
    // for topological ordering), then the main proof file. All theorems
    // share the same map so dep theorems' facts are available to the
    // main file.
    for (const auto& dep : dep_proofs) {
        process_proof_file(rt, dep, theorem_facts, results);
    }
    process_proof_file(rt, proof_path, theorem_facts, results);

    // Report.
    int ok = 0, unproved_marker = 0;
    std::unordered_map<std::string, int> by_stage;
    for (const auto& r : results) {
        if (r.stage == "ok") ++ok;
        else if (r.stage == "unproved-marker") ++unproved_marker;
        else ++by_stage[r.stage];
    }

    std::cout << "Total theorems processed: " << results.size() << "\n";
    std::cout << "  OK: " << ok << "\n";
    if (unproved_marker > 0)
        std::cout << "  unproved-marker: " << unproved_marker << "\n";
    for (const auto& [stage, count] : by_stage) {
        std::cout << "  FAIL @ " << stage << ": " << count << "\n";
    }
    std::cout << "\n";

    int max_errors = 50;
    if (const char* m = std::getenv("COMB_CHECKER_MAX_ERRORS")) {
        max_errors = std::atoi(m);
    }
    int printed = 0;
    for (const auto& r : results) {
        if (r.stage == "ok") {
            std::cout << "  + " << r.claim << "\n";
        } else if (r.stage == "unproved-marker") {
            std::cout << "  ? " << r.claim << "\n";
        } else {
            std::cout << "  x " << r.claim << " @ " << r.stage;
            if (printed < max_errors) {
                std::cout << ": " << r.detail;
                ++printed;
            }
            std::cout << "\n";
        }
    }

    int failed = 0;
    for (const auto& r : results) {
        if (r.stage != "ok" && r.stage != "unproved-marker") ++failed;
    }
    return failed == 0 ? 0 : 1;
}
