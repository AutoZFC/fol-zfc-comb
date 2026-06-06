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
#include "src/proof/translate/lkr_cut_elim/b0.h"
#include "src/proof/translate/lkr_cut_elim/deriv.h"
#include "src/proof/translate/lkr_cut_elim/reduce.h"
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
namespace lce = logic::proof::translate::lkr_cut_elim;

namespace {

// Cut-free, lemma-free proofs of processed theorems, keyed by statement
// SentenceHandle. Built in processing (topological) order; fed to
// eliminate_cuts so a downstream theorem's proven-theorem citations inline.
using CutFreeCache =
    std::unordered_map<SentenceHandle, lce::DerivPtr, SentenceHandleHash>;

struct StageResult {
    std::string file;         // proof file containing this theorem
    std::string claim;
    std::string stage;        // "ok", "unproved-marker", or first failing stage
    std::string detail;
    std::string cut_elim;     // cut-elim outcome for ok theorems (see run_cut_elim)
};

// Build → eliminate_cuts → emit → re-verify the LKR proof, inlining cited
// proven theorems from `cache`, and cache the cut-free result for downstream
// citers. eliminate_cuts is sound (returns the tree as-is on an unhandled
// case), so a re-verify FAILURE is an engine bug; residual Cut/Lemma ops are
// just incomplete elimination (axiom-dependent cuts are irreducible, §7a).
// Returns a short outcome tag for reporting.
std::string run_cut_elim(GlobalContext& ctx, FormulaHandle wrapped_goal,
                         const Program<lkr::Instr>& lkr_prog,
                         std::optional<SentenceHandle> sh_self,
                         CutFreeCache& cache) {
    FormulaBuilder fb(ctx);
    FormulaHandle goal_nnf = fb.to_nnf(wrapped_goal);
    auto deriv_r = lce::build(fb, goal_nnf, lkr_prog);
    if (!deriv_r.ok()) return "build_err: " + deriv_r.error().to_string();

    // Diagnostic: does build∘emit alone round-trip (no cut-elim)? Isolates
    // build/emit bugs from reduction bugs.
    if (std::getenv("COMB_CHECKER_ROUNDTRIP_ONLY")) {
        auto rt_r = lce::emit(*deriv_r.value());
        if (!rt_r.ok()) return "rt_emit_err: " + rt_r.error().to_string();
        Proof pf0{System::LKR, rt_r.value()};
        lkr::LKRVerifier v0;
        auto rv0 = v0.verify(ctx, wrapped_goal, pf0);
        return rv0.ok() ? "roundtrip_ok" : ("roundtrip_fail: " + rv0.error().to_string());
    }
    // Diagnostic: does B0 (additive→multiplicative) alone round-trip? Isolates
    // the B0 pass from the §5 reductions.
    if (std::getenv("COMB_CHECKER_B0_ONLY")) {
        auto b0_r = lce::additive_to_multiplicative(*deriv_r.value());
        if (!b0_r.ok()) return "b0_err: " + b0_r.error().to_string();
        auto e_r = lce::emit(*b0_r.value());
        if (!e_r.ok()) return "b0_emit_err: " + e_r.error().to_string();
        Proof pf0{System::LKR, e_r.value()};
        lkr::LKRVerifier v0;
        auto rv0 = v0.verify(ctx, wrapped_goal, pf0);
        return rv0.ok() ? "b0_ok" : ("b0_fail: " + rv0.error().to_string());
    }

    lce::LemmaProofs lemmas;
    for (auto& [k, v] : cache) lemmas[k] = v.get();
    auto elim_r = lce::eliminate_cuts(fb, *deriv_r.value(), lemmas);
    if (!elim_r.ok()) return "elim_err: " + elim_r.error().to_string();
    lce::DerivPtr cutfree = std::move(elim_r).unwrap();

    auto prog_r = lce::emit(*cutfree);
    if (!prog_r.ok()) return "emit_err: " + prog_r.error().to_string();

    std::size_t residual = 0;
    for (const auto& instr : prog_r.value().instrs)
        if (std::holds_alternative<lkr::Cut>(instr) ||
            std::holds_alternative<lkr::CloseByLemma>(instr))
            ++residual;

    Proof pf{System::LKR, prog_r.value()};
    lkr::LKRVerifier v;
    auto rv = v.verify(ctx, wrapped_goal, pf);
    if (!rv.ok()) return "reverify_fail: " + rv.error().to_string();

    // Cache only genuinely cut-free proofs (the Stage A invariant): a residual
    // (axiom-dependent, §7a) proof must never be inlined into a downstream
    // citer, which would reintroduce cuts.
    if (residual == 0 && sh_self.has_value())
        cache[sh_self.value()] = std::move(cutfree);
    return residual == 0 ? "cutfree"
                         : ("residual(" + std::to_string(residual) + ")");
}

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
    CutFreeCache&             cut_free_cache,
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

        // Stage 3 cut-elimination over the verified LKR proof (bug-catcher +
        // cut-free output for the eventual LKR→KS1→comb back-end).
        std::string ce = run_cut_elim(rt.context(), wrapped_goal, lkr_r.value(),
                                      sh_self, cut_free_cache);
        results.push_back({proof_path, name, "ok", "", ce});

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

    // Cut-elim is non-elementary worst-case (B5-C duplicates subderivations),
    // so on big corpus proofs full elimination blows up. Default eliminate_cuts
    // to a modest step budget for this bug-catcher tool so it stays interactive
    // (it reports cutfree / residual / reverify_fail within the budget). Raise
    // via LKR_CUT_ELIM_MAX_STEPS for deeper runs.
    if (!std::getenv("LKR_CUT_ELIM_MAX_STEPS"))
        setenv("LKR_CUT_ELIM_MAX_STEPS", "500", /*overwrite=*/0);
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
    CutFreeCache          cut_free_cache;
    std::vector<StageResult> results;

    // Process dep proofs first (in argv order — caller is responsible
    // for topological ordering), then the main proof file. All theorems
    // share the same maps so dep theorems' facts and cut-free proofs are
    // available to the main file.
    for (const auto& dep : dep_proofs) {
        process_proof_file(rt, dep, theorem_facts, cut_free_cache, results);
    }
    process_proof_file(rt, proof_path, theorem_facts, cut_free_cache, results);

    // Report.
    int ok = 0, unproved_marker = 0;
    std::unordered_map<std::string, int> by_stage;
    // Cut-elim sub-outcomes over the OK theorems (cutfree / residual(n) /
    // *_err / reverify_fail), bucketed by the tag prefix.
    std::unordered_map<std::string, int> by_cut_elim;
    for (const auto& r : results) {
        if (r.stage == "ok") {
            ++ok;
            std::string tag = r.cut_elim.substr(0, r.cut_elim.find_first_of(":("));
            ++by_cut_elim[tag];
        }
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
    if (!by_cut_elim.empty()) {
        std::cout << "  cut-elim (of OK): ";
        bool first = true;
        for (const auto& [tag, count] : by_cut_elim) {
            std::cout << (first ? "" : ", ") << tag << "=" << count;
            first = false;
        }
        std::cout << "\n";
    }
    std::cout << "\n";

    int max_errors = 50;
    if (const char* m = std::getenv("COMB_CHECKER_MAX_ERRORS")) {
        max_errors = std::atoi(m);
    }
    int printed = 0;
    for (const auto& r : results) {
        if (r.stage == "ok") {
            std::cout << "  + " << r.claim << " [cut-elim: " << r.cut_elim << "]\n";
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
