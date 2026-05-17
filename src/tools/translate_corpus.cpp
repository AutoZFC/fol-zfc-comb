// translate_corpus: iterate over all proofs in a .fol.proof file, run the
// ND→LKR translator (translate_and_verify) on each iota-using proof, and
// report per-outcome counts. Used to measure real-world coverage of the
// iota-elimination pre-pass against the isa2fol corpus.
//
// Usage:
//   translate_corpus <bridge.fol.def> <bridge.fol.proof> [--limit N]
//                    [--only-iota] [--show-errors K]
//
// Iota-free proofs are translated too (the iota-free path is exercised
// even without iota), unless --only-iota is set.
//
// Theorems are registered via ND-verify (cheap) before translation, so
// downstream proofs that reference earlier theorems still resolve.

#include "src/parser/parser.h"
#include "src/proof/nd/lowering.h"
#include "src/proof/translate/nd_to_lkr.h"
#include "src/runtime/runtime.h"

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <variant>

using namespace logic;
using namespace logic::proof;

namespace {

int count_iota_elim(const Program<nd::Instr>& prog) {
    int count = 0;
    for (const auto& instr : prog.instrs) {
        if (std::holds_alternative<nd::IotaElim>(instr)) ++count;
    }
    return count;
}

// Strip noisy parts of error messages (line numbers, formula details) so
// distinct failure CAUSES bucket together for reporting.
std::string normalize_err(const std::string& s) {
    std::string out;
    out.reserve(s.size());
    for (char c : s) {
        if (c == '\n') { out.push_back(' '); continue; }
        out.push_back(c);
    }
    // Truncate to a reasonable length.
    if (out.size() > 160) out = out.substr(0, 160) + "...";
    return out;
}

}  // namespace

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: translate_corpus <bridge.fol.def> <bridge.fol.proof> "
                  << "[--limit N] [--only-iota] [--show-errors K]\n";
        return 1;
    }

    std::string def_path = argv[1];
    std::string proof_path = argv[2];
    int limit = -1;
    bool only_iota = false;
    int show_errors = 5;
    for (int i = 3; i < argc; ++i) {
        if (std::strcmp(argv[i], "--limit") == 0 && i + 1 < argc) {
            limit = std::atoi(argv[++i]);
        } else if (std::strcmp(argv[i], "--only-iota") == 0) {
            only_iota = true;
        } else if (std::strcmp(argv[i], "--show-errors") == 0 && i + 1 < argc) {
            show_errors = std::atoi(argv[++i]);
        }
    }

    Runtime rt;

    std::cerr << "Loading " << def_path << "...\n";
    auto def_r = rt.load_file_recursive(def_path);
    if (!def_r.ok()) {
        std::cerr << "ERROR: load .def: " << def_r.error().to_string() << "\n";
        return 1;
    }

    std::cerr << "Parsing " << proof_path << "...\n";
    std::ifstream proof_file(proof_path);
    if (!proof_file.is_open()) {
        std::cerr << "ERROR: open .proof\n";
        return 1;
    }
    std::stringstream buf;
    buf << proof_file.rdbuf();
    std::string err;
    auto proof_result = try_parse_with_proofs(buf.str(), rt.context(), &err);
    if (!err.empty()) {
        std::cerr << "ERROR: parse: " << err << "\n";
        return 1;
    }

    std::cerr << "Parsed " << proof_result.proofs.size() << " proofs.\n";

    int total = 0;
    int skipped_unproved = 0;
    int skipped_iota_free = 0;
    int skipped_no_claim = 0;
    int total_iota_using = 0;
    int translated_ok = 0;
    int lower_failed = 0;
    int translate_failed = 0;
    std::map<std::string, int> failure_buckets;
    std::map<std::string, std::vector<std::string>> failure_examples;

    for (const auto& proof : proof_result.proofs) {
        if (limit > 0 && total >= limit) break;
        ++total;

        if (proof.unproved) {
            ++skipped_unproved;
            continue;
        }

        // Try to register the theorem first so downstream proofs see it.
        // Ignore failures (we'll classify them via the translator path).
        rt.execute_proof(proof);

        auto lowered = nd::lower(proof);
        if (!lowered.ok()) {
            ++lower_failed;
            continue;
        }
        Program<nd::Instr> nd_prog = std::move(lowered).unwrap();
        int iota_count = count_iota_elim(nd_prog);

        if (only_iota && iota_count == 0) {
            ++skipped_iota_free;
            continue;
        }
        if (iota_count > 0) ++total_iota_using;

        auto claim = rt.context().find_claim(proof.claim_name);
        if (!claim.has_value()) claim = rt.context().find_known(proof.claim_name);
        if (!claim.has_value()) {
            ++skipped_no_claim;
            continue;
        }
        FormulaHandle goal = claim.value().get().root();

        auto t_status = translate::translate_and_verify(rt.context(), goal, nd_prog);
        if (t_status.ok()) {
            ++translated_ok;
        } else {
            ++translate_failed;
            std::string msg = normalize_err(t_status.error().to_string());
            // Bucket by the first segment of the error (rough categorization).
            std::string bucket = msg;
            auto colon = bucket.find(':');
            if (colon != std::string::npos && colon < 80) {
                bucket = bucket.substr(0, colon);
            }
            // Even cruder bucket: collapse common prefixes.
            for (const char* prefix : {
                "Phase 2.7 Light", "Phase 2.7 General Or",
                "Phase 2.7 General", "Phase 2.2", "Phase 2.1",
                "Phase 1", "eliminate_iota_in_program",
                "process_single_iota",
            }) {
                if (msg.find(prefix) != std::string::npos) {
                    bucket = prefix;
                    break;
                }
            }
            ++failure_buckets[bucket];
            if (failure_examples[bucket].size() < 2) {
                failure_examples[bucket].push_back(proof.claim_name + ": " + msg);
            }
        }
    }

    std::cout << "\n=== Summary ===\n";
    std::cout << "Total proofs examined:    " << total << "\n";
    std::cout << "  skipped (UNPROVED):     " << skipped_unproved << "\n";
    std::cout << "  skipped (iota-free):    " << skipped_iota_free << "\n";
    std::cout << "  skipped (no claim):     " << skipped_no_claim << "\n";
    std::cout << "  lower failed:           " << lower_failed << "\n";
    std::cout << "  total iota-using:       " << total_iota_using << "\n";
    std::cout << "Translator outcomes (over " << (translated_ok + translate_failed) << " attempts):\n";
    std::cout << "  translated OK:          " << translated_ok << "\n";
    std::cout << "  translator failed:      " << translate_failed << "\n";

    std::cout << "\n=== Failure buckets ===\n";
    std::vector<std::pair<std::string, int>> sorted(failure_buckets.begin(), failure_buckets.end());
    std::sort(sorted.begin(), sorted.end(), [](auto& a, auto& b) { return a.second > b.second; });
    for (const auto& [bucket, cnt] : sorted) {
        std::cout << "[" << cnt << "] " << bucket << "\n";
        if (show_errors > 0) {
            int shown = 0;
            for (const auto& ex : failure_examples[bucket]) {
                if (shown >= show_errors) break;
                std::cout << "    " << ex << "\n";
                ++shown;
            }
        }
    }

    return 0;
}
