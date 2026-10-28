#pragma once

// Stage 2's translation τ(S, s, T, π) (ELIMINATION_DEMANDS_DESIGN.md §2). Work
// waits on an agenda, so the call depth does not grow with the derivation.

#include "demand.h"
#include "formula_reader.h"
#include "proof_index.h"
#include "sequent_shadow.h"

#include "src/core/formula.h"
#include "src/proof/lkr/ops.h"
#include "src/proof/nd/ops.h"
#include "src/util/error.h"

#include <cstdint>
#include <optional>
#include <variant>
#include <vector>

namespace logic::proof::translate::nd_to_lkr {

class Dispatcher {
public:
    Dispatcher(const ProofIndex& index, const FormulaReader& reader,
               FormulaBuilder& builder, OpSink& sink)
        : index_(index), reader_(reader), builder_(builder), sink_(sink) {}

    util::ResultStatus translate_proof(FormulaHandle goal_nnf);

private:
    struct Task {
        SequentShadow seq;
        StepRef       step;
        Target        target;
        DemandPath    path;
    };

    struct TranslateWork { Task task; };
    struct ExistsIntroWork { Task task; StepRef body; TermBinding witness; };
    using BodyWork = std::variant<TranslateWork, ExistsIntroWork>;
    static Task& task_of(BodyWork& body) {
        return std::visit([](auto& b) -> Task& { return b.task; }, body);
    }
    struct EnterWork {
        BlockId  block;
        size_t   next;
        BodyWork body;
        bool     split{false};
    };
    struct LeftRulesWork {
        SequentShadow seq;
        size_t        dual;
        Target        target;
        DemandPath    path;
    };
    using Work = std::variant<TranslateWork, ExistsIntroWork, EnterWork,
                              LeftRulesWork>;

    util::ResultStatus next(Work w);
    util::ResultStatus next(Task t) {
        return next(Work{TranslateWork{std::move(t)}});
    }
    util::ResultStatus next(std::optional<Work> first, Work second);

    util::ResultStatus run(TranslateWork w) {
        return translate(std::move(w.task));
    }
    util::ResultStatus run(ExistsIntroWork w);
    util::ResultStatus run(EnterWork w);
    util::ResultStatus run(LeftRulesWork w);

    util::ResultStatus translate(Task t);

    util::ResultStatus on(const nd::AndElimL& op, Task t);
    util::ResultStatus on(const nd::AndElimR& op, Task t);
    util::ResultStatus on(const nd::DoubleNegElim& op, Task t);
    util::ResultStatus on(const nd::ForallElim& op, Task t);
    util::ResultStatus on(const nd::ImpliesElim& op, Task t);
    util::ResultStatus on(const nd::IffElimL& op, Task t);
    util::ResultStatus on(const nd::IffElimR& op, Task t);
    util::ResultStatus on(const nd::NotElim& op, Task t);
    util::ResultStatus on(const nd::OrElim& op, Task t);
    util::ResultStatus on(const nd::ExistsIntro& op, Task t);

    util::ResultStatus on(const nd::AndIntro& op, Task t);
    util::ResultStatus on(const nd::OrIntroL& op, Task t);
    util::ResultStatus on(const nd::OrIntroR& op, Task t);
    util::ResultStatus on(const nd::ImpliesIntro& op, Task t);
    util::ResultStatus on(const nd::IffIntro& op, Task t);
    util::ResultStatus on(const nd::ForallIntro& op, Task t);
    util::ResultStatus on(const nd::ExcludedMiddle& op, Task t);
    util::ResultStatus on(const nd::Peirce& op, Task t);

    util::ResultStatus on(const nd::NotIntro& op, Task t);
    util::ResultStatus on(const nd::ClassicalAbsurd& op, Task t);
    util::ResultStatus on(const nd::BottomElim& op, Task t);

    util::ResultStatus on(const nd::Use& op, Task t);
    util::ResultStatus on(const nd::SchemaInst& op, Task t);
    util::ResultStatus on(const nd::Assume& op, Task t);
    util::ResultStatus on(const nd::ExistsElim& op, Task t);

    template <typename Op>
    util::ResultStatus on(const Op& op, Task t);

    util::ResultStatus closer(Task t, StepRef bottom, bool not_intro);
    util::ResultStatus lemma(Task t, lkr::CloseByLemma close);
    util::ResultStatus let_cut(Task t);

    struct Bound {
        SequentShadow       seq;
        std::optional<Work> first;
    };
    util::Result<Bound> bind(SequentShadow seq, StepRef hypothesis,
                             const Minor& m);

    util::Result<BodyWork> exists_elim_body(Task t, StepRef closer) const;

    util::ResultStatus split_projections(SequentShadow& seq, BlockId b);

    util::ResultStatus impossible_head(const Task& t) const;

    util::ResultStatus leaf(Task t, DualSlot slot);
    util::ResultStatus modus(SequentShadow seq, size_t principal,
                             const Minor& m, Target target, DemandPath rest);
    util::ResultStatus cases(SequentShadow seq, size_t principal,
                             DemandCases c, Target target, DemandPath rest);
    util::Result<std::optional<Work>> minor(SequentShadow seq, const Minor& m,
                                            size_t into);
    util::ResultStatus refute(SequentShadow seq, StepRef refuter,
                              Target into, DemandPath path);

    void need(const SequentShadow& seq, StepRef s,
              std::vector<size_t>& out) const;
    void need(const SequentShadow& seq, const DemandPath& path,
              std::vector<size_t>& out) const;
    void need(const SequentShadow& seq, const Minor& m,
              std::vector<size_t>& out) const;
    void need_free(const SequentShadow& seq, const std::vector<uint32_t>& free,
                   std::vector<size_t>& out) const;

    HypId fresh_local() { return HypId::local(next_local_++); }

    const ProofIndex&    index_;
    const FormulaReader& reader_;
    FormulaBuilder&      builder_;
    OpSink&              sink_;
    std::vector<Work>    agenda_;  // the next work is at the back
    uint32_t             next_local_{0};
};

}  // namespace logic::proof::translate::nd_to_lkr
