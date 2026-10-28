#include "proof_index.h"

#include "src/proof/lkr_build/nnf_shapes.h"

#include <algorithm>
#include <iterator>
#include <optional>
#include <utility>
#include <variant>

namespace logic::proof::translate::nd_to_lkr {

namespace {

bool is_hypothesis(const nd::Instr& instr) {
    return std::holds_alternative<nd::Assume>(instr) ||
           std::holds_alternative<nd::ExistsElim>(instr);
}

bool is_binder(const nd::Instr& instr) {
    return std::holds_alternative<nd::Fix>(instr) ||
           std::holds_alternative<nd::ExistsElim>(instr);
}

// Leaves and non-derivations are never shared (§5.2).
bool shareable(const nd::Instr& instr) {
    return !is_hypothesis(instr) &&
           !std::holds_alternative<nd::Fix>(instr) &&
           !std::holds_alternative<nd::Let>(instr) &&
           !std::holds_alternative<nd::Use>(instr) &&
           !std::holds_alternative<nd::SchemaInst>(instr) &&
           !std::holds_alternative<nd::Qed>(instr);
}

bool closes_block(const nd::Instr& instr) {
    if (auto* e = std::get_if<nd::ExistsIntro>(&instr)) {
        return !e->witness.has_value();
    }
    return std::holds_alternative<nd::ForallIntro>(instr) ||
           std::holds_alternative<nd::ImpliesIntro>(instr) ||
           std::holds_alternative<nd::NotIntro>(instr) ||
           std::holds_alternative<nd::ClassicalAbsurd>(instr);
}

void unite(std::vector<uint32_t>& acc, const std::vector<uint32_t>& add) {
    if (add.empty()) return;
    std::vector<uint32_t> out;
    out.reserve(acc.size() + add.size());
    std::set_union(acc.begin(), acc.end(), add.begin(), add.end(),
                   std::back_inserter(out));
    acc = std::move(out);
}

void subtract(std::vector<uint32_t>& acc, const std::vector<uint32_t>& remove) {
    if (remove.empty()) return;
    std::vector<uint32_t> out;
    std::set_difference(acc.begin(), acc.end(), remove.begin(), remove.end(),
                        std::back_inserter(out));
    acc = std::move(out);
}

}  // namespace

// Builds a ProofIndex: blocks, references, projections, FH, I-4, sharing.
class ProofIndexBuilder {
public:
    ProofIndexBuilder(const Program<nd::Instr>&        prog,
                      const nd::NDVerifier::TraceFull& trace,
                      bool                             share)
        : prog_(prog), trace_(trace), share_(share) {}

    util::Result<ProofIndex> run();

private:
    struct Operand {
        StepRef step;
        BlockId position;
    };

    uint32_t size() const { return static_cast<uint32_t>(prog_.instrs.size()); }
    const nd::Instr& instr(uint32_t s) const { return prog_.instrs[s]; }

    void add_block(const Block& block, uint32_t parent, uint32_t depth);
    util::ResultStatus read_levels();
    std::vector<Operand> operands(uint32_t c) const;
    std::vector<uint32_t> binder_operands(uint32_t c) const;
    BlockId lca(BlockId a, BlockId b) const;
    bool encloses(BlockId outer, BlockId inner) const;
    void collect_references();
    void find_projections();
    std::unique_ptr<ProofIndex::Component> component(
        std::vector<StepRef> steps, StepRef root);
    void choose_shared();
    void compute_free(bool sharing);
    util::ResultStatus check_i4() const;

    const Program<nd::Instr>&        prog_;
    const nd::NDVerifier::TraceFull& trace_;
    bool                             share_;
    ProofIndex                       index_;

    std::vector<uint32_t>              opened_by_;
    std::vector<bool>                  hypothesis_;
    std::vector<bool>                  reachable_;
    std::vector<uint32_t>              references_;
    // Reachable consumers of each step, with multiplicity; kInvalidIdx is Qed.
    std::vector<std::vector<uint32_t>> referrers_;
    std::unordered_map<uint32_t, std::vector<uint32_t>> views_of_;
    std::vector<std::optional<BlockId>> cut_block_;
};

util::Result<ProofIndex> ProofIndex::build(
    const Program<nd::Instr>&        prog,
    const nd::NDVerifier::TraceFull& trace,
    bool                             share)
{
    return ProofIndexBuilder(prog, trace, share).run();
}

BlockId ProofIndex::closed_by(StepRef closer) const {
    return BlockId{closed_by_[closer.idx]};
}

util::Result<ProofIndex> ProofIndexBuilder::run() {
    const uint32_t n = size();
    index_.prog_ = &prog_;
    index_.block_of_.assign(n, BlockId{0});
    index_.closed_by_.assign(n, kInvalidIdx);
    opened_by_.assign(n, kInvalidIdx);

    TRY_ASSIGN(root, decompose_blocks(prog_));
    add_block(*root, 0, 0);
    index_.root_ = StepRef{root->target_idx};

    TRY(read_levels());

    hypothesis_.assign(n, false);
    index_.bottom_.assign(n, false);
    index_.requantifies_.assign(n, false);
    for (uint32_t s = 0; s < n; ++s) {
        hypothesis_[s] = is_hypothesis(instr(s));
        FormulaHandle f = trace_.step_env[s];
        if (f.valid()) index_.bottom_[s] = lkr_build::is_falsum(f);
        auto* closer = std::get_if<nd::ExistsIntro>(&instr(s));
        if (closer && !closer->witness.has_value()) {
            index_.requantifies_[s] = trace_.step_env[s] !=
                                      trace_.step_env[closer->body.idx];
        }
    }

    collect_references();
    find_projections();
    index_.shared_.assign(n, false);
    compute_free(/*sharing=*/false);
    TRY(check_i4());
    if (share_) {
        choose_shared();
        compute_free(/*sharing=*/true);
    }
    return std::move(index_);
}

void ProofIndexBuilder::add_block(const Block& block, uint32_t parent,
                                  uint32_t depth)
{
    const uint32_t id = static_cast<uint32_t>(index_.blocks_.size());
    ProofIndex::BlockInfo info;
    info.kind   = block.kind;
    info.opener = StepRef{block.opener_idx};
    info.closer = StepRef{block.closer_idx};
    info.target = StepRef{block.target_idx};
    info.parent = parent;
    info.depth  = depth;
    if (id != parent) info.binders = index_.blocks_[parent].binders;
    if (block.opener_idx != kInvalidIdx && is_binder(instr(block.opener_idx))) {
        info.binders.push_back(StepRef{block.opener_idx});
    }
    index_.blocks_.push_back(std::move(info));

    if (block.opener_idx != kInvalidIdx) {
        index_.block_of_[block.opener_idx] = BlockId{id};
        opened_by_[block.opener_idx] = id;
    }
    if (block.kind != BlockKind::OUTER) {
        index_.closed_by_[block.closer_idx] = id;
        index_.block_of_[block.closer_idx] = BlockId{parent};
    }
    for (const auto& item : block.body) {
        if (auto* flat = std::get_if<FlatStep>(&item)) {
            index_.block_of_[flat->nd_idx] = BlockId{id};
        } else {
            add_block(*std::get<std::unique_ptr<Block>>(item), id, depth + 1);
        }
    }
}

util::ResultStatus ProofIndexBuilder::read_levels() {
    index_.levels_.assign(size(), 0);
    for (uint32_t s = 0; s < size(); ++s) {
        if (!is_binder(instr(s))) continue;
        if (s >= trace_.term_present.size() || !trace_.term_present[s] ||
            !trace_.term_env[s].is_fixed()) {
            return MAKE_ERROR << "ProofIndex: binder #" << s
                              << " has no fixed variable in the trace";
        }
        index_.levels_[s] = trace_.term_env[s].as_variable();
    }
    return util::Ok();
}

std::vector<ProofIndexBuilder::Operand> ProofIndexBuilder::operands(
    uint32_t c) const
{
    BlockId here = index_.block_of_[c];
    BlockId inner{index_.closed_by_[c]};
    std::vector<Operand> out;
    auto at = [&](StepRef x, BlockId p) { out.push_back(Operand{x, p}); };
    std::visit([&](const auto& op) {
        using T = std::decay_t<decltype(op)>;
        if constexpr (std::is_same_v<T, nd::AndIntro>) {
            at(op.a, here); at(op.b, here);
        } else if constexpr (std::is_same_v<T, nd::AndElimL> ||
                             std::is_same_v<T, nd::AndElimR> ||
                             std::is_same_v<T, nd::DoubleNegElim>) {
            at(op.of, here);
        } else if constexpr (std::is_same_v<T, nd::OrIntroL>) {
            at(op.a, here);
        } else if constexpr (std::is_same_v<T, nd::OrIntroR>) {
            at(op.b, here);
        } else if constexpr (std::is_same_v<T, nd::OrElim>) {
            at(op.or_formula, here); at(op.ac, here); at(op.bc, here);
        } else if constexpr (std::is_same_v<T, nd::ImpliesIntro>) {
            at(op.conclusion, inner);
        } else if constexpr (std::is_same_v<T, nd::ImpliesElim>) {
            at(op.impl, here); at(op.ant, here);
        } else if constexpr (std::is_same_v<T, nd::NotIntro> ||
                             std::is_same_v<T, nd::ClassicalAbsurd>) {
            at(op.bottom, inner);
        } else if constexpr (std::is_same_v<T, nd::NotElim>) {
            at(op.negation, here); at(op.formula, here);
        } else if constexpr (std::is_same_v<T, nd::BottomElim>) {
            at(op.bottom, here);
        } else if constexpr (std::is_same_v<T, nd::IffIntro>) {
            at(op.ab, here); at(op.ba, here);
        } else if constexpr (std::is_same_v<T, nd::IffElimL>) {
            at(op.iff, here); at(op.a, here);
        } else if constexpr (std::is_same_v<T, nd::IffElimR>) {
            at(op.iff, here); at(op.b, here);
        } else if constexpr (std::is_same_v<T, nd::ForallIntro>) {
            at(op.body, inner);
        } else if constexpr (std::is_same_v<T, nd::ForallElim>) {
            at(op.formula, here);
        } else if constexpr (std::is_same_v<T, nd::ExistsIntro>) {
            if (op.witness.has_value()) {
                at(op.body, here);
            } else {
                // The ∃E closer's body is inside its block, its ∃x.φ outside.
                at(op.body, inner);
                StepRef opener = index_.blocks_[inner.idx].opener;
                at(std::get<nd::ExistsElim>(instr(opener.idx)).formula, here);
            }
        }
    }, instr(c));
    return out;
}

std::vector<uint32_t> ProofIndexBuilder::binder_operands(uint32_t c) const {
    if (auto* e = std::get_if<nd::ForallElim>(&instr(c))) return {e->term.idx};
    if (auto* e = std::get_if<nd::ExistsIntro>(&instr(c))) {
        if (e->witness.has_value()) return {e->witness->idx};
    }
    return {};
}

BlockId ProofIndexBuilder::lca(BlockId a, BlockId b) const {
    const auto& blocks = index_.blocks_;
    auto depth = [&](BlockId x) { return blocks[x.idx].depth; };
    while (depth(a) > depth(b)) a.idx = blocks[a.idx].parent;
    while (depth(b) > depth(a)) b.idx = blocks[b.idx].parent;
    while (a.idx != b.idx) {
        a.idx = blocks[a.idx].parent;
        b.idx = blocks[b.idx].parent;
    }
    return a;
}

bool ProofIndexBuilder::encloses(BlockId outer, BlockId inner) const {
    return lca(outer, inner) == outer;
}

void ProofIndexBuilder::collect_references() {
    const uint32_t n = size();
    reachable_.assign(n, false);
    references_.assign(n, 0);
    referrers_.assign(n, {});
    cut_block_.assign(n, std::nullopt);

    auto refer = [&](uint32_t consumer, StepRef x, BlockId position,
                     std::vector<uint32_t>& work) {
        ++references_[x.idx];
        referrers_[x.idx].push_back(consumer);
        auto& cut = cut_block_[x.idx];
        cut = cut ? lca(*cut, position) : position;
        if (!reachable_[x.idx]) {
            reachable_[x.idx] = true;
            work.push_back(x.idx);
        }
    };
    std::vector<uint32_t> work;
    refer(kInvalidIdx, index_.root_, index_.outer(), work);
    while (!work.empty()) {
        uint32_t c = work.back();
        work.pop_back();
        for (const Operand& o : operands(c)) refer(c, o.step, o.position, work);
    }
}

void ProofIndexBuilder::find_projections() {
    index_.view_root_.assign(size(), kInvalidIdx);
    for (uint32_t h = 0; h < size(); ++h) {
        if (!hypothesis_[h] || !reachable_[h]) continue;
        auto root = component({StepRef{h}}, StepRef{h});
        if (!root->split()) continue;
        std::sort(views_of_[h].begin(), views_of_[h].end());
        index_.projections_[StepRef{h}] = std::move(root);
    }
    for (auto it = views_of_.begin(); it != views_of_.end();) {
        if (index_.projections_.count(StepRef{it->first})) {
            for (uint32_t v : it->second) index_.view_root_[v] = it->first;
            ++it;
        } else {
            it = views_of_.erase(it);
        }
    }
}

std::unique_ptr<ProofIndex::Component> ProofIndexBuilder::component(
    std::vector<StepRef> steps, StepRef root)
{
    auto c = std::make_unique<ProofIndex::Component>();
    auto has = [&](StepRef s) {
        return std::find(steps.begin(), steps.end(), s) != steps.end();
    };
    for (size_t i = 0; i < steps.size(); ++i) {
        for (uint32_t r : referrers_[steps[i].idx]) {
            if (r != kInvalidIdx &&
                std::holds_alternative<nd::DoubleNegElim>(instr(r)) &&
                !has(StepRef{r})) {
                steps.push_back(StepRef{r});
            }
        }
    }
    std::vector<StepRef> left, right;
    bool projected_only = true;
    for (StepRef s : steps) {
        if (s != root) views_of_[root.idx].push_back(s.idx);
        for (uint32_t r : referrers_[s.idx]) {
            if (r == kInvalidIdx) {
                projected_only = false;
            } else if (std::holds_alternative<nd::AndElimL>(instr(r))) {
                left.push_back(StepRef{r});
            } else if (std::holds_alternative<nd::AndElimR>(instr(r))) {
                right.push_back(StepRef{r});
            } else if (!std::holds_alternative<nd::DoubleNegElim>(instr(r))) {
                projected_only = false;
            }
        }
    }
    c->steps = std::move(steps);
    if (projected_only && (!left.empty() || !right.empty())) {
        if (!left.empty()) c->left = component(std::move(left), root);
        if (!right.empty()) c->right = component(std::move(right), root);
    }
    return c;
}

void ProofIndexBuilder::choose_shared() {
    for (uint32_t s = 0; s < size(); ++s) {
        if (!reachable_[s] || references_[s] < 2 || !shareable(instr(s)) ||
            index_.view_root_[s] != kInvalidIdx) {
            continue;
        }
        index_.shared_[s] = true;
        index_.blocks_[cut_block_[s]->idx].shared.push_back(StepRef{s});
    }
}

void ProofIndexBuilder::compute_free(bool sharing) {
    const uint32_t n = size();
    auto& deriv = index_.free_hypotheses_;
    deriv.assign(n, {});
    std::vector<std::vector<uint32_t>> self(n);
    auto leaf = [&](uint32_t s) {
        return hypothesis_[s] || index_.view_root_[s] != kInvalidIdx;
    };
    auto ref_of = [&](uint32_t s) -> const std::vector<uint32_t>& {
        if (leaf(s) || (sharing && index_.shared_[s])) {
            if (self[s].empty()) self[s] = {s};
            return self[s];
        }
        return deriv[s];
    };

    for (uint32_t s = 0; s < n; ++s) {
        if (leaf(s)) {
            deriv[s] = {s};
            continue;
        }
        std::vector<uint32_t> acc;
        uint32_t closed = index_.closed_by_[s];
        for (const Operand& o : operands(s)) {
            if (closes_block(instr(s)) && o.position.idx == closed) continue;
            unite(acc, ref_of(o.step.idx));
        }
        for (uint32_t b : binder_operands(s)) unite(acc, {b});
        if (closes_block(instr(s))) {
            auto& block = index_.blocks_[closed];
            std::vector<uint32_t> body = ref_of(block.target.idx);
            std::vector<uint32_t> bound;
            if (sharing) {
                for (StepRef k : block.shared) {
                    unite(body, deriv[k.idx]);
                    bound.push_back(k.idx);
                }
            }
            bound.push_back(block.opener.idx);
            if (auto views = views_of_.find(block.opener.idx);
                views != views_of_.end()) {
                bound.insert(bound.end(), views->second.begin(),
                             views->second.end());
            }
            std::sort(bound.begin(), bound.end());
            subtract(body, bound);
            block.free = body;
            unite(acc, block.free);
        }
        deriv[s] = std::move(acc);
    }
}

util::ResultStatus ProofIndexBuilder::check_i4() const {
    for (uint32_t c = 0; c < size(); ++c) {
        if (!reachable_[c]) continue;
        for (const Operand& o : operands(c)) {
            const auto& free = index_.free_hypotheses_[o.step.idx];
            for (uint32_t e : free) {
                uint32_t root = index_.view_root_[e] != kInvalidIdx
                    ? index_.view_root_[e] : e;
                BlockId home{opened_by_[root]};
                if (opened_by_[root] == kInvalidIdx ||
                    !encloses(home, o.position)) {
                    return MAKE_ERROR
                        << "NDtoLKR InputGate: I-4 violation — step #" << c
                        << " uses #" << o.step.idx
                        << ", whose derivation depends on #" << e
                        << ", which is not in scope at #" << c
                        << " (ELIMINATION_DEMANDS_DESIGN.md §4)";
                }
            }
        }
    }
    return util::Ok();
}

}  // namespace logic::proof::translate::nd_to_lkr
