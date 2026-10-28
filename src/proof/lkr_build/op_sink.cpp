#include "op_sink.h"

#include "identity.h"
#include "sequent.h"

#include <utility>

namespace logic::proof::lkr_build {

util::ResultStatus LkrSink::identity(Sequent seq, size_t a, size_t b,
                                     var_index first_eigen,
                                     FormulaBuilder& builder) {
    return expand_identity(std::move(seq), a, b, first_eigen, builder, *this);
}

util::ResultStatus CompactSink::identity(Sequent, size_t a, size_t b,
                                         var_index first_eigen,
                                         FormulaBuilder&) {
    ops_.push_back(Identity{{}, a, b, first_eigen});
    return util::Ok();
}

}  // namespace logic::proof::lkr_build
