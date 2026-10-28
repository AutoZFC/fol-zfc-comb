#pragma once

// The identity X, η-expanded to atomic axioms (COMPACT_LKR_DESIGN.md §1).

#include "op_sink.h"
#include "sequent.h"

#include "src/core/formula.h"
#include "src/util/error.h"

#include <cstddef>

namespace logic::proof::lkr_build {

// A's quantifier occurrences: the eigenvariables X uses on A and its dual.
size_t identity_eigens(FormulaHandle a);

util::ResultStatus expand_identity(Sequent seq, size_t a, size_t b,
                                   var_index first_eigen,
                                   FormulaBuilder& builder, OpSink& sink);

}  // namespace logic::proof::lkr_build
