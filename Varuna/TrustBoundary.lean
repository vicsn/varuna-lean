/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AxiomCheck
import Varuna.SonicPC

/-!
# Trust boundary (iterations 0–4)

Ironwood keeps the trusted base of every advertised endpoint as a
build-time check. `assert_axioms` fails the build if a named theorem
depends on `sorryAx` or any axiom outside `propext` / `Classical.choice` /
`Quot.sound`. `assert_computable` additionally requires a `def` that is
not `noncomputable` and forbids `Classical.choice` on the data path.
-/

open Varuna.AxiomCheck

assert_axioms Varuna.satisfies_nil
assert_axioms Varuna.satisfies_append
assert_axioms Varuna.mulConstraint_holds_iff
assert_axioms Varuna.hadamardSat_zero
assert_axioms Varuna.satisfies_iff_hadamard
assert_axioms Varuna.unformat_formatPublicInput
assert_axioms Varuna.assignmentOf_format_zero
assert_axioms Varuna.formatPublicInput_nil_admissible
assert_axioms Varuna.toy_mul_holds
assert_axioms Varuna.formatted_toy_holds
assert_axioms Varuna.formatted_toy_iff
assert_axioms Varuna.EvalDomain.vanishing_eq_zero_iff
assert_axioms Varuna.schwartzZippel_card
assert_axioms Varuna.card_szBadSet_le_natDegree
assert_axioms Varuna.eval_ne_zero_of_notMem_szBadSet
assert_axioms Varuna.EvalDomain.eval_lagrange_self
assert_axioms Varuna.EvalDomain.eval_interpolate
assert_axioms Varuna.holographicEval_at_nodes
assert_axioms Varuna.rowOracle_eval
assert_axioms Varuna.colOracle_eval
assert_axioms Varuna.valOracle_eval
assert_axioms Varuna.matrixAt
assert_computable Varuna.CircuitInfo.maxNonZero
assert_axioms Varuna.EvalDomain.vanishing_dvd_of_eval_eq_zero
assert_axioms Varuna.EvalDomain.sum_eval_of_natDegree_lt
assert_axioms Varuna.inspectResidual_accepts
assert_axioms Varuna.rowcheck_on_domain
assert_axioms Varuna.rowcheckResidual_honest
assert_axioms Varuna.rowcheck_extract
assert_axioms Varuna.univariateResidual_honest
assert_axioms Varuna.univariate_sum
assert_axioms Varuna.honestUnivariate_sum
assert_axioms Varuna.univariate_extract
assert_axioms Varuna.matrix_on_domain
assert_axioms Varuna.matrix_rational
assert_axioms Varuna.matrixResidual_honest
assert_axioms Varuna.matrix_extract
assert_axioms Varuna.accepts_of_residuals_zero
assert_computable Varuna.lcWithZeroEval
assert_axioms Varuna.LinearCombination.eval_add
assert_axioms Varuna.kzgCheck_honest
assert_axioms Varuna.pairingBreak_of_double_opening
assert_axioms Varuna.inspectBinding_of_double_check
assert_axioms Varuna.kzgCheck_batch
assert_computable Varuna.LinearCombination.empty