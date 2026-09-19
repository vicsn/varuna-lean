/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AxiomCheck
import Varuna.Indexer

/-!
# Trust boundary (iterations 0–2)

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