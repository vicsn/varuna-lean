/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Domain

/-!
# Trust boundary (iterations 0–1)

Ironwood keeps the trusted base of every advertised endpoint as a
build-time check (`assert_axioms` / `assert_computable` in
`Zcash/TrustBoundary.lean`). This file is the corresponding census for
Varuna, in stub form.

A later iteration will replace `#print axioms` with an `assert_axioms`
elaborator that fails the build on `sorry` or unexpected axioms.

Recorded axiom sets after `lake build` :

* iteration 0 R1CS lemmas — `propext` / `Classical.choice` / `Quot.sound`
  as listed previously; none mention `sorryAx`
* `EvalDomain.vanishing_eq_zero_iff`, `schwartzZippel_card`,
  `card_szBadSet_le_natDegree`, `eval_ne_zero_of_notMem_szBadSet`,
  `EvalDomain.eval_lagrange_self` — `propext`, `Classical.choice`,
  `Quot.sound`
-/

#print axioms Varuna.satisfies_nil
#print axioms Varuna.satisfies_append
#print axioms Varuna.mulConstraint_holds_iff
#print axioms Varuna.hadamardSat_zero
#print axioms Varuna.satisfies_iff_hadamard
#print axioms Varuna.unformat_formatPublicInput
#print axioms Varuna.assignmentOf_format_zero
#print axioms Varuna.formatPublicInput_nil_admissible
#print axioms Varuna.toy_mul_holds
#print axioms Varuna.formatted_toy_holds
#print axioms Varuna.formatted_toy_iff
#print axioms Varuna.EvalDomain.vanishing_eq_zero_iff
#print axioms Varuna.schwartzZippel_card
#print axioms Varuna.card_szBadSet_le_natDegree
#print axioms Varuna.eval_ne_zero_of_notMem_szBadSet
#print axioms Varuna.EvalDomain.eval_lagrange_self