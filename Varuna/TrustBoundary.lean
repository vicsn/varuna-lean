/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.R1CS

/-!
# Trust boundary (iteration 0)

Ironwood keeps the trusted base of every advertised endpoint as a
build-time check (`assert_axioms` / `assert_computable` in
`Zcash/TrustBoundary.lean`). This file is the corresponding census for
Varuna, in stub form.

Iteration 0 pins the proven R1CS lemmas by importing them into the
default `lake build` target and printing their axiom set. A later
iteration will replace `#print axioms` with an `assert_axioms` elaborator
that fails the build on `sorry` or unexpected axioms.

Recorded axiom sets after `lake build` (iteration 0 complete):

* `satisfies_nil`, `hadamardSat_zero`, `unformat_formatPublicInput`,
  `formatPublicInput_nil_admissible` — no axioms
* `satisfies_append`, `satisfies_iff_hadamard`,
  `assignmentOf_format_zero` — `propext`
* `mulConstraint_holds_iff`, `formatted_toy_iff` — `propext`, `Quot.sound`
* `toy_mul_holds`, `formatted_toy_holds` — `propext`, `Classical.choice`,
  `Quot.sound` (`omega` on the concrete assignment)

All of these sit inside the standard classical tier. None mention
`sorryAx`.
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