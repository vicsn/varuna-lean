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

Iteration 0 pins the first proven R1CS lemmas by importing them into the
default `lake build` target and printing their axiom set. A later
iteration will replace `#print axioms` with an `assert_axioms` elaborator
that fails the build on `sorry` or unexpected axioms.

Recorded axiom sets after `lake build` (iteration 0):

* `satisfies_nil`, `hadamardSat_zero` — no axioms
* `satisfies_append` — `propext`
* `mulConstraint_holds_iff` — `propext`, `Quot.sound`
* `toy_mul_holds` — `propext`, `Classical.choice`, `Quot.sound`
  (`omega` on the concrete assignment)

All of these sit inside the standard classical tier. None mention
`sorryAx`.
-/

#print axioms Varuna.satisfies_nil
#print axioms Varuna.satisfies_append
#print axioms Varuna.mulConstraint_holds_iff
#print axioms Varuna.hadamardSat_zero
#print axioms Varuna.toy_mul_holds
