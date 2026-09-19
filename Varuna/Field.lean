/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Mathlib field carrier

Iteration 0 used a hand-rolled `[0, p)` integer carrier so the R1CS
relation could be stated without Mathlib. Iteration 1 switches the AHP
layer to Mathlib `ZMod p` with `Fact p.Prime`, which is a field.

The deployed system uses the BLS12-377 scalar field; that concrete pin
is later work. The algebraic lemmas (domains, vanishing, Schwartz–Zippel)
are stated for an arbitrary `Field`.
-/

namespace Varuna

/-- `17` is prime; the iteration-0 toy field is therefore `ZMod 17`. -/
instance fact_prime_17 : Fact (Nat.Prime 17) :=
  ⟨by decide⟩

/-- Prime field of characteristic `p`. -/
abbrev Fp (p : ℕ) [Fact p.Prime] := ZMod p

/-- The iteration-0 toy prime, now as a Mathlib field. -/
abbrev ToyField := Fp 17

end Varuna