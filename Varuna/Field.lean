/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Mathlib field carrier

The R1CS relation (`Varuna.R1CS`) is stated on integer residues in
`[0, p)`. Domains, PIOPs, and the polynomial commitment use Mathlib
`ZMod p` with `Fact p.Prime`, which is a field. `Bridge.lean` relates
the two carriers.

Algebraic lemmas are stated for an arbitrary `Field`. The deployed
system uses the BLS12-377 scalar field; `Fingerprint.lean` checks one
captured proof over that field.
-/

namespace Varuna

/-- `17` is prime, so the toy field is `ZMod 17`. -/
instance fact_prime_17 : Fact (Nat.Prime 17) :=
  ⟨by decide⟩

/-- Prime field of characteristic `p`. -/
abbrev Fp (p : ℕ) [Fact p.Prime] := ZMod p

/-- Toy prime as a Mathlib field. -/
abbrev ToyField := Fp 17

end Varuna