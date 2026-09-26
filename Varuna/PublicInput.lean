/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AHP

/-!
# The public-input subdomain

Public inputs are bound into the witness polynomial through the input
subdomain `X ⊆ C` : `ẑ = x̂ + v_X ŵ` equals the verifier's `x̂` on `X`
(`assignmentPoly_eval_on_input`), and `reindexBySubdomain` (snarkVM
`reindex_by_subdomain`) places inputs on `X` and the witness off it.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-! ## Public-input subdomain -/

/-- On the input subdomain `X`, the full assignment `x̂ + v_X ŵ` is `x̂`. -/
theorem assignmentPoly_eval_on_input (X : EvalDomain F) (xPoly w : F[X]) {x : F}
    (hx : x ∈ X.elements) : (assignmentPoly X xPoly w).eval x = xPoly.eval x := by
  rw [eval_assignmentPoly, (X.vanishing_eq_zero_iff x).2 hx, zero_mul, add_zero]

/-- snarkVM `reindex_by_subdomain`: input index `i < |S|` goes to `i · period`;
the `j`-th witness index goes to the `j`-th non-multiple of the period. -/
def reindexBySubdomain (nG nS index : Nat) : Nat :=
  if index < nS then index * (nG / nS)
  else
    let i := index - nS
    i + i / (nG / nS - 1) + 1

/-- Input indices land on multiples of the period. -/
theorem reindex_input (nG nS : Nat) {i : Nat} (hi : i < nS) :
    reindexBySubdomain nG nS i = i * (nG / nS) := by
  simp [reindexBySubdomain, hi]

/-- Witness indices never land on a multiple of the period (so never on `X`). -/
theorem reindex_witness_mod_ne_zero {nG nS index : Nat} (hp : 2 ≤ nG / nS) (hi : nS ≤ index) :
    reindexBySubdomain nG nS index % (nG / nS) ≠ 0 := by
  unfold reindexBySubdomain
  rw [if_neg (by omega)]
  simp only
  set x := nG / nS - 1 with hx
  have hxpos : 0 < x := by omega
  have hper : nG / nS = x + 1 := by omega
  set i := index - nS
  have hdecomp : i + i / x + 1 = (i / x) * (x + 1) + (i % x + 1) := by
    have := Nat.div_add_mod i x
    nlinarith [this]
  rw [hper, hdecomp, mul_comm (i / x), Nat.mul_add_mod]
  have hr : i % x < x := Nat.mod_lt _ hxpos
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- With the canonical generator `ω_X = ω_C^{period}`, the `i`-th input node of
`X` is the node of `C` at the reindexed position. -/
theorem input_node_eq (X C : EvalDomain F) (hgen : X.ω = C.ω ^ (C.n / X.n)) {i : Nat}
    (hi : i < X.n) : X.node i = C.node (reindexBySubdomain C.n X.n i) := by
  rw [reindex_input C.n X.n hi]
  unfold EvalDomain.node
  rw [hgen, ← pow_mul, mul_comm]

/-- The public input is bound into the witness polynomial: at every input
position of `C`, `ẑ` equals the verifier's interpolant of the formatted input. -/
theorem assignment_at_input_position (X C : EvalDomain F) (hgen : X.ω = C.ω ^ (C.n / X.n))
    (xs : Nat → F) (w : F[X]) {i : Nat} (hi : i < X.n) :
    (assignmentPoly X (X.interpolate xs) w).eval (C.node (reindexBySubdomain C.n X.n i)) = xs i :=
      by
  rw [← input_node_eq X C hgen hi, assignmentPoly_eval_on_input X _ w (x :=
    X.node i) (X.ω_pow_mem i),
    X.eval_interpolate xs hi]

end Varuna