/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Batching

/-!
# Selectors as indicators, and batched checks

On the common domain `H`, snarkVM's selector `s_{H,H_i}` is the indicator
of the subdomain `H_i`. That is what makes batching sound : a batched
identity, restricted to a point of `H`, is a combination of the
per-circuit claims at that point, so either each claim vanishes or the
combination is a computed batch break (`inspectBatch`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- A subdomain of a nested FFT domain lies inside it. -/
theorem elements_subset_of_dvd {H Hi : EvalDomain F} (hdvd : Hi.n ∣ H.n) :
    Hi.elements ⊆ H.elements := by
  intro x hx
  obtain ⟨m, hm⟩ := hdvd
  rw [H.mem_elements_iff, hm, pow_mul, (Hi.mem_elements_iff).1 hx, one_pow]

/-- On `H_i` the selector is `1`. -/
theorem selectorPoly_eval_of_mem {H Hi : EvalDomain F} (hdvd : Hi.n ∣ H.n) {x : F}
    (hx : x ∈ Hi.elements) : (selectorPoly H Hi).eval x = 1 := by
  have hxn : x ^ Hi.n = 1 := (Hi.mem_elements_iff).1 hx
  have hcast : ((H.n / Hi.n : ℕ) : F) * (Hi.n : F) = (H.n : F) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  unfold selectorPoly selectorGeom EvalDomain.sizeAsField EvalDomain.sizeInv
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X, hxn, one_pow, sum_const,
    card_range, nsmul_eq_mul, mul_one]
  rw [mul_comm ((Hi.n : F)), mul_assoc, mul_comm _ ((H.n / Hi.n : ℕ) : F), hcast,
    inv_mul_cancel₀ H.n_ne_zero]

/-- On `H \ H_i` the selector is `0`. -/
theorem selectorPoly_eval_of_not_mem {H Hi : EvalDomain F} (hdvd : Hi.n ∣ H.n) {x : F}
    (hx : x ∈ H.elements) (hxi : x ∉ Hi.elements) : (selectorPoly H Hi).eval x = 0 := by
  have hy : x ^ Hi.n ≠ 1 := fun h => hxi ((Hi.mem_elements_iff).2 h)
  have hym : (x ^ Hi.n) ^ (H.n / Hi.n) = 1 := by
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, (H.mem_elements_iff).1 hx]
  have hgeom : (x ^ Hi.n - 1) * ∑ i ∈ range (H.n / Hi.n), (x ^ Hi.n) ^ i = 0 := by
    rw [mul_geom_sum, hym, sub_self]
  have hsum : ∑ i ∈ range (H.n / Hi.n), (x ^ Hi.n) ^ i = 0 :=
    (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hy)
  unfold selectorPoly selectorGeom
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X, hsum, mul_zero]

/-- On `H` the selector is the indicator of `H_i`. -/
theorem selectorPoly_eval_indicator {H Hi : EvalDomain F} (hdvd : Hi.n ∣ H.n) {x : F}
    (hx : x ∈ H.elements) [Decidable (x ∈ Hi.elements)] :
    (selectorPoly H Hi).eval x = if x ∈ Hi.elements then 1 else 0 := by
  split_ifs with h
  · exact selectorPoly_eval_of_mem hdvd h
  · exact selectorPoly_eval_of_not_mem hdvd hx h

/-! ## Batched zerocheck -/

/-- Batched zerocheck numerator `Σ_i ν_i s_{H,H_i} P_i` over circuits `(H_i, P_i)`. -/
noncomputable def batchedZerocheck (H : EvalDomain F) (ws : List F)
    (cs : List (EvalDomain F × F[X])) : F[X] :=
  weightedSumPoly ws (cs.map fun c => selectorPoly H c.1 * c.2)

/-- Per-circuit claims `s_{H,H_i}(x) P_i(x)` at a point of `H`. -/
noncomputable def batchedClaims (H : EvalDomain F) (cs : List (EvalDomain F × F[X])) (x : F) :
    List F :=
  cs.map fun c => (selectorPoly H c.1 * c.2).eval x

/-- Batched zerocheck soundness. If the batched numerator is a multiple of
`v_H` and no point of `H` yields a lucky combination, every circuit's
numerator vanishes on its own domain. -/
theorem batchedZerocheck_extract [DecidableEq F] {H : EvalDomain F} {ws : List F}
    {cs : List (EvalDomain F × F[X])} (hdvd : ∀ c ∈ cs, c.1.n ∣ H.n) {h : F[X]}
    (hid : batchedZerocheck H ws cs = h * H.vanishing)
    (hnone : ∀ x ∈ H.elements, inspectBatch ws (batchedClaims H cs x) = none) :
    ∀ c ∈ cs, ∀ x ∈ c.1.elements, c.2.eval x = 0 := by
  intro c hc x hxi
  have hx : x ∈ H.elements := elements_subset_of_dvd (hdvd c hc) hxi
  have hev := congrArg (eval x) hid
  rw [batchedZerocheck, eval_weightedSumPoly, eval_mul, (H.vanishing_eq_zero_iff x).2 hx,
    mul_zero, List.map_map] at hev
  have hall := inspectBatch_accepts hev (hnone x hx)
  have hmem : (selectorPoly H c.1 * c.2).eval x ∈ batchedClaims H cs x :=
    List.mem_map_of_mem (f := fun c : EvalDomain F × F[X] => (selectorPoly H c.1 * c.2).eval x) hc
  have hzero := hall _ hmem
  rwa [eval_mul, selectorPoly_eval_of_mem (hdvd c hc) hxi, one_mul] at hzero

end Varuna