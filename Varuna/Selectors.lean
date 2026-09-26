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

/-! ## Batched sumcheck -/

/-- Summing over the indices `0 .. n-1` is summing over the domain elements. -/
theorem sum_range_node [DecidableEq F] (H : EvalDomain F) (f : F → F) :
    ∑ i ∈ range H.n, f (H.node i) = ∑ x ∈ H.elements, f x := by
  have hinj : Set.InjOn H.node ↑(range H.n) := H.injOn_node
  have himage : (range H.n).image H.node = H.elements := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact H.ω_pow_mem i
    · rw [card_image_of_injOn hinj, card_range, H.card_elements]
  rw [← himage, sum_image hinj]

/-- The selector turns a sum over `H` into a sum over `H_i`. -/
theorem sum_selectorPoly_mul [DecidableEq F] {H Hi : EvalDomain F} (hdvd : Hi.n ∣ H.n)
    (f : F[X]) :
    ∑ x ∈ H.elements, (selectorPoly H Hi * f).eval x = ∑ x ∈ Hi.elements, f.eval x := by
  have hterm : ∀ x ∈ H.elements,
      (selectorPoly H Hi * f).eval x = if x ∈ Hi.elements then f.eval x else 0 := by
    intro x hx
    rw [eval_mul, selectorPoly_eval_indicator hdvd hx]
    split_ifs <;> simp
  rw [sum_congr rfl hterm, ← sum_filter, filter_mem_eq_inter,
    inter_eq_right.mpr (elements_subset_of_dvd hdvd)]

/-- A weighted sum of differences is the difference of weighted sums. -/
theorem weightedSum_map_sub {α : Type*} (g h : α → F) :
    ∀ (ws : List F) (cs : List α),
      weightedSum ws (cs.map fun c => g c - h c) =
        weightedSum ws (cs.map g) - weightedSum ws (cs.map h)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | w :: ws, c :: cs => by
    simp only [List.map_cons, weightedSum_cons, weightedSum_map_sub g h ws cs]
    ring

/-- Summing weighted sums over a finite set commutes with the combination. -/
theorem sum_weightedSum {α β : Type*} (s : Finset β) (g : β → α → F) :
    ∀ (ws : List F) (cs : List α),
      ∑ x ∈ s, weightedSum ws (cs.map (g x)) = weightedSum ws (cs.map fun c =>
        ∑ x ∈ s, g x c)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | w :: ws, c :: cs => by
    simp only [List.map_cons, weightedSum_cons, sum_add_distrib, ← mul_sum,
      sum_weightedSum s g ws cs]

/-- Per-circuit sum claims `Σ_{x ∈ H_i} f_i(x) − σ_i` for circuits `(H_i, f_i, σ_i)`. -/
noncomputable def batchedSumClaims (cs : List (EvalDomain F × F[X] × F)) : List F :=
  cs.map fun c => ∑ x ∈ c.1.elements, c.2.1.eval x - c.2.2

/-- Batched sumcheck soundness. If the selector-lifted combination sums over
`H` to the combined claim and the combination of per-circuit discrepancies is
not lucky, every circuit's sum over its own domain is its claim. -/
theorem batchedSumcheck_extract [DecidableEq F] {H : EvalDomain F} {ws : List F}
    {cs : List (EvalDomain F × F[X] × F)} (hdvd : ∀ c ∈ cs, c.1.n ∣ H.n)
    (hsum : ∑ x ∈ H.elements,
        (weightedSumPoly ws (cs.map fun c => selectorPoly H c.1 * c.2.1)).eval x =
      weightedSum ws (cs.map fun c => c.2.2))
    (hnone : inspectBatch ws (batchedSumClaims cs) = none) :
    ∀ c ∈ cs, ∑ x ∈ c.1.elements, c.2.1.eval x = c.2.2 := by
  have hlift : ∀ c ∈ cs, ∑ x ∈ H.elements, (selectorPoly H c.1 * c.2.1).eval x =
      ∑ x ∈ c.1.elements, c.2.1.eval x := fun c hc => sum_selectorPoly_mul (hdvd c hc) _
  simp only [eval_weightedSumPoly, List.map_map, Function.comp_def] at hsum
  have hswap := sum_weightedSum H.elements (fun x c => (selectorPoly H c.1 * c.2.1).eval x) ws cs
  rw [hswap, List.map_congr_left hlift] at hsum
  have hws : weightedSum ws (batchedSumClaims cs) = 0 := by
    rw [batchedSumClaims, weightedSum_map_sub, hsum, sub_self]
  have hz := inspectBatch_accepts hws hnone
  intro c hc
  exact sub_eq_zero.mp (hz _ (List.mem_map_of_mem
    (f := fun c : EvalDomain F × F[X] × F => ∑ x ∈ c.1.elements, c.2.1.eval x - c.2.2) hc))

end Varuna