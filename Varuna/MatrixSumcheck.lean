/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Lineval

/-!
# The matrix sumcheck proves `M̂(α, β)`

The last link of the V2 chain : the rational sumcheck
`a − b (X g + σ) = h v_K` on the indexer's oracles proves the
fourth-round claim ` | K | σ = M̂(α, β)` that lineval consumes.

The key fact is the closed form of a subgroup Lagrange polynomial off the
domain, `L_i(x) = ω^i v_H(x) / ( | H | (x − ω^i))`, which turns each term
`a(κ)/b(κ)` of the rational sum into `val · L^R_row(α) · L^C_col(β)`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

namespace EvalDomain

variable (H : EvalDomain F)

/-- Closed form `(ω^i / |H|) · Σ_{k<n} X^k (ω^i)^{n-1-k}` of the `i`-th Lagrange polynomial. -/
noncomputable def lagrangeClosed (i : Nat) : F[X] :=
  C (H.node i * (H.n : F)⁻¹) * ∑ k ∈ range H.n, X ^ k * C (H.node i) ^ (H.n - 1 - k)

/-- `L_i(X) (X − ω^i) = (ω^i / |H|) v_H(X)`. -/
theorem lagrangeClosed_mul (i : Nat) :
    H.lagrangeClosed i * (X - C (H.node i)) = C (H.node i * (H.n : F)⁻¹) * H.vanishing := by
  have hn : H.node i ^ H.n = 1 := (H.mem_elements_iff).1 (H.ω_pow_mem i)
  unfold lagrangeClosed vanishing
  rw [mul_assoc, geom_sum₂_mul, ← C_pow, hn]

/-- The closed form has degree below `|H|`. -/
theorem natDegree_lagrangeClosed_lt (i : Nat) : (H.lagrangeClosed i).natDegree < H.n := by
  have hsum : (∑ k ∈ range H.n, X ^ k * C (H.node i) ^ (H.n - 1 - k)).natDegree ≤ H.n - 1 :=
    by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hk' := mem_range.mp hk
    calc (X ^ k * C (H.node i) ^ (H.n - 1 - k)).natDegree
        ≤ (X ^ k : F[X]).natDegree + (C (H.node i) ^ (H.n - 1 - k)).natDegree := natDegree_mul_le
      _ ≤ k + 0 := by
          gcongr
          · exact natDegree_X_pow_le k
          · rw [← C_pow, natDegree_C]
      _ ≤ H.n - 1 := by omega
  have := H.n_pos
  calc (H.lagrangeClosed i).natDegree ≤ H.n - 1 := (natDegree_C_mul_le _ _).trans hsum
    _ < H.n := by omega

/-- The closed form is `1` at its own node. -/
theorem eval_lagrangeClosed_self (i : Nat) : (H.lagrangeClosed i).eval (H.node i) = 1 := by
  have hn : H.node i ^ H.n = 1 := (H.mem_elements_iff).1 (H.ω_pow_mem i)
  have hterm : ∀ k ∈ range H.n, H.node i ^ k * H.node i ^ (H.n - 1 - k) = H.node i ^ (H.n - 1) :=
    by
    intro k hk
    rw [← pow_add]
    congr 1
    have := mem_range.mp hk
    omega
  unfold lagrangeClosed
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  have hpos := H.n_pos
  calc H.node i * (H.n : F)⁻¹ * ((H.n : F) * H.node i ^ (H.n - 1))
      = (H.n : F)⁻¹ * (H.n : F) * (H.node i * H.node i ^ (H.n - 1)) := by ring
    _ = H.node i ^ H.n := by
      rw [inv_mul_cancel₀ H.n_ne_zero, one_mul, ← pow_succ']
      congr 1
      omega
    _ = 1 := hn

/-- The closed form vanishes at the other nodes. -/
theorem eval_lagrangeClosed_of_ne {i j : Nat} (hi : i < H.n) (hj : j < H.n) (hij : i ≠ j) :
    (H.lagrangeClosed i).eval (H.node j) = 0 := by
  have hmul := congrArg (eval (H.node j)) (H.lagrangeClosed_mul i)
  have hv : H.vanishing.eval (H.node j) = 0 := (H.vanishing_eq_zero_iff _).2 (H.ω_pow_mem j)
  simp only [eval_mul, eval_sub, eval_X, eval_C, hv, mul_zero] at hmul
  have hne : H.node j - H.node i ≠ 0 := by
    intro h
    exact hij (H.injOn_node (mem_range.mpr hi) (mem_range.mpr hj) (sub_eq_zero.mp h).symm)
  exact (mul_eq_zero.mp hmul).resolve_right hne

/-- The Lagrange polynomial equals its closed form. -/
theorem lagrange_eq_closed {i : Nat} (hi : i < H.n) : H.lagrange i = H.lagrangeClosed i := by
  have hdeg : (H.lagrange i - H.lagrangeClosed i).natDegree < H.elements.card := by
    rw [H.card_elements]
    have hL : (H.lagrange i).natDegree < H.n := by
      unfold lagrange
      rw [Lagrange.natDegree_basis H.injOn_node (mem_range.mpr hi)]
      simp [indexSet, H.n_pos]
    exact (natDegree_sub_le _ _).trans_lt (max_lt hL (H.natDegree_lagrangeClosed_lt i))
  refine sub_eq_zero.mp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ H.elements ?_ hdeg)
  intro x hx
  obtain ⟨j, hj, rfl⟩ := (H.mem_elements_iff_pow).1 hx
  change (H.lagrange i - H.lagrangeClosed i).eval (H.node j) = 0
  rw [eval_sub, H.eval_lagrange_node_ite hi hj]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, H.eval_lagrangeClosed_self, sub_self]
  · rw [if_neg hij, H.eval_lagrangeClosed_of_ne hi hj hij, sub_self]

/-- Off the domain, `L_i(x) = ω^i v_H(x) / (|H| (x − ω^i))`. -/
theorem eval_lagrange_off {i : Nat} (hi : i < H.n) {x : F} (hx : x ∉ H.elements) :
    (H.lagrange i).eval x = H.node i * H.vanishing.eval x / ((H.n : F) * (x - H.node i)) := by
  have hne : x - H.node i ≠ 0 := fun h => hx (sub_eq_zero.mp h ▸ H.ω_pow_mem i)
  have hmul := congrArg (eval x) (H.lagrangeClosed_mul i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hmul
  rw [H.lagrange_eq_closed hi, eq_div_iff (mul_ne_zero H.n_ne_zero hne)]
  calc (H.lagrangeClosed i).eval x * ((H.n : F) * (x - H.node i))
      = (H.n : F) * ((H.lagrangeClosed i).eval x * (x - H.node i)) := by ring
    _ = H.node i * H.vanishing.eval x := by
      rw [hmul, ← mul_assoc, ← mul_assoc, mul_comm (H.n : F), mul_assoc (H.node i),
        mul_inv_cancel₀ H.n_ne_zero, mul_one]

end EvalDomain

/-! ## The rational sum -/

/-- snarkVM's committed `row_col_val`: `val · row · col` at each nonzero. -/
noncomputable def rowColVal (R Cd : EvalDomain F) (M : SparseMatrix F) (k : Nat) : F :=
  M.value k * R.node (M.rowIdx k) * Cd.node (M.colIdx k)

/-- Each term of the rational sum is `val · L^R_row(α) · L^C_col(β)`. -/
theorem matrix_term {R Cd K : EvalDomain F} {M : SparseMatrix F} (hM : M.Bounded R Cd)
    {α β : F} (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements) {k : Nat} (hk : k < K.n)
    (hkM : k < M.nK) :
    (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M)).eval (K.node k) /
        (matrixBPoly R Cd K α β M.rowIdx M.colIdx).eval (K.node k) =
      M.value k * (R.lagrange (M.rowIdx k)).eval α * (Cd.lagrange (M.colIdx k)).eval β := by
  have ⟨hr, hc⟩ := hM k hkM
  have hαr : α - R.node (M.rowIdx k) ≠ 0 := fun h => hα (sub_eq_zero.mp h ▸ R.ω_pow_mem _)
  have hβc : β - Cd.node (M.colIdx k) ≠ 0 := fun h => hβ (sub_eq_zero.mp h ▸ Cd.ω_pow_mem _)
  rw [eval_matrixAPoly _ _ _ hk, eval_matrixBPoly _ _ _ _ _ _ _ hk, R.eval_lagrange_off hr hα,
    Cd.eval_lagrange_off hc hβ]
  unfold rowColVal EvalDomain.sizeAsField
  field_simp [R.n_ne_zero, Cd.n_ne_zero]

/-- Matrix sumcheck value from the domain sum of the remainder, rather than
from a degree bound. `matrix_sumcheck_value` is this plus
`sum_eval_of_natDegree_lt`; a selector batch supplies the same sum via
`batchedSumcheck_extract`. -/
theorem matrix_sumcheck_value_of_sum {R Cd K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β σ : F} {g h : F[X]}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements)
    (hres : matrixResidual K
      (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M))
      (matrixBPoly R Cd K α β M.rowIdx M.colIdx) g h σ = 0)
    (hsum : ∑ k ∈ range K.n, (X * g + C σ).eval (K.node k) = (K.n : F) * σ) :
    (K.n : F) * σ = (matrixAtAlpha R Cd M α).eval β := by
  rw [eval_matrixAtAlpha, holographicEval, hK]
  have hterm : ∀ k ∈ range K.n, (X * g + C σ).eval (K.node k) =
      M.value k * (R.lagrange (M.rowIdx k)).eval α * (Cd.lagrange (M.colIdx k)).eval β := by
    intro k hk
    have hk' := mem_range.mp hk
    have hkM : k < M.nK := hK ▸ hk'
    have ⟨hr, hc⟩ := hM k hkM
    have hb : (matrixBPoly R Cd K α β M.rowIdx M.colIdx).eval (K.node k) ≠ 0 := by
      rw [eval_matrixBPoly _ _ _ _ _ _ _ hk']
      have hαr : α - R.node (M.rowIdx k) ≠ 0 := fun e =>
        hα (sub_eq_zero.mp e ▸ R.ω_pow_mem _)
      have hβc : β - Cd.node (M.colIdx k) ≠ 0 := fun e =>
        hβ (sub_eq_zero.mp e ▸ Cd.ω_pow_mem _)
      unfold EvalDomain.sizeAsField
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero R.n_ne_zero Cd.n_ne_zero) hαr) hβc
    have hrat : (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M)).eval
          (K.node k) / (matrixBPoly R Cd K α β M.rowIdx M.colIdx).eval (K.node k) =
        K.node k * g.eval (K.node k) + σ := matrix_rational hres (K.ω_pow_mem k) hb
    rw [← matrix_term hM hα hβ hk' hkM, hrat]
    simp [eval_add, eval_mul, eval_X, eval_C]
  rw [← sum_congr rfl hterm, hsum]

/-- Matrix sumcheck value. If the rational sumcheck residual is zero on the
indexer's oracles, the remainder has degree below ` | K | `, and `α ∉ R`,
`β ∉ C` (both checked by the verifier), then ` | K | σ = M̂(α, β)`. -/
theorem matrix_sumcheck_value {R Cd K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β σ : F} {g h : F[X]}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements)
    (hres : matrixResidual K
      (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M))
      (matrixBPoly R Cd K α β M.rowIdx M.colIdx) g h σ = 0)
    (hdeg : (X * g + C σ).natDegree < K.n) :
    (K.n : F) * σ = (matrixAtAlpha R Cd M α).eval β := by
  refine matrix_sumcheck_value_of_sum hM hK hα hβ hres ?_
  rw [K.sum_eval_of_natDegree_lt hdeg, coeff_add, coeff_C, coeff_X_mul_zero, zero_add,
    if_pos rfl]

end Varuna