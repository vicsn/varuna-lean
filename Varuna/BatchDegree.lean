/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchEndpoint

/-!
# Residual degrees of the V3 batch

`V3Batch.adaptive_soundness` charges every squeeze at one `b` bounding the three
batched residuals. This file computes `b` from two kinds of bound on a batch
(`V3Batch.Within`) :

* every polynomial the prover commits to has degree below `D`, the number of SRS
  powers (snarkVM `MAX_NUM_POWERS`) : an algebraic prover combines those powers;
* every domain is at most `R`, `C`, `X`, `K` (constraint, variable, input, nonzero).

The selector `s_{H,H_i}` has degree ` | H | − | H_i | `, so a claim of degree
` | H_i | − 1 + e` on `H_i` has degree at most `N − 1 + e` lifted to `H`, for any `N`
bounding both domains (`natDegree_selectorPoly_mul_le`). With the matrix `b` in
product form :

* rowcheck : `max(2R − 2, D + R − 1)` (`V3Batch.natDegree_rowResidual_le`);
* lineval : `D + C + X − 2` (`V3Batch.natDegree_linResidual_le`);
* matrix : `D + 2K − 2` (`V3Batch.natDegree_matrixResidual_le`).

`V3Batch.Within.residualsBounded` : a batch within the bounds has all three
residuals at most `b = max(d_R, d_L, d_M, 1)`, for any weights.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

namespace EvalDomain

variable (H : EvalDomain F)

theorem natDegree_interpolate_le (v : ℕ → F) : (H.interpolate v).natDegree ≤ H.n - 1 := by
  by_cases h0 : H.interpolate v = 0
  · rw [h0, natDegree_zero]
    exact Nat.zero_le _
  have h : (H.interpolate v).degree < (H.n : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (r := v) H.injOn_node
    rwa [indexSet, card_range] at this
  have := (natDegree_lt_iff_degree_lt h0).mpr h
  omega

theorem natDegree_lagrange_le (i : ℕ) : (H.lagrange i).natDegree ≤ H.n - 1 := by
  by_cases hi : i < H.n
  · rw [lagrange, Lagrange.natDegree_basis H.injOn_node (mem_range.mpr hi), indexSet, card_range]
  have hmod : i % H.n < H.n := Nat.mod_lt _ H.n_pos
  have hnode : H.node i = H.node (i % H.n) := by
    unfold node
    conv_lhs => rw [← Nat.mod_add_div i H.n, pow_add, pow_mul, H.hω.pow_eq_one, one_pow, mul_one]
  have hne : i % H.n ≠ i := fun h => hi (h ▸ hmod)
  have hz : H.lagrange i = 0 := by
    unfold lagrange Lagrange.basis
    refine prod_eq_zero (i := i % H.n) (mem_erase.mpr ⟨hne, mem_range.mpr hmod⟩) ?_
    rw [hnode, Lagrange.basisDivisor_self]
  rw [hz, natDegree_zero]
  exact Nat.zero_le _

end EvalDomain

theorem natDegree_selectorPoly_le (H Hi : EvalDomain F) :
    (selectorPoly H Hi).natDegree ≤ H.n - Hi.n := by
  unfold selectorPoly selectorGeom
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_)
  rw [← pow_mul, natDegree_X_pow]
  have h1 : Hi.n * (i + 1) ≤ Hi.n * (H.n / Hi.n) := Nat.mul_le_mul_left _ (mem_range.mp hi)
  have h2 : Hi.n * (H.n / Hi.n) ≤ H.n := Nat.mul_div_le H.n Hi.n
  rw [Nat.mul_succ] at h1
  omega

/-- A claim of degree `|H_i| − 1 + e` on `H_i`, lifted to `H` by the selector, has
degree at most `N − 1 + e` for any `N` bounding both domains. -/
theorem natDegree_selectorPoly_mul_le (H Hi : EvalDomain F) {p : F[X]} {e N : ℕ}
    (hp : p.natDegree ≤ Hi.n - 1 + e) (hH : H.n ≤ N) (hHi : Hi.n ≤ N) :
    (selectorPoly H Hi * p).natDegree ≤ N - 1 + e := by
  have := natDegree_mul_le.trans (add_le_add (natDegree_selectorPoly_le H Hi) hp)
  have := Hi.n_pos
  omega

theorem natDegree_weightedSumPoly_le {d : ℕ} :
    ∀ (ws : List F) (ps : List F[X]), (∀ p ∈ ps, p.natDegree ≤ d) →
      (weightedSumPoly ws ps).natDegree ≤ d
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [weightedSumPoly]
  | w :: ws, p :: ps, h => by
    rw [weightedSumPoly]
    exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (h p (by simp)))
      (natDegree_weightedSumPoly_le ws ps fun q hq => h q (by simp [hq])))

theorem natDegree_C_sub_le (a : F) {p : F[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (C a - p).natDegree ≤ n :=
  (natDegree_sub_le _ _).trans (max_le (by simp) hp)

theorem natDegree_X_mul_add_C_le {g : F[X]} {D : ℕ} (hg : g.natDegree < D) (σ : F) :
    (X * g + C σ).natDegree ≤ D := by
  refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
  have := natDegree_mul_le (p := (X : F[X])) (q := g)
  have := natDegree_X_le (R := F)
  omega

theorem natDegree_maskPoly_le (m : SNARKMode) (p : F[X]) : (maskPoly m p).natDegree ≤ p.natDegree :=
  by cases m <;> simp [maskPoly]

theorem natDegree_matrixAtAlpha_le (R Cd : EvalDomain F) (M : SparseMatrix F) (α : F) :
    (matrixAtAlpha R Cd M α).natDegree ≤ Cd.n - 1 := by
  unfold matrixAtAlpha
  exact natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (natDegree_C_mul_le _ _).trans (Cd.natDegree_lagrange_le _)

namespace MatrixTerm

variable (t : MatrixTerm F)

theorem natDegree_a_le : t.a.natDegree ≤ t.K.n - 1 := by
  unfold a matrixAPoly valOracle
  exact (natDegree_C_mul_le _ _).trans (t.K.natDegree_interpolate_le _)

theorem natDegree_b_le : t.b.natDegree ≤ t.K.n - 1 + (t.K.n - 1) := by
  unfold b matrixBPoly rowOracle colOracle
  exact natDegree_mul_le.trans (add_le_add
    ((natDegree_C_mul_le _ _).trans (natDegree_C_sub_le _ (t.K.natDegree_interpolate_le _)))
    (natDegree_C_sub_le _ (t.K.natDegree_interpolate_le _)))

/-- The numerator `a − b (X g + σ)` with `deg g < D`. -/
theorem natDegree_numer_le {D : ℕ} (hg : t.g.natDegree < D) :
    t.numer.natDegree ≤ t.K.n - 1 + (t.K.n - 1 + D) := by
  unfold numer
  have ha := t.natDegree_a_le
  have hbr :=
    natDegree_mul_le.trans (add_le_add t.natDegree_b_le (natDegree_X_mul_add_C_le hg t.σ))
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;> omega

end MatrixTerm

namespace BatchCircuit

variable (c : BatchCircuit F) (x : BatchInstance F)

theorem natDegree_rowPoly_le : (c.rowPoly x).natDegree ≤ c.R.n - 1 + (c.R.n - 1) := by
  unfold rowPoly mzPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_mul_le.trans
      (add_le_add (c.R.natDegree_interpolate_le _) (c.R.natDegree_interpolate_le _))
  · exact (c.R.natDegree_interpolate_le _).trans (Nat.le_add_right _ _)

theorem natDegree_zhat_le {D : ℕ} (hw : x.w.natDegree < D) :
    (c.zhat x).natDegree ≤ c.Xd.n + D - 1 := by
  unfold zhat assignmentPoly
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have := c.Xd.natDegree_interpolate_le fun k => x.x.getD k 0
    omega
  · have := natDegree_mul_le (p := c.Xd.vanishing) (q := x.w)
    rw [c.Xd.natDegree_vanishing] at this
    omega

theorem natDegree_linPoly_le {D : ℕ} (hw : x.w.natDegree < D) (α ηA ηB ηC : F) :
    (c.linPoly x α ηA ηB ηC).natDegree ≤ c.Cd.n - 1 + (c.Xd.n + D - 1) := by
  unfold linPoly
  refine natDegree_mul_le.trans (add_le_add ?_ (c.natDegree_zhat_le x hw))
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_) <;>
    exact (natDegree_C_mul_le _ _).trans (natDegree_matrixAtAlpha_le _ _ _ _)

end BatchCircuit

/-- Bounds on a batch's degrees : `D` SRS powers, and the largest constraint,
variable, input, and nonzero domains. -/
structure DegreeBounds where
  /-- SRS powers : every committed polynomial has degree below `D`. -/
  D : ℕ
  /-- Constraint domains. -/
  R : ℕ
  /-- Variable domains. -/
  C : ℕ
  /-- Input domains. -/
  X : ℕ
  /-- Nonzero domains. -/
  K : ℕ

namespace DegreeBounds

variable (d : DegreeBounds)

/-- Rowcheck residual degree `max(2R − 2, D + R − 1)`. -/
def dR : ℕ :=
  max (2 * d.R - 2) (d.D + d.R - 1)

/-- Lineval residual degree `D + C + X − 2`. -/
def dL : ℕ :=
  d.D + d.C + d.X - 2

/-- Matrix residual degree `D + 2K − 2`. -/
def dM : ℕ :=
  d.D + 2 * d.K - 2

/-- The per-squeeze charge `max(d_R, d_L, d_M, 1)`. -/
def b : ℕ :=
  max (max d.dR d.dL) (max d.dM 1)

theorem one_le_b : 1 ≤ d.b :=
  le_max_of_le_right (le_max_right _ _)

end DegreeBounds

namespace V3Batch

/-- The batch within `d` : every polynomial the prover commits to has degree below
`d.D`, and every domain is at most `d`'s sizes. -/
structure Within (P : V3Batch F) (d : DegreeBounds) : Prop where
  R : P.R.n ≤ d.R
  Cd : P.Cd.n ≤ d.C
  K : P.K.n ≤ d.K
  circR : ∀ c ∈ P.circuits, c.R.n ≤ d.R
  circC : ∀ c ∈ P.circuits, c.Cd.n ≤ d.C
  circX : ∀ c ∈ P.circuits, c.Xd.n ≤ d.X
  circK : ∀ c ∈ P.circuits, c.KA.n ≤ d.K ∧ c.KB.n ≤ d.K ∧ c.KC.n ≤ d.K
  w : ∀ p ∈ P.instances, p.2.w.natDegree < d.D
  mask : P.mask.natDegree < d.D
  h0 : (toPoly P.h0rep).natDegree < d.D
  h1 : P.h1.natDegree < d.D
  g1 : P.g1.natDegree < d.D
  g : ∀ c ∈ P.circuits, c.gA.natDegree < d.D ∧ c.gB.natDegree < d.D ∧ c.gC.natDegree < d.D
  h2 : P.h2.natDegree < d.D

variable {P : V3Batch F} {d : DegreeBounds}

theorem Within.term (hW : P.Within d) {t : MatrixTerm F} (ht : t ∈ P.matrixTerms) :
    t.K.n ≤ d.K ∧ t.g.natDegree < d.D := by
  obtain ⟨c, hc, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨kA, kB, kC⟩ := hW.circK c hc
  obtain ⟨gA, gB, gC⟩ := hW.g c hc
  simp only [BatchCircuit.matrixTerms, List.mem_cons] at ht
  rcases ht with rfl | rfl | rfl | h
  · exact ⟨kA, gA⟩
  · exact ⟨kB, gB⟩
  · exact ⟨kC, gC⟩
  · simp at h

theorem natDegree_rowResidual_le (hW : P.Within d) (ws : List F) :
    (P.rowResidual ws).natDegree ≤ d.dR := by
  unfold rowResidual batchedZerocheck DegreeBounds.dR
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ ?_)
  · refine natDegree_weightedSumPoly_le _ _ fun q hq => ?_
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcl
    have hc := hW.circR _ (P.fst_mem_circuits hp)
    have h := natDegree_selectorPoly_mul_le P.R p.1.R (p.1.natDegree_rowPoly_le p.2) hW.R hc
    have := p.1.R.n_pos
    show (selectorPoly P.R p.1.R * p.1.rowPoly p.2).natDegree ≤ _
    omega
  · have := natDegree_mul_le (p := toPoly P.h0rep) (q := P.R.vanishing)
    rw [P.R.natDegree_vanishing] at this
    have := hW.h0
    have := hW.R
    omega

theorem natDegree_linResidual_le (hW : P.Within d) (hX : 1 ≤ d.X) (ws : List F) :
    (P.linResidual ws).natDegree ≤ d.dL := by
  have hD : 1 ≤ d.D := by
    have := hW.g1
    omega
  have hC := P.Cd.n_pos
  have hCd := hW.Cd
  dsimp only [linResidual, univariateResidual, linWitness, linevalPoly, DegreeBounds.dL]
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
    (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · have := (natDegree_maskPoly_le P.mode P.mask).trans_lt hW.mask
      omega
    · refine natDegree_weightedSumPoly_le _ _ fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      have hc := P.fst_mem_circuits hp
      have h := natDegree_selectorPoly_mul_le P.Cd p.1.Cd
        (p.1.natDegree_linPoly_le p.2 (hW.w p hp) P.α P.ηA P.ηB P.ηC) hW.Cd (hW.circC _ hc)
      have := hW.circX _ hc
      have := p.1.Xd.n_pos
      omega
  · have := natDegree_mul_le (p := P.h1) (q := P.Cd.vanishing)
    rw [P.Cd.natDegree_vanishing] at this
    have := hW.h1
    omega
  · have := natDegree_mul_le (p := (X : F[X])) (q := P.g1)
    have := natDegree_X_le (R := F)
    have := hW.g1
    omega
  · rw [natDegree_C]
    exact Nat.zero_le _

theorem natDegree_matrixResidual_le (hW : P.Within d) (δs : List F) :
    (batchedMatrixResidual P.K δs P.matrixTerms P.h2).natDegree ≤ d.dM := by
  have hD : 1 ≤ d.D := by
    have := hW.h2
    omega
  have hK := P.K.n_pos
  have hKd := hW.K
  unfold batchedMatrixResidual batchedZerocheck DegreeBounds.dM
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_weightedSumPoly_le _ _ fun q hq => ?_
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hcl
    obtain ⟨htK, htg⟩ := hW.term ht
    have h := natDegree_selectorPoly_mul_le P.K t.K (t.natDegree_numer_le htg) hW.K htK
    have := t.K.n_pos
    show (selectorPoly P.K t.K * t.numer).natDegree ≤ _
    omega
  · have := natDegree_mul_le (p := P.h2) (q := P.K.vanishing)
    rw [P.K.natDegree_vanishing] at this
    have := hW.h2
    omega

/-- The three batched residuals of `Q` have degree at most `b`. -/
def ResidualsBounded (Q : V3Batch F) (chal : V2Challenge → List F) (b : ℕ) : Prop :=
  (Q.rowResidual (Q.rowWeights chal)).natDegree ≤ b ∧
    (Q.linResidual (Q.linWeights chal)).natDegree ≤ b ∧
    (batchedMatrixResidual Q.K (Q.deltaWeights chal) Q.matrixTerms Q.h2).natDegree ≤ b

/-- A batch within `d` has its three residuals at most `d.b`, whatever the squeezes. -/
theorem Within.residualsBounded (hW : P.Within d) (hX : 1 ≤ d.X) (chal : V2Challenge → List F) :
    P.ResidualsBounded chal d.b :=
  ⟨(natDegree_rowResidual_le hW _).trans (le_max_of_le_left (le_max_left _ _)),
    (natDegree_linResidual_le hW hX _).trans (le_max_of_le_left (le_max_right _ _)),
    (natDegree_matrixResidual_le hW _).trans (le_max_of_le_right (le_max_left _ _))⟩

end V3Batch

end Varuna