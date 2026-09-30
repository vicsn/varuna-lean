/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AHP

/-!
# The V2 lineval polynomial

snarkVM never commits `ẑ_M = LDE(M z)`. The lineval sumcheck instead
proves the prover-sent sums `σ_M = Σ_{c ∈ C} M̂(α, c) ẑ(c)` with the
polynomial

\[
  f(X) = s(X) + \sum_M \eta_M \hat M(\alpha, X)\, \hat z(X), \qquad \eta_A = 1.
\]

`M̂(α, X)` is a polynomial in `X`; the verifier only ever sees its value at
`β`, as the fourth-round claim that the matrix sumcheck proves. This file
defines `M̂(α, X)`, the faithful `f`, and the verifier's evaluation at `β`,
and proves the identity that makes the chain work : the lineval target
`Σ_c M̂(α, c) ẑ(c)` is the LDE over `R` of the dense product `M z`,
evaluated at `α`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- Sparse matrix on `K`: `nK` entries with row / column indices and values. -/
structure SparseMatrix (F : Type*) where
  /-- Number of (padded) nonzero entries. -/
  nK : Nat
  /-- Constraint-domain row index of entry `k`. -/
  rowIdx : Nat → Nat
  /-- Variable-domain column index of entry `k`. -/
  colIdx : Nat → Nat
  /-- Value of entry `k`. -/
  value : Nat → F

/-- Every row index lies in `R` and every column index in `C`. -/
def SparseMatrix.Bounded (M : SparseMatrix F) (R Cd : EvalDomain F) : Prop :=
  ∀ k, k < M.nK → M.rowIdx k < R.n ∧ M.colIdx k < Cd.n

/-- `M̂(α, X) = Σ_k val_k L^R_{row k}(α) L^C_{col k}(X)`, a polynomial in `X`. -/
noncomputable def matrixAtAlpha (R Cd : EvalDomain F) (M : SparseMatrix F) (α : F) : F[X] :=
  ∑ k ∈ range M.nK, C (M.value k * (R.lagrange (M.rowIdx k)).eval α) * Cd.lagrange (M.colIdx k)

/-- Evaluating `M̂(α, X)` at `b` is the holographic encoding `M̂(α, b)`. -/
theorem eval_matrixAtAlpha (R Cd : EvalDomain F) (M : SparseMatrix F) (α b : F) :
    (matrixAtAlpha R Cd M α).eval b =
      holographicEval R Cd M.nK M.rowIdx M.colIdx M.value α b := by
  simp [matrixAtAlpha, holographicEval, eval_finsetSum, mul_assoc]

/-- `(M z)_r = Σ_k [row k = r] val_k z_{col k}`, with `z_c = ẑ(ω_C^c)`. -/
noncomputable def mzRow (Cd : EvalDomain F) (M : SparseMatrix F) (zhat : F[X]) (r : Nat) : F :=
  ∑ k ∈ range M.nK, if M.rowIdx k = r then M.value k * zhat.eval (Cd.node (M.colIdx k)) else 0

/-- `(M z)_r` is the dense matrix–vector product of `matrixAt` with `z`. -/
theorem mzRow_eq_dense {R Cd : EvalDomain F} {M : SparseMatrix F} (hM : M.Bounded R Cd)
    (zhat : F[X]) (r : Nat) :
    mzRow Cd M zhat r =
      ∑ c ∈ range Cd.n, matrixAt M.nK M.rowIdx M.colIdx M.value r c * zhat.eval (Cd.node c) :=
        by
  unfold mzRow matrixAt
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hc := (hM k (mem_range.mp hk)).2
  by_cases hr : M.rowIdx k = r
  · simp [hr, ite_mul, zero_mul, sum_ite_eq', mem_range.mpr hc, eq_comm]
  · simp [hr]

/-- LDE over `R` of `M z`. -/
noncomputable def mzPoly (R Cd : EvalDomain F) (M : SparseMatrix F) (zhat : F[X]) : F[X] :=
  R.interpolate (mzRow Cd M zhat)

/-- `LDE(M z)` interpolates `M z` on the constraint domain. -/
theorem mzPoly_eval_node (R Cd : EvalDomain F) (M : SparseMatrix F) (zhat : F[X]) {r : Nat}
    (hr : r < R.n) : (mzPoly R Cd M zhat).eval (R.node r) = mzRow Cd M zhat r :=
  R.eval_interpolate _ hr

/-- The lineval target `Σ_k val_k L^R_{row k}(α) ẑ(ω_C^{col k})`. -/
noncomputable def linevalTarget (R Cd : EvalDomain F) (M : SparseMatrix F) (zhat : F[X])
    (α : F) : F :=
  ∑ k ∈ range M.nK, M.value k * (R.lagrange (M.rowIdx k)).eval α * zhat.eval (Cd.node (M.colIdx k))

/-- Summing `M̂(α, c) ẑ(c)` over `C` collapses each Lagrange factor onto its column. -/
theorem sum_matrixAtAlpha_mul {R Cd : EvalDomain F} {M : SparseMatrix F} (hM : M.Bounded R Cd)
    (zhat : F[X]) (α : F) :
    ∑ c ∈ range Cd.n, (matrixAtAlpha R Cd M α).eval (Cd.node c) * zhat.eval (Cd.node c) =
      linevalTarget R Cd M zhat α := by
  unfold matrixAtAlpha linevalTarget
  simp_rw [eval_finsetSum, eval_mul, eval_C, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hc := (hM k (mem_range.mp hk)).2
  have hlag : ∀ c ∈ range Cd.n,
      M.value k * (R.lagrange (M.rowIdx k)).eval α * (Cd.lagrange (M.colIdx k)).eval (Cd.node c) *
          zhat.eval (Cd.node c) =
        if M.colIdx k = c then
          M.value k * (R.lagrange (M.rowIdx k)).eval α * zhat.eval (Cd.node c)
        else 0 := by
    intro c hcm
    rw [Cd.eval_lagrange_node_ite hc (mem_range.mp hcm)]
    split_ifs <;> ring
  rw [sum_congr rfl hlag, sum_ite_eq, if_pos (mem_range.mpr hc)]

/-- The lineval target is `LDE(M z)(α)`. -/
theorem linevalTarget_eq_mzPoly {R Cd : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (zhat : F[X]) (α : F) :
    linevalTarget R Cd M zhat α = (mzPoly R Cd M zhat).eval α := by
  unfold mzPoly EvalDomain.interpolate linevalTarget mzRow
  rw [Lagrange.interpolate_apply]
  simp_rw [eval_finsetSum, eval_mul, eval_C, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hr := (hM k (mem_range.mp hk)).1
  have hterm : ∀ r ∈ R.indexSet,
      (if M.rowIdx k = r then M.value k * zhat.eval (Cd.node (M.colIdx k)) else 0) *
          (Lagrange.basis R.indexSet R.node r).eval α =
        if M.rowIdx k = r then
          M.value k * (R.lagrange (M.rowIdx k)).eval α * zhat.eval (Cd.node (M.colIdx k))
        else 0 := by
    intro r _
    split_ifs with h
    · subst h
      unfold EvalDomain.lagrange
      ring
    · simp
  rw [sum_congr rfl hterm, sum_ite_eq]
  simp [EvalDomain.indexSet, hr]

/-- snarkVM V2 lineval polynomial `s(X) + Σ_M η_M M̂(α, X) ẑ(X)` with `η_A = 1`. -/
noncomputable def linevalPoly (mode : SNARKMode) (mask zhat mA mB mC : F[X]) (ηB ηC : F) :
    F[X] :=
  maskPoly mode mask + (mA + C ηB * mB + C ηC * mC) * zhat

/-- The verifier's `lineval_sumcheck` at `β`: the claims `τ_M` stand in for
`M̂(α, β)` (fourth-round sums), and `w.σ = σ / | C | ` for the batch sum `σ`. -/
noncomputable def linevalEval (mode : SNARKMode) (mask zhat : F[X]) (Cd : EvalDomain F)
    (ηB ηC τA τB τC : F) (w : UnivariateWitness F) (β : F) : F :=
  (maskPoly mode mask).eval β + (τA + ηB * τB + ηC * τC) * zhat.eval β -
    w.h.eval β * Cd.vanishing.eval β - β * w.g.eval β - w.σ

/-- With true claims `τ_M = M̂(α, β)`, the verifier's lineval LC is the
univariate residual of the faithful `linevalPoly` at `β`. -/
theorem linevalEval_eq_residual (mode : SNARKMode) (mask zhat mA mB mC : F[X]) (Cd : EvalDomain F)
    (ηB ηC τA τB τC : F) (w : UnivariateWitness F) (β : F) (hA : τA = mA.eval β)
    (hB : τB = mB.eval β) (hC : τC = mC.eval β) :
    linevalEval mode mask zhat Cd ηB ηC τA τB τC w β =
      (univariateResidual Cd (linevalPoly mode mask zhat mA mB mC ηB ηC) w).eval β := by
  subst hA hB hC
  simp [linevalEval, univariateResidual, linevalPoly, eval_add, eval_mul, eval_sub, eval_C, eval_X]

/-- Domain sum of the faithful lineval polynomial: mask sum plus the
`η`-combination of the three lineval targets. -/
theorem sum_linevalPoly {R Cd : EvalDomain F} {A B Cm : SparseMatrix F} (hA : A.Bounded R Cd)
    (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd) (mode : SNARKMode) (mask zhat : F[X])
    (ηB ηC α : F) :
    ∑ c ∈ range Cd.n,
        (linevalPoly mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
          (matrixAtAlpha R Cd Cm α) ηB ηC).eval (Cd.node c) =
      (∑ c ∈ range Cd.n, (maskPoly mode mask).eval (Cd.node c)) +
        linevalTarget R Cd A zhat α + ηB * linevalTarget R Cd B zhat α +
          ηC * linevalTarget R Cd Cm zhat α := by
  have h : ∀ c ∈ range Cd.n,
      (linevalPoly mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
          (matrixAtAlpha R Cd Cm α) ηB ηC).eval (Cd.node c) =
        (maskPoly mode mask).eval (Cd.node c) +
            (matrixAtAlpha R Cd A α).eval (Cd.node c) * zhat.eval (Cd.node c) +
          ηB * ((matrixAtAlpha R Cd B α).eval (Cd.node c) * zhat.eval (Cd.node c)) +
        ηC * ((matrixAtAlpha R Cd Cm α).eval (Cd.node c) * zhat.eval (Cd.node c)) := by
    intro c _
    simp only [linevalPoly, eval_add, eval_mul, eval_C]
    ring
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_matrixAtAlpha_mul hA, sum_matrixAtAlpha_mul hB, sum_matrixAtAlpha_mul hC]

/-! ## V3 lineval: `η_A` is a challenge -/

/-- V3 lineval polynomial `s + (η_A M̂_A + η_B M̂_B + η_C M̂_C) ẑ`.
V2 is the special case `η_A = 1`. -/
noncomputable def linevalPolyEta (mode : SNARKMode) (mask zhat mA mB mC : F[X])
    (ηA ηB ηC : F) : F[X] :=
  maskPoly mode mask + (C ηA * mA + C ηB * mB + C ηC * mC) * zhat

/-- V2 lineval is V3 lineval at `η_A = 1`. -/
theorem linevalPoly_eq_eta (mode : SNARKMode) (mask zhat mA mB mC : F[X]) (ηB ηC : F) :
    linevalPoly mode mask zhat mA mB mC ηB ηC =
      linevalPolyEta mode mask zhat mA mB mC 1 ηB ηC := by
  simp [linevalPoly, linevalPolyEta]

/-- Verifier lineval LC with a squeezed `η_A`. -/
noncomputable def linevalEvalEta (mode : SNARKMode) (mask zhat : F[X]) (Cd : EvalDomain F)
    (ηA ηB ηC τA τB τC : F) (w : UnivariateWitness F) (β : F) : F :=
  (maskPoly mode mask).eval β + (ηA * τA + ηB * τB + ηC * τC) * zhat.eval β -
    w.h.eval β * Cd.vanishing.eval β - β * w.g.eval β - w.σ

/-- V2 lineval evaluation is V3 at `η_A = 1`. -/
theorem linevalEval_eq_eta (mode : SNARKMode) (mask zhat : F[X]) (Cd : EvalDomain F)
    (ηB ηC τA τB τC : F) (w : UnivariateWitness F) (β : F) :
    linevalEval mode mask zhat Cd ηB ηC τA τB τC w β =
      linevalEvalEta mode mask zhat Cd 1 ηB ηC τA τB τC w β := by
  simp [linevalEval, linevalEvalEta]

/-- With true claims, the V3 lineval LC is the univariate residual of `linevalPolyEta`. -/
theorem linevalEvalEta_eq_residual (mode : SNARKMode) (mask zhat mA mB mC : F[X])
    (Cd : EvalDomain F) (ηA ηB ηC τA τB τC : F) (w : UnivariateWitness F) (β : F)
    (hA : τA = mA.eval β) (hB : τB = mB.eval β) (hC : τC = mC.eval β) :
    linevalEvalEta mode mask zhat Cd ηA ηB ηC τA τB τC w β =
      (univariateResidual Cd (linevalPolyEta mode mask zhat mA mB mC ηA ηB ηC) w).eval β := by
  subst hA hB hC
  simp [linevalEvalEta, univariateResidual, linevalPolyEta, eval_add, eval_mul, eval_sub, eval_C,
    eval_X]

/-- Domain sum of the V3 lineval polynomial. -/
theorem sum_linevalPolyEta {R Cd : EvalDomain F} {A B Cm : SparseMatrix F} (hA : A.Bounded R Cd)
    (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd) (mode : SNARKMode) (mask zhat : F[X])
    (ηA ηB ηC α : F) :
    ∑ c ∈ range Cd.n,
        (linevalPolyEta mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
          (matrixAtAlpha R Cd Cm α) ηA ηB ηC).eval (Cd.node c) =
      (∑ c ∈ range Cd.n, (maskPoly mode mask).eval (Cd.node c)) +
        ηA * linevalTarget R Cd A zhat α + ηB * linevalTarget R Cd B zhat α +
          ηC * linevalTarget R Cd Cm zhat α := by
  have h : ∀ c ∈ range Cd.n,
      (linevalPolyEta mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
          (matrixAtAlpha R Cd Cm α) ηA ηB ηC).eval (Cd.node c) =
        (maskPoly mode mask).eval (Cd.node c) +
          ηA * ((matrixAtAlpha R Cd A α).eval (Cd.node c) * zhat.eval (Cd.node c)) +
          ηB * ((matrixAtAlpha R Cd B α).eval (Cd.node c) * zhat.eval (Cd.node c)) +
          ηC * ((matrixAtAlpha R Cd Cm α).eval (Cd.node c) * zhat.eval (Cd.node c)) := by
    intro c _
    simp only [linevalPolyEta, eval_add, eval_mul, eval_C]
    ring
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    ← mul_sum, sum_matrixAtAlpha_mul hA, sum_matrixAtAlpha_mul hB, sum_matrixAtAlpha_mul hC]

end Varuna