/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Tactic.LinearCombination
import Varuna.Lineval
import Varuna.Batching
import Varuna.Field

/-!
# The V2 check chain, and the mask-sum shift

snarkVM V2 never commits `ẑ_M`. The three zero-evaluation LCs are chained :

1. `rowcheck_zerocheck` uses the prover-sent sums `σ_M` in place of `ẑ_M(α)`.
2. `lineval_sumcheck` proves `Σ_c (s(c) + Σ_M η_M M̂(α, c) ẑ(c)) = Σ_M η_M σ_M`,
   with `η_A = 1` and the fourth-round claims standing in for `M̂(α, β)`.
3. `matrix_sumcheck` proves those claims.

Composing the first two (the claims are hypotheses `hτ` here) gives

\[
  (A z + e) \circ B z = C z \quad\text{on } R, \qquad e = \sum_{c \in C} s(c).
\]

Nothing checks `e = 0`. The honest mask (`calculate_mask_poly`) has zero
sum, but a prover may commit any mask. Because `η_A = 1` is fixed, the
mask sum moves `σ_A` by `e` without any challenge noticing :
`shifted_witness_accepts` shows that every witness of the shifted relation
passes both LCs at every challenge. The shifted relation is strictly
weaker (`xIsZero_shifted`): a prover can "prove" `5 · 1 = 0`.

This was confirmed end to end against the pinned snarkVM in hiding (ZK)
mode with a prover-only patch; the verifier accepted a proof of `5 · 1 = 0`.
NonZK mode has no mask, so `e = 0` (`v2_chain_nonZK`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- snarkVM V2 `rowcheck_zerocheck` at `α` (single instance): the sums `σ_M`
stand in for `ẑ_M(α)`. -/
noncomputable def rowcheckV2Eval (R : EvalDomain F) (h0 : F[X]) (σA σB σC α : F) : F :=
  σA * σB - σC - h0.eval α * R.vanishing.eval α

/-- Sum of the mask over the variable domain. -/
noncomputable def maskSum (Cd : EvalDomain F) (mode : SNARKMode) (mask : F[X]) : F :=
  ∑ c ∈ range Cd.n, (maskPoly mode mask).eval (Cd.node c)

/-- NonZK has no mask, so its sum is zero. -/
@[simp] theorem maskSum_nonZK (Cd : EvalDomain F) (mask : F[X]) :
    maskSum Cd .NonZK mask = 0 := by
  simp [maskSum]

/-- Rowcheck residual of the shifted relation `(LDE(Az) + e) LDE(Bz) − LDE(Cz) − h₀ v_R`. -/
noncomputable def shiftedRowResidual (R Cd : EvalDomain F) (A B Cm : SparseMatrix F)
    (zhat h0 : F[X]) (e : F) : F[X] :=
  (mzPoly R Cd A zhat + C e) * mzPoly R Cd B zhat - mzPoly R Cd Cm zhat - h0 * R.vanishing

/-- The `η`-combination the lineval sum leaves: `[e + t_A − σ_A, t_B − σ_B, t_C − σ_C]`. -/
noncomputable def etaClaims (R Cd : EvalDomain F) (A B Cm : SparseMatrix F) (zhat : F[X])
    (α e σA σB σC : F) : List F :=
  [e + linevalTarget R Cd A zhat α - σA, linevalTarget R Cd B zhat α - σB,
    linevalTarget R Cd Cm zhat α - σC]

/-- The lineval witness the verifier checks: `(h₁, g₁)` from the prover and
constant term `σ / | C | ` computed from the sums. -/
noncomputable def linevalWitness (Cd : EvalDomain F) (h1 g1 : F[X]) (ηB ηC σA σB σC : F) :
    UnivariateWitness F :=
  ⟨h1, g1, (σA + ηB * σB + ηC * σC) * Cd.sizeInv⟩

/-- The V2 chain. Accepting rowcheck and lineval LCs with true matrix claims,
no Schwartz–Zippel break at `α` or `β`, and no lucky `η`-combination, give
the shifted relation on the constraint domain with shift `e = Σ_C s`. -/
theorem v2_chain [DecidableEq F] {R Cd : EvalDomain F} {A B Cm : SparseMatrix F}
    (hA : A.Bounded R Cd) (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd) (mode : SNARKMode)
    {mask zhat h0 h1 g1 : F[X]} {σA σB σC τA τB τC ηB ηC α β : F}
    (hτA : τA = (matrixAtAlpha R Cd A α).eval β) (hτB : τB = (matrixAtAlpha R Cd B α).eval β)
    (hτC : τC = (matrixAtAlpha R Cd Cm α).eval β)
    (hlin : linevalEval mode mask zhat Cd ηB ηC τA τB τC
      (linevalWitness Cd h1 g1 ηB ηC σA σB σC) β = 0)
    (hlinI : inspectResidual (univariateResidual Cd
      (linevalPoly mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
        (matrixAtAlpha R Cd Cm α) ηB ηC) (linevalWitness Cd h1 g1 ηB ηC σA σB σC)) β = none)
    (hdeg : (X * g1 + C ((σA + ηB * σB + ηC * σC) * Cd.sizeInv)).natDegree < Cd.n)
    (hη : inspectBatch [1, ηB, ηC]
      (etaClaims R Cd A B Cm zhat α (maskSum Cd mode mask) σA σB σC) = none)
    (hrow : rowcheckV2Eval R h0 σA σB σC α = 0)
    (hrowI : inspectResidual (shiftedRowResidual R Cd A B Cm zhat h0 (maskSum Cd mode mask)) α =
      none) :
    ∀ r, r < R.n →
      (mzRow Cd A zhat r + maskSum Cd mode mask) * mzRow Cd B zhat r = mzRow Cd Cm zhat r := by
  set e := maskSum Cd mode mask
  set w := linevalWitness Cd h1 g1 ηB ηC σA σB σC
  have hres := inspectResidual_accepts
    ((linevalEval_eq_residual mode mask zhat _ _ _ Cd ηB ηC τA τB τC w β hτA hτB hτC).symm.trans
      hlin) hlinI
  have hsum := univariate_sum hres hdeg
  rw [sum_linevalPoly hA hB hC] at hsum
  have hn : (Cd.n : F) * ((σA + ηB * σB + ηC * σC) * Cd.sizeInv) = σA + ηB * σB + ηC * σC :=
    by
    rw [mul_comm, mul_assoc, mul_comm Cd.sizeInv, ← EvalDomain.sizeAsField, Cd.mul_sizeInv,
      mul_one]
  have hlinSum : e + linevalTarget R Cd A zhat α + ηB * linevalTarget R Cd B zhat α +
      ηC * linevalTarget R Cd Cm zhat α = σA + ηB * σB + ηC * σC := by
    rw [← hn]
    exact hsum
  have hws : weightedSum [1, ηB, ηC] (etaClaims R Cd A B Cm zhat α e σA σB σC) = 0 := by
    simp only [etaClaims, weightedSum_cons, weightedSum_nil_weights]
    linear_combination hlinSum
  have hz := inspectBatch_accepts hws hη
  have hσA : σA = e + linevalTarget R Cd A zhat α :=
    (sub_eq_zero.mp (hz (e + linevalTarget R Cd A zhat α - σA) (by simp [etaClaims]))).symm
  have hσB : σB = linevalTarget R Cd B zhat α :=
    (sub_eq_zero.mp (hz (linevalTarget R Cd B zhat α - σB) (by simp [etaClaims]))).symm
  have hσC : σC = linevalTarget R Cd Cm zhat α :=
    (sub_eq_zero.mp (hz (linevalTarget R Cd Cm zhat α - σC) (by simp [etaClaims]))).symm
  have hrowEval : (shiftedRowResidual R Cd A B Cm zhat h0 e).eval α = 0 := by
    unfold rowcheckV2Eval at hrow
    rw [hσA, hσB, hσC, linevalTarget_eq_mzPoly hA, linevalTarget_eq_mzPoly hB,
      linevalTarget_eq_mzPoly hC] at hrow
    simp only [shiftedRowResidual, eval_sub, eval_mul, eval_add, eval_C]
    linear_combination hrow
  have hzero := inspectResidual_accepts hrowEval hrowI
  intro r hr
  have hnode := congrArg (eval (R.node r)) hzero
  have hv : R.vanishing.eval (R.node r) = 0 := (R.vanishing_eq_zero_iff _).2 (R.ω_pow_mem r)
  simp only [shiftedRowResidual, eval_sub, eval_mul, eval_add, eval_C, hv, mul_zero, sub_zero,
    eval_zero, mzPoly_eval_node R Cd _ zhat hr] at hnode
  exact sub_eq_zero.mp hnode

/-- In NonZK mode there is no mask, and the chain yields `Az ∘ Bz = Cz` on `R`
for the dense matrices of the index. -/
theorem v2_chain_nonZK [DecidableEq F] {R Cd : EvalDomain F} {A B Cm : SparseMatrix F}
    (hA : A.Bounded R Cd) (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd)
    {mask zhat h0 h1 g1 : F[X]} {σA σB σC τA τB τC ηB ηC α β : F}
    (hτA : τA = (matrixAtAlpha R Cd A α).eval β) (hτB : τB = (matrixAtAlpha R Cd B α).eval β)
    (hτC : τC = (matrixAtAlpha R Cd Cm α).eval β)
    (hlin : linevalEval .NonZK mask zhat Cd ηB ηC τA τB τC
      (linevalWitness Cd h1 g1 ηB ηC σA σB σC) β = 0)
    (hlinI : inspectResidual (univariateResidual Cd
      (linevalPoly .NonZK mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
        (matrixAtAlpha R Cd Cm α) ηB ηC) (linevalWitness Cd h1 g1 ηB ηC σA σB σC)) β = none)
    (hdeg : (X * g1 + C ((σA + ηB * σB + ηC * σC) * Cd.sizeInv)).natDegree < Cd.n)
    (hη : inspectBatch [1, ηB, ηC] (etaClaims R Cd A B Cm zhat α 0 σA σB σC) = none)
    (hrow : rowcheckV2Eval R h0 σA σB σC α = 0)
    (hrowI : inspectResidual (shiftedRowResidual R Cd A B Cm zhat h0 0) α = none) :
    ∀ r, r < R.n → mzRow Cd A zhat r * mzRow Cd B zhat r = mzRow Cd Cm zhat r := by
  intro r hr
  have h := v2_chain hA hB hC .NonZK hτA hτB hτC hlin hlinI hdeg
    (by simpa using hη) hrow (by simpa using hrowI) r hr
  simpa using h

/-- The attack is complete: for any mask with sum `e` and any assignment
satisfying the shifted relation, honest-shaped prover messages make both
LCs vanish at every `α, β, η_B, η_C`, with all residuals identically zero
and all `η`-claims zero, so no inspector reports a break. -/
theorem shifted_witness_accepts {R Cd : EvalDomain F} {A B Cm : SparseMatrix F}
    (hA : A.Bounded R Cd) (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd) (mode : SNARKMode)
    (mask zhat : F[X])
    (hsat : ∀ r, r < R.n →
      (mzRow Cd A zhat r + maskSum Cd mode mask) * mzRow Cd B zhat r = mzRow Cd Cm zhat r)
    (α β ηB ηC : F) :
    let e := maskSum Cd mode mask
    let σA := e + linevalTarget R Cd A zhat α
    let σB := linevalTarget R Cd B zhat α
    let σC := linevalTarget R Cd Cm zhat α
    let zA := mzPoly R Cd A zhat + C e
    let h0 := rowcheckQuotient R zA (mzPoly R Cd B zhat) (mzPoly R Cd Cm zhat)
    let f := linevalPoly mode mask zhat (matrixAtAlpha R Cd A α) (matrixAtAlpha R Cd B α)
      (matrixAtAlpha R Cd Cm α) ηB ηC
    let uw := honestUnivariate Cd f
    rowcheckV2Eval R h0 σA σB σC α = 0 ∧
      shiftedRowResidual R Cd A B Cm zhat h0 e = 0 ∧
      linevalEval mode mask zhat Cd ηB ηC ((matrixAtAlpha R Cd A α).eval β)
        ((matrixAtAlpha R Cd B α).eval β) ((matrixAtAlpha R Cd Cm α).eval β)
        (linevalWitness Cd uw.h uw.g ηB ηC σA σB σC) β = 0 ∧
      univariateResidual Cd f (linevalWitness Cd uw.h uw.g ηB ηC σA σB σC) = 0 ∧
      ∀ x ∈ etaClaims R Cd A B Cm zhat α e σA σB σC, x = 0 := by
  intro e σA σB σC zA h0 f uw
  have hvan : ∀ x ∈ R.elements, (rowcheckPoly zA (mzPoly R Cd B zhat) (mzPoly R Cd Cm zhat)).eval x = 0 :=
    by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (R.mem_elements_iff_pow).1 hx
    have hs := hsat r hr
    have hn : R.ω ^ r = R.node r := rfl
    simp only [rowcheckPoly, zA, eval_sub, eval_mul, eval_add, eval_C, hn,
      mzPoly_eval_node R Cd _ zhat hr]
    exact sub_eq_zero.mpr hs
  have hrowRes := rowcheckResidual_honest hvan
  have hshift : shiftedRowResidual R Cd A B Cm zhat h0 e = 0 := by
    simpa [shiftedRowResidual, rowcheckResidual, rowcheckPoly, zA, h0] using hrowRes
  have hsumf : ∑ c ∈ range Cd.n, f.eval (Cd.node c) = σA + ηB * σB + ηC * σC := by
    simp only [f, sum_linevalPoly hA hB hC, σA, σB, σC, e, maskSum]
  have hσw : uw.σ = (σA + ηB * σB + ηC * σC) * Cd.sizeInv := by
    have h := honestUnivariate_sum Cd f
    rw [hsumf] at h
    have hn : (Cd.n : F) * Cd.sizeInv = 1 := Cd.mul_sizeInv
    rw [h, mul_comm (Cd.n : F), mul_assoc, hn, mul_one]
  have hw : linevalWitness Cd uw.h uw.g ηB ηC σA σB σC = uw := by
    unfold linevalWitness
    rw [← hσw]
  have hlinRes : univariateResidual Cd f (linevalWitness Cd uw.h uw.g ηB ηC σA σB σC) = 0 := by
    rw [hw]
    exact univariateResidual_honest Cd f
  refine ⟨?_, hshift, ?_, hlinRes, ?_⟩
  · have := congrArg (eval α) hshift
    simp only [shiftedRowResidual, eval_sub, eval_mul, eval_add, eval_C, eval_zero] at this
    simp only [rowcheckV2Eval, σA, σB, σC, linevalTarget_eq_mzPoly hA, linevalTarget_eq_mzPoly hB,
      linevalTarget_eq_mzPoly hC]
    linear_combination this
  · rw [linevalEval_eq_residual mode mask zhat _ _ _ Cd ηB ηC _ _ _ _ β rfl rfl rfl, hlinRes,
      eval_zero]
  · intro x hx
    simp only [etaClaims, σA, σB, σC, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> ring

/-! ## The shifted relation is strictly weaker -/

/-- Sparse constraints with every `A`-row shifted by `e`: `(A_i·z + e)(B_i·z) = C_i·z`. -/
def satisfiesShifted (cs : List Constraint) (asg : Assignment) (p : Nat) (e : Int) : Prop :=
  ∀ c ∈ cs, mul (add (dotProduct c.a asg p) e p) (dotProduct c.b asg p) p = dotProduct c.c asg p

/-- The PoC statement `x · 1 = 0` over the formatted slot `x = z₁`. -/
def xIsZero : Constraint :=
  { a := [(1, .var 1)], b := [(1, .one)], c := [] }

/-- Formatted assignment with public input `x = 5`. -/
def xIsFive : Assignment
  | 0 => 1
  | 1 => 5
  | _ => 0

/-- Over `𝔽₁₇`, `x · 1 = 0` is false at `x = 5`. -/
theorem xIsZero_false : ¬ satisfies [xIsZero] xIsFive toyPrime := by
  simp [satisfies, constraintHolds, xIsZero, dotProduct, xIsFive, toyPrime, PseudoVar.value, add,
    mul]

/-- With shift `e = −5 ≡ 12`, the same instance satisfies the shifted relation. -/
theorem xIsZero_shifted : satisfiesShifted [xIsZero] xIsFive toyPrime 12 := by
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  simp [xIsZero, dotProduct, xIsFive, toyPrime, PseudoVar.value, add, mul]

end Varuna