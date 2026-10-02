/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Indexer

/-!
# AHP PIOPs (VarunaVersion.V2, algebraic / interactive)

The deployed verifier checks three virtual linear combinations
(`AHPForR1CS::LC_WITH_ZERO_EVAL` in snarkVM):

* `rowcheck_zerocheck` — `σ_A σ_B − σ_C = h₀(α) v_H(α)`
* `lineval_sumcheck` — univariate sumcheck of the lineval polynomial
* `matrix_sumcheck` — rational sumcheck of the sparse row·col·val encoding

This module treats challenges as free field elements (the interactive AHP).
The Fiat–Shamir schedule is `Varuna.FiatShamir`. Multi-circuit selectors
are `Varuna.Batching` and `Varuna.Selectors`.

Soundness is stated Ironwood-style : inspecting a residual at a challenge
returns either “the identity holds identically” or the challenge as
Schwartz–Zippel break data. Completeness is a sibling theorem, not a
hypothesis of soundness.

Zero-knowledge masking (`SNARKMode::ZK`, `mask_poly`) is parameterized.
The honest-verifier simulator is `Varuna.ZK`. Non-ZK mode drops the mask.
-/

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- snarkVM `SNARKMode`: whether witness polynomials are masked. -/
inductive SNARKMode where
  /-- Masking polynomials are included (zero-knowledge). -/
  | ZK
  /-- No masking (succinct non-ZK). -/
  | NonZK
  deriving DecidableEq, Repr

/-- Optional mask: the polynomial itself in ZK mode, otherwise `0`. -/
noncomputable def maskPoly (mode : SNARKMode) (mask : F[X]) : F[X] :=
  match mode with
  | .ZK => mask
  | .NonZK => 0

/-- The non-ZK mask is the zero polynomial. -/
@[simp] theorem maskPoly_nonZK (mask : F[X]) : maskPoly .NonZK mask = 0 :=
  rfl

/-- Inspect a residual at a challenge: `none` means the identity holds
identically or the verifier rejects; `some α` is SZ-break data. -/
noncomputable def inspectResidual [DecidableEq F] (res : F[X]) (α : F) : Option F :=
  if res = 0 then none
  else if res.eval α = 0 then some α
  else none

/-- A zero residual never yields break data. -/
theorem inspectResidual_eq_none_of_zero [DecidableEq F] {res : F[X]} {α : F}
    (h : res = 0) : inspectResidual res α = none := by
  simp [inspectResidual, h]

/-- If the verifier accepts (`res(α) = 0`) and inspection returns no break,
the residual is the zero polynomial. -/
theorem inspectResidual_accepts [DecidableEq F] {res : F[X]} {α : F}
    (hacc : res.eval α = 0) (h : inspectResidual res α = none) : res = 0 := by
  by_cases h0 : res = 0
  · exact h0
  · have hsome : inspectResidual res α = some α := by
      simp [inspectResidual, h0, hacc]
    rw [hsome] at h
    cases h

/-- A nonzero residual that vanishes at `α` is reported as break data. -/
theorem inspectResidual_szBreak [DecidableEq F] {res : F[X]} {α : F}
    (hne : res ≠ 0) (hα : res.eval α = 0) :
    inspectResidual res α = some α := by
  simp [inspectResidual, hne, hα]

/-- Labels of the three virtual commitments that must evaluate to zero. -/
def lcWithZeroEval : List String :=
  ["matrix_sumcheck", "lineval_sumcheck", "rowcheck_zerocheck"]

/-! ## Rowcheck (`rowcheck_zerocheck`) -/

/-- Rowcheck numerator `z_A z_B − z_C`. -/
noncomputable def rowcheckPoly (zA zB zC : F[X]) : F[X] :=
  zA * zB - zC

/-- Residual of `z_A z_B − z_C = h₀ v_H`. -/
noncomputable def rowcheckResidual (H : EvalDomain F) (zA zB zC h0 : F[X]) : F[X] :=
  rowcheckPoly zA zB zC - h0 * H.vanishing

/-- Honest rowcheck quotient by the monic vanishing polynomial. -/
noncomputable def rowcheckQuotient (H : EvalDomain F) (zA zB zC : F[X]) : F[X] :=
  rowcheckPoly zA zB zC /ₘ H.vanishing

/-- snarkVM `rowcheck_zerocheck` at `α` (single instance, combiners `= 1`). -/
noncomputable def rowcheckEval (H : EvalDomain F) (zA zB zC h0 : F[X]) (α : F) : F :=
  (zA.eval α * zB.eval α - zC.eval α) - h0.eval α * H.vanishing.eval α

/-- The LC evaluation is the residual polynomial evaluated at the challenge. -/
theorem rowcheckEval_eq (H : EvalDomain F) (zA zB zC h0 : F[X]) (α : F) :
    rowcheckEval H zA zB zC h0 α = (rowcheckResidual H zA zB zC h0).eval α := by
  simp [rowcheckEval, rowcheckResidual, rowcheckPoly, eval_sub, eval_mul]

/-- A zero residual makes the verifier equation hold at every challenge. -/
theorem rowcheckEval_eq_zero_of_residual (H : EvalDomain F) (zA zB zC h0 : F[X])
    (h : rowcheckResidual H zA zB zC h0 = 0) (α : F) :
    rowcheckEval H zA zB zC h0 α = 0 := by
  simp [rowcheckEval_eq, h]

/-- If the residual is identically zero, the Hadamard identity holds on `H`. -/
theorem rowcheck_on_domain {H : EvalDomain F} {zA zB zC h0 : F[X]}
    (h : rowcheckResidual H zA zB zC h0 = 0) {α : F} (hα : α ∈ H.elements) :
    zA.eval α * zB.eval α = zC.eval α := by
  have := congrArg (eval α) h
  simp [rowcheckResidual, rowcheckPoly, eval_sub, eval_mul,
    (H.vanishing_eq_zero_iff α).2 hα] at this
  exact sub_eq_zero.mp this

/-- Completeness: a product that vanishes on `H` is exactly `h₀ v_H` for the
honest quotient. -/
theorem rowcheckResidual_honest {H : EvalDomain F} {zA zB zC : F[X]}
    (hp : ∀ α ∈ H.elements, (rowcheckPoly zA zB zC).eval α = 0) :
    rowcheckResidual H zA zB zC (rowcheckQuotient H zA zB zC) = 0 := by
  have hdiv := H.vanishing_dvd_of_eval_eq_zero hp
  unfold rowcheckResidual rowcheckQuotient
  have hmod : rowcheckPoly zA zB zC %ₘ H.vanishing = 0 :=
    (modByMonic_eq_zero_iff_dvd H.vanishing_monic).2 hdiv
  have hdecomp := modByMonic_add_div (rowcheckPoly zA zB zC) H.vanishing
  rw [hmod, zero_add, mul_comm] at hdecomp
  exact sub_eq_zero.mpr hdecomp.symm

/-- Completeness of the LC check for an honest rowcheck witness. -/
theorem rowcheckEval_honest {H : EvalDomain F} {zA zB zC : F[X]}
    (hp : ∀ α ∈ H.elements, (rowcheckPoly zA zB zC).eval α = 0) (α : F) :
    rowcheckEval H zA zB zC (rowcheckQuotient H zA zB zC) α = 0 :=
  rowcheckEval_eq_zero_of_residual _ _ _ _ _
    (rowcheckResidual_honest hp) α

/-- Soundness at a good challenge: a nonzero residual is rejected. -/
theorem rowcheck_sound [DecidableEq F] {H : EvalDomain F} {zA zB zC h0 : F[X]} {α : F}
    (hne : rowcheckResidual H zA zB zC h0 ≠ 0)
    (hα : α ∉ szBadSet (rowcheckResidual H zA zB zC h0)) :
    rowcheckEval H zA zB zC h0 α ≠ 0 := by
  rw [rowcheckEval_eq]
  exact eval_ne_zero_of_notMem_szBadSet hne hα

/-- Accepting rowcheck at `α` yields the Hadamard identity on `H` or SZ-break
data. -/
theorem rowcheck_extract [DecidableEq F] {H : EvalDomain F} {zA zB zC h0 : F[X]} {α : F}
    (hacc : rowcheckEval H zA zB zC h0 α = 0)
    (hnone : inspectResidual (rowcheckResidual H zA zB zC h0) α = none)
    {β : F} (hβ : β ∈ H.elements) :
    zA.eval β * zB.eval β = zC.eval β :=
  rowcheck_on_domain
    (inspectResidual_accepts (rowcheckEval_eq H zA zB zC h0 α ▸ hacc) hnone) hβ

/-! ## Univariate / lineval sumcheck (`lineval_sumcheck`) -/

/-- Witness polynomials for `f = h v_K + X g + σ`. `σ` is the protocol’s
claimed `sum / | K | ` (the constant term of the remainder). -/
structure UnivariateWitness (F : Type*) [Semiring F] where
  /-- Quotient by the vanishing polynomial. -/
  h : F[X]
  /-- Shifted remainder (`coeffs[1..]` in snarkVM). -/
  g : F[X]
  /-- Constant term of the remainder (`σ / |K|`). -/
  σ : F

/-- Residual of the univariate sumcheck identity. -/
noncomputable def univariateResidual (K : EvalDomain F) (f : F[X])
    (w : UnivariateWitness F) : F[X] :=
  f - w.h * K.vanishing - X * w.g - C w.σ

/-- Honest sumcheck witness by monic division (snarkVM `from_coefficients_slice`). -/
noncomputable def honestUnivariate (K : EvalDomain F) (f : F[X]) :
    UnivariateWitness F :=
  let r := f %ₘ K.vanishing
  { h := f /ₘ K.vanishing
    g := divX r
    σ := r.coeff 0 }

/-- snarkVM `lineval_sumcheck` at `β` (single instance, combiners `= 1`). -/
noncomputable def univariateEval (K : EvalDomain F) (f : F[X])
    (w : UnivariateWitness F) (β : F) : F :=
  f.eval β - w.h.eval β * K.vanishing.eval β - β * w.g.eval β - w.σ

/-- The LC evaluation is the residual at the challenge. -/
theorem univariateEval_eq (K : EvalDomain F) (f : F[X])
    (w : UnivariateWitness F) (β : F) :
    univariateEval K f w β = (univariateResidual K f w).eval β := by
  simp [univariateEval, univariateResidual, eval_sub, eval_mul, eval_X, eval_C]

/-- Completeness: the honest witness makes the residual identically zero. -/
theorem univariateResidual_honest (K : EvalDomain F) (f : F[X]) :
    univariateResidual K f (honestUnivariate K f) = 0 := by
  set r := f %ₘ K.vanishing
  set q := f /ₘ K.vanishing
  have hdecomp : r + K.vanishing * q = f := modByMonic_add_div f K.vanishing
  unfold univariateResidual honestUnivariate
  change f - q * K.vanishing - X * divX r - C (r.coeff 0) = 0
  rw [show f = r + K.vanishing * q from hdecomp.symm]
  rw [mul_comm q, add_sub_cancel_right, sub_sub, X_mul_divX_add, sub_self]

/-- Completeness of the LC check for the honest univariate witness. -/
theorem univariateEval_honest (K : EvalDomain F) (f : F[X]) (β : F) :
    univariateEval K f (honestUnivariate K f) β = 0 := by
  simp [univariateEval_eq, univariateResidual_honest]

/-- On the domain, a zero residual equals the low-degree remainder `X g + σ`. -/
theorem univariate_on_domain {K : EvalDomain F} {f : F[X]} {w : UnivariateWitness F}
    (h : univariateResidual K f w = 0) {κ : F} (hκ : κ ∈ K.elements) :
    f.eval κ = κ * w.g.eval κ + w.σ := by
  have := congrArg (eval κ) h
  simp [univariateResidual, eval_sub, eval_mul, eval_X, eval_C,
    (K.vanishing_eq_zero_iff κ).2 hκ] at this
  rw [sub_sub, sub_eq_zero] at this
  exact this

/-- Domain-sum of a zero-residual polynomial is `|K| · σ`. -/
theorem univariate_sum {K : EvalDomain F} {f : F[X]} {w : UnivariateWitness F}
    (h : univariateResidual K f w = 0)
    (hdeg : (X * w.g + C w.σ).natDegree < K.n) :
    ∑ i ∈ range K.n, f.eval (K.node i) = (K.n : F) * w.σ := by
  have hpt : ∀ i ∈ range K.n, f.eval (K.node i) = (X * w.g + C w.σ).eval (K.node i) := by
    intro i hi
    have hmem : K.node i ∈ K.elements := K.ω_pow_mem i
    have := univariate_on_domain h hmem
    simp [eval_add, eval_mul, eval_X, eval_C, this]
  rw [sum_congr rfl hpt, K.sum_eval_of_natDegree_lt hdeg, coeff_add, coeff_C,
    coeff_X_mul_zero, zero_add, if_pos rfl]

/-- Honest remainder has degree less than the domain size. -/
theorem natDegree_honest_remainder_lt (K : EvalDomain F) (f : F[X]) :
    (X * (honestUnivariate K f).g + C (honestUnivariate K f).σ).natDegree < K.n := by
  have hr : X * (honestUnivariate K f).g + C (honestUnivariate K f).σ =
      f %ₘ K.vanishing := by
    simp [honestUnivariate, X_mul_divX_add]
  rw [hr]
  exact K.natDegree_modByVanishing_lt f

/-- Honest sumcheck recovers the domain-sum as `|K| · σ`. -/
theorem honestUnivariate_sum (K : EvalDomain F) (f : F[X]) :
    ∑ i ∈ range K.n, f.eval (K.node i) = (K.n : F) * (honestUnivariate K f).σ :=
  univariate_sum (univariateResidual_honest K f) (natDegree_honest_remainder_lt K f)

/-- Full assignment polynomial: public interpolant plus `v_X · w`. -/
noncomputable def assignmentPoly (Xdom : EvalDomain F) (xPoly w : F[X]) : F[X] :=
  xPoly + Xdom.vanishing * w

/-- Evaluating the assignment splits into public and `v_X(β) w(β)` as in snarkVM. -/
theorem eval_assignmentPoly (Xdom : EvalDomain F) (xPoly w : F[X]) (β : F) :
    (assignmentPoly Xdom xPoly w).eval β =
      xPoly.eval β + Xdom.vanishing.eval β * w.eval β := by
  simp [assignmentPoly, eval_add, eval_mul]

/-- Soundness at a good challenge for the univariate residual. -/
theorem univariate_sound [DecidableEq F] {K : EvalDomain F} {f : F[X]}
    {w : UnivariateWitness F} {β : F}
    (hne : univariateResidual K f w ≠ 0)
    (hβ : β ∉ szBadSet (univariateResidual K f w)) :
    univariateEval K f w β ≠ 0 := by
  rw [univariateEval_eq]
  exact eval_ne_zero_of_notMem_szBadSet hne hβ

/-- Accepting univariate check yields the domain-sum identity or SZ-break data. -/
theorem univariate_extract [DecidableEq F] {K : EvalDomain F} {f : F[X]}
    {w : UnivariateWitness F} {β : F}
    (hacc : univariateEval K f w β = 0)
    (hnone : inspectResidual (univariateResidual K f w) β = none)
    (hdeg : (X * w.g + C w.σ).natDegree < K.n) :
    ∑ i ∈ range K.n, f.eval (K.node i) = (K.n : F) * w.σ :=
  univariate_sum
    (inspectResidual_accepts (univariateEval_eq K f w β ▸ hacc) hnone) hdeg

/-! ## Matrix / rational sumcheck (`matrix_sumcheck`) -/

/-- `a(X)` in snarkVM: `v_R(α) v_C(β) · row_col_val(X)`. -/
noncomputable def matrixAPoly (H_K : EvalDomain F) (vRC : F) (rowColVal : Nat → F) :
    F[X] :=
  C vRC * valOracle H_K rowColVal

/-- `b(X)` in snarkVM: `|R| |C| (αβ − α col − β row + row_col)`, with the committed
`row_col` (`construct_matrix_linear_combinations`). On `K` it is the product form
`(α − row)(β − col)` scaled (`eval_matrixBPoly`); off `K`, `row_col ≠ row · col`. -/
noncomputable def matrixBPoly (H_R H_C H_K : EvalDomain F) (α β : F)
    (rowIdx colIdx : Nat → Nat) : F[X] :=
  C (H_R.sizeAsField * H_C.sizeAsField) *
    (C (α * β) - C α * colOracle H_C H_K colIdx - C β * rowOracle H_R H_K rowIdx +
      rowColOracle H_R H_C H_K rowIdx colIdx)

/-- Residual of `a − b (X g + σ) = h v_K` (single matrix, selector `= 1`). -/
noncomputable def matrixResidual (K : EvalDomain F) (a b : F[X])
    (g h : F[X]) (σ : F) : F[X] :=
  a - b * (X * g + C σ) - h * K.vanishing

/-- snarkVM `matrix_sumcheck` at `γ` (single matrix, `δ = 1`, selector `= 1`). -/
noncomputable def matrixEval (K : EvalDomain F) (a b g h : F[X]) (σ γ : F) : F :=
  a.eval γ - b.eval γ * (γ * g.eval γ + σ) - h.eval γ * K.vanishing.eval γ

/-- The LC evaluation is the residual at the challenge. -/
theorem matrixEval_eq (K : EvalDomain F) (a b g h : F[X]) (σ γ : F) :
    matrixEval K a b g h σ γ = (matrixResidual K a b g h σ).eval γ := by
  simp [matrixEval, matrixResidual, eval_sub, eval_mul, eval_add, eval_X, eval_C]

/-- On `K`, a zero residual says `a(κ) = b(κ) (κ g(κ) + σ)`. -/
theorem matrix_on_domain {K : EvalDomain F} {a b g h : F[X]} {σ : F}
    (hres : matrixResidual K a b g h σ = 0) {κ : F} (hκ : κ ∈ K.elements) :
    a.eval κ = b.eval κ * (κ * g.eval κ + σ) := by
  have := congrArg (eval κ) hres
  simp [matrixResidual, eval_sub, eval_mul, eval_add, eval_X, eval_C,
    (K.vanishing_eq_zero_iff κ).2 hκ] at this
  exact sub_eq_zero.mp this

/-- When the denominator is nonzero, the rational value equals the remainder. -/
theorem matrix_rational {K : EvalDomain F} {a b g h : F[X]} {σ κ : F}
    (hres : matrixResidual K a b g h σ = 0) (hκ : κ ∈ K.elements)
    (hb : b.eval κ ≠ 0) :
    a.eval κ / b.eval κ = κ * g.eval κ + σ := by
  have := matrix_on_domain hres hκ
  rw [mul_comm] at this
  exact (div_eq_iff hb).2 this

/-- Completeness: if `a − b f` vanishes on `K` and `f` is the honest remainder
`X g + σ`, the residual of the honest quotient is zero. -/
theorem matrixResidual_honest {K : EvalDomain F} {a b f : F[X]}
    (hp : ∀ κ ∈ K.elements, (a - b * f).eval κ = 0)
    (hf : f = X * (honestUnivariate K f).g + C (honestUnivariate K f).σ) :
    matrixResidual K a b (honestUnivariate K f).g
        ((a - b * f) /ₘ K.vanishing) (honestUnivariate K f).σ = 0 := by
  have hdiv := K.vanishing_dvd_of_eval_eq_zero hp
  unfold matrixResidual
  rw [← hf]
  have hmod : (a - b * f) %ₘ K.vanishing = 0 :=
    (modByMonic_eq_zero_iff_dvd K.vanishing_monic).2 hdiv
  have hdecomp := modByMonic_add_div (a - b * f) K.vanishing
  rw [hmod, zero_add, mul_comm] at hdecomp
  exact sub_eq_zero.mpr hdecomp.symm

/-- `a` at a `K`-node is `v_R(α) v_C(β)` times the stored `row_col_val`. -/
theorem eval_matrixAPoly (H_K : EvalDomain F) (vRC : F) (rowColVal : Nat → F)
    {k : Nat} (hk : k < H_K.n) :
    (matrixAPoly H_K vRC rowColVal).eval (H_K.node k) = vRC * rowColVal k := by
  simp [matrixAPoly, eval_mul, eval_C, valOracle_eval _ _ hk]

/-- `b` at a `K`-node is `|R| |C| (α − row) (β − col)`. -/
theorem eval_matrixBPoly (H_R H_C H_K : EvalDomain F) (α β : F)
    (rowIdx colIdx : Nat → Nat) {k : Nat} (hk : k < H_K.n) :
    (matrixBPoly H_R H_C H_K α β rowIdx colIdx).eval (H_K.node k) =
      H_R.sizeAsField * H_C.sizeAsField *
        (α - H_R.node (rowIdx k)) * (β - H_C.node (colIdx k)) := by
  simp only [matrixBPoly, eval_mul, eval_add, eval_sub, eval_C, rowOracle_eval _ _ _ hk,
    colOracle_eval _ _ _ hk, rowColOracle_eval _ _ _ _ _ hk]
  ring

/-- Soundness at a good challenge for the matrix residual. -/
theorem matrix_sound [DecidableEq F] {K : EvalDomain F} {a b g h : F[X]} {σ γ : F}
    (hne : matrixResidual K a b g h σ ≠ 0)
    (hγ : γ ∉ szBadSet (matrixResidual K a b g h σ)) :
    matrixEval K a b g h σ γ ≠ 0 := by
  rw [matrixEval_eq]
  exact eval_ne_zero_of_notMem_szBadSet hne hγ

/-- Accepting matrix check yields the on-`K` rational identity or SZ-break data. -/
theorem matrix_extract [DecidableEq F] {K : EvalDomain F} {a b g h : F[X]} {σ γ κ : F}
    (hacc : matrixEval K a b g h σ γ = 0)
    (hnone : inspectResidual (matrixResidual K a b g h σ) γ = none)
    (hκ : κ ∈ K.elements) :
    a.eval κ = b.eval κ * (κ * g.eval κ + σ) :=
  matrix_on_domain
    (inspectResidual_accepts (matrixEval_eq K a b g h σ γ ▸ hacc) hnone) hκ

/-- The three AHP checks the V2 verifier requires to vanish. -/
structure AHPVerifierChecks (F : Type*) [Field F] where
  /-- `rowcheck_zerocheck` at `α`. -/
  rowcheck : F
  /-- `lineval_sumcheck` at `β`. -/
  lineval : F
  /-- `matrix_sumcheck` at `γ`. -/
  matrix : F

/-- Acceptance is the three LC evaluations being zero. -/
def AHPVerifierChecks.accepts (c : AHPVerifierChecks F) : Prop :=
  c.rowcheck = 0 ∧ c.lineval = 0 ∧ c.matrix = 0

/-- Zero residuals make every challenge an accepting AHP transcript. -/
theorem accepts_of_residuals_zero {H K Cdom : EvalDomain F}
    {zA zB zC h0 f a b : F[X]} {uw : UnivariateWitness F}
    {g h : F[X]} {σ : F} {α β γ : F}
    (hr : rowcheckResidual H zA zB zC h0 = 0)
    (hl : univariateResidual Cdom f uw = 0)
    (hm : matrixResidual K a b g h σ = 0) :
    (⟨rowcheckEval H zA zB zC h0 α,
        univariateEval Cdom f uw β,
        matrixEval K a b g h σ γ⟩ : AHPVerifierChecks F).accepts :=
  ⟨rowcheckEval_eq_zero_of_residual _ _ _ _ _ hr α,
    by simp [univariateEval_eq, hl],
    by simp [matrixEval_eq, hm]⟩

end Varuna