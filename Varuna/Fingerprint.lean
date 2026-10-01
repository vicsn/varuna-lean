/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Fingerprint.Capture
import Varuna.Composition
import Varuna.Field

/-!
# Captured-proof fingerprint

Ironwood ties its Lean verifier to the shipped Rust one with a *fingerprint* :
the Lean-assembled check is compared with the Rust-assembled one on captured
proofs. This is the Varuna counterpart, at the level of the three
zero-evaluation linear combinations that the V2 verifier opens :
`rowcheck_zerocheck`, `lineval_sumcheck`, `matrix_sumcheck`.

`Capture.lean` holds one honest snarkVM V2 hiding-mode proof : each LC's
`(coefficient, value)` terms as snarkVM assembles them, and the independent
inputs (sizes, challenges, sums) the coefficients are built from. The checks :

* **Coefficients agree.** Every coefficient snarkVM computed equals Lean's
  formula applied to the captured inputs (`rowcheck_coeffs`, `lineval_coeffs`,
  `matrix_coeffs`). This covers vanishing polynomials, `K_M.n σ^K_M`, the
  `1 / C.n` batch sum, the selector scale `K_M.n / K.n`, and the four-term `b`.
* **The LCs vanish.** Each captured LC sums to zero (`*_vanishes`), and so does
  Lean's scalar form of it (`*_model`).
* **The scalar forms are the model.** `rowcheckV2Eval_eq_scalar`,
  `linevalEval_eq_scalar`, `matrixTerm_eq_scalar`, and `selector_eval_scalar`
  prove the scalar forms are the definitions `v2_chain` reasons about.

Everything is kernel `decide` over `ZMod q`, the BLS12-377 scalar field : no
`native_decide`, so the census stays standard. The fixture also pins one
modelling fact : at `γ`, `row(γ) col(γ) ≠ row_col(γ)` (`product_form_differs`).
The Lean `matrixBPoly` uses the product, the deployed verifier the committed
`row_col`. They agree on `K`, which is all `matrix_sumcheck_value` needs.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

/-! ## Scalar forms of the zero-evaluation LCs -/

section Scalar

variable {R : Type*} [CommRing R]

/-- `rowcheck_zerocheck` at `α`: `σ_A σ_B − σ_C − h₀(α) v_R(α)`. -/
def rowcheckScalar (vR h0 σA σB σC : R) : R :=
  σA * σB - σC - h0 * vR

/-- `lineval_sumcheck` at `β`, with `ẑ(β) = x̂(β) + v_X(β) ŵ(β)` and constant `σ / C.n`. -/
def linevalScalar (mask τA τB τC ηB ηC x vX w h1 vC β g1 σc : R) : R :=
  mask + (τA + ηB * τB + ηC * τC) * (x + vX * w) - h1 * vC - β * g1 - σc

/-- One matrix's term of `matrix_sumcheck` at `γ`, with the deployed four-term `b`. -/
def matrixTermScalar (vrc rc α β rowColVal col row rowCol g σ γ : R) : R :=
  vrc * rowColVal - rc * (α * β - α * col - β * row + rowCol) * (γ * g + σ)

/-- Value `Σ coeff · value` of a flat LC. -/
def lcValue (ts : List (String × R × R)) : R :=
  (ts.map fun t => t.2.1 * t.2.2).sum

/-- The `(label, coefficient)` pairs of a flat LC. -/
def lcCoeffs (ts : List (String × R × R)) : List (String × R) :=
  ts.map fun t => (t.1, t.2.1)

end Scalar

/-! ## The scalar forms are the model -/

section Link

variable {F : Type*} [Field F]

/-- The V2 rowcheck the chain uses is `rowcheckScalar` at `v_R(α)` and `h₀(α)`. -/
theorem rowcheckV2Eval_eq_scalar (R : EvalDomain F) (h0 : F[X]) (σA σB σC α : F) :
    rowcheckV2Eval R h0 σA σB σC α =
      rowcheckScalar (R.vanishing.eval α) (h0.eval α) σA σB σC :=
  rfl

/-- The V2 lineval LC the chain uses is `linevalScalar`, for the ZK mask and
`ẑ = x̂ + v_X ŵ`. -/
theorem linevalEval_eq_scalar (mask xPoly w h1 g1 : F[X]) (Xd Cd : EvalDomain F)
    (ηB ηC τA τB τC σA σB σC β : F) :
    linevalEval .ZK mask (assignmentPoly Xd xPoly w) Cd ηB ηC τA τB τC
        (linevalWitness Cd h1 g1 ηB ηC σA σB σC) β =
      linevalScalar (mask.eval β) τA τB τC ηB ηC (xPoly.eval β) (Xd.vanishing.eval β) (w.eval β)
        (h1.eval β) (Cd.vanishing.eval β) β (g1.eval β)
        ((σA + ηB * σB + ηC * σC) * Cd.sizeInv) := by
  simp only [linevalEval, linevalWitness, maskPoly, eval_assignmentPoly, linevalScalar]

/-- The matrix term the Lean model uses is `matrixTermScalar` with `row_col := row · col`. -/
theorem matrixTerm_eq_scalar (R Cd K : EvalDomain F) (vRC : F) (rcv : Nat → F) (α β : F)
    (rowIdx colIdx : Nat → Nat) (g : F[X]) (σ γ : F) :
    (matrixAPoly K vRC rcv).eval γ -
        (matrixBPoly R Cd K α β rowIdx colIdx).eval γ * (γ * g.eval γ + σ) =
      matrixTermScalar vRC (R.sizeAsField * Cd.sizeAsField) α β ((valOracle K rcv).eval γ)
        ((colOracle Cd K colIdx).eval γ) ((rowOracle R K rowIdx).eval γ)
        ((rowOracle R K rowIdx).eval γ * (colOracle Cd K colIdx).eval γ) (g.eval γ) σ γ := by
  simp only [matrixAPoly, matrixBPoly, matrixTermScalar, eval_mul, eval_sub, eval_C]
  ring

/-- The selector the model uses is `v_H(γ) H_i.n · (v_{H_i}(γ) H.n)^{-1}`, the
form the fixture checks with an inverse witness. -/
theorem selector_eval_scalar (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) {γ : F}
    (hγ : Hi.vanishing.eval γ ≠ 0) :
    (selectorPoly H Hi).eval γ =
      H.vanishing.eval γ * Hi.sizeAsField * (Hi.vanishing.eval γ * H.sizeAsField)⁻¹ := by
  rw [selectorPoly_eval H Hi hdvd hγ, div_eq_mul_inv]

end Link

/-! ## The captured proof -/

namespace Fingerprint

/-- The captured modulus is the named BLS12-377 scalar prime. -/
theorem q_eq_bls12_377_r : q = bls12_377_r := rfl

/-- `v_R(α) = α^{R.n} − 1`. -/
def vRAtAlpha : Fr := alpha ^ sizeR - 1

/-- `v_C(β)`. -/
def vCAtBeta : Fr := beta ^ sizeC - 1

/-- `v_X(β)`. -/
def vXAtBeta : Fr := beta ^ sizeX - 1

/-- `v_K(γ)`. -/
def vKAtGamma : Fr := gamma ^ sizeK - 1

/-- Fourth-round claim `τ_A = K_A.n σ^K_A`. -/
def tauA : Fr := (sizeKA : Fr) * sum4A

/-- `τ_B`. -/
def tauB : Fr := (sizeKB : Fr) * sum4B

/-- `τ_C`. -/
def tauC : Fr := (sizeKC : Fr) * sum4C

/-- `τ_A + η_B τ_B + η_C τ_C` (with `η_A = 1`). -/
def tauComb : Fr := tauA + etaB * tauB + etaC * tauC

/-- Batch lineval sum `σ = σ_A + η_B σ_B + η_C σ_C`. -/
def sigmaComb : Fr := sigmaA + etaB * sigmaB + etaC * sigmaC

/-- Lean's selector `s_{K,K_A}(γ) = v_K(γ) K_A.n (v_{K_A}(γ) K.n)^{-1}`. -/
def selA : Fr := vKAtGamma * (sizeKA : Fr) * invSeldenA

/-- `s_{K,K_B}(γ)`. -/
def selB : Fr := vKAtGamma * (sizeKB : Fr) * invSeldenB

/-- `s_{K,K_C}(γ)`. -/
def selC : Fr := vKAtGamma * (sizeKC : Fr) * invSeldenC

/-- `v_R(α) v_C(β)`, the `a`-polynomial scale. -/
def vrc : Fr := vRAtAlpha * vCAtBeta

/-- `R.n C.n`, the `b`-polynomial scale. -/
def rc : Fr := (sizeR : Fr) * (sizeC : Fr)

/-- `γ g_A(γ) + σ^K_A`. -/
def bTermA : Fr := gamma * gAAtGamma + sum4A

/-- `γ g_B(γ) + σ^K_B`. -/
def bTermB : Fr := gamma * gBAtGamma + sum4B

/-- `γ g_C(γ) + σ^K_C`. -/
def bTermC : Fr := gamma * gCAtGamma + sum4C

/-! ### Inverse witnesses -/

/-- The captured `1 / C.n` is the inverse of `C.n`. -/
theorem invC_correct : (sizeC : Fr) * invC = 1 := by decide

/-- The captured `(v_{K_A}(γ) K.n)^{-1}` is an inverse. -/
theorem invSeldenA_correct : (gamma ^ sizeKA - 1) * (sizeK : Fr) * invSeldenA = 1 := by decide

/-- The captured `(v_{K_B}(γ) K.n)^{-1}` is an inverse. -/
theorem invSeldenB_correct : (gamma ^ sizeKB - 1) * (sizeK : Fr) * invSeldenB = 1 := by decide

/-- The captured `(v_{K_C}(γ) K.n)^{-1}` is an inverse. -/
theorem invSeldenC_correct : (gamma ^ sizeKC - 1) * (sizeK : Fr) * invSeldenC = 1 := by decide

/-! ### snarkVM's coefficients are Lean's formulas -/

/-- `rowcheck_zerocheck`: `σ_A σ_B − σ_C` on `1`, `−v_R(α)` on `h₀`. -/
theorem rowcheck_coeffs :
    lcCoeffs rowcheckTerms = [("1", sigmaA * sigmaB - sigmaC), ("h_0", -vRAtAlpha)] := by
  decide

/-- `lineval_sumcheck`: the mask on `1`, `τ v_X(β)` on `ŵ`, `−v_C(β)` on `h₁`, and
`τ x̂(β) − β g₁(β) − σ / C.n` on `1`. -/
theorem lineval_coeffs :
    lcCoeffs linevalTerms =
      [("1", tauComb * xAtBeta - beta * g1AtBeta - sigmaComb * invC),
        ("w_00000000", tauComb * vXAtBeta), ("h_1", -vCAtBeta), ("mask_poly", 1)] := by
  decide

/-- `matrix_sumcheck`: per matrix `δ_M s_M` times `v_R v_C` on `row_col_val`,
`R.n C.n (α col + β row − row_col − αβ) (γ g + σ)`, and `−v_K(γ)` on `h₂`. -/
theorem matrix_coeffs :
    lcCoeffs matrixTerms =
      [("1", -(deltaA * selA * rc * alpha * beta * bTermA) -
          deltaB * selB * rc * alpha * beta * bTermB - deltaC * selC * rc * alpha * beta * bTermC),
        ("col_a", deltaA * selA * rc * alpha * bTermA),
        ("col_b", deltaB * selB * rc * alpha * bTermB),
        ("col_c", deltaC * selC * rc * alpha * bTermC),
        ("row_a", deltaA * selA * rc * beta * bTermA),
        ("row_b", deltaB * selB * rc * beta * bTermB),
        ("row_c", deltaC * selC * rc * beta * bTermC),
        ("row_col_a", -(deltaA * selA * rc * bTermA)),
        ("row_col_b", -(deltaB * selB * rc * bTermB)),
        ("row_col_c", -(deltaC * selC * rc * bTermC)),
        ("row_col_val_a", deltaA * selA * vrc),
        ("row_col_val_b", deltaB * selB * vrc),
        ("row_col_val_c", deltaC * selC * vrc),
        ("h_2", -vKAtGamma)] := by
  decide

/-! ### The LCs vanish on the captured proof -/

/-- The captured `rowcheck_zerocheck` sums to zero. -/
theorem rowcheck_vanishes : lcValue rowcheckTerms = 0 := by decide

/-- The captured `lineval_sumcheck` sums to zero. -/
theorem lineval_vanishes : lcValue linevalTerms = 0 := by decide

/-- The captured `matrix_sumcheck` sums to zero. -/
theorem matrix_vanishes : lcValue matrixTerms = 0 := by decide

/-- Lean's rowcheck, on the captured values, vanishes. -/
theorem rowcheck_model : rowcheckScalar vRAtAlpha h0AtAlpha sigmaA sigmaB sigmaC = 0 := by
  decide

/-- Lean's lineval LC, on the captured values, vanishes. -/
theorem lineval_model :
    linevalScalar maskAtBeta tauA tauB tauC etaB etaC xAtBeta vXAtBeta wAtBeta h1AtBeta vCAtBeta
        beta g1AtBeta (sigmaComb * invC) = 0 := by
  decide

/-- Lean's batched matrix LC (deployed `b`, Lean selectors), on the captured values, vanishes. -/
theorem matrix_model :
    deltaA * selA * matrixTermScalar vrc rc alpha beta rowColValAAtGamma colAAtGamma rowAAtGamma
          rowColAAtGamma gAAtGamma sum4A gamma +
        deltaB * selB * matrixTermScalar vrc rc alpha beta rowColValBAtGamma colBAtGamma
          rowBAtGamma rowColBAtGamma gBAtGamma sum4B gamma +
        deltaC * selC * matrixTermScalar vrc rc alpha beta rowColValCAtGamma colCAtGamma
          rowCAtGamma rowColCAtGamma gCAtGamma sum4C gamma -
      h2AtGamma * vKAtGamma = 0 := by
  decide

/-! ### Pinned facts -/

/-- First-circuit `δ_A = 1`, as `DeltaCombiners.first` models. -/
theorem deltaA_eq_one : deltaA = 1 := by decide

/-- `K_A.n = K.n`, so `s_{K,K_A}(γ) = 1`. -/
theorem selA_eq_one : selA = 1 := by decide

/-- `K_B.n < K.n`, so `s_{K,K_B}(γ) ≠ 1`: the selector scale is exercised. -/
theorem selB_ne_one : selB ≠ 1 := by decide

/-- Off `K`, the product of the row and column oracles is not the committed
`row_col` : the Lean `matrixBPoly` and the deployed `b` differ at `γ`. -/
theorem product_form_differs : rowAAtGamma * colAAtGamma ≠ rowColAAtGamma := by decide

/-- Negative control: changing `h₀(α)` by one breaks the rowcheck. -/
theorem rowcheck_rejects_tampered :
    rowcheckScalar vRAtAlpha (h0AtAlpha + 1) sigmaA sigmaB sigmaC ≠ 0 := by
  decide

/-- Negative control: changing `ŵ(β)` by one breaks the lineval LC. -/
theorem lineval_rejects_tampered :
    linevalScalar maskAtBeta tauA tauB tauC etaB etaC xAtBeta vXAtBeta (wAtBeta + 1) h1AtBeta
        vCAtBeta beta g1AtBeta (sigmaComb * invC) ≠ 0 := by
  decide

end Fingerprint

end Varuna