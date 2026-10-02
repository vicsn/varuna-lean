/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Fingerprint.Capture
import Varuna.AHP
import Varuna.Selectors
import Varuna.Field

/-!
# Captured-proof fingerprint

Ironwood ties its Lean verifier to the shipped Rust one with a *fingerprint* :
the Lean-assembled check is compared with the Rust-assembled one on captured
proofs. This is the Varuna counterpart, at the level of the three
zero-evaluation linear combinations that the V3 verifier opens :
`rowcheck_zerocheck`, `lineval_sumcheck`, `matrix_sumcheck`.

`Capture.lean` holds one honest snarkVM V3 hiding-mode batch proof over two
circuits, `c0` and `c1`, with two instances each (`batch_shape`) : each LC's
`(coefficient, value)` terms as snarkVM assembles them, and the independent
inputs (sizes, challenges, combiners, sums) the coefficients are built from.
The circuits differ on every domain, so the circuit and instance combiners,
the selectors at `α`, `β`, and `γ`, the per-circuit `δ`s, and the per-circuit
`v_X(β)` all enter. The checks :

* **Coefficients agree.** Every coefficient snarkVM computed equals Lean's
  formula applied to the captured inputs (`rowcheck_coeffs`, `lineval_coeffs`,
  `matrix_coeffs`). Circuits and instances are combined with `weightedSum`,
  the combination the batching theorems use.
* **The LCs vanish.** Each captured LC sums to zero (`*_vanishes`), and so does
  Lean's scalar form of it (`*_model`).
* **The scalar forms are the model.** `eval_selectorBatch` is the batched
  zerocheck and batched sums at a point, `selector_eval_scalar` the selector
  values, `eval_assignmentPoly` the per-instance `ẑ(β) = x̂(β) + v_X(β) ŵ(β)`,
  and `matrixTerm_eq_scalar` each matrix term.

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

/-- A selector-lifted combination `Σ_i w_i s_{H,H_i} P_i` evaluates at `x` to
`Σ_i w_i s_{H,H_i}(x) P_i(x)`. This is `batchedZerocheck` at `α` and the
batched sums of `batchedSumcheck_extract` at `β` and `γ`. -/
theorem eval_selectorBatch (H : EvalDomain F) (ws : List F) (ps : List (EvalDomain F × F[X]))
    (x : F) :
    (weightedSumPoly ws (ps.map fun p => selectorPoly H p.1 * p.2)).eval x =
      weightedSum ws (ps.map fun p => (selectorPoly H p.1).eval x * p.2.eval x) := by
  rw [eval_weightedSumPoly, List.map_map]
  simp only [Function.comp_def, eval_mul]

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

/-- `v_R(α)` on the batch constraint domain. -/
def vRAtAlpha : Fr := alpha ^ sizeR - 1

/-- `v_C(β)` on the batch variable domain. -/
def vCAtBeta : Fr := beta ^ sizeC - 1

/-- `v_K(γ)` on the batch nonzero domain. -/
def vKAtGamma : Fr := gamma ^ sizeK - 1

/-! ### One instance -/

namespace CapturedInstance

/-- Rowcheck claim `σ_A σ_B − σ_C`. -/
def rowClaim (i : CapturedInstance) : Fr := i.sigmaA * i.sigmaB - i.sigmaC

/-- Lineval claim `η_A σ_A + η_B σ_B + η_C σ_C`. -/
def linClaim (i : CapturedInstance) : Fr := etaA * i.sigmaA + etaB * i.sigmaB + etaC * i.sigmaC

end CapturedInstance

/-! ### One circuit -/

namespace CapturedCircuit

variable (c : CapturedCircuit)

/-- `v_{R_i}(α)` on the circuit's constraint domain. -/
def vR : Fr := alpha ^ c.sizeR - 1

/-- `v_{C_i}(β)` on the circuit's variable domain. -/
def vC : Fr := beta ^ c.sizeC - 1

/-- `v_{X_i}(β)` on the circuit's input domain. -/
def vX : Fr := beta ^ c.sizeX - 1

/-- Lean's selector `s_{R,R_i}(α) = v_R(α) R_i.n (v_{R_i}(α) R.n)^{-1}`. -/
def selR : Fr := vRAtAlpha * (c.sizeR : Fr) * c.invSeldenR

/-- `s_{C,C_i}(β)`. -/
def selC : Fr := vCAtBeta * (c.sizeC : Fr) * c.invSeldenC

/-- `s_{K,K_A}(γ)`. -/
def selKA : Fr := vKAtGamma * (c.sizeKA : Fr) * c.invSeldenKA

/-- `s_{K,K_B}(γ)`. -/
def selKB : Fr := vKAtGamma * (c.sizeKB : Fr) * c.invSeldenKB

/-- `s_{K,K_C}(γ)`. -/
def selKC : Fr := vKAtGamma * (c.sizeKC : Fr) * c.invSeldenKC

/-- Fourth-round claim `τ_A = K_A.n σ^K_A`. -/
def tauA : Fr := (c.sizeKA : Fr) * c.sum4A

/-- `τ_B`. -/
def tauB : Fr := (c.sizeKB : Fr) * c.sum4B

/-- `τ_C`. -/
def tauC : Fr := (c.sizeKC : Fr) * c.sum4C

/-- `η_A τ_A + η_B τ_B + η_C τ_C`. -/
def tauComb : Fr := etaA * c.tauA + etaB * c.tauB + etaC * c.tauC

/-- `v_{R_i}(α) v_{C_i}(β)`, the `a`-polynomial scale. -/
def vrc : Fr := c.vR * c.vC

/-- `R_i.n C_i.n`, the `b`-polynomial scale. -/
def rc : Fr := (c.sizeR : Fr) * (c.sizeC : Fr)

/-- Matrix `A`'s weight on the `b` terms: `δ_A s_{K,K_A}(γ) R_i.n C_i.n (γ g_A(γ) + σ^K_A)`. -/
def bWeightA : Fr := c.deltaA * c.selKA * c.rc * (gamma * c.gAAtGamma + c.sum4A)

/-- Matrix `B`'s weight on the `b` terms. -/
def bWeightB : Fr := c.deltaB * c.selKB * c.rc * (gamma * c.gBAtGamma + c.sum4B)

/-- Matrix `C`'s weight on the `b` terms. -/
def bWeightC : Fr := c.deltaC * c.selKC * c.rc * (gamma * c.gCAtGamma + c.sum4C)

/-- First-round instance combination `Σ_j τ_{i,j} (σ_A σ_B − σ_C)_{i,j}`. -/
def rowInstances : Fr :=
  weightedSum (c.instances.map (·.combiner1)) (c.instances.map (·.rowClaim))

/-- Third-round instance combination `Σ_j τ_{i,j} x̂_{i,j}(β)`. -/
def xInstances : Fr :=
  weightedSum (c.instances.map (·.combiner3)) (c.instances.map (·.xAtBeta))

/-- Third-round instance combination `Σ_j τ_{i,j} ẑ_{i,j}(β)`, with
`ẑ(β) = x̂(β) + v_{X_i}(β) ŵ(β)` as in `eval_assignmentPoly`. -/
def zInstances : Fr :=
  weightedSum (c.instances.map (·.combiner3))
    (c.instances.map fun i => i.xAtBeta + c.vX * i.wAtBeta)

/-- Third-round instance combination `Σ_j τ_{i,j} (η_A σ_A + η_B σ_B + η_C σ_C)_{i,j}`. -/
def linInstances : Fr :=
  weightedSum (c.instances.map (·.combiner3)) (c.instances.map (·.linClaim))

/-- Coefficient on instance `i`'s `ŵ` : `ν_c s_{C,C_c}(β) τ_i (η·τ_c) v_{X_c}(β)`. -/
def wCoeff (i : CapturedInstance) : Fr :=
  c.combiner3 * c.selC * i.combiner3 * c.tauComb * c.vX

/-- Lean's `δ`-combination of the circuit's three selector-scaled matrix terms. -/
def matrixComb : Fr :=
  weightedSum [c.deltaA, c.deltaB, c.deltaC]
    [c.selKA * matrixTermScalar c.vrc c.rc alpha beta c.rowColValAAtGamma c.colAAtGamma
        c.rowAAtGamma c.rowColAAtGamma c.gAAtGamma c.sum4A gamma,
      c.selKB * matrixTermScalar c.vrc c.rc alpha beta c.rowColValBAtGamma c.colBAtGamma
        c.rowBAtGamma c.rowColBAtGamma c.gBAtGamma c.sum4B gamma,
      c.selKC * matrixTermScalar c.vrc c.rc alpha beta c.rowColValCAtGamma c.colCAtGamma
        c.rowCAtGamma c.rowColCAtGamma c.gCAtGamma c.sum4C gamma]

end CapturedCircuit

/-! ### The batch -/

/-- `rowcheck_zerocheck`'s constant `Σ_i ν_i s_{R,R_i}(α) Σ_j τ_{i,j} (σ_A σ_B − σ_C)_{i,j}`,
with first-round combiners. -/
def rowcheckOne (cs : List CapturedCircuit) : Fr :=
  weightedSum (cs.map (·.combiner1)) (cs.map fun c => c.selR * c.rowInstances)

/-- Batch lineval sum `σ = Σ_i ν_i Σ_j τ_{i,j} (η_A σ_A + η_B σ_B + η_C σ_C)_{i,j}`. -/
def sigmaBatch (cs : List CapturedCircuit) : Fr :=
  weightedSum (cs.map (·.combiner3)) (cs.map (·.linInstances))

/-- `lineval_sumcheck`'s constant
`Σ_i ν_i s_{C,C_i}(β) (η·τ_i) Σ_j τ_{i,j} x̂_{i,j}(β) − β g₁(β) − σ / C.n`. -/
def linevalOne (cs : List CapturedCircuit) : Fr :=
  weightedSum (cs.map (·.combiner3)) (cs.map fun c => c.selC * c.tauComb * c.xInstances) -
    beta * g1AtBeta - sigmaBatch cs * invC

/-- Lean's batched rowcheck at `α` : the constant minus `h₀(α) v_R(α)`. -/
def rowcheckModel (cs : List CapturedCircuit) : Fr :=
  rowcheckOne cs - h0AtAlpha * vRAtAlpha

/-- Lean's batched lineval at `β`, with `ẑ = x̂ + v_X ŵ` for every instance. -/
def linevalModel (cs : List CapturedCircuit) : Fr :=
  maskAtBeta + weightedSum (cs.map (·.combiner3)) (cs.map fun c =>
    c.selC * c.tauComb * c.zInstances) -
    h1AtBeta * vCAtBeta - beta * g1AtBeta - sigmaBatch cs * invC

/-- Lean's batched matrix check at `γ` : every circuit's `δ`-combination, minus `h₂(γ) v_K(γ)`. -/
def matrixModel (cs : List CapturedCircuit) : Fr :=
  (cs.map (·.matrixComb)).sum - h2AtGamma * vKAtGamma

/-- Two circuits with two instances each. -/
theorem batch_shape : circuits.map (·.instances.length) = [2, 2] := by decide

/-! ### Inverse witnesses -/

/-- The captured `1 / C.n` is the inverse of `C.n`. -/
theorem invC_correct : (sizeC : Fr) * invC = 1 := by decide

/-- Every captured selector denominator inverse is an inverse : `(v_{R_i}(α) R.n)^{-1}`,
`(v_{C_i}(β) C.n)^{-1}`, and `(v_{K_M}(γ) K.n)^{-1}` for each circuit. -/
theorem invSelden_correct :
    ∀ c ∈ circuits,
      c.vR * (sizeR : Fr) * c.invSeldenR = 1 ∧ c.vC * (sizeC : Fr) * c.invSeldenC = 1 ∧
        (gamma ^ c.sizeKA - 1) * (sizeK : Fr) * c.invSeldenKA = 1 ∧
        (gamma ^ c.sizeKB - 1) * (sizeK : Fr) * c.invSeldenKB = 1 ∧
        (gamma ^ c.sizeKC - 1) * (sizeK : Fr) * c.invSeldenKC = 1 := by
  decide

/-! ### snarkVM's coefficients are Lean's formulas -/

/-- `rowcheck_zerocheck` : the batched constant on `1`, `−v_R(α)` on `h₀`. -/
theorem rowcheck_coeffs :
    lcCoeffs rowcheckTerms = [("1", rowcheckOne circuits), ("h_0", -vRAtAlpha)] := by
  decide

/-- `lineval_sumcheck` : the batched constant on `1`, one `ŵ` per circuit and
instance, `−v_C(β)` on `h₁`, and the mask. -/
theorem lineval_coeffs :
    lcCoeffs linevalTerms =
      [("1", linevalOne circuits),
        ("c0_w_00000000", c0.wCoeff c0i0), ("c0_w_00000001", c0.wCoeff c0i1),
        ("c1_w_00000000", c1.wCoeff c1i0), ("c1_w_00000001", c1.wCoeff c1i1),
        ("h_1", -vCAtBeta), ("mask_poly", 1)] := by
  decide

/-- `matrix_sumcheck` : per circuit and matrix, `δ s v_{R_i}(α) v_{C_i}(β)` on
`row_col_val`, and the `b` weight times `α col + β row − row_col − αβ`;
`−v_K(γ)` on `h₂`. -/
theorem matrix_coeffs :
    lcCoeffs matrixTerms =
      [("1", -(alpha * beta * (c0.bWeightA + c0.bWeightB + c0.bWeightC +
          c1.bWeightA + c1.bWeightB + c1.bWeightC))),
        ("c0_col_a", alpha * c0.bWeightA), ("c0_col_b", alpha * c0.bWeightB),
        ("c0_col_c", alpha * c0.bWeightC),
        ("c0_row_a", beta * c0.bWeightA), ("c0_row_b", beta * c0.bWeightB),
        ("c0_row_c", beta * c0.bWeightC),
        ("c0_row_col_a", -c0.bWeightA), ("c0_row_col_b", -c0.bWeightB),
        ("c0_row_col_c", -c0.bWeightC),
        ("c0_row_col_val_a", c0.deltaA * c0.selKA * c0.vrc),
        ("c0_row_col_val_b", c0.deltaB * c0.selKB * c0.vrc),
        ("c0_row_col_val_c", c0.deltaC * c0.selKC * c0.vrc),
        ("c1_col_a", alpha * c1.bWeightA), ("c1_col_b", alpha * c1.bWeightB),
        ("c1_col_c", alpha * c1.bWeightC),
        ("c1_row_a", beta * c1.bWeightA), ("c1_row_b", beta * c1.bWeightB),
        ("c1_row_c", beta * c1.bWeightC),
        ("c1_row_col_a", -c1.bWeightA), ("c1_row_col_b", -c1.bWeightB),
        ("c1_row_col_c", -c1.bWeightC),
        ("c1_row_col_val_a", c1.deltaA * c1.selKA * c1.vrc),
        ("c1_row_col_val_b", c1.deltaB * c1.selKB * c1.vrc),
        ("c1_row_col_val_c", c1.deltaC * c1.selKC * c1.vrc),
        ("h_2", -vKAtGamma)] := by
  decide

/-! ### The LCs vanish on the captured proof -/

/-- The captured `rowcheck_zerocheck` sums to zero. -/
theorem rowcheck_vanishes : lcValue rowcheckTerms = 0 := by decide

/-- The captured `lineval_sumcheck` sums to zero. -/
theorem lineval_vanishes : lcValue linevalTerms = 0 := by decide

/-- The captured `matrix_sumcheck` sums to zero. -/
theorem matrix_vanishes : lcValue matrixTerms = 0 := by decide

/-- Lean's batched rowcheck, on the captured values, vanishes. -/
theorem rowcheck_model : rowcheckModel circuits = 0 := by decide

/-- Lean's batched lineval, on the captured values, vanishes. -/
theorem lineval_model : linevalModel circuits = 0 := by decide

/-- Lean's batched matrix check (deployed `b`, Lean selectors), on the captured
values, vanishes. -/
theorem matrix_model : matrixModel circuits = 0 := by decide

/-! ### Pinned facts -/

/-- The first combiner of each family is `1`, as `circuitCombiners`,
`instanceCombiners`, and `DeltaCombiners.first` model : `c0`'s circuit
combiners and `δ_A`, and each circuit's first instance combiners. -/
theorem first_combiners_eq_one :
    c0.combiner1 = 1 ∧ c0.combiner3 = 1 ∧ c0.deltaA = 1 ∧
      ∀ c ∈ circuits, ∀ i ∈ c.instances.head?, i.combiner1 = 1 ∧ i.combiner3 = 1 := by
  decide

/-- The other combiners are squeezed, and the third-round combiners are fresh
squeezes rather than the first-round ones. -/
theorem later_combiners_squeezed :
    c1.combiner1 ≠ 1 ∧ c1.combiner3 ≠ 1 ∧ c1.deltaA ≠ 1 ∧ c1.combiner3 ≠ c1.combiner1 ∧
      ∀ c ∈ circuits, ∀ i ∈ c.instances.tail,
        i.combiner1 ≠ 1 ∧ i.combiner3 ≠ 1 ∧ i.combiner3 ≠ i.combiner1 := by
  decide

/-- `c0` spans the batch domains `R`, `C`, and `K` (selectors `1`). `c1` is
smaller on all three, and `c0`'s `K_B` is smaller than `K`, so the selector
scale is exercised at `α`, `β`, and `γ`. -/
theorem selectors_scaled :
    c0.selR = 1 ∧ c0.selC = 1 ∧ c0.selKA = 1 ∧
      c0.selKB ≠ 1 ∧ c1.selR ≠ 1 ∧ c1.selC ≠ 1 ∧ c1.selKA ≠ 1 := by
  decide

/-- The circuits have different input domains, so `v_X(β)` is per circuit. -/
theorem input_domains_differ : c0.vX ≠ c1.vX := by decide

/-- Off `K`, the product of the row and column oracles is not the committed
`row_col` : the Lean `matrixBPoly` and the deployed `b` differ at `γ`. -/
theorem product_form_differs :
    ∀ c ∈ circuits, c.rowAAtGamma * c.colAAtGamma ≠ c.rowColAAtGamma := by
  decide

/-- The captured `η_A` is a squeezed challenge, not the V2 constant `1`. -/
theorem etaA_ne_one : etaA ≠ 1 := by decide

/-- Negative control : changing `σ_C` of `c1`'s second instance by one breaks
the rowcheck. -/
theorem rowcheck_rejects_tampered :
    rowcheckModel [c0, { c1 with instances := [c1i0, { c1i1 with sigmaC := c1i1.sigmaC + 1 }] }] ≠
      0 := by
  decide

/-- Negative control : changing `ŵ(β)` of `c1`'s second instance by one breaks
the lineval check. -/
theorem lineval_rejects_tampered :
    linevalModel [c0, { c1 with instances := [c1i0, { c1i1 with wAtBeta :=
      c1i1.wAtBeta + 1 }] }] ≠
      0 := by
  decide

end Fingerprint

end Varuna