/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Lineval

/-!
# Honest-verifier simulator, query bound 1

ZK mode adds `mask_poly` to the lineval polynomial and hides the
commitments (`random_v`). This file is the AHP half. Commitment hiding
stays a floor : the verifier's openings are field elements, and the
simulator programs those.

The verifier opens a masked polynomial at one challenge outside the
domain. `maskAt` is the constant mask that sends that opening to any
chosen field element and leaves every domain value unchanged.
`simulateRowcheck` then makes the rowcheck accept at that challenge.

The lineval polynomial is affine in the witness. `simulateLineval`
builds it from the public input alone. `simulateLineval_eq_real` moves
a real witness into the mask, so the lineval polynomial and its honest
sumcheck witness equal the public-input simulation. In non-ZK mode the
mask is ignored, and that move is not available.
-/

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- A polynomial plus a multiple of `v_H`. On `H` the multiple vanishes. -/
noncomputable def masked (H : EvalDomain F) (p r : F[X]) : F[X] :=
  p + H.vanishing * r

/-- Constant mask sending `p(α)` to `target` when `α ∉ H`. Degree `< 1`. -/
noncomputable def maskAt (H : EvalDomain F) (p : F[X]) (α target : F) : F[X] :=
  C ((target - p.eval α) * (H.vanishing.eval α)⁻¹)

/-- Masking does not change values on the domain. -/
theorem masked_agrees_on_domain (H : EvalDomain F) (p r : F[X]) {x : F}
    (hx : x ∈ H.elements) : (masked H p r).eval x = p.eval x := by
  simp [masked, eval_add, eval_mul, (H.vanishing_eq_zero_iff x).2 hx]

/-- One query outside `H` can be programmed to any field element. -/
theorem masked_eval_at_query (H : EvalDomain F) (p : F[X]) (α target : F)
    (hα : H.vanishing.eval α ≠ 0) :
    (masked H p (maskAt H p α target)).eval α = target := by
  unfold masked maskAt
  rw [eval_add, eval_mul, eval_C]
  field_simp [hα]
  ring

/-- Masking `z_A` leaves the rowcheck numerator unchanged on `H`. -/
theorem rowcheckPoly_mask_on_domain (H : EvalDomain F) (zA zB zC r : F[X]) {x : F}
    (hx : x ∈ H.elements) :
    (rowcheckPoly (masked H zA r) zB zC).eval x = (rowcheckPoly zA zB zC).eval x := by
  simp [rowcheckPoly, masked_agrees_on_domain H zA r hx, eval_mul, eval_sub]

/-- Quotient that makes the rowcheck accept at a known `α ∉ H`. -/
noncomputable def simulateRowcheck (H : EvalDomain F) (zA zB zC : F[X]) (α : F) : F[X] :=
  C ((rowcheckPoly zA zB zC).eval α * (H.vanishing.eval α)⁻¹)

/-- The simulated rowcheck passes at the challenge the simulator was given. -/
theorem simulateRowcheck_accepts (H : EvalDomain F) (zA zB zC : F[X]) (α : F)
    (hα : H.vanishing.eval α ≠ 0) :
    rowcheckEval H zA zB zC (simulateRowcheck H zA zB zC α) α = 0 := by
  unfold rowcheckEval simulateRowcheck rowcheckPoly
  simp only [eval_sub, eval_mul, eval_C]
  rw [mul_assoc, inv_mul_cancel₀ hα, mul_one, sub_self]

/-- Weighted matrix combination in the V3 lineval polynomial. -/
noncomputable def linPoly (mA mB mC : F[X]) (ηA ηB ηC : F) : F[X] :=
  C ηA * mA + C ηB * mB + C ηC * mC

/-- In ZK mode the mask is the polynomial itself. -/
@[simp] theorem maskPoly_ZK (mask : F[X]) : maskPoly .ZK mask = mask :=
  rfl

/-- In non-ZK mode every mask is dropped, so a witness cannot be moved into it. -/
theorem linevalPolyEta_nonZK_ignores_mask (mask z mA mB mC : F[X]) (ηA ηB ηC : F) :
    linevalPolyEta .NonZK mask z mA mB mC ηA ηB ηC =
      linevalPolyEta .NonZK 0 z mA mB mC ηA ηB ηC := by
  simp [linevalPolyEta, maskPoly]

/-- Moving `zReal − zSim` into the ZK mask leaves the lineval polynomial fixed. -/
theorem linevalPolyEta_absorb (mask zSim zReal mA mB mC : F[X]) (ηA ηB ηC : F) :
    linevalPolyEta .ZK (mask + linPoly mA mB mC ηA ηB ηC * (zReal - zSim))
        zSim mA mB mC ηA ηB ηC =
      linevalPolyEta .ZK mask zReal mA mB mC ηA ηB ηC := by
  simp only [linevalPolyEta, maskPoly_ZK, linPoly]
  ring

/-- The witness part of an assignment is `v_X · w`. -/
theorem assignmentPoly_witness_delta (X : EvalDomain F) (xPoly w : F[X]) :
    assignmentPoly X xPoly w - assignmentPoly X xPoly 0 = X.vanishing * w := by
  simp only [assignmentPoly, mul_zero, add_zero]
  ring

/-- Lineval polynomial of the public input and a mask. No witness. -/
noncomputable def simulateLineval (X : EvalDomain F) (xPoly mask mA mB mC : F[X])
    (ηA ηB ηC : F) : F[X] :=
  linevalPolyEta .ZK mask (assignmentPoly X xPoly 0) mA mB mC ηA ηB ηC

/-- A real witness's lineval polynomial is the public-input simulation
under the mask that absorbs `v_X · w`. -/
theorem simulateLineval_eq_real (X : EvalDomain F) (xPoly mask mA mB mC : F[X])
    (ηA ηB ηC : F) (w : F[X]) :
    simulateLineval X xPoly
        (mask + linPoly mA mB mC ηA ηB ηC *
          (assignmentPoly X xPoly w - assignmentPoly X xPoly 0))
        mA mB mC ηA ηB ηC =
      linevalPolyEta .ZK mask (assignmentPoly X xPoly w) mA mB mC ηA ηB ηC := by
  simpa [simulateLineval] using
    linevalPolyEta_absorb mask (assignmentPoly X xPoly 0) (assignmentPoly X xPoly w)
      mA mB mC ηA ηB ηC

/-- The honest sumcheck witness depends only on the lineval polynomial,
so the simulated and real witnesses agree. -/
theorem simulateLineval_witness (Cd X : EvalDomain F) (xPoly mask mA mB mC : F[X])
    (ηA ηB ηC : F) (w : F[X]) :
    honestUnivariate Cd (simulateLineval X xPoly
        (mask + linPoly mA mB mC ηA ηB ηC *
          (assignmentPoly X xPoly w - assignmentPoly X xPoly 0))
        mA mB mC ηA ηB ηC) =
      honestUnivariate Cd
        (linevalPolyEta .ZK mask (assignmentPoly X xPoly w) mA mB mC ηA ηB ηC) := by
  rw [simulateLineval_eq_real]

/-- The simulated lineval sumcheck accepts at every challenge. -/
theorem simulateLineval_accepts (Cd X : EvalDomain F) (xPoly mask mA mB mC : F[X])
    (ηA ηB ηC β : F) :
    univariateEval Cd (simulateLineval X xPoly mask mA mB mC ηA ηB ηC)
      (honestUnivariate Cd (simulateLineval X xPoly mask mA mB mC ηA ηB ηC)) β = 0 :=
  univariateEval_honest _ _ _

end Varuna