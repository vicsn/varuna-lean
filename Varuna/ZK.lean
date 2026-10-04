/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Algebraic
import Varuna.Lineval
import Mathlib.Data.Fintype.Pi

/-!
# Honest-verifier simulator

Query bound 1 is the constant mask `maskAt`. Query bound `n` is
`maskedAnswers_bijective` : degree-`< n` masks, at `n` distinct points
outside the domain, hit every answer tuple once. `card_zkProof` counts
masks of a whole view (those answers, the lineval polynomial and its
value at `β`, a shared rowcheck value, a matrix message that does not
read the witness, and the constant blinding). The lineval polynomials
match after a mask translation when `lin · (zReal − zSim)` has degree
less than the lineval mask. The raw opening `w(β)` is not in the view,
and the rowcheck value is not the quotient `h₀(α)`.

ZK mode adds `mask_poly` to the lineval polynomial and hides the
commitments (`random_v`). This file is the AHP half. A constant blinding
shifts the hiding commitment along `gamma_g`. The simulator opens
`simulateLineval` with that blinding. A fresh algebraic opening is a
trapdoor break or the represented polynomial's value.

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

/-- The simulator's hiding opening of the masked lineval checks. -/
theorem simulateHidingLineval_accepts {G1 G2 GT : Type*} [AddCommGroup G1] [AddCommGroup G2]
    [AddCommGroup GT] [Module F G1] [Module F G2] [Module F GT]
    (e : Pairing F G1 G2 GT) (vk : HidingKey G1 G2) {β : F} (hwf : vk.wellFormed β)
    (X : EvalDomain F) (xPoly mask mA mB mC blind : F[X]) (ηA ηB ηC z : F) :
    kzgCheckHiding e vk
      (kzgCommitHiding vk β (simulateLineval X xPoly mask mA mB mC ηA ηB ηC) blind) (blind.eval z)
      (honestHidingOpening vk β (simulateLineval X xPoly mask mA mB mC ηA ηB ηC) blind z) :=
  kzgCheckHiding_honest e vk hwf _ _ _

/-- Simulation extractability of one hiding opening. The simulator's lineval
opening checks. A fresh algebraic opening of a different polynomial is a
trapdoor break or the represented value. -/
theorem simulation_extractable [DecidableEq F] {G1 G2 GT : Type*} [AddCommGroup G1]
    [AddCommGroup G2] [AddCommGroup GT] [Module F G1] [Module F G2] [Module F GT]
    (e : Pairing F G1 G2 GT) (vk : HidingKey G1 G2) {τ : F} (hwf : vk.wellFormed τ)
    (hind : pairingIndependent e vk) (X : EvalDomain F)
    (xPoly mask mA mB mC blind : F[X]) (ηA ηB ηC z : F) (p r q s : List F) {C : G1}
    {randomV : F} (o : Opening G1 F)
    (hC : C = represent vk.g τ p + represent vk.gammaG τ r)
    (hw : o.witness = represent vk.g τ q + represent vk.gammaG τ s)
    (hc : kzgCheckHiding e vk C randomV o)
    (hfresh : toPoly p ≠ simulateLineval X xPoly mask mA mB mC ηA ηB ηC) :
    kzgCheckHiding e vk
        (kzgCommitHiding vk τ (simulateLineval X xPoly mask mA mB mC ηA ηB ηC) blind)
        (blind.eval z)
        (honestHidingOpening vk τ (simulateLineval X xPoly mask mA mB mC ηA ηB ηC) blind z) ∧
      ((∃ b, inspectOpening p q o.point o.value = some b ∧ b.holds τ) ∨
        o.value = (toPoly p).eval o.point) ∧
      toPoly p ≠ simulateLineval X xPoly mask mA mB mC ηA ηB ηC :=
  ⟨kzgCheckHiding_honest e vk hwf _ _ _,
    hidingOpening_extract e vk hwf hind p r q s o hC hw hc, hfresh⟩

/-! ## Query bound `n`, and the same number of masks

`coeffPoly` is a mask of degree less than `n`. At `n` distinct queries
outside the domain, every answer tuple arises from exactly one such mask
(`maskedAnswers_bijective`). Translating coefficients by the Lagrange
interpolant of `p(q) / v_H(q)` sends the answers of `masked p` to the
answers of `masked 0`. On a finite field that translation is a bijection of
the mask space, so every predicate on the answers has the same number of
preimages (`card_maskedAnswers`).

The lineval mask absorbs `lin · (zReal − zSim)` when that product has
degree less than the mask length. The simulator's view — query answers,
the lineval polynomial and its value at `β`, the rowcheck value, a matrix
message that does not read the witness, and the constant blinding — then
agrees with the real view after one translation of the two masks. The
blinding is not translated : equal polynomials and the same `ρ` are the
same hiding commitment. The raw opening `w(β)` is not part of this view.
-/

/-- A mask whose coefficients are `c`, constant term first. Degree less than `n`. -/
noncomputable def coeffPoly {n : ℕ} (c : Fin n → F) : F[X] :=
  ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

theorem coeff_coeffPoly {n : ℕ} (c : Fin n → F) (k : ℕ) :
    (coeffPoly c).coeff k = if h : k < n then c ⟨k, h⟩ else 0 := by
  classical
  unfold coeffPoly
  rw [finsetSum_coeff]
  by_cases hk : k < n
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · simp [hk]
    · intro i _ hne
      rw [coeff_C_mul_X_pow]
      split_ifs with hik
      · exact absurd (Fin.ext hik.symm) hne
      · rfl
    · simp
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro i _
      rw [coeff_C_mul_X_pow]
      split_ifs with hik
      · exact (hk (hik.symm ▸ i.isLt)).elim
      · rfl
    · simp [hk]

/-- Every polynomial of degree less than `n` is the mask of its coefficients. -/
theorem coeffPoly_of_degree_lt {n : ℕ} {p : F[X]} (hp : p.degree < n) :
    coeffPoly (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  ext k
  rw [coeff_coeffPoly]
  by_cases hk : k < n
  · simp [hk]
  · have hdeg : p.degree < k := lt_of_lt_of_le hp (by exact_mod_cast (le_of_not_gt hk))
    simp [hk, Polynomial.coeff_eq_zero_of_degree_lt hdeg]

theorem coeffPoly_add {n : ℕ} (c d : Fin n → F) :
    coeffPoly (fun i => c i + d i) = coeffPoly c + coeffPoly d := by
  ext k
  rw [coeff_add, coeff_coeffPoly, coeff_coeffPoly, coeff_coeffPoly]
  by_cases hk : k < n <;> simp [hk]

/-- Adding a fixed mask is a bijection of coefficient space. -/
def addCoeffEquiv {n : ℕ} (d : Fin n → F) : (Fin n → F) ≃ (Fin n → F) where
  toFun c i := c i + d i
  invFun c i := c i - d i
  left_inv c := by ext i; ring
  right_inv c := by ext i; ring

/-- Answers of `masked H p (coeffPoly c)` at the queries `q`. -/
noncomputable def maskedAnswers (H : EvalDomain F) (p : F[X]) {n : ℕ}
    (c : Fin n → F) (q : Fin n → F) : Fin n → F :=
  fun i => (masked H p (coeffPoly c)).eval (q i)

/-- The degree-`< n` mask that cancels `p` at `n` distinct outside queries. -/
noncomputable def queryShiftPoly (H : EvalDomain F) (p : F[X]) {n : ℕ}
    (q : Fin n → F) : F[X] :=
  Lagrange.interpolate (Finset.univ : Finset (Fin n)) q
    (fun i => p.eval (q i) * (H.vanishing.eval (q i))⁻¹)

omit [Field F] in
theorem injOn_query {n : ℕ} {q : Fin n → F} (hinj : Function.Injective q) :
    Set.InjOn q (↑(Finset.univ : Finset (Fin n))) := by
  simpa [Finset.coe_univ] using (Set.injOn_univ.mpr hinj)

theorem degree_queryShiftPoly_lt (H : EvalDomain F) (p : F[X]) {n : ℕ}
    {q : Fin n → F} (hinj : Function.Injective q) :
    (queryShiftPoly H p q).degree < n := by
  simpa [queryShiftPoly, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n))) (v := q)
      (r := fun i => p.eval (q i) * (H.vanishing.eval (q i))⁻¹)
      (injOn_query hinj)

theorem eval_queryShiftPoly (H : EvalDomain F) (p : F[X]) {n : ℕ}
    {q : Fin n → F} (hinj : Function.Injective q) (i : Fin n) :
    (queryShiftPoly H p q).eval (q i) =
      p.eval (q i) * (H.vanishing.eval (q i))⁻¹ := by
  simpa [queryShiftPoly] using
    Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin n))) (v := q)
      (r := fun j => p.eval (q j) * (H.vanishing.eval (q j))⁻¹)
      (injOn_query hinj) (Finset.mem_univ i)

theorem natDegree_coeffPoly_lt {n : ℕ} (hn : 0 < n) (c : Fin n → F) :
    (coeffPoly c).natDegree < n := by
  have hle : (coeffPoly c).natDegree ≤ n - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_coeffPoly]
    simp [show ¬ N < n by omega]
  omega

/-- Evaluation of degree-`< n` masks at `n` distinct points is bijective. -/
theorem eval_coeffPoly_bijective {n : ℕ} {q : Fin n → F} (hinj : Function.Injective q) :
    Function.Bijective (fun c : Fin n → F => fun i => (coeffPoly c).eval (q i)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro c₁ c₂ h
    by_cases hn : n = 0
    · subst hn
      ext i
      exact Fin.elim0 i
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      let p := coeffPoly c₁ - coeffPoly c₂
      have heval : ∀ i, p.eval (q i) = 0 := by
        intro i
        simp only [p, eval_sub, sub_eq_zero]
        exact congr_fun h i
      have hdeg : p.natDegree < n := by
        have hle := Polynomial.natDegree_sub_le (coeffPoly c₁) (coeffPoly c₂)
        exact lt_of_le_of_lt hle
          (max_lt (natDegree_coeffPoly_lt hn' c₁) (natDegree_coeffPoly_lt hn' c₂))
      have hp : p = 0 :=
        eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj heval (by simpa [Fintype.card_fin] using hdeg)
      have hc : coeffPoly c₁ = coeffPoly c₂ := sub_eq_zero.mp (by simpa [p] using hp)
      ext i
      have hcoeff := congrArg (fun r : F[X] => r.coeff (i : ℕ)) hc
      simpa [coeff_coeffPoly, i.isLt] using hcoeff
  · intro a
    by_cases hn : n = 0
    · subst hn
      exact ⟨fun i => Fin.elim0 (α := F) i, by ext i; exact Fin.elim0 i⟩
    · let r := Lagrange.interpolate (Finset.univ : Finset (Fin n)) q a
      have hdeg : r.degree < n := by
        simpa [r, Finset.card_univ, Fintype.card_fin] using
          Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n))) (v := q) (r := a)
            (injOn_query hinj)
      refine ⟨fun i => r.coeff (i : ℕ), ?_⟩
      ext i
      change (coeffPoly (fun j => r.coeff (j : ℕ))).eval (q i) = a i
      rw [coeffPoly_of_degree_lt hdeg]
      simpa [r] using
        Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin n))) (v := q) (r := a)
          (injOn_query hinj) (Finset.mem_univ i)

/-- Coordinatewise `y ↦ p(q) + v · y` is bijective when no `v` is zero. -/
theorem affineAnswers_bijective {n : ℕ} (base : Fin n → F) {v : Fin n → F}
    (hv : ∀ i, v i ≠ 0) :
    Function.Bijective (fun y : Fin n → F => fun i => base i + v i * y i) := by
  refine ⟨?_, ?_⟩
  · intro y₁ y₂ h
    ext i
    have hi := congr_fun h i
    exact mul_left_cancel₀ (hv i) (by simpa [add_right_inj] using hi)
  · intro z
    refine ⟨fun i => (z i - base i) * (v i)⁻¹, ?_⟩
    ext i
    change base i + v i * ((z i - base i) * (v i)⁻¹) = z i
    rw [mul_comm (z i - base i) ((v i)⁻¹), mul_inv_cancel_left₀ (hv i)]
    abel

/-- At `n` distinct queries outside the domain, every answer tuple is one mask. -/
theorem maskedAnswers_bijective (H : EvalDomain F) (p : F[X]) {n : ℕ} {q : Fin n → F}
    (hinj : Function.Injective q) (hv : ∀ i, H.vanishing.eval (q i) ≠ 0) :
    Function.Bijective (maskedAnswers H p (q := q)) := by
  have heval := eval_coeffPoly_bijective (q := q) hinj
  have haff := affineAnswers_bijective (fun i => p.eval (q i))
    (v := fun i => H.vanishing.eval (q i)) hv
  have hcomp : maskedAnswers H p (q := q) =
      (fun y i => p.eval (q i) + H.vanishing.eval (q i) * y i) ∘
        (fun c i => (coeffPoly c).eval (q i)) := by
    ext c i
    simp [maskedAnswers, masked, eval_add, eval_mul]
  rw [hcomp]
  exact haff.comp heval

/-- `masked p` and `masked 0` give the same answers after one coefficient translation. -/
theorem maskedAnswers_translate (H : EvalDomain F) (p : F[X]) {n : ℕ} {q : Fin n → F}
    (hinj : Function.Injective q) (hv : ∀ i, H.vanishing.eval (q i) ≠ 0) :
    ∃ d : Fin n → F, ∀ c,
      maskedAnswers H p c q =
        maskedAnswers H 0 (fun i => c i + d i) q := by
  let r := queryShiftPoly H p q
  refine ⟨fun i => r.coeff (i : ℕ), ?_⟩
  intro c
  ext j
  have hr := coeffPoly_of_degree_lt (degree_queryShiftPoly_lt H p hinj)
  have he := eval_queryShiftPoly H p hinj j
  simp only [maskedAnswers, masked, eval_add, eval_mul, zero_add, coeffPoly_add]
  have hdEval : (coeffPoly (fun i : Fin n => r.coeff (i : ℕ))).eval (q j) =
      p.eval (q j) * (H.vanishing.eval (q j))⁻¹ := by
    rw [hr]
    exact he
  rw [mul_add, hdEval, ← mul_assoc, mul_comm (H.vanishing.eval (q j)) (p.eval (q j)), mul_assoc,
    mul_inv_cancel₀ (hv j), mul_one]
  abel

/-- A predicate on the answers has the same number of masks for every base polynomial. -/
theorem card_maskedAnswers [Fintype F] [DecidableEq F] (H : EvalDomain F) (p : F[X])
    {n : ℕ} {q : Fin n → F} (hinj : Function.Injective q)
    (hv : ∀ i, H.vanishing.eval (q i) ≠ 0) (φ : (Fin n → F) → Prop) [DecidablePred φ] :
    (Finset.univ.filter fun c => φ (maskedAnswers H p c q)).card =
      (Finset.univ.filter fun c => φ (maskedAnswers H 0 c q)).card := by
  obtain ⟨d, hd⟩ := maskedAnswers_translate H p hinj hv
  refine Finset.card_equiv (addCoeffEquiv d) fun c => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hd c]
  simp [addCoeffEquiv]

/-- What an honest verifier sees, and a simulator can produce without the witness.
`matrixMsg` is shared : matrix `g` and `σ` are functions of the public matrix
(`honestMatrixF`), not of the witness. `row` is the rowcheck value, not `h₀(α)`.
`blind` is the constant hiding scalar; the commitment is determined by the
lineval polynomial together with it. The raw witness opening is absent. -/
@[ext]
structure ZKSimView (F : Type*) [Field F] (n : ℕ) (β : Type*) where
  answers : Fin n → F
  lineval : F[X]
  atBeta : F
  row : F
  matrixMsg : β
  blind : F

/-- Real view at query mask `cQ`, lineval mask `cL`, and blinding `ρ`. -/
noncomputable def realZKView {n m : ℕ} (H : EvalDomain F) (p zReal : F[X])
    (mA mB mC : F[X]) (ηA ηB ηC β₀ row : F) {β : Type*} (matrixMsg : β)
    (cQ : Fin n → F) (q : Fin n → F) (cL : Fin m → F) (ρ : F) : ZKSimView F n β where
  answers := maskedAnswers H p cQ q
  lineval := linevalPolyEta .ZK (coeffPoly cL) zReal mA mB mC ηA ηB ηC
  atBeta := (linevalPolyEta .ZK (coeffPoly cL) zReal mA mB mC ηA ηB ηC).eval β₀
  row := row
  matrixMsg := matrixMsg
  blind := ρ

/-- Simulator view. No witness: the lineval polynomial uses `zSim`. -/
noncomputable def simZKView {n m : ℕ} (H : EvalDomain F) (zSim : F[X])
    (mA mB mC : F[X]) (ηA ηB ηC β₀ row : F) {β : Type*} (matrixMsg : β)
    (cQ : Fin n → F) (q : Fin n → F) (cL : Fin m → F) (ρ : F) : ZKSimView F n β where
  answers := maskedAnswers H 0 cQ q
  lineval := linevalPolyEta .ZK (coeffPoly cL) zSim mA mB mC ηA ηB ηC
  atBeta := (linevalPolyEta .ZK (coeffPoly cL) zSim mA mB mC ηA ηB ηC).eval β₀
  row := row
  matrixMsg := matrixMsg
  blind := ρ

/-- Masks, the space the honest prover samples. -/
abbrev ZKMask (n m : ℕ) (F : Type*) := (Fin n → F) × (Fin m → F) × F

/-- Translate both masks and leave the blinding fixed. -/
def translateZKMask {n m : ℕ} (dQ : Fin n → F) (dL : Fin m → F) :
    ZKMask n m F ≃ ZKMask n m F where
  toFun x := (addCoeffEquiv dQ x.1, addCoeffEquiv dL x.2.1, x.2.2)
  invFun x := ((addCoeffEquiv dQ).symm x.1, (addCoeffEquiv dL).symm x.2.1, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The real view equals the witness-free view after translating the two masks.
The lineval translation exists when `lin · (zReal − zSim)` has degree less than
the lineval mask. Both views use the same rowcheck value and the same matrix
message. -/
theorem zkProof_translate {n m : ℕ} (H : EvalDomain F) (p zReal zSim mA mB mC : F[X])
    (ηA ηB ηC β₀ row : F) {β : Type*} (matrixMsg : β) {q : Fin n → F}
    (hinj : Function.Injective q) (hv : ∀ i, H.vanishing.eval (q i) ≠ 0)
    (hdeg : (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).degree < m) :
    ∃ dQ : Fin n → F, ∃ dL : Fin m → F, ∀ (cQ : Fin n → F) (cL : Fin m → F) (ρ : F),
      realZKView H p zReal mA mB mC ηA ηB ηC β₀ row matrixMsg cQ q cL ρ =
        simZKView H zSim mA mB mC ηA ηB ηC β₀ row matrixMsg
          (fun i => cQ i + dQ i) q (fun i => cL i + dL i) ρ := by
  obtain ⟨dQ, hdQ⟩ := maskedAnswers_translate H p hinj hv
  let dL : Fin m → F := fun i =>
    (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).coeff (i : ℕ)
  refine ⟨dQ, dL, ?_⟩
  intro cQ cL ρ
  have hlin := linevalPolyEta_absorb (coeffPoly cL) zSim zReal mA mB mC ηA ηB ηC
  have hd : coeffPoly dL = linPoly mA mB mC ηA ηB ηC * (zReal - zSim) :=
    coeffPoly_of_degree_lt hdeg
  apply ZKSimView.ext
  · simpa [realZKView, simZKView] using hdQ cQ
  · simpa [realZKView, simZKView, coeffPoly_add, hd] using hlin.symm
  · simpa [realZKView, simZKView, coeffPoly_add, hd] using congrArg (eval β₀) hlin.symm
  · rfl
  · rfl
  · rfl

/-- Every predicate of the view has the same number of real masks and simulator masks. -/
theorem card_zkProof [Fintype F] [DecidableEq F] {n m : ℕ} (H : EvalDomain F)
    (p zReal zSim mA mB mC : F[X]) (ηA ηB ηC β₀ row : F) {β : Type*} (matrixMsg : β)
    {q : Fin n → F} (hinj : Function.Injective q) (hv : ∀ i, H.vanishing.eval (q i) ≠ 0)
    (hdeg : (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).degree < m)
    (φ : ZKSimView F n β → Prop) [DecidablePred φ] :
    (Finset.univ.filter fun x : ZKMask n m F =>
        φ (realZKView H p zReal mA mB mC ηA ηB ηC β₀ row matrixMsg x.1 q x.2.1 x.2.2)).card =
      (Finset.univ.filter fun x : ZKMask n m F =>
        φ (simZKView H zSim mA mB mC ηA ηB ηC β₀ row matrixMsg x.1 q x.2.1 x.2.2)).card := by
  obtain ⟨dQ, dL, htr⟩ :=
    zkProof_translate H p zReal zSim mA mB mC ηA ηB ηC β₀ row matrixMsg
    hinj hv hdeg
  refine Finset.card_equiv (translateZKMask dQ dL) fun x => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htr x.1 x.2.1 x.2.2]
  simp [translateZKMask, addCoeffEquiv]

/-- Equal lineval polynomials with the same constant blinding are the same hiding commitment. -/
theorem hidingCommit_of_translate {G1 G2 : Type*} [AddCommGroup G1] [Module F G1] {m : ℕ}
    (vk : HidingKey G1 G2) (β₀ : F) (zReal zSim mA mB mC : F[X]) (ηA ηB ηC : F)
    (cL : Fin m → F) (ρ : F)
    (hdeg : (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).degree < m) :
    kzgCommitHiding vk β₀ (linevalPolyEta .ZK (coeffPoly cL) zReal mA mB mC ηA ηB ηC) (C ρ) =
      kzgCommitHiding vk β₀
        (linevalPolyEta .ZK (coeffPoly (fun i => cL i +
          (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).coeff (i : ℕ)))
          zSim mA mB mC ηA ηB ηC) (C ρ) := by
  have hd : coeffPoly (fun i : Fin m =>
    (linPoly mA mB mC ηA ηB ηC * (zReal - zSim)).coeff (i : ℕ)) =
      linPoly mA mB mC ηA ηB ηC * (zReal - zSim) := coeffPoly_of_degree_lt hdeg
  have hlin := linevalPolyEta_absorb (coeffPoly cL) zSim zReal mA mB mC ηA ηB ηC
  rw [← hlin, coeffPoly_add, hd]

end Varuna