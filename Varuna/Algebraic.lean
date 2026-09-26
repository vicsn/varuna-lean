/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.SonicPC

/-!
# KZG openings under an algebraic adversary

Ironwood's adversary is *algebraic* : every group element it outputs comes
with a representation over the public points it was given. For Sonic-KZG
those points are the SRS powers `[τ^i] g`, so a representation is a
coefficient list `r` and the element is `r(τ) · g`.

Under that restriction an accepted opening either claims the true
evaluation of the representation, or the SRS trapdoor `τ` is a root of a
nonzero polynomial computed from the prover's own output. The latter is
the break (q-DLOG : root finding recovers `τ`). The break data is a plain
coefficient list produced by a computable `def`; the polynomial facts
about it are `Prop` certificates.

The algebraic restriction and trapdoor hardness are modelling floors
(`ModellingFloor.algebraicAdversary`, `ModellingFloor.pairingHardness`).
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-! ## Coefficient lists -/

/-- Pointwise sum of coefficient lists; the shorter list is padded with zeros. -/
def addCoeffs : List F → List F → List F
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addCoeffs l m

/-- Multiply every coefficient by `c`. -/
def scaleCoeffs (c : F) (l : List F) : List F :=
  l.map (c * ·)

/-- Multiply by `X`. -/
def shiftCoeffs (l : List F) : List F :=
  0 :: l

/-- Horner evaluation of a coefficient list. -/
def evalCoeffs (l : List F) (x : F) : F :=
  l.foldr (fun a acc => a + x * acc) 0

/-- The polynomial a coefficient list denotes (constant term first). -/
noncomputable def toPoly : List F → F[X]
  | [] => 0
  | a :: l => C a + X * toPoly l

/-- The empty list is the zero polynomial. -/
@[simp] theorem toPoly_nil : toPoly ([] : List F) = 0 :=
  rfl

/-- Unfolding a cons cell. -/
@[simp] theorem toPoly_cons (a : F) (l : List F) : toPoly (a :: l) = C a + X * toPoly l :=
  rfl

/-- Coefficient sums denote polynomial sums. -/
theorem toPoly_addCoeffs : ∀ l m : List F, toPoly (addCoeffs l m) = toPoly l + toPoly m
  | [], m => by simp [addCoeffs]
  | a :: l, [] => by simp [addCoeffs]
  | a :: l, b :: m => by
    simp only [addCoeffs, toPoly_cons, toPoly_addCoeffs l m, C_add]
    ring

/-- Scaling coefficients is multiplication by a constant. -/
theorem toPoly_scaleCoeffs (c : F) : ∀ l : List F, toPoly (scaleCoeffs c l) = C c * toPoly l
  | [] => by simp [scaleCoeffs]
  | a :: l => by
    have ih := toPoly_scaleCoeffs c l
    simp only [scaleCoeffs, List.map_cons, toPoly_cons] at ih ⊢
    rw [ih, C_mul]
    ring

/-- Shifting coefficients is multiplication by `X`. -/
@[simp] theorem toPoly_shiftCoeffs (l : List F) : toPoly (shiftCoeffs l) = X * toPoly l := by
  simp [shiftCoeffs]

/-- Horner evaluation agrees with polynomial evaluation. -/
theorem eval_toPoly (x : F) : ∀ l : List F, (toPoly l).eval x = evalCoeffs l x
  | [] => by simp [evalCoeffs]
  | a :: l => by
    have ih := eval_toPoly x l
    simp only [evalCoeffs, List.foldr_cons] at ih ⊢
    simp [ih]

/-! ## Algebraic group elements -/

/-- The group element with representation `r` over the SRS powers of `g`. -/
def represent {G1 : Type*} [AddCommGroup G1] [Module F G1] (g : G1) (τ : F) (r : List F) :
    G1 :=
  evalCoeffs r τ • g

/-- Opening defect `p − v − (X − z) q` for representations `p` (commitment)
and `q` (witness). It vanishes at `τ` exactly when the KZG check holds. -/
def openingDefect (p q : List F) (z v : F) : List F :=
  addCoeffs (addCoeffs p [-v]) (addCoeffs (scaleCoeffs (-1) (shiftCoeffs q)) (scaleCoeffs z q))

/-- The defect list denotes `p − v − (X − z) q`. -/
theorem toPoly_openingDefect (p q : List F) (z v : F) :
    toPoly (openingDefect p q z v) = toPoly p - C v - (X - C z) * toPoly q := by
  simp only [openingDefect, toPoly_addCoeffs, toPoly_scaleCoeffs, toPoly_shiftCoeffs,
    toPoly_cons, toPoly_nil, mul_zero, add_zero, C_neg, C_1]
  ring

/-- A nonzero polynomial whose roots include the SRS trapdoor. -/
structure TrapdoorBreak (F : Type*) where
  /-- Coefficients of the polynomial (constant term first). -/
  coeffs : List F

/-- The certificate a trapdoor break carries: nonzero, and `τ` is a root. -/
def TrapdoorBreak.holds (b : TrapdoorBreak F) (τ : F) : Prop :=
  toPoly b.coeffs ≠ 0 ∧ (toPoly b.coeffs).eval τ = 0

/-- Inspect an opening of the representation `p` at `z` with claimed value
`v` and witness representation `q` : a wrong claim is returned as break data. -/
def inspectOpening [DecidableEq F] (p q : List F) (z v : F) : Option (TrapdoorBreak F) :=
  if v = evalCoeffs p z then none else some ⟨openingDefect p q z v⟩

/-- No break is reported exactly when the claimed value is the evaluation. -/
theorem inspectOpening_eq_none_iff [DecidableEq F] (p q : List F) (z v : F) :
    inspectOpening p q z v = none ↔ v = evalCoeffs p z := by
  unfold inspectOpening
  split_ifs with h <;> simp [h]

/-- A wrong claimed value makes the defect polynomial nonzero. -/
theorem toPoly_openingDefect_ne_zero {p q : List F} {z v : F} (hv : v ≠ evalCoeffs p z) :
    toPoly (openingDefect p q z v) ≠ 0 := by
  intro h
  have hz := congrArg (eval z) h
  simp only [toPoly_openingDefect, eval_sub, eval_mul, eval_C, eval_X, sub_self, zero_mul,
    sub_zero, eval_zero, eval_toPoly] at hz
  exact hv (sub_eq_zero.mp hz).symm

/-- In a vector space, a nonzero vector has a trivial annihilator. -/
theorem eq_zero_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module F M] {r : F} {x : M}
    (h : r • x = 0) (hx : x ≠ 0) : r = 0 := by
  by_contra hr
  apply hx
  calc x = r⁻¹ • r • x := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    _ = 0 := by rw [h, smul_zero]

variable {G1 G2 GT : Type*}
  [AddCommGroup G1] [AddCommGroup G2] [AddCommGroup GT]
  [Module F G1] [Module F G2] [Module F GT]

/-- An accepted KZG check on algebraic elements is the field identity
`p(τ) − v = (τ − z) q(τ)`, i.e. the defect vanishes at the trapdoor. -/
theorem openingDefect_eval_trapdoor (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    {τ : F} (hwf : vk.wellFormed τ) (hgh : e.pair vk.g vk.h ≠ 0) (p q : List F)
    (o : Opening G1 F) (hw : o.witness = represent vk.g τ q)
    (hc : kzgCheck e vk (represent vk.g τ p) o) :
    (toPoly (openingDefect p q o.point o.value)).eval τ = 0 := by
  unfold kzgCheck VerifyingKey.wellFormed at *
  rw [hwf, hw] at hc
  unfold represent at hc
  rw [← sub_smul, ← sub_smul, e.map_smul_left, e.map_smul_left, e.map_smul_right,
    smul_smul] at hc
  have h0 : (evalCoeffs p τ - o.value - evalCoeffs q τ * (τ - o.point)) • e.pair vk.g vk.h = 0 :=
    by
    rw [sub_smul, hc, sub_self]
  have hs := eq_zero_of_smul_eq_zero h0 hgh
  rw [toPoly_openingDefect]
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_toPoly]
  rw [mul_comm (τ - o.point)]
  exact hs

/-- Evaluation soundness under the algebraic restriction: if the check
accepts and inspection returns data, that data is a genuine trapdoor break. -/
theorem inspectOpening_break [DecidableEq F] (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    {τ : F} (hwf : vk.wellFormed τ) (hgh : e.pair vk.g vk.h ≠ 0) (p q : List F)
    (o : Opening G1 F) (hw : o.witness = represent vk.g τ q)
    (hc : kzgCheck e vk (represent vk.g τ p) o) {b : TrapdoorBreak F}
    (hb : inspectOpening p q o.point o.value = some b) : b.holds τ := by
  unfold inspectOpening at hb
  split_ifs at hb with hv
  cases hb
  exact ⟨toPoly_openingDefect_ne_zero hv, openingDefect_eval_trapdoor e vk hwf hgh p q o hw hc⟩

/-- The trapdoor of a break lies in the Schwartz–Zippel root set of its polynomial. -/
theorem TrapdoorBreak.mem_szBadSet [DecidableEq F] {b : TrapdoorBreak F} {τ : F}
    (h : b.holds τ) : τ ∈ szBadSet (toPoly b.coeffs) :=
  Multiset.mem_toFinset.2 ((mem_roots h.1).2 h.2)

/-- Honest representations: the honest KZG commitment is `represent` of the
polynomial's coefficients, so honest openings never produce break data. -/
theorem inspectOpening_honest [DecidableEq F] (p q : List F) (z : F) :
    inspectOpening p q z (evalCoeffs p z) = none :=
  (inspectOpening_eq_none_iff p q z _).2 rfl

end Varuna