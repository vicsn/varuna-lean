/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Tactic.Module
import Varuna.SonicPC

/-!
# KZG openings under an algebraic adversary

Ironwood's adversary is *algebraic* : every group element it outputs comes
with a representation over the public points it was given. For Sonic-KZG
those points are the SRS powers `[τ^i] g`, so a representation is a
coefficient list `r` and the element is `r(τ) · g`. A hiding
commitment also carries a blinding representation over `gamma_g`.

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

/-- The PC reduction's contract: when inspection returns no break, the opened
value is the evaluation of the prover's represented polynomial. This is what
lets a downstream soundness argument treat an opened scalar as a true
polynomial evaluation. -/
theorem value_correct_of_inspect_none [DecidableEq F] {p q : List F} {z v : F}
    (h : inspectOpening p q z v = none) : v = (toPoly p).eval z := by
  rw [eval_toPoly]
  exact (inspectOpening_eq_none_iff p q z v).1 h

/-! ## Degree bounds

Sonic/Marlin enforce `deg p ≤ d` with a shifted commitment `C̃` to
`X^{D-d} p` and the check `e(C̃, h) = e(C, [τ^{D-d}] h)`, where `D` is the
SRS degree. snarkVM folds this pairing into the batched check (Gabizon19
§3); the algebraic content is the same. An algebraic prover can only
represent `C̃` over `D + 1` powers, so a polynomial above degree `d`
cannot be shifted into range without a trapdoor break. -/

/-- Multiply by `X^m`. -/
def shiftCoeffsBy (m : Nat) (l : List F) : List F :=
  List.replicate m 0 ++ l

/-- `X^m · l`. -/
theorem toPoly_shiftCoeffsBy (m : Nat) (l : List F) :
    toPoly (shiftCoeffsBy m l) = X ^ m * toPoly l := by
  induction m with
  | zero => simp [shiftCoeffsBy]
  | succ m ih =>
    simp only [shiftCoeffsBy, List.replicate_succ, List.cons_append, toPoly_cons, C_0,
      zero_add] at ih ⊢
    rw [ih]
    ring

/-- Coefficients of a list polynomial are the list entries. -/
theorem coeff_toPoly : ∀ (l : List F) (i : Nat), (toPoly l).coeff i = l.getD i 0
  | [], i => by simp
  | a :: l, 0 => by simp
  | a :: l, i + 1 => by simp [coeff_X_mul, coeff_toPoly l i]

/-- Coefficients of `p` through its degree, constant term first. -/
def coeffList (p : F[X]) : List F :=
  (List.range (p.natDegree + 1)).map p.coeff

/-- Every polynomial is the list of its coefficients. -/
theorem toPoly_coeffList (p : F[X]) : toPoly (coeffList p) = p := by
  ext i
  rw [coeff_toPoly, List.getD_eq_getElem?_getD]
  simp only [coeffList]
  by_cases hi : i < p.natDegree + 1
  · have hget : ((List.range (p.natDegree + 1)).map p.coeff)[i]? = some (p.coeff i) := by
      rw [List.getElem?_map, List.getElem?_range (by simpa using hi)]
      simp
    simp [hget]
  · have hlen : ((List.range (p.natDegree + 1)).map p.coeff).length = p.natDegree + 1 := by
      simp [List.length_map, List.length_range]
    have hi' : p.natDegree + 1 ≤ i := by omega
    rw [List.getElem?_eq_none (by rw [hlen]; exact hi')]
    simp
    exact (coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hi')).symm

/-- Whether some coefficient above degree `d` is nonzero. -/
def exceedsBound [DecidableEq F] (p : List F) (d : Nat) : Bool :=
  (p.drop (d + 1)).any (· ≠ 0)

/-- No nonzero coefficient above `d` means degree at most `d`. -/
theorem natDegree_toPoly_le [DecidableEq F] {p : List F} {d : Nat}
    (h : exceedsBound p d = false) : (toPoly p).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly, List.getD_eq_getElem?_getD]
  have hNd : d + 1 ≤ N := by exact_mod_cast hN
  cases hget : p[N]? with
  | none => rfl
  | some a =>
    have hdrop : (p.drop (d + 1))[N - (d + 1)]? = some a := by
      rw [List.getElem?_drop, Nat.add_sub_cancel' hNd, hget]
    have hmem : a ∈ p.drop (d + 1) := List.mem_of_getElem? hdrop
    unfold exceedsBound at h
    have := List.any_eq_false.mp h a hmem
    simpa using this

/-- A nonzero coefficient above `d` is witnessed at some index. -/
theorem exists_coeff_of_exceedsBound [DecidableEq F] {p : List F} {d : Nat}
    (h : exceedsBound p d = true) : ∃ N, d < N ∧ p.getD N 0 ≠ 0 := by
  unfold exceedsBound at h
  obtain ⟨a, ha, hne⟩ := List.any_eq_true.mp h
  obtain ⟨j, hj, hja⟩ := List.getElem_of_mem ha
  refine ⟨d + 1 + j, by omega, ?_⟩
  have : p[d + 1 + j]? = some a := by
    rw [← List.getElem?_drop, List.getElem?_eq_getElem hj, hja]
  rw [List.getD_eq_getElem?_getD, this]
  simpa using hne

/-- Degree defect `p̃ − X^{D-d} p`: vanishes at `τ` exactly when the shifted check holds. -/
def degreeDefect (p pShift : List F) (D d : Nat) : List F :=
  addCoeffs pShift (scaleCoeffs (-1) (shiftCoeffsBy (D - d) p))

/-- The degree defect denotes `p̃ − X^{D-d} p`. -/
theorem toPoly_degreeDefect (p pShift : List F) (D d : Nat) :
    toPoly (degreeDefect p pShift D d) = toPoly pShift - X ^ (D - d) * toPoly p := by
  rw [degreeDefect, toPoly_addCoeffs, toPoly_scaleCoeffs, toPoly_shiftCoeffsBy, C_neg, C_1]
  ring

/-- Inspect a degree-bound claim: exceeding the bound is returned as break data. -/
def inspectDegree [DecidableEq F] (p pShift : List F) (D d : Nat) : Option (TrapdoorBreak F) :=
  if exceedsBound p d then some ⟨degreeDefect p pShift D d⟩ else none

/-- No break reported means the representation respects the bound. -/
theorem natDegree_le_of_inspectDegree [DecidableEq F] {p pShift : List F} {D d : Nat}
    (h : inspectDegree p pShift D d = none) : (toPoly p).natDegree ≤ d := by
  unfold inspectDegree at h
  split_ifs at h with hb
  exact natDegree_toPoly_le (Bool.eq_false_iff.mpr hb)

/-- Sonic/Marlin degree-bound pairing check with `shiftH = [τ^{D-d}] h`. -/
def degreeCheck (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2) (shiftH : G2)
    (cm cmShift : G1) : Prop :=
  e.pair cmShift vk.h = e.pair cm shiftH

/-- Degree-bound soundness under the algebraic restriction: if the shifted
check accepts, the shifted representation lives in the SRS range, and the
representation exceeds the bound, inspection returns a genuine trapdoor break. -/
theorem inspectDegree_break [DecidableEq F] (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    {τ : F} (hgh : e.pair vk.g vk.h ≠ 0) {D d : Nat} (hdD : d ≤ D) (p pShift : List F)
    (hlen : pShift.length ≤ D + 1)
    (hc : degreeCheck e vk ((τ ^ (D - d)) • vk.h) (represent vk.g τ p)
      (represent vk.g τ pShift)) {b : TrapdoorBreak F}
    (hb : inspectDegree p pShift D d = some b) : b.holds τ := by
  unfold inspectDegree at hb
  split_ifs at hb with hex
  cases hb
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hN, hne⟩ := exists_coeff_of_exceedsBound hex
    intro h0
    have hcoeff := congrArg (fun q => q.coeff (D - d + N)) h0
    have hpS : pShift.getD (D - d + N) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    simp only [toPoly_degreeDefect, coeff_sub, coeff_X_pow_mul', coeff_zero] at hcoeff
    rw [if_pos (by omega), Nat.add_sub_cancel_left, coeff_toPoly, coeff_toPoly, hpS, zero_sub,
      neg_eq_zero] at hcoeff
    exact hne hcoeff
  · unfold degreeCheck represent at hc
    rw [e.map_smul_left, e.map_smul_right, e.map_smul_left, smul_smul] at hc
    have h0 : (evalCoeffs pShift τ - τ ^ (D - d) * evalCoeffs p τ) • e.pair vk.g vk.h = 0 := by
      rw [sub_smul, hc, sub_self]
    have hs := eq_zero_of_smul_eq_zero h0 hgh
    rw [toPoly_degreeDefect]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_toPoly]
    exact hs

/-- An accepted hiding check splits across the two generators: both the
polynomial and the blinding open at the trapdoor. -/
theorem hidingDefect_eval_trapdoor (e : Pairing F G1 G2 GT) (vk : HidingKey G1 G2)
    {τ : F} (hwf : vk.wellFormed τ) (hind : pairingIndependent e vk)
    (p r q s : List F) {C : G1} {randomV : F} (o : Opening G1 F)
    (hC : C = represent vk.g τ p + represent vk.gammaG τ r)
    (hw : o.witness = represent vk.g τ q + represent vk.gammaG τ s)
    (hc : kzgCheckHiding e vk C randomV o) :
    (toPoly (openingDefect p q o.point o.value)).eval τ = 0 ∧
      (toPoly (openingDefect r s o.point randomV)).eval τ = 0 := by
  unfold kzgCheckHiding HidingKey.wellFormed at *
  rw [hwf, hC, hw] at hc
  unfold represent at hc
  have hL :
      evalCoeffs p τ • vk.g + evalCoeffs r τ • vk.gammaG - o.value • vk.g -
          randomV • vk.gammaG =
        (evalCoeffs p τ - o.value) • vk.g + (evalCoeffs r τ - randomV) • vk.gammaG := by
    rw [sub_smul, sub_smul]
    abel_nf
  have hβ : τ • vk.h - o.point • vk.h = (τ - o.point) • vk.h := by rw [← sub_smul]
  rw [hL, hβ] at hc
  have hLpair :
      e.pair ((evalCoeffs p τ - o.value) • vk.g + (evalCoeffs r τ - randomV) • vk.gammaG) vk.h =
        (evalCoeffs p τ - o.value) • e.pair vk.g vk.h +
          (evalCoeffs r τ - randomV) • e.pair vk.gammaG vk.h := by
    rw [e.map_add_left, e.map_smul_left, e.map_smul_left]
  have hRpair :
      e.pair (evalCoeffs q τ • vk.g + evalCoeffs s τ • vk.gammaG) ((τ - o.point) • vk.h) =
        ((τ - o.point) * evalCoeffs q τ) • e.pair vk.g vk.h +
          ((τ - o.point) * evalCoeffs s τ) • e.pair vk.gammaG vk.h := by
    rw [e.map_smul_right, e.map_add_left, e.map_smul_left, e.map_smul_left, smul_add, smul_smul,
      smul_smul]
  rw [hLpair, hRpair] at hc
  set eg := e.pair vk.g vk.h
  set eγ := e.pair vk.gammaG vk.h
  set a := evalCoeffs p τ - o.value
  set b := evalCoeffs r τ - randomV
  set c := (τ - o.point) * evalCoeffs q τ
  set d := (τ - o.point) * evalCoeffs s τ
  have h0 : (a - c) • eg + (b - d) • eγ = 0 := by
    suffices hgen :
        ∀ (a b c d : F) (eg eγ : GT),
          a • eg + b • eγ = c • eg + d • eγ → (a - c) • eg + (b - d) • eγ = 0 by
      exact hgen a b c d eg eγ hc
    intro a b c d eg eγ hc
    have hsplit : (a - c) • eg + (b - d) • eγ = (a • eg + b • eγ) - (c • eg + d • eγ) :=
      by
      module
    rw [hsplit, hc, sub_self]
  have ⟨ha, hb⟩ := hind _ _ h0
  refine ⟨?_, ?_⟩
  · rw [toPoly_openingDefect]
    simpa [eval_sub, eval_mul, eval_C, eval_X, eval_toPoly] using ha
  · rw [toPoly_openingDefect]
    simpa [eval_sub, eval_mul, eval_C, eval_X, eval_toPoly] using hb

/-- Simulation extraction for one hiding opening. An accepted algebraic proof
is a trapdoor break or the opened value of the represented polynomial. -/
theorem hidingOpening_extract [DecidableEq F] (e : Pairing F G1 G2 GT) (vk : HidingKey G1 G2)
    {τ : F} (hwf : vk.wellFormed τ) (hind : pairingIndependent e vk)
    (p r q s : List F) {C : G1} {randomV : F} (o : Opening G1 F)
    (hC : C = represent vk.g τ p + represent vk.gammaG τ r)
    (hw : o.witness = represent vk.g τ q + represent vk.gammaG τ s)
    (hc : kzgCheckHiding e vk C randomV o) :
    (∃ b, inspectOpening p q o.point o.value = some b ∧ b.holds τ) ∨
      o.value = (toPoly p).eval o.point := by
  have ⟨hp, _⟩ := hidingDefect_eval_trapdoor e vk hwf hind p r q s o hC hw hc
  by_cases hv : o.value = evalCoeffs p o.point
  · right
    rw [eval_toPoly]
    exact hv
  · left
    refine ⟨⟨openingDefect p q o.point o.value⟩, ?_, ?_⟩
    · simp [inspectOpening, hv]
    · exact ⟨toPoly_openingDefect_ne_zero hv, hp⟩

/-- A degree bound `deg g₁ ≤ |C| − 2` gives the lineval remainder bound
`deg (X g₁ + σ) < | C | ` that `univariate_sum` and `knowledgeSoundness` take. -/
theorem natDegree_X_mul_add_C_lt {g : F[X]} {n : Nat} (hn : 2 ≤ n) (hg : g.natDegree ≤ n - 2)
    (σ : F) : (X * g + C σ).natDegree < n := by
  have hX : (X * g).natDegree ≤ n - 1 := by
    calc (X * g).natDegree ≤ (X : F[X]).natDegree + g.natDegree := natDegree_mul_le
      _ ≤ 1 + (n - 2) := by gcongr; exact natDegree_X_le
      _ ≤ n - 1 := by omega
  calc (X * g + C σ).natDegree ≤ max (X * g).natDegree (C σ).natDegree := natDegree_add_le _ _
    _ ≤ n - 1 := by rw [natDegree_C]; exact max_le hX (Nat.zero_le _)
    _ < n := by omega

end Varuna