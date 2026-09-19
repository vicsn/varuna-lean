/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Polynomial.Div
import Varuna.AHP

/-!
# Sonic / KZG polynomial commitment (snarkVM `polycommit/sonic_pc`)

Varuna compiles AHP oracles through Sonic-KZG10 : labeled polynomials,
optional degree bounds, linear combinations (including the three
`LC_WITH_ZERO_EVAL` names), and batch openings.

Pairing groups stay abstract. The kernel checks :

* completeness of an honest KZG opening (`C = p(β)·g`, well-formed SRS)
* evaluation of linear combinations
* binding as *computed data* : two distinct openings of one commitment
  produce a pairing-product identity (the “PC forgery ⇒ pairing break
  structure” reduction). Hardness of that break is a floor.

Hiding (`random_v`, `gamma_g`) is parameterized; the first proofs use the
non-hiding check, matching `SNARKMode::NonZK`.
-/

set_option linter.unusedSectionVars false

open Polynomial List

namespace Varuna

variable {F : Type*} [Field F]

/-! ## Labeled polynomials and linear combinations -/

/-- snarkVM `PolynomialInfo`: label plus optional degree / hiding bounds. -/
structure PolynomialInfo where
  /-- Polynomial label (snarkVM `PolynomialLabel`). -/
  label : String
  /-- Enforced degree bound, if any (`g_1` uses `|C| - 2`). -/
  degreeBound : Option Nat
  /-- Hiding bound; `none` means NonZK. -/
  hidingBound : Option Nat

/-- snarkVM `LabeledPolynomial`. -/
structure LabeledPolynomial (F : Type*) [Semiring F] where
  /-- Label and bounds. -/
  info : PolynomialInfo
  /-- The underlying univariate polynomial. -/
  poly : F[X]

/-- Evaluate a labeled polynomial at a field point. -/
noncomputable def LabeledPolynomial.evaluate (p : LabeledPolynomial F) (z : F) : F :=
  p.poly.eval z

/-- The labeled polynomial respects its optional degree bound. -/
def LabeledPolynomial.respectsDegreeBound (p : LabeledPolynomial F) : Prop :=
  match p.info.degreeBound with
  | none => True
  | some d => p.poly.natDegree ≤ d

/-- A polynomial with no degree bound always respects it. -/
theorem respectsDegreeBound_none (p : LabeledPolynomial F)
    (h : p.info.degreeBound = none) : p.respectsDegreeBound := by
  simp [LabeledPolynomial.respectsDegreeBound, h]

/-- A polynomial with bound `d` respects it iff `natDegree ≤ d`. -/
theorem respectsDegreeBound_some (p : LabeledPolynomial F) {d : Nat}
    (h : p.info.degreeBound = some d) :
    p.respectsDegreeBound ↔ p.poly.natDegree ≤ d := by
  simp [LabeledPolynomial.respectsDegreeBound, h]

/-- snarkVM `LCTerm`. -/
inductive LCTerm where
  /-- Constant `1` (not committed). -/
  | one
  /-- Label of a committed polynomial. -/
  | polyLabel (label : String)
  deriving DecidableEq, Repr

/-- snarkVM `LinearCombination`. Duplicate terms add under evaluation. -/
structure LinearCombination (F : Type*) where
  /-- Combination label (`rowcheck_zerocheck`, `g_1`, …). -/
  label : String
  /-- `(coefficient, term)` list. -/
  terms : List (F × LCTerm)

/-- Empty labeled combination. -/
def LinearCombination.empty (label : String) : LinearCombination F :=
  ⟨label, []⟩

/-- Append a term (snarkVM `LinearCombination::add`). -/
def LinearCombination.add (lc : LinearCombination F) (c : F) (t : LCTerm) :
    LinearCombination F :=
  ⟨lc.label, (c, t) :: lc.terms⟩

/-- Evaluate a term given the constant `1` and a label → value map. -/
def LCTerm.value (t : LCTerm) (one : F) (polys : String → F) : F :=
  match t with
  | .one => one
  | .polyLabel l => polys l

/-- Evaluate a linear combination at a point (snarkVM `get_lc_eval`). -/
def LinearCombination.eval (lc : LinearCombination F) (one : F)
    (polys : String → F) : F :=
  (lc.terms.map fun tc => tc.1 * LCTerm.value tc.2 one polys).sum

/-- Empty combinations evaluate to zero. -/
@[simp] theorem LinearCombination.eval_empty (label : String) (one : F)
    (polys : String → F) :
    (LinearCombination.empty (F := F) label).eval one polys = 0 := by
  simp [LinearCombination.empty, LinearCombination.eval]

/-- Adding a term adds its contribution to the evaluation. -/
theorem LinearCombination.eval_add (lc : LinearCombination F) (c : F) (t : LCTerm)
    (one : F) (polys : String → F) :
    (lc.add c t).eval one polys =
      c * LCTerm.value t one polys + lc.eval one polys := by
  simp [LinearCombination.add, LinearCombination.eval]

/-- The three virtual combinations the AHP verifier requires to be zero. -/
theorem lcWithZeroEval_complete :
    lcWithZeroEval =
      ["matrix_sumcheck", "lineval_sumcheck", "rowcheck_zerocheck"] :=
  rfl

/-- Whether a combination is one of the three zero-evaluation LCs. -/
def LinearCombination.isZeroEval (lc : LinearCombination F) : Bool :=
  lc.label ∈ lcWithZeroEval

/-- The three AHP LC labels are classified as zero-evaluation. -/
theorem isZeroEval_ahp (label : String) (terms : List (F × LCTerm))
    (h : label ∈ lcWithZeroEval) :
    (⟨label, terms⟩ : LinearCombination F).isZeroEval = true := by
  simpa [LinearCombination.isZeroEval] using h

/-! ## Abstract pairing and KZG openings -/

/-- Bilinear pairing `e : G1 × G2 → GT`. Parameters are explicit so later
lemmas cannot leave `G1` as a metavariable. -/
structure Pairing (F : Type*) (G1 G2 GT : Type*) [Field F]
    [AddCommGroup G1] [AddCommGroup G2] [AddCommGroup GT]
    [Module F G1] [Module F G2] [Module F GT] where
  /-- The pairing map. -/
  pair : G1 → G2 → GT
  /-- Left additivity. -/
  map_add_left : ∀ a a' b, pair (a + a') b = pair a b + pair a' b
  /-- Right additivity. -/
  map_add_right : ∀ a b b', pair a (b + b') = pair a b + pair a b'
  /-- Left scalar multiplication. -/
  map_smul_left : ∀ (r : F) a b, pair (r • a) b = r • pair a b
  /-- Right scalar multiplication. -/
  map_smul_right : ∀ (r : F) a b, pair a (r • b) = r • pair a b

variable {G1 G2 GT : Type*}
  [AddCommGroup G1] [AddCommGroup G2] [AddCommGroup GT]
  [Module F G1] [Module F G2] [Module F GT]

/-- Left zero: `e(0, b) = 0`. -/
theorem Pairing.pair_zero_left (e : Pairing F G1 G2 GT) (b : G2) :
    e.pair 0 b = 0 := by
  have h := e.map_add_left 0 0 b
  simpa using h

/-- Right zero: `e(a, 0) = 0`. -/
theorem Pairing.pair_zero_right (e : Pairing F G1 G2 GT) (a : G1) :
    e.pair a 0 = 0 := by
  have h := e.map_add_right a 0 0
  simpa using h

/-- Left negation. -/
theorem Pairing.pair_neg_left (e : Pairing F G1 G2 GT) (a : G1) (b : G2) :
    e.pair (-a) b = -e.pair a b := by
  apply eq_neg_of_add_eq_zero_left
  rw [← e.map_add_left, neg_add_cancel, e.pair_zero_left]

/-- Right negation. -/
theorem Pairing.pair_neg_right (e : Pairing F G1 G2 GT) (a : G1) (b : G2) :
    e.pair a (-b) = -e.pair a b := by
  apply eq_neg_of_add_eq_zero_left
  rw [← e.map_add_right, neg_add_cancel, e.pair_zero_right]

/-- Left subtraction. -/
theorem Pairing.pair_sub_left (e : Pairing F G1 G2 GT) (a a' : G1) (b : G2) :
    e.pair (a - a') b = e.pair a b - e.pair a' b := by
  rw [sub_eq_add_neg, e.map_add_left, e.pair_neg_left, sub_eq_add_neg]

/-- Right subtraction. -/
theorem Pairing.pair_sub_right (e : Pairing F G1 G2 GT) (a : G1) (b b' : G2) :
    e.pair a (b - b') = e.pair a b - e.pair a b' := by
  rw [sub_eq_add_neg, e.map_add_right, e.pair_neg_right, sub_eq_add_neg]

/-- snarkVM KZG `VerifierKey` fields used by `KZG10::check` (non-hiding). -/
structure VerifyingKey (G1 G2 : Type*) where
  /-- `vk.g` in G1. -/
  g : G1
  /-- `vk.h` in G2. -/
  h : G2
  /-- `vk.beta_h = [β] h`. -/
  betaH : G2

/-- SRS well-formedness: `beta_h` is the trapdoor times `h`. -/
def VerifyingKey.wellFormed (vk : VerifyingKey G1 G2) (β : F) : Prop :=
  vk.betaH = β • vk.h

/-- A KZG evaluation proof (`KZGProof.w`) with claimed value. -/
structure Opening (G1 : Type*) (F : Type*) where
  /-- Evaluation point. -/
  point : F
  /-- Claimed evaluation. -/
  value : F
  /-- Witness `w ∈ G1`. -/
  witness : G1

/-- snarkVM `KZG10::check` without hiding: `e(C − v g, h) = e(w, βh − z h)`. -/
def kzgCheck (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    (C : G1) (o : Opening G1 F) : Prop :=
  e.pair (C - o.value • vk.g) vk.h = e.pair o.witness (vk.betaH - o.point • vk.h)

/-- Honest KZG commitment `p(β) · g` (trapdoor `β`; no hiding). -/
def kzgCommit (vk : VerifyingKey G1 G2) (β : F) (p : F[X]) : G1 :=
  p.eval β • vk.g

/-- Witness polynomial `q` with `p(X) − p(z) = (X − z) q(X)`. -/
noncomputable def kzgWitnessPoly (p : F[X]) (z : F) : F[X] :=
  (p - C (p.eval z)) /ₘ (X - C z)

/-- Honest opening of `p` at `z` under trapdoor `β`. -/
noncomputable def honestOpening (vk : VerifyingKey G1 G2) (β : F) (p : F[X])
    (z : F) : Opening G1 F :=
  ⟨z, p.eval z, (kzgWitnessPoly p z).eval β • vk.g⟩

/-- `p − p(z)` vanishes at `z`. -/
theorem eval_sub_eval (p : F[X]) (z : F) : (p - C (p.eval z)).eval z = 0 := by
  simp

/-- `X − z` divides `p − p(z)`. -/
theorem X_sub_C_dvd_sub_eval (p : F[X]) (z : F) : X - C z ∣ p - C (p.eval z) :=
  dvd_iff_isRoot.mpr (by simp [IsRoot.def])

/-- Algebraic identity `p(β) − p(z) = (β − z) q(β)`. -/
theorem eval_sub_eq_mul_witness (p : F[X]) (z β : F) :
    p.eval β - p.eval z = (β - z) * (kzgWitnessPoly p z).eval β := by
  have hdiv := X_sub_C_dvd_sub_eval p z
  have hmod : (p - C (p.eval z)) %ₘ (X - C z) = 0 :=
    (modByMonic_eq_zero_iff_dvd (monic_X_sub_C z)).2 hdiv
  have hdecomp := modByMonic_add_div (p - C (p.eval z)) (X - C z)
  have hpoly : p - C (p.eval z) = (X - C z) * kzgWitnessPoly p z := by
    unfold kzgWitnessPoly
    rw [hmod, zero_add] at hdecomp
    exact hdecomp.symm
  have := congrArg (eval β) hpoly
  simpa [eval_sub, eval_mul, eval_C, eval_X] using this

/-- Completeness: an honest opening of `p(β)·g` verifies against a well-formed SRS. -/
theorem kzgCheck_honest (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    {β : F} (hwf : vk.wellFormed β) (p : F[X]) (z : F) :
    kzgCheck e vk (kzgCommit vk β p) (honestOpening vk β p z) := by
  unfold kzgCheck kzgCommit honestOpening VerifyingKey.wellFormed at *
  rw [hwf]
  have hC : p.eval β • vk.g - p.eval z • vk.g = (p.eval β - p.eval z) • vk.g := by
    rw [← sub_smul]
  have hβ : β • vk.h - z • vk.h = (β - z) • vk.h := by
    rw [← sub_smul]
  rw [hC, hβ, e.map_smul_left, e.map_smul_left, e.map_smul_right, smul_smul]
  have hid := eval_sub_eq_mul_witness p z β
  rw [hid, mul_comm]

/-! ## Binding as computed break data -/

/-- Two openings of one commitment at one point with distinct claimed values. -/
structure BindingBreak (G1 : Type*) (F : Type*) where
  /-- The reused commitment. -/
  comm : G1
  /-- Common evaluation point. -/
  point : F
  /-- First claimed value. -/
  value₁ : F
  /-- Second claimed value. -/
  value₂ : F
  /-- First witness. -/
  witness₁ : G1
  /-- Second witness. -/
  witness₂ : G1

/-- The two claimed values really differ. -/
def BindingBreak.distinct (b : BindingBreak G1 F) : Prop :=
  b.value₁ ≠ b.value₂

/-- Pairing-product witness extracted from a binding break.
`e((v₂−v₁)·g, h) = e(w₁−w₂, βh − z h)`. -/
structure PairingBreak (G1 G2 : Type*) (F : Type*) where
  /-- Scalar `v₂ − v₁`. -/
  scalar : F
  /-- Left G1 argument `(v₂−v₁)·g`. -/
  g1elem : G1
  /-- Right G2 argument `βh − z h`. -/
  g2elem : G2
  /-- Witness difference `w₁ − w₂`. -/
  proofDiff : G1

/-- Inspect two openings of `C`: `some` is binding-break data. -/
def inspectBinding [DecidableEq F] (C : G1) (o₁ o₂ : Opening G1 F) :
    Option (BindingBreak G1 F) :=
  if o₁.point = o₂.point ∧ o₁.value ≠ o₂.value then
    some ⟨C, o₁.point, o₁.value, o₂.value, o₁.witness, o₂.witness⟩
  else
    none

/-- Distinct values at the same point are reported as a break. -/
theorem inspectBinding_some [DecidableEq F] {C : G1} {o₁ o₂ : Opening G1 F}
    (hp : o₁.point = o₂.point) (hv : o₁.value ≠ o₂.value) :
    inspectBinding C o₁ o₂ =
      some ⟨C, o₁.point, o₁.value, o₂.value, o₁.witness, o₂.witness⟩ := by
  simp [inspectBinding, hp, hv]

/-- No break is reported when the values agree. -/
theorem inspectBinding_none_of_eq [DecidableEq F] {C : G1} {o₁ o₂ : Opening G1 F}
    (hv : o₁.value = o₂.value) : inspectBinding C o₁ o₂ = none := by
  simp [inspectBinding, hv]

/-- Convert a binding break into a pairing-product witness against `vk`. -/
def BindingBreak.toPairingBreak (b : BindingBreak G1 F)
    (vk : VerifyingKey G1 G2) : PairingBreak G1 G2 F :=
  ⟨b.value₂ - b.value₁, (b.value₂ - b.value₁) • vk.g,
    vk.betaH - b.point • vk.h, b.witness₁ - b.witness₂⟩

/-- The extracted scalar is nonzero exactly when the values differ. -/
theorem toPairingBreak_scalar_ne {b : BindingBreak G1 F}
    (vk : VerifyingKey G1 G2) (hd : b.distinct) :
    (b.toPairingBreak vk).scalar ≠ 0 :=
  sub_ne_zero.2 (Ne.symm hd)

/-- Both openings of a binding break, packaged as `Opening`s. -/
def BindingBreak.opening₁ (b : BindingBreak G1 F) : Opening G1 F :=
  ⟨b.point, b.value₁, b.witness₁⟩

/-- Second opening of a binding break. -/
def BindingBreak.opening₂ (b : BindingBreak G1 F) : Opening G1 F :=
  ⟨b.point, b.value₂, b.witness₂⟩

/-- Pairing identity carried by a `PairingBreak`. -/
def PairingBreak.holds (br : PairingBreak G1 G2 F) (e : Pairing F G1 G2 GT)
    (vk : VerifyingKey G1 G2) : Prop :=
  e.pair br.g1elem vk.h = e.pair br.proofDiff br.g2elem

/-- PC forgery ⇒ pairing-break structure: two verifying openings with distinct
values yield a pairing-product identity with nonzero scalar. -/
theorem pairingBreak_of_double_opening (e : Pairing F G1 G2 GT)
    (vk : VerifyingKey G1 G2) (b : BindingBreak G1 F)
    (h₁ : kzgCheck e vk b.comm b.opening₁)
    (h₂ : kzgCheck e vk b.comm b.opening₂)
    (hd : b.distinct) :
    (b.toPairingBreak vk).holds e vk ∧ (b.toPairingBreak vk).scalar ≠ 0 := by
  refine ⟨?_, toPairingBreak_scalar_ne vk hd⟩
  unfold PairingBreak.holds BindingBreak.toPairingBreak kzgCheck
    BindingBreak.opening₁ BindingBreak.opening₂ at *
  have hsub :
      e.pair (b.comm - b.value₁ • vk.g) vk.h -
        e.pair (b.comm - b.value₂ • vk.g) vk.h =
        e.pair b.witness₁ (vk.betaH - b.point • vk.h) -
          e.pair b.witness₂ (vk.betaH - b.point • vk.h) := by
    rw [h₁, h₂]
  rw [← e.pair_sub_left] at hsub
  have hG :
      (b.comm - b.value₁ • vk.g) - (b.comm - b.value₂ • vk.g) =
        b.value₂ • vk.g - b.value₁ • vk.g := by
    abel
  rw [hG, ← sub_smul] at hsub
  rw [← e.pair_sub_left] at hsub
  exact hsub

/-- Accepting two openings at one point with distinct values is a binding break. -/
theorem inspectBinding_of_double_check [DecidableEq F]
    (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2) (C : G1)
    (o₁ o₂ : Opening G1 F)
    (h₁ : kzgCheck e vk C o₁) (h₂ : kzgCheck e vk C o₂)
    (hp : o₁.point = o₂.point) (hv : o₁.value ≠ o₂.value) :
    ∃ b : BindingBreak G1 F,
      inspectBinding C o₁ o₂ = some b ∧
        (b.toPairingBreak vk).holds e vk ∧
        (b.toPairingBreak vk).scalar ≠ 0 := by
  set b : BindingBreak G1 F :=
    ⟨C, o₁.point, o₁.value, o₂.value, o₁.witness, o₂.witness⟩
  refine ⟨b, inspectBinding_some hp hv, ?_⟩
  have h₁' : kzgCheck e vk b.comm b.opening₁ := h₁
  have h₂' : kzgCheck e vk b.comm b.opening₂ := by
    change e.pair (C - o₂.value • vk.g) vk.h =
      e.pair o₂.witness (vk.betaH - o₁.point • vk.h)
    rw [hp]
    exact h₂
  exact pairingBreak_of_double_opening e vk b h₁' h₂' hv

/-! ## Batch opening (two claims, one randomizer) -/

/-- Combined commitment `C₁ + ξ C₂` as in snarkVM `batch_check`. -/
def batchCommit (C₁ C₂ : G1) (ξ : F) : G1 :=
  C₁ + ξ • C₂

/-- Combined opening at a shared point. -/
def batchOpening (o₁ o₂ : Opening G1 F) (ξ : F) : Opening G1 F :=
  ⟨o₁.point, o₁.value + ξ * o₂.value, o₁.witness + ξ • o₂.witness⟩

/-- Bilinearity: if both openings at the same point verify, so does the
`ξ`-combination. -/
theorem kzgCheck_batch (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    {C₁ C₂ : G1} {o₁ o₂ : Opening G1 F} {ξ : F}
    (hp : o₁.point = o₂.point)
    (h₁ : kzgCheck e vk C₁ o₁) (h₂ : kzgCheck e vk C₂ o₂) :
    kzgCheck e vk (batchCommit C₁ C₂ ξ) (batchOpening o₁ o₂ ξ) := by
  unfold kzgCheck batchCommit batchOpening
  have hC :
      C₁ + ξ • C₂ - (o₁.value + ξ * o₂.value) • vk.g =
        (C₁ - o₁.value • vk.g) + ξ • (C₂ - o₂.value • vk.g) := by
    rw [add_smul, mul_smul, smul_sub]
    abel
  rw [hC, e.map_add_left, e.map_smul_left, h₁, h₂]
  have hD : vk.betaH - o₂.point • vk.h = vk.betaH - o₁.point • vk.h := by
    rw [hp]
  rw [hD, ← e.map_smul_left, ← e.map_add_left]

end Varuna