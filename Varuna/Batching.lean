/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.FiatShamir

/-!
# Multi-circuit / multi-instance batching (VarunaVersion.V2)

Sage is single-circuit. snarkVM batches circuits `i` and instances `j`
with random linear combinations and selector polynomials that lift a
subdomain identity to the common domain `R` :

\[
  \sum_i \nu_i s_{R,R_i}(X) \sum_j \tau_{i,j} (z_{A,ij} z_{B,ij} - z_{C,ij})
    = h_0(X)\, v_R(X).
\]

The first combiner of each family is `1` (not squeezed). V2's extra
`prepare_third` round absorbs instance sums *before* squeezing `η_b, η_c`
and the third-round combiners, so those challenges cannot be chosen
after seeing verifier randomness from the second squeeze (`α` only).

Soundness of a combination is Ironwood-style : `inspectBatch` returns
the claims and combiners when the weighted sum is zero but some claim
is not.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace Varuna

variable {F : Type*} [Field F]

/-! ## Combiners (snarkVM `BatchCombiners`) -/

/-- snarkVM `BatchCombiners` for one circuit : `ν_i` and `{τ_{i,j}}`. -/
structure BatchCombiners (F : Type*) where
  /-- Circuit combiner `ν_i`; the first circuit uses `1`. -/
  circuitCombiner : F
  /-- Instance combiners `τ_{i,j}`; the first instance uses `1`. -/
  instanceCombiners : List F

/-- First circuit / instance combiner is the constant `1`. -/
def firstCombiner : F :=
  1

/-- Circuit combiners : `ν_1 = 1`, the rest are squeezed. -/
def circuitCombiners (rest : List F) : List F :=
  firstCombiner :: rest

/-- Instance combiners : `τ_{i,1} = 1`, the rest are squeezed. -/
def instanceCombiners (rest : List F) : List F :=
  firstCombiner :: rest

/-- The head of the circuit-combiner list is `1`. -/
@[simp] theorem circuitCombiners_head (rest : List F) :
    (circuitCombiners rest).head? = some (1 : F) :=
  rfl

/-- The head of the instance-combiner list is `1`. -/
@[simp] theorem instanceCombiners_head (rest : List F) :
    (instanceCombiners rest).head? = some (1 : F) :=
  rfl

/-- Matrix combiners `η_A, η_B, η_C` with `η_A = 1` (snarkVM). -/
structure MatrixCombiners (F : Type*) where
  /-- `η_A = 1`, not squeezed. -/
  etaA : F
  /-- `η_B`, squeezed in V2 prepare-third. -/
  etaB : F
  /-- `η_C`, squeezed in V2 prepare-third. -/
  etaC : F

/-- V2 / snarkVM packing : `η_A = 1`. -/
def MatrixCombiners.ofEtaBC (etaB etaC : F) : MatrixCombiners F :=
  ⟨1, etaB, etaC⟩

/-- `η_A` is identically one. -/
@[simp] theorem etaA_eq_one (etaB etaC : F) :
    (MatrixCombiners.ofEtaBC etaB etaC).etaA = 1 :=
  rfl

/-- Fourth-round `δ_A, δ_B, δ_C` for the first circuit (`δ_A = 1`). -/
structure DeltaCombiners (F : Type*) where
  /-- `δ_A`; first circuit uses `1`. -/
  deltaA : F
  /-- `δ_B`. -/
  deltaB : F
  /-- `δ_C`. -/
  deltaC : F

/-- First-circuit deltas : `δ_A = 1`. -/
def DeltaCombiners.first (deltaB deltaC : F) : DeltaCombiners F :=
  ⟨1, deltaB, deltaC⟩

/-- First-circuit `δ_A` is one. -/
@[simp] theorem deltaA_first_eq_one (deltaB deltaC : F) :
    (DeltaCombiners.first deltaB deltaC).deltaA = 1 :=
  rfl

/-! ## Weighted sums and batch-break data -/

section CommRing

variable {R : Type*} [CommRing R]

/-- Weighted sum `∑ wᵢ cᵢ` (snarkVM batch combination of field claims). Over a
commutative ring : the captured proof is over `ZMod q`, a field only under a
primality `Fact`. -/
def weightedSum : List R → List R → R
  | [], _ => 0
  | _, [] => 0
  | w :: ws, c :: cs => w * c + weightedSum ws cs

/-- Empty weights yield zero. -/
@[simp] theorem weightedSum_nil_weights (cs : List R) : weightedSum [] cs = 0 :=
  rfl

/-- Empty claims yield zero. -/
@[simp] theorem weightedSum_nil_claims : ∀ ws : List R, weightedSum ws [] = 0
  | [] => rfl
  | _ :: _ => rfl

/-- Cons cell of a weighted sum. -/
@[simp] theorem weightedSum_cons (w c : R) (ws cs : List R) :
    weightedSum (w :: ws) (c :: cs) = w * c + weightedSum ws cs :=
  rfl

/-- A list of zeros is a zero combination, for any weights. -/
theorem weightedSum_all_zero :
    ∀ (ws cs : List R), (∀ x ∈ cs, x = 0) → weightedSum ws cs = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | w :: ws, c :: cs, h => by
    have hc : c = 0 := h c (by simp)
    have hcs : ∀ x ∈ cs, x = 0 := fun x hx => h x (by simp [hx])
    simp [hc, weightedSum_all_zero ws cs hcs]

end CommRing

/-- Whether a claim list has a nonzero entry (Bool, for `inspectBatch`). -/
def hasNonzero [DecidableEq F] : List F → Bool
  | [] => false
  | c :: cs => decide (c ≠ 0) || hasNonzero cs

/-- `hasNonzero` is true iff some claim is nonzero. -/
theorem hasNonzero_iff [DecidableEq F] :
    ∀ cs : List F, hasNonzero cs = true ↔ ∃ c ∈ cs, c ≠ 0
  | [] => by simp [hasNonzero]
  | c :: cs => by
    simp [hasNonzero, Bool.or_eq_true, hasNonzero_iff cs, List.mem_cons]

/-- Inspect a batch : `some` iff the combination accepts but a claim is live. -/
def inspectBatch [DecidableEq F] (ws cs : List F) : Option (List F × List F) :=
  if decide (weightedSum ws cs = 0) && hasNonzero cs then some (ws, cs) else none

/-- A lucky combination of a live claim is reported. -/
theorem inspectBatch_some [DecidableEq F] {ws cs : List F}
    (hacc : weightedSum ws cs = 0) (hne : ∃ c ∈ cs, c ≠ 0) :
    inspectBatch ws cs = some (ws, cs) := by
  have hb : hasNonzero cs = true := (hasNonzero_iff cs).2 hne
  simp [inspectBatch, hacc, hb]

/-- All-zero claims are never a batch break. -/
theorem inspectBatch_none_of_all_zero [DecidableEq F] {ws cs : List F}
    (h : ∀ x ∈ cs, x = 0) : inspectBatch ws cs = none := by
  have hb : hasNonzero cs = false := by
    rw [Bool.eq_false_iff, Ne, hasNonzero_iff]
    exact fun ⟨x, hx, hne⟩ => hne (h x hx)
  simp [inspectBatch, hb]

/-- Accepting combination with no break data means every claim is zero. -/
theorem inspectBatch_accepts [DecidableEq F] {ws cs : List F}
    (hacc : weightedSum ws cs = 0) (hnone : inspectBatch ws cs = none) :
    ∀ c ∈ cs, c = 0 := by
  intro c hc
  by_contra hne
  have := inspectBatch_some hacc ⟨c, hc, hne⟩
  simp [this] at hnone

/-- Inspect a combination of claims indexed by the points of `D`, on all of `D` at
once : `some ws` iff the combination vanishes at every point of `D` but some
claim is live at some point. `D` is a list because deciding a quantifier over a
`Finset` goes through `Classical.choice`. -/
def inspectBatchOn [DecidableEq F] (D : List F) (ws : List F) (claims : F → List F) :
    Option (List F) :=
  if (∀ x ∈ D, weightedSum ws (claims x) = 0) ∧ ∃ x ∈ D, ∃ c ∈ claims x, c ≠ 0 then some ws
  else none

/-- `inspectBatchOn` reports data exactly when the combination vanishes on `D` and a
claim is live. -/
theorem inspectBatchOn_ne_none_iff [DecidableEq F] (D : List F) (ws : List F)
    (claims : F → List F) :
    inspectBatchOn D ws claims ≠ none ↔
      (∀ x ∈ D, weightedSum ws (claims x) = 0) ∧
        ∃ x ∈ D, ∃ c ∈ claims x, c ≠ 0 := by
  unfold inspectBatchOn
  split_ifs with h
  · exact iff_of_true (by simp) h
  · exact iff_of_false (by simp) h

/-- Accepting on all of `D` with no break data means every claim is zero on `D`. -/
theorem inspectBatchOn_accepts [DecidableEq F] {D : List F} {ws : List F}
    {claims : F → List F} (hacc : ∀ x ∈ D, weightedSum ws (claims x) = 0)
    (hnone : inspectBatchOn D ws claims = none) : ∀ x ∈ D, ∀ c ∈ claims x, c = 0 := by
  intro x hx c hc
  by_contra hne
  exact (inspectBatchOn_ne_none_iff D ws claims).2 ⟨hacc, x, hx, c, hc, hne⟩ hnone

/-- No break at any single point of `D` means no break on `D`. -/
theorem inspectBatchOn_eq_none_of_pointwise [DecidableEq F] {D : List F} {ws : List F}
    {claims : F → List F} (h : ∀ x ∈ D, inspectBatch ws (claims x) = none) :
    inspectBatchOn D ws claims = none := by
  by_contra hne
  obtain ⟨hacc, x, hx, c, hc, hc0⟩ := (inspectBatchOn_ne_none_iff D ws claims).1 hne
  exact hc0 (inspectBatch_accepts (hacc x hx) (h x hx) c hc)

/-! ## Selector polynomials `s_{H, H_i}` -/

/-- Nested FFT domains : a smaller power-of-two size divides a larger one. -/
theorem powTwo_dvd_of_le {n m : Nat} (hn : PowTwo n) (hm : PowTwo m)
    (hle : n ≤ m) : n ∣ m := by
  have ⟨a, ha⟩ := (PowTwo.iff_isPowerOfTwo).1 hn
  have ⟨b, hb⟩ := (PowTwo.iff_isPowerOfTwo).1 hm
  subst ha; subst hb
  have : a ≤ b := (Nat.pow_le_pow_iff_right (by decide : (1 : Nat) < 2)).1 hle
  exact pow_dvd_pow (2 : Nat) this

/-- A smaller evaluation domain's cardinality divides a larger one's. -/
theorem nested_domain_card_dvd (H Hi : EvalDomain F) (hle : Hi.n ≤ H.n) :
    Hi.n ∣ H.n :=
  powTwo_dvd_of_le Hi.hn H.hn hle

/-- Geometric quotient `(X^{|H|} - 1) / (X^{|H_i|} - 1)`. -/
noncomputable def selectorGeom (H Hi : EvalDomain F) : F[X] :=
  ∑ i ∈ range (H.n / Hi.n), (X ^ Hi.n) ^ i

/-- snarkVM `H.selector_polynomial(H_i) = (v_H / v_{H_i}) * (|H_i| / |H|)`.
The size ratio is required so the selector is `1` on `H_i` and `0` on
`H \ H_i` (see `snarkVM/.../ahp/selectors.rs`). -/
noncomputable def selectorPoly (H Hi : EvalDomain F) : F[X] :=
  C (Hi.sizeAsField * H.sizeInv) * selectorGeom H Hi

/-- On equal domains the selector is `1`. -/
theorem selectorPoly_self (H : EvalDomain F) : selectorPoly H H = 1 := by
  unfold selectorPoly selectorGeom
  rw [Nat.div_self H.n_pos, sum_range_one, pow_zero, H.mul_sizeInv]
  simp

/-- `X^n - 1` divides `X^m - 1` when `n` divides `m`. -/
theorem vanishing_dvd_of_card_dvd (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) :
    Hi.vanishing ∣ H.vanishing := by
  unfold EvalDomain.vanishing
  convert dvd_pow_sub_one_of_dvd (r := (X : F[X])) hdvd using 1 <;> simp

/-- The unscaled geometric quotient times `v_{H_i}` is `v_H`. -/
theorem selectorGeom_mul_vanishing (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) :
    selectorGeom H Hi * Hi.vanishing = H.vanishing := by
  have hdiv : Hi.n * (H.n / Hi.n) = H.n := Nat.mul_div_cancel' hdvd
  unfold selectorGeom EvalDomain.vanishing
  have hgeom := geom_sum_mul ((X : F[X]) ^ Hi.n) (H.n / Hi.n)
  rw [← pow_mul, hdiv] at hgeom
  convert hgeom using 2 <;> simp

/-- The deployed selector times `v_{H_i}` is `(|H_i|/|H|) v_H`. -/
theorem selector_mul_vanishing (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) :
    selectorPoly H Hi * Hi.vanishing =
      C (Hi.sizeAsField * H.sizeInv) * H.vanishing := by
  unfold selectorPoly
  rw [mul_assoc, selectorGeom_mul_vanishing H Hi hdvd]

/-- A residual that is a multiple of `v_{H_i}` lifts with the snarkVM scale. -/
theorem lift_residual (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) (h f : F[X])
    (hf : f = h * Hi.vanishing) :
    selectorPoly H Hi * f =
      C (Hi.sizeAsField * H.sizeInv) * h * H.vanishing := by
  rw [hf, mul_left_comm, selector_mul_vanishing H Hi hdvd]
  ring

/-- Honest two-circuit rowcheck batching with snarkVM selectors. -/
theorem batched_rowcheck_two (H H1 H2 : EvalDomain F)
    (hd1 : H1.n ∣ H.n) (hd2 : H2.n ∣ H.n)
    (h1 f1 h2 f2 : F[X]) (ν : F)
    (hf1 : f1 = h1 * H1.vanishing) (hf2 : f2 = h2 * H2.vanishing) :
    selectorPoly H H1 * f1 + C ν * (selectorPoly H H2 * f2) =
      (C (H1.sizeAsField * H.sizeInv) * h1 +
        C ν * C (H2.sizeAsField * H.sizeInv) * h2) * H.vanishing := by
  rw [lift_residual H H1 hd1 h1 f1 hf1, lift_residual H H2 hd2 h2 f2 hf2]
  ring

/-- Point evaluation matches snarkVM `evaluate_selector_polynomial`. -/
theorem selectorPoly_eval (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n) {α : F}
    (hα : Hi.vanishing.eval α ≠ 0) :
    (selectorPoly H Hi).eval α =
      H.vanishing.eval α * Hi.sizeAsField /
        (Hi.vanishing.eval α * H.sizeAsField) := by
  have hgeom := congrArg (eval α) (selectorGeom_mul_vanishing H Hi hdvd)
  simp only [eval_mul] at hgeom
  have hdiv : (selectorGeom H Hi).eval α =
      H.vanishing.eval α / Hi.vanishing.eval α :=
    (eq_div_iff_mul_eq hα).2 hgeom
  unfold selectorPoly
  simp [eval_mul, eval_C, hdiv, EvalDomain.sizeInv, EvalDomain.sizeAsField]
  field_simp

/-- Polynomial weighted sum of residuals (circuit-level batching). -/
noncomputable def weightedSumPoly : List F → List (F[X]) → F[X]
  | [], _ => 0
  | _, [] => 0
  | w :: ws, p :: ps => C w * p + weightedSumPoly ws ps

/-- Empty weights yield the zero polynomial. -/
@[simp] theorem weightedSumPoly_nil_weights (ps : List (F[X])) :
    weightedSumPoly [] ps = 0 :=
  rfl

/-- Evaluating a polynomial combination is the field combination of evaluations. -/
theorem eval_weightedSumPoly (α : F) :
    ∀ ws ps, (weightedSumPoly ws ps).eval α =
      weightedSum ws (ps.map fun p => p.eval α)
  | [], _ => by simp [weightedSumPoly]
  | _ :: _, [] => by simp [weightedSumPoly]
  | w :: ws, p :: ps => by
    simp [weightedSumPoly, eval_weightedSumPoly α ws ps]

/-- Honest combination of zero residuals is the zero polynomial. -/
theorem weightedSumPoly_zero_of_zero :
    ∀ (ws : List F) (ps : List (F[X])), (∀ p ∈ ps, p = 0) →
      weightedSumPoly ws ps = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | w :: ws, p :: ps, h => by
    have hp : p = 0 := h p (by simp)
    have hps : ∀ q ∈ ps, q = 0 := fun q hq => h q (by simp [hq])
    simp [weightedSumPoly, hp, weightedSumPoly_zero_of_zero ws ps hps]

/-! ## Squeeze counts and the extra round -/

/-- Layout of a multi-circuit batch (`|D|` and `{D_i}`). -/
structure BatchLayout where
  /-- Number of circuits. -/
  nCircuits : Nat
  /-- Instance count per circuit. -/
  nInstances : List Nat

/-- Total instances `∑_i D_i`. -/
def BatchLayout.totalInstances (b : BatchLayout) : Nat :=
  b.nInstances.sum

/-- First-round squeezes for one circuit : `D_i - 1` instance combiners,
plus a circuit combiner unless this is the first circuit. -/
def firstRoundSqueezeCount (nInstances : Nat) (isFirstCircuit : Bool) : Nat :=
  nInstances.pred + bif isFirstCircuit then 0 else 1

/-- The first circuit does not squeeze `ν` (`ν_1 = 1`). -/
@[simp] theorem firstRoundSqueezeCount_first (n : Nat) :
    firstRoundSqueezeCount n true = n.pred :=
  rfl

/-- Later circuits squeeze one extra field (the circuit combiner). -/
@[simp] theorem firstRoundSqueezeCount_later (n : Nat) :
    firstRoundSqueezeCount n false = n.pred + 1 :=
  rfl

/-- Extra field elements squeezed in V2 prepare-third after the combiners
(`η_b, η_c`). V3 squeezes three (`η_a, η_b, η_c`); see `prepareThirdEtaSqueeze`. -/
def prepareThirdExtraSqueeze : Nat :=
  2

/-- V2 prepare-third squeezes two extra challenges that V1 drew with `α`. -/
@[simp] theorem prepareThirdExtraSqueeze_eq : prepareThirdExtraSqueeze = 2 :=
  rfl

/-- How many matrix weights prepare-third squeezes. V1 draws them with `α`.
V2 squeezes `η_B, η_C` and fixes `η_A = 1`. V3 squeezes all three. -/
def prepareThirdEtaSqueeze : VarunaVersion → Nat
  | .V1 => 0
  | .V2 => 2
  | .V3 => 3

/-- V3 prepare-third squeezes `η_A` as well as `η_B, η_C`. -/
@[simp] theorem prepareThirdEtaSqueeze_V3 : prepareThirdEtaSqueeze .V3 = 3 :=
  rfl

/-- V2 prepare-third still squeezes only `η_B, η_C`. -/
@[simp] theorem prepareThirdEtaSqueeze_V2 : prepareThirdEtaSqueeze .V2 = 2 :=
  rfl

/-- The prepare-third *message* (instance sums) sits in the η-prefix. -/
theorem prepareThird_mem_before (t : V2Transcript F) :
    t.prepareThird ∈ t.before .prepareThird := by
  simp [V2Transcript.before]

/-- `α` is squeezed from a prefix that does not include prepare-third. -/
theorem before_alpha_eq (t : V2Transcript F) :
    t.before .alpha = t.init ++ [t.first, t.second] :=
  rfl

/-- Two transcripts that agree up to the second round have the same `α`.
Instance sums in `prepareThird` cannot shift `α` (they are absorbed later). -/
theorem alpha_independent_of_prepareThird (ro : RO F) {t₁ t₂ : V2Transcript F}
    (hi : t₁.init = t₂.init) (hf : t₁.first = t₂.first)
    (hs : t₁.second = t₂.second) :
    t₁.challenge ro .alpha = t₂.challenge ro .alpha := by
  simp [V2Transcript.challenge, V2Transcript.before, hi, hf, hs]

/-- `η_b, η_c` (the prepare-third squeeze) are a function of a prefix that
*does* contain the instance sums, blocking adaptive statement selection. -/
theorem prepareThird_challenge_eq (ro : RO F) (t : V2Transcript F) :
    t.challenge ro .prepareThird =
      ro (t.init ++ [t.first, t.second, t.prepareThird]) :=
  rfl

/-- V2 and V3 have the extra round; V1 does not. -/
theorem hasPrepareThird_iff (v : VarunaVersion) :
    hasPrepareThird v = true ↔ v = .V2 ∨ v = .V3 := by
  cases v <;> simp

end Varuna