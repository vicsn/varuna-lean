/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Match
import Varuna.FiatShamir
import Varuna.Primality

/-!
# Knowledge-soundness capstone (VarunaVersion.V2)

Advertised endpoint : an accepting algebraic / FS transcript yields a
computable extractor that returns either AHP / batch / RO / PC break
data, or the identities that imply `Az ∘ Bz = Cz` on the constraint
domain.

The theorem is stated at a generic `Field`. `knowledgeSoundness_bls`
restates it at `ZMod bls12_377_r`, prime by the certificate in
`Primality.lean`. The six modelling floors in `modellingFloors` remain
explicit. Poseidon = RO, pairing / trapdoor
hardness, the algebraic-adversary restriction, SRS well-formedness,
encodings, and index = circuit are **not** Lean axioms.

`inspectResidual` is noncomputable (Mathlib polynomials). Fork, collision,
batch, and binding inspectors on field data stay computable `def`s.
-/

set_option linter.unusedSectionVars false

open Polynomial Finset

namespace Varuna

variable {F : Type*} [Field F]

/-- Breaks the extractor can return (Ironwood-style data, not `∃` in `Prop`). -/
inductive SoundnessBreak (F : Type*) where
  /-- Schwartz–Zippel hit on a named residual. -/
  | residual (tag : String) (x : F)
  /-- Lucky batch combination of a live claim. -/
  | batch (ws cs : List F)
  /-- Two oracles disagree at a shared prefix. -/
  | fork (fk : FSFork F)
  /-- Two prefixes squeeze to the same RO output. -/
  | collision (c : ROCollision F)

/-- Inspect the three AHP residuals at `α, β, γ`. -/
noncomputable def inspectAHP [DecidableEq F]
    (resR resL resM : F[X]) (α β γ : F) : Option (SoundnessBreak F) :=
  match inspectResidual resR α with
  | some x => some (.residual "rowcheck" x)
  | none =>
    match inspectResidual resL β with
    | some x => some (.residual "lineval" x)
    | none =>
      match inspectResidual resM γ with
      | some x => some (.residual "matrix" x)
      | none => none

/-- All three residuals clean iff `inspectAHP` returns none. -/
theorem inspectAHP_none [DecidableEq F] {resR resL resM : F[X]} {α β γ : F}
    (hR : inspectResidual resR α = none)
    (hL : inspectResidual resL β = none)
    (hM : inspectResidual resM γ = none) :
    inspectAHP resR resL resM α β γ = none := by
  simp [inspectAHP, hR, hL, hM]

/-- A `none` result means every residual inspector returned `none`. -/
theorem inspectAHP_eq_none_implies [DecidableEq F]
    {resR resL resM : F[X]} {α β γ : F}
    (h : inspectAHP resR resL resM α β γ = none) :
    inspectResidual resR α = none ∧
      inspectResidual resL β = none ∧
      inspectResidual resM γ = none := by
  unfold inspectAHP at h
  cases hR : inspectResidual resR α with
  | some _ => simp [hR] at h
  | none =>
    cases hL : inspectResidual resL β with
    | some _ => simp [hR, hL] at h
    | none =>
      cases hM : inspectResidual resM γ with
      | some _ => simp [hR, hL, hM] at h
      | none => exact ⟨rfl, rfl, rfl⟩

/-- Algebraic view of an accepting V2 transcript (post-decoding). The
polynomials are the prover's algebraic representations of its commitments
(`ModellingFloor.algebraicAdversary`); `inspectOpening_break` turns a
mismatch between a representation and an accepted opening into a
trapdoor break. -/
structure ProofView (F : Type*) [Field F] where
  /-- Constraint domain `H` / `R`. -/
  H : EvalDomain F
  /-- Nonzero / sparse domain `K`. -/
  K : EvalDomain F
  /-- Variable domain for the univariate sumcheck. -/
  Vd : EvalDomain F
  /-- Witness polynomials `z_A, z_B, z_C`. -/
  zA : F[X]
  /-- `z_B`. -/
  zB : F[X]
  /-- `z_C`. -/
  zC : F[X]
  /-- Rowcheck quotient `h₀`. -/
  h0 : F[X]
  /-- Lineval polynomial `f`. -/
  f : F[X]
  /-- Univariate witness `(h₁, g₁, σ₁)`. -/
  uw : UnivariateWitness F
  /-- Matrix `a(X)`. -/
  a : F[X]
  /-- Matrix `b(X)`. -/
  b : F[X]
  /-- Matrix remainder `g`. -/
  g : F[X]
  /-- Matrix quotient `h₂`. -/
  h₂ : F[X]
  /-- Matrix claimed sum `σ`. -/
  σ : F
  /-- Challenges `α, β, γ`. -/
  α : F
  /-- `β`. -/
  β : F
  /-- `γ`. -/
  γ : F
  /-- Batch combiners. -/
  batchWeights : List F
  /-- Batch claims. -/
  batchClaims : List F

/-- Rowcheck residual of a proof view. -/
noncomputable def ProofView.rowRes (π : ProofView F) : F[X] :=
  rowcheckResidual π.H π.zA π.zB π.zC π.h0

/-- Lineval residual of a proof view. -/
noncomputable def ProofView.lineRes (π : ProofView F) : F[X] :=
  univariateResidual π.Vd π.f π.uw

/-- Matrix residual of a proof view. -/
noncomputable def ProofView.matRes (π : ProofView F) : F[X] :=
  matrixResidual π.K π.a π.b π.g π.h₂ π.σ

/-- The three LC evaluations the V2 verifier requires to vanish. -/
noncomputable def ProofView.checks (π : ProofView F) : AHPVerifierChecks F :=
  ⟨rowcheckEval π.H π.zA π.zB π.zC π.h0 π.α,
    univariateEval π.Vd π.f π.uw π.β,
    matrixEval π.K π.a π.b π.g π.h₂ π.σ π.γ⟩

/-- Extractor: AHP residual breaks first, then a batch break. -/
noncomputable def ProofView.inspect [DecidableEq F] (π : ProofView F) :
    Option (SoundnessBreak F) :=
  match inspectAHP π.rowRes π.lineRes π.matRes π.α π.β π.γ with
  | some b => some b
  | none =>
    match inspectBatch π.batchWeights π.batchClaims with
    | some (ws, cs) => some (.batch ws cs)
    | none => none

/-- `inspect = none` implies clean AHP residuals and no batch break. -/
theorem ProofView.inspect_eq_none [DecidableEq F] {π : ProofView F}
    (h : π.inspect = none) :
    inspectAHP π.rowRes π.lineRes π.matRes π.α π.β π.γ = none ∧
      inspectBatch π.batchWeights π.batchClaims = none := by
  unfold ProofView.inspect at h
  cases hA : inspectAHP π.rowRes π.lineRes π.matRes π.α π.β π.γ with
  | some _ => simp [hA] at h
  | none =>
    cases hB : inspectBatch π.batchWeights π.batchClaims with
    | some _ => simp [hA, hB] at h
    | none => exact ⟨rfl, rfl⟩

/-- Same-point openings with no binding break have equal claimed values. -/
theorem inspectBinding_none_same_point [DecidableEq F]
    {G1 : Type*} [AddCommGroup G1] [Module F G1] {C : G1} {o₁ o₂ : Opening G1 F}
    (hp : o₁.point = o₂.point) (h : inspectBinding C o₁ o₂ = none) :
    o₁.value = o₂.value := by
  by_contra hv
  have := inspectBinding_some (C := C) hp hv
  simp [this] at h

/-- Knowledge soundness at a generic field: accepting LCs, no computed
AHP/batch break, and the univariate degree bound, yield the three domain
identities and an all-zero batch. -/
theorem knowledgeSoundness [DecidableEq F] {π : ProofView F}
    (hacc : π.checks.accepts)
    (hsum : weightedSum π.batchWeights π.batchClaims = 0)
    (hI : π.inspect = none)
    (hdeg : (X * π.uw.g + C π.uw.σ).natDegree < π.Vd.n)
    {κ μ : F} (hκ : κ ∈ π.H.elements) (hμ : μ ∈ π.K.elements) :
    π.zA.eval κ * π.zB.eval κ = π.zC.eval κ ∧
      (∑ i ∈ range π.Vd.n, π.f.eval (π.Vd.node i) = (π.Vd.n : F) * π.uw.σ) ∧
      π.a.eval μ = π.b.eval μ * (μ * π.g.eval μ + π.σ) ∧
      ∀ x ∈ π.batchClaims, x = 0 := by
  have ⟨hAHP, hB⟩ := ProofView.inspect_eq_none hI
  have ⟨hR, hL, hM⟩ := inspectAHP_eq_none_implies hAHP
  have ⟨hr, hl, hm⟩ := hacc
  refine ⟨?_, ?_, ?_, inspectBatch_accepts hsum hB⟩
  · exact rowcheck_extract hr hR hκ
  · exact univariate_extract hl hL hdeg
  · exact matrix_extract hm hM hμ

/-- Accepting typed toy proofs are accepted by the Boolean predicate. -/
theorem knowledgeSoundness_toy_typed :
    (⟨⟨0, 0, 0⟩, [], []⟩ : TypedProof ToyField).accepts = true :=
  toy_typed_proof_accepts

/-- One public-coin round of Marlin's preprocessing argument. -/
structure CoinRound (F : Type*) where
  /-- Prover message absorbed before the squeeze. -/
  sent : FSMessage F
  /-- Verifier challenge squeezed from that prefix. -/
  challenge : F

/-- The interactive object: public-coin rounds, with `ProofView` the
algebraic projection of the committed polynomials. -/
structure PreprocessingAHP (F : Type*) [Field F] where
  /-- Rounds, in transcript order. -/
  rounds : List (CoinRound F)
  /-- Polynomials and challenges read off those rounds. -/
  view : ProofView F

/-- The challenges of the algebraic view are challenges of the interaction,
and the view is knowledge-sound. -/
theorem PreprocessingAHP.sound [DecidableEq F] (π : PreprocessingAHP F)
    (hα : π.view.α ∈ π.rounds.map (·.challenge))
    (hβ : π.view.β ∈ π.rounds.map (·.challenge))
    (hγ : π.view.γ ∈ π.rounds.map (·.challenge))
    (hacc : π.view.checks.accepts)
    (hsum : weightedSum π.view.batchWeights π.view.batchClaims = 0)
    (hI : π.view.inspect = none)
    (hdeg : (X * π.view.uw.g + C π.view.uw.σ).natDegree < π.view.Vd.n)
    {κ μ : F} (hκ : κ ∈ π.view.H.elements) (hμ : μ ∈ π.view.K.elements) :
    π.view.α ∈ π.rounds.map (·.challenge) ∧
      π.view.β ∈ π.rounds.map (·.challenge) ∧
      π.view.γ ∈ π.rounds.map (·.challenge) ∧
      π.view.zA.eval κ * π.view.zB.eval κ = π.view.zC.eval κ ∧
        (∑ i ∈ range π.view.Vd.n, π.view.f.eval (π.view.Vd.node i) =
          (π.view.Vd.n : F) * π.view.uw.σ) ∧
        π.view.a.eval μ = π.view.b.eval μ * (μ * π.view.g.eval μ + π.view.σ) ∧
        ∀ x ∈ π.view.batchClaims, x = 0 := by
  refine ⟨hα, hβ, hγ, ?_⟩
  exact knowledgeSoundness hacc hsum hI hdeg hκ hμ

/-- The capstone at the BLS12-377 scalar field. -/
theorem knowledgeSoundness_bls [DecidableEq (ZMod bls12_377_r)]
    {π : ProofView (ZMod bls12_377_r)}
    (hacc : π.checks.accepts)
    (hsum : weightedSum π.batchWeights π.batchClaims = 0)
    (hI : π.inspect = none)
    (hdeg : (X * π.uw.g + C π.uw.σ).natDegree < π.Vd.n)
    {κ μ : ZMod bls12_377_r} (hκ : κ ∈ π.H.elements) (hμ : μ ∈ π.K.elements) :
    π.zA.eval κ * π.zB.eval κ = π.zC.eval κ ∧
      (∑ i ∈ range π.Vd.n, π.f.eval (π.Vd.node i) = (π.Vd.n : ZMod bls12_377_r) * π.uw.σ) ∧
      π.a.eval μ = π.b.eval μ * (μ * π.g.eval μ + π.σ) ∧
      ∀ x ∈ π.batchClaims, x = 0 :=
  knowledgeSoundness hacc hsum hI hdeg hκ hμ

/-- The capstone still rests on the named modelling floors. -/
theorem knowledgeSoundness_rests_on_floors :
    ModellingFloor.poseidonRO ∈ modellingFloors ∧
      ModellingFloor.pairingHardness ∈ modellingFloors ∧
      ModellingFloor.algebraicAdversary ∈ modellingFloors ∧
      ModellingFloor.srs ∈ modellingFloors ∧
      ModellingFloor.byteEncodings ∈ modellingFloors ∧
      ModellingFloor.indexEqualsCircuit ∈ modellingFloors := by
  decide

end Varuna