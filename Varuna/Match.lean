/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Batching
import Varuna.SonicPC
import Varuna.Field

/-!
# Deployed-verifier faithfulness (typed, post-decoding)

Ironwood's fingerprint pattern : a Lean model of the *assembled
accept predicate* next to named modelling floors. This is not a
byte-level refinement of snarkVM. Domain-separator bytes, field/group
encodings, and Poseidon parameters stay out of Lean.

Fixtures are closed facts on `ToyField = ZMod 17`, kernel-checked with
`decide` (not `native_decide`, which would extend the trusted base).
Captured snarkVM / Sage proofs over BLS12-377 are future pins; the
typed equation they must satisfy is the one below.
-/

set_option linter.unusedSectionVars false

namespace Varuna

variable {F : Type*} [Field F]

/-! ## Modelling floors (out of Lean, not axioms) -/

/-- Identifications the kernel does not and will not check. -/
inductive ModellingFloor where
  /-- Poseidon sponge = programmable random oracle. -/
  | poseidonRO
  /-- Pairing-product and trapdoor-recovery (q-DLOG) breaks are infeasible. -/
  | pairingHardness
  /-- The prover is algebraic: it outputs SRS representations of its group elements. -/
  | algebraicAdversary
  /-- Universal SRS is well-formed; toxic waste is unknown. -/
  | srs
  /-- Domain separators, encodings, Poseidon parameters. -/
  | byteEncodings
  /-- Verifying key is the holographic index of the claimed circuit. -/
  | indexEqualsCircuit
  deriving DecidableEq, Repr

/-- Human-readable name of a floor. -/
def ModellingFloor.description : ModellingFloor → String
  | .poseidonRO => "Poseidon sponge = programmable RO"
  | .pairingHardness => "pairing-product and SRS-trapdoor (q-DLOG) breaks are hard on BLS12-377"
  | .algebraicAdversary => "the prover outputs SRS representations of its group elements"
  | .srs => "universal SRS well-formed, trapdoor unknown"
  | .byteEncodings => "domain-separator bytes and field/group encodings"
  | .indexEqualsCircuit => "verifying key indexes the claimed circuit"

/-- Every floor is an out-of-Lean identification, never a Lean `axiom`. -/
def ModellingFloor.isFloor (_ : ModellingFloor) : Bool :=
  true

/-- The floors the capstone still rests on. -/
def modellingFloors : List ModellingFloor :=
  [.poseidonRO, .pairingHardness, .algebraicAdversary, .srs, .byteEncodings,
    .indexEqualsCircuit]

/-- There are six named floors. -/
@[simp] theorem modellingFloors_length : modellingFloors.length = 6 :=
  rfl

/-- Poseidon = RO is among the floors. -/
theorem poseidonRO_mem_floors : ModellingFloor.poseidonRO ∈ modellingFloors :=
  by decide

/-! ## snarkVM name correspondence (typed) -/

/-- The three LC labels snarkVM requires to evaluate to zero. -/
theorem lcNames_match_snarkVM :
    lcWithZeroEval =
      ["matrix_sumcheck", "lineval_sumcheck", "rowcheck_zerocheck"] :=
  rfl

/-- Query-set challenge names used by snarkVM `QuerySet`. -/
def queryChallengeNames : List String :=
  ["alpha", "beta", "gamma"]

/-- The query names are exactly the three AHP challenges. -/
@[simp] theorem queryChallengeNames_eq :
    queryChallengeNames = ["alpha", "beta", "gamma"] :=
  rfl

/-- Deployed protocol version. -/
def deployedVersion : VarunaVersion :=
  .V2

/-- The target version is V2. -/
@[simp] theorem deployedVersion_eq : deployedVersion = .V2 :=
  rfl

/-- V2 includes the extra prepare-third round. -/
@[simp] theorem deployed_hasPrepareThird :
    hasPrepareThird deployedVersion = true :=
  rfl

/-! ## Typed accept predicate -/

/-- Boolean AHP accept: the three zero-eval LCs vanish. -/
def typedAHPAccepts [DecidableEq F] (c : AHPVerifierChecks F) : Bool :=
  decide (c.rowcheck = 0) && decide (c.lineval = 0) && decide (c.matrix = 0)

/-- Boolean accept agrees with the Prop accept. -/
theorem typedAHPAccepts_iff [DecidableEq F] (c : AHPVerifierChecks F) :
    typedAHPAccepts c = true ↔ c.accepts := by
  simp [typedAHPAccepts, AHPVerifierChecks.accepts, Bool.and_eq_true, and_assoc]

/-- Batch accept: the combination is zero and no live (nonzero) claim. -/
def typedBatchAccepts [DecidableEq F] (ws cs : List F) : Bool :=
  decide (weightedSum ws cs = 0) && !hasNonzero cs

/-- Batch accept iff the combination vanishes and every claim is zero. -/
theorem typedBatchAccepts_iff [DecidableEq F] (ws cs : List F) :
    typedBatchAccepts ws cs = true ↔
      weightedSum ws cs = 0 ∧ ∀ x ∈ cs, x = 0 := by
  constructor
  · intro h
    simp [typedBatchAccepts, Bool.and_eq_true] at h
    refine ⟨h.1, ?_⟩
    have hb : hasNonzero cs = false := by
      simpa [Bool.not_eq_true'] using h.2
    intro x hx
    by_contra hne
    have : hasNonzero cs = true := (hasNonzero_iff cs).2 ⟨x, hx, hne⟩
    simp [hb] at this
  · intro ⟨hsum, hz⟩
    have hb : hasNonzero cs = false := by
      rw [Bool.eq_false_iff, Ne, hasNonzero_iff]
      exact fun ⟨x, hx, hne⟩ => hne (hz x hx)
    simp [typedBatchAccepts, hsum, hb]

/-- Inspect reports a break exactly when the combination accepts a live claim. -/
theorem typedBatchAccepts_not_break [DecidableEq F] {ws cs : List F}
    (h : typedBatchAccepts ws cs = true) : inspectBatch ws cs = none :=
  inspectBatch_none_of_all_zero ((typedBatchAccepts_iff ws cs).1 h).2

/-- Typed proof : AHP evaluations plus a batch combination. -/
structure TypedProof (F : Type*) [Field F] where
  /-- The three LC evaluations. -/
  checks : AHPVerifierChecks F
  /-- Batch combiners (`1` first). -/
  batchWeights : List F
  /-- Batch claims (instance/circuit residuals at a challenge). -/
  batchClaims : List F

/-- Typed accept of an AHP + batch transcript. -/
def TypedProof.accepts [DecidableEq F] (π : TypedProof F) : Bool :=
  typedAHPAccepts π.checks && typedBatchAccepts π.batchWeights π.batchClaims

/-- Accepting typed proofs have vanishing AHP LCs. -/
theorem TypedProof.accepts_ahp [DecidableEq F] {π : TypedProof F}
    (h : π.accepts = true) : π.checks.accepts := by
  simp [TypedProof.accepts, Bool.and_eq_true] at h
  exact (typedAHPAccepts_iff _).1 h.1

/-- Accepting typed proofs have an all-zero batch. -/
theorem TypedProof.accepts_batch [DecidableEq F] {π : TypedProof F}
    (h : π.accepts = true) : ∀ x ∈ π.batchClaims, x = 0 := by
  simp [TypedProof.accepts, Bool.and_eq_true] at h
  exact ((typedBatchAccepts_iff _ _).1 h.2).2

/-! ## ToyField fixtures (kernel `decide`, not `native_decide`) -/

/-- Honest zero LCs are accepted on the toy field. -/
theorem toy_ahp_accepts :
    typedAHPAccepts (⟨0, 0, 0⟩ : AHPVerifierChecks ToyField) = true := by
  decide

/-- Flipping the rowcheck evaluation is rejected. -/
theorem toy_ahp_rejects_flip_rowcheck :
    typedAHPAccepts (⟨1, 0, 0⟩ : AHPVerifierChecks ToyField) = false := by
  decide

/-- Flipping the lineval evaluation is rejected. -/
theorem toy_ahp_rejects_flip_lineval :
    typedAHPAccepts (⟨0, 1, 0⟩ : AHPVerifierChecks ToyField) = false := by
  decide

/-- Flipping the matrix evaluation is rejected. -/
theorem toy_ahp_rejects_flip_matrix :
    typedAHPAccepts (⟨0, 0, 1⟩ : AHPVerifierChecks ToyField) = false := by
  decide

/-- `1·3 + 2·7 = 17 = 0` in `𝔽₁₇` with live claims is a batch break. -/
theorem toy_batch_lucky :
    inspectBatch ([1, 2] : List ToyField) [3, 7] =
      some ([1, 2], [3, 7]) := by
  decide

/-- Flipping the second claim makes the combination nonzero, so no break
(the verifier already rejects). -/
theorem toy_batch_flip_no_break :
    inspectBatch ([1, 2] : List ToyField) [3, 8] = none := by
  decide

/-- All-zero claims of any weight are accepted. -/
theorem toy_batch_zeros_accept :
    typedBatchAccepts ([1, 4] : List ToyField) [0, 0] = true := by
  decide

/-- Empty batch (single-circuit, no extra claims) is accepted. -/
theorem toy_batch_nil_accept :
    typedBatchAccepts ([] : List ToyField) [] = true := by
  decide

/-- A full typed proof with zero LCs and no batch claims is accepted. -/
theorem toy_typed_proof_accepts :
    (⟨⟨0, 0, 0⟩, [], []⟩ : TypedProof ToyField).accepts = true := by
  decide

/-- Flipping a field in the assembled accept predicate rejects the proof. -/
theorem toy_typed_proof_rejects_flip :
    (⟨⟨1, 0, 0⟩, [], []⟩ : TypedProof ToyField).accepts = false := by
  decide

/-! ## Toy bilinear pairing (field multiplication) for KZG fixtures -/

/-- Multiplicative pairing on `ToyField` used only as a closed test vector.
BLS12-377 remains a floor. -/
def toyMulPairing : Pairing ToyField ToyField ToyField ToyField where
  pair x y := x * y
  map_add_left a a' b := add_mul a a' b
  map_add_right a b b' := mul_add a b b'
  map_smul_left r a b := by simp [smul_eq_mul, mul_assoc]
  map_smul_right r a b := by
    simp [smul_eq_mul]
    ring

/-- Toy verifying key `g = h = 1`, `βh = 3`. -/
def toyVK : VerifyingKey ToyField ToyField :=
  ⟨1, 1, 3⟩

/-- Honest-shaped opening at `z = 2` of value `4` with witness `1`. -/
def toyOpening : Opening ToyField ToyField :=
  ⟨2, 4, 1⟩

/-- `e(5 − 4·1, 1) = e(1, 3 − 2·1)` holds in the toy pairing. -/
theorem toy_kzg_accepts :
    kzgCheck toyMulPairing toyVK 5 toyOpening := by
  unfold kzgCheck toyMulPairing toyVK toyOpening
  simp [smul_eq_mul]
  decide

/-- Distinct claimed values at the same point are a binding break. -/
theorem toy_binding_break :
    inspectBinding (5 : ToyField)
      (⟨2, 4, 1⟩ : Opening ToyField ToyField)
      ⟨2, 5, 7⟩ =
      some ⟨5, 2, 4, 5, 1, 7⟩ := by
  simp [inspectBinding]
  decide

/-- Equal claimed values are not a binding break. -/
theorem toy_binding_none :
    inspectBinding (5 : ToyField)
      (⟨2, 4, 1⟩ : Opening ToyField ToyField)
      ⟨2, 4, 9⟩ = none := by
  simp [inspectBinding]

end Varuna