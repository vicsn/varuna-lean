/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Match
import Varuna.Soundness

/-!
# Spot checks against the snarkVM submodule

Ironwood fingerprints a deployed verifier by capturing assembled MSM
coefficients and `native_decide`-ing them in Lean. This module is the
Varuna analogue that we can discharge today : **source-pinned samples**
of the identities snarkVM actually runs, checked against the Lean defs.

It is *not* a BLS12-377 proof capture. Byte encodings, Poseidon, and
pairing hardness stay floors. Each sample names a path in the pinned
`snarkVM/` submodule (`29343ebbb7970e4240b4444346aeb26e31009bd7`, v4.11.0).
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- Pinned snarkVM git object the samples were read from. -/
def snarkVMPin : String :=
  "29343ebbb7970e4240b4444346aeb26e31009bd7"

/-- The pin is the 40-character SHA of the `snarkVM` submodule commit. -/
@[simp] theorem snarkVMPin_length : snarkVMPin.length = 40 :=
  rfl

/-! ## Names and schedule (`ahp.rs`, `verifier.rs`) -/

/-- `AHPForR1CS::LC_WITH_ZERO_EVAL` in `ahp/ahp.rs`. -/
theorem sample_lcWithZeroEval :
    lcWithZeroEval =
      ["matrix_sumcheck", "lineval_sumcheck", "rowcheck_zerocheck"] :=
  lcNames_match_snarkVM

/-- Query-set challenge names in `ahp/verifier/messages.rs`. -/
theorem sample_queryChallengeNames :
    queryChallengeNames = ["alpha", "beta", "gamma"] :=
  rfl

/-- V2 second-round squeeze is one field (`α` only), `verifier.rs`. -/
theorem sample_v2_second_round_squeeze :
    secondRoundSqueezeCount .V2 = 1 :=
  rfl

/-- V1 second-round squeeze is three fields (`α, η_b, η_c`). -/
theorem sample_v1_second_round_squeeze :
    secondRoundSqueezeCount .V1 = 3 :=
  rfl

/-- V2 prepare-third squeezes two extra fields (`η_b, η_c`). -/
theorem sample_prepareThird_eta_squeezes :
    prepareThirdEtaSqueeze .V2 = 2 :=
  rfl

/-- V3 prepare-third squeezes three fields (`η_a, η_b, η_c`). -/
theorem sample_v3_prepareThird_eta_squeezes :
    prepareThirdEtaSqueeze .V3 = 3 :=
  rfl

/-- V3 second-round squeeze is one field (`α` only), as in V2. -/
theorem sample_v3_second_round_squeeze :
    secondRoundSqueezeCount .V3 = 1 :=
  rfl

/-- First circuit combiner is `1` (`sample_batch_combiners`). -/
theorem sample_first_circuit_combiner (rest : List F) :
    (circuitCombiners rest).head? = some 1 :=
  circuitCombiners_head rest

/-- First instance combiner is `1` (`sample_batch_combiners`). -/
theorem sample_first_instance_combiner (rest : List F) :
    (instanceCombiners rest).head? = some 1 :=
  instanceCombiners_head rest

/-- `η_A = 1` (`third.rs` `matrix_combiners = [one, eta_b, eta_c]`). -/
theorem sample_etaA_is_one (etaB etaC : F) :
    (MatrixCombiners.ofEtaBC etaB etaC).etaA = 1 :=
  etaA_eq_one etaB etaC

/-- First-circuit `δ_A = 1` (`verifier_fourth_round`). -/
theorem sample_deltaA_first_is_one (deltaB deltaC : F) :
    (DeltaCombiners.first deltaB deltaC).deltaA = 1 :=
  deltaA_first_eq_one deltaB deltaC

/-- Deployed version is V3 and has the extra round. -/
theorem sample_deployed_is_V3 :
    deployedVersion = .V3 ∧ hasPrepareThird .V3 = true ∧
      prepareThirdEtaSqueeze deployedVersion = 3 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Domains, padding, indexer (`fft/domain.rs`, `ahp/matrices.rs`) -/

/-- `evaluate_vanishing_polynomial`: `τ^n - 1`. -/
theorem sample_vanishing_eval (H : EvalDomain F) (τ : F) :
    H.vanishing.eval τ = τ ^ H.n - 1 :=
  H.vanishing_eval τ

/-- `elements` starts at `F::one()`; node 0 is `ω^0 = 1`. -/
theorem sample_node_zero (H : EvalDomain F) : H.node 0 = 1 :=
  H.node_zero

/-- `matrix_evals` pads with field `1` at row/col (index 0) and value `0`. -/
theorem sample_padEntry_indices :
    let p : MatrixEntry ToyField := padEntry
    p.rowIdx = 0 ∧ p.colIdx = 0 ∧ p.value = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Padding indices evaluate to `1` on any domain (snarkVM `F::one()`). -/
theorem sample_pad_nodes_are_one (H : EvalDomain F) :
    H.node (padEntry (F := F)).rowIdx = 1 ∧
      H.node (padEntry (F := F)).colIdx = 1 := by
  simp [padEntry]

/-- `CircuitInfo::num_public_and_private_variables`. -/
theorem sample_circuitInfo_variables (info : CircuitInfo) :
    info.numPublicAndPrivateVariables = info.numVariables :=
  rfl

/-- Formatted public input is admissible iff length is `2^k`
(`count_ones() == 1` in `ahp.rs`). -/
theorem sample_formatted_admissible (input : List Int) :
    formattedPublicInputAdmissible input ↔ PowTwo input.length :=
  Iff.rfl

/-- Formatting prepends the constant-`1` slot. -/
theorem sample_format_prepends_one (xs : List Int) :
    formatPublicInput xs = 1 :: xs :=
  rfl

/-- Empty public input formats to a power-of-two length. -/
theorem sample_toy_admissible_one :
    formattedPublicInputAdmissible (formatPublicInput []) :=
  formatPublicInput_nil_admissible

/-! ## Selectors (`ahp/selectors.rs`) -/

/-- Pointwise, the Lean selector is snarkVM
`v_H(α) | H_i | / (v_{H_i}(α) | H | )`. -/
theorem sample_selector_eval (H Hi : EvalDomain F) (hdvd : Hi.n ∣ H.n)
    {α : F} (hα : Hi.vanishing.eval α ≠ 0) :
    (selectorPoly H Hi).eval α =
      H.vanishing.eval α * Hi.sizeAsField /
        (Hi.vanishing.eval α * H.sizeAsField) :=
  selectorPoly_eval H Hi hdvd hα

/-- Equal domains give selector `1` (snarkVM skips the scale when sizes match). -/
theorem sample_selector_self (H : EvalDomain F) : selectorPoly H H = 1 :=
  selectorPoly_self H

/-! ## Matrix `b` LC (`ahp.rs` `construct_matrix_linear_combinations`) -/

/-- Deployed four-term `b`: `|R||C|(αβ − α col − β row + row·col)`. -/
theorem sample_matrixB_four_terms (H_R H_C H_K : EvalDomain F) (α β : F)
    (rowIdx colIdx : Nat → Nat) :
    matrixBPoly H_R H_C H_K α β rowIdx colIdx =
      C (H_R.sizeAsField * H_C.sizeAsField) *
        (C (α * β) - C α * colOracle H_C H_K colIdx -
          C β * rowOracle H_R H_K rowIdx +
          rowOracle H_R H_K rowIdx * colOracle H_C H_K colIdx) :=
  matrixBPoly_four_terms H_R H_C H_K α β rowIdx colIdx

/-- On `K`, `row*col` recovers the stored nodes (the committed `row_col`
interpolant agrees here; off `K` it may differ). -/
theorem sample_row_col_at_node (H_R H_C H_K : EvalDomain F)
    (rowIdx colIdx : Nat → Nat) {k : Nat} (hk : k < H_K.n) :
    (rowOracle H_R H_K rowIdx * colOracle H_C H_K colIdx).eval (H_K.node k) =
      H_R.node (rowIdx k) * H_C.node (colIdx k) := by
  simp [eval_mul, rowOracle_eval, colOracle_eval, hk]

/-! ## KZG check (`polycommit/kzg10/mod.rs`) -/

/-- Non-hiding `KZG10::check`: `e(C − v g, h) = e(w, βh − z h)`. -/
theorem sample_kzg_equation {G1 G2 GT : Type*}
    [AddCommGroup G1] [AddCommGroup G2] [AddCommGroup GT]
    [Module F G1] [Module F G2] [Module F GT]
    (e : Pairing F G1 G2 GT) (vk : VerifyingKey G1 G2)
    (C : G1) (o : Opening G1 F) :
    kzgCheck e vk C o ↔
      e.pair (C - o.value • vk.g) vk.h =
        e.pair o.witness (vk.betaH - o.point • vk.h) :=
  Iff.rfl

/-! ## Numeric samples on `𝔽₁₇` (kernel `decide`) -/

/-- Vanishing at `1` (domain node 0): `1^n − 1 = 0`. -/
theorem sample_toy_vanishing_at_one :
    (1 : ToyField) ^ 8 - 1 = 0 := by
  decide

/-- Selector scale `|H_i|/|H|` for sizes `4` and `8` in `𝔽₁₇`. -/
theorem sample_toy_size_ratio :
    (4 : ToyField) * (8 : ToyField)⁻¹ = 9 := by
  have h8 : (8 : ToyField) * 15 = 1 := by decide
  rw [inv_eq_of_mul_eq_one_right h8]
  decide

/-- Lucky batch `1·3 + 2·7 = 0` in `𝔽₁₇` is reported as a break. -/
theorem sample_toy_batch_break :
    inspectBatch ([1, 2] : List ToyField) [3, 7] =
      some ([1, 2], [3, 7]) :=
  toy_batch_lucky

/-- Flipping a zero-eval LC is rejected. -/
theorem sample_toy_flip_rejects :
    typedAHPAccepts (⟨1, 0, 0⟩ : AHPVerifierChecks ToyField) = false :=
  toy_ahp_rejects_flip_rowcheck

/-- Honest zeros are accepted. -/
theorem sample_toy_zeros_accept :
    typedAHPAccepts (⟨0, 0, 0⟩ : AHPVerifierChecks ToyField) = true :=
  toy_ahp_accepts

/-- Toy KZG pairing equation from `KZG10::check`. -/
theorem sample_toy_kzg : kzgCheck toyMulPairing toyVK 5 toyOpening :=
  toy_kzg_accepts

end Varuna