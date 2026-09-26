/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Algebraic
import Varuna.Selectors

/-!
# Batched Sonic openings

snarkVM batches openings at two levels (`polycommit/sonic_pc/mod.rs`):

* at one query point, the polynomials are combined with one Fiat–Shamir
  challenge each (`combine_polynomials`), and one KZG proof opens the
  combination;
* across the query points `α, β, γ`, the verifier combines the pairing
  checks with randomizers from a sponge that has absorbed the proofs
  (`batch_check`).

Under the algebraic restriction each level reduces to a field-level
combination of discrepancies. A combination that vanishes while some
discrepancy does not is returned by `inspectBatch`, like every other
lucky combination; `Probability.lean` bounds how many challenges do that.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- Combine representations with challenges: `Σ_i c_i p_i`. -/
def combineCoeffs : List F → List (List F) → List F
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, p :: ps => addCoeffs (scaleCoeffs c p) (combineCoeffs cs ps)

/-- The combined representation denotes the weighted polynomial sum. -/
theorem toPoly_combineCoeffs : ∀ (cs : List F) (ps : List (List F)),
    toPoly (combineCoeffs cs ps) = weightedSumPoly cs (ps.map toPoly)
  | [], _ => by simp [combineCoeffs, weightedSumPoly]
  | _ :: _, [] => by simp [combineCoeffs, weightedSumPoly]
  | c :: cs, p :: ps => by
    simp [combineCoeffs, weightedSumPoly, toPoly_addCoeffs, toPoly_scaleCoeffs,
      toPoly_combineCoeffs cs ps]

/-- Evaluating the combination is combining the evaluations. -/
theorem evalCoeffs_combineCoeffs (cs : List F) (ps : List (List F)) (x : F) :
    evalCoeffs (combineCoeffs cs ps) x = weightedSum cs (ps.map fun p => evalCoeffs p x) := by
  rw [← eval_toPoly, toPoly_combineCoeffs, eval_weightedSumPoly, List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => eval_toPoly x p

/-- Per-point batched opening. If the combined claim is the evaluation of the
combined representation (the combined opening passed and `inspectOpening`
found nothing) and the combination of discrepancies is not lucky, every
individual claim is the evaluation of its representation. -/
theorem batchedOpening_extract [DecidableEq F] {cs : List F} {os : List (List F × F)} {z : F}
    (hcomb : weightedSum cs (os.map fun o => o.2) =
      evalCoeffs (combineCoeffs cs (os.map fun o => o.1)) z)
    (hnone : inspectBatch cs (os.map fun o => evalCoeffs o.1 z - o.2) = none) :
    ∀ o ∈ os, o.2 = evalCoeffs o.1 z := by
  rw [evalCoeffs_combineCoeffs, List.map_map] at hcomb
  simp only [Function.comp_def] at hcomb
  have hws : weightedSum cs (os.map fun o => evalCoeffs o.1 z - o.2) = 0 := by
    rw [weightedSum_map_sub, ← hcomb, sub_self]
  intro o ho
  have := inspectBatch_accepts hws hnone _
    (List.mem_map_of_mem (f := fun o : List F × F => evalCoeffs o.1 z - o.2) ho)
  exact (sub_eq_zero.mp this).symm

/-- A root of the opening defect at the trapdoor, with a wrong claimed value,
is a trapdoor break (the field form of `inspectOpening_break`). -/
theorem inspectOpening_break_of_root [DecidableEq F] {p q : List F} {z v τ : F}
    (hroot : (toPoly (openingDefect p q z v)).eval τ = 0) {b : TrapdoorBreak F}
    (hb : inspectOpening p q z v = some b) : b.holds τ := by
  unfold inspectOpening at hb
  split_ifs at hb with hv
  cases hb
  exact ⟨toPoly_openingDefect_ne_zero hv, hroot⟩

/-- Across query points. The verifier's randomized pairing check, read
against the algebraic representations, says `Σ_j r_j D_j(τ) = 0` for the
per-point defects `D_j`. Unless that combination is lucky, every defect
vanishes at the trapdoor, so each point's opening is correct or a trapdoor
break (`inspectOpening_break_of_root`). -/
theorem acrossPoints_extract [DecidableEq F] {rs : List F} {ds : List (List F)} {τ : F}
    (hsum : weightedSum rs (ds.map fun d => (toPoly d).eval τ) = 0)
    (hnone : inspectBatch rs (ds.map fun d => (toPoly d).eval τ) = none) :
    ∀ d ∈ ds, (toPoly d).eval τ = 0 := fun _ hd =>
  inspectBatch_accepts hsum hnone _ (List.mem_map_of_mem (f := fun e => (toPoly e).eval τ) hd)

end Varuna