/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchFS

/-!
# The batched pairing check

snarkVM's verifier does not open `h₀`, the mask, `h₁`, `ŵ`, or `h₂` one by one. Its query
set (`ahp/verifier/messages.rs:100-140`) is the rowcheck LC at `α`, `g₁` and the lineval
LC at `β`, and every circuit's `g_A, g_B, g_C` and the matrix LC at `γ`, each LC opened
to `0` (`ahp.rs:179-404`). `batch_check` (`sonic_pc/mod.rs:347-420`) combines the
openings at each point with one challenge per polynomial (`accumulate_elems`), and the
points with randomizers `1, r₁, r₂`. One pairing product checks the lot.

Against the algebraic representations, the pairing product reads `Σ_j r_j D_j(τ) = 0`,
with `D_j = Σ_i ξ_{j,i} p_{j,i} − Σ_i ξ_{j,i} v_{j,i} − (X − z_j) q_j` the KZG defect at
point `j` (`PointOpening.defect`). The degree-bound shifts and the hiding component of
the product are group-level assembly, not part of this reading. Unless the randomizers
are lucky every `D_j(τ)` is zero. A nonzero `D_j` with root `τ` is a trapdoor break
(`PCBreak.trapdoorBreak`). `D_j = 0` gives `Σ_i ξ_{j,i} (p_{j,i}(z_j) − v_{j,i}) = 0`, so
unless the `ξ_j` are lucky every claim is correct (`batchCheck_extract`).

`V3Batch.holds_of_deployedAccepts` : the V3 checks with the batch check in place of
correct openings (`DeployedAccepts`), no break of the transcript, no lucky combination,
and no trapdoor break give the relation.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## One pairing product over the query points -/

/-- One query point of `batch_check`, read against the algebraic representations : the
point, each opened polynomial with its claimed value, and the polynomial behind the
point's KZG proof. -/
structure PointOpening (F : Type*) [Field F] where
  z : F
  opened : List (F[X] × F)
  proof : F[X]

namespace PointOpening

variable (o : PointOpening F)

/-- The KZG defect of the point with combination challenges `ξ` :
`Σ ξ_i p_i − Σ ξ_i v_i − (X − z) q`. -/
noncomputable def defect (ξ : List F) : F[X] :=
  weightedSumPoly ξ (o.opened.map Prod.fst) - C (weightedSum ξ (o.opened.map Prod.snd)) -
    (X - C o.z) * o.proof

/-- Each opened polynomial's value at the point less its claimed value. -/
noncomputable def discrepancies : List F :=
  o.opened.map fun pv => pv.1.eval o.z - pv.2

theorem eval_defect_z (ξ : List F) : (o.defect ξ).eval o.z = weightedSum ξ o.discrepancies := by
  rw [discrepancies, weightedSum_map_sub (fun pv : F[X] × F => pv.1.eval o.z) Prod.snd, defect]
  simp [eval_weightedSumPoly, List.map_map, Function.comp_def]

end PointOpening

/-- The defects at `τ`, point by point. -/
noncomputable def defectsAt (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) : List F :=
  List.zipWith (fun o ξ => (o.defect ξ).eval τ) os ξs

/-- The batch check passes by luck : the randomizers `rs` cancel nonzero defects at `τ`, or
some point's challenges cancel a wrong claim. -/
def PCLucky (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) (rs : List F) : Prop :=
  inspectBatch rs (defectsAt τ os ξs) ≠ none ∨
    ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
      inspectBatch ξs[j] os[j].discrepancies ≠ none

/-- Some point's defect is a nonzero polynomial with root `τ`. -/
def PCBreak (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) : Prop :=
  ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
    os[j].defect ξs[j] ≠ 0 ∧ (os[j].defect ξs[j]).eval τ = 0

/-- A defect with root `τ` is a trapdoor break. -/
theorem PCBreak.trapdoorBreak {τ : F} {os : List (PointOpening F)} {ξs : List (List F)}
    (h : PCBreak τ os ξs) : ∃ br : TrapdoorBreak F, br.holds τ := by
  obtain ⟨j, hj, hj', hne, hev⟩ := h
  refine ⟨⟨coeffList (os[j].defect ξs[j])⟩, ?_, ?_⟩
  · rw [toPoly_coeffList]
    exact hne
  · rw [toPoly_coeffList]
    exact hev

/-- Batch-check extraction. If the randomized defects at `τ` sum to zero, nothing is lucky,
and no defect is a nonzero polynomial with root `τ`, every claimed value is its
polynomial's value at the point. -/
theorem batchCheck_extract {τ : F} {os : List (PointOpening F)} {ξs : List (List F)}
    {rs : List F} (hlen : os.length ≤ ξs.length) (hcheck : weightedSum rs (defectsAt τ os ξs) = 0)
    (hl : ¬PCLucky τ os ξs rs) (hbr : ¬PCBreak τ os ξs) :
    ∀ o ∈ os, ∀ pv ∈ o.opened, pv.2 = pv.1.eval o.z := by
  intro o ho pv hpv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
  have hj' : j < ξs.length := by omega
  have hr : inspectBatch rs (defectsAt τ os ξs) = none := by
    by_contra h
    exact hl (Or.inl h)
  have hτ : (os[j].defect ξs[j]).eval τ = 0 := by
    refine inspectBatch_accepts hcheck hr _ ?_
    have hlt : j < (defectsAt τ os ξs).length := by
      simp only [defectsAt, List.length_zipWith]
      omega
    have hmem := List.getElem_mem hlt
    have heq : (defectsAt τ os ξs)[j] = (os[j].defect ξs[j]).eval τ := by
      simp [defectsAt]
    rw [heq] at hmem
    exact hmem
  have hzero : os[j].defect ξs[j] = 0 := by
    by_contra hne
    exact hbr ⟨j, hj, hj', hne, hτ⟩
  have hξ : inspectBatch ξs[j] os[j].discrepancies = none := by
    by_contra h
    exact hl (Or.inr ⟨j, hj, hj', h⟩)
  have hsum : weightedSum ξs[j] os[j].discrepancies = 0 := by
    rw [← PointOpening.eval_defect_z, hzero, eval_zero]
  have h0 := inspectBatch_accepts hsum hξ _
    (List.mem_map_of_mem (f := fun pv : F[X] × F => pv.1.eval os[j].z - pv.2) hpv)
  exact (sub_eq_zero.mp h0).symm

/-! ## The V3 query set -/

/-- A matrix term's `matrix_sumcheck` LC term `s(γ) (a − (γ vg + σ) b)`, with `g(γ)` read
as `vg` (`ahp.rs:407-422`). -/
noncomputable def MatrixTerm.lcAt (K : EvalDomain F) (t : MatrixTerm F) (γ vg : F) : F[X] :=
  C ((selectorPoly K t.K).eval γ) * (t.a - C (γ * vg + t.σ) * t.b)

theorem MatrixTerm.eval_lcAt (K : EvalDomain F) (t : MatrixTerm F) (γ vg : F) :
    (t.lcAt K γ vg).eval γ = t.summandAt K γ vg := by
  simp only [lcAt, summandAt, eval_mul, eval_C, eval_sub]
  ring

/-- The circuit's three `matrix_sumcheck` LC terms, `A, B, C` in order, with the opened
`g_M(γ)`. -/
noncomputable def BatchCircuit.matrixLCs (c : BatchCircuit F) (K : EvalDomain F) (α β γ : F) :
    List F[X] :=
  [MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KA, c.A, α, β, c.gA, c.σmA⟩ γ c.vgA,
    MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KB, c.B, α, β, c.gB, c.σmB⟩ γ c.vgB,
    MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KC, c.Cm, α, β, c.gC, c.σmC⟩ γ c.vgC]

namespace V3Batch

variable (P : V3Batch F)

/-- snarkVM's `rowcheck_zerocheck` (`ahp.rs:246-271`) as a polynomial : the prepare-third
sums as a constant, less `v_R(α) h₀`. -/
noncomputable def rowLC (ws : List F) : F[X] :=
  C (weightedSum ws (P.instances.map fun p =>
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC))) -
    C (P.R.vanishing.eval P.α) * toPoly P.h0rep

/-- snarkVM's `lineval_sumcheck` (`ahp.rs:314-355`) as a polynomial : the mask, each
instance's `x̂(β) + v_X(β) ŵ` with its weight, less `v_C(β) h₁` and the constants
`β g₁(β)`, read off the claimed value, and the batch sum. -/
noncomputable def linLC (ws : List F) : F[X] :=
  maskPoly P.mode P.mask +
      weightedSumPoly ws (P.instances.map fun p =>
        C ((selectorPoly P.Cd p.1.Cd).eval P.β *
            (P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
              P.ηC * ((p.1.KC.n : F) * p.1.σmC))) *
          (C ((p.1.Xd.interpolate fun k => p.2.x.getD k 0).eval P.β) +
            C (p.1.Xd.vanishing.eval P.β) * p.2.w)) -
    C (P.Cd.vanishing.eval P.β) * P.h1 - C (P.β * P.vG1 + P.linSum ws * P.Cd.sizeInv)

/-- snarkVM's `matrix_sumcheck` (`ahp.rs:363-402`) as a polynomial : every matrix term,
`δ`-weighted, with the opened `g_M(γ)`, less `v_K(γ) h₂`. -/
noncomputable def matLC (δs : List F) : F[X] :=
  weightedSumPoly δs (P.circuits.flatMap fun c => c.matrixLCs P.K P.α P.β P.γ) -
    C (P.K.vanishing.eval P.γ) * P.h2

/-- Every circuit's opened `g_A(γ), g_B(γ), g_C(γ)`, in label order (`circuit_{id}_g_a_…`
sorts before `matrix_sumcheck`). -/
def gOpenings : List (F[X] × F) :=
  P.circuits.flatMap fun c => [(c.gA, c.vgA), (c.gB, c.vgB), (c.gC, c.vgC)]

/-- `batch_check`'s query points in order (`messages.rs:100-140`) : the rowcheck LC at `α`;
`g₁` and the lineval LC at `β`; the `g_M` and the matrix LC at `γ`. Each LC opens to `0`;
the weights are read off `chal`, and `qs` are the polynomials behind the KZG proofs. -/
noncomputable def pcPoints (chal : V2Challenge → List F) (qs : List F[X]) :
    List (PointOpening F) :=
  [⟨P.α, [(P.rowLC (P.rowWeights chal), 0)], qs.getD 0 0⟩,
    ⟨P.β, [(P.g1, P.vG1), (P.linLC (P.linWeights chal), 0)], qs.getD 1 0⟩,
    ⟨P.γ, P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)], qs.getD 2 0⟩]

theorem eval_rowLC (ws : List F) :
    (P.rowLC ws).eval P.α = weightedSum ws (P.instances.map fun p =>
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC)) -
        evalCoeffs P.h0rep P.α * P.R.vanishing.eval P.α := by
  simp only [rowLC, eval_sub, eval_C, eval_mul, eval_toPoly]
  ring

theorem eval_linLC {ws : List F} (hg : P.vG1 = P.g1.eval P.β) :
    (P.linLC ws).eval P.β = P.linEval ws := by
  simp only [linLC, linEval, eval_add, eval_sub, eval_mul, eval_C, eval_weightedSumPoly,
    List.map_map, Function.comp_def, BatchCircuit.zhat, eval_assignmentPoly, hg, mul_assoc]
  ring

theorem eval_matLC {δs : List F}
    (hg : ∀ c ∈ P.circuits, c.vgA = c.gA.eval P.γ ∧ c.vgB = c.gB.eval P.γ ∧ c.vgC = c.gC.eval P.γ) :
    (P.matLC δs).eval P.γ = batchedMatrixEval P.K δs P.matrixTerms P.h2 P.γ := by
  have hc : ∀ c ∈ P.circuits, (c.matrixLCs P.K P.α P.β P.γ).map (fun q => q.eval P.γ) =
      (c.matrixTerms P.α P.β).map fun t => (selectorPoly P.K t.K).eval P.γ *
        (t.a.eval P.γ - t.b.eval P.γ * (P.γ * t.g.eval P.γ + t.σ)) := by
    intro c hc
    obtain ⟨hA, hB, hC⟩ := hg c hc
    simp only [BatchCircuit.matrixLCs, BatchCircuit.matrixTerms, List.map_cons, List.map_nil,
      MatrixTerm.eval_lcAt, MatrixTerm.summandAt, hA, hB, hC]
  rw [matLC, eval_sub, eval_weightedSumPoly, List.map_flatMap, flatMap_congr_mem hc,
    batchedMatrixEval, matrixTerms, List.map_flatMap]
  simp only [eval_mul, eval_C]
  ring

/-- The V3 verifier's checks of `P` as snarkVM runs them : those of `Accepts` but the
openings and the three LC equations, which the batch check over `pcPoints` replaces. The
check reads the randomizers `rs`, each point's combination challenges `ξs`, and the
polynomials `qs` behind the KZG proofs, against the trapdoor `τ`. -/
structure DeployedAccepts (P : V3Batch F) (S : Finset F) (t : V2Transcript F)
    (chal : V2Challenge → List F) (comms : List (List F)) (τ : F) (qs : List F[X])
    (ξs : List (List F)) (rs : List F) : Prop where
  init : t.init = v3Init P.statement comms
  msg : ∀ x, FSMessage.field x ∉ t.messages
  inS : ∀ c, ∀ a ∈ chal c, a ∈ S
  alpha : chal .alpha = [P.α]
  beta : chal .beta = [P.β]
  gamma : chal .gamma = [P.γ]
  nu : (chal .firstCombiners).length = combinerDraws P.sizes
  eta : (chal .prepareThird).length = combinerDraws P.sizes + 3
  etaA : P.ηA = (chal .prepareThird).getD (combinerDraws P.sizes) 0
  etaB : P.ηB = (chal .prepareThird).getD (combinerDraws P.sizes + 1) 0
  etaC : P.ηC = (chal .prepareThird).getD (combinerDraws P.sizes + 2) 0
  delta : (chal .deltas).length = 3 * P.circuits.length - 1
  dvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n
  dvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n
  dvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n
  valid : ∀ t ∈ P.matrixTerms, t.Valid
  gen : ∀ c ∈ P.circuits, c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n)
  degL : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n
  points : ξs.length = 3
  check : weightedSum rs (defectsAt τ (P.pcPoints chal qs) ξs) = 0

/-- The relation from the deployed checks : with no squeezed element in its bad set, no
lucky combination in the batch check, and no trapdoor break, the transcript's batch
satisfies `Holds`. -/
theorem holds_of_deployedAccepts {P : V3Batch F} {S : Finset F} {t : V2Transcript F}
    {chal : V2Challenge → List F} {comms : List (List F)} {τ : F} {qs : List F[X]}
    {ξs : List (List F)} {rs : List F} (h : P.DeployedAccepts S t chal comms τ qs ξs rs)
    (hnb : outputBreaks (prefixBad t (P.squeezeBad S chal)) t chal = false)
    (hl : ¬PCLucky τ (P.pcPoints chal qs) ξs rs) (hbr : ¬PCBreak τ (P.pcPoints chal qs) ξs) :
    P.Holds t := by
  have hpt : ∀ o ∈ P.pcPoints chal qs, ∀ pv ∈ o.opened, pv.2 = pv.1.eval o.z :=
    batchCheck_extract (by simp [pcPoints, h.points]) h.check hl hbr
  have hα := hpt ⟨P.α, [(P.rowLC (P.rowWeights chal), 0)], qs.getD 0 0⟩ (by simp [pcPoints])
  have hβ := hpt ⟨P.β, [(P.g1, P.vG1), (P.linLC (P.linWeights chal), 0)], qs.getD 1 0⟩
    (by simp [pcPoints])
  have hγ := hpt ⟨P.γ, P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)], qs.getD 2 0⟩
    (by simp [pcPoints])
  have hrow : (0 : F) = (P.rowLC (P.rowWeights chal)).eval P.α :=
    hα (P.rowLC (P.rowWeights chal), 0) (by simp)
  have hg1 : P.vG1 = P.g1.eval P.β := hβ (P.g1, P.vG1) (by simp)
  have hlin : (0 : F) = (P.linLC (P.linWeights chal)).eval P.β :=
    hβ (P.linLC (P.linWeights chal), 0) (by simp)
  have hmat : (0 : F) = (P.matLC (P.deltaWeights chal)).eval P.γ :=
    hγ (P.matLC (P.deltaWeights chal), 0) (by simp)
  have hgM : ∀ c ∈ P.circuits,
      c.vgA = c.gA.eval P.γ ∧ c.vgB = c.gB.eval P.γ ∧ c.vgC = c.gC.eval P.γ := by
    intro c hc
    have hmem : ∀ pv ∈ [(c.gA, c.vgA), (c.gB, c.vgB), (c.gC, c.vgC)],
        pv ∈ P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)] :=
      fun pv hpv => List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hpv⟩)
    exact ⟨hγ (c.gA, c.vgA) (hmem _ (by simp)), hγ (c.gB, c.vgB) (hmem _ (by simp)),
      hγ (c.gC, c.vgC) (hmem _ (by simp))⟩
  exact V3Batch.sound_of_transcript_evals { P with vH0 := evalCoeffs P.h0rep P.α } S t chal comms
    h.init h.msg h.inS h.alpha h.beta h.gamma h.nu h.eta h.etaA h.etaB h.etaC h.delta hnb h.dvdR
    h.dvdC h.dvdK h.valid h.gen (inspectOpening_honest P.h0rep [] P.α)
    ((P.eval_rowLC _).symm.trans hrow.symm) ((P.eval_linLC hg1).symm.trans hlin.symm) h.degL
    ((P.eval_matLC hgM).symm.trans hmat.symm)

end V3Batch

end Varuna