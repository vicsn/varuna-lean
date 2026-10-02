/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Composition
import Varuna.MatrixSumcheck
import Varuna.Algebraic
import Varuna.Bridge
import Varuna.Selectors

/-!
# End-to-end V2 endpoint

This composes the polynomial-commitment reductions with the AHP chain into a
single statement. A `V2Endpoint` bundles a V2 proof as algebraic data : the
committed rowcheck quotient as a representation with its opened value, the
lineval and per-matrix sumcheck witnesses, and the prover's sums.

`V2Endpoint.sound` shows that if

* the rowcheck-quotient opening reports no break (`inspectOpening = none`),
* each matrix sumcheck accepts (with its degree bound), and
* the AHP inspectors (`inspectResidual`, `inspectBatch`) report no break,

then the accepted proof establishes exactly `(A z + e) ∘ B z = C z` on the
constraint domain, with `e` the mask sum. The PC reduction enters through
`value_correct_of_inspect_none` : the opened scalar the rowcheck uses is the
evaluation of the committed polynomial. The matrix claims come from
`matrix_sumcheck_value`; the chain is closed by `v2_chain`.

`V2Endpoint.sound_nonZK` specialises to non-hiding mode (`e = 0`) and hands
the rows to `satisfies_of_rows`, yielding the R1CS relation.

`V3Endpoint.sound` is the same composition for the V3 schedule, with a
nonzero domain per matrix. The `γ` check is an accepting `matrixEval`
plus `inspectResidual`. `sound_of_openings` reduces the `ẑ`, `h₁`, `g₁`,
and matrix-witness openings the way `h₀` is reduced.
`sound_of_combined_matrix` is the `δ` batch of the three matrix checks.
`matrix_sumcheck_of_selector` turns a selector-batched sum on a common
domain into ` | K | σ = M̂(α, β)`.

The batched endpoint, every check over every circuit and instance, is
`V3Batch.sound` (`BatchEndpoint.lean`).
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

/-- A V2 proof as algebraic / post-decoding data. -/
structure V2Endpoint (F : Type*) [Field F] where
  /-- Constraint domain `R`. -/
  R : EvalDomain F
  /-- Variable domain `C`. -/
  Cd : EvalDomain F
  /-- Nonzero domain `K`. -/
  K : EvalDomain F
  /-- Sparse matrices `A, B, C`. -/
  A : SparseMatrix F
  /-- `B`. -/
  B : SparseMatrix F
  /-- `C`. -/
  Cm : SparseMatrix F
  /-- ZK mode. -/
  mode : SNARKMode
  /-- Committed mask. -/
  mask : F[X]
  /-- Committed assignment polynomial `ẑ`. -/
  zhat : F[X]
  /-- Representation of the committed rowcheck quotient `h₀`. -/
  h0rep : List F
  /-- Opened value of `h₀` at `α`. -/
  vH0 : F
  /-- Lineval commitments `h₁, g₁`. -/
  h1 : F[X]
  /-- `g₁`. -/
  g1 : F[X]
  /-- Matrix sumcheck witnesses for `A` (`g_a, h_a`). -/
  gA : F[X]
  /-- `h_a`. -/
  hA2 : F[X]
  /-- `g_b`. -/
  gB : F[X]
  /-- `h_b`. -/
  hB2 : F[X]
  /-- `g_c`. -/
  gC : F[X]
  /-- `h_c`. -/
  hC2 : F[X]
  /-- Prepare-third sums `σ_{A,B,C}` (used by rowcheck and lineval batching). -/
  σA : F
  /-- `σ_B`. -/
  σB : F
  /-- `σ_C`. -/
  σC : F
  /-- Fourth-round matrix sums `σ^K_{A,B,C}` (`|K| σ^K_M = M̂(α, β)`). -/
  σmA : F
  /-- `σ^K_B`. -/
  σmB : F
  /-- `σ^K_C`. -/
  σmC : F
  /-- `η_B`. -/
  ηB : F
  /-- `η_C`. -/
  ηC : F
  /-- `α`. -/
  α : F
  /-- `β`. -/
  β : F

namespace V2Endpoint

variable {F : Type*} [Field F] [DecidableEq F] (P : V2Endpoint F)

/-- The matrix `a`-polynomial for matrix `M` at the challenges. -/
private noncomputable def aPoly (M : SparseMatrix F) : F[X] :=
  matrixAPoly P.K (P.R.vanishing.eval P.α * P.Cd.vanishing.eval P.β) (rowColVal P.R P.Cd M)

/-- The matrix `b`-polynomial for matrix `M` at the challenges. -/
private noncomputable def bPoly (M : SparseMatrix F) : F[X] :=
  matrixBPoly P.R P.Cd P.K P.α P.β M.rowIdx M.colIdx

/-- The mask sum `e`. -/
private noncomputable def e : F :=
  maskSum P.Cd P.mode P.mask

/-- End-to-end soundness of the V2 endpoint: no PC or AHP break implies the
shifted relation `(A z + e) ∘ B z = C z` on `R`. -/
theorem sound
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hKA : P.A.nK = P.K.n) (hKB : P.B.nK = P.K.n) (hKC : P.Cm.nK = P.K.n)
    (hαR : P.α ∉ P.R.elements) (hβC : P.β ∉ P.Cd.elements)
    (hmA : matrixResidual P.K (P.aPoly P.A) (P.bPoly P.A) P.gA P.hA2 P.σmA = 0)
    (hmB : matrixResidual P.K (P.aPoly P.B) (P.bPoly P.B) P.gB P.hB2 P.σmB = 0)
    (hmC : matrixResidual P.K (P.aPoly P.Cm) (P.bPoly P.Cm) P.gC P.hC2 P.σmC = 0)
    (hdegA : (X * P.gA + C P.σmA).natDegree < P.K.n)
    (hdegB : (X * P.gB + C P.σmB).natDegree < P.K.n)
    (hdegC : (X * P.gC + C P.σmC).natDegree < P.K.n)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrowScalar : P.σA * P.σB - P.σC - P.vH0 * P.R.vanishing.eval P.α = 0)
    (hrowI : inspectResidual
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) P.e) P.α = none)
    (hlin : linevalEval P.mode P.mask P.zhat P.Cd P.ηB P.ηC
      ((P.K.n : F) * P.σmA) ((P.K.n : F) * P.σmB) ((P.K.n : F) * P.σmC)
      (linevalWitness P.Cd P.h1 P.g1 P.ηB P.ηC P.σA P.σB P.σC) P.β = 0)
    (hlinI : inspectResidual (univariateResidual P.Cd
      (linevalPoly P.mode P.mask P.zhat (matrixAtAlpha P.R P.Cd P.A P.α)
        (matrixAtAlpha P.R P.Cd P.B P.α) (matrixAtAlpha P.R P.Cd P.Cm P.α) P.ηB P.ηC)
      (linevalWitness P.Cd P.h1 P.g1 P.ηB P.ηC P.σA P.σB P.σC)) P.β = none)
    (hdegL : (X * P.g1 +
      C ((P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hη : inspectBatch [1, P.ηB, P.ηC]
      (etaClaims P.R P.Cd P.A P.B P.Cm P.zhat P.α P.e P.σA P.σB P.σC) = none) :
    ∀ r, r < P.R.n →
      (mzRow P.Cd P.A P.zhat r + P.e) * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
  -- PC reduction: the opened scalar is the committed polynomial's evaluation.
  have hvH0 : P.vH0 = (toPoly P.h0rep).eval P.α := value_correct_of_inspect_none hH0
  have hrow : rowcheckV2Eval P.R (toPoly P.h0rep) P.σA P.σB P.σC P.α = 0 := by
    unfold rowcheckV2Eval
    rw [← hvH0]; exact hrowScalar
  -- Matrix sumchecks give the fourth-round claims `|K| σ^K_M = M̂(α, β)`.
  have hτA := matrix_sumcheck_value hA hKA hαR hβC hmA hdegA
  have hτB := matrix_sumcheck_value hB hKB hαR hβC hmB hdegB
  have hτC := matrix_sumcheck_value hC hKC hαR hβC hmC hdegC
  -- Close the chain.
  exact v2_chain hA hB hC P.mode hτA hτB hτC hlin hlinI hdegL hη hrow hrowI

/-- In non-hiding mode the mask sum is zero, so the endpoint gives the honest
rows; with the index encoding the constraint list, that is the R1CS relation. -/
theorem sound_nonZK {p : ℕ} [Fact p.Prime] (P : V2Endpoint (ZMod p)) (hmode : P.mode = .NonZK)
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hrows : ∀ r, r < P.R.n →
      (mzRow P.Cd P.A P.zhat r + P.e) * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r)
    {cs : List Constraint} {asg : Assignment} (hfmt : asg 0 = 1)
    (hbnd : systemBounded cs P.Cd.n) (hlen : cs.length ≤ P.R.n)
    (hidxA : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.A.nK P.A.rowIdx P.A.colIdx P.A.value r j = (matrixA cs r j : ZMod p))
    (hidxB : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.B.nK P.B.rowIdx P.B.colIdx P.B.value r j = (matrixB cs r j : ZMod p))
    (hidxC : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.Cm.nK P.Cm.rowIdx P.Cm.colIdx P.Cm.value r j = (matrixC cs r j : ZMod p))
    (hz : ∀ j < P.Cd.n, P.zhat.eval (P.Cd.node j) = (asg j : ZMod p)) :
    satisfies cs asg p := by
  have he : P.e = 0 := by simp [V2Endpoint.e, hmode]
  have hrows' : ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
    intro r hr
    have := hrows r hr
    rwa [he, add_zero] at this
  exact satisfies_of_rows hA hB hC hfmt hbnd hlen hidxA hidxB hidxC hz hrows'

end V2Endpoint

/-! ## V3 endpoint -/

/-- A V3 proof: the V2 algebraic bundle, plus the squeezed `η_A`. -/
structure V3Endpoint (F : Type*) [Field F] extends V2Endpoint F where
  /-- `η_A`, squeezed in prepare-third after the mask and the sums. -/
  ηA : F

namespace V3Endpoint

variable {F : Type*} [Field F] [DecidableEq F] (P : V3Endpoint F)

/-- The matrix `a`-polynomial for matrix `M` on nonzero domain `K`. -/
private noncomputable def aPoly (K : EvalDomain F) (M : SparseMatrix F) : F[X] :=
  matrixAPoly K (P.R.vanishing.eval P.α * P.Cd.vanishing.eval P.β) (rowColVal P.R P.Cd M)

/-- The matrix `b`-polynomial for matrix `M` on nonzero domain `K`. -/
private noncomputable def bPoly (K : EvalDomain F) (M : SparseMatrix F) : F[X] :=
  matrixBPoly P.R P.Cd K P.α P.β M.rowIdx M.colIdx

/-- The mask sum `e`. -/
private noncomputable def e : F :=
  maskSum P.Cd P.mode P.mask

/-- The rowcheck and lineval half of `sound`, from the three matrix claims
` | K_M | σ_M = M̂(α, β)`, however the matrix sumchecks established them. -/
theorem sound_of_matrix_claims (KA KB KC : EvalDomain F)
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hτA : (KA.n : F) * P.σmA = (matrixAtAlpha P.R P.Cd P.A P.α).eval P.β)
    (hτB : (KB.n : F) * P.σmB = (matrixAtAlpha P.R P.Cd P.B P.α).eval P.β)
    (hτC : (KC.n : F) * P.σmC = (matrixAtAlpha P.R P.Cd P.Cm P.α).eval P.β)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrowScalar : P.σA * P.σB - P.σC - P.vH0 * P.R.vanishing.eval P.α = 0)
    (hrowI : inspectResidual
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) 0) P.α = none)
    (hlin : linevalEvalEta P.mode P.mask P.zhat P.Cd P.ηA P.ηB P.ηC
      ((KA.n : F) * P.σmA) ((KB.n : F) * P.σmB) ((KC.n : F) * P.σmC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC) P.β = 0)
    (hlinI : inspectResidual (univariateResidual P.Cd
      (linevalPolyEta P.mode P.mask P.zhat (matrixAtAlpha P.R P.Cd P.A P.α)
        (matrixAtAlpha P.R P.Cd P.B P.α) (matrixAtAlpha P.R P.Cd P.Cm P.α) P.ηA P.ηB P.ηC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC)) P.β = none)
    (hdegL : (X * P.g1 +
      C ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hη : inspectBatch [1, P.ηA, P.ηB, P.ηC]
      (v3Claims P.R P.Cd P.A P.B P.Cm P.zhat P.α P.e P.σA P.σB P.σC) = none) :
    P.e = 0 ∧ ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
  have hvH0 : P.vH0 = (toPoly P.h0rep).eval P.α := value_correct_of_inspect_none hH0
  have hrow : rowcheckV2Eval P.R (toPoly P.h0rep) P.σA P.σB P.σC P.α = 0 := by
    unfold rowcheckV2Eval
    rw [← hvH0]; exact hrowScalar
  exact v3_chain hA hB hC P.mode hτA hτB hτC hlin hlinI hdegL hη hrow hrowI

/-- End-to-end soundness of the V3 endpoint. Each matrix has its own nonzero
domain. The `γ` check is an accepting evaluation plus `inspectResidual`,
which `matrix_extract` turns into the residual identity. No PC or AHP break
implies `e = 0` and `Az ∘ Bz = Cz` on `R`, including in ZK mode. -/
theorem sound
    (KA KB KC : EvalDomain F) (γ : F)
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hKA : P.A.nK = KA.n) (hKB : P.B.nK = KB.n) (hKC : P.Cm.nK = KC.n)
    (hαR : P.α ∉ P.R.elements) (hβC : P.β ∉ P.Cd.elements)
    (hγA : matrixEval KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA γ = 0)
    (hγB : matrixEval KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB γ = 0)
    (hγC : matrixEval KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC γ = 0)
    (hγIA : inspectResidual
      (matrixResidual KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA) γ = none)
    (hγIB : inspectResidual
      (matrixResidual KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB) γ = none)
    (hγIC : inspectResidual
      (matrixResidual KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC) γ = none)
    (hdegA : (X * P.gA + C P.σmA).natDegree < KA.n)
    (hdegB : (X * P.gB + C P.σmB).natDegree < KB.n)
    (hdegC : (X * P.gC + C P.σmC).natDegree < KC.n)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrowScalar : P.σA * P.σB - P.σC - P.vH0 * P.R.vanishing.eval P.α = 0)
    (hrowI : inspectResidual
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) 0) P.α = none)
    (hlin : linevalEvalEta P.mode P.mask P.zhat P.Cd P.ηA P.ηB P.ηC
      ((KA.n : F) * P.σmA) ((KB.n : F) * P.σmB) ((KC.n : F) * P.σmC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC) P.β = 0)
    (hlinI : inspectResidual (univariateResidual P.Cd
      (linevalPolyEta P.mode P.mask P.zhat (matrixAtAlpha P.R P.Cd P.A P.α)
        (matrixAtAlpha P.R P.Cd P.B P.α) (matrixAtAlpha P.R P.Cd P.Cm P.α) P.ηA P.ηB P.ηC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC)) P.β = none)
    (hdegL : (X * P.g1 +
      C ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hη : inspectBatch [1, P.ηA, P.ηB, P.ηC]
      (v3Claims P.R P.Cd P.A P.B P.Cm P.zhat P.α P.e P.σA P.σB P.σC) = none) :
    P.e = 0 ∧ ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
  have hmA := inspectResidual_accepts
    (matrixEval_eq KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA γ ▸ hγA) hγIA
  have hmB := inspectResidual_accepts
    (matrixEval_eq KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB γ ▸ hγB) hγIB
  have hmC := inspectResidual_accepts
    (matrixEval_eq KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC γ ▸ hγC) hγIC
  have hτA := matrix_sumcheck_value hA hKA hαR hβC hmA hdegA
  have hτB := matrix_sumcheck_value hB hKB hαR hβC hmB hdegB
  have hτC := matrix_sumcheck_value hC hKC hαR hβC hmC hdegC
  exact P.sound_of_matrix_claims KA KB KC hA hB hC hτA hτB hτC hH0 hrowScalar hrowI hlin hlinI
    hdegL hη

/-- An opened `ẑ`, `h₁`, and `g₁` make the scalar lineval check the polynomial one. -/
theorem linevalEvalEta_of_openings (mode : SNARKMode) (mask : F[X])
    (zRep h1Rep g1Rep : List F) (Cd : EvalDomain F)
    (ηA ηB ηC τA τB τC vZ vH vG σc β : F)
    (hZ : inspectOpening zRep [] β vZ = none)
    (hH : inspectOpening h1Rep [] β vH = none)
    (hG : inspectOpening g1Rep [] β vG = none)
    (hcheck : (maskPoly mode mask).eval β + (ηA * τA + ηB * τB + ηC * τC) * vZ -
        vH * Cd.vanishing.eval β - β * vG - σc = 0) :
    linevalEvalEta mode mask (toPoly zRep) Cd ηA ηB ηC τA τB τC
      ⟨toPoly h1Rep, toPoly g1Rep, σc⟩ β = 0 := by
  have hz := value_correct_of_inspect_none hZ
  have hh := value_correct_of_inspect_none hH
  have hg := value_correct_of_inspect_none hG
  rw [hz, hh, hg] at hcheck
  simpa [linevalEvalEta] using hcheck

/-- Opened matrix witnesses make the scalar matrix check `matrixEval`. -/
theorem matrixEval_of_openings (a b : F[X]) (gRep hRep : List F) (K : EvalDomain F)
    (σ γ vG vH : F) (hG : inspectOpening gRep [] γ vG = none)
    (hH : inspectOpening hRep [] γ vH = none)
    (hcheck : a.eval γ - b.eval γ * (γ * vG + σ) - vH * K.vanishing.eval γ = 0) :
    matrixEval K a b (toPoly gRep) (toPoly hRep) σ γ = 0 := by
  have hg := value_correct_of_inspect_none hG
  have hh := value_correct_of_inspect_none hH
  rw [hg, hh] at hcheck
  simpa [matrixEval] using hcheck

/-- Openings of `ẑ`, `h₁`, `g₁`, and the three matrix witnesses, together with
the scalar checks the verifier runs on the opened values, are the polynomial
checks `sound` consumes. -/
theorem sound_of_openings
    (KA KB KC : EvalDomain F) (γ : F)
    (zRep h1Rep g1Rep gARep hARep gBRep hBRep gCRep hCRep : List F)
    (vZ vH1 vG1 vGA vHA vGB vHB vGC vHC : F)
    (hZ : P.zhat = toPoly zRep) (hh1 : P.h1 = toPoly h1Rep) (hg1 : P.g1 = toPoly g1Rep)
    (hgA : P.gA = toPoly gARep) (hhA : P.hA2 = toPoly hARep)
    (hgB : P.gB = toPoly gBRep) (hhB : P.hB2 = toPoly hBRep)
    (hgC : P.gC = toPoly gCRep) (hhC : P.hC2 = toPoly hCRep)
    (oZ : inspectOpening zRep [] P.β vZ = none)
    (oH : inspectOpening h1Rep [] P.β vH1 = none)
    (oG : inspectOpening g1Rep [] P.β vG1 = none)
    (oGA : inspectOpening gARep [] γ vGA = none)
    (oHA : inspectOpening hARep [] γ vHA = none)
    (oGB : inspectOpening gBRep [] γ vGB = none)
    (oHB : inspectOpening hBRep [] γ vHB = none)
    (oGC : inspectOpening gCRep [] γ vGC = none)
    (oHC : inspectOpening hCRep [] γ vHC = none)
    (hlinScalar : (maskPoly P.mode P.mask).eval P.β +
        (P.ηA * ((KA.n : F) * P.σmA) + P.ηB * ((KB.n : F) * P.σmB) +
          P.ηC * ((KC.n : F) * P.σmC)) * vZ -
        vH1 * P.Cd.vanishing.eval P.β - P.β * vG1 -
        ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv) = 0)
    (hmatA : (P.aPoly KA P.A).eval γ -
        (P.bPoly KA P.A).eval γ * (γ * vGA + P.σmA) - vHA * KA.vanishing.eval γ = 0)
    (hmatB : (P.aPoly KB P.B).eval γ -
        (P.bPoly KB P.B).eval γ * (γ * vGB + P.σmB) - vHB * KB.vanishing.eval γ = 0)
    (hmatC : (P.aPoly KC P.Cm).eval γ -
        (P.bPoly KC P.Cm).eval γ * (γ * vGC + P.σmC) - vHC * KC.vanishing.eval γ = 0)
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hKA : P.A.nK = KA.n) (hKB : P.B.nK = KB.n) (hKC : P.Cm.nK = KC.n)
    (hαR : P.α ∉ P.R.elements) (hβC : P.β ∉ P.Cd.elements)
    (hγIA : inspectResidual
      (matrixResidual KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA) γ = none)
    (hγIB : inspectResidual
      (matrixResidual KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB) γ = none)
    (hγIC : inspectResidual
      (matrixResidual KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC) γ = none)
    (hdegA : (X * P.gA + C P.σmA).natDegree < KA.n)
    (hdegB : (X * P.gB + C P.σmB).natDegree < KB.n)
    (hdegC : (X * P.gC + C P.σmC).natDegree < KC.n)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrowScalar : P.σA * P.σB - P.σC - P.vH0 * P.R.vanishing.eval P.α = 0)
    (hrowI : inspectResidual
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) 0) P.α = none)
    (hlinI : inspectResidual (univariateResidual P.Cd
      (linevalPolyEta P.mode P.mask P.zhat (matrixAtAlpha P.R P.Cd P.A P.α)
        (matrixAtAlpha P.R P.Cd P.B P.α) (matrixAtAlpha P.R P.Cd P.Cm P.α) P.ηA P.ηB P.ηC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC)) P.β = none)
    (hdegL : (X * P.g1 +
      C ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hη : inspectBatch [1, P.ηA, P.ηB, P.ηC]
      (v3Claims P.R P.Cd P.A P.B P.Cm P.zhat P.α P.e P.σA P.σB P.σC) = none) :
    P.e = 0 ∧ ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
  have hlin0 := linevalEvalEta_of_openings P.mode P.mask zRep h1Rep g1Rep P.Cd P.ηA P.ηB P.ηC
    ((KA.n : F) * P.σmA) ((KB.n : F) * P.σmB) ((KC.n : F) * P.σmC) vZ vH1 vG1
    ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv) P.β oZ oH oG hlinScalar
  rw [← hZ, ← hh1, ← hg1] at hlin0
  have hlin : linevalEvalEta P.mode P.mask P.zhat P.Cd P.ηA P.ηB P.ηC
      ((KA.n : F) * P.σmA) ((KB.n : F) * P.σmB) ((KC.n : F) * P.σmC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC) P.β = 0 := by
    simpa [linevalWitnessEta] using hlin0
  have hγA0 := matrixEval_of_openings (P.aPoly KA P.A) (P.bPoly KA P.A) gARep hARep KA
    P.σmA γ vGA vHA oGA oHA hmatA
  rw [← hgA, ← hhA] at hγA0
  have hγB0 := matrixEval_of_openings (P.aPoly KB P.B) (P.bPoly KB P.B) gBRep hBRep KB
    P.σmB γ vGB vHB oGB oHB hmatB
  rw [← hgB, ← hhB] at hγB0
  have hγC0 := matrixEval_of_openings (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) gCRep hCRep KC
    P.σmC γ vGC vHC oGC oHC hmatC
  rw [← hgC, ← hhC] at hγC0
  exact sound P KA KB KC γ hA hB hC hKA hKB hKC hαR hβC hγA0 hγB0 hγC0 hγIA hγIB hγIC
    hdegA hdegB hdegC hH0 hrowScalar hrowI hlin hlinI hdegL hη

/-- One `δ`-combination of the three matrix checks, plus each residual
inspector, is the three accepting checks `sound` consumes. -/
theorem sound_of_combined_matrix
    (KA KB KC : EvalDomain F) (γ δA δB δC : F)
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hKA : P.A.nK = KA.n) (hKB : P.B.nK = KB.n) (hKC : P.Cm.nK = KC.n)
    (hαR : P.α ∉ P.R.elements) (hβC : P.β ∉ P.Cd.elements)
    (hcomb : weightedSum [δA, δB, δC]
        [matrixEval KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA γ,
          matrixEval KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB γ,
          matrixEval KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC γ] = 0)
    (hcombI : inspectBatch [δA, δB, δC]
        [matrixEval KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA γ,
          matrixEval KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB γ,
          matrixEval KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC γ] = none)
    (hγIA : inspectResidual
      (matrixResidual KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA) γ = none)
    (hγIB : inspectResidual
      (matrixResidual KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB) γ = none)
    (hγIC : inspectResidual
      (matrixResidual KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC) γ = none)
    (hdegA : (X * P.gA + C P.σmA).natDegree < KA.n)
    (hdegB : (X * P.gB + C P.σmB).natDegree < KB.n)
    (hdegC : (X * P.gC + C P.σmC).natDegree < KC.n)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrowScalar : P.σA * P.σB - P.σC - P.vH0 * P.R.vanishing.eval P.α = 0)
    (hrowI : inspectResidual
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) 0) P.α = none)
    (hlin : linevalEvalEta P.mode P.mask P.zhat P.Cd P.ηA P.ηB P.ηC
      ((KA.n : F) * P.σmA) ((KB.n : F) * P.σmB) ((KC.n : F) * P.σmC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC) P.β = 0)
    (hlinI : inspectResidual (univariateResidual P.Cd
      (linevalPolyEta P.mode P.mask P.zhat (matrixAtAlpha P.R P.Cd P.A P.α)
        (matrixAtAlpha P.R P.Cd P.B P.α) (matrixAtAlpha P.R P.Cd P.Cm P.α) P.ηA P.ηB P.ηC)
      (linevalWitnessEta P.Cd P.h1 P.g1 P.ηA P.ηB P.ηC P.σA P.σB P.σC)) P.β = none)
    (hdegL : (X * P.g1 +
      C ((P.ηA * P.σA + P.ηB * P.σB + P.ηC * P.σC) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hη : inspectBatch [1, P.ηA, P.ηB, P.ηC]
      (v3Claims P.R P.Cd P.A P.B P.Cm P.zhat P.α P.e P.σA P.σB P.σC) = none) :
    P.e = 0 ∧ ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r := by
  have hz := inspectBatch_accepts hcomb hcombI
  have hγA : matrixEval KA (P.aPoly KA P.A) (P.bPoly KA P.A) P.gA P.hA2 P.σmA γ = 0 :=
    hz _ (by simp)
  have hγB : matrixEval KB (P.aPoly KB P.B) (P.bPoly KB P.B) P.gB P.hB2 P.σmB γ = 0 :=
    hz _ (by simp)
  have hγC : matrixEval KC (P.aPoly KC P.Cm) (P.bPoly KC P.Cm) P.gC P.hC2 P.σmC γ = 0 :=
    hz _ (by simp)
  exact sound P KA KB KC γ hA hB hC hKA hKB hKC hαR hβC hγA hγB hγC hγIA hγIB hγIC
    hdegA hdegB hdegC hH0 hrowScalar hrowI hlin hlinI hdegL hη

/-- `|K| σ = M̂(α, β)` from a selector-batched sum on a common domain `H`.
`batchedSumcheck_extract` turns the big-domain sum into the sum on `K`, and
`matrix_sumcheck_value_of_sum` turns that into the lineval claim. -/
theorem matrix_sumcheck_of_selector {R Cd H K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β σ : F} {g h : F[X]}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements) (hdvd : K.n ∣ H.n)
    (hres : matrixResidual K
      (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M))
      (matrixBPoly R Cd K α β M.rowIdx M.colIdx) g h σ = 0)
    (hsum : ∑ x ∈ H.elements,
        (weightedSumPoly [1]
          ([(K, X * g + C σ, (K.n : F) * σ)].map fun c =>
            selectorPoly H c.1 * c.2.1)).eval x =
          weightedSum [1]
            ([(K, X * g + C σ, (K.n : F) * σ)].map fun c => c.2.2))
    (hnone : inspectBatch ([1] : List F)
        (batchedSumClaims [(K, X * g + C σ, (K.n : F) * σ)]) = none) :
    (K.n : F) * σ = (matrixAtAlpha R Cd M α).eval β := by
  have hsub := batchedSumcheck_extract (H := H) (ws := [1])
    (cs := [(K, X * g + C σ, (K.n : F) * σ)])
    (hdvd := by
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact hdvd) hsum hnone
  have hrange : ∑ k ∈ Finset.range K.n, (X * g + C σ).eval (K.node k) = (K.n : F) * σ := by
    have hdom := sum_range_node K fun x => (X * g + C σ).eval x
    have hclaim := hsub (K, X * g + C σ, (K.n : F) * σ) (by simp)
    simpa using hdom.trans hclaim
  exact matrix_sumcheck_value_of_sum hM hK hα hβ hres hrange

/-- V3 reaches the R1CS relation in either mode: the mask sum is forced to zero. -/
theorem sound_r1cs {p : ℕ} [Fact p.Prime] (P : V3Endpoint (ZMod p))
    (hA : P.A.Bounded P.R P.Cd) (hB : P.B.Bounded P.R P.Cd) (hC : P.Cm.Bounded P.R P.Cd)
    (hrows : ∀ r, r < P.R.n →
      mzRow P.Cd P.A P.zhat r * mzRow P.Cd P.B P.zhat r = mzRow P.Cd P.Cm P.zhat r)
    {cs : List Constraint} {asg : Assignment} (hfmt : asg 0 = 1)
    (hbnd : systemBounded cs P.Cd.n) (hlen : cs.length ≤ P.R.n)
    (hidxA : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.A.nK P.A.rowIdx P.A.colIdx P.A.value r j = (matrixA cs r j : ZMod p))
    (hidxB : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.B.nK P.B.rowIdx P.B.colIdx P.B.value r j = (matrixB cs r j : ZMod p))
    (hidxC : ∀ r < cs.length, ∀ j < P.Cd.n,
      matrixAt P.Cm.nK P.Cm.rowIdx P.Cm.colIdx P.Cm.value r j = (matrixC cs r j : ZMod p))
    (hz : ∀ j < P.Cd.n, P.zhat.eval (P.Cd.node j) = (asg j : ZMod p)) :
    satisfies cs asg p :=
  satisfies_of_rows hA hB hC hfmt hbnd hlen hidxA hidxB hidxC hz hrows

end V3Endpoint

end Varuna