/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Composition
import Varuna.MatrixSumcheck
import Varuna.Algebraic
import Varuna.Bridge

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

/-- The matrix `a`-polynomial for matrix `M` at the challenges. -/
private noncomputable def aPoly (M : SparseMatrix F) : F[X] :=
  matrixAPoly P.K (P.R.vanishing.eval P.α * P.Cd.vanishing.eval P.β) (rowColVal P.R P.Cd M)

/-- The matrix `b`-polynomial for matrix `M` at the challenges. -/
private noncomputable def bPoly (M : SparseMatrix F) : F[X] :=
  matrixBPoly P.R P.Cd P.K P.α P.β M.rowIdx M.colIdx

/-- The mask sum `e`. -/
private noncomputable def e : F :=
  maskSum P.Cd P.mode P.mask

/-- End-to-end soundness of the V3 endpoint. No PC or AHP break implies
`e = 0` and `Az ∘ Bz = Cz` on `R`, including in ZK mode. -/
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
      (shiftedRowResidual P.R P.Cd P.A P.B P.Cm P.zhat (toPoly P.h0rep) 0) P.α = none)
    (hlin : linevalEvalEta P.mode P.mask P.zhat P.Cd P.ηA P.ηB P.ηC
      ((P.K.n : F) * P.σmA) ((P.K.n : F) * P.σmB) ((P.K.n : F) * P.σmC)
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
  have hτA := matrix_sumcheck_value hA hKA hαR hβC hmA hdegA
  have hτB := matrix_sumcheck_value hB hKB hαR hβC hmB hdegB
  have hτC := matrix_sumcheck_value hC hKC hαR hβC hmC hdegC
  exact v3_chain hA hB hC P.mode hτA hτB hτC hlin hlinI hdegL hη hrow hrowI

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