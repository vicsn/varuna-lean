/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Endpoint
import Varuna.MatrixBatch
import Varuna.FSBound
import Varuna.Statement
import Varuna.PublicInput

/-!
# The batched V3 endpoint

snarkVM proves a batch : several circuits, several instances of each, in one
proof. A `V3Batch` bundles such a proof as algebraic data. Every check is one
linear combination over the whole batch, selector-lifted to the largest
domain and weighted by squeezed combiners :

* rowcheck at `α` : `Σ ν_i τ_{i,j} s_{R,R_i}(α)(σ_A σ_B − σ_C)_{i,j} − v_R(α) h₀(α)`,
  with one `h₀` on the largest constraint domain `R` (`rowEval`);
* lineval at `β` : the mask, plus `Σ μ_i ρ_{i,j} s_{C,C_i}(β) Σ_M η_M τ_{M,i} ẑ_{i,j}(β)`,
  less `v_C(β) h₁(β) + β g₁(β)` and the batch sum, with
  `τ_{M,i} = | K_{M,i} | σ_{M,i}` (`linEval`);
* matrix at `γ` : every matrix of every circuit, `δ`-weighted, with one `h₂`
  (`batchedMatrixEval`).

`V3Batch.sound` : if the three LCs accept, no residual has a Schwartz–Zippel
break, and no combiner draw is lucky, the mask sum is zero and every instance
satisfies `Az ∘ Bz = Cz` on its circuit's constraint domain. The matrix batch
gives each circuit's ` | K_M | σ_M = M̂(α, β)` (`batchedMatrix_extract`); the
lineval, given those, gives each instance's `σ_M` as its lineval target; the
rowcheck, given those, gives the rows (`batchedZerocheck_extract`).

`V3Batch.sound_of_openings` runs the lineval and matrix LCs on the values the
verifier reads : the opened `s(β)`, `ŵ_{i,j}(β)`, `h₁(β)`, `g₁(β)`,
`g_{M,i}(γ)`, `h₂(γ)`, with `ẑ_{i,j}(β) = x̂_{i,j}(β) + v_{X_i}(β) ŵ_{i,j}(β)`
from the public input. An opening with no break (`OpenedAt`) is the
polynomial's value, so these are the LCs `sound` consumes.

`V3Batch.sound_of_transcript` reads the challenges and weights off the
squeezes of a V3 transcript with snarkVM's schemes, and replaces the six
break hypotheses with one : the output does not break
(`outputBreaks … = false`, charged in `V3Batch.adaptive_soundness`). The
transcript's init absorbs the batch's statement (`v3Init`), so the relation
holds for the one statement the transcript binds, each instance's `ẑ` equal
to its public input on the input domain.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- A matrix term's summand in `matrix_sumcheck` at `γ` on `K`, with `g(γ)` read as `vg`. -/
noncomputable def MatrixTerm.summandAt (K : EvalDomain F) (t : MatrixTerm F) (γ vg : F) : F :=
  (selectorPoly K t.K).eval γ * (t.a.eval γ - t.b.eval γ * (γ * vg + t.σ))

/-- `v` opens `p` at `z` with no break : `p` is the polynomial of a representation
whose opening at `z` to `v` inspection passes. -/
def OpenedAt [DecidableEq F] (p : F[X]) (z v : F) : Prop :=
  ∃ rep q : List F, p = toPoly rep ∧ inspectOpening rep q z v = none

theorem OpenedAt.eq_eval [DecidableEq F] {p : F[X]} {z v : F} (h : OpenedAt p z v) :
    v = p.eval z := by
  obtain ⟨rep, q, rfl, h⟩ := h
  exact value_correct_of_inspect_none h

theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- One instance of a circuit in a V3 batch. -/
structure BatchInstance (F : Type*) [Field F] where
  /-- Formatted public input. -/
  x : List F
  /-- Witness polynomial `ŵ`. -/
  w : F[X]
  /-- Prepare-third sum for `A`. -/
  σA : F
  /-- Prepare-third sum for `B`. -/
  σB : F
  /-- Prepare-third sum for `C`. -/
  σC : F
  /-- Opened `ŵ(β)`. -/
  vw : F

/-- One circuit of a V3 batch, with its instances. -/
structure BatchCircuit (F : Type*) [Field F] where
  /-- Constraint domain. -/
  R : EvalDomain F
  /-- Variable domain. -/
  Cd : EvalDomain F
  /-- Public-input domain. -/
  Xd : EvalDomain F
  /-- Nonzero domain of `A`. -/
  KA : EvalDomain F
  /-- Nonzero domain of `B`. -/
  KB : EvalDomain F
  /-- Nonzero domain of `C`. -/
  KC : EvalDomain F
  /-- Matrix `A`. -/
  A : SparseMatrix F
  /-- Matrix `B`. -/
  B : SparseMatrix F
  /-- Matrix `C`. -/
  Cm : SparseMatrix F
  /-- Matrix-sumcheck `g` for `A`. -/
  gA : F[X]
  /-- Matrix-sumcheck `g` for `B`. -/
  gB : F[X]
  /-- Matrix-sumcheck `g` for `C`. -/
  gC : F[X]
  /-- Fourth-round sum for `A`. -/
  σmA : F
  /-- Fourth-round sum for `B`. -/
  σmB : F
  /-- Fourth-round sum for `C`. -/
  σmC : F
  /-- Opened `g_A(γ)`. -/
  vgA : F
  /-- Opened `g_B(γ)`. -/
  vgB : F
  /-- Opened `g_C(γ)`. -/
  vgC : F
  /-- The instances, in order. -/
  insts : List (BatchInstance F)

namespace BatchCircuit

variable (c : BatchCircuit F)

/-- `ẑ = x̂ + v_X ŵ`, with `x̂` the interpolant of the public input on `X`. -/
noncomputable def zhat (x : BatchInstance F) : F[X] :=
  assignmentPoly c.Xd (c.Xd.interpolate fun k => x.x.getD k 0) x.w

/-- `LDE(Az) LDE(Bz) − LDE(Cz)` on the circuit's constraint domain. -/
noncomputable def rowPoly (x : BatchInstance F) : F[X] :=
  mzPoly c.R c.Cd c.A (c.zhat x) * mzPoly c.R c.Cd c.B (c.zhat x) -
    mzPoly c.R c.Cd c.Cm (c.zhat x)

/-- An instance's lineval term `Σ_M η_M M̂(α, X) ẑ(X)`. -/
noncomputable def linPoly (x : BatchInstance F) (α ηA ηB ηC : F) : F[X] :=
  (C ηA * matrixAtAlpha c.R c.Cd c.A α + C ηB * matrixAtAlpha c.R c.Cd c.B α +
    C ηC * matrixAtAlpha c.R c.Cd c.Cm α) * c.zhat x

/-- The lineval target of matrix `M` for an instance. -/
noncomputable def target (x : BatchInstance F) (M : SparseMatrix F) (α : F) : F :=
  linevalTarget c.R c.Cd M (c.zhat x) α

/-- The three terms the circuit contributes to `matrix_sumcheck`, `A, B, C` in order. -/
def matrixTerms (α β : F) : List (MatrixTerm F) :=
  [⟨c.R, c.Cd, c.KA, c.A, α, β, c.gA, c.σmA⟩, ⟨c.R, c.Cd, c.KB, c.B, α, β, c.gB, c.σmB⟩,
    ⟨c.R, c.Cd, c.KC, c.Cm, α, β, c.gC, c.σmC⟩]

/-- The circuit's three `matrix_sumcheck` summands at `γ` on `K`, from the opened
`g_M(γ)`. -/
noncomputable def matrixSummands (K : EvalDomain F) (α β γ : F) : List F :=
  [MatrixTerm.summandAt K ⟨c.R, c.Cd, c.KA, c.A, α, β, c.gA, c.σmA⟩ γ c.vgA,
    MatrixTerm.summandAt K ⟨c.R, c.Cd, c.KB, c.B, α, β, c.gB, c.σmB⟩ γ c.vgB,
    MatrixTerm.summandAt K ⟨c.R, c.Cd, c.KC, c.Cm, α, β, c.gC, c.σmC⟩ γ c.vgC]

theorem sum_linPoly {c : BatchCircuit F} (hA : c.A.Bounded c.R c.Cd)
    (hB : c.B.Bounded c.R c.Cd) (hC : c.Cm.Bounded c.R c.Cd) (x : BatchInstance F)
    (α ηA ηB ηC : F) :
    ∑ i ∈ range c.Cd.n, (c.linPoly x α ηA ηB ηC).eval (c.Cd.node i) =
      ηA * c.target x c.A α + ηB * c.target x c.B α + ηC * c.target x c.Cm α := by
  have h := sum_linevalPolyEta hA hB hC .NonZK 0 (c.zhat x) ηA ηB ηC α
  simpa [linevalPolyEta, linPoly, target] using h

end BatchCircuit

/-- What a circuit's commitments carry besides its polynomials : each instance's `ŵ`
blinding (its part along the powers of `gamma_g`), and for each degree-bounded `g_M` the
part of its commitment below the shift, and its blinding. -/
structure CircuitExtra (F : Type*) [Field F] where
  /-- Each instance's `ŵ` blinding. -/
  wBlind : List F[X] := []
  /-- `g_A`'s commitment below the shift. -/
  gALow : F[X] := 0
  /-- `g_B`'s commitment below the shift. -/
  gBLow : F[X] := 0
  /-- `g_C`'s commitment below the shift. -/
  gCLow : F[X] := 0
  /-- `g_A`'s blinding. -/
  gABlind : F[X] := 0
  /-- `g_B`'s blinding. -/
  gBBlind : F[X] := 0
  /-- `g_C`'s blinding. -/
  gCBlind : F[X] := 0

/-- What the batch's commitments carry besides its polynomials : the blindings of the
mask, `h₀`, `h₁`, `g₁` and `h₂`, the part of `g₁`'s commitment below the shift, and each
circuit's. -/
structure BatchExtra (F : Type*) [Field F] where
  /-- The mask's blinding. -/
  maskBlind : F[X] := 0
  /-- `h₀`'s blinding. -/
  h0Blind : F[X] := 0
  /-- `h₁`'s blinding. -/
  h1Blind : F[X] := 0
  /-- `g₁`'s commitment below the shift. -/
  g1Low : F[X] := 0
  /-- `g₁`'s blinding. -/
  g1Blind : F[X] := 0
  /-- `h₂`'s blinding. -/
  h2Blind : F[X] := 0
  /-- Each circuit's, in order. -/
  circuits : List (CircuitExtra F) := []

/-- A V3 batch proof as algebraic / post-decoding data. -/
structure V3Batch (F : Type*) [Field F] where
  /-- The circuits, in order. -/
  circuits : List (BatchCircuit F)
  /-- Largest constraint domain. -/
  R : EvalDomain F
  /-- Largest variable domain. -/
  Cd : EvalDomain F
  /-- Largest nonzero domain. -/
  K : EvalDomain F
  /-- ZK or not. -/
  mode : SNARKMode
  /-- Lineval mask polynomial. -/
  mask : F[X]
  /-- Representation of the committed rowcheck quotient `h₀`. -/
  h0rep : List F
  /-- Opened value `h₀(α)`. -/
  vH0 : F
  /-- Lineval quotient. -/
  h1 : F[X]
  /-- Lineval remainder. -/
  g1 : F[X]
  /-- Matrix-sumcheck quotient. -/
  h2 : F[X]
  /-- Rowcheck challenge. -/
  α : F
  /-- Lineval challenge. -/
  β : F
  /-- Matrix-sumcheck challenge. -/
  γ : F
  /-- Lineval weight of `A`. -/
  ηA : F
  /-- Lineval weight of `B`. -/
  ηB : F
  /-- Lineval weight of `C`. -/
  ηC : F
  /-- Opened mask `s(β)`. -/
  vMask : F
  /-- Opened `h₁(β)`. -/
  vH1 : F
  /-- Opened `g₁(β)`. -/
  vG1 : F
  /-- Opened `h₂(γ)`. -/
  vH2 : F
  /-- The SRS's largest power `M` : a commitment with degree bound `d` is shifted by
  `X^{M−d}`. -/
  srsMax : ℕ := 0
  /-- What the commitments carry besides the polynomials. -/
  ext : BatchExtra F := {}

namespace V3Batch

variable (P : V3Batch F)

/-- Every instance with its circuit, circuit by circuit. -/
def instances : List (BatchCircuit F × BatchInstance F) :=
  P.circuits.flatMap fun c => c.insts.map (c, ·)

/-- Instances per circuit. -/
def sizes : List ℕ :=
  P.circuits.map fun c => c.insts.length

/-- The public inputs, per circuit and instance, as `v3Init` absorbs them. -/
def statement : List (List (List F)) :=
  P.circuits.map fun c => c.insts.map BatchInstance.x

/-- Every matrix term of every circuit, in `matrix_sumcheck` order (`ahp.rs:365-397`). -/
def matrixTerms : List (MatrixTerm F) :=
  P.circuits.flatMap fun c => c.matrixTerms P.α P.β

/-- The mask sum over the largest variable domain. -/
noncomputable def e : F :=
  maskSum P.Cd P.mode P.mask

/-- Per-instance rowcheck claims, on each circuit's constraint domain. -/
noncomputable def rowClaims : List (EvalDomain F × F[X]) :=
  P.instances.map fun p => (p.1.R, p.1.rowPoly p.2)

/-- The batched rowcheck residual. -/
noncomputable def rowResidual (ws : List F) : F[X] :=
  batchedZerocheck P.R ws P.rowClaims - toPoly P.h0rep * P.R.vanishing

/-- snarkVM's `rowcheck_zerocheck` at `α`, from the prepare-third sums. -/
noncomputable def rowEval (ws : List F) : F :=
  weightedSum ws (P.instances.map fun p =>
    (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC)) -
    P.vH0 * P.R.vanishing.eval P.α

/-- The batch's lineval sum `Σ μ_i ρ_{i,j} Σ_M η_M σ_{M,i,j}`. -/
def linSum (ws : List F) : F :=
  weightedSum ws (P.instances.map fun p => P.ηA * p.2.σA + P.ηB * p.2.σB + P.ηC * p.2.σC)

/-- The batched lineval polynomial. -/
noncomputable def linevalPoly (ws : List F) : F[X] :=
  maskPoly P.mode P.mask + weightedSumPoly ws (P.instances.map fun p =>
    selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC)

/-- The lineval sumcheck witness, with the batch sum over ` | C | `. -/
noncomputable def linWitness (ws : List F) : UnivariateWitness F :=
  ⟨P.h1, P.g1, P.linSum ws * P.Cd.sizeInv⟩

/-- The batched lineval residual. -/
noncomputable def linResidual (ws : List F) : F[X] :=
  univariateResidual P.Cd (P.linevalPoly ws) (P.linWitness ws)

/-- snarkVM's `lineval_sumcheck` at `β`, reading `M̂_i(α, β)` as ` | K_{M,i} | σ_{M,i}`. -/
noncomputable def linEval (ws : List F) : F :=
  (maskPoly P.mode P.mask).eval P.β +
      weightedSum ws (P.instances.map fun p => (selectorPoly P.Cd p.1.Cd).eval P.β *
        ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
          P.ηC * ((p.1.KC.n : F) * p.1.σmC)) * (p.1.zhat p.2).eval P.β)) -
    P.h1.eval P.β * P.Cd.vanishing.eval P.β - P.β * P.g1.eval P.β - P.linSum ws * P.Cd.sizeInv

/-- The lineval claims : the mask sum, then each instance's `target_M − σ_M`. -/
noncomputable def linClaims : List F :=
  P.e :: P.instances.flatMap fun p =>
    [p.1.target p.2 p.1.A P.α - p.2.σA, p.1.target p.2 p.1.B P.α - p.2.σB,
      p.1.target p.2 p.1.Cm P.α - p.2.σC]

theorem fst_mem_circuits {p : BatchCircuit F × BatchInstance F} (hp : p ∈ P.instances) :
    p.1 ∈ P.circuits := by
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
  exact hc

theorem matrixTerms_mem {c : BatchCircuit F} (hc : c ∈ P.circuits) :
    (⟨c.R, c.Cd, c.KA, c.A, P.α, P.β, c.gA, c.σmA⟩ : MatrixTerm F) ∈ P.matrixTerms ∧
      (⟨c.R, c.Cd, c.KB, c.B, P.α, P.β, c.gB, c.σmB⟩ : MatrixTerm F) ∈ P.matrixTerms ∧
      (⟨c.R, c.Cd, c.KC, c.Cm, P.α, P.β, c.gC, c.σmC⟩ : MatrixTerm F) ∈ P.matrixTerms := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact List.mem_flatMap.mpr ⟨c, hc, by simp [BatchCircuit.matrixTerms]⟩

theorem length_instances : P.instances.length = P.sizes.sum := by
  simp [instances, sizes, List.length_flatMap]

theorem sum_le_sum_pred_succ : ∀ ms : List ℕ, ms.sum ≤ (ms.map (· - 1 + 1)).sum
  | [] => le_rfl
  | m :: ms => by
    have := sum_le_sum_pred_succ ms
    simp only [List.sum_cons, List.map_cons]
    omega

theorem length_rowClaims_le : P.rowClaims.length ≤ (P.sizes.map (· - 1 + 1)).sum := by
  rw [rowClaims, List.length_map, length_instances]
  exact sum_le_sum_pred_succ _

theorem length_linClaims_le : P.linClaims.length ≤ (P.sizes.map (· - 1 + 1)).sum * 3 + 1 := by
  have h : P.linClaims.length = P.instances.length * 3 + 1 := by
    simp [linClaims, List.length_flatMap]
  rw [h, length_instances]
  have := sum_le_sum_pred_succ P.sizes
  omega

theorem length_matrixTerms : P.matrixTerms.length = 3 * P.circuits.length := by
  unfold matrixTerms
  induction P.circuits with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]
    simp [BatchCircuit.matrixTerms]
    ring

end V3Batch

/-- Three claims per item, weighted `w η_A, w η_B, w η_C` by the item's weight `w`. -/
theorem weightedSum_flatMap_three {α : Type*} (a b c : F) (f g h : α → F) :
    ∀ (ws : List F) (cs : List α),
      weightedSum (ws.flatMap fun w => [w * a, w * b, w * c])
          (cs.flatMap fun p => [f p, g p, h p]) =
        weightedSum ws (cs.map fun p => a * f p + b * g p + c * h p)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | w :: ws, p :: cs => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, weightedSum_cons,
      List.map_cons, weightedSum_flatMap_three a b c f g h ws cs]
    ring

namespace V3Batch

variable [DecidableEq F] (P : V3Batch F)

/-- End-to-end soundness of a V3 batch, every check batched over every circuit and
instance. If the rowcheck, lineval and matrix LCs accept, the opened `h₀(α)` and
the three residuals report no break, and none of the three combiner draws is lucky,
then the mask sum is zero and every instance satisfies `Az ∘ Bz = Cz` on its
circuit's constraint domain. -/
theorem sound (rowWs linWs δs : List F)
    (hdvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n) (hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n)
    (hdvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n) (hvalid : ∀ t ∈ P.matrixTerms, t.Valid)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrow : P.rowEval rowWs = 0) (hrowI : inspectResidual (P.rowResidual rowWs) P.α = none)
    (hrowB : inspectBatchOn P.R.nodeList rowWs (batchedClaims P.R P.rowClaims) = none)
    (hlin : P.linEval linWs = 0) (hlinI : inspectResidual (P.linResidual linWs) P.β = none)
    (hdegL : (X * P.g1 + C (P.linSum linWs * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hlinB : inspectBatch (etaWeights linWs P.ηA P.ηB P.ηC) P.linClaims = none)
    (hmat : batchedMatrixEval P.K δs P.matrixTerms P.h2 P.γ = 0)
    (hmatI : inspectResidual (batchedMatrixResidual P.K δs P.matrixTerms P.h2) P.γ = none)
    (hmatB : inspectBatchOn P.K.nodeList δs
      (batchedClaims P.K (P.matrixTerms.map MatrixTerm.claim)) = none) :
    P.e = 0 ∧ ∀ p ∈ P.instances, ∀ r, r < p.1.R.n →
      mzRow p.1.Cd p.1.A (p.1.zhat p.2) r * mzRow p.1.Cd p.1.B (p.1.zhat p.2) r =
        mzRow p.1.Cd p.1.Cm (p.1.zhat p.2) r := by
  have hτ := batchedMatrix_extract hdvdK hvalid hmat hmatI hmatB
  have hcirc : ∀ c ∈ P.circuits, c.A.Bounded c.R c.Cd ∧ c.B.Bounded c.R c.Cd ∧
      c.Cm.Bounded c.R c.Cd ∧
      (c.KA.n : F) * c.σmA = (matrixAtAlpha c.R c.Cd c.A P.α).eval P.β ∧
      (c.KB.n : F) * c.σmB = (matrixAtAlpha c.R c.Cd c.B P.α).eval P.β ∧
      (c.KC.n : F) * c.σmC = (matrixAtAlpha c.R c.Cd c.Cm P.α).eval P.β := by
    intro c hc
    obtain ⟨mA, mB, mC⟩ := P.matrixTerms_mem hc
    exact ⟨(hvalid _ mA).bounded, (hvalid _ mB).bounded, (hvalid _ mC).bounded, hτ _ mA,
      hτ _ mB, hτ _ mC⟩
  -- lineval
  have hlinTerm : ∀ p ∈ P.instances, (selectorPoly P.Cd p.1.Cd).eval P.β *
      ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
        P.ηC * ((p.1.KC.n : F) * p.1.σmC)) * (p.1.zhat p.2).eval P.β) =
      (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval P.β := by
    intro p hp
    obtain ⟨-, -, -, hA, hB, hC⟩ := hcirc _ (P.fst_mem_circuits hp)
    simp only [BatchCircuit.linPoly, eval_mul, eval_add, eval_C, hA, hB, hC]
  have hlinEq : P.linEval linWs = (P.linResidual linWs).eval P.β := by
    rw [linEval, List.map_congr_left hlinTerm]
    simp only [linResidual, univariateResidual, linevalPoly, linWitness, eval_sub, eval_add,
      eval_mul, eval_X, eval_C, eval_weightedSumPoly, List.map_map, Function.comp_def]
  have hsum := univariate_sum (inspectResidual_accepts (hlinEq.symm.trans hlin) hlinI) hdegL
  have hsumInst : ∀ p ∈ P.instances, ∑ i ∈ range P.Cd.n,
      (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval (P.Cd.node i) =
      P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
        P.ηC * p.1.target p.2 p.1.Cm P.α := by
    intro p hp
    have hc := P.fst_mem_circuits hp
    obtain ⟨hA, hB, hC, -⟩ := hcirc _ hc
    calc ∑ i ∈ range P.Cd.n,
          (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval (P.Cd.node i)
        = ∑ x ∈ P.Cd.elements,
          (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval x :=
          sum_range_node P.Cd fun x =>
            (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval x
      _ = ∑ x ∈ p.1.Cd.elements, (p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval x :=
          sum_selectorPoly_mul (hdvdC _ hc) _
      _ = ∑ i ∈ range p.1.Cd.n, (p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval (p.1.Cd.node i) :=
          (sum_range_node p.1.Cd fun x => (p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval x).symm
      _ = _ := BatchCircuit.sum_linPoly hA hB hC p.2 P.α P.ηA P.ηB P.ηC
  have hsumAll : ∑ i ∈ range P.Cd.n, (P.linevalPoly linWs).eval (P.Cd.node i) =
      P.e + weightedSum linWs (P.instances.map fun p =>
        P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
          P.ηC * p.1.target p.2 p.1.Cm P.α) := by
    simp only [linevalPoly, eval_add, eval_weightedSumPoly, List.map_map, Function.comp_def,
      sum_add_distrib]
    rw [sum_weightedSum, List.map_congr_left hsumInst]
    rfl
  have hn : (P.Cd.n : F) * (P.linSum linWs * P.Cd.sizeInv) = P.linSum linWs := by
    rw [mul_comm, mul_assoc, mul_comm P.Cd.sizeInv, ← EvalDomain.sizeAsField, P.Cd.mul_sizeInv,
      mul_one]
  have hlinSum := hsumAll.symm.trans (hsum.trans hn)
  have hws : weightedSum (etaWeights linWs P.ηA P.ηB P.ηC) P.linClaims = 0 := by
    have hsplit : weightedSum linWs (P.instances.map fun p =>
        P.ηA * (p.1.target p.2 p.1.A P.α - p.2.σA) + P.ηB * (p.1.target p.2 p.1.B P.α - p.2.σB) +
          P.ηC * (p.1.target p.2 p.1.Cm P.α - p.2.σC)) =
        weightedSum linWs (P.instances.map fun p =>
          P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
            P.ηC * p.1.target p.2 p.1.Cm P.α) - P.linSum linWs := by
      rw [linSum, ← weightedSum_map_sub]
      congr 1
      exact List.map_congr_left fun p _ => by ring
    rw [etaWeights, linClaims, weightedSum_cons, weightedSum_flatMap_three, hsplit]
    linear_combination hlinSum
  have hz := inspectBatch_accepts hws hlinB
  have he : P.e = 0 := hz _ (by simp [linClaims])
  have hσ : ∀ p ∈ P.instances, p.2.σA = p.1.target p.2 p.1.A P.α ∧
      p.2.σB = p.1.target p.2 p.1.B P.α ∧ p.2.σC = p.1.target p.2 p.1.Cm P.α := by
    intro p hp
    have hmem : ∀ c ∈ [p.1.target p.2 p.1.A P.α - p.2.σA, p.1.target p.2 p.1.B P.α - p.2.σB,
        p.1.target p.2 p.1.Cm P.α - p.2.σC], c ∈ P.linClaims :=
      fun c hc => List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p, hp, hc⟩)
    exact ⟨(sub_eq_zero.mp (hz _ (hmem _ (by simp)))).symm,
      (sub_eq_zero.mp (hz _ (hmem _ (by simp)))).symm,
      (sub_eq_zero.mp (hz _ (hmem _ (by simp)))).symm⟩
  -- rowcheck
  have hrowTerm : ∀ p ∈ P.instances,
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC) =
        (selectorPoly P.R p.1.R * p.1.rowPoly p.2).eval P.α := by
    intro p hp
    obtain ⟨hσA, hσB, hσC⟩ := hσ p hp
    obtain ⟨hA, hB, hC, -⟩ := hcirc _ (P.fst_mem_circuits hp)
    rw [hσA, hσB, hσC]
    simp only [BatchCircuit.target, linevalTarget_eq_mzPoly hA, linevalTarget_eq_mzPoly hB,
      linevalTarget_eq_mzPoly hC, BatchCircuit.rowPoly, eval_mul, eval_sub]
  have hrowEq : (P.rowResidual rowWs).eval P.α = 0 := by
    rw [rowEval, List.map_congr_left hrowTerm, value_correct_of_inspect_none hH0] at hrow
    simp only [rowResidual, batchedZerocheck, rowClaims, eval_sub, eval_mul,
      eval_weightedSumPoly, List.map_map, Function.comp_def] at hrow ⊢
    exact hrow
  have hid : batchedZerocheck P.R rowWs P.rowClaims = toPoly P.h0rep * P.R.vanishing :=
    sub_eq_zero.mp (inspectResidual_accepts hrowEq hrowI)
  have hdvd : ∀ c ∈ P.rowClaims, c.1.n ∣ P.R.n := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact hdvdR _ (P.fst_mem_circuits hp)
  have hrows := batchedZerocheck_extract hdvd hid hrowB
  refine ⟨he, fun p hp r hr => ?_⟩
  have h :=
    hrows (p.1.R, p.1.rowPoly p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩) _ (p.1.R.ω_pow_mem r)
  have hnode : p.1.R.ω ^ r = p.1.R.node r := rfl
  simp only [BatchCircuit.rowPoly, eval_sub, eval_mul, hnode,
    mzPoly_eval_node _ _ _ _ hr] at h
  exact sub_eq_zero.mp h

/-- snarkVM's `lineval_sumcheck` at `β` on the opened values, with
`ẑ(β) = x̂(β) + v_X(β) ŵ(β)` from the public input. -/
noncomputable def linOpenedEval (ws : List F) : F :=
  P.vMask +
      weightedSum ws (P.instances.map fun p => (selectorPoly P.Cd p.1.Cd).eval P.β *
        ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
          P.ηC * ((p.1.KC.n : F) * p.1.σmC)) *
          ((p.1.Xd.interpolate fun k => p.2.x.getD k 0).eval P.β +
            p.1.Xd.vanishing.eval P.β * p.2.vw))) -
    P.vH1 * P.Cd.vanishing.eval P.β - P.β * P.vG1 - P.linSum ws * P.Cd.sizeInv

/-- snarkVM's `matrix_sumcheck` at `γ` on the opened values. -/
noncomputable def matOpenedEval (δs : List F) : F :=
  weightedSum δs (P.circuits.flatMap fun c => c.matrixSummands P.K P.α P.β P.γ) -
    P.vH2 * P.K.vanishing.eval P.γ

/-- Every polynomial the lineval and matrix checks read, opened with no break. -/
structure Openings : Prop where
  mask : OpenedAt (maskPoly P.mode P.mask) P.β P.vMask
  h1 : OpenedAt P.h1 P.β P.vH1
  g1 : OpenedAt P.g1 P.β P.vG1
  h2 : OpenedAt P.h2 P.γ P.vH2
  w : ∀ p ∈ P.instances, OpenedAt p.2.w P.β p.2.vw
  gA : ∀ c ∈ P.circuits, OpenedAt c.gA P.γ c.vgA
  gB : ∀ c ∈ P.circuits, OpenedAt c.gB P.γ c.vgB
  gC : ∀ c ∈ P.circuits, OpenedAt c.gC P.γ c.vgC

theorem linOpenedEval_eq {P : V3Batch F} (ho : P.Openings) (ws : List F) :
    P.linOpenedEval ws = P.linEval ws := by
  have hterm : ∀ p ∈ P.instances, (selectorPoly P.Cd p.1.Cd).eval P.β *
      ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
        P.ηC * ((p.1.KC.n : F) * p.1.σmC)) *
        ((p.1.Xd.interpolate fun k => p.2.x.getD k 0).eval P.β +
          p.1.Xd.vanishing.eval P.β * p.2.vw)) =
      (selectorPoly P.Cd p.1.Cd).eval P.β *
        ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
          P.ηC * ((p.1.KC.n : F) * p.1.σmC)) * (p.1.zhat p.2).eval P.β) := by
    intro p hp
    rw [(ho.w p hp).eq_eval, BatchCircuit.zhat, eval_assignmentPoly]
  rw [linOpenedEval, linEval, List.map_congr_left hterm, ho.mask.eq_eval, ho.h1.eq_eval,
    ho.g1.eq_eval]

theorem matOpenedEval_eq {P : V3Batch F} (ho : P.Openings) (δs : List F) :
    P.matOpenedEval δs = batchedMatrixEval P.K δs P.matrixTerms P.h2 P.γ := by
  have hc : ∀ c ∈ P.circuits, c.matrixSummands P.K P.α P.β P.γ =
      (c.matrixTerms P.α P.β).map fun t => (selectorPoly P.K t.K).eval P.γ *
        (t.a.eval P.γ - t.b.eval P.γ * (P.γ * t.g.eval P.γ + t.σ)) := by
    intro c hc
    simp only [BatchCircuit.matrixSummands, BatchCircuit.matrixTerms, MatrixTerm.summandAt,
      List.map_cons, List.map_nil, (ho.gA c hc).eq_eval, (ho.gB c hc).eq_eval,
      (ho.gC c hc).eq_eval]
  rw [matOpenedEval, batchedMatrixEval, matrixTerms, List.map_flatMap, flatMap_congr_mem hc,
    ho.h2.eq_eval]

/-- `sound` on the values the verifier reads. The lineval and matrix checks run on
the opened `s(β)`, `ŵ_{i,j}(β)`, `h₁(β)`, `g₁(β)`, `g_{M,i}(γ)`, and `h₂(γ)`, with
`ẑ(β)` assembled from the public input; with every opening free of breaks they
are the polynomial checks `sound` consumes. -/
theorem sound_of_openings (rowWs linWs δs : List F) (ho : P.Openings)
    (hdvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n) (hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n)
    (hdvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n) (hvalid : ∀ t ∈ P.matrixTerms, t.Valid)
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrow : P.rowEval rowWs = 0) (hrowI : inspectResidual (P.rowResidual rowWs) P.α = none)
    (hrowB : inspectBatchOn P.R.nodeList rowWs (batchedClaims P.R P.rowClaims) = none)
    (hlin : P.linOpenedEval linWs = 0)
    (hlinI : inspectResidual (P.linResidual linWs) P.β = none)
    (hdegL : (X * P.g1 + C (P.linSum linWs * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hlinB : inspectBatch (etaWeights linWs P.ηA P.ηB P.ηC) P.linClaims = none)
    (hmat : P.matOpenedEval δs = 0)
    (hmatI : inspectResidual (batchedMatrixResidual P.K δs P.matrixTerms P.h2) P.γ = none)
    (hmatB : inspectBatchOn P.K.nodeList δs
      (batchedClaims P.K (P.matrixTerms.map MatrixTerm.claim)) = none) :
    P.e = 0 ∧ ∀ p ∈ P.instances, ∀ r, r < p.1.R.n →
      mzRow p.1.Cd p.1.A (p.1.zhat p.2) r * mzRow p.1.Cd p.1.B (p.1.zhat p.2) r =
        mzRow p.1.Cd p.1.Cm (p.1.zhat p.2) r :=
  P.sound rowWs linWs δs hdvdR hdvdC hdvdK hvalid hH0 hrow hrowI hrowB
    ((linOpenedEval_eq ho linWs).symm.trans hlin) hlinI hdegL hlinB
    ((matOpenedEval_eq ho δs).symm.trans hmat) hmatI hmatB

/-- The first-round weights `ν_i τ_{i,j}` from the first-combiners squeeze. -/
def rowWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (combinerScheme P.sizes) (chal .firstCombiners)

/-- The third-round weights `μ_i ρ_{i,j}` from the prepare-third squeeze. -/
def linWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (combinerScheme P.sizes) (chal .prepareThird)

/-- The `δ`s from the deltas squeeze. -/
def deltaWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (deltaScheme P.circuits.length) (chal .deltas)

/-- The batch's bad set at each squeeze element : the Schwartz–Zippel roots of the
three batched residuals at `α`, `β`, `γ`, and the liveness-ending elements of the
three combiner draws. -/
noncomputable def squeezeBad (S : Finset F) (chal : V2Challenge → List F) :
    V2Challenge → List F → Finset F :=
  Varuna.squeezeBad S (P.rowResidual (P.rowWeights chal)) (P.linResidual (P.linWeights chal))
    (batchedMatrixResidual P.K (P.deltaWeights chal) P.matrixTerms P.h2)
    (rowcheckDraw P.R P.sizes P.rowClaims) (linevalDraw P.sizes P.linClaims)
    (deltaDraw P.K P.circuits.length (P.matrixTerms.map MatrixTerm.claim))

/-- `sound_of_transcript` with the lineval and matrix LCs on the polynomials' values,
as `batch_check` gives them, rather than on opened values. -/
theorem sound_of_transcript_evals (S : Finset F) (t : V2Transcript F) (chal : V2Challenge → List F)
    (comms : List (List F)) (hinit : t.init = v3Init P.statement comms)
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) (hS : ∀ c, ∀ a ∈ chal c, a ∈ S)
    (hα : chal .alpha = [P.α]) (hβ : chal .beta = [P.β]) (hγ : chal .gamma = [P.γ])
    (hν : (chal .firstCombiners).length = combinerDraws P.sizes)
    (hη : (chal .prepareThird).length = combinerDraws P.sizes + 3)
    (hηA : P.ηA = (chal .prepareThird).getD (combinerDraws P.sizes) 0)
    (hηB : P.ηB = (chal .prepareThird).getD (combinerDraws P.sizes + 1) 0)
    (hηC : P.ηC = (chal .prepareThird).getD (combinerDraws P.sizes + 2) 0)
    (hδ : (chal .deltas).length = 3 * P.circuits.length - 1)
    (hnb : outputBreaks (prefixBad t (P.squeezeBad S chal)) t chal = false)
    (hdvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n) (hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n)
    (hdvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n) (hvalid : ∀ t ∈ P.matrixTerms, t.Valid)
    (hgen : ∀ c ∈ P.circuits, c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n))
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none)
    (hrow : P.rowEval (P.rowWeights chal) = 0) (hlin : P.linEval (P.linWeights chal) = 0)
    (hdegL : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hmat : batchedMatrixEval P.K (P.deltaWeights chal) P.matrixTerms P.h2 P.γ = 0) :
    (∀ inputs comms', t.init = v3Init inputs comms' → inputs = P.statement) ∧ P.e = 0 ∧
      ∀ p ∈ P.instances,
        (∀ k < p.1.Xd.n, (p.1.zhat p.2).eval
          (p.1.Cd.node (reindexBySubdomain p.1.Cd.n p.1.Xd.n k)) = p.2.x.getD k 0) ∧
        ∀ r, r < p.1.R.n →
          mzRow p.1.Cd p.1.A (p.1.zhat p.2) r * mzRow p.1.Cd p.1.B (p.1.zhat p.2) r =
            mzRow p.1.Cd p.1.Cm (p.1.zhat p.2) r := by
  have hrowI : inspectResidual (P.rowResidual (P.rowWeights chal)) P.α = none :=
    inspectResidual_eq_none_of_no_break hmsg rfl hα (hS .alpha _ (by simp [hα])) hnb
  have hlinI : inspectResidual (P.linResidual (P.linWeights chal)) P.β = none :=
    inspectResidual_eq_none_of_no_break hmsg rfl hβ (hS .beta _ (by simp [hβ])) hnb
  have hmatI : inspectResidual
      (batchedMatrixResidual P.K (P.deltaWeights chal) P.matrixTerms P.h2) P.γ = none :=
    inspectResidual_eq_none_of_no_break hmsg rfl hγ (hS .gamma _ (by simp [hγ])) hnb
  have hrowB : inspectBatchOn P.R.nodeList (P.rowWeights chal)
      (batchedClaims P.R P.rowClaims) = none := by
    by_contra h
    exact not_lucky_of_no_break hmsg (c := .firstCombiners) rfl (hS _) hnb
      (rowcheckDraw_lucky P.length_rowClaims_le hν h)
  have hlinB : inspectBatch (etaWeights (P.linWeights chal) P.ηA P.ηB P.ηC) P.linClaims =
      none := by
    by_contra h
    rw [hηA, hηB, hηC, linWeights, ← schemeWeights_linevalScheme] at h
    exact not_lucky_of_no_break hmsg (c := .prepareThird) rfl (hS _) hnb
      (linevalDraw_lucky P.length_linClaims_le hη h)
  have hmatB : inspectBatchOn P.K.nodeList (P.deltaWeights chal)
      (batchedClaims P.K (P.matrixTerms.map MatrixTerm.claim)) = none := by
    by_contra h
    exact not_lucky_of_no_break hmsg (c := .deltas) rfl (hS _) hnb
      (deltaDraw_lucky (by rw [List.length_map, length_matrixTerms]; omega) hδ h)
  obtain ⟨he, hrows⟩ := P.sound _ _ _ hdvdR hdvdC hdvdK hvalid hH0 hrow hrowI hrowB hlin hlinI
    hdegL hlinB hmat hmatI hmatB
  refine ⟨fun inputs comms' h => (v3Init_injective (h.symm.trans hinit)).1, he,
    fun p hp => ⟨fun k hk => ?_, hrows p hp⟩⟩
  exact assignment_at_input_position p.1.Xd p.1.Cd (hgen _ (P.fst_mem_circuits hp)) _ _ hk

/-- End-to-end soundness of a V3 batch on its transcript. The challenges and weights
are the transcript's squeezes, read with snarkVM's schemes; the init absorbs the
batch's statement. If the three LCs accept on the opened values, every opening has
no break, and no squeezed element lands in its bad set, then the transcript binds exactly this
statement, the mask sum is zero, and every instance has `ẑ` equal to its public
input on the input domain and satisfies `Az ∘ Bz = Cz` on its constraint domain. -/
theorem sound_of_transcript (S : Finset F) (t : V2Transcript F) (chal : V2Challenge → List F)
    (comms : List (List F)) (hinit : t.init = v3Init P.statement comms)
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) (hS : ∀ c, ∀ a ∈ chal c, a ∈ S)
    (hα : chal .alpha = [P.α]) (hβ : chal .beta = [P.β]) (hγ : chal .gamma = [P.γ])
    (hν : (chal .firstCombiners).length = combinerDraws P.sizes)
    (hη : (chal .prepareThird).length = combinerDraws P.sizes + 3)
    (hηA : P.ηA = (chal .prepareThird).getD (combinerDraws P.sizes) 0)
    (hηB : P.ηB = (chal .prepareThird).getD (combinerDraws P.sizes + 1) 0)
    (hηC : P.ηC = (chal .prepareThird).getD (combinerDraws P.sizes + 2) 0)
    (hδ : (chal .deltas).length = 3 * P.circuits.length - 1)
    (hnb : outputBreaks (prefixBad t (P.squeezeBad S chal)) t chal = false)
    (hdvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n) (hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n)
    (hdvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n) (hvalid : ∀ t ∈ P.matrixTerms, t.Valid)
    (hgen : ∀ c ∈ P.circuits, c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n))
    (hH0 : inspectOpening P.h0rep [] P.α P.vH0 = none) (ho : P.Openings)
    (hrow : P.rowEval (P.rowWeights chal) = 0) (hlin : P.linOpenedEval (P.linWeights chal) = 0)
    (hdegL : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n)
    (hmat : P.matOpenedEval (P.deltaWeights chal) = 0) :
    (∀ inputs comms', t.init = v3Init inputs comms' → inputs = P.statement) ∧ P.e = 0 ∧
      ∀ p ∈ P.instances,
        (∀ k < p.1.Xd.n, (p.1.zhat p.2).eval
          (p.1.Cd.node (reindexBySubdomain p.1.Cd.n p.1.Xd.n k)) = p.2.x.getD k 0) ∧
        ∀ r, r < p.1.R.n →
          mzRow p.1.Cd p.1.A (p.1.zhat p.2) r * mzRow p.1.Cd p.1.B (p.1.zhat p.2) r =
            mzRow p.1.Cd p.1.Cm (p.1.zhat p.2) r :=
  P.sound_of_transcript_evals S t chal comms hinit hmsg hS hα hβ hγ hν hη hηA hηB hηC hδ hnb hdvdR
    hdvdC hdvdK hvalid hgen hH0 hrow ((linOpenedEval_eq ho _).symm.trans hlin) hdegL
    ((matOpenedEval_eq ho _).symm.trans hmat)

end V3Batch

end Varuna