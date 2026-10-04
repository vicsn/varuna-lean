/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchFS

/-!
# Completeness of the honest V3 batch

Marlin's completeness : for every satisfying assignment the honest prover
makes the verifier accept at every challenge. Here the challenges are the
transcript's squeezes. `honestBatch` is that prover, in the algebraic
projection the verifier checks (`V3Batch.Accepts`): quotients by the
vanishing polynomials, prepare-third and matrix sums, and openings of the
polynomials the prover committed to.

The mask is an honest one, summing to zero over the variable domain
(`maskSum_nonZK` in non-ZK mode). Matrix messages are defined when `α` lies
outside each constraint domain and `β` outside each variable domain, which
is when the rational sumcheck's denominator is nonzero. The rowcheck and
lineval identities the honest quotients satisfy hold at every challenge.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- An honest opening: the coefficient list of `p`, opened at its true value. -/
theorem openedAt_eval [DecidableEq F] (p : F[X]) (z : F) : OpenedAt p z (p.eval z) := by
  refine ⟨coeffList p, [], (toPoly_coeffList p).symm, ?_⟩
  have h := inspectOpening_honest (coeffList p) [] z
  rwa [← eval_toPoly, toPoly_coeffList] at h

/-! ## Honest matrix remainder -/

/-- Degree-`< |K|` polynomial agreeing with `a(κ) / b(κ)` on `K`. -/
noncomputable def honestMatrixF (R Cd K : EvalDomain F) (M : SparseMatrix F) (α β : F) : F[X] :=
  let a := matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M)
  let b := matrixBPoly R Cd K α β M.rowIdx M.colIdx
  (K.interpolate fun k => a.eval (K.node k) * (b.eval (K.node k))⁻¹) %ₘ K.vanishing

/-- `b(κ) ≠ 0` for `κ ∈ K` when `α ∉ R` and `β ∉ C`. -/
theorem matrixB_eval_ne_zero {R Cd K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β : F}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements) {k : ℕ} (hk : k < K.n) :
    (matrixBPoly R Cd K α β M.rowIdx M.colIdx).eval (K.node k) ≠ 0 := by
  rw [eval_matrixBPoly _ _ _ _ _ _ _ hk]
  have hkM : k < M.nK := hK.symm ▸ hk
  obtain ⟨_hr, _hc⟩ := hM k hkM
  have hαr : α - R.node (M.rowIdx k) ≠ 0 := fun e => hα (sub_eq_zero.mp e ▸ R.ω_pow_mem _)
  have hβc : β - Cd.node (M.colIdx k) ≠ 0 := fun e => hβ (sub_eq_zero.mp e ▸ Cd.ω_pow_mem _)
  unfold EvalDomain.sizeAsField
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero R.n_ne_zero Cd.n_ne_zero) hαr) hβc

theorem honestMatrixF_eval_node {R Cd K : EvalDomain F} {M : SparseMatrix F} {α β : F}
    {k : ℕ} (hk : k < K.n) :
    (honestMatrixF R Cd K M α β).eval (K.node k) =
      (matrixAPoly K (R.vanishing.eval α * Cd.vanishing.eval β) (rowColVal R Cd M)).eval
          (K.node k) *
        ((matrixBPoly R Cd K α β M.rowIdx M.colIdx).eval (K.node k))⁻¹ := by
  simp only [honestMatrixF]
  rw [K.eval_modByVanishing _ (by simpa [EvalDomain.node] using K.ω_pow_mem k),
    K.eval_interpolate _ hk]

theorem natDegree_honestMatrixF_lt (R Cd K : EvalDomain F) (M : SparseMatrix F) (α β : F) :
    (honestMatrixF R Cd K M α β).natDegree < K.n := by
  simpa [honestMatrixF] using K.natDegree_modByVanishing_lt _

theorem honestMatrix_remainder (R Cd K : EvalDomain F) (M : SparseMatrix F) (α β : F) :
    X * divX (honestMatrixF R Cd K M α β) + C ((honestMatrixF R Cd K M α β).coeff 0) =
      honestMatrixF R Cd K M α β :=
  X_mul_divX_add _

/-- `|K| σ = M̂(α, β)` for the honest remainder `X g + σ`. -/
theorem honest_matrix_value {R Cd K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β : F}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements) :
    (K.n : F) * (honestMatrixF R Cd K M α β).coeff 0 =
      (matrixAtAlpha R Cd M α).eval β := by
  set f := honestMatrixF R Cd K M α β
  refine matrix_sumcheck_value_of_numer (g := divX f) (σ := f.coeff 0) hM hK hα hβ ?_ ?_
  · intro κ hκ
    obtain ⟨k, hk, hkκ⟩ := (K.mem_elements_iff_pow).1 hκ
    have hb := matrixB_eval_ne_zero hM hK hα hβ hk
    have hf := honestMatrixF_eval_node (R := R) (Cd := Cd) (M := M) (α := α) (β := β) hk
    have hrem := congrArg (eval (K.node k)) (honestMatrix_remainder R Cd K M α β)
    have hκn : κ = K.node k := by rw [EvalDomain.node]; exact hkκ.symm
    subst hκn
    simp only [eval_add, eval_mul, eval_X, eval_C] at hrem hf
    rw [hrem, hf, mul_comm ((matrixAPoly _ _ _).eval _) ((matrixBPoly _ _ _ _ _ _ _).eval _)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  · exact sum_remainder_of_natDegree_lt (by
      simpa [f, honestMatrix_remainder] using natDegree_honestMatrixF_lt R Cd K M α β)

/-- The honest numerator `a − b (X g + σ)` vanishes on `K`. -/
theorem honest_numer_eval_zero {R Cd K : EvalDomain F} {M : SparseMatrix F}
    (hM : M.Bounded R Cd) (hK : M.nK = K.n) {α β : F}
    (hα : α ∉ R.elements) (hβ : β ∉ Cd.elements) {x : F} (hx : x ∈ K.elements) :
    (⟨R, Cd, K, M, α, β, divX (honestMatrixF R Cd K M α β),
        (honestMatrixF R Cd K M α β).coeff 0⟩ : MatrixTerm F).numer.eval x = 0 := by
  obtain ⟨k, hk, hkx⟩ := (K.mem_elements_iff_pow).1 hx
  have hb := matrixB_eval_ne_zero hM hK hα hβ hk
  have hf := honestMatrixF_eval_node (R := R) (Cd := Cd) (M := M) (α := α) (β := β) hk
  have hxn : x = K.node k := by rw [EvalDomain.node]; exact hkx.symm
  subst hxn
  simp only [MatrixTerm.numer, MatrixTerm.a, MatrixTerm.b, eval_sub, eval_mul,
    honestMatrix_remainder R Cd K M α β]
  rw [hf, mul_comm ((matrixAPoly _ _ _).eval _) ((matrixBPoly _ _ _ _ _ _ _).eval _)⁻¹,
    ← mul_assoc, mul_inv_cancel₀ hb, one_mul, sub_self]

/-! ## Honest prover data -/

/-- One instance the honest prover holds: public input and witness polynomial. -/
structure InputInstance (F : Type*) [Field F] where
  x : List F
  w : F[X]

/-- One circuit the honest prover holds, before it builds quotients. -/
structure InputCircuit (F : Type*) [Field F] where
  R : EvalDomain F
  Cd : EvalDomain F
  Xd : EvalDomain F
  KA : EvalDomain F
  KB : EvalDomain F
  KC : EvalDomain F
  A : SparseMatrix F
  B : SparseMatrix F
  Cm : SparseMatrix F
  insts : List (InputInstance F)

namespace InputCircuit

variable (c : InputCircuit F)

/-- `ẑ = x̂ + v_X ŵ`. -/
noncomputable def zPoly (i : InputInstance F) : F[X] :=
  assignmentPoly c.Xd (c.Xd.interpolate fun k => i.x.getD k 0) i.w

/-- The instance satisfies `Az ∘ Bz = Cz` on the constraint domain. -/
def Satisfies : Prop :=
  ∀ i ∈ c.insts, ∀ r, r < c.R.n →
    mzRow c.Cd c.A (c.zPoly i) r * mzRow c.Cd c.B (c.zPoly i) r =
      mzRow c.Cd c.Cm (c.zPoly i) r

/-- What the honest matrix and row messages need of one circuit at `α, β`. -/
structure Ready (α β : F) : Prop where
  boundA : c.A.Bounded c.R c.Cd
  boundB : c.B.Bounded c.R c.Cd
  boundC : c.Cm.Bounded c.R c.Cd
  nKA : c.A.nK = c.KA.n
  nKB : c.B.nK = c.KB.n
  nKC : c.Cm.nK = c.KC.n
  alpha : α ∉ c.R.elements
  beta : β ∉ c.Cd.elements
  sat : c.Satisfies
  gen : c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n)

/-- Prepare-third sums and the opened witness, from the assignment. -/
noncomputable def toInstance (α β : F) (i : InputInstance F) : BatchInstance F where
  x := i.x
  w := i.w
  σA := linevalTarget c.R c.Cd c.A (c.zPoly i) α
  σB := linevalTarget c.R c.Cd c.B (c.zPoly i) α
  σC := linevalTarget c.R c.Cd c.Cm (c.zPoly i) α
  vw := i.w.eval β

/-- Honest matrix remainders and per-instance sums. -/
noncomputable def toCircuit (α β γ : F) : BatchCircuit F :=
  let fA := honestMatrixF c.R c.Cd c.KA c.A α β
  let fB := honestMatrixF c.R c.Cd c.KB c.B α β
  let fC := honestMatrixF c.R c.Cd c.KC c.Cm α β
  { R := c.R, Cd := c.Cd, Xd := c.Xd, KA := c.KA, KB := c.KB, KC := c.KC
    A := c.A, B := c.B, Cm := c.Cm
    gA := divX fA, gB := divX fB, gC := divX fC
    σmA := fA.coeff 0, σmB := fB.coeff 0, σmC := fC.coeff 0
    vgA := (divX fA).eval γ, vgB := (divX fB).eval γ, vgC := (divX fC).eval γ
    insts := c.insts.map (c.toInstance α β) }

theorem insts_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).insts = c.insts.map (c.toInstance α β) := rfl

theorem zhat_toInstance (i : InputInstance F) (α β γ : F) :
    (c.toCircuit α β γ).zhat (c.toInstance α β i) = c.zPoly i := by
  simp [BatchCircuit.zhat, toCircuit, toInstance, zPoly]

theorem gA_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).gA = divX (honestMatrixF c.R c.Cd c.KA c.A α β) := rfl

theorem gB_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).gB = divX (honestMatrixF c.R c.Cd c.KB c.B α β) := rfl

theorem gC_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).gC = divX (honestMatrixF c.R c.Cd c.KC c.Cm α β) := rfl

theorem σmA_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).σmA = (honestMatrixF c.R c.Cd c.KA c.A α β).coeff 0 := rfl

theorem σmB_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).σmB = (honestMatrixF c.R c.Cd c.KB c.B α β).coeff 0 := rfl

theorem σmC_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).σmC = (honestMatrixF c.R c.Cd c.KC c.Cm α β).coeff 0 := rfl

theorem vgA_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).vgA = (c.toCircuit α β γ).gA.eval γ := rfl

theorem vgB_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).vgB = (c.toCircuit α β γ).gB.eval γ := rfl

theorem vgC_toCircuit (α β γ : F) :
    (c.toCircuit α β γ).vgC = (c.toCircuit α β γ).gC.eval γ := rfl

theorem vw_toInstance (α β : F) (i : InputInstance F) :
    (c.toInstance α β i).vw = (c.toInstance α β i).w.eval β := rfl

/-- Honest prepare-third sums are the lineval targets, so `σ_A σ_B − σ_C` is the
row polynomial at `α`. -/
theorem toInstance_row (i : InputInstance F) (α β γ : F)
    (hA : c.A.Bounded c.R c.Cd) (hB : c.B.Bounded c.R c.Cd) (hC : c.Cm.Bounded c.R c.Cd) :
    (c.toInstance α β i).σA * (c.toInstance α β i).σB - (c.toInstance α β i).σC =
      ((c.toCircuit α β γ).rowPoly (c.toInstance α β i)).eval α := by
  rw [BatchCircuit.rowPoly, eval_sub, eval_mul, c.zhat_toInstance i α β γ]
  simp only [InputCircuit.toCircuit, toInstance, linevalTarget_eq_mzPoly hA,
    linevalTarget_eq_mzPoly hB, linevalTarget_eq_mzPoly hC]

theorem rowPoly_vanishes {i : InputInstance F} (h : c.Satisfies) (hi : i ∈ c.insts)
    (α β γ : F) {x : F} (hx : x ∈ c.R.elements) :
    ((c.toCircuit α β γ).rowPoly (c.toInstance α β i)).eval x = 0 := by
  obtain ⟨r, hr, rfl⟩ := (c.R.mem_elements_iff_pow).1 hx
  have hs := h i hi r hr
  rw [show c.R.ω ^ r = c.R.node r from rfl, BatchCircuit.rowPoly, eval_sub, eval_mul,
    c.zhat_toInstance i α β γ]
  simp only [InputCircuit.toCircuit]
  rw [mzPoly_eval_node _ _ _ _ hr, mzPoly_eval_node _ _ _ _ hr, mzPoly_eval_node _ _ _ _ hr]
  exact sub_eq_zero.mpr hs

end InputCircuit

/-- A batch the honest prover holds. -/
structure InputBatch (F : Type*) [Field F] where
  circuits : List (InputCircuit F)
  R : EvalDomain F
  Cd : EvalDomain F
  K : EvalDomain F
  mode : SNARKMode
  mask : F[X]

namespace InputBatch

variable (b : InputBatch F)

/-- Subdomain division, a zero mask sum, and each circuit ready at `α, β`. -/
structure Ready (α β : F) : Prop where
  dvdR : ∀ c ∈ b.circuits, c.R.n ∣ b.R.n
  dvdC : ∀ c ∈ b.circuits, c.Cd.n ∣ b.Cd.n
  dvdKA : ∀ c ∈ b.circuits, c.KA.n ∣ b.K.n
  dvdKB : ∀ c ∈ b.circuits, c.KB.n ∣ b.K.n
  dvdKC : ∀ c ∈ b.circuits, c.KC.n ∣ b.K.n
  mask : maskSum b.Cd b.mode b.mask = 0
  each : ∀ c ∈ b.circuits, c.Ready α β

/-- Instances per circuit, in snarkVM's combiner order. -/
def sizes : List ℕ :=
  b.circuits.map fun c => c.insts.length

def rowWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (combinerScheme b.sizes) (chal .firstCombiners)

def linWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (combinerScheme b.sizes) (chal .prepareThird)

def deltaWeights (chal : V2Challenge → List F) : List F :=
  schemeWeights (deltaScheme b.circuits.length) (chal .deltas)

/-- Public inputs as `v3Init` absorbs them. -/
def statement : List (List (List F)) :=
  b.circuits.map fun c => c.insts.map (·.x)

end InputBatch

/-- The transcript squeezes the honest batch is built from. Lengths are snarkVM's
combiner draws; the prover reads `α, β, γ, η` off those squeezes. -/
structure BatchSchedule (F : Type*) [Field F] (b : InputBatch F) (S : Finset F)
    (t : V2Transcript F) (chal : V2Challenge → List F) (comms : List (List F))
    (α β γ ηA ηB ηC : F) : Prop where
  init : t.init = v3Init b.statement comms
  msg : ∀ x, FSMessage.field x ∉ t.messages
  inS : ∀ c, ∀ a ∈ chal c, a ∈ S
  alpha : chal .alpha = [α]
  beta : chal .beta = [β]
  gamma : chal .gamma = [γ]
  nu : (chal .firstCombiners).length = combinerDraws b.sizes
  eta : (chal .prepareThird).length = combinerDraws b.sizes + 3
  etaA : ηA = (chal .prepareThird).getD (combinerDraws b.sizes) 0
  etaB : ηB = (chal .prepareThird).getD (combinerDraws b.sizes + 1) 0
  etaC : ηC = (chal .prepareThird).getD (combinerDraws b.sizes + 2) 0
  delta : (chal .deltas).length = 3 * b.circuits.length - 1

/-- A polynomial vanishing on `H` is `v_H` times its quotient. -/
theorem mul_vanishing_of_zero_on {H : EvalDomain F} {p : F[X]}
    (hp : ∀ x ∈ H.elements, p.eval x = 0) :
    p = H.vanishing * (p /ₘ H.vanishing) := by
  have hdiv := H.vanishing_dvd_of_eval_eq_zero hp
  have hmod : p %ₘ H.vanishing = 0 := (modByMonic_eq_zero_iff_dvd H.vanishing_monic).2 hdiv
  have hdecomp := modByMonic_add_div p H.vanishing
  rw [hmod, zero_add] at hdecomp
  exact hdecomp.symm

/-- On `H`, a selector times a polynomial that vanishes on `H_i` is zero. -/
theorem eval_selectorPoly_mul_of_vanishes [DecidableEq F] {H Hi : EvalDomain F}
    (hdvd : Hi.n ∣ H.n) {p : F[X]} (hvan : ∀ x ∈ Hi.elements, p.eval x = 0)
    {x : F} (hx : x ∈ H.elements) : (selectorPoly H Hi * p).eval x = 0 := by
  by_cases hxi : x ∈ Hi.elements
  · rw [eval_mul, hvan x hxi, mul_zero]
  · rw [eval_mul, selectorPoly_eval_of_not_mem hdvd hx hxi, zero_mul]

/-- A batched numerator whose claims vanish on their own domains vanishes on `H`. -/
theorem batchedZerocheck_eval_zero [DecidableEq F] {H : EvalDomain F} {ws : List F}
    {cs : List (EvalDomain F × F[X])} (hdvd : ∀ c ∈ cs, c.1.n ∣ H.n)
    (hvan : ∀ c ∈ cs, ∀ x ∈ c.1.elements, c.2.eval x = 0) {x : F} (hx : x ∈ H.elements) :
    (batchedZerocheck H ws cs).eval x = 0 := by
  rw [batchedZerocheck, eval_weightedSumPoly]
  refine weightedSum_all_zero _ _ ?_
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact eval_selectorPoly_mul_of_vanishes (hdvd c hc) (hvan c hc) hx

theorem eval_batchedZerocheck (H : EvalDomain F) (ws : List F)
    (cs : List (EvalDomain F × F[X])) (α : F) :
    (batchedZerocheck H ws cs).eval α =
      weightedSum ws (cs.map fun c => (selectorPoly H c.1 * c.2).eval α) := by
  simp [batchedZerocheck, eval_weightedSumPoly, List.map_map, Function.comp_def]

/-- Domain sum of a batch lineval: the mask sum plus the combined targets. -/
theorem sum_linevalPoly_batch [DecidableEq F] {P : V3Batch F} (ws : List F)
    (hA : ∀ c ∈ P.circuits, c.A.Bounded c.R c.Cd)
    (hB : ∀ c ∈ P.circuits, c.B.Bounded c.R c.Cd)
    (hC : ∀ c ∈ P.circuits, c.Cm.Bounded c.R c.Cd)
    (hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n) :
    ∑ i ∈ range P.Cd.n, (P.linevalPoly ws).eval (P.Cd.node i) =
      P.e + weightedSum ws (P.instances.map fun p =>
        P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
          P.ηC * p.1.target p.2 p.1.Cm P.α) := by
  have hsumInst : ∀ p ∈ P.instances, ∑ i ∈ range P.Cd.n,
      (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval (P.Cd.node i) =
      P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
        P.ηC * p.1.target p.2 p.1.Cm P.α := by
    intro p hp
    have hc := P.fst_mem_circuits hp
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
      _ = _ := BatchCircuit.sum_linPoly (hA _ hc) (hB _ hc) (hC _ hc) p.2 P.α P.ηA P.ηB P.ηC
  simp only [V3Batch.linevalPoly, eval_add, eval_weightedSumPoly, List.map_map, Function.comp_def,
    sum_add_distrib]
  rw [sum_weightedSum, List.map_congr_left hsumInst]
  rfl

/-- Circuits filled with honest matrix messages. The batch-level quotients are
filled by `honestBatch`. -/
noncomputable def honestShell (b : InputBatch F) (α β γ ηA ηB ηC : F) : V3Batch F :=
  let a0 := α
  let b0 := β
  let g0 := γ
  let eA := ηA
  let eB := ηB
  let eC := ηC
  { circuits := b.circuits.map fun c => c.toCircuit a0 b0 g0
    R := b.R, Cd := b.Cd, K := b.K, mode := b.mode, mask := b.mask
    h0rep := [], vH0 := 0, h1 := 0, g1 := 0, h2 := 0
    α := a0, β := b0, γ := g0, ηA := eA, ηB := eB, ηC := eC
    vMask := 0, vH1 := 0, vG1 := 0, vH2 := 0 }

/-- Honest rowcheck quotient on the largest constraint domain. -/
noncomputable def honestH0 (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) : F[X] :=
  batchedZerocheck b.R (b.rowWeights chal) (honestShell b α β γ ηA ηB ηC).rowClaims /ₘ
    b.R.vanishing

/-- Honest lineval sumcheck witness. -/
noncomputable def honestLin (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) : UnivariateWitness F :=
  honestUnivariate b.Cd ((honestShell b α β γ ηA ηB ηC).linevalPoly (b.linWeights chal))

/-- Honest matrix-sumcheck quotient on the largest nonzero domain. -/
noncomputable def honestH2 (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) : F[X] :=
  batchedZerocheck b.K (b.deltaWeights chal)
      ((honestShell b α β γ ηA ηB ηC).matrixTerms.map MatrixTerm.claim) /ₘ
    b.K.vanishing

/-- The honest V3 batch: snarkVM's quotients, sums, and opened values. -/
noncomputable def honestBatch (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) : V3Batch F :=
  let a0 := α
  let b0 := β
  let g0 := γ
  let eA := ηA
  let eB := ηB
  let eC := ηC
  let h0 := honestH0 b a0 b0 g0 eA eB eC chal
  let uw := honestLin b a0 b0 g0 eA eB eC chal
  let h2 := honestH2 b a0 b0 g0 eA eB eC chal
  { circuits := (honestShell b a0 b0 g0 eA eB eC).circuits
    R := b.R, Cd := b.Cd, K := b.K, mode := b.mode, mask := b.mask
    h0rep := coeffList h0, vH0 := h0.eval a0, h1 := uw.h, g1 := uw.g, h2 := h2
    α := a0, β := b0, γ := g0, ηA := eA, ηB := eB, ηC := eC
    vMask := (maskPoly b.mode b.mask).eval b0
    vH1 := uw.h.eval b0, vG1 := uw.g.eval b0, vH2 := h2.eval g0 }

theorem honestShell_sizes (b : InputBatch F) (α β γ ηA ηB ηC : F) :
    (honestShell b α β γ ηA ηB ηC).sizes = b.sizes := by
  simp [V3Batch.sizes, honestShell, InputBatch.sizes, InputCircuit.insts_toCircuit, List.map_map,
    List.length_map]

theorem honestBatch_sizes (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).sizes = b.sizes := by
  simpa [V3Batch.sizes, honestBatch] using honestShell_sizes b α β γ ηA ηB ηC

theorem honestBatch_circuits (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).circuits =
      (honestShell b α β γ ηA ηB ηC).circuits := rfl

theorem honestBatch_rowWeights (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).rowWeights chal = b.rowWeights chal := by
  simp [V3Batch.rowWeights, InputBatch.rowWeights, honestBatch_sizes]

theorem honestBatch_linWeights (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).linWeights chal = b.linWeights chal := by
  simp [V3Batch.linWeights, InputBatch.linWeights, honestBatch_sizes]

theorem honestBatch_deltaWeights (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).deltaWeights chal = b.deltaWeights chal := by
  simp [V3Batch.deltaWeights, InputBatch.deltaWeights, honestBatch, honestShell, List.length_map]

theorem honestBatch_lineval (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) (ws : List F) :
    (honestBatch b α β γ ηA ηB ηC chal).linevalPoly ws =
      (honestShell b α β γ ηA ηB ηC).linevalPoly ws := by
  simp [V3Batch.linevalPoly, V3Batch.instances, honestBatch, honestShell]

theorem honestBatch_rowClaims (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).rowClaims =
      (honestShell b α β γ ηA ηB ηC).rowClaims := by
  simp [V3Batch.rowClaims, V3Batch.instances, honestBatch]

theorem honestBatch_matrixTerms (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).matrixTerms =
      (honestShell b α β γ ηA ηB ηC).matrixTerms := by
  simp [V3Batch.matrixTerms, honestBatch, honestShell]

theorem honestBatch_statement (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) :
    (honestBatch b α β γ ηA ηB ηC chal).statement = b.statement := by
  simp [V3Batch.statement, InputBatch.statement, honestBatch, honestShell, InputCircuit.toCircuit,
    InputCircuit.toInstance, List.map_map, Function.comp]

theorem honestBatch_e (b : InputBatch F) (α β γ ηA ηB ηC : F)
    (chal : V2Challenge → List F) (hmask : maskSum b.Cd b.mode b.mask = 0) :
    (honestBatch b α β γ ηA ηB ηC chal).e = 0 := by
  simp [V3Batch.e, honestBatch, honestShell, hmask]

theorem mem_honestShell_circuits {b : InputBatch F} {α β γ ηA ηB ηC : F}
    {c : BatchCircuit F} (hc : c ∈ (honestShell b α β γ ηA ηB ηC).circuits) :
    ∃ d ∈ b.circuits, c = d.toCircuit α β γ := by
  simp only [honestShell, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact ⟨d, hd, rfl⟩

/-- Completeness. On a ready batch and a schedule of challenges outside each
circuit's domains, `Accepts` holds : the three linear combinations vanish, the
lineval degree bound holds, and every opening is the committed polynomial. -/
theorem honestBatch_accepts [DecidableEq F] (b : InputBatch F) (S : Finset F)
    (t : V2Transcript F) (chal : V2Challenge → List F) (comms : List (List F))
    (α β γ ηA ηB ηC : F) (hR : b.Ready α β)
    (hS : BatchSchedule F b S t chal comms α β γ ηA ηB ηC) :
    (honestBatch b α β γ ηA ηB ηC chal).Accepts S t chal comms := by
  set P := honestBatch b α β γ ηA ηB ηC chal
  have hshell : ∀ c ∈ (honestShell b α β γ ηA ηB ηC).circuits,
      ∃ d ∈ b.circuits, c = d.toCircuit α β γ := fun _ hc => mem_honestShell_circuits hc
  have hPR : P.R = b.R := by simp [P, honestBatch, honestShell]
  have hPCd : P.Cd = b.Cd := by simp [P, honestBatch, honestShell]
  have hPK : P.K = b.K := by simp [P, honestBatch, honestShell]
  have hPα : P.α = α := by simp [P, honestBatch, honestShell]
  have hPβ : P.β = β := by simp [P, honestBatch, honestShell]
  have hPγ : P.γ = γ := by simp [P, honestBatch, honestShell]
  have hcirc : ∀ c ∈ P.circuits, ∃ d ∈ b.circuits, c = d.toCircuit α β γ := by
    intro c hc
    exact hshell c (honestBatch_circuits b α β γ ηA ηB ηC chal ▸ hc)
  have hready : ∀ c ∈ P.circuits, ∃ d ∈ b.circuits, c = d.toCircuit α β γ ∧ d.Ready α β :=
    by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hcirc c hc
    exact ⟨d, hd, rfl, hR.each d hd⟩
  have hboundA : ∀ c ∈ P.circuits, c.A.Bounded c.R c.Cd := by
    intro c hc
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    simpa [InputCircuit.toCircuit] using hd.boundA
  have hboundB : ∀ c ∈ P.circuits, c.B.Bounded c.R c.Cd := by
    intro c hc
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    simpa [InputCircuit.toCircuit] using hd.boundB
  have hboundC : ∀ c ∈ P.circuits, c.Cm.Bounded c.R c.Cd := by
    intro c hc
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    simpa [InputCircuit.toCircuit] using hd.boundC
  have hdvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n := by
    intro c hc
    obtain ⟨d, hd, rfl, -⟩ := hready c hc
    rw [show (d.toCircuit α β γ).Cd = d.Cd from rfl, hPCd]
    exact hR.dvdC d hd
  have hdvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n := by
    intro c hc
    obtain ⟨d, hd, rfl, -⟩ := hready c hc
    rw [show (d.toCircuit α β γ).R = d.R from rfl, hPR]
    exact hR.dvdR d hd
  have hdvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n := by
    intro tm htm
    simp only [V3Batch.matrixTerms, List.mem_flatMap] at htm
    obtain ⟨c, hc, htm⟩ := htm
    obtain ⟨d, hd, rfl⟩ := hshell c hc
    simp only [InputCircuit.toCircuit, BatchCircuit.matrixTerms, List.mem_cons,
      List.not_mem_nil] at htm
    rw [hPK]
    rcases htm with rfl | rfl | rfl | hbad
    · exact hR.dvdKA d hd
    · exact hR.dvdKB d hd
    · exact hR.dvdKC d hd
    · exact hbad.elim
  have hgen : ∀ c ∈ P.circuits, c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n) := by
    intro c hc
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    simpa [InputCircuit.toCircuit] using hd.gen
  have hvalid : ∀ tm ∈ P.matrixTerms, tm.Valid := by
    intro tm htm
    simp only [V3Batch.matrixTerms, List.mem_flatMap] at htm
    obtain ⟨c, hc, htm⟩ := htm
    obtain ⟨d, hd, rfl⟩ := hshell c hc
    have hRd := hR.each d hd
    simp only [InputCircuit.toCircuit, BatchCircuit.matrixTerms, List.mem_cons,
      List.not_mem_nil] at htm
    have hdeg (K : EvalDomain F) (M : SparseMatrix F) :
        (X * divX (honestMatrixF d.R d.Cd K M α β) +
            C ((honestMatrixF d.R d.Cd K M α β).coeff 0)).natDegree < K.n := by
      rw [honestMatrix_remainder]
      exact natDegree_honestMatrixF_lt _ _ _ _ _ _
    rcases htm with rfl | rfl | rfl | hbad
    · rw [hPα, hPβ]
      exact ⟨by simpa [InputCircuit.toCircuit] using hRd.boundA, by
        simpa [InputCircuit.toCircuit] using hRd.nKA, hRd.alpha, hRd.beta, by
        simpa [InputCircuit.toCircuit, d.gA_toCircuit, d.σmA_toCircuit] using
          hdeg d.KA d.A⟩
    · rw [hPα, hPβ]
      exact ⟨by simpa [InputCircuit.toCircuit] using hRd.boundB, by
        simpa [InputCircuit.toCircuit] using hRd.nKB, hRd.alpha, hRd.beta, by
        simpa [InputCircuit.toCircuit, d.gB_toCircuit, d.σmB_toCircuit] using
          hdeg d.KB d.B⟩
    · rw [hPα, hPβ]
      exact ⟨by simpa [InputCircuit.toCircuit] using hRd.boundC, by
        simpa [InputCircuit.toCircuit] using hRd.nKC, hRd.alpha, hRd.beta, by
        simpa [InputCircuit.toCircuit, d.gC_toCircuit, d.σmC_toCircuit] using
          hdeg d.KC d.Cm⟩
    · exact hbad.elim
  have hopen : P.Openings := by
    refine ⟨openedAt_eval _ _, openedAt_eval _ _, openedAt_eval _ _, openedAt_eval _ _, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [V3Batch.instances, List.mem_flatMap] at hp
      obtain ⟨c, hc, hp⟩ := hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      obtain ⟨d, hd, rfl, -⟩ := hready c hc
      have hx' : x ∈ (d.insts.map (d.toInstance α β)) := d.insts_toCircuit α β γ ▸ hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      rw [hPβ]
      simpa [InputCircuit.toInstance, d.vw_toInstance] using openedAt_eval i.w β
    · intro c hc
      obtain ⟨d, -, rfl, -⟩ := hready c hc
      rw [hPγ]
      simpa [d.vgA_toCircuit] using openedAt_eval (d.toCircuit α β γ).gA γ
    · intro c hc
      obtain ⟨d, -, rfl, -⟩ := hready c hc
      rw [hPγ]
      simpa [d.vgB_toCircuit] using openedAt_eval (d.toCircuit α β γ).gB γ
    · intro c hc
      obtain ⟨d, -, rfl, -⟩ := hready c hc
      rw [hPγ]
      simpa [d.vgC_toCircuit] using openedAt_eval (d.toCircuit α β γ).gC γ
  have hh0 : inspectOpening P.h0rep [] P.α P.vH0 = none := by
    have h := inspectOpening_honest (coeffList (honestH0 b α β γ ηA ηB ηC chal)) [] α
    rw [← eval_toPoly, toPoly_coeffList] at h
    exact h
  have hrowTerm : ∀ p ∈ P.instances,
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC) =
        (selectorPoly P.R p.1.R * p.1.rowPoly p.2).eval P.α := by
    intro p hp
    simp only [V3Batch.instances, List.mem_flatMap] at hp
    obtain ⟨c, hc, hp⟩ := hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    have hx' : x ∈ (d.insts.map (d.toInstance α β)) := d.insts_toCircuit α β γ ▸ hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx'
    rw [eval_mul, d.toInstance_row i α β γ hd.boundA hd.boundB hd.boundC, hPR]
    simp [P, honestBatch, honestShell]
  have hrowVan : ∀ c ∈ P.rowClaims, ∀ x ∈ c.1.elements, c.2.eval x = 0 := by
    intro c hc x hx
    simp only [V3Batch.rowClaims, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    simp only [V3Batch.instances, List.mem_flatMap] at hp
    obtain ⟨bc, hbc, hp⟩ := hp
    obtain ⟨xi, hxi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨d, -, rfl, hd⟩ := hready bc hbc
    have hxi' : xi ∈ (d.insts.map (d.toInstance α β)) := d.insts_toCircuit α β γ ▸ hxi
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hxi'
    exact d.rowPoly_vanishes hd.sat hi α β γ hx
  have hrowDvd : ∀ c ∈ P.rowClaims, c.1.n ∣ P.R.n := by
    intro c hc
    simp only [V3Batch.rowClaims, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact hdvdR _ (P.fst_mem_circuits hp)
  have hrow0 : P.rowEval (b.rowWeights chal) = 0 := by
    have hzero : ∀ x ∈ P.R.elements,
        (batchedZerocheck P.R (b.rowWeights chal) P.rowClaims).eval x = 0 :=
      fun x hx => batchedZerocheck_eval_zero (ws := b.rowWeights chal) hrowDvd hrowVan hx
    have hid := mul_vanishing_of_zero_on hzero
    simp only [V3Batch.rowEval]
    rw [List.map_congr_left hrowTerm]
    have hclaims : P.instances.map (fun p => (selectorPoly P.R p.1.R * p.1.rowPoly p.2).eval P.α) =
        P.rowClaims.map (fun c => (selectorPoly P.R c.1 * c.2).eval P.α) := by
      simp [V3Batch.rowClaims, List.map_map, Function.comp_def]
    have hv : P.vH0 =
        (batchedZerocheck P.R (b.rowWeights chal) P.rowClaims /ₘ P.R.vanishing).eval P.α := by
      rw [show P.vH0 = (honestH0 b α β γ ηA ηB ηC chal).eval α from rfl, honestH0,
        honestBatch_rowClaims, hPR, hPα]
    rw [hclaims, ← eval_batchedZerocheck P.R (b.rowWeights chal) P.rowClaims P.α, hid, eval_mul, hv]
    ring
  have hσ : ∀ p ∈ P.instances, p.2.σA = p.1.target p.2 p.1.A P.α ∧
      p.2.σB = p.1.target p.2 p.1.B P.α ∧ p.2.σC = p.1.target p.2 p.1.Cm P.α := by
    intro p hp
    simp only [V3Batch.instances, List.mem_flatMap] at hp
    obtain ⟨c, hc, hp⟩ := hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    have hx' : x ∈ (d.insts.map (d.toInstance α β)) := d.insts_toCircuit α β γ ▸ hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx'
    rw [hPα, InputCircuit.toInstance, InputCircuit.toCircuit]
    simp [BatchCircuit.target, BatchCircuit.zhat, InputCircuit.zPoly]
  have hlinSum : P.linSum (b.linWeights chal) =
      weightedSum (b.linWeights chal) (P.instances.map fun p =>
        P.ηA * p.1.target p.2 p.1.A P.α + P.ηB * p.1.target p.2 p.1.B P.α +
          P.ηC * p.1.target p.2 p.1.Cm P.α) := by
    simp only [V3Batch.linSum]
    congr 1
    exact List.map_congr_left fun p hp => by
      obtain ⟨ha, hb, hc⟩ := hσ p hp
      rw [ha, hb, hc]
  have hsumLin : ∑ i ∈ range P.Cd.n, (P.linevalPoly (b.linWeights chal)).eval (P.Cd.node i) =
      P.linSum (b.linWeights chal) := by
    rw [sum_linevalPoly_batch _ hboundA hboundB hboundC hdvdC, honestBatch_e _ _ _ _ _ _ _ _ hR.mask,
      zero_add, hlinSum]
  have hσw : (honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal))).σ =
      P.linSum (b.linWeights chal) * P.Cd.sizeInv := by
    have hsum := honestUnivariate_sum P.Cd (P.linevalPoly (b.linWeights chal))
    rw [hsumLin] at hsum
    have hn : (P.Cd.n : F) * P.Cd.sizeInv = 1 := P.Cd.mul_sizeInv
    calc (honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal))).σ
        = (P.Cd.n : F) * P.Cd.sizeInv *
            (honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal))).σ := by rw [hn, one_mul]
      _ = P.Cd.sizeInv * ((P.Cd.n : F) *
            (honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal))).σ) := by ring
      _ = P.Cd.sizeInv * P.linSum (b.linWeights chal) := by rw [hsum]
      _ = P.linSum (b.linWeights chal) * P.Cd.sizeInv := mul_comm _ _
  have huw : P.linWitness (b.linWeights chal) =
      honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal)) := by
    simp only [V3Batch.linWitness]
    have hh : P.h1 = (honestLin b α β γ ηA ηB ηC chal).h := rfl
    have hg : P.g1 = (honestLin b α β γ ηA ηB ηC chal).g := rfl
    have hpoly : (honestShell b α β γ ηA ηB ηC).linevalPoly (b.linWeights chal) =
        P.linevalPoly (b.linWeights chal) := by
      simpa [P] using (honestBatch_lineval b α β γ ηA ηB ηC chal (b.linWeights chal)).symm
    rw [hh, hg, honestLin, hpoly, ← hσw]
    rfl
  have hmatVal : ∀ c ∈ P.circuits,
      (c.KA.n : F) * c.σmA = (matrixAtAlpha c.R c.Cd c.A P.α).eval P.β ∧
      (c.KB.n : F) * c.σmB = (matrixAtAlpha c.R c.Cd c.B P.α).eval P.β ∧
      (c.KC.n : F) * c.σmC = (matrixAtAlpha c.R c.Cd c.Cm P.α).eval P.β := by
    intro c hc
    obtain ⟨d, -, rfl, hd⟩ := hready c hc
    simp only [show P.α = α from rfl, show P.β = β from rfl, InputCircuit.toCircuit]
    exact ⟨honest_matrix_value hd.boundA hd.nKA hd.alpha hd.beta,
      honest_matrix_value hd.boundB hd.nKB hd.alpha hd.beta,
      honest_matrix_value hd.boundC hd.nKC hd.alpha hd.beta⟩
  have hlinTerm : ∀ p ∈ P.instances, (selectorPoly P.Cd p.1.Cd).eval P.β *
      ((P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
        P.ηC * ((p.1.KC.n : F) * p.1.σmC)) * (p.1.zhat p.2).eval P.β) =
      (selectorPoly P.Cd p.1.Cd * p.1.linPoly p.2 P.α P.ηA P.ηB P.ηC).eval P.β := by
    intro p hp
    obtain ⟨hA, hB, hC⟩ := hmatVal _ (P.fst_mem_circuits hp)
    simp only [BatchCircuit.linPoly, eval_mul, eval_add, eval_C, hA, hB, hC]
  have hlinEq : P.linEval (b.linWeights chal) =
      univariateEval P.Cd (P.linevalPoly (b.linWeights chal))
        (P.linWitness (b.linWeights chal)) P.β := by
    rw [V3Batch.linEval, List.map_congr_left hlinTerm]
    simp only [univariateEval, V3Batch.linevalPoly, V3Batch.linWitness, eval_add, eval_mul,
      eval_weightedSumPoly, List.map_map, Function.comp_def]
  have hlin0 : P.linEval (b.linWeights chal) = 0 := by
    rw [hlinEq, huw, show P.β = β from rfl]
    exact univariateEval_honest _ _ _
  have hdeg : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n := by
    rw [honestBatch_linWeights, ← hσw]
    have hg : P.g1 = (honestUnivariate P.Cd (P.linevalPoly (b.linWeights chal))).g := by
      have hg1 : P.g1 = (honestLin b α β γ ηA ηB ηC chal).g := rfl
      have hpoly : (honestShell b α β γ ηA ηB ηC).linevalPoly (b.linWeights chal) =
          P.linevalPoly (b.linWeights chal) := by
        simpa [P] using (honestBatch_lineval b α β γ ηA ηB ηC chal (b.linWeights chal)).symm
      rw [hg1, honestLin, hpoly, hPCd]
    rw [hg]
    exact natDegree_honest_remainder_lt _ _
  have hnumer : ∀ tm ∈ P.matrixTerms, ∀ x ∈ tm.K.elements, tm.numer.eval x = 0 := by
    intro tm htm x hx
    simp only [V3Batch.matrixTerms, List.mem_flatMap] at htm
    obtain ⟨c, hc, htm⟩ := htm
    obtain ⟨d, hdmem, rfl⟩ := hshell c hc
    have hd := hR.each d hdmem
    simp only [InputCircuit.toCircuit, BatchCircuit.matrixTerms, List.mem_cons,
      List.not_mem_nil] at htm
    rcases htm with rfl | rfl | rfl | hbad
    · rw [hPα, hPβ]
      simpa [d.gA_toCircuit, d.σmA_toCircuit] using
        honest_numer_eval_zero hd.boundA hd.nKA hd.alpha hd.beta hx
    · rw [hPα, hPβ]
      simpa [d.gB_toCircuit, d.σmB_toCircuit] using
        honest_numer_eval_zero hd.boundB hd.nKB hd.alpha hd.beta hx
    · rw [hPα, hPβ]
      simpa [d.gC_toCircuit, d.σmC_toCircuit] using
        honest_numer_eval_zero hd.boundC hd.nKC hd.alpha hd.beta hx
    · exact hbad.elim
  have hmatVan : ∀ c ∈ P.matrixTerms.map MatrixTerm.claim, ∀ x ∈ c.1.elements, c.2.eval x = 0 :=
    by
    intro c hc x hx
    obtain ⟨tm, htm, rfl⟩ := List.mem_map.mp hc
    exact hnumer tm htm x hx
  have hmatDvd : ∀ c ∈ P.matrixTerms.map MatrixTerm.claim, c.1.n ∣ P.K.n := by
    intro c hc
    obtain ⟨tm, htm, rfl⟩ := List.mem_map.mp hc
    exact hdvdK tm htm
  have hmat0 : P.matOpenedEval (b.deltaWeights chal) = 0 := by
    have hzero : ∀ x ∈ P.K.elements,
        (batchedZerocheck P.K (b.deltaWeights chal)
          (P.matrixTerms.map MatrixTerm.claim)).eval x = 0 :=
      fun x hx => batchedZerocheck_eval_zero (ws := b.deltaWeights chal) hmatDvd hmatVan hx
    have hid := mul_vanishing_of_zero_on hzero
    have hh2 : P.h2 = batchedZerocheck P.K (b.deltaWeights chal)
        (P.matrixTerms.map MatrixTerm.claim) /ₘ P.K.vanishing := by
      rw [show P.h2 = honestH2 b α β γ ηA ηB ηC chal from rfl, honestH2,
        show (honestShell b α β γ ηA ηB ηC).matrixTerms = P.matrixTerms from
          (honestBatch_matrixTerms b α β γ ηA ηB ηC chal).symm,
        hPK]
    rw [V3Batch.matOpenedEval_eq hopen, batchedMatrixEval_eq, hPγ, hh2, batchedMatrixResidual]
    nth_rw 1 [hid]
    rw [mul_comm (P.K.vanishing)]
    simp
  refine
    { init := ?_, msg := hS.msg, inS := hS.inS, alpha := ?_, beta := ?_, gamma := ?_, nu := ?_,
      eta := ?_, etaA := ?_, etaB := ?_, etaC := ?_, delta := ?_, dvdR := hdvdR, dvdC := hdvdC,
      dvdK := hdvdK, valid := hvalid, gen := hgen, h0 := hh0, openings := hopen,
      row := ?_, lin := ?_, degL := hdeg, mat := ?_ }
  · rw [honestBatch_statement]
    exact hS.init
  · simpa [show P.α = α from rfl] using hS.alpha
  · simpa [show P.β = β from rfl] using hS.beta
  · simpa [show P.γ = γ from rfl] using hS.gamma
  · rw [honestBatch_sizes]
    exact hS.nu
  · rw [honestBatch_sizes]
    exact hS.eta
  · rw [honestBatch_sizes, show P.ηA = ηA from rfl]
    exact hS.etaA
  · rw [honestBatch_sizes, show P.ηB = ηB from rfl]
    exact hS.etaB
  · rw [honestBatch_sizes, show P.ηC = ηC from rfl]
    exact hS.etaC
  · have hlen : P.circuits.length = b.circuits.length := by
      simp [P, honestBatch, honestShell, List.length_map]
    rw [hlen]
    exact hS.delta
  · rw [honestBatch_rowWeights]
    exact hrow0
  · rw [V3Batch.linOpenedEval_eq hopen, honestBatch_linWeights]
    exact hlin0
  · rw [honestBatch_deltaWeights]
    exact hmat0

end Varuna