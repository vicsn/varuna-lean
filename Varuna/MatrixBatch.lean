/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.MatrixSumcheck
import Varuna.Selectors

/-!
# The batched matrix sumcheck

snarkVM checks every matrix of every circuit in one `matrix_sumcheck` LC
(`ahp.rs:362-400`). Term `(i, M)` is the rational-sumcheck numerator
`a − b (X g + σ)` of matrix `M` of circuit `i` on its nonzero domain
`K_{M,i}`, lifted to the largest nonzero domain `K` by the selector
`s_{K,K_{M,i}}` and weighted by `δ_{M,i}`; one quotient `h₂` covers the sum.
That is a batched zerocheck on `K`, so `batchedZerocheck_extract` gives each
numerator on its own domain, or a lucky `δ` combination on `K` as a whole,
and the per-matrix argument (`matrix_sumcheck_value_of_numer`) gives each
` | K_{M,i} | σ_{M,i} = M̂_i(α, β)`.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- One term of the batched matrix sumcheck: matrix `M` of a circuit with
constraint domain `R` and variable domain `Cd`, its nonzero domain `K`, the
challenges `α, β`, and the prover's `g` and `σ`. -/
structure MatrixTerm (F : Type*) [Field F] where
  /-- Constraint domain of the circuit. -/
  R : EvalDomain F
  /-- Variable domain of the circuit. -/
  Cd : EvalDomain F
  /-- Nonzero domain of the matrix. -/
  K : EvalDomain F
  /-- The matrix. -/
  M : SparseMatrix F
  /-- `α`. -/
  α : F
  /-- `β`. -/
  β : F
  /-- The prover's `g_M`. -/
  g : F[X]
  /-- The prover's sum `σ_M`, with `|K| σ_M` the claimed `M̂(α, β)`. -/
  σ : F

namespace MatrixTerm

variable (t : MatrixTerm F)

/-- `a(X) = v_R(α) v_C(β) row_col_val(X)`. -/
noncomputable def a : F[X] :=
  matrixAPoly t.K (t.R.vanishing.eval t.α * t.Cd.vanishing.eval t.β) (rowColVal t.R t.Cd t.M)

/-- `b(X) = |R| |C| (αβ − α col(X) − β row(X) + row_col(X))`. -/
noncomputable def b : F[X] :=
  matrixBPoly t.R t.Cd t.K t.α t.β t.M.rowIdx t.M.colIdx

/-- The numerator `a − b (X g + σ)`. -/
noncomputable def numer : F[X] :=
  t.a - t.b * (X * t.g + C t.σ)

/-- The term as a claim of the batched zerocheck: its domain and its numerator. -/
noncomputable def claim : EvalDomain F × F[X] :=
  (t.K, t.numer)

/-- What the verifier enforces per term: the indexed matrix is bounded and has
` | K | ` nonzeros, `α ∉ R`, `β ∉ C`, and `g` has degree at most ` | K | − 2`. -/
structure Valid : Prop where
  bounded : t.M.Bounded t.R t.Cd
  nK : t.M.nK = t.K.n
  alpha : t.α ∉ t.R.elements
  beta : t.β ∉ t.Cd.elements
  deg : (X * t.g + C t.σ).natDegree < t.K.n

/-- A numerator that vanishes on `K` proves the term's claim `|K| σ = M̂(α, β)`. -/
theorem value_of_numer {t : MatrixTerm F} (ht : t.Valid)
    (hvan : ∀ κ ∈ t.K.elements, t.numer.eval κ = 0) :
    (t.K.n : F) * t.σ = (matrixAtAlpha t.R t.Cd t.M t.α).eval t.β := by
  refine matrix_sumcheck_value_of_numer ht.bounded ht.nK ht.alpha ht.beta (fun κ hκ => ?_)
    (sum_remainder_of_natDegree_lt ht.deg)
  have h := hvan κ hκ
  simp only [numer, a, b, eval_sub, eval_mul, eval_add, eval_X, eval_C] at h
  exact sub_eq_zero.mp h

end MatrixTerm

/-- snarkVM's batched matrix residual `Σ_t δ_t s_{K,K_t} (a_t − b_t (X g_t + σ_t)) − h₂ v_K`. -/
noncomputable def batchedMatrixResidual (K : EvalDomain F) (δs : List F)
    (ts : List (MatrixTerm F)) (h2 : F[X]) : F[X] :=
  batchedZerocheck K δs (ts.map MatrixTerm.claim) - h2 * K.vanishing

/-- The `matrix_sumcheck` LC at `γ` as the verifier assembles it: per term
`δ · s(γ) · (a(γ) − b(γ) (γ g(γ) + σ))` (`construct_g_m_term`), minus
`v_K(γ) h₂(γ)`. -/
noncomputable def batchedMatrixEval (K : EvalDomain F) (δs : List F)
    (ts : List (MatrixTerm F)) (h2 : F[X]) (γ : F) : F :=
  weightedSum δs (ts.map fun t => (selectorPoly K t.K).eval γ *
      (t.a.eval γ - t.b.eval γ * (γ * t.g.eval γ + t.σ))) -
    h2.eval γ * K.vanishing.eval γ

/-- The LC evaluation is the residual at the challenge. -/
theorem batchedMatrixEval_eq (K : EvalDomain F) (δs : List F) (ts : List (MatrixTerm F))
    (h2 : F[X]) (γ : F) :
    batchedMatrixEval K δs ts h2 γ = (batchedMatrixResidual K δs ts h2).eval γ := by
  simp [batchedMatrixEval, batchedMatrixResidual, batchedZerocheck, eval_weightedSumPoly,
    Function.comp_def, MatrixTerm.claim, MatrixTerm.numer]

/-- Batched matrix sumcheck soundness. If the `matrix_sumcheck` LC accepts at
`γ`, the residual inspector reports no root, and the `δ` combination is not
lucky on `K` as a whole, every term's claim ` | K_t | σ_t = M̂_t(α, β)` holds. -/
theorem batchedMatrix_extract [DecidableEq F] {K : EvalDomain F} {δs : List F}
    {ts : List (MatrixTerm F)} {h2 : F[X]} {γ : F}
    (hdvd : ∀ t ∈ ts, t.K.n ∣ K.n) (hvalid : ∀ t ∈ ts, t.Valid)
    (hγ : batchedMatrixEval K δs ts h2 γ = 0)
    (hγI : inspectResidual (batchedMatrixResidual K δs ts h2) γ = none)
    (hδ : inspectBatchOn K.nodeList δs (batchedClaims K (ts.map MatrixTerm.claim)) = none) :
    ∀ t ∈ ts, (t.K.n : F) * t.σ = (matrixAtAlpha t.R t.Cd t.M t.α).eval t.β := by
  have hres := inspectResidual_accepts (batchedMatrixEval_eq K δs ts h2 γ ▸ hγ) hγI
  have hz := batchedZerocheck_extract (cs := ts.map MatrixTerm.claim)
    (fun c hc => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
      exact hdvd t ht)
    (sub_eq_zero.mp hres) hδ
  intro t ht
  exact MatrixTerm.value_of_numer (hvalid t ht) (hz t.claim (List.mem_map_of_mem ht))

end Varuna