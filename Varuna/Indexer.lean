/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Varuna.Domain

/-!
# Holographic indexer

snarkVM’s indexer arithmetizes each sparse R1CS matrix `M` into oracles
on a nonzero domain `K` of size `2^k` :

* `row(k)` — constraint-domain node of the `k`-th nonzero
* `col(k)` — variable-domain node of the `k`-th nonzero
* `val(k)` — the entry value (padding is `0`)

These satisfy the holographic identity (snarkVM `matrix_evals`)

\[
  M(a,b)=\sum_{k\in K}\mathrm{val}(k)\,L^{R}_{\mathrm{row}(k)}(a)\,
    L^{C}_{\mathrm{col}(k)}(b)
\]

Evaluating the interpolants of `row` / `col` / `val` at a `K`-node
recovers the stored table — that is the holography.

Column reindexing of the public-input subdomain (snarkVM
`reindex_by_subdomain`) is deferred to the batching layer; here `colIdx`
is already a variable-domain index.
-/

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-- A sparse matrix entry: constraint-row, variable-column, value. -/
structure MatrixEntry (F : Type*) [Field F] where
  /-- Row index in the constraint domain. -/
  rowIdx : Nat
  /-- Column index in the variable domain. -/
  colIdx : Nat
  /-- Entry value; padding uses `0`. -/
  value : F

/-- Circuit dimensions matching snarkVM `CircuitInfo`. -/
structure CircuitInfo where
  /-- Public inputs after padding, including the constant-`1` slot. -/
  numPublicInputs : Nat
  /-- Public and private variables (snarkVM `num_public_and_private_variables`). -/
  numVariables : Nat
  /-- Number of constraints (unpadded). -/
  numConstraints : Nat
  /-- Nonzeros in `A`. -/
  numNonZeroA : Nat
  /-- Nonzeros in `B`. -/
  numNonZeroB : Nat
  /-- Nonzeros in `C`. -/
  numNonZeroC : Nat

/-- snarkVM `CircuitInfo::num_public_and_private_variables`. -/
abbrev CircuitInfo.numPublicAndPrivateVariables (info : CircuitInfo) : Nat :=
  info.numVariables

/-- Largest nonzero count among `A, B, C`. -/
def CircuitInfo.maxNonZero (info : CircuitInfo) : Nat :=
  max (max info.numNonZeroA info.numNonZeroB) info.numNonZeroC

/-- Dense coefficient at `(r, c)` by summing sparse entries that land there. -/
def matrixAt (nK : Nat) (rowIdx colIdx : Nat → Nat) (value : Nat → F)
    (r c : Nat) : F :=
  ∑ k ∈ range nK, if rowIdx k = r ∧ colIdx k = c then value k else 0

/-- Holographic encoding of `M` at field points `(a, b)`. -/
noncomputable def holographicEval (H_R H_C : EvalDomain F) (nK : Nat)
    (rowIdx colIdx : Nat → Nat) (value : Nat → F) (a b : F) : F :=
  ∑ k ∈ range nK,
    value k * (H_R.lagrange (rowIdx k)).eval a *
      (H_C.lagrange (colIdx k)).eval b

/-- On domain nodes, the holographic encoding recovers the sparse matrix. -/
theorem holographicEval_at_nodes (H_R H_C : EvalDomain F) (nK : Nat)
    (rowIdx colIdx : Nat → Nat) (value : Nat → F)
    (hrow : ∀ k, k < nK → rowIdx k < H_R.n)
    (hcol : ∀ k, k < nK → colIdx k < H_C.n)
    {r c : Nat} (hr : r < H_R.n) (hc : c < H_C.n) :
    holographicEval H_R H_C nK rowIdx colIdx value (H_R.node r) (H_C.node c) =
      matrixAt nK rowIdx colIdx value r c := by
  unfold holographicEval matrixAt
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < nK := mem_range.mp hk
  rw [EvalDomain.eval_lagrange_node_ite H_R (hrow k hk') hr,
    EvalDomain.eval_lagrange_node_ite H_C (hcol k hk') hc]
  by_cases h1 : rowIdx k = r
  · by_cases h2 : colIdx k = c
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- Row oracle: LDE of the constraint-domain nodes of each sparse entry. -/
noncomputable def rowOracle (H_R H_K : EvalDomain F) (rowIdx : Nat → Nat) : F[X] :=
  H_K.interpolate (fun k => H_R.node (rowIdx k))

/-- Column oracle: LDE of the variable-domain nodes of each sparse entry. -/
noncomputable def colOracle (H_C H_K : EvalDomain F) (colIdx : Nat → Nat) : F[X] :=
  H_K.interpolate (fun k => H_C.node (colIdx k))

/-- Value oracle: LDE of the sparse entry values (padding is `0`). -/
noncomputable def valOracle (H_K : EvalDomain F) (value : Nat → F) : F[X] :=
  H_K.interpolate value

/-- `row_col` oracle: LDE of the entry-wise product of the row and column nodes
(snarkVM `arithmetize_matrix`, padding `1 · 1`). -/
noncomputable def rowColOracle (H_R H_C H_K : EvalDomain F) (rowIdx colIdx : Nat → Nat) : F[X] :=
  H_K.interpolate (fun k => H_R.node (rowIdx k) * H_C.node (colIdx k))

/-- Evaluating the row oracle at a `K`-node recovers the stored row node. -/
theorem rowOracle_eval (H_R H_K : EvalDomain F) (rowIdx : Nat → Nat)
    {k : Nat} (hk : k < H_K.n) :
    (rowOracle H_R H_K rowIdx).eval (H_K.node k) = H_R.node (rowIdx k) :=
  H_K.eval_interpolate (fun k => H_R.node (rowIdx k)) hk

/-- Evaluating the column oracle at a `K`-node recovers the stored column node. -/
theorem colOracle_eval (H_C H_K : EvalDomain F) (colIdx : Nat → Nat)
    {k : Nat} (hk : k < H_K.n) :
    (colOracle H_C H_K colIdx).eval (H_K.node k) = H_C.node (colIdx k) :=
  H_K.eval_interpolate (fun k => H_C.node (colIdx k)) hk

/-- Evaluating the value oracle at a `K`-node recovers the stored value. -/
theorem valOracle_eval (H_K : EvalDomain F) (value : Nat → F)
    {k : Nat} (hk : k < H_K.n) :
    (valOracle H_K value).eval (H_K.node k) = value k :=
  H_K.eval_interpolate value hk

/-- Evaluating the `row_col` oracle at a `K`-node recovers the product of the stored
row and column nodes. -/
theorem rowColOracle_eval (H_R H_C H_K : EvalDomain F) (rowIdx colIdx : Nat → Nat)
    {k : Nat} (hk : k < H_K.n) :
    (rowColOracle H_R H_C H_K rowIdx colIdx).eval (H_K.node k) =
      H_R.node (rowIdx k) * H_C.node (colIdx k) :=
  H_K.eval_interpolate (fun k => H_R.node (rowIdx k) * H_C.node (colIdx k)) hk

/-- Padding used by snarkVM `matrix_evals`: field elements `1` (row/col node 0)
and value `0`. Index `0` is `ω^0 = 1`. -/
def padEntry : MatrixEntry F :=
  ⟨0, 0, 0⟩

end Varuna