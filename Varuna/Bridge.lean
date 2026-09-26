/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Composition

/-!
# From the V2 chain to the R1CS relation

The R1CS relation (`R1CS.lean`) is stated on `Int` residues in `[0, p)`;
the AHP lives in a Mathlib field. The residue operations cast exactly to
`ZMod p`, so a sparse constraint list is satisfied iff its field Hadamard
identity holds (`satisfies_iff_zmod`).

`satisfies_of_rows` closes the loop. If the index encodes the constraint
list (the `indexEqualsCircuit` floor, stated here as the hypotheses
`hidx*`) and `ẑ` interpolates the assignment on `C`, the row identity that
`v2_chain_nonZK` concludes is `satisfies`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {p : ℕ} [Fact p.Prime]

/-- Residue addition is field addition. -/
@[simp] theorem cast_add (x y : Int) : ((add x y p : Int) : ZMod p) = (x : ZMod p) + y := by
  simp [add, ZMod.intCast_mod]

/-- Residue multiplication is field multiplication. -/
@[simp] theorem cast_mul (x y : Int) : ((mul x y p : Int) : ZMod p) = (x : ZMod p) * y := by
  simp [mul, ZMod.intCast_mod]

/-- Field value of a sparse dot product. -/
def fieldDot (p : ℕ) (vec : SparseVector) (asg : Assignment) : ZMod p :=
  (vec.map fun t => (t.1 : ZMod p) * (t.2.value asg : ZMod p)).sum

/-- The residue dot product casts to the field dot product. -/
theorem cast_dotProduct (asg : Assignment) :
    ∀ vec : SparseVector, ((dotProduct vec asg p : Int) : ZMod p) = fieldDot p vec asg
  | [] => by simp [fieldDot]
  | (c, pv) :: rest => by
    rw [dotProduct_cons, cast_add, cast_mul, ZMod.intCast_mod, cast_dotProduct asg rest]
    simp [fieldDot]

/-- Two residues are equal iff they are equal in the field. -/
theorem residue_eq_iff {a b : Int} (ha : Fep p a) (hb : Fep p b) :
    a = b ↔ (a : ZMod p) = (b : ZMod p) := by
  rw [ZMod.intCast_eq_intCast_iff', ha.emod_eq, hb.emod_eq]

/-- One sparse constraint holds iff its field identity holds. -/
theorem constraintHolds_iff_zmod (c : Constraint) (asg : Assignment) :
    constraintHolds c asg p ↔ fieldDot p c.a asg * fieldDot p c.b asg = fieldDot p c.c asg := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  unfold constraintHolds
  rw [residue_eq_iff (fep_mul _ _ hp) (fep_dotProduct _ _ hp), cast_mul, cast_dotProduct,
    cast_dotProduct, cast_dotProduct]

/-- A sparse system is satisfied iff every constraint's field identity holds. -/
theorem satisfies_iff_zmod (asg : Assignment) :
    ∀ cs : List Constraint,
      satisfies cs asg p ↔ ∀ c ∈ cs, fieldDot p c.a asg * fieldDot p c.b asg = fieldDot p c.c asg
  | [] => by simp [satisfies]
  | c :: cs => by
    rw [satisfies_cons, constraintHolds_iff_zmod, satisfies_iff_zmod asg cs]
    simp

/-- The residue inner product casts to the field inner product. -/
theorem cast_rowDot1 (row : Nat → Int) (z : Assignment) :
    ∀ n, ((rowDot1 row z n p : Int) : ZMod p) = ∑ j ∈ range n, (row j : ZMod p) * (z j : ZMod p)
  | 0 => by simp [rowDot1]
  | n + 1 => by
    rw [show rowDot1 row z (n + 1) p = add (rowDot1 row z n p) (mul (row n) (z n) p) p from rfl,
      cast_add, cast_mul, cast_rowDot1 row z n, sum_range_succ]

/-- On a formatted, bounded row, the field dot product is the dense row sum. -/
theorem fieldDot_eq_sum {row : SparseVector} {asg : Assignment} {n : Nat} (hfmt : asg 0 = 1)
    (hb : rowBounded row n) :
    fieldDot p row asg = ∑ j ∈ range n, (coeffOf row j : ZMod p) * (asg j : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← cast_dotProduct, dotProduct_eq_rowDot1 row asg n hp hfmt hb, cast_rowDot1]

/-- Row `r` of the dense encoding is the coefficient row of constraint `r`. -/
theorem constraintEntry_getElem (sel : Constraint → SparseVector) :
    ∀ (cs : List Constraint) (r : Nat) (hr : r < cs.length) (j : Nat),
      constraintEntry sel cs r j = coeffOf (sel cs[r]) j
  | c :: _, 0, _, j => rfl
  | _ :: cs, r + 1, hr, j => constraintEntry_getElem sel cs r (by simpa using hr) j

/-- The V2 row identity gives the R1CS relation, once the index encodes the
constraint list and `ẑ` interpolates the formatted assignment on `C`. -/
theorem satisfies_of_rows {R Cd : EvalDomain (ZMod p)} {A B Cm : SparseMatrix (ZMod p)}
    (hA : A.Bounded R Cd) (hB : B.Bounded R Cd) (hC : Cm.Bounded R Cd) {cs : List Constraint}
    {asg : Assignment} {zhat : (ZMod p)[X]} (hfmt : asg 0 = 1) (hbnd : systemBounded cs Cd.n)
    (hlen : cs.length ≤ R.n)
    (hidxA : ∀ r < cs.length, ∀ j < Cd.n,
      matrixAt A.nK A.rowIdx A.colIdx A.value r j = (matrixA cs r j : ZMod p))
    (hidxB : ∀ r < cs.length, ∀ j < Cd.n,
      matrixAt B.nK B.rowIdx B.colIdx B.value r j = (matrixB cs r j : ZMod p))
    (hidxC : ∀ r < cs.length, ∀ j < Cd.n,
      matrixAt Cm.nK Cm.rowIdx Cm.colIdx Cm.value r j = (matrixC cs r j : ZMod p))
    (hz : ∀ j < Cd.n, zhat.eval (Cd.node j) = (asg j : ZMod p))
    (hrows : ∀ r < R.n, mzRow Cd A zhat r * mzRow Cd B zhat r = mzRow Cd Cm zhat r) :
    satisfies cs asg p := by
  rw [satisfies_iff_zmod]
  intro c hc
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hc
  have hcb := hbnd _ hc
  have row : ∀ (M : SparseMatrix (ZMod p)) (sel : Constraint → SparseVector),
      M.Bounded R Cd → rowBounded (sel cs[r]) Cd.n →
      (∀ j < Cd.n, matrixAt M.nK M.rowIdx M.colIdx M.value r j =
        (constraintEntry sel cs r j : ZMod p)) →
      fieldDot p (sel cs[r]) asg = mzRow Cd M zhat r := by
    intro M sel hM hrow hidx
    rw [fieldDot_eq_sum hfmt hrow, mzRow_eq_dense hM]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [hidx j hj', hz j hj', constraintEntry_getElem sel cs r hr j]
  rw [row A (fun c => c.a) hA hcb.1 (hidxA r hr), row B (fun c => c.b) hB hcb.2.1 (hidxB r hr),
    row Cm (fun c => c.c) hC hcb.2.2 (hidxC r hr)]
  exact hrows r (lt_of_lt_of_le hr hlen)

end Varuna