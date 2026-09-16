/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.PrimeField

/-!
# The Varuna SNARK relation : R1CS

Varuna (Marlin [CHMMVW19], as specified in `varuna-sage-impl/docs/spec.pdf`
and implemented in snarkVM) proves knowledge of a witness `z` satisfying

\[
  Az \circ Bz = Cz
\]

over a prime field — the Hadamard (row-wise) product of the three matrix–
vector products. snarkVM stores the same relation as a list of sparse
constraints `(Aᵢ · z)(Bᵢ · z) = (Cᵢ · z)`.

This module is iteration 0 of the formalization : it defines both views and
proves the first sorry-free lemmas the rest of the AHP will sit on.

* **Proven (this commit).** Empty systems are satisfied; a single
  multiplication constraint holds iff the assigned values multiply; the
  Hadamard form of the empty system holds.
* **Not yet proven.** The general sparse-list ↔ dense-Hadamard equivalence
  for arbitrary rows (duplicate columns, missing indices). That is the
  remainder of this layer, marked `hyp` on the proof map.
-/

namespace Varuna

/-- Circuit variable indices. Index `0` is conventionally the constant-`1`
slot in formatted Varuna public inputs; we still model the constant
explicitly as `PseudoVar.one` so the encoding is not smuggled into the
assignment. -/
abbrev Var := Nat

/-- Total assignment of field elements to variables. -/
abbrev Assignment := Var → Int

/-- Every assigned value is a field element. -/
def Valuationp (asg : Assignment) (p : Nat) : Prop :=
  ∀ v, Fep p (asg v)

/-- A pseudo-variable is a circuit variable or the constant `1`. -/
inductive PseudoVar where
  | one
  | var (v : Var)
deriving Repr, DecidableEq, Inhabited

/-- Evaluate a pseudo-variable: the constant 1, or the assigned value. -/
def PseudoVar.value (pv : PseudoVar) (asg : Assignment) : Int :=
  match pv with
  | .one => 1
  | .var v => asg v

/-- Sparse vector: unmentioned pseudo-vars have coefficient `0`.
Coefficients may be any integer; they are reduced modulo `p` on use, so
`-1` is a legal encoding of `p - 1` (matching snarkVM). -/
abbrev SparseVector := List (Int × PseudoVar)

/-- Dot product of a sparse vector with an assignment, in the prime field. -/
def dotProduct (vec : SparseVector) (asg : Assignment) (p : Nat) : Int :=
  match vec with
  | [] => 0
  | (coeff, pv) :: rest =>
    add (mul (coeff % (p : Int)) (pv.value asg) p) (dotProduct rest asg p) p

/-- The empty sparse vector dots to 0. -/
@[simp] theorem dotProduct_nil (asg : Assignment) (p : Nat) :
    dotProduct [] asg p = 0 :=
  rfl

/-- Unfolding a cons cell of a sparse dot product. -/
theorem dotProduct_cons (coeff : Int) (pv : PseudoVar) (rest : SparseVector)
    (asg : Assignment) (p : Nat) :
    dotProduct ((coeff, pv) :: rest) asg p =
      add (mul (coeff % (p : Int)) (pv.value asg) p)
        (dotProduct rest asg p) p :=
  rfl

/-- A sparse dot product is always a field element. -/
theorem fep_dotProduct (vec : SparseVector) (asg : Assignment) {p : Nat}
    (hp : 0 < p) : Fep p (dotProduct vec asg p) := by
  induction vec with
  | nil => exact Fep.zero hp
  | cons _ _ ih =>
    rw [dotProduct_cons]
    exact fep_add _ _ hp

/-- One R1CS constraint `(A · z) * (B · z) = (C · z)`. -/
structure Constraint where
  a : SparseVector
  b : SparseVector
  c : SparseVector
deriving Repr, DecidableEq, Inhabited

/-- A constraint holds when the Hadamard identity is true at this row. -/
def constraintHolds (c : Constraint) (asg : Assignment) (p : Nat) : Prop :=
  mul (dotProduct c.a asg p) (dotProduct c.b asg p) p = dotProduct c.c asg p

/-- Satisfaction of a list of constraints — the sparse view used by snarkVM. -/
def satisfies : List Constraint → Assignment → Nat → Prop
  | [], _, _ => True
  | c :: cs, asg, p => constraintHolds c asg p ∧ satisfies cs asg p

/-- An empty constraint list is satisfied by any assignment. -/
@[simp] theorem satisfies_nil (asg : Assignment) (p : Nat) :
    satisfies [] asg p :=
  trivial

/-- Satisfaction of a cons cell is the head constraint and the tail. -/
theorem satisfies_cons (c : Constraint) (cs : List Constraint)
    (asg : Assignment) (p : Nat) :
    satisfies (c :: cs) asg p ↔
      constraintHolds c asg p ∧ satisfies cs asg p :=
  Iff.rfl

/-- A singleton list is satisfied iff its unique constraint holds. -/
theorem satisfies_single (c : Constraint) (asg : Assignment) (p : Nat) :
    satisfies [c] asg p ↔ constraintHolds c asg p := by
  simp [satisfies_cons]

/-- Satisfaction splits over list append. -/
theorem satisfies_append (cs1 cs2 : List Constraint)
    (asg : Assignment) (p : Nat) :
    satisfies (cs1 ++ cs2) asg p ↔
      satisfies cs1 asg p ∧ satisfies cs2 asg p := by
  induction cs1 with
  | nil => simp [satisfies]
  | cons c cs ih =>
    rw [List.cons_append, satisfies_cons, satisfies_cons, ih]
    exact and_assoc.symm

/-- A one-term sparse vector `coeff · v`. -/
def monomial (coeff : Int) (v : Var) : SparseVector :=
  [(coeff, .var v)]

/-- The multiplication constraint `(x)(y) = (out)`. -/
def mulConstraint (x y out : Var) : Constraint :=
  { a := monomial 1 x, b := monomial 1 y, c := monomial 1 out }

/-- Evaluating a variable pseudo-var reads the assignment. -/
theorem PseudoVar.value_var (v : Var) (asg : Assignment) :
    (PseudoVar.var v).value asg = asg v :=
  rfl

/-- Dotting the unit monomial `1 · v` recovers the assigned value. -/
theorem dotProduct_monomial_one (v : Var) (asg : Assignment) {p : Nat}
    (hp : 2 ≤ p) (hv : Fep p (asg v)) :
    dotProduct (monomial 1 v) asg p = asg v := by
  unfold monomial
  rw [dotProduct_cons, dotProduct_nil, PseudoVar.value_var]
  have hmul : mul ((1 : Int) % p) (asg v) p = asg v :=
    mul_one_mod_left hp hv
  rw [hmul]
  exact add_zero_right hv

/-- A multiplication constraint holds iff the assigned values multiply. -/
theorem mulConstraint_holds_iff (x y out : Var) (asg : Assignment) {p : Nat}
    (hp : 2 ≤ p) (hx : Fep p (asg x)) (hy : Fep p (asg y))
    (hout : Fep p (asg out)) :
    constraintHolds (mulConstraint x y out) asg p ↔
      asg out = mul (asg x) (asg y) p := by
  unfold mulConstraint constraintHolds
  rw [dotProduct_monomial_one x asg hp hx,
      dotProduct_monomial_one y asg hp hy,
      dotProduct_monomial_one out asg hp hout]
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

/-- Dense row-dot `∑_{j < n} M i j * z j`, computed recursively. -/
def rowDot (M : Nat → Nat → Int) (i : Nat) (z : Assignment) (n p : Nat) : Int :=
  match n with
  | 0 => 0
  | n + 1 =>
    add (rowDot M i z n p) (mul (M i n) (z n) p) p

/-- Hadamard form of R1CS: `(Az)ᵢ (Bz)ᵢ = (Cz)ᵢ` for every row `i < m`. -/
def hadamardSat (A B C : Nat → Nat → Int) (z : Assignment)
    (n m p : Nat) : Prop :=
  ∀ i, i < m →
    mul (rowDot A i z n p) (rowDot B i z n p) p = rowDot C i z n p

/-- The empty Hadamard system (`m = 0`) holds for any matrices and witness. -/
theorem hadamardSat_zero (A B C : Nat → Nat → Int) (z : Assignment)
    (n p : Nat) : hadamardSat A B C z n 0 p := by
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

/-- Toy prime used by the concrete multiplication check. -/
def toyPrime : Nat := 17

/-- Toy assignment `x=3, y=5, out=15` for the multiplication check. -/
def toyAsg : Assignment
  | 0 => 3
  | 1 => 5
  | 2 => 15
  | _ => 0

/-- Every value of the toy assignment is a field element of `𝔽₁₇`. -/
theorem toy_fep (v : Var) : Fep toyPrime (toyAsg v) := by
  unfold toyAsg toyPrime Fep
  split <;> omega

/-- Concrete instance: `3 * 5 = 15` satisfies the multiplication constraint over `𝔽₁₇`. -/
theorem toy_mul_holds :
    constraintHolds (mulConstraint 0 1 2) toyAsg toyPrime := by
  refine (mulConstraint_holds_iff 0 1 2 toyAsg
    (by unfold toyPrime; omega)
    (toy_fep 0) (toy_fep 1) (toy_fep 2)).mpr ?_
  unfold toyAsg toyPrime mul
  rfl

end Varuna