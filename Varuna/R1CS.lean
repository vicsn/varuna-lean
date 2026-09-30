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

This module defines both views and proves they agree.

* Sparse-list satisfaction `satisfies` is the snarkVM constraint store.
* Dense Hadamard `hadamardSat` is the AHP relation `Az ∘ Bz = Cz`.
* `satisfies_iff_hadamard` converts between them, including duplicate
  columns and implicit zeros, once every variable index is `< n` and the
  assignment is formatted (`z 0 = 1`, matching snarkVM's constant-1 slot).
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

/-- Column of a pseudo-variable: the constant-1 slot is index `0`. -/
def colIndex : PseudoVar → Nat
  | .one => 0
  | .var v => v

/-- Under a formatted assignment, evaluating a pseudo-var is a lookup. -/
theorem PseudoVar.value_eq_asg (pv : PseudoVar) (asg : Assignment)
    (h : asg 0 = 1) : pv.value asg = asg (colIndex pv) := by
  cases pv with
  | one => simp [PseudoVar.value, colIndex, h]
  | var v => rfl

/-- Unreduced integer coefficient of column `j` in a sparse row. -/
def coeffOf : SparseVector → Nat → Int
  | [], _ => 0
  | (c, pv) :: rest, j =>
    if colIndex pv = j then c + coeffOf rest j else coeffOf rest j

/-- The empty sparse row has coefficient `0` in every column. -/
@[simp] theorem coeffOf_nil (j : Nat) : coeffOf [] j = 0 :=
  rfl

/-- Unfolding a cons cell of `coeffOf`. -/
theorem coeffOf_cons (c : Int) (pv : PseudoVar) (rest : SparseVector) (j : Nat) :
    coeffOf ((c, pv) :: rest) j =
      if colIndex pv = j then c + coeffOf rest j else coeffOf rest j :=
  rfl

/-- Duplicate entries for the same column add in the dense coefficient. -/
theorem coeffOf_duplicate (c₁ c₂ : Int) (pv : PseudoVar) (j : Nat) :
    coeffOf [(c₁, pv), (c₂, pv)] j =
      if colIndex pv = j then c₁ + c₂ else 0 := by
  rw [coeffOf_cons, coeffOf_cons, coeffOf_nil]
  by_cases h : colIndex pv = j
  · simp [h]
  · simp [h]

/-- A column that is never mentioned has dense coefficient `0`. -/
theorem coeffOf_eq_zero_of_not_mem (row : SparseVector) (j : Nat)
    (h : ∀ e ∈ row, colIndex e.2 ≠ j) : coeffOf row j = 0 := by
  induction row with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨c, pv⟩ := e
    have hne : colIndex pv ≠ j := h (c, pv) List.mem_cons_self
    have hrest : ∀ e ∈ rest, colIndex e.2 ≠ j :=
      fun e he => h e (List.mem_cons_of_mem (c, pv) he)
    simp [coeffOf, hne, ih hrest]

/-- Every mentioned column of a sparse row lies in `0 .. n-1`. -/
def rowBounded (row : SparseVector) (n : Nat) : Prop :=
  ∀ e ∈ row, colIndex e.2 < n

/-- The empty row is bounded in every dimension. -/
@[simp] theorem rowBounded_nil (n : Nat) : rowBounded [] n := by
  intro e he
  cases he

/-- Boundedness of a cons cell splits into the head index and the tail. -/
theorem rowBounded_cons (c : Int) (pv : PseudoVar) (rest : SparseVector)
    (n : Nat) :
    rowBounded ((c, pv) :: rest) n ↔
      colIndex pv < n ∧ rowBounded rest n :=
  List.forall_mem_cons

/-- Columns at or past `n` are implicit zeros of a bounded row. -/
theorem coeffOf_eq_zero_of_ge (row : SparseVector) {n j : Nat}
    (hb : rowBounded row n) (hj : n ≤ j) : coeffOf row j = 0 :=
  coeffOf_eq_zero_of_not_mem row j fun e he =>
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (hb e he) hj)

/-- Dense 1-row inner product `∑_{j < n} row j * z j`. -/
def rowDot1 (row : Nat → Int) (z : Assignment) (n p : Nat) : Int :=
  match n with
  | 0 => 0
  | n + 1 => add (rowDot1 row z n p) (mul (row n) (z n) p) p

/-- The 2-dimensional `rowDot` is `rowDot1` of that matrix row. -/
theorem rowDot_eq_rowDot1 (M : Nat → Nat → Int) (i : Nat) (z : Assignment)
    (n p : Nat) : rowDot M i z n p = rowDot1 (fun j => M i j) z n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold rowDot rowDot1
    rw [ih]

/-- A dense 1-row inner product is always a field element. -/
theorem fep_rowDot1 (row : Nat → Int) (z : Assignment) (n : Nat) {p : Nat}
    (hp : 0 < p) : Fep p (rowDot1 row z n p) := by
  induction n with
  | zero => exact Fep.zero hp
  | succ _ _ => exact fep_add _ _ hp

/-- The all-zero dense row dots to `0`. -/
theorem rowDot1_zero (z : Assignment) (n : Nat) {p : Nat} (hp : 0 < p) :
    rowDot1 (fun _ => 0) z n p = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold rowDot1
    rw [ih, mul_zero_left]
    exact add_zero_right (Fep.zero hp)

/-- Dense inner products depend only on the first `n` coefficients. -/
theorem rowDot1_congr {row row' : Nat → Int} {z : Assignment} {n p : Nat}
    (h : ∀ j, j < n → row j = row' j) :
    rowDot1 row z n p = rowDot1 row' z n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold rowDot1
    have ht : ∀ j, j < n → row j = row' j :=
      fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hn : row n = row' n := h n (Nat.lt_succ_self n)
    rw [ih ht, hn]

/-- Adding coefficient `c` at column `k` increases the inner product by `c * zₖ`. -/
theorem rowDot1_add_at (row : Nat → Int) (k : Nat) (c : Int) (z : Assignment)
    (n p : Nat) (hk : k < n) :
    rowDot1 (fun j => if j = k then row j + c else row j) z n p =
      add (rowDot1 row z n p) (mul c (z k) p) p := by
  induction n with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ n ih =>
    rw [show rowDot1 (fun j => if j = k then row j + c else row j) z (n + 1) p =
          add (rowDot1 (fun j => if j = k then row j + c else row j) z n p)
            (mul (if n = k then row n + c else row n) (z n) p) p from rfl]
    rw [show rowDot1 row z (n + 1) p =
          add (rowDot1 row z n p) (mul (row n) (z n) p) p from rfl]
    by_cases hkn : k = n
    · have hpref : ∀ j, j < n →
          (if j = k then row j + c else row j) = row j := by
        intro j hj
        have hjk : j ≠ k := Nat.ne_of_lt (hkn ▸ hj)
        simp [hjk]
      have hlast : (if n = k then row n + c else row n) = row n + c := by
        simp [hkn.symm]
      rw [rowDot1_congr hpref, hlast, mul_add_left, hkn, ← add_assoc]
    · have hk' : k < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkn
      have hlast : (if n = k then row n + c else row n) = row n := by
        simp [Ne.symm hkn]
      rw [ih hk', hlast, add_right_comm]

/-- Sparse dot product equals the dense inner product of summed coefficients. -/
theorem dotProduct_eq_rowDot1 (row : SparseVector) (asg : Assignment)
    (n : Nat) {p : Nat} (hp : 0 < p) (hfmt : asg 0 = 1)
    (hb : rowBounded row n) :
    dotProduct row asg p = rowDot1 (coeffOf row) asg n p := by
  induction row with
  | nil =>
    simpa [dotProduct, coeffOf] using (rowDot1_zero asg n hp).symm
  | cons e rest ih =>
    obtain ⟨c, pv⟩ := e
    have hsplit := (rowBounded_cons c pv rest n).mp hb
    have hpv : colIndex pv < n := hsplit.1
    have hrest : rowBounded rest n := hsplit.2
    rw [dotProduct_cons, PseudoVar.value_eq_asg pv asg hfmt, mul_emod_left,
      ih hrest]
    have hcoeff : ∀ j, j < n →
        coeffOf ((c, pv) :: rest) j =
          (if j = colIndex pv then coeffOf rest j + c else coeffOf rest j) := by
      intro j _
      rw [coeffOf_cons]
      by_cases h : colIndex pv = j
      · simp [h, Int.add_comm]
      · simp [h, Ne.symm h]
    rw [rowDot1_congr hcoeff, rowDot1_add_at (coeffOf rest) (colIndex pv) c
      asg n p hpv, add_comm]

/-- Dense matrix entry of selector `sel` at `(i, j)`; missing rows are zero. -/
def constraintEntry (sel : Constraint → SparseVector) :
    List Constraint → Nat → Nat → Int
  | [], _, _ => 0
  | c :: _, 0, j => coeffOf (sel c) j
  | _ :: rest, i + 1, j => constraintEntry sel rest i j

/-- Dense `A` matrix encoded by a sparse constraint list. -/
def matrixA (cs : List Constraint) : Nat → Nat → Int :=
  constraintEntry (fun c => c.a) cs

/-- Dense `B` matrix encoded by a sparse constraint list. -/
def matrixB (cs : List Constraint) : Nat → Nat → Int :=
  constraintEntry (fun c => c.b) cs

/-- Dense `C` matrix encoded by a sparse constraint list. -/
def matrixC (cs : List Constraint) : Nat → Nat → Int :=
  constraintEntry (fun c => c.c) cs

/-- Row `0` of a cons matrix is the head constraint's coefficients. -/
theorem rowDot_constraintEntry_zero (sel : Constraint → SparseVector)
    (c : Constraint) (cs : List Constraint) (asg : Assignment) (n p : Nat) :
    rowDot (constraintEntry sel (c :: cs)) 0 asg n p =
      rowDot1 (coeffOf (sel c)) asg n p := by
  rw [rowDot_eq_rowDot1]
  exact rowDot1_congr fun _ _ => rfl

/-- Later rows of a cons matrix are the tail system's rows. -/
theorem rowDot_constraintEntry_succ (sel : Constraint → SparseVector)
    (c : Constraint) (cs : List Constraint) (asg : Assignment) (n p : Nat)
    (i : Nat) :
    rowDot (constraintEntry sel (c :: cs)) (i + 1) asg n p =
      rowDot (constraintEntry sel cs) i asg n p := by
  rw [rowDot_eq_rowDot1, rowDot_eq_rowDot1]
  exact rowDot1_congr fun _ _ => rfl

/-- Every sparse row of a constraint uses only columns `< n`. -/
def constraintBounded (c : Constraint) (n : Nat) : Prop :=
  rowBounded c.a n ∧ rowBounded c.b n ∧ rowBounded c.c n

/-- Every constraint of a system uses only columns `< n`. -/
def systemBounded (cs : List Constraint) (n : Nat) : Prop :=
  ∀ c ∈ cs, constraintBounded c n

/-- The empty system is bounded in every dimension. -/
@[simp] theorem systemBounded_nil (n : Nat) : systemBounded [] n := by
  intro c hc
  cases hc

/-- Boundedness of a cons system splits into the head and the tail. -/
theorem systemBounded_cons (c : Constraint) (cs : List Constraint) (n : Nat) :
    systemBounded (c :: cs) n ↔
      constraintBounded c n ∧ systemBounded cs n :=
  List.forall_mem_cons

/-- One sparse constraint holds iff the corresponding Hadamard row holds. -/
theorem constraintHolds_iff_row (c : Constraint) (asg : Assignment)
    (n : Nat) {p : Nat} (hp : 0 < p) (hfmt : asg 0 = 1)
    (hb : constraintBounded c n) :
    constraintHolds c asg p ↔
      mul (rowDot1 (coeffOf c.a) asg n p)
          (rowDot1 (coeffOf c.b) asg n p) p =
        rowDot1 (coeffOf c.c) asg n p := by
  unfold constraintHolds
  rw [dotProduct_eq_rowDot1 c.a asg n hp hfmt hb.1,
    dotProduct_eq_rowDot1 c.b asg n hp hfmt hb.2.1,
    dotProduct_eq_rowDot1 c.c asg n hp hfmt hb.2.2]

/-- Hadamard of a cons system is the head row and the tail system. -/
theorem hadamardSat_cons (c : Constraint) (cs : List Constraint)
    (asg : Assignment) (n p : Nat) :
    hadamardSat (matrixA (c :: cs)) (matrixB (c :: cs)) (matrixC (c :: cs))
        asg n (cs.length + 1) p ↔
      (mul (rowDot1 (coeffOf c.a) asg n p)
          (rowDot1 (coeffOf c.b) asg n p) p =
        rowDot1 (coeffOf c.c) asg n p) ∧
      hadamardSat (matrixA cs) (matrixB cs) (matrixC cs) asg n cs.length p := by
  constructor
  · intro h
    constructor
    · have h0 := h 0 (Nat.succ_pos _)
      rw [matrixA, matrixB, matrixC, rowDot_constraintEntry_zero,
        rowDot_constraintEntry_zero, rowDot_constraintEntry_zero] at h0
      exact h0
    · intro i hi
      have hs := h (i + 1) (Nat.succ_lt_succ hi)
      rw [matrixA, matrixB, matrixC, rowDot_constraintEntry_succ,
        rowDot_constraintEntry_succ, rowDot_constraintEntry_succ] at hs
      exact hs
  · intro ⟨hhead, htail⟩ i hi
    cases i with
    | zero =>
      rw [matrixA, matrixB, matrixC, rowDot_constraintEntry_zero,
        rowDot_constraintEntry_zero, rowDot_constraintEntry_zero]
      exact hhead
    | succ i =>
      have hi' : i < cs.length := Nat.lt_of_succ_lt_succ hi
      rw [matrixA, matrixB, matrixC, rowDot_constraintEntry_succ,
        rowDot_constraintEntry_succ, rowDot_constraintEntry_succ]
      exact htail i hi'

/-- Sparse snarkVM constraints are the Hadamard identity of the matrices they encode. -/
theorem satisfies_iff_hadamard (cs : List Constraint) (asg : Assignment)
    (n : Nat) {p : Nat} (hp : 0 < p) (hfmt : asg 0 = 1)
    (hb : systemBounded cs n) :
    satisfies cs asg p ↔
      hadamardSat (matrixA cs) (matrixB cs) (matrixC cs) asg n cs.length p := by
  induction cs with
  | nil =>
    constructor
    · intro _
      exact hadamardSat_zero _ _ _ _ _ _
    · intro _
      exact trivial
  | cons c rest ih =>
    have hsplit := (systemBounded_cons c rest n).mp hb
    rw [satisfies_cons, ih hsplit.2, List.length_cons, hadamardSat_cons,
      constraintHolds_iff_row c asg n hp hfmt hsplit.1]

/-- Prepend the constant-1 slot. Matches `ConstraintSystem::format_public_input`. -/
def formatPublicInput (xs : List Int) : List Int :=
  1 :: xs

/-- Drop the constant-1 slot. Matches `unformat_public_input`. -/
def unformatPublicInput : List Int → List Int
  | [] => []
  | _ :: rest => rest

/-- Unformatting undoes formatting. -/
@[simp] theorem unformat_formatPublicInput (xs : List Int) :
    unformatPublicInput (formatPublicInput xs) = xs :=
  rfl

/-- A formatted public input is nonempty and starts with `1`. -/
theorem formatPublicInput_head (xs : List Int) :
    (formatPublicInput xs).head? = some 1 :=
  rfl

/-- Positive powers of two, matching snarkVM `count_ones() == 1`. -/
inductive PowTwo : Nat → Prop where
  | one : PowTwo 1
  | twice {n : Nat} : PowTwo n → PowTwo (2 * n)

/-- A power of two is positive. -/
theorem PowTwo.pos {n : Nat} (h : PowTwo n) : 0 < n := by
  induction h with
  | one => exact Nat.one_pos
  | twice _ ih => exact Nat.mul_pos (by decide : 0 < 2) ih

/-- Formatted public input is admissible iff its length is a power of two. -/
def formattedPublicInputAdmissible (input : List Int) : Prop :=
  PowTwo input.length

/-- Admissibility of a formatted input is a statement about `1 + |x|`. -/
theorem formattedPublicInputAdmissible_format (xs : List Int) :
    formattedPublicInputAdmissible (formatPublicInput xs) ↔
      PowTwo (xs.length + 1) :=
  Iff.rfl

/-- The empty public input formats to `[1]`, which is admissible. -/
theorem formatPublicInput_nil_admissible :
    formattedPublicInputAdmissible (formatPublicInput []) :=
  PowTwo.one

/-- Pad a list with `k` trailing zeros (snarkVM `pad_input_for_indexer_and_prover`). -/
def padZeros (xs : List Int) (k : Nat) : List Int :=
  xs ++ List.replicate k 0

/-- Padding with zeros does not change the length formula ` |xs| + k `. -/
theorem padZeros_length (xs : List Int) (k : Nat) :
    (padZeros xs k).length = xs.length + k := by
  simp [padZeros]

/-- Padding a formatted input preserves the constant-1 head. -/
theorem padZeros_head_one (xs : List Int) (k : Nat) :
    (padZeros (formatPublicInput xs) k).head? = some 1 :=
  rfl

/-- Padding to a power-of-two length is an admissible formatted input. -/
theorem padZeros_admissible (xs : List Int) {k : Nat}
    (h : PowTwo (xs.length + k)) :
    formattedPublicInputAdmissible (padZeros xs k) := by
  simpa [formattedPublicInputAdmissible, padZeros] using h

/-- Read a list as an assignment; missing indices are `0`. -/
def assignmentOf (vals : List Int) : Assignment :=
  fun v => vals[v]?.getD 0

/-- Index `0` of a formatted public input is the constant `1`. -/
theorem assignmentOf_format_zero (xs : List Int) :
    assignmentOf (formatPublicInput xs) 0 = 1 :=
  rfl

/-- Padding a formatted input leaves the constant-1 slot unchanged. -/
theorem assignmentOf_padZeros_format_zero (xs : List Int) (k : Nat) :
    assignmentOf (padZeros (formatPublicInput xs) k) 0 = 1 :=
  rfl

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

/-- A monomial `1 · v` is bounded once `v < n`. -/
theorem rowBounded_monomial (v n : Nat) (hv : v < n) :
    rowBounded (monomial 1 v) n := by
  intro e he
  have : e = (1, PseudoVar.var v) := by
    simp [monomial] at he
    exact he
  rw [this, colIndex]
  exact hv

/-- A multiplication constraint is bounded once each variable is `< n`. -/
theorem constraintBounded_mul (x y out n : Nat)
    (hx : x < n) (hy : y < n) (hout : out < n) :
    constraintBounded (mulConstraint x y out) n :=
  ⟨rowBounded_monomial x n hx, rowBounded_monomial y n hy,
    rowBounded_monomial out n hout⟩

/-- Formatted assignment: constant-`1` at index 0, then `3 * 5 = 15`. -/
def formattedToyAsg : Assignment
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 15
  | _ => 0

/-- The formatted toy assignment has a constant-`1` slot. -/
theorem formattedToyAsg_zero : formattedToyAsg 0 = 1 :=
  rfl

/-- The formatted toy multiplication system uses only columns `< 4`. -/
theorem formatted_toy_systemBounded :
    systemBounded [mulConstraint 1 2 3] 4 := by
  intro c hc
  have : c = mulConstraint 1 2 3 := by
    simp at hc
    exact hc
  rw [this]
  exact constraintBounded_mul 1 2 3 4 (by decide) (by decide) (by decide)

/-- Sparse ↔ Hadamard on the formatted toy: `1 · (x)(y)=(out)` over `𝔽₁₇`. -/
theorem formatted_toy_iff :
    satisfies [mulConstraint 1 2 3] formattedToyAsg toyPrime ↔
      hadamardSat (matrixA [mulConstraint 1 2 3])
        (matrixB [mulConstraint 1 2 3])
        (matrixC [mulConstraint 1 2 3]) formattedToyAsg 4 1 toyPrime :=
  satisfies_iff_hadamard _ _ 4 (by unfold toyPrime; omega)
    formattedToyAsg_zero formatted_toy_systemBounded

/-- Field-element facts for the formatted toy assignment over `𝔽₁₇`. -/
theorem formatted_toy_fep (v : Var) : Fep toyPrime (formattedToyAsg v) := by
  unfold formattedToyAsg toyPrime Fep
  split <;> omega

/-- The formatted toy instance satisfies the sparse multiplication constraint. -/
theorem formatted_toy_holds :
    satisfies [mulConstraint 1 2 3] formattedToyAsg toyPrime := by
  refine (satisfies_single _ _ _).mpr ?_
  refine (mulConstraint_holds_iff 1 2 3 formattedToyAsg
    (by unfold toyPrime; omega)
    (formatted_toy_fep 1) (formatted_toy_fep 2) (formatted_toy_fep 3)).mpr ?_
  unfold formattedToyAsg toyPrime mul
  rfl

end Varuna