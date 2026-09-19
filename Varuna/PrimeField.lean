/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

/-!
# Prime-field carrier

Integers in `[0, p)` with modular add/mul. This is the iteration-0 stand-in
for the scalar field of BLS12-377 used by deployed Varuna. Iteration 1 will
replace it with Mathlib `ZMod p` once vanishing polynomials and AHP
identities need a real `Field`.
-/

namespace Varuna

/-- `p` is an integer ≥ 2 whose only positive divisors are 1 and itself. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ n : Nat, n ∣ p → n = 1 ∨ n = p

/-- Field-element predicate: `x` lies in `[0, p)`. -/
def Fep (p : Nat) (x : Int) : Prop :=
  0 ≤ x ∧ x < (p : Int)

namespace Fep

/-- A field element is already reduced, so `x % p = x`. -/
theorem emod_eq {p : Nat} {x : Int} (hx : Fep p x) : x % (p : Int) = x :=
  Int.emod_eq_of_lt hx.1 hx.2

/-- Zero is a field element whenever `p` is positive. -/
theorem zero {p : Nat} (hp : 0 < p) : Fep p 0 :=
  ⟨Int.le_refl 0, Int.natCast_pos.mpr hp⟩

/-- One is a field element whenever `p ≥ 2`. -/
theorem one {p : Nat} (hp : 2 ≤ p) : Fep p 1 :=
  ⟨by omega, by omega⟩

end Fep

/-- Modular addition in `[0, p)`. -/
def add (x y : Int) (p : Nat) : Int :=
  (x + y) % (p : Int)

/-- Modular multiplication in `[0, p)`. -/
def mul (x y : Int) (p : Nat) : Int :=
  (x * y) % (p : Int)

/-- A positive natural is a nonzero integer, so `% p` is well-defined. -/
private theorem natCast_ne_zero_of_pos {p : Nat} (hp : 0 < p) : (p : Int) ≠ 0 :=
  Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)

/-- The sum of any two integers is a field element modulo `p`. -/
theorem fep_add (x y : Int) {p : Nat} (hp : 0 < p) : Fep p (add x y p) :=
  ⟨Int.emod_nonneg _ (natCast_ne_zero_of_pos hp),
    Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hp)⟩

/-- The product of any two integers is a field element modulo `p`. -/
theorem fep_mul (x y : Int) {p : Nat} (hp : 0 < p) : Fep p (mul x y p) :=
  ⟨Int.emod_nonneg _ (natCast_ne_zero_of_pos hp),
    Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hp)⟩

/-- `1 % p = 1` once `p ≥ 2`. -/
theorem emod_one_of_two_le {p : Nat} (hp : 2 ≤ p) : (1 : Int) % p = 1 :=
  Int.emod_eq_of_lt (by omega) (by omega)

/-- Adding zero on the right is a no-op on a field element. -/
theorem add_zero_right {x : Int} {p : Nat} (hx : Fep p x) : add x 0 p = x := by
  unfold add
  rw [Int.add_zero, hx.emod_eq]

/-- Multiplying a field element by 1 on the left is a no-op. -/
theorem mul_one_left {x : Int} {p : Nat} (_hp : 2 ≤ p) (hx : Fep p x) :
    mul 1 x p = x := by
  unfold mul
  rw [Int.one_mul, hx.emod_eq]

/-- Multiplying by the already-reduced residue `1 % p` is a no-op. -/
theorem mul_one_mod_left {x : Int} {p : Nat} (hp : 2 ≤ p) (hx : Fep p x) :
    mul ((1 : Int) % p) x p = x := by
  rw [emod_one_of_two_le hp, mul_one_left hp hx]

/-- Reducing the left factor modulo `p` does not change a field product. -/
theorem mul_emod_left (a z : Int) (p : Nat) :
    mul (a % (p : Int)) z p = mul a z p := by
  unfold mul
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

/-- Field addition of already-reduced residues agrees with addition of the originals. -/
theorem add_emod_add (x y : Int) (p : Nat) :
    add (x % (p : Int)) (y % (p : Int)) p = add x y p := by
  unfold add
  rw [← Int.add_emod]

/-- Reducing the left factor does not change an integer product modulo `p`. -/
theorem mul_emod_eq (a z : Int) (p : Nat) :
    (a * z) % (p : Int) = (a % (p : Int) * z) % (p : Int) := by
  rw [Int.mul_emod a z (p : Int), Int.mul_emod (a % (p : Int)) z (p : Int),
    Int.emod_emod]

/-- Modular multiplication distributes over integer addition of coefficients. -/
theorem mul_add_coeff (a b z : Int) (p : Nat) :
    mul ((a + b) % (p : Int)) z p =
      add (mul (a % (p : Int)) z p) (mul (b % (p : Int)) z p) p := by
  unfold mul add
  calc
    ((a + b) % (p : Int) * z) % (p : Int)
        = ((a + b) * z) % (p : Int) := (mul_emod_eq (a + b) z p).symm
    _ = (a * z + b * z) % (p : Int) := by rw [Int.add_mul]
    _ = ((a * z) % (p : Int) + (b * z) % (p : Int)) % (p : Int) :=
      Int.add_emod _ _ _
    _ = ((a % (p : Int) * z) % (p : Int) +
            (b % (p : Int) * z) % (p : Int)) % (p : Int) := by
          rw [mul_emod_eq a z p, mul_emod_eq b z p]

/-- Left-distributivity of modular multiplication over integer addition. -/
theorem mul_add_left (a b z : Int) (p : Nat) :
    mul (a + b) z p = add (mul a z p) (mul b z p) p := by
  rw [← mul_emod_left (a + b) z p, mul_add_coeff, mul_emod_left, mul_emod_left]

/-- Modular addition is commutative. -/
theorem add_comm (x y : Int) (p : Nat) : add x y p = add y x p := by
  unfold add
  rw [Int.add_comm]

/-- Modular addition is associative. -/
theorem add_assoc (x y z : Int) (p : Nat) :
    add (add x y p) z p = add x (add y z p) p := by
  unfold add
  rw [Int.emod_add_emod, Int.add_emod_emod, Int.add_assoc]

/-- Left-commutation lemma for three modular addends. -/
theorem add_left_comm (x y z : Int) (p : Nat) :
    add x (add y z p) p = add y (add x z p) p := by
  rw [← add_assoc, add_comm x y, add_assoc]

/-- Right-commutation lemma for three modular addends. -/
theorem add_right_comm (x y z : Int) (p : Nat) :
    add (add x y p) z p = add (add x z p) y p := by
  rw [add_assoc, add_comm y z, ← add_assoc]

/-- Adding zero on the left is a no-op on a field element. -/
theorem add_zero_left {x : Int} {p : Nat} (hx : Fep p x) : add 0 x p = x := by
  unfold add
  rw [Int.zero_add, hx.emod_eq]

/-- Multiplying by zero on the left yields zero. -/
theorem mul_zero_left (z : Int) (p : Nat) : mul 0 z p = 0 := by
  unfold mul
  rw [Int.zero_mul, Int.zero_emod]

end Varuna