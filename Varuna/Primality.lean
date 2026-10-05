/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Varuna.Field

/-!
# Primality of the BLS12-377 scalar modulus

A Pratt certificate. Lucas's test (`lucas_primality`) takes a witness `a`
and the prime factors of `p - 1`; each factor above `10^3` gets its own
certificate. The modular powers are square-and-multiply on numerals
(`powMod`), which the kernel evaluates with its arbitrary-precision `Nat`
arithmetic.
-/

namespace Varuna

/-- `b ^ e % m`, square-and-multiply on the low `n` bits of `e`. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | n + 1, b, e =>
    let r := powMod m n (b * b % m) (e / 2)
    if e % 2 = 0 then r else r * b % m

theorem powMod_cast (m : ℕ) :
    ∀ n b e, e < 2 ^ n → ((powMod m n b e : ℕ) : ZMod m) = (b : ZMod m) ^ e
  | 0, b, e, he => by
    obtain rfl : e = 0 := by omega
    rw [powMod, ZMod.natCast_mod]
    simp
  | n + 1, b, e, he => by
    have ih := powMod_cast m n (b * b % m) (e / 2) (by rw [pow_succ] at he; omega)
    have hb : ((b * b % m : ℕ) : ZMod m) = (b : ZMod m) ^ 2 := by
      rw [ZMod.natCast_mod, Nat.cast_mul, sq]
    rw [hb, ← pow_mul] at ih
    have he2 := Nat.div_add_mod e 2
    simp only [powMod]
    split_ifs with h
    · rw [ih]
      congr 1
      omega
    · rw [ZMod.natCast_mod, Nat.cast_mul, ih, ← pow_succ]
      congr 1
      omega

theorem powMod_lt (m : ℕ) (hm : 0 < m) : ∀ n b e, powMod m n b e < m
  | 0, _, _ => Nat.mod_lt _ hm
  | n + 1, b, e => by
    simp only [powMod]
    split_ifs
    · exact powMod_lt m hm n _ _
    · exact Nat.mod_lt _ hm

/-- Lucas's test on a factorization of `p - 1` into prime powers. -/
theorem prime_of_lucas (p a n : ℕ) (fs : List (ℕ × ℕ)) (hn : p - 1 < 2 ^ n)
    (hfs : ∀ f ∈ fs, f.1.Prime) (hprod : (fs.map fun f => f.1 ^ f.2).prod = p - 1)
    (ha : powMod p n a (p - 1) = 1) (hd : ∀ f ∈ fs, powMod p n a ((p - 1) / f.1) ≠ 1) :
    p.Prime := by
  have hpos : 0 < p - 1 := by
    rw [← hprod]
    refine List.prod_pos fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    exact pow_pos (hfs f hf).pos _
  have hp : 1 < p := by omega
  refine lucas_primality p a ?_ fun q hq hdvd heq => ?_
  · rw [← powMod_cast p n a _ hn, ha, Nat.cast_one]
  · rw [← hprod] at hdvd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).1 hdvd
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hfs f hf)).1 (hq.dvd_of_dvd_pow hqx)
    have h1 : ((powMod p n a ((p - 1) / f.1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [powMod_cast p n a _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn), heq, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (powMod_lt p (by omega) _ _ _),
      Nat.mod_eq_of_lt hp] at h1
    exact hd f hf h1

theorem prime_3511 : Nat.Prime 3511 :=
  prime_of_lucas 3511 7 12 [(2, 1), (3, 3), (5, 1), (13, 1)] (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]; norm_num)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_126397 : Nat.Prime 126397 :=
  prime_of_lucas 126397 5 17 [(2, 2), (3, 2), (3511, 1)] (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]
        exact ⟨by norm_num, by norm_num, prime_3511, by simp⟩)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_1832756501 : Nat.Prime 1832756501 :=
  prime_of_lucas 1832756501 2 31 [(2, 2), (5, 3), (29, 1), (126397, 1)] (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_126397, by simp⟩)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_49484425527001 : Nat.Prime 49484425527001 :=
  prime_of_lucas 49484425527001 14 46 [(2, 3), (3, 3), (5, 3), (1832756501, 1)] (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_1832756501, by simp⟩)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_958612291309063373 : Nat.Prime 958612291309063373 :=
  prime_of_lucas 958612291309063373 2 60 [(2, 2), (29, 1), (167, 1), (49484425527001, 1)]
    (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]
        exact ⟨by norm_num, by norm_num, by norm_num, prime_49484425527001, by simp⟩)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_9586122913090633729 : Nat.Prime 9586122913090633729 :=
  prime_of_lucas 9586122913090633729 11 64 [(2, 46), (3, 1), (7, 1), (13, 1), (499, 1)]
    (by decide) (by simp only [List.forall_mem_cons, List.not_mem_nil]; norm_num)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem prime_bls12_377_r : Nat.Prime bls12_377_r :=
  prime_of_lucas bls12_377_r 22 253
    [(2, 47), (3, 1), (5, 1), (7, 1), (13, 1), (499, 1), (958612291309063373, 1),
      (9586122913090633729, 2)]
    (by decide)
    (by simp only [List.forall_mem_cons, List.not_mem_nil]
        exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
          prime_958612291309063373, prime_9586122913090633729, by simp⟩)
    (by decide) (by decide +kernel) (by decide +kernel)

instance fact_prime_bls12_377_r : Fact (Nat.Prime bls12_377_r) :=
  ⟨prime_bls12_377_r⟩

end Varuna