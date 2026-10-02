/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Tactic.LinearCombination
import Varuna.Selectors

/-!
# Counting bad challenges

Probabilities are counts over a finite challenge set `S : Finset F`, which
need not be all of `F` : snarkVM squeezes 252-bit AHP challenges and 168-bit
PC challenges. A bound `card (bad ∩ S) ≤ d` reads as error `d / | S | `.

* Per challenge : a nonzero residual has at most `deg` bad challenges; a
  combination with one free, uniformly drawn weight has at most one.
* Across rounds : `card_hits_le` is the adaptive union bound. Challenges are
  a tape of answers; the bad set at each step may depend on all earlier
  answers (the prover adapts). Over all ` | S | ^n` tapes, at most
  `(Σ_i b_i) · | S | ^{n-1}` hit a bad set.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## One challenge -/

/-- A nonzero polynomial vanishes on at most `natDegree` challenges of `S`. -/
theorem card_filter_eval_eq_zero_le {p : F[X]} (hp : p ≠ 0) (S : Finset F) :
    (S.filter fun α => p.eval α = 0).card ≤ p.natDegree :=
  (card_le_card fun _ hα => Multiset.mem_toFinset.2 ((mem_roots hp).2 (mem_filter.mp hα).2)).trans
    (card_szBadSet_le_natDegree p)

/-- `inspectResidual` reports a break on at most `natDegree` challenges of `S`. -/
theorem card_filter_inspectResidual_le (res : F[X]) (S : Finset F) :
    (S.filter fun α => inspectResidual res α ≠ none).card ≤ res.natDegree := by
  by_cases h0 : res = 0
  · simp [inspectResidual, h0]
  · refine (card_le_card fun α hα => ?_).trans (card_filter_eval_eq_zero_le h0 S)
    simp only [mem_filter] at hα ⊢
    refine ⟨hα.1, ?_⟩
    by_contra hne
    exact hα.2 (by simp [inspectResidual, h0, hne])

/-- `inspectBatch` reports data exactly when the combination vanishes on a live claim. -/
theorem inspectBatch_ne_none_iff (ws cs : List F) :
    inspectBatch ws cs ≠ none ↔ weightedSum ws cs = 0 ∧ ∃ c ∈ cs, c ≠ 0 := by
  rw [← hasNonzero_iff]
  unfold inspectBatch
  split_ifs with h <;> simp_all [Bool.and_eq_true]

/-- With one free weight `η` on a nonzero claim, at most one `η ∈ S` cancels. -/
theorem card_filter_linear_le_one {a c : F} (hc : c ≠ 0) (S : Finset F) :
    (S.filter fun η => a + η * c = 0).card ≤ 1 := by
  refine card_le_one.mpr fun x hx y hy => ?_
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  have h : (x - y) * c = 0 := by linear_combination hx' - hy'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hc)

/-- Two claims combined as `a + η b` with `η` drawn from `S`: at most one bad `η`. -/
theorem card_filter_inspectBatch_pair (a b : F) (S : Finset F) :
    (S.filter fun η => inspectBatch [1, η] [a, b] ≠ none).card ≤ 1 := by
  by_cases hb : b = 0
  · have hempty : (S.filter fun η => inspectBatch [1, η] [a, b] ≠ none) = ∅ := by
      refine filter_eq_empty_iff.mpr fun η _ h => ?_
      obtain ⟨hs, c, hc, hne⟩ := (inspectBatch_ne_none_iff _ _).1 h
      simp only [weightedSum_cons, weightedSum_nil_weights, hb, mul_zero, add_zero,
        one_mul] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hne hs
      · exact hne hb
    rw [hempty, card_empty]
    exact zero_le_one
  · refine (card_le_card fun η hη => ?_).trans (card_filter_linear_le_one (a := a) hb S)
    have ⟨hs, _⟩ := (inspectBatch_ne_none_iff _ _).1 (mem_filter.mp hη).2
    simp only [weightedSum_cons, weightedSum_nil_weights, add_zero, one_mul] at hs
    exact mem_filter.mpr ⟨(mem_filter.mp hη).1, hs⟩

/-- Two claims on a domain `D` combined as `a + η b`, with `η` drawn from `S` : at most
one bad `η`, however large `D` is. A point where `b` is live fixes `η`; if `b`
vanishes on `D`, no `η` is bad. -/
theorem card_filter_inspectBatchOn_pair (D : List F) (a b : F → F) (S : Finset F) :
    (S.filter fun η => inspectBatchOn D [1, η] (fun x => [a x, b x]) ≠ none).card ≤ 1 := by
  by_cases hb : ∃ x ∈ D, b x ≠ 0
  · obtain ⟨x₀, hx₀, hb₀⟩ := hb
    refine (card_le_card fun η hη => ?_).trans (card_filter_linear_le_one (a := a x₀) hb₀ S)
    obtain ⟨hacc, _⟩ := (inspectBatchOn_ne_none_iff _ _ _).1 (mem_filter.mp hη).2
    have h₀ := hacc x₀ hx₀
    simp only [weightedSum_cons, weightedSum_nil_weights, add_zero, one_mul] at h₀
    exact mem_filter.mpr ⟨(mem_filter.mp hη).1, h₀⟩
  · push Not at hb
    have hempty :
        (S.filter fun η => inspectBatchOn D [1, η] (fun x => [a x, b x]) ≠ none) = ∅ := by
      refine filter_eq_empty_iff.mpr fun η _ h => ?_
      obtain ⟨hacc, x, hx, c, hc, hne⟩ := (inspectBatchOn_ne_none_iff _ _ _).1 h
      have hs := hacc x hx
      simp only [weightedSum_cons, weightedSum_nil_weights, hb x hx, mul_zero, add_zero,
        one_mul] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hne hs
      · exact hne (hb x hx)
    rw [hempty, card_empty]
    exact zero_le_one

/-- The batched rowcheck over two circuits, with first-round weights `[1, ν]` : at
most one bad `ν ∈ S` on all of `H`. Counted point by point, the same event could
cost one bad `ν` per point of `H`. -/
theorem card_filter_batchedZerocheck_pair (H : EvalDomain F) (c₀ c₁ : EvalDomain F × F[X])
    (S : Finset F) :
    (S.filter fun ν =>
      inspectBatchOn H.nodeList [1, ν] (batchedClaims H [c₀, c₁]) ≠ none).card ≤ 1 :=
  card_filter_inspectBatchOn_pair H.nodeList (fun x => (selectorPoly H c₀.1 * c₀.2).eval x)
    (fun x => (selectorPoly H c₁.1 * c₁.2).eval x) S

/-! ## Challenge tapes -/

/-- All answer tapes of length `n` with entries in `S`. -/
def tapes (S : Finset F) : ℕ → Finset (List F)
  | 0 => {[]}
  | n + 1 => S.biUnion fun a => (tapes S n).image (a :: ·)

/-- There are `|S|^n` tapes. -/
theorem card_tapes (S : Finset F) : ∀ n, (tapes S n).card = S.card ^ n
  | 0 => rfl
  | n + 1 => by
    rw [tapes, card_biUnion]
    · simp only [card_image_of_injective _ (List.cons_injective), card_tapes S n, sum_const,
        smul_eq_mul, pow_succ]
      ring
    · intro a _ a' _ haa'
      simp only [Function.onFun, disjoint_left, mem_image]
      rintro _ ⟨t, _, rfl⟩ ⟨t', _, h⟩
      exact haa' (List.cons.inj h).1.symm

/-- A tape of length `n` has length `n` and entries in `S`. -/
theorem mem_tapes {S : Finset F} :
    ∀ {n : ℕ} {t : List F}, t ∈ tapes S n → t.length = n ∧ ∀ a ∈ t, a ∈ S
  | 0, t, h => by
    rw [tapes, mem_singleton] at h
    subst h
    simp
  | n + 1, t, h => by
    simp only [tapes, mem_biUnion, mem_image] at h
    obtain ⟨a, ha, t', ht', rfl⟩ := h
    obtain ⟨hlen, hS⟩ := mem_tapes ht'
    refine ⟨by simp [hlen], ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨ha, hS⟩

/-- Whether some answer lands in the bad set of its prefix. -/
def hitsB (Bad : List F → Finset F) : List F → List F → Bool
  | _, [] => false
  | pre, a :: t => decide (a ∈ Bad pre) || hitsB Bad (pre ++ [a]) t

/-- A hit is an index whose answer is bad for the prefix before it. -/
theorem hitsB_iff (Bad : List F → Finset F) :
    ∀ (t pre : List F), hitsB Bad pre t = true ↔
      ∃ i, ∃ h : i < t.length, t[i] ∈ Bad (pre ++ t.take i)
  | [], pre => by simp [hitsB]
  | a :: t, pre => by
    rw [hitsB, Bool.or_eq_true, decide_eq_true_iff, hitsB_iff Bad t (pre ++ [a])]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · exact ⟨i + 1, by simpa using hi, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => left; simpa using h
      | succ i => right; exact ⟨i, by simpa using hi, by simpa using h⟩

/-- Adaptive union bound. If the bad set after a prefix of length `k` holds at
most `b k` elements of `S`, at most `(Σ_{i<n} b ( | pre | + i)) · | S | ^{n-1}` of
the ` | S | ^n` tapes hit. -/
theorem card_hits_le (S : Finset F) (Bad : List F → Finset F) (b : ℕ → ℕ)
    (hb : ∀ pre, (S.filter (· ∈ Bad pre)).card ≤ b pre.length) :
    ∀ (n : ℕ) (pre : List F),
      ((tapes S n).filter fun t => hitsB Bad pre t = true).card ≤
        (∑ i ∈ range n, b (pre.length + i)) * S.card ^ (n - 1)
  | 0, pre => by simp [tapes, hitsB]
  | n + 1, pre => by
    rw [tapes, filter_biUnion]
    refine card_biUnion_le.trans ?_
    set T := ∑ i ∈ range n, b (pre.length + 1 + i) with hT
    have hstep : ∀ a ∈ S, (((tapes S n).image (a :: ·)).filter
          fun t => hitsB Bad pre t = true).card ≤
        (if a ∈ Bad pre then S.card ^ n else 0) + T * S.card ^ (n - 1) := by
      intro a _
      rw [filter_image]
      refine card_image_le.trans ?_
      by_cases ha : a ∈ Bad pre
      · rw [if_pos ha, ← card_tapes S n]
        exact (card_filter_le _ _).trans (Nat.le_add_right _ _)
      · rw [if_neg ha, zero_add]
        have ih := card_hits_le S Bad b hb n (pre ++ [a])
        simp only [List.length_append, List.length_singleton] at ih
        have hcongr : ((tapes S n).filter fun t => hitsB Bad pre (a :: t) = true) =
            (tapes S n).filter fun t => hitsB Bad (pre ++ [a]) t = true :=
          filter_congr fun t _ => by simp [hitsB, ha]
        simpa [Function.comp_def, hcongr, ← hT] using ih
    refine (sum_le_sum hstep).trans ?_
    rw [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, sum_const, smul_eq_mul]
    have hbad : (S.filter fun a => a ∈ Bad pre).card ≤ b pre.length := hb pre
    have hkey : S.card * (T * S.card ^ (n - 1)) ≤ T * S.card ^ n := by
      rcases n with _ | n
      · simp [hT]
      · rw [Nat.add_sub_cancel, pow_succ]
        exact le_of_eq (by ring)
    have hsplit : ∑ i ∈ range (n + 1), b (pre.length + i) = b pre.length + T := by
      rw [sum_range_succ', add_zero, Nat.add_comm, hT]
      congr 1
      exact sum_congr rfl fun i _ => by congr 1; omega
    rw [hsplit, Nat.add_sub_cancel, add_mul]
    exact add_le_add (Nat.mul_le_mul_right _ hbad) hkey

/-- Filtering by membership in `T` keeps at most `|T|` elements. -/
theorem card_filter_mem_le (S T : Finset F) : (S.filter (· ∈ T)).card ≤ T.card :=
  card_le_card fun _ hx => (mem_filter.mp hx).2

/-! ## The three AHP challenges -/

/-- Bad sets of the three AHP rounds for an adaptive prover: the rowcheck
residual is fixed before `α`, the lineval residual may depend on `α`, and
the matrix residual on `α, β`. -/
noncomputable def ahpBad (S : Finset F) (resR : F[X]) (resL : F → F[X]) (resM : F → F → F[X]) :
    List F → Finset F
  | [] => S.filter fun α => inspectResidual resR α ≠ none
  | [α] => S.filter fun β => inspectResidual (resL α) β ≠ none
  | [α, β] => S.filter fun γ => inspectResidual (resM α β) γ ≠ none
  | _ => ∅

/-- Composed error of the interactive AHP: over all `(α, β, γ) ∈ S³`, at most
`(d_R + d_L + d_M) · | S | ²` produce a Schwartz–Zippel break, where the
degrees bound the (adaptively chosen) residuals. -/
theorem ahp_error (S : Finset F) (resR : F[X]) (resL : F → F[X]) (resM : F → F → F[X])
    {dR dL dM : ℕ} (hR : resR.natDegree ≤ dR) (hL : ∀ α, (resL α).natDegree ≤ dL)
    (hM : ∀ α β, (resM α β).natDegree ≤ dM) :
    ((tapes S 3).filter fun t => hitsB (ahpBad S resR resL resM) [] t = true).card ≤
      (dR + dL + dM) * S.card ^ 2 := by
  let b : ℕ → ℕ := fun k =>
    if k = 0 then dR else if k = 1 then dL else if k = 2 then dM else 0
  have hb : ∀ pre, (S.filter (· ∈ ahpBad S resR resL resM pre)).card ≤ b pre.length := by
    intro pre
    match pre with
    | [] =>
      show (S.filter (· ∈ S.filter fun α => inspectResidual resR α ≠ none)).card ≤ dR
      exact (card_filter_mem_le _ _).trans ((card_filter_inspectResidual_le resR S).trans hR)
    | [α] =>
      show (S.filter (· ∈ S.filter fun β => inspectResidual (resL α) β ≠ none)).card ≤ dL
      exact (card_filter_mem_le _ _).trans ((card_filter_inspectResidual_le _ S).trans (hL α))
    | [α, β] =>
      show (S.filter (· ∈ S.filter fun γ =>
        inspectResidual (resM α β) γ ≠ none)).card ≤ dM
      exact (card_filter_mem_le _ _).trans ((card_filter_inspectResidual_le _ S).trans (hM α β))
    | _ :: _ :: _ :: _ => simp [ahpBad, b]
  have := card_hits_le S (ahpBad S resR resL resM) b hb 3 []
  simpa [b, sum_range_succ, add_assoc] using this

end Varuna