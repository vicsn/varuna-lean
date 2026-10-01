/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Probability

/-!
# Fiat–Shamir : charging the adversary per oracle query

The random oracle is lazily sampled : the adversary's `i`-th query is
answered with the `i`-th entry of a uniformly random tape in `S^Q`.
Queries are fresh (a repeated query gets its earlier answer, so an
adversary gains nothing by repeating one). The adversary is deterministic
given the answers so far.

Round-by-round soundness supplies, for each query prefix, the bad
challenges that would let a prover out of a doomed state (for Varuna, the
roots of the residual the prefix determines, or the one lucky combiner;
see `Probability.lean`). If each query has at most `b` bad answers in `S`,
at most `Q · b · | S | ^{Q-1}` of the ` | S | ^Q` tapes let the adversary hit one
(`fs_query_charge`): knowledge error `Q · b / | S | `, as in Ironwood.

`fs_break_count` connects that bound to the V2 transcript : if every
challenge of the adversary's output was answered on one of its queries, an
output with a break at any challenge is a hit.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-- A deterministic Fiat–Shamir adversary: its next query given the answers so far. -/
structure FSAdversary (F : Type*) where
  /-- Next query prefix. -/
  query : List F → Transcript F

/-- Some answer on the tape lands in the bad set of the query it answers. -/
def fsHits (A : FSAdversary F) (Bad : Transcript F → Finset F) (tape : List F) : Bool :=
  hitsB (fun pre => Bad (A.query pre)) [] tape

/-- Query charging. With at most `b` bad answers per query, at most
`Q · b · | S | ^{Q-1}` of the ` | S | ^Q` oracle tapes produce a hit. -/
theorem fs_query_charge (S : Finset F) (A : FSAdversary F) (Bad : Transcript F → Finset F)
    (b : ℕ) (hb : ∀ t, (S.filter (· ∈ Bad t)).card ≤ b) (Q : ℕ) :
    ((tapes S Q).filter fun tape => fsHits A Bad tape = true).card ≤ Q * b * S.card ^ (Q - 1) :=
      by
  have := card_hits_le S (fun pre => Bad (A.query pre)) (fun _ => b) (fun pre => hb _) Q []
  simp only [sum_const, card_range, smul_eq_mul] at this
  unfold fsHits
  convert this using 2

/-- The challenge `ch` for prefix `pre` is the answer to one of the adversary's queries. -/
def ChallengeFromQuery (A : FSAdversary F) (tape : List F) (pre : Transcript F) (ch : F) : Prop :=
  ∃ i, ∃ h : i < tape.length, A.query (tape.take i) = pre ∧ tape[i] = ch

/-- A bad challenge that was answered on a query is a hit. -/
theorem fsHits_of_bad (A : FSAdversary F) (Bad : Transcript F → Finset F) {tape : List F}
    {pre : Transcript F} {ch : F} (hq : ChallengeFromQuery A tape pre ch) (hbad : ch ∈ Bad pre) :
    fsHits A Bad tape = true := by
  obtain ⟨i, hi, hpre, hch⟩ := hq
  rw [fsHits, hitsB_iff]
  refine ⟨i, hi, ?_⟩
  rw [List.nil_append, hpre, hch]
  exact hbad

/-- The six V2 squeezes, in order. -/
def v2Challenges : List V2Challenge :=
  [.firstCombiners, .alpha, .prepareThird, .beta, .deltas, .gamma]

/-- Whether the output transcript has a bad challenge at some V2 squeeze. -/
def outputBreaks (Bad : Transcript F → Finset F) (t : V2Transcript F) (chal : V2Challenge → F) :
    Bool :=
  v2Challenges.any fun c => decide (chal c ∈ Bad (t.before c))

/-- Fiat–Shamir knowledge error for V2, counting form. If every challenge of the
output transcript was answered on one of the adversary's `Q` queries, at most
`Q · b · | S | ^{Q-1}` tapes yield an output with a break at any squeeze. -/
theorem fs_break_count (S : Finset F) (A : FSAdversary F) (Bad : Transcript F → Finset F) (b : ℕ)
    (hb : ∀ t, (S.filter (· ∈ Bad t)).card ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → F)
    (hcons : ∀ tape ∈ tapes S Q, ∀ c, ChallengeFromQuery A tape ((out tape).before c) (chal tape c)) :
    ((tapes S Q).filter fun tape => outputBreaks Bad (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) := by
  refine (card_le_card fun tape htape => ?_).trans (fs_query_charge S A Bad b hb Q)
  obtain ⟨hmem, hbr⟩ := mem_filter.mp htape
  obtain ⟨c, _, hc⟩ := List.any_eq_true.mp hbr
  exact mem_filter.mpr ⟨hmem, fsHits_of_bad A Bad (hcons tape hmem c) (of_decide_eq_true hc)⟩

/-- Distinct absorb prefixes, so a transcript prefix names at most one squeeze. -/
theorem before_injective (t : V2Transcript F) : Function.Injective t.before := by
  intro c₁ c₂ h
  have hlen := congrArg List.length h
  rw [before_length, before_length] at hlen
  cases c₁ <;> cases c₂ <;> first | rfl | simp [V2Challenge.prefixAbsorbs] at hlen

theorem before_ne (t : V2Transcript F) {c₁ c₂ : V2Challenge} (h : c₁ ≠ c₂) :
    t.before c₁ ≠ t.before c₂ :=
  fun heq => h (before_injective t heq)

/-- Bad answers at each V2 squeeze, read off the residuals and the one-weight
batches that squeeze determines. `α`, `β`, `γ` are Schwartz–Zippel roots.
The three combiner squeezes are the single root of `a + η b = 0` on a live claim. -/
noncomputable def squeezeBad (S : Finset F) (resα resβ resγ : F[X])
    (aη bη aδ bδ aν bν : F) : V2Challenge → Finset F
  | .alpha => S.filter (· ∈ szBadSet resα)
  | .beta => S.filter (· ∈ szBadSet resβ)
  | .gamma => S.filter (· ∈ szBadSet resγ)
  | .prepareThird => S.filter fun η => inspectBatch [1, η] [aη, bη] ≠ none
  | .deltas => S.filter fun δ => inspectBatch [1, δ] [aδ, bδ] ≠ none
  | .firstCombiners => S.filter fun ν => inspectBatch [1, ν] [aν, bν] ≠ none

/-- Every squeeze's bad set has size at most `max(deg resα, deg resβ, deg resγ, 1)`. -/
theorem squeezeBad_card (S : Finset F) (resα resβ resγ : F[X])
    (aη bη aδ bδ aν bν : F) {b : ℕ}
    (hα : resα.natDegree ≤ b) (hβ : resβ.natDegree ≤ b) (hγ : resγ.natDegree ≤ b)
    (hb : 1 ≤ b) :
    ∀ c, (squeezeBad S resα resβ resγ aη bη aδ bδ aν bν c).card ≤ b := by
  intro c
  cases c with
  | alpha =>
    exact (card_filter_mem_le _ _).trans ((card_szBadSet_le_natDegree resα).trans hα)
  | beta =>
    exact (card_filter_mem_le _ _).trans ((card_szBadSet_le_natDegree resβ).trans hβ)
  | gamma =>
    exact (card_filter_mem_le _ _).trans ((card_szBadSet_le_natDegree resγ).trans hγ)
  | prepareThird => exact (card_filter_inspectBatch_pair aη bη S).trans hb
  | deltas => exact (card_filter_inspectBatch_pair aδ bδ S).trans hb
  | firstCombiners => exact (card_filter_inspectBatch_pair aν bν S).trans hb

/-- Outside a squeeze's Schwartz–Zippel set, an accepting evaluation is a zero residual. -/
theorem squeeze_safe_residual {res : F[X]} {α : F} (hα : α ∉ szBadSet res)
    (hacc : res.eval α = 0) : inspectResidual res α = none := by
  have h0 : res = 0 := by
    by_contra hne
    exact eval_ne_zero_of_notMem_szBadSet hne hα hacc
  exact inspectResidual_eq_none_of_zero h0

/-- The bad set of a query is the bad set of the squeeze whose prefix it is.
A prefix that is none of the six squeezes contributes nothing. -/
noncomputable def prefixBad (t : V2Transcript F) (Bad : V2Challenge → Finset F)
    (pre : Transcript F) : Finset F :=
  if t.before .firstCombiners = pre then Bad .firstCombiners
  else if t.before .alpha = pre then Bad .alpha
  else if t.before .prepareThird = pre then Bad .prepareThird
  else if t.before .beta = pre then Bad .beta
  else if t.before .deltas = pre then Bad .deltas
  else if t.before .gamma = pre then Bad .gamma
  else ∅

theorem prefixBad_before (t : V2Transcript F) (Bad : V2Challenge → Finset F) (c : V2Challenge) :
    prefixBad t Bad (t.before c) = Bad c := by
  cases c with
  | firstCombiners => simp [prefixBad]
  | alpha =>
    simp only [prefixBad]
    rw [if_neg (before_ne t (by decide : V2Challenge.firstCombiners ≠ .alpha))]
    rw [if_true]
  | prepareThird =>
    simp only [prefixBad]
    rw [if_neg (before_ne t (by decide : V2Challenge.firstCombiners ≠ .prepareThird))]
    rw [if_neg (before_ne t (by decide : V2Challenge.alpha ≠ .prepareThird))]
    rw [if_true]
  | beta =>
    simp only [prefixBad]
    rw [if_neg (before_ne t (by decide : V2Challenge.firstCombiners ≠ .beta))]
    rw [if_neg (before_ne t (by decide : V2Challenge.alpha ≠ .beta))]
    rw [if_neg (before_ne t (by decide : V2Challenge.prepareThird ≠ .beta))]
    rw [if_true]
  | deltas =>
    simp only [prefixBad]
    rw [if_neg (before_ne t (by decide : V2Challenge.firstCombiners ≠ .deltas))]
    rw [if_neg (before_ne t (by decide : V2Challenge.alpha ≠ .deltas))]
    rw [if_neg (before_ne t (by decide : V2Challenge.prepareThird ≠ .deltas))]
    rw [if_neg (before_ne t (by decide : V2Challenge.beta ≠ .deltas))]
    rw [if_true]
  | gamma =>
    simp only [prefixBad]
    rw [if_neg (before_ne t (by decide : V2Challenge.firstCombiners ≠ .gamma))]
    rw [if_neg (before_ne t (by decide : V2Challenge.alpha ≠ .gamma))]
    rw [if_neg (before_ne t (by decide : V2Challenge.prepareThird ≠ .gamma))]
    rw [if_neg (before_ne t (by decide : V2Challenge.beta ≠ .gamma))]
    rw [if_neg (before_ne t (by decide : V2Challenge.deltas ≠ .gamma))]
    rw [if_true]

/-- A challenge outside its squeeze's bad set is outside the prefix bad set. -/
theorem not_mem_prefixBad_of_not_mem {t : V2Transcript F} {Bad : V2Challenge → Finset F}
    {c : V2Challenge} {x : F} (hx : x ∉ Bad c) :
    x ∉ prefixBad t Bad (t.before c) := by
  rw [prefixBad_before]
  exact hx

/-- Query charging for the six V2 squeezes. `squeezeBad_card` supplies `b`. -/
theorem fs_squeeze_charge (S : Finset F) (A : FSAdversary F) (t : V2Transcript F)
    (Bad : V2Challenge → Finset F) (b : ℕ)
    (hb : ∀ c, (S.filter (· ∈ Bad c)).card ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → F)
    (hcons : ∀ tape ∈ tapes S Q, ∀ c,
      ChallengeFromQuery A tape ((out tape).before c) (chal tape c)) :
    ((tapes S Q).filter fun tape =>
      outputBreaks (prefixBad t Bad) (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) := by
  have hcard : ∀ pre, (S.filter (· ∈ prefixBad t Bad pre)).card ≤ b := by
    intro pre
    unfold prefixBad
    split_ifs
    · exact hb .firstCombiners
    · exact hb .alpha
    · exact hb .prepareThird
    · exact hb .beta
    · exact hb .deltas
    · exact hb .gamma
    · simp
  exact fs_break_count S A (prefixBad t Bad) b hcard Q out chal hcons

/-- The six V2 squeezes, with bad sets read off the residuals and the
one-weight batches, charged as one query-bounded break count. -/
theorem fs_v2_squeeze_charge (S : Finset F) (A : FSAdversary F) (t : V2Transcript F)
    (resα resβ resγ : F[X]) (aη bη aδ bδ aν bν : F) {b : ℕ}
    (hα : resα.natDegree ≤ b) (hβ : resβ.natDegree ≤ b) (hγ : resγ.natDegree ≤ b)
    (hb : 1 ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → F)
    (hcons : ∀ tape ∈ tapes S Q, ∀ c,
      ChallengeFromQuery A tape ((out tape).before c) (chal tape c)) :
    ((tapes S Q).filter fun tape =>
      outputBreaks (prefixBad t (squeezeBad S resα resβ resγ aη bη aδ bδ aν bν))
        (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) := by
  refine fs_squeeze_charge S A t (squeezeBad S resα resβ resγ aη bη aδ bδ aν bν) b ?_ Q out chal hcons
  intro c
  exact (card_filter_mem_le _ _).trans
    (squeezeBad_card S resα resβ resγ aη bη aδ bδ aν bν hα hβ hγ hb c)

end Varuna