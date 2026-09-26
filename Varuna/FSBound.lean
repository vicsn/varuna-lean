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

open Finset

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

end Varuna