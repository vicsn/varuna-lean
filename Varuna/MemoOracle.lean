/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AdaptiveFS

/-!
# A random oracle with memory, and the verifier's queries

`fs_query_charge` answers the adversary's `i`-th query with the `i`-th tape entry,
so a repeated query gets a fresh answer, and `fs_rounds_charge` takes as a
hypothesis that every squeezed element of the output was answered on one of the
queries (`RoundsFromQueries`). A random function answers a repeated query with its
earlier answer, and the verifier recomputes every challenge with queries of its own.

`memoRun` runs a query strategy against the memoized oracle : a query already in
the log gets its logged answer, a new query the next unused tape entry. The new
queries form an `FSAdversary` (`memoAdversary`) : the `k`-th is a function of the
first `k` tape entries, and every logged answer was given on one of them
(`challengeFromQuery_of_mem`).

`withVerifier` runs the verifier after the adversary's `Q` queries. The verifier
squeezes the elements of the rounds the adversary's log fixes, one query per
element at the statement followed by the element's history (`nextQuery`), and
reads each element off the answer (`fillRounds`). With as many verifier queries as
elements, every element of the rounds it reads was answered on one of the `Q + V`
new queries (`roundsFromQueries_runLog`), which is the hypothesis of
`fs_rounds_charge`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The memoized oracle -/

/-- Queries with their answers, in order. -/
abbrev QueryLog (F : Type*) := List (Transcript F × F)

/-- The first logged answer to `q`. -/
def QueryLog.lookup (log : QueryLog F) (q : Transcript F) : Option F :=
  (log.find? fun e => e.1 = q).map Prod.snd

theorem QueryLog.mem_of_lookup {log : QueryLog F} {q : Transcript F} {a : F}
    (h : log.lookup q = some a) : (q, a) ∈ log := by
  unfold QueryLog.lookup at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hq : e.1 = q := by simpa using List.find?_some he
  rw [← hq]
  exact List.mem_of_find?_eq_some he

/-- Run `n` queries of `next` against the memoized oracle, from `log`. A logged
query gets its logged answer, a new one the next entry of `tape`. If the tape runs
out, stop with the new query it could not answer. -/
def memoRun (next : QueryLog F → Transcript F) :
    ℕ → QueryLog F → List F → QueryLog F × Option (Transcript F)
  | 0, log, _ => (log, none)
  | n + 1, log, tape =>
    match log.lookup (next log), tape with
    | some a, tape => memoRun next n (log ++ [(next log, a)]) tape
    | none, [] => (log, some (next log))
    | none, a :: tape => memoRun next n (log ++ [(next log, a)]) tape

/-- The new queries of `n` steps of `next` : the query `memoRun` stops at once the
answers `pre` are used up. -/
def memoAdversary (next : QueryLog F → Transcript F) (n : ℕ) : FSAdversary F :=
  ⟨fun pre => ((memoRun next n [] pre).2).getD []⟩

/-- Every entry of the log was there at the start, or is a new query with the tape
entry that answered it : the `k`-th new query, asked once `k` entries are used. -/
theorem mem_memoRun (next : QueryLog F → Transcript F) :
    ∀ (n : ℕ) (log : QueryLog F) (tape : List F) {e : Transcript F × F},
      e ∈ (memoRun next n log tape).1 → e ∈ log ∨
        ∃ k, ∃ hk : k < tape.length,
          (memoRun next n log (tape.take k)).2 = some e.1 ∧ tape[k] = e.2
  | 0, log, tape, e, he => Or.inl he
  | n + 1, log, tape, e, he => by
    cases hl : log.lookup (next log) with
    | some a =>
      have he' : e ∈ (memoRun next n (log ++ [(next log, a)]) tape).1 := by
        simpa [memoRun, hl] using he
      rcases mem_memoRun next n _ tape he' with h | ⟨k, hk, hq, ha⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.mp h]
          exact Or.inl (QueryLog.mem_of_lookup hl)
      · exact Or.inr ⟨k, hk, by simpa [memoRun, hl] using hq, ha⟩
    | none =>
      cases tape with
      | nil => exact Or.inl (by simpa [memoRun, hl] using he)
      | cons a tape =>
        have he' : e ∈ (memoRun next n (log ++ [(next log, a)]) tape).1 := by
          simpa [memoRun, hl] using he
        rcases mem_memoRun next n _ tape he' with h | ⟨k, hk, hq, ha⟩
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton.mp h]
            exact Or.inr ⟨0, by simp, by simp [memoRun, hl], rfl⟩
        · exact Or.inr ⟨k + 1, by simpa using hk, by simpa [memoRun, hl] using hq,
            by simpa using ha⟩

/-- Every logged answer was given on one of the new queries. -/
theorem challengeFromQuery_of_mem (next : QueryLog F → Transcript F) (n : ℕ)
    (tape : List F) {q : Transcript F} {a : F} (h : (q, a) ∈ (memoRun next n [] tape).1) :
    ChallengeFromQuery (memoAdversary next n) tape q a := by
  rcases mem_memoRun next n [] tape h with h | ⟨k, hk, hq, ha⟩
  · simp at h
  · exact ⟨k, hk, by simp [memoAdversary, hq], ha⟩

theorem prefix_memoRun (next : QueryLog F → Transcript F) :
    ∀ (n : ℕ) (log : QueryLog F) (tape : List F), List.IsPrefix log (memoRun next n log tape).1
  | 0, log, tape => List.prefix_refl log
  | n + 1, log, tape => by
    cases hl : log.lookup (next log) with
    | some a =>
      simpa [memoRun, hl] using
        (List.prefix_append log _).trans (prefix_memoRun next n (log ++ [(next log, a)]) tape)
    | none =>
      cases tape with
      | nil => simp [memoRun, hl]
      | cons a tape =>
        simpa [memoRun, hl] using
          (List.prefix_append log _).trans (prefix_memoRun next n (log ++ [(next log, a)]) tape)

/-- With at least `n` tape entries, `n` steps log `n` queries. -/
theorem length_memoRun (next : QueryLog F → Transcript F) :
    ∀ (n : ℕ) (log : QueryLog F) (tape : List F), n ≤ tape.length →
      (memoRun next n log tape).1.length = log.length + n
  | 0, log, tape, _ => rfl
  | n + 1, log, tape, hn => by
    cases hl : log.lookup (next log) with
    | some a =>
      have := length_memoRun next n (log ++ [(next log, a)]) tape (by omega)
      simp only [List.length_append, List.length_singleton] at this
      simp only [memoRun, hl]
      omega
    | none =>
      cases tape with
      | nil => simp at hn
      | cons a tape =>
        have := length_memoRun next n (log ++ [(next log, a)]) tape (by simpa using hn)
        simp only [List.length_append, List.length_singleton] at this
        simp only [memoRun, hl]
        omega

/-- The query logged at step `k` is `next` of the log before it. -/
theorem memoRun_getElem_fst (next : QueryLog F → Transcript F) :
    ∀ (n : ℕ) (log : QueryLog F) (tape : List F) (k : ℕ)
      (hk : k < (memoRun next n log tape).1.length), log.length ≤ k →
      ((memoRun next n log tape).1[k]).1 = next ((memoRun next n log tape).1.take k)
  | 0, log, tape, k, hk, hle => by simp [memoRun] at hk; omega
  | n + 1, log, tape, k, hk, hle => by
    have step : ∀ a tape', memoRun next (n + 1) log tape =
        memoRun next n (log ++ [(next log, a)]) tape' →
        ((memoRun next (n + 1) log tape).1[k]).1 =
          next ((memoRun next (n + 1) log tape).1.take k) := by
      intro a tape' heq
      simp only [heq] at hk ⊢
      rcases Nat.lt_or_ge k (log ++ [(next log, a)]).length with hlt | hge
      · have hk' : k = log.length := by simp at hlt; omega
        obtain ⟨rest, hrest⟩ := prefix_memoRun next n (log ++ [(next log, a)]) tape'
        simp only [← hrest, hk']
        simp
      · exact memoRun_getElem_fst next n _ tape' k hk hge
    cases hl : log.lookup (next log) with
    | some a => exact step a tape (by simp [memoRun, hl])
    | none =>
      cases tape with
      | nil => simp [memoRun, hl] at hk; omega
      | cons a tape => exact step a tape (by simp [memoRun, hl])

theorem getElem_fst_of_memoRun {next : QueryLog F → Transcript F} {n : ℕ} {log : QueryLog F}
    {tape : List F} {L : QueryLog F} (hL : (memoRun next n log tape).1 = L) {k : ℕ}
    (hk : k < L.length) (hle : log.length ≤ k) : L[k].1 = next (L.take k) := by
  subst hL
  exact memoRun_getElem_fst next n log tape k hk hle

/-! ## The verifier's queries -/

/-- The adversary's `Q` queries, then the verifier's : `vq` of the adversary's log and
the verifier's answers so far. -/
def withVerifier (next : QueryLog F → Transcript F) (Q : ℕ)
    (vq : QueryLog F → List F → Transcript F) (log : QueryLog F) : Transcript F :=
  if log.length < Q then next log else vq (log.take Q) ((log.drop Q).map Prod.snd)

/-- The log of the adversary's `Q` queries and the verifier's `V`. The adversary's log
is its first `Q` entries; the verifier's answers are the rest. -/
def runLog (next : QueryLog F → Transcript F) (Q : ℕ) (vq : QueryLog F → List F → Transcript F)
    (V : ℕ) (tape : List F) : QueryLog F :=
  (memoRun (withVerifier next Q vq) (Q + V) [] tape).1

theorem length_runLog (next : QueryLog F → Transcript F) (Q : ℕ)
    (vq : QueryLog F → List F → Transcript F) (V : ℕ) {tape : List F}
    (htape : tape.length = Q + V) : (runLog next Q vq V tape).length = Q + V := by
  rw [runLog, length_memoRun _ _ _ _ htape.ge, List.length_nil, zero_add]

/-- The verifier's `i`-th query, with the answer it got, is in the log. -/
theorem mem_runLog (next : QueryLog F → Transcript F) (Q : ℕ)
    (vq : QueryLog F → List F → Transcript F) (V : ℕ) (tape : List F) {L : QueryLog F}
    (hL : runLog next Q vq V tape = L) {i : ℕ} (hi : i < ((L.drop Q).map Prod.snd).length) :
    (vq (L.take Q) (((L.drop Q).map Prod.snd).take i), ((L.drop Q).map Prod.snd)[i]) ∈ L := by
  have hk : Q + i < L.length := by simp at hi; omega
  have hfst := getElem_fst_of_memoRun hL hk (Nat.zero_le _)
  have htake : (L.take (Q + i)).length = Q + i := by simp; omega
  rw [withVerifier, htake, if_neg (by omega), List.take_take, Nat.min_eq_left (by omega),
    List.drop_take, Nat.add_sub_cancel_left] at hfst
  have hans : ((L.drop Q).map Prod.snd)[i] = L[Q + i].2 := by simp
  rw [hans, ← List.map_take, ← hfst]
  exact List.getElem_mem hk

/-! ## The verifier's challenges -/

/-- The rounds of the messages `ms`, each with its count of the elements `ans`, in
order. -/
def fillRounds : List (FSMessage F × ℕ) → List F → List (Round F)
  | [], _ => []
  | (m, n) :: ms, ans => (m, ans.take n) :: fillRounds ms (ans.drop n)

/-- The verifier's query for its next element, after the rounds `pre`, with the
elements `ans` of the rounds `ms` so far : the statement `I`, the rounds before, then
the message and the elements of its round so far. -/
def nextQuery (I : Transcript F) :
    List (Round F) → List (FSMessage F × ℕ) → List F → Transcript F
  | _, [], _ => []
  | pre, (m, n) :: ms, ans =>
    if ans.length < n then I ++ encodeRounds (pre ++ [(m, ans)])
    else nextQuery I (pre ++ [(m, ans.take n)]) ms (ans.drop n)

/-- Each element of the rounds is the answer to the verifier's query at its history. -/
theorem nextQuery_fillRounds (I : Transcript F) :
    ∀ (pre : List (Round F)) (ms : List (FSMessage F × ℕ)) (ans : List F),
      (ms.map Prod.snd).sum ≤ ans.length →
      ∀ pre' m a post, fillRounds ms ans = pre' ++ (m, a) :: post → ∀ j (hj : j < a.length),
        ∃ k, ∃ hk : k < ans.length,
          nextQuery I pre ms (ans.take k) = I ++ encodeRounds (pre ++ pre' ++ [(m, a.take j)]) ∧
            ans[k] = a[j]
  | _, [], _, _, pre', _, _, _, h, _, _ => by simp [fillRounds] at h
  | pre, (m₀, n) :: ms, ans, hsum, [], m, a, post, h, j, hj => by
    simp only [fillRounds, List.nil_append, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    simp only [List.map_cons, List.sum_cons] at hsum
    simp only [List.length_take] at hj
    refine ⟨j, by omega, ?_, by simp⟩
    rw [nextQuery, if_pos (by simp; omega), List.take_take, Nat.min_eq_left (by omega),
      List.append_nil]
  | pre, (m₀, n) :: ms, ans, hsum, r :: pre', m, a, post, h, j, hj => by
    simp only [fillRounds, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.map_cons, List.sum_cons] at hsum
    obtain ⟨k, hk, hq, ha⟩ := nextQuery_fillRounds I (pre ++ [(m₀, ans.take n)]) ms
      (ans.drop n) (by simp; omega) pre' m a post h j hj
    simp only [List.length_drop] at hk
    refine ⟨n + k, by omega, ?_, by simpa using ha⟩
    rw [nextQuery, if_neg (by simp; omega), List.take_take, Nat.min_eq_left (by omega),
      List.drop_take, Nat.add_sub_cancel_left, hq]
    simp

/-- If the verifier asks, for each element of the rounds `ms` of the adversary's log,
the statement `I` followed by the element's history, and reads the element off the
answer, every element was answered on one of the new queries, provided the verifier
has as many queries as elements. -/
theorem roundsFromQueries_runLog (next : QueryLog F → Transcript F) (Q : ℕ)
    (vq : QueryLog F → List F → Transcript F) (V : ℕ) (I : QueryLog F → Transcript F)
    (ms : QueryLog F → List (FSMessage F × ℕ)) (hvq : ∀ log, vq log = nextQuery (I log) [] (ms log))
    (tape : List F) {L : QueryLog F} (hL : runLog next Q vq V tape = L)
    (hV : ((ms (L.take Q)).map Prod.snd).sum ≤ ((L.drop Q).map Prod.snd).length) :
    RoundsFromQueries (memoAdversary (withVerifier next Q vq) (Q + V)) tape (I (L.take Q))
      (fillRounds (ms (L.take Q)) ((L.drop Q).map Prod.snd)) := by
  intro pre m a post hrs j hj
  obtain ⟨k, hk, hq, ha⟩ := nextQuery_fillRounds (I (L.take Q)) [] _ _ hV pre m a post hrs j hj
  have hmem := mem_runLog next Q vq V tape hL hk
  rw [hvq, hq, ha, List.nil_append] at hmem
  apply challengeFromQuery_of_mem
  show _ ∈ runLog next Q vq V tape
  rw [hL]
  exact hmem

end Varuna