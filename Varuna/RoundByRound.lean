/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchFS

/-!
# Round-by-round knowledge soundness

The state-function definition of round-by-round soundness (Canetti, Chen, Holmgren,
Lombardi, Rothblum, Rothblum, Wichs 2019), with the extractor of round-by-round
knowledge soundness (Chiesa, Manohar, Spooner 2019), counted over a challenge set `S`
with one squeezed element per challenge. The history of an element is the rounds
before it, its own round cut at it.

A verifier has round-by-round knowledge error `b / | S | ` for a relation
(`RBRKnowledge`) if a state function marks histories doomed so that the empty history
is doomed, a prover message keeps a history doomed, from a doomed history whose
extraction fails at most `b` elements of `S` lead to one that is not, and the verifier
rejects doomed transcripts. `RBRKnowledge.fs_charge` is Fiat–Shamir for such a
verifier : at most `Q · b · | S | ^{Q-1}` of the ` | S | ^Q` tapes give an accepted output
from none of whose histories the extractor reads a witness. `V3Batch.rbrKnowledge` is
the V3 batch as an instance, and `V3Batch.rbr_soundness` the count it gives.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Elements and their histories -/

/-- Some squeezed element of `rs` satisfies `p` with its history. -/
def SomeElem (p : List (Round F) → F → Prop) (rs : List (Round F)) : Prop :=
  ∃ pre m a post, rs = pre ++ (m, a) :: post ∧
    ∃ j, ∃ hj : j < a.length, p (pre ++ [(m, a.take j)]) a[j]

theorem not_someElem_nil (p : List (Round F) → F → Prop) : ¬SomeElem p [] := by
  rintro ⟨pre, m, a, post, h, -⟩
  simp at h

theorem split_append_singleton {rs pre post : List (Round F)} {r q : Round F}
    (h : rs ++ [r] = pre ++ q :: post) : (pre = rs ∧ q = r ∧ post = []) ∨
      ∃ post', post = post' ++ [r] ∧ rs = pre ++ q :: post' := by
  rcases List.eq_nil_or_concat post with rfl | ⟨post', y, rfl⟩
  · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact Or.inl ⟨h1.symm, (List.singleton_inj.1 h2).symm, rfl⟩
  · have h' : rs ++ [r] = (pre ++ q :: post') ++ [y] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    obtain rfl := List.singleton_inj.1 h2
    exact Or.inr ⟨post', by simp, h1⟩

/-- A message with no elements adds no element. -/
theorem someElem_append_empty (p : List (Round F) → F → Prop) (rs : List (Round F))
    (m : FSMessage F) : SomeElem p (rs ++ [(m, [])]) ↔ SomeElem p rs := by
  constructor
  · rintro ⟨pre, m', a, post, h, j, hj, hp⟩
    rcases split_append_singleton h with ⟨rfl, hq, rfl⟩ | ⟨post', rfl, hrs⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      simp at hj
    · exact ⟨pre, m', a, post', hrs, j, hj, hp⟩
  · rintro ⟨pre, m', a, post, rfl, j, hj, hp⟩
    exact ⟨pre, m', a, post ++ [(m, [])], by simp, j, hj, hp⟩

/-- A new element is the only element its squeeze adds. -/
theorem someElem_snoc (p : List (Round F) → F → Prop) (pre : List (Round F)) (m : FSMessage F)
    (a : List F) (x : F) : SomeElem p (pre ++ [(m, a ++ [x])]) ↔
      SomeElem p (pre ++ [(m, a)]) ∨ p (pre ++ [(m, a)]) x := by
  constructor
  · rintro ⟨pre', m', a', post, h, j, hj, hp⟩
    rcases split_append_singleton h with ⟨rfl, hq, rfl⟩ | ⟨post', rfl, hrs⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      rcases Nat.lt_or_ge j a.length with hj' | hj'
      · refine Or.inl ⟨pre', m', a, [], rfl, j, hj', ?_⟩
        simpa [List.take_append_of_le_length hj'.le, List.getElem_append_left hj'] using hp
      · obtain rfl : j = a.length := by simp at hj; omega
        exact Or.inr (by simpa using hp)
    · exact Or.inl ⟨pre', m', a', post' ++ [(m, a)], by rw [hrs]; simp, j, hj, hp⟩
  · rintro (⟨pre', m', a', post, h, j, hj, hp⟩ | hp)
    · rcases split_append_singleton h with ⟨rfl, hq, rfl⟩ | ⟨post', rfl, hrs⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
        refine ⟨pre', m', a' ++ [x], [], rfl, j, by simp; omega, ?_⟩
        simpa [List.take_append_of_le_length hj.le, List.getElem_append_left hj] using hp
      · exact ⟨pre', m', a', post' ++ [(m, a ++ [x])], by rw [hrs]; simp, j, hj, hp⟩
    · exact ⟨pre, m, a ++ [x], [], rfl, a.length, by simp, by simpa using hp⟩

/-- `rs` with `x` squeezed after its last message. -/
def snocElem (rs : List (Round F)) (x : F) : List (Round F) :=
  match rs.getLast? with
  | some (m, a) => rs.dropLast ++ [(m, a ++ [x])]
  | none => []

theorem snocElem_append (pre : List (Round F)) (m : FSMessage F) (a : List F) (x : F) :
    snocElem (pre ++ [(m, a)]) x = pre ++ [(m, a ++ [x])] := by
  simp [snocElem]

/-! ## The definition -/

open Classical in
/-- Round-by-round knowledge soundness of the verifier `accepts` for the relation
`rel`, with at most `b` elements of `S` escaping each doomed step : knowledge error
`b / | S | ` per squeezed element. -/
structure RBRKnowledge {Stmt W : Type*} (accepts : Stmt → List (Round F) → Prop)
    (rel : Stmt → W → Prop) (S : Finset F) (b : ℕ) where
  /-- The state function. -/
  doomed : Stmt → List (Round F) → Prop
  /-- The witness read off a history. -/
  extract : Stmt → List (Round F) → W
  start : ∀ s, doomed s []
  absorb : ∀ s rs m, doomed s rs → doomed s (rs ++ [(m, [])])
  squeeze : ∀ s pre m a, doomed s (pre ++ [(m, a)]) → ¬rel s (extract s (pre ++ [(m, a)])) →
    (S.filter fun x => ¬doomed s (pre ++ [(m, a ++ [x])])).card ≤ b
  reject : ∀ s rs, doomed s rs → ¬accepts s rs

namespace RBRKnowledge

variable {Stmt W : Type*} {accepts : Stmt → List (Round F) → Prop} {rel : Stmt → W → Prop}
  {S : Finset F} {b : ℕ} (P : RBRKnowledge accepts rel S b)

/-- Some history of an element of `rs` extracts a witness. -/
def Extracts (s : Stmt) (rs : List (Round F)) : Prop :=
  SomeElem (fun h _ => rel s (P.extract s h)) rs

open Classical in
/-- The elements that leave a doomed history whose extraction fails. -/
noncomputable def bad (s : Stmt) (h : List (Round F)) : Finset F :=
  if P.doomed s h ∧ ¬rel s (P.extract s h) then S.filter fun x => ¬P.doomed s (snocElem h x)
  else ∅

theorem card_bad_le (s : Stmt) (h : List (Round F)) : (S.filter (· ∈ P.bad s h)).card ≤ b := by
  refine (card_filter_mem_le _ _).trans ?_
  unfold bad
  split_ifs with hd
  · cases hl : h.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff.1 hl]
      simp [snocElem, P.start]
    | some r =>
      obtain ⟨m, a⟩ := r
      obtain ⟨pre, rfl⟩ : ∃ pre, h = pre ++ [(m, a)] :=
        ⟨_, (List.dropLast_append_getLast? _ hl).symm⟩
      refine le_of_eq_of_le ?_ (P.squeeze s pre m a hd.1 hd.2)
      congr 1
      ext x
      simp only [mem_filter, snocElem_append]
  · simp

/-- A history is doomed if none of its elements is outside `S`, extracts, or lands in
the bad set of its history. -/
theorem doomed_of_not_someElem (s : Stmt) (rs : List (Round F))
    (h : ¬SomeElem (fun h x => x ∉ S ∨ rel s (P.extract s h) ∨ x ∈ P.bad s h) rs) :
    P.doomed s rs := by
  classical
  induction rs using List.reverseRecOn with
  | nil => exact P.start s
  | append_singleton rs r ih =>
    obtain ⟨m, a⟩ := r
    induction a using List.reverseRecOn with
    | nil =>
      rw [someElem_append_empty] at h
      exact P.absorb s rs m (ih h)
    | append_singleton a x iha =>
      rw [someElem_snoc, not_or] at h
      have hd := iha h.1
      simp only [not_or, not_not] at h
      obtain ⟨-, hxS, hrel, hbad⟩ := h
      unfold bad at hbad
      rw [if_pos ⟨hd, hrel⟩, mem_filter, snocElem_append] at hbad
      by_contra hnd
      exact hbad ⟨hxS, hnd⟩

/-- Fiat–Shamir of a round-by-round knowledge-sound verifier. Let the statement
encoding followed by rounds decode uniquely. If on the tapes of an event `E` every
squeezed element of the output was answered on one of the adversary's `Q` queries,
and the output is accepted with no history extracting a witness, at most
`Q · b · | S | ^{Q-1}` tapes yield `E`. -/
theorem fs_charge (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (hinj : ∀ s s' rs rs', WF s → WF s' → NoLoneField rs → NoLoneField rs' →
      enc s ++ encodeRounds rs = enc s' ++ encodeRounds rs' → s = s' ∧ rs = rs')
    (A : FSAdversary F) (Q : ℕ) (stmt : List F → Stmt) (rounds : List F → List (Round F))
    (E : List F → Prop) [DecidablePred E]
    (hcons : ∀ tape ∈ tapes S Q, E tape →
      RoundsFromQueries A tape (enc (stmt tape)) (rounds tape))
    (hE : ∀ tape ∈ tapes S Q, E tape → WF (stmt tape) ∧ NoLoneField (rounds tape) ∧
      accepts (stmt tape) (rounds tape) ∧ ¬P.Extracts (stmt tape) (rounds tape)) :
    ((tapes S Q).filter E).card ≤ Q * b * S.card ^ (Q - 1) := by
  refine fs_rounds_charge enc WF hinj S A P.bad b P.card_bad_le Q stmt rounds E hcons
    fun tape h he => ?_
  obtain ⟨hwf, hnl, hacc, hext⟩ := hE tape h he
  refine ⟨hwf, hnl, ?_⟩
  by_contra hnb
  refine P.reject _ _ (P.doomed_of_not_someElem _ _ ?_) hacc
  rintro ⟨pre, m, a, post, hrs, j, hj, hp | hp | hp⟩
  · obtain ⟨i, hi, -, hx⟩ := hcons tape h he pre m a post hrs j hj
    exact hp (hx ▸ (mem_tapes h).2 _ (List.getElem_mem hi))
  · exact hext ⟨pre, m, a, post, hrs, j, hj, hp⟩
  · exact hnb ⟨pre, m, a, post, hrs, j, hj, hp⟩

end RBRKnowledge

/-! ## The V3 batch -/

namespace V3Batch

theorem holds_init {P : V3Batch F} {t t' : V2Transcript F} (h : t.init = t'.init) :
    P.Holds t ↔ P.Holds t' := by
  simp only [Holds, h]

theorem holds_absorbed (P : V3Batch F) (t : V2Transcript F) {k : ℕ} (hk : 1 ≤ k) :
    (P.absorbed k).Holds t ↔ P.Holds t := by
  have hst : (P.absorbed k).statement = P.statement := by
    simp [absorbed, upTo, withChallenges, statement, BatchCircuit.upTo, BatchInstance.upTo,
      Function.comp_def]
  have he : (P.absorbed k).e = P.e := by
    simp [absorbed, upTo, withChallenges, e, hk]
  have hi : (P.absorbed k).instances = P.instances.map fun p => (p.1.upTo k, p.2.upTo k) := by
    rw [absorbed, instances_upTo]
    rfl
  simp only [Holds, hst, he, hi, List.forall_mem_map]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun p _ => ?_))
  rw [BatchCircuit.zhat_upTo _ _ hk]
  rfl

/-- The V3 verifier on rounds : they are a transcript's rounds, the transcript opens
with the statement, and the checks accept a batch that `ext` reads off its messages,
with its residuals of degree at most `b`. -/
def RBRAccepts (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F) (b : ℕ)
    (s : V3Stmt F) (rs : List (Round F)) : Prop :=
  ∃ (t : V2Transcript F) (chal : V2Challenge → List F) (B : V3Batch F), rs = t.rounds chal ∧
    t.init = v3Init s.1 s.2 ∧ ExtractsBefore ext s t B ∧
    (B.withChallenges chal).Accepts S t chal s.2 ∧
    (B.withChallenges chal).ResidualsBounded chal b

/-- The batch relation at a statement, on every transcript that opens with it. -/
def RBRRel (s : V3Stmt F) (P : V3Batch F) : Prop :=
  ∀ t : V2Transcript F, t.init = v3Init s.1 s.2 → P.Holds t

/-- No element so far extracts a witness or lands in the batch bad set of its history. -/
def RBRDoomed (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F) (b : ℕ)
    (s : V3Stmt F) (h : List (Round F)) : Prop :=
  ¬SomeElem (fun h' x => RBRRel s (ext s (h'.map Prod.fst)) ∨ x ∈ batchBad ext S b s h') h

/-- The V3 batch is round-by-round knowledge sound with error `b / | S | `, the
extractor reading the batch off a history's messages. -/
noncomputable def rbrKnowledge (ext : V3Stmt F → List (FSMessage F) → V3Batch F)
    (S : Finset F) {b : ℕ} (hb : 1 ≤ b) : RBRKnowledge (RBRAccepts ext S b) RBRRel S b where
  doomed := RBRDoomed ext S b
  extract s h := ext s (h.map Prod.fst)
  start _ := not_someElem_nil _
  absorb s rs m h := by
    rw [RBRDoomed, someElem_append_empty]
    exact h
  squeeze s pre m a hd hrel := by
    classical
    refine (card_le_card fun x hx => ?_).trans (card_batchBad_le ext S b s (pre ++ [(m, a)]))
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h := hx.2
    rw [RBRDoomed, not_not, someElem_snoc] at h
    rcases h with h | h | h
    · exact (hd h).elim
    · exact (hrel h).elim
    · exact h
  reject s rs hd := by
    rintro ⟨t, chal, B, rfl, hinit, hB, hacc, hres⟩
    apply hd
    by_cases hbr : outputBreaks (prefixBad t (B.badAt S chal)) t chal = true
    · obtain ⟨pre, m, a, post, hrs, j, hj, hx⟩ :=
        roundsBreak_of_outputBreaks hB hacc.msg S hb hres hbr
      exact ⟨pre, m, a, post, hrs, j, hj, Or.inr hx⟩
    · have hh := holds_of_accepts hacc (Bool.eq_false_iff.mpr hbr)
      refine ⟨_, _, _, _, t.rounds_split chal .alpha, 0, by simp [hacc.alpha], Or.inl ?_⟩
      intro t' ht'
      have hm := t.map_fst_history chal .alpha 0
      simp only [V2Transcript.history] at hm
      rw [hm, ← holds_absorbed _ _ (by decide : 1 ≤ V2Challenge.alpha.prefixAbsorbs), ← hB,
        holds_absorbed _ _ (by decide), holds_init (ht'.trans hinit.symm)]
      exact hh

/-- Fiat–Shamir soundness of the V3 batch through its round-by-round knowledge
soundness. If on the tapes of an event `E` every squeezed element of the output was
answered on one of the adversary's `Q` queries, and the output is accepted with no
history extracting a witness, at most `Q · b · | S | ^{Q-1}` tapes yield `E`. -/
theorem rbr_soundness (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F)
    {b : ℕ} (hb : 1 ≤ b) (A : FSAdversary F) (Q : ℕ) (stmt : List F → V3Stmt F)
    (rounds : List F → List (Round F)) (E : List F → Prop) [DecidablePred E]
    (hcons : ∀ tape ∈ tapes S Q, E tape →
      RoundsFromQueries A tape (v3Init (stmt tape).1 (stmt tape).2) (rounds tape))
    (hE : ∀ tape ∈ tapes S Q, E tape → V3StmtWF (stmt tape) ∧
      RBRAccepts ext S b (stmt tape) (rounds tape) ∧
      ¬(rbrKnowledge ext S hb).Extracts (stmt tape) (rounds tape)) :
    ((tapes S Q).filter E).card ≤ Q * b * S.card ^ (Q - 1) := by
  refine (rbrKnowledge ext S hb).fs_charge (fun s => v3Init s.1 s.2) V3StmtWF
    (fun _ _ _ _ hs hs' hr hr' h => v3Init_rounds_inj hs hs' hr hr' h) A Q stmt rounds E hcons
    fun tape h he => ?_
  obtain ⟨hwf, hacc, hext⟩ := hE tape h he
  refine ⟨hwf, ?_, hacc, hext⟩
  obtain ⟨t, chal, B, hrs, -, -, hacc', -⟩ := hacc
  exact hrs ▸ V2Transcript.noLoneField_rounds hacc'.msg chal

end V3Batch

end Varuna