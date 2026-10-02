/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.FSBound
import Varuna.Statement

/-!
# Adaptive Fiat–Shamir : bad sets read off the query

`fs_break_count` charges bad sets fixed before the adversary runs. An adaptive
prover picks each message after seeing the challenges before it, so the bad set
at a squeeze is a function of everything absorbed and squeezed so far.

In the multi-round Fiat–Shamir transform each query carries that history : the
statement, then every round's message followed by the elements squeezed after
it (`encodeRounds`), as `squeezeN` already does within one squeeze
(`squeezeN_getElem_rounds`). The history decodes uniquely from the query
(`encodeRounds_injective`; for V3, `v3Init_rounds_inj`), so a bad set on
statements and histories is a bad set on queries (`queryBad`). `fs_query_charge`
then charges it per query (`fs_rounds_charge`) : at most `Q · b · | S | ^{Q-1}` of
the ` | S | ^Q` tapes let a squeezed element land in the bad set of its history.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Rounds -/

/-- A round : a prover message, then the elements squeezed after it. -/
abbrev Round (F : Type*) := FSMessage F × List F

/-- Rounds in absorb order : each message, then its squeezed elements as `field`s. -/
def encodeRounds : List (Round F) → Transcript F
  | [] => []
  | (m, a) :: rs => m :: (a.map FSMessage.field ++ encodeRounds rs)

theorem encodeRounds_append :
    ∀ rs rs' : List (Round F), encodeRounds (rs ++ rs') = encodeRounds rs ++ encodeRounds rs'
  | [], _ => rfl
  | (m, a) :: rs, rs' => by simp [encodeRounds, encodeRounds_append rs rs']

/-- No message is a single `field` (snarkVM absorbs commitment vectors and sums). -/
def NoLoneField (rs : List (Round F)) : Prop :=
  ∀ p ∈ rs, ∀ x, p.1 ≠ FSMessage.field x

theorem NoLoneField.tail {r : Round F} {rs : List (Round F)} (h : NoLoneField (r :: rs)) :
    NoLoneField rs :=
  fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `T` does not start with a single `field`. -/
def FieldFree (T : Transcript F) : Prop :=
  ∀ x rest, T ≠ FSMessage.field x :: rest

/-- A run of `field`s is self-delimiting before a tail that does not start with one. -/
theorem map_field_append_inj : ∀ {a a' : List F} {E E' : Transcript F}, FieldFree E →
    FieldFree E' → a.map FSMessage.field ++ E = a'.map FSMessage.field ++ E' → a = a' ∧ E = E'
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], x :: a', _, E', hE, _, h =>
    (hE x (a'.map FSMessage.field ++ E') (by simpa using h)).elim
  | x :: a, [], E, _, _, hE', h =>
    (hE' x (a.map FSMessage.field ++ E) (by simpa using h.symm)).elim
  | x :: a, x' :: a', _, _, hE, hE', h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq, FSMessage.field.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, hT⟩ := map_field_append_inj hE hE' h
    exact ⟨rfl, hT⟩

theorem fieldFree_encodeRounds : ∀ {rs : List (Round F)}, NoLoneField rs →
    FieldFree (encodeRounds rs)
  | [], _ => fun _ _ h => by simp [encodeRounds] at h
  | (m, a) :: _, h => fun x _ heq => h (m, a) (by simp) x (List.cons.inj heq).1

/-- Rounds with no lone `field` message decode uniquely. -/
theorem encodeRounds_injective : ∀ {rs rs' : List (Round F)}, NoLoneField rs →
    NoLoneField rs' → encodeRounds rs = encodeRounds rs' → rs = rs'
  | [], [], _, _, _ => rfl
  | [], (_, _) :: _, _, _, h => by simp [encodeRounds] at h
  | (_, _) :: _, [], _, _, h => by simp [encodeRounds] at h
  | (m, a) :: rs, (m', a') :: rs', h, h', heq => by
    simp only [encodeRounds, List.cons.injEq] at heq
    obtain ⟨rfl, heq⟩ := heq
    obtain ⟨rfl, hT⟩ :=
      map_field_append_inj (fieldFree_encodeRounds h.tail) (fieldFree_encodeRounds h'.tail) heq
    rw [encodeRounds_injective h.tail h'.tail hT]

/-- An honest squeeze answers each element at its history : the rounds before, then
the message and the elements already squeezed. -/
theorem squeezeN_getElem_rounds (ro : RO F) (I : Transcript F) (pre : List (Round F))
    (m : FSMessage F) (n j : ℕ)
    (hj : j < (squeezeN ro (I ++ encodeRounds pre ++ [m]) n).length) :
    (squeezeN ro (I ++ encodeRounds pre ++ [m]) n)[j] =
      ro (I ++ encodeRounds
        (pre ++ [(m, (squeezeN ro (I ++ encodeRounds pre ++ [m]) n).take j)])) := by
  rw [squeezeN_getElem, encodeRounds_append]
  simp [encodeRounds]

/-! ## The V3 statement prefix -/

/-- `T` does not start with a batch size. -/
def SizeFree (T : Transcript F) : Prop :=
  ∀ n rest, T ≠ FSMessage.size n :: rest

/-- The input blocks are self-delimiting before any tail that does not start with a
batch size. -/
theorem inputBlocks_append_inj' : ∀ {a b : List (List (List F))} {X Y : Transcript F},
    SizeFree X → SizeFree Y → inputBlocks a ++ X = inputBlocks b ++ Y → a = b ∧ X = Y
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], ys :: b, _, Y, hX, _, h =>
    (hX ys.length (ys.map FSMessage.fields ++ inputBlocks b ++ Y)
      (by simpa [inputBlocks] using h)).elim
  | xs :: a, [], X, _, _, hY, h =>
    (hY xs.length (xs.map FSMessage.fields ++ inputBlocks a ++ X)
      (by simpa [inputBlocks] using h.symm)).elim
  | xs :: a, ys :: b, _, _, hX, hY, h => by
    simp only [inputBlocks, List.cons_append, List.append_assoc, List.cons.injEq,
      FSMessage.size.injEq] at h
    obtain ⟨hlen, h⟩ := h
    have hmap : xs.map FSMessage.fields = ys.map FSMessage.fields := by
      have := congrArg (List.take xs.length) h
      simpa [List.take_left', hlen] using this
    obtain rfl := map_fields_injective hmap
    obtain ⟨rfl, hT⟩ := inputBlocks_append_inj' hX hY (List.append_cancel_left h)
    exact ⟨rfl, hT⟩

/-- A V3 statement : public inputs per circuit and instance, and circuit commitments. -/
abbrev V3Stmt (F : Type*) := List (List (List F)) × List (List F)

/-- snarkVM's statements : at least one circuit, one commitment vector per circuit
(`init_sponge` absorbs one per circuit). -/
def V3StmtWF (s : V3Stmt F) : Prop :=
  s.1 ≠ [] ∧ s.2.length = s.1.length

/-- The V3 init followed by rounds decodes uniquely : the statement and the rounds. -/
theorem v3Init_rounds_inj {s s' : V3Stmt F} {rs rs' : List (Round F)} (hs : V3StmtWF s)
    (hs' : V3StmtWF s') (hrs : NoLoneField rs) (hrs' : NoLoneField rs')
    (h : v3Init s.1 s.2 ++ encodeRounds rs = v3Init s'.1 s'.2 ++ encodeRounds rs') :
    s = s' ∧ rs = rs' := by
  obtain ⟨i, c⟩ := s
  obtain ⟨i', c'⟩ := s'
  obtain ⟨hi, hc⟩ := hs
  obtain ⟨hi', hc'⟩ := hs'
  simp only [v3Init, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  have hsf : ∀ {c : List (List F)} {i : List (List (List F))} (E : Transcript F), i ≠ [] →
      c.length = i.length → SizeFree (c.map FSMessage.fields ++ E) := by
    intro c i E hi hc n rest heq
    cases c with
    | nil => exact hi (List.length_eq_zero_iff.mp (by simpa using hc.symm))
    | cons x c => simp at heq
  obtain ⟨rfl, h⟩ := inputBlocks_append_inj' (hsf _ hi hc) (hsf _ hi' hc') h
  have hlen : c.length = c'.length := hc.trans hc'.symm
  have hmap : c.map FSMessage.fields = c'.map FSMessage.fields := by
    have := congrArg (List.take c.length) h
    simpa [List.take_left', hlen] using this
  obtain rfl := map_fields_injective hmap
  exact ⟨rfl, encodeRounds_injective hrs hrs' (List.append_cancel_left h)⟩

/-! ## Charging bad sets on histories -/

/-- Some squeezed element lands in the bad set of its history : the rounds before
it, with its own round cut at that element. -/
def RoundsBreak (RB : List (Round F) → Finset F) (rs : List (Round F)) : Prop :=
  ∃ pre m a post, rs = pre ++ (m, a) :: post ∧
    ∃ j, ∃ hj : j < a.length, a[j] ∈ RB (pre ++ [(m, a.take j)])

/-- Every squeezed element was answered on one of the adversary's queries, at the
statement `I` followed by its history. -/
def RoundsFromQueries (A : FSAdversary F) (tape : List F) (I : Transcript F)
    (rs : List (Round F)) : Prop :=
  ∀ pre m a post, rs = pre ++ (m, a) :: post → ∀ j (hj : j < a.length),
    ChallengeFromQuery A tape (I ++ encodeRounds (pre ++ [(m, a.take j)])) a[j]

open Classical in
/-- A bad set on statements and histories, read off a query : decode it as a
well-formed statement's encoding followed by rounds. -/
noncomputable def queryBad {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (RB : Stmt → List (Round F) → Finset F) (q : Transcript F) : Finset F :=
  if h : ∃ p : Stmt × List (Round F), WF p.1 ∧ NoLoneField p.2 ∧ q = enc p.1 ++ encodeRounds p.2
  then RB h.choose.1 h.choose.2 else ∅

theorem queryBad_eq {Stmt : Type*} {enc : Stmt → Transcript F} {WF : Stmt → Prop}
    (hinj : ∀ s s' rs rs', WF s → WF s' → NoLoneField rs → NoLoneField rs' →
      enc s ++ encodeRounds rs = enc s' ++ encodeRounds rs' → s = s' ∧ rs = rs')
    (RB : Stmt → List (Round F) → Finset F) {s : Stmt} {rs : List (Round F)} (hs : WF s)
    (hrs : NoLoneField rs) : queryBad enc WF RB (enc s ++ encodeRounds rs) = RB s rs := by
  have h : ∃ p : Stmt × List (Round F), WF p.1 ∧ NoLoneField p.2 ∧
      enc s ++ encodeRounds rs = enc p.1 ++ encodeRounds p.2 := ⟨(s, rs), hs, hrs, rfl⟩
  rw [queryBad, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := h.choose_spec
  obtain ⟨e1, e2⟩ := hinj _ _ _ _ hs h1 hrs h2 h3
  rw [← e1, ← e2]

theorem card_filter_queryBad_le {Stmt : Type*} {enc : Stmt → Transcript F} {WF : Stmt → Prop}
    {RB : Stmt → List (Round F) → Finset F} {S : Finset F} {b : ℕ}
    (hb : ∀ s rs, (S.filter (· ∈ RB s rs)).card ≤ b) (q : Transcript F) :
    (S.filter (· ∈ queryBad enc WF RB q)).card ≤ b := by
  unfold queryBad
  split
  · exact hb _ _
  · simp

/-- Adaptive query charging. Let the bad set of a squeezed element be any function
of the statement and its history, with at most `b` bad answers in `S`, and let the
statement encoding followed by rounds decode uniquely. If every squeezed element of
the adversary's output was answered on one of its `Q` queries, at most
`Q · b · | S | ^{Q-1}` tapes yield an event `E` that forces a break. -/
theorem fs_rounds_charge {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (hinj : ∀ s s' rs rs', WF s → WF s' → NoLoneField rs → NoLoneField rs' →
      enc s ++ encodeRounds rs = enc s' ++ encodeRounds rs' → s = s' ∧ rs = rs')
    (S : Finset F) (A : FSAdversary F) (RB : Stmt → List (Round F) → Finset F) (b : ℕ)
    (hb : ∀ s rs, (S.filter (· ∈ RB s rs)).card ≤ b) (Q : ℕ) (stmt : List F → Stmt)
    (rounds : List F → List (Round F))
    (hcons : ∀ tape ∈ tapes S Q, RoundsFromQueries A tape (enc (stmt tape)) (rounds tape))
    (E : List F → Prop) [DecidablePred E]
    (hE : ∀ tape ∈ tapes S Q, E tape → WF (stmt tape) ∧ NoLoneField (rounds tape) ∧
      RoundsBreak (RB (stmt tape)) (rounds tape)) :
    ((tapes S Q).filter E).card ≤ Q * b * S.card ^ (Q - 1) := by
  refine (card_le_card fun tape htape => ?_).trans
    (fs_query_charge S A (queryBad enc WF RB) b (card_filter_queryBad_le hb) Q)
  obtain ⟨hmem, he⟩ := mem_filter.mp htape
  obtain ⟨hs, hnl, pre, m, a, post, hrs, j, hj, hbad⟩ := hE tape hmem he
  have hnl' : NoLoneField (pre ++ [(m, a.take j)]) := by
    intro p hp x
    rcases List.mem_append.mp hp with hp | hp
    · exact hnl p (by rw [hrs]; exact List.mem_append_left _ hp) x
    · rw [List.mem_singleton.mp hp]
      exact hnl (m, a) (by rw [hrs]; simp) x
  refine mem_filter.mpr ⟨hmem, fsHits_of_bad A _ (hcons tape hmem pre m a post hrs j hj) ?_⟩
  rw [queryBad_eq hinj RB hs hnl']
  exact hbad

end Varuna