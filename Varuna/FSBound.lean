/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Combiners

/-!
# Fiat–Shamir : charging the adversary per oracle query

The random oracle is lazily sampled : the adversary's `i`-th query is
answered with the `i`-th entry of a uniformly random tape in `S^Q`.
Queries are fresh (a repeated query gets its earlier answer, so an
adversary gains nothing by repeating one). The adversary is deterministic
given the answers so far.

Round-by-round soundness supplies, for each query prefix, the bad
challenges that would let a prover out of a doomed state (for Varuna, the
roots of the residual the prefix determines, or the one element that ends
a weight draw's liveness; see `Probability.lean` and `Combiners.lean`). If
each query has at most `b` bad answers in `S`,
at most `Q · b · | S | ^{Q-1}` of the ` | S | ^Q` tapes let the adversary hit one
(`fs_query_charge`): knowledge error `Q · b / | S | `, as in Ironwood.

`fs_break_count` connects that bound to the V2 transcript. A squeeze draws
one element per oracle query, each prefix extended by the elements before it
(`squeezeN`, `elemBefore`). If every squeezed element of the adversary's
output was answered on one of its queries, an output with a break at any
element is a hit.
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

theorem mem_v2Challenges (c : V2Challenge) : c ∈ v2Challenges := by
  cases c <;> simp [v2Challenges]

/-- Query prefix of the next element of squeeze `c`, after its elements `w` : the
elements already squeezed are appended as `field` messages, as in `squeezeN`. -/
def V2Transcript.elemBefore (t : V2Transcript F) (c : V2Challenge) (w : List F) :
    Transcript F :=
  t.before c ++ w.map FSMessage.field

/-- Element `j` of a squeeze is the oracle's answer at the prefix extended by the
elements before it. -/
theorem squeezeN_getElem (ro : RO F) :
    ∀ (pre : Transcript F) (n j : ℕ) (hj : j < (squeezeN ro pre n).length),
      (squeezeN ro pre n)[j] = ro (pre ++ ((squeezeN ro pre n).take j).map FSMessage.field)
  | pre, 0, j, hj => by simp at hj
  | pre, n + 1, 0, _ => by simp [squeezeN]
  | pre, n + 1, j + 1, hj => by
    have hj' : j < (squeezeN ro (pre ++ [FSMessage.field (ro pre)]) n).length := by
      rw [squeezeN_length]
      rw [squeezeN_length] at hj
      omega
    simp only [squeezeN, List.getElem_cons_succ, List.take_succ_cons, List.map_cons]
    rw [squeezeN_getElem ro _ n j hj', List.append_assoc, List.singleton_append]

/-- In an honest transcript, element `j` of squeeze `c` is the oracle at `elemBefore`. -/
theorem squeezeN_before_getElem (ro : RO F) (t : V2Transcript F) (c : V2Challenge) (n j : ℕ)
    (hj : j < (squeezeN ro (t.before c) n).length) :
    (squeezeN ro (t.before c) n)[j] =
      ro (t.elemBefore c ((squeezeN ro (t.before c) n).take j)) :=
  squeezeN_getElem ro _ n j hj

/-- Whether some squeezed element of the output lands in the bad set of its query
prefix. `chal c` lists the elements squeezed at `c`. -/
def outputBreaks (Bad : Transcript F → Finset F) (t : V2Transcript F)
    (chal : V2Challenge → List F) : Bool :=
  v2Challenges.any fun c => hitsB (fun w => Bad (t.elemBefore c w)) [] (chal c)

/-- Every squeezed element of the output was answered on one of the adversary's
queries, at its `elemBefore` prefix. -/
def OutputFromQueries (A : FSAdversary F) (tape : List F) (t : V2Transcript F)
    (chal : V2Challenge → List F) : Prop :=
  ∀ c j (hj : j < (chal c).length),
    ChallengeFromQuery A tape (t.elemBefore c ((chal c).take j)) (chal c)[j]

/-- Fiat–Shamir knowledge error for V2, counting form. If every squeezed element of
the output transcript was answered on one of the adversary's `Q` queries, at most
`Q · b · | S | ^{Q-1}` tapes yield an output with a break at any element. -/
theorem fs_break_count (S : Finset F) (A : FSAdversary F) (Bad : Transcript F → Finset F) (b : ℕ)
    (hb : ∀ t, (S.filter (· ∈ Bad t)).card ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → List F)
    (hcons : ∀ tape ∈ tapes S Q, OutputFromQueries A tape (out tape) (chal tape)) :
    ((tapes S Q).filter fun tape => outputBreaks Bad (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) := by
  refine (card_le_card fun tape htape => ?_).trans (fs_query_charge S A Bad b hb Q)
  obtain ⟨hmem, hbr⟩ := mem_filter.mp htape
  obtain ⟨c, _, hc⟩ := List.any_eq_true.mp hbr
  obtain ⟨j, hj, hbad⟩ := (hitsB_iff _ _ _).mp hc
  rw [List.nil_append] at hbad
  exact mem_filter.mpr ⟨hmem, fsHits_of_bad A Bad (hcons tape hmem c j hj) hbad⟩

/-- Distinct absorb prefixes, so a transcript prefix names at most one squeeze. -/
theorem before_injective (t : V2Transcript F) : Function.Injective t.before := by
  intro c₁ c₂ h
  have hlen := congrArg List.length h
  rw [before_length, before_length] at hlen
  cases c₁ <;> cases c₂ <;> first | rfl | simp [V2Challenge.prefixAbsorbs] at hlen

/-- The prover's six round messages, in order. -/
def V2Transcript.messages (t : V2Transcript F) : List (FSMessage F) :=
  [t.first, t.second, t.prepareThird, t.third, t.fourth, t.fifth]

theorem before_eq_take (t : V2Transcript F) (c : V2Challenge) :
    t.before c = t.init ++ t.messages.take c.prefixAbsorbs := by
  cases c <;> rfl

theorem prefixAbsorbs_injective : Function.Injective V2Challenge.prefixAbsorbs := by
  intro c₁ c₂ h
  cases c₁ <;> cases c₂ <;> first | rfl | simp [V2Challenge.prefixAbsorbs] at h

theorem prefixAbsorbs_le (c : V2Challenge) : c.prefixAbsorbs ≤ 6 := by
  cases c <;> decide

/-- Squeezed elements stand in for a prover message only if it is a lone `field`. -/
theorem take_append_fields_ne {l : List (FSMessage F)} (hl : ∀ x, FSMessage.field x ∉ l)
    {a a' : ℕ} (ha : a < a') (ha' : a' ≤ l.length) (w w' : List F) :
    l.take a ++ w.map FSMessage.field ≠ l.take a' ++ w'.map FSMessage.field := by
  intro h
  have hlt : a < l.length := by omega
  obtain ⟨k, hk⟩ : ∃ k, a' = a + (k + 1) := ⟨a' - a - 1, by omega⟩
  rw [hk, List.take_add, List.append_assoc, List.drop_eq_getElem_cons hlt,
    List.take_succ_cons] at h
  have hmem : l[a] ∈ w.map FSMessage.field := by
    rw [List.append_cancel_left h]
    simp
  obtain ⟨x, -, hx⟩ := List.mem_map.mp hmem
  exact hl x (hx ▸ List.getElem_mem hlt)

/-- If no prover message is a lone `field`, a query prefix is an element prefix of at
most one squeeze. -/
theorem elemBefore_inj {t : V2Transcript F} (hmsg : ∀ x, FSMessage.field x ∉ t.messages)
    {c c' : V2Challenge} {w w' : List F} (h : t.elemBefore c w = t.elemBefore c' w') :
    c = c' := by
  rw [V2Transcript.elemBefore, V2Transcript.elemBefore, before_eq_take, before_eq_take,
    List.append_assoc, List.append_assoc] at h
  have h' := List.append_cancel_left h
  have hlen : t.messages.length = 6 := rfl
  rcases lt_trichotomy c.prefixAbsorbs c'.prefixAbsorbs with hlt | heq | hgt
  · exact absurd h' (take_append_fields_ne hmsg hlt (hlen ▸ prefixAbsorbs_le c') w w')
  · exact prefixAbsorbs_injective heq
  · exact absurd h'.symm (take_append_fields_ne hmsg hgt (hlen ▸ prefixAbsorbs_le c) w' w)

/-- The elements of a run of `field` messages. -/
def fieldRun : Transcript F → Option (List F)
  | [] => some []
  | .field x :: ms => (fieldRun ms).map (x :: ·)
  | _ :: _ => none

theorem fieldRun_map : ∀ w : List F, fieldRun (w.map FSMessage.field) = some w
  | [] => rfl
  | x :: w => by simp [fieldRun, fieldRun_map w]

theorem eq_map_field_of_fieldRun :
    ∀ {ms : Transcript F} {w : List F}, fieldRun ms = some w → ms = w.map FSMessage.field
  | [], w, h => by
    simp only [fieldRun, Option.some.injEq] at h
    simp [← h]
  | .field x :: ms, w, h => by
    simp only [fieldRun, Option.map_eq_some_iff] at h
    obtain ⟨w', hw', rfl⟩ := h
    simp [eq_map_field_of_fieldRun hw']
  | .tag _ :: _, _, h => by simp [fieldRun] at h
  | .fields _ :: _, _, h => by simp [fieldRun] at h
  | .size _ :: _, _, h => by simp [fieldRun] at h

/-- The elements `w` with `pre = t.elemBefore c w`, if any. -/
def V2Transcript.decodeAt (t : V2Transcript F) (c : V2Challenge) (pre : Transcript F) :
    Option (List F) :=
  if pre.take (t.before c).length = t.before c then fieldRun (pre.drop (t.before c).length)
  else none

theorem decodeAt_elemBefore (t : V2Transcript F) (c : V2Challenge) (w : List F) :
    t.decodeAt c (t.elemBefore c w) = some w := by
  simp [V2Transcript.decodeAt, V2Transcript.elemBefore, fieldRun_map]

theorem eq_elemBefore_of_decodeAt {t : V2Transcript F} {c : V2Challenge} {pre : Transcript F}
    {w : List F} (h : t.decodeAt c pre = some w) : pre = t.elemBefore c w := by
  unfold V2Transcript.decodeAt at h
  split_ifs at h with htake
  rw [V2Transcript.elemBefore, ← eq_map_field_of_fieldRun h]
  calc pre = pre.take (t.before c).length ++ pre.drop (t.before c).length :=
        (List.take_append_drop _ _).symm
    _ = _ := by rw [htake]

/-- The squeeze and the earlier elements of it that a query prefix names, if any. -/
def V2Transcript.decodeElem (t : V2Transcript F) (pre : Transcript F) :
    Option (V2Challenge × List F) :=
  v2Challenges.findSome? fun c => (t.decodeAt c pre).map (c, ·)

theorem findSome?_eq_of_unique {α β : Type*} {f : α → Option β} {a : α} {b : β}
    (hfa : f a = some b) (huniq : ∀ a', f a' ≠ none → a' = a) :
    ∀ {l : List α}, a ∈ l → l.findSome? f = some b
  | [], h => absurd h List.not_mem_nil
  | x :: l, h => by
    by_cases hx : f x = none
    · have hxa : x ≠ a := fun hxa => by rw [hxa, hfa] at hx; cases hx
      rw [List.findSome?_cons_of_isNone (by simp [hx])]
      exact findSome?_eq_of_unique hfa huniq ((List.mem_cons.mp h).resolve_left (Ne.symm hxa))
    · obtain rfl := huniq x hx
      rw [List.findSome?_cons_of_isSome (by simp [hfa]), hfa]

theorem decodeElem_elemBefore {t : V2Transcript F} (hmsg : ∀ x, FSMessage.field x ∉ t.messages)
    (c : V2Challenge) (w : List F) : t.decodeElem (t.elemBefore c w) = some (c, w) := by
  refine findSome?_eq_of_unique (by simp [decodeAt_elemBefore]) (fun c' hc' => ?_)
    (mem_v2Challenges c)
  cases hd : t.decodeAt c' (t.elemBefore c w) with
  | none => simp [hd] at hc'
  | some w' => exact (elemBefore_inj hmsg (eq_elemBefore_of_decodeAt hd)).symm

/-- The bad set of a query : the bad set of the squeeze element whose prefix it is,
given the elements of that squeeze before it. A prefix that is no squeeze element
contributes nothing. -/
def prefixBad (t : V2Transcript F) (Bad : V2Challenge → List F → Finset F)
    (pre : Transcript F) : Finset F :=
  match t.decodeElem pre with
  | some (c, w) => Bad c w
  | none => ∅

theorem prefixBad_elemBefore {t : V2Transcript F} (hmsg : ∀ x, FSMessage.field x ∉ t.messages)
    (Bad : V2Challenge → List F → Finset F) (c : V2Challenge) (w : List F) :
    prefixBad t Bad (t.elemBefore c w) = Bad c w := by
  rw [prefixBad, decodeElem_elemBefore hmsg]

theorem card_filter_prefixBad_le {t : V2Transcript F} {Bad : V2Challenge → List F → Finset F}
    {S : Finset F} {b : ℕ} (hb : ∀ c w, (S.filter (· ∈ Bad c w)).card ≤ b) (pre : Transcript F) :
    (S.filter (· ∈ prefixBad t Bad pre)).card ≤ b := by
  unfold prefixBad
  split
  · exact hb _ _
  · simp

/-- A squeezed element of `t` in its bad set makes the output `t` break. -/
theorem outputBreaks_of_mem_bad {t : V2Transcript F}
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) {Bad : V2Challenge → List F → Finset F}
    {chal : V2Challenge → List F} {c : V2Challenge} {j : ℕ} (hj : j < (chal c).length)
    (hbad : (chal c)[j] ∈ Bad c ((chal c).take j)) :
    outputBreaks (prefixBad t Bad) t chal = true :=
  List.any_eq_true.mpr ⟨c, mem_v2Challenges c, (hitsB_iff _ _ _).mpr
    ⟨j, hj, by rwa [List.nil_append, prefixBad_elemBefore hmsg]⟩⟩

/-- A lucky weight draw at a squeeze of `t` makes the output `t` break. -/
theorem outputBreaks_of_lucky {t : V2Transcript F} (hmsg : ∀ x, FSMessage.field x ∉ t.messages)
    {S : Finset F} {Bad : V2Challenge → List F → Finset F} {d : WeightDraw F} {c : V2Challenge}
    (hc : Bad c = d.bad S) {chal : V2Challenge → List F} (hl : d.Lucky (chal c))
    (hS : ∀ a ∈ chal c, a ∈ S) : outputBreaks (prefixBad t Bad) t chal = true := by
  obtain ⟨j, hj, hbad⟩ := d.exists_bad_of_lucky hl hS
  exact outputBreaks_of_mem_bad hmsg hj (hc ▸ hbad)

/-- Schwartz–Zippel roots of `res`, at the one element of a single-element squeeze. -/
noncomputable def szAt (S : Finset F) (res : F[X]) (w : List F) : Finset F :=
  if w = [] then S.filter (· ∈ szBadSet res) else ∅

theorem card_szAt_le (S : Finset F) (res : F[X]) (w : List F) :
    (szAt S res w).card ≤ res.natDegree := by
  unfold szAt
  split_ifs
  · exact (card_filter_mem_le _ _).trans (card_szBadSet_le_natDegree res)
  · simp

/-- Bad answers at each V2 squeeze element. `α`, `β`, `γ` are single elements with
Schwartz–Zippel roots as bad set. The combiner squeezes draw several elements;
the bad set of each is the elements that end liveness of that squeeze's weight
draw (`WeightDraw.bad`), at most one. -/
noncomputable def squeezeBad (S : Finset F) (resα resβ resγ : F[X]) (dν dη dδ : WeightDraw F) :
    V2Challenge → List F → Finset F
  | .alpha => szAt S resα
  | .beta => szAt S resβ
  | .gamma => szAt S resγ
  | .firstCombiners => dν.bad S
  | .prepareThird => dη.bad S
  | .deltas => dδ.bad S

/-- Every squeeze element's bad set has size at most
`max(deg resα, deg resβ, deg resγ, 1)`. -/
theorem squeezeBad_card (S : Finset F) (resα resβ resγ : F[X]) (dν dη dδ : WeightDraw F)
    (hν : ∀ x ∈ dν.D, CoordAffine (dν.comb x)) (hη : ∀ x ∈ dη.D, CoordAffine (dη.comb x))
    (hδ : ∀ x ∈ dδ.D, CoordAffine (dδ.comb x)) {b : ℕ}
    (hα : resα.natDegree ≤ b) (hβ : resβ.natDegree ≤ b) (hγ : resγ.natDegree ≤ b)
    (hb : 1 ≤ b) :
    ∀ c w, (squeezeBad S resα resβ resγ dν dη dδ c w).card ≤ b := by
  intro c w
  cases c with
  | alpha => exact (card_szAt_le S resα w).trans hα
  | beta => exact (card_szAt_le S resβ w).trans hβ
  | gamma => exact (card_szAt_le S resγ w).trans hγ
  | firstCombiners => exact (dν.card_bad_le_one hν S w).trans hb
  | prepareThird => exact (dη.card_bad_le_one hη S w).trans hb
  | deltas => exact (dδ.card_bad_le_one hδ S w).trans hb

/-- Outside a squeeze's Schwartz–Zippel set, an accepting evaluation is a zero residual. -/
theorem squeeze_safe_residual {res : F[X]} {α : F} (hα : α ∉ szBadSet res)
    (hacc : res.eval α = 0) : inspectResidual res α = none := by
  have h0 : res = 0 := by
    by_contra hne
    exact eval_ne_zero_of_notMem_szBadSet hne hα hacc
  exact inspectResidual_eq_none_of_zero h0

/-- Query charging for the V2 squeezes, element by element. `squeezeBad_card`
supplies `b`. -/
theorem fs_squeeze_charge (S : Finset F) (A : FSAdversary F) (t : V2Transcript F)
    (Bad : V2Challenge → List F → Finset F) (b : ℕ)
    (hb : ∀ c w, (S.filter (· ∈ Bad c w)).card ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → List F)
    (hcons : ∀ tape ∈ tapes S Q, OutputFromQueries A tape (out tape) (chal tape)) :
    ((tapes S Q).filter fun tape =>
      outputBreaks (prefixBad t Bad) (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) :=
  fs_break_count S A (prefixBad t Bad) b (card_filter_prefixBad_le hb) Q out chal hcons

/-- The V2 squeezes, element by element, with bad sets read off the residuals and
the three weight draws, charged as one query-bounded break count. -/
theorem fs_v2_squeeze_charge (S : Finset F) (A : FSAdversary F) (t : V2Transcript F)
    (resα resβ resγ : F[X]) (dν dη dδ : WeightDraw F)
    (hν : ∀ x ∈ dν.D, CoordAffine (dν.comb x)) (hη : ∀ x ∈ dη.D, CoordAffine (dη.comb x))
    (hδ : ∀ x ∈ dδ.D, CoordAffine (dδ.comb x)) {b : ℕ}
    (hα : resα.natDegree ≤ b) (hβ : resβ.natDegree ≤ b) (hγ : resγ.natDegree ≤ b)
    (hb : 1 ≤ b) (Q : ℕ) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → List F)
    (hcons : ∀ tape ∈ tapes S Q, OutputFromQueries A tape (out tape) (chal tape)) :
    ((tapes S Q).filter fun tape =>
      outputBreaks (prefixBad t (squeezeBad S resα resβ resγ dν dη dδ))
        (out tape) (chal tape) = true).card ≤
      Q * b * S.card ^ (Q - 1) :=
  fs_squeeze_charge S A t _ b (fun c w => (card_filter_mem_le _ _).trans
    (squeezeBad_card S resα resβ resγ dν dη dδ hν hη hδ hα hβ hγ hb c w)) Q out chal hcons

/-- `batchedZerocheck_extract` needs no lucky combination on all of `H`. With the
first-round combiners of the output `t` as weights `ν_i τ_{i,j}`, a lucky one makes
`t` break at the first-combiners squeeze. -/
theorem outputBreaks_of_rowcheck_lucky {t : V2Transcript F}
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) {S : Finset F} (resα resβ resγ : F[X])
    {H : EvalDomain F} {sizes : List ℕ} {cs : List (EvalDomain F × F[X])}
    (hcs : cs.length ≤ (sizes.map (· - 1 + 1)).sum) (dη dδ : WeightDraw F)
    {chal : V2Challenge → List F} (hlen : (chal .firstCombiners).length = combinerDraws sizes)
    (hS : ∀ a ∈ chal .firstCombiners, a ∈ S)
    (h : inspectBatchOn H.nodeList (schemeWeights (combinerScheme sizes) (chal .firstCombiners))
      (batchedClaims H cs) ≠ none) :
    outputBreaks (prefixBad t (squeezeBad S resα resβ resγ (rowcheckDraw H sizes cs) dη dδ)) t
      chal = true :=
  outputBreaks_of_lucky hmsg rfl (rowcheckDraw_lucky hcs hlen h) hS

/-- `batchedMatrix_extract` needs no lucky `δ` combination on all of `K`. With the
fourth-round elements of the output `t` as the `δ`s of `n` circuits, a lucky one
makes `t` break at the deltas squeeze. -/
theorem outputBreaks_of_matrix_lucky {t : V2Transcript F}
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) {S : Finset F} (resα resβ resγ : F[X])
    {K : EvalDomain F} {n : ℕ} {cs : List (EvalDomain F × F[X])}
    (hcs : cs.length ≤ 3 * n - 1 + 1) (dν dη : WeightDraw F)
    {chal : V2Challenge → List F} (hlen : (chal .deltas).length = 3 * n - 1)
    (hS : ∀ a ∈ chal .deltas, a ∈ S)
    (h : inspectBatchOn K.nodeList (schemeWeights (deltaScheme n) (chal .deltas))
      (batchedClaims K cs) ≠ none) :
    outputBreaks (prefixBad t (squeezeBad S resα resβ resγ dν dη (deltaDraw K n cs))) t
      chal = true :=
  outputBreaks_of_lucky hmsg rfl (deltaDraw_lucky hcs hlen h) hS

/-- An output with no break leaves the residual of a single-element squeeze with
no Schwartz–Zippel break at its element. -/
theorem inspectResidual_eq_none_of_no_break {t : V2Transcript F}
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) {S : Finset F}
    {Bad : V2Challenge → List F → Finset F} {chal : V2Challenge → List F} {c : V2Challenge}
    {res : F[X]} {α : F} (hc : Bad c = szAt S res) (hα : chal c = [α]) (hS : α ∈ S)
    (hnb : outputBreaks (prefixBad t Bad) t chal = false) : inspectResidual res α = none := by
  have hbad : α ∉ szBadSet res := fun h => by
    have hj : 0 < (chal c).length := by simp [hα]
    have hmem : (chal c)[0] ∈ Bad c ((chal c).take 0) := by
      simp [hα, hc, szAt, hS, h]
    rw [outputBreaks_of_mem_bad hmsg hj hmem] at hnb
    cases hnb
  by_cases h0 : res = 0
  · exact inspectResidual_eq_none_of_zero h0
  · simp [inspectResidual, h0, eval_ne_zero_of_notMem_szBadSet h0 hbad]

/-- An output with no break draws no lucky weights at a squeeze. -/
theorem not_lucky_of_no_break {t : V2Transcript F} (hmsg : ∀ x, FSMessage.field x ∉ t.messages)
    {S : Finset F} {Bad : V2Challenge → List F → Finset F} {d : WeightDraw F} {c : V2Challenge}
    (hc : Bad c = d.bad S) {chal : V2Challenge → List F} (hS : ∀ a ∈ chal c, a ∈ S)
    (hnb : outputBreaks (prefixBad t Bad) t chal = false) : ¬d.Lucky (chal c) := fun hl => by
  rw [outputBreaks_of_lucky hmsg hc hl hS] at hnb
  cases hnb

end Varuna