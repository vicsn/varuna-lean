/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AlgebraicFS

/-!
# Fiat–Shamir with the sponge's queries

snarkVM's duplex sponge absorbs the prover's messages only. The sponge state before a
squeezed element is fixed by the statement, the messages, and how many elements were
squeezed after each (`spongeRounds`), not by the values of the earlier challenges. As
a random oracle, each element is the oracle's answer at that state. A prover can ask
for a later state before it knows the earlier challenges, so the bad set of a query is
not a function of what was answered before it, and lazy sampling does not charge it.

Here the oracle is a table : a list `T` of elements of `S`, one entry per query of a
finite domain `D`, answers each query with its entry (`tableAns`), and the count is
over tables. The bad set of a query reads
the log before it and the table only at other queries, the earlier elements' states
(`spongeBad`). Changing the entry of a fresh query then changes neither the log before
it nor its bad set, so at most `b` of its values in `S` are bad (`card_resample_le`),
whatever order the queries come in (`table_charge`).

`V3Batch.sponge_soundness` is `V3Batch.algebraic_soundness` against the sponge : the
algebraic prover makes `Q` queries, the verifier's challenges are the table's answers
at its sponge states, and on the tables with no clash at most `(Q + V) · b · | S | ^(n-1)`
of the ` | S | ^n`, `n` the length of `D`, give an accepted output while the relation
fails.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Resampling one entry -/

theorem mem_tapes_of {S : Finset F} :
    ∀ {n : ℕ} {t : List F}, t.length = n → (∀ a ∈ t, a ∈ S) → t ∈ tapes S n
  | 0, [], _, _ => by simp [tapes]
  | n + 1, a :: t, hlen, hS => by
    simp only [tapes, mem_biUnion, mem_image]
    exact ⟨a, hS a (by simp), t, mem_tapes_of (by simpa using hlen) fun x hx =>
      hS x (by simp [hx]),
      rfl⟩

/-- Resampling one entry of a tape. Let each tape `T` of an event `E` fix a position
`k T` and a bad set `B T` that stay put when the entry at `k T` changes, with that
entry bad. If at most `b` elements of `S` are bad, `E` has at most a `b / | S | `
fraction of the ` | S | ^n` tapes. -/
theorem card_resample_le (S : Finset F) (n : ℕ) (E : Finset (List F)) (hE : E ⊆ tapes S n)
    (k : List F → ℕ) (B : List F → Finset F) (b : ℕ) (hb : ∀ T, (S.filter (· ∈ B T)).card ≤ b)
    (hk : ∀ T ∈ E, ∃ h : k T < T.length, T[k T] ∈ B T)
    (hinv : ∀ T ∈ E, ∀ x ∈ S, k (T.set (k T) x) = k T ∧ B (T.set (k T) x) = B T) :
    E.card * S.card ≤ b * S.card ^ n := by
  set f : List F × F → List F := fun p => p.1.set (k p.1) p.2
  have hmaps : ∀ p ∈ E ×ˢ S, f p ∈ tapes S n := by
    intro p hp
    obtain ⟨hT, hx⟩ := mem_product.1 hp
    obtain ⟨hlen, hS⟩ := mem_tapes (hE hT)
    refine mem_tapes_of (by simp [f, hlen]) fun a ha => ?_
    rcases List.mem_or_eq_of_mem_set ha with ha | rfl
    · exact hS a ha
    · exact hx
  have hfib : ∀ T' ∈ (E ×ˢ S).image f, ((E ×ˢ S).filter fun p => f p = T').card ≤ b := by
    intro T' _
    refine (card_le_card_of_injOn (fun p => (p.1[k p.1]?).getD 0) (t := S.filter (· ∈ B T'))
      ?_ ?_).trans (hb T')
    · intro p hp
      obtain ⟨hp0, rfl⟩ := mem_filter.1 (mem_coe.1 hp)
      obtain ⟨hT, hx⟩ := mem_product.1 hp0
      obtain ⟨hkT, hbad⟩ := hk p.1 hT
      simp only [List.getElem?_eq_getElem hkT, Option.getD_some]
      refine mem_coe.2 (mem_filter.2 ⟨(mem_tapes (hE hT)).2 _ (List.getElem_mem hkT), ?_⟩)
      rw [(hinv p.1 hT p.2 hx).2]
      exact hbad
    · intro p hp p' hp' heq
      obtain ⟨hp, hpT⟩ := mem_filter.1 (mem_coe.1 hp)
      obtain ⟨hp', hpT'⟩ := mem_filter.1 (mem_coe.1 hp')
      obtain ⟨hT, hx⟩ := mem_product.1 hp
      obtain ⟨hT', hx'⟩ := mem_product.1 hp'
      have hkk : k p.1 = k p'.1 := by
        rw [← (hinv p.1 hT p.2 hx).1, ← (hinv p'.1 hT' p'.2 hx').1]
        exact congrArg k (hpT.trans hpT'.symm)
      obtain ⟨hk1, -⟩ := hk p.1 hT
      obtain ⟨hk2, -⟩ := hk p'.1 hT'
      simp only [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2,
        Option.getD_some] at heq
      have h2 : p.2 = p'.2 := by
        have h := congrArg (fun T => T[k p.1]?) (hpT.trans hpT'.symm)
        simp only [f, hkk, List.getElem?_set_self (hkk ▸ hk1 : k p'.1 < p.1.length),
          List.getElem?_set_self hk2, Option.some.injEq] at h
        exact h
      have hT'' : p.1.set (k p.1) p.2 = p'.1.set (k p.1) p'.2 := by
        have h := hpT.trans hpT'.symm
        simp only [f] at h
        rw [← hkk] at h
        exact h
      have hlen : p.1.length = p'.1.length := by simpa using congrArg List.length hT''
      have h1 : p.1 = p'.1 := by
        refine List.ext_getElem hlen fun i hi hi' => ?_
        by_cases hik : k p.1 = i
        · subst hik
          rw [heq]
          simp only [hkk]
        · have h := congrArg (fun T => T[i]?) hT''
          simp only [List.getElem?_set_ne hik, List.getElem?_eq_getElem hi,
            List.getElem?_eq_getElem hi', Option.some.injEq] at h
          exact h
      exact Prod.ext h1 h2
  calc E.card * S.card = (E ×ˢ S).card := (card_product _ _).symm
    _ ≤ b * ((E ×ˢ S).image f).card := card_le_mul_card_image _ _ hfib
    _ ≤ b * (tapes S n).card := Nat.mul_le_mul_left _ (card_le_card fun T hT => by
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hT
        exact hmaps p hp)
    _ = b * S.card ^ n := by rw [card_tapes]

/-! ## A random oracle as a table -/

/-- The oracle the table `T` defines on the domain `D` : each query's entry at its first
index in `D`, `0` off `D`. -/
def tableAns (D : List (Transcript F)) (T : List F) (q : Transcript F) : F :=
  (T[D.idxOf q]?).getD 0

/-- `n` queries of `next` against the oracle `H`, each with its answer. -/
def tableRun (next : QueryLog F → Transcript F) (H : Transcript F → F) : ℕ → QueryLog F
  | 0 => []
  | n + 1 => tableRun next H n ++ [(next (tableRun next H n), H (next (tableRun next H n)))]

theorem length_tableRun (next : QueryLog F → Transcript F) (H : Transcript F → F) :
    ∀ n, (tableRun next H n).length = n
  | 0 => rfl
  | n + 1 => by simp [tableRun, length_tableRun next H n]

theorem take_tableRun (next : QueryLog F → Transcript F) (H : Transcript F → F) {m : ℕ} :
    ∀ {n}, m ≤ n → (tableRun next H n).take m = tableRun next H m
  | 0, h => by
    obtain rfl : m = 0 := by omega
    rfl
  | n + 1, h => by
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · rw [tableRun, List.take_append_of_le_length (by rw [length_tableRun]; omega),
        take_tableRun next H (by omega)]
    · obtain rfl : m = n + 1 := by omega
      exact List.take_of_length_le (by rw [length_tableRun])

/-- Oracles that agree off `q` give the same run while no query is `q`. -/
theorem tableRun_congr (next : QueryLog F → Transcript F) {H H' : Transcript F → F}
    {q : Transcript F} (hH : ∀ q', q' ≠ q → H q' = H' q') :
    ∀ n, (∀ i < n, next (tableRun next H i) ≠ q) → tableRun next H n = tableRun next H' n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := tableRun_congr next hH n fun i hi => h i (by omega)
    rw [tableRun, tableRun, ← ih, hH _ (h n (by omega))]

/-- Strategies that agree on logs shorter than `Q` make the same first `Q` queries. -/
theorem tableRun_congr_next {next next' : QueryLog F → Transcript F} {Q : ℕ}
    (h : ∀ log : QueryLog F, log.length < Q → next' log = next log) (H : Transcript F → F) :
    ∀ n, n ≤ Q → tableRun next' H n = tableRun next H n
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := tableRun_congr_next h H n (by omega)
    rw [tableRun, tableRun, ih, h _ (by rw [length_tableRun]; omega)]

theorem tableAns_set {D : List (Transcript F)} {q : Transcript F} (hq : q ∈ D) (T : List F)
    (x : F) {q' : Transcript F} (hq' : q' ≠ q) :
    tableAns D (T.set (D.idxOf q) x) q' = tableAns D T q' := by
  unfold tableAns
  rw [List.getElem?_set_ne fun h => hq' ((List.idxOf_inj hq).1 h).symm]

/-- The query at step `i` is in `D`, differs from every earlier query, and gets an
answer in its bad set, read off the log before it, the query, and the oracle. -/
def TableHit (D : List (Transcript F)) (next : QueryLog F → Transcript F)
    (RB : QueryLog F → Transcript F → (Transcript F → F) → Finset F) (T : List F) (i : ℕ) :
    Prop :=
  next (tableRun next (tableAns D T) i) ∈ D ∧
    (∀ i' < i, next (tableRun next (tableAns D T) i') ≠ next (tableRun next (tableAns D T) i)) ∧
    tableAns D T (next (tableRun next (tableAns D T) i)) ∈
      RB (tableRun next (tableAns D T) i) (next (tableRun next (tableAns D T) i)) (tableAns D T)

open Classical in
/-- Table charging. Let each query's bad set have at most `b` elements of `S` and read
the oracle only off that query. At most `n · b · | S | ^(m-1)` of the ` | S | ^m` tables,
`m` the length of `D`, let one of the first `n` queries be a hit. -/
theorem table_charge (D : List (Transcript F)) (S : Finset F)
    (next : QueryLog F → Transcript F)
    (RB : QueryLog F → Transcript F → (Transcript F → F) → Finset F) (b : ℕ)
    (hb : ∀ log q H, (S.filter (· ∈ RB log q H)).card ≤ b)
    (hRB : ∀ log q H H', (∀ q', q' ≠ q → H q' = H' q') → RB log q H = RB log q H') (n : ℕ) :
    ((tapes S D.length).filter fun T => ∃ i < n, TableHit D next RB T i).card ≤
      n * b * S.card ^ (D.length - 1) := by
  have step : ∀ i, ((tapes S D.length).filter fun T => TableHit D next RB T i).card ≤
      b * S.card ^ (D.length - 1) := by
    intro i
    set E := (tapes S D.length).filter fun T => TableHit D next RB T i
    set qi : List F → Transcript F := fun T => next (tableRun next (tableAns D T) i)
    have hres : E.card * S.card ≤ b * S.card ^ D.length := by
      refine card_resample_le S D.length E (filter_subset _ _) (fun T => D.idxOf (qi T))
        (fun T => RB (tableRun next (tableAns D T) i) (qi T) (tableAns D T)) b
        (fun T => hb _ _ _) ?_ ?_
      · intro T hT
        obtain ⟨hTt, hD, -, hbad⟩ := mem_filter.1 hT
        have hlt : D.idxOf (qi T) < T.length := by
          rw [(mem_tapes hTt).1]
          exact List.idxOf_lt_length_of_mem hD
        refine ⟨hlt, ?_⟩
        have hans : tableAns D T (qi T) = T[D.idxOf (qi T)] := by
          simp [tableAns, List.getElem?_eq_getElem hlt]
        rw [← hans]
        exact hbad
      · intro T hT x _
        obtain ⟨-, hD, hfresh, -⟩ := mem_filter.1 hT
        have hH : ∀ q', q' ≠ qi T → tableAns D T q' = tableAns D (T.set (D.idxOf (qi T)) x) q' :=
          fun q' hq' => (tableAns_set hD T x hq').symm
        have hrun := tableRun_congr next hH i hfresh
        have hq : qi (T.set (D.idxOf (qi T)) x) = qi T := by
          simp only [qi]
          rw [← hrun]
        refine ⟨by simp only [hq], ?_⟩
        show RB (tableRun next _ i) (qi _) _ = RB (tableRun next _ i) (qi T) _
        rw [hq, ← hrun]
        exact (hRB _ _ _ _ hH).symm
    rcases Nat.eq_zero_or_pos D.length with h0 | hD
    · have hE : E = ∅ := by
        refine filter_eq_empty_iff.2 fun T _ h => ?_
        rw [List.length_eq_zero_iff.1 h0] at h
        exact List.not_mem_nil h.1
      simp [hE]
    rcases Nat.eq_zero_or_pos S.card with hS | hS
    · have : tapes S D.length = ∅ := by
        rw [← card_eq_zero, card_tapes, hS, zero_pow hD.ne']
      simp [E, this]
    obtain ⟨m, hm⟩ : ∃ m, D.length = m + 1 := ⟨D.length - 1, by omega⟩
    rw [hm, pow_succ, ← mul_assoc] at hres
    rw [hm, Nat.add_sub_cancel]
    exact Nat.le_of_mul_le_mul_right hres hS
  calc ((tapes S D.length).filter fun T => ∃ i < n, TableHit D next RB T i).card
      ≤ ((range n).biUnion fun i => (tapes S D.length).filter fun T =>
        TableHit D next RB T i).card
        := by
        refine card_le_card fun T hT => ?_
        obtain ⟨hTt, i, hi, h⟩ := mem_filter.1 hT
        exact mem_biUnion.2 ⟨i, mem_range.2 hi, mem_filter.2 ⟨hTt, h⟩⟩
    _ ≤ ∑ i ∈ range n, ((tapes S D.length).filter fun T => TableHit D next RB T i).card :=
        card_biUnion_le
    _ ≤ ∑ _i ∈ range n, b * S.card ^ (D.length - 1) := sum_le_sum fun i _ => step i
    _ = n * b * S.card ^ (D.length - 1) := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-! ## The sponge's queries -/

/-- Rounds as the sponge absorbs them : each message, then the number of elements
squeezed after it. -/
def spongeRounds : List (FSMessage F × ℕ) → Transcript F
  | [] => []
  | (m, n) :: ms => m :: FSMessage.size n :: spongeRounds ms

theorem spongeRounds_append : ∀ ms ms' : List (FSMessage F × ℕ),
    spongeRounds (ms ++ ms') = spongeRounds ms ++ spongeRounds ms'
  | [], _ => rfl
  | (m, n) :: ms, ms' => by simp [spongeRounds, spongeRounds_append ms ms']

theorem spongeRounds_injective : ∀ {ms ms' : List (FSMessage F × ℕ)},
    spongeRounds ms = spongeRounds ms' → ms = ms'
  | [], [], _ => rfl
  | [], (_, _) :: _, h => by simp [spongeRounds] at h
  | (_, _) :: _, [], h => by simp [spongeRounds] at h
  | (m, n) :: ms, (m', n') :: ms', h => by
    simp only [spongeRounds, List.cons.injEq, FSMessage.size.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rw [spongeRounds_injective h]

/-- The rounds of the shape `ps` after the shape `pre`, each element read off `H` at the
statement `I` followed by the sponge state before it. -/
def readRounds (H : Transcript F → F) (I : Transcript F) :
    List (FSMessage F × ℕ) → List (FSMessage F × ℕ) → List (Round F)
  | _, [] => []
  | pre, (m, n) :: ps =>
    (m, (List.range n).map fun j => H (I ++ spongeRounds (pre ++ [(m, j)]))) ::
      readRounds H I (pre ++ [(m, n)]) ps

theorem readRounds_append (H : Transcript F → F) (I : Transcript F) :
    ∀ pre ps ps' : List (FSMessage F × ℕ),
      readRounds H I pre (ps ++ ps') = readRounds H I pre ps ++ readRounds H I (pre ++ ps) ps'
  | _, [], _ => by simp [readRounds]
  | pre, (m, n) :: ps, ps' => by
    simp [readRounds, readRounds_append H I (pre ++ [(m, n)]) ps ps']

theorem length_readRounds (H : Transcript F → F) (I : Transcript F) :
    ∀ pre ps : List (FSMessage F × ℕ), (readRounds H I pre ps).length = ps.length
  | _, [] => rfl
  | pre, (m, n) :: ps => by simp [readRounds, length_readRounds H I _ ps]

theorem map_fst_readRounds (H : Transcript F → F) (I : Transcript F) :
    ∀ pre ps : List (FSMessage F × ℕ), (readRounds H I pre ps).map Prod.fst = ps.map Prod.fst
  | _, [] => rfl
  | pre, (m, n) :: ps => by simp [readRounds, map_fst_readRounds H I _ ps]

theorem readRounds_congr {H H' : Transcript F → F} (I : Transcript F) {q : Transcript F}
    (hH : ∀ q', q' ≠ q → H q' = H' q') :
    ∀ pre ps : List (FSMessage F × ℕ), (∀ ps₁ m n ps₂, ps = ps₁ ++ (m, n) :: ps₂ → ∀ j < n,
      I ++ spongeRounds (pre ++ ps₁ ++ [(m, j)]) ≠ q) →
      readRounds H I pre ps = readRounds H' I pre ps
  | _, [], _ => rfl
  | pre, (m, n) :: ps, h => by
    simp only [readRounds, List.cons.injEq, Prod.mk.injEq, true_and]
    refine ⟨List.map_congr_left fun j hj => hH _ ?_,
      readRounds_congr I hH _ ps fun ps₁ m' n' ps₂ hps j hj => ?_⟩
    · simpa using h [] m n ps rfl j (by simpa using hj)
    · simpa using h ((m, n) :: ps₁) m' n' ps₂ (by rw [hps]; rfl) j hj

/-- An element's history reads the oracle only off the states of earlier elements. -/
theorem readRounds_history_congr {H H' : Transcript F → F} (I : Transcript F)
    (ps : List (FSMessage F × ℕ)) (m : FSMessage F) (j : ℕ)
    (hH : ∀ q', q' ≠ I ++ spongeRounds (ps ++ [(m, j)]) → H q' = H' q') :
    readRounds H I [] (ps ++ [(m, j)]) = readRounds H' I [] (ps ++ [(m, j)]) := by
  refine readRounds_congr I hH [] _ fun ps₁ m' n' ps₂ hps j' hj' heq => ?_
  have h := spongeRounds_injective (List.append_cancel_left heq)
  simp only [List.nil_append] at h
  obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.singleton_inj.1 h2)
  have h3 := List.append_cancel_left hps
  simp only [List.cons.injEq, Prod.mk.injEq, true_and] at h3
  omega

open Classical in
/-- A bad set on statements and histories, read off a sponge query : decode the query as
a well-formed statement's encoding followed by a sponge state, and read the history of
that state's element off `H`. -/
noncomputable def spongeBad {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (RB : Stmt → List (Round F) → Finset F) (q : Transcript F) (H : Transcript F → F) :
    Finset F :=
  if h : ∃ x : Stmt × List (FSMessage F × ℕ), WF x.1 ∧ q = enc x.1 ++ spongeRounds x.2 then
    RB h.choose.1 (readRounds H (enc h.choose.1) [] h.choose.2)
  else ∅

theorem spongeBad_eq {Stmt : Type*} {enc : Stmt → Transcript F} {WF : Stmt → Prop}
    (hinj : ∀ s s' X X', WF s → WF s' → enc s ++ X = enc s' ++ X' → s = s' ∧ X = X')
    (RB : Stmt → List (Round F) → Finset F) {s : Stmt} (hs : WF s)
    (ps : List (FSMessage F × ℕ)) (H : Transcript F → F) :
    spongeBad enc WF RB (enc s ++ spongeRounds ps) H = RB s (readRounds H (enc s) [] ps) := by
  have h : ∃ x : Stmt × List (FSMessage F × ℕ), WF x.1 ∧
      enc s ++ spongeRounds ps = enc x.1 ++ spongeRounds x.2 := ⟨(s, ps), hs, rfl⟩
  rw [spongeBad, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  obtain ⟨e1, e2⟩ := hinj _ _ _ _ hs h1 h2
  rw [← e1, ← spongeRounds_injective e2]

theorem card_spongeBad_le {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    {RB : Stmt → List (Round F) → Finset F} {S : Finset F} {b : ℕ}
    (hb : ∀ s rs, (S.filter (· ∈ RB s rs)).card ≤ b) (q : Transcript F)
    (H : Transcript F → F) : (S.filter (· ∈ spongeBad enc WF RB q H)).card ≤ b := by
  unfold spongeBad
  split
  · exact hb _ _
  · simp

/-- The bad set of a sponge query reads the oracle only off other queries. -/
theorem spongeBad_congr {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (RB : Stmt → List (Round F) → Finset F) (q : Transcript F) {H H' : Transcript F → F}
    (hH : ∀ q', q' ≠ q → H q' = H' q') :
    spongeBad enc WF RB q H = spongeBad enc WF RB q H' := by
  unfold spongeBad
  split
  · next h =>
    obtain ⟨-, hq⟩ := h.choose_spec
    congr 1
    rcases List.eq_nil_or_concat h.choose.2 with hn | ⟨ps, mj, hps⟩
    · rw [hn]
      rfl
    · rw [List.concat_eq_append] at hps
      rw [hps]
      obtain ⟨m, j⟩ := mj
      rw [hq, hps] at hH
      exact readRounds_history_congr _ ps m j hH
  · rfl

/-! ## The V3 batch against the sponge -/

/-- The V3 init followed by anything decodes the statement. -/
theorem v3Init_append_inj {s s' : V3Stmt F} {X X' : Transcript F} (hs : V3StmtWF s)
    (hs' : V3StmtWF s') (h : v3Init s.1 s.2 ++ X = v3Init s'.1 s'.2 ++ X') : s = s' ∧ X = X' := by
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
  exact ⟨rfl, List.append_cancel_left h⟩

/-- The element states of the shape `ps` after `pre`, in order, after the statement `I`. -/
def elemQueries (I : Transcript F) :
    List (FSMessage F × ℕ) → List (FSMessage F × ℕ) → List (Transcript F)
  | _, [] => []
  | pre, (m, n) :: ps =>
    (List.range n).map (fun j => I ++ spongeRounds (pre ++ [(m, j)])) ++
      elemQueries I (pre ++ [(m, n)]) ps

theorem length_elemQueries (I : Transcript F) :
    ∀ pre ps : List (FSMessage F × ℕ), (elemQueries I pre ps).length = (ps.map Prod.snd).sum
  | _, [] => rfl
  | pre, (m, n) :: ps => by simp [elemQueries, length_elemQueries I _ ps]

theorem mem_elemQueries (I : Transcript F) :
    ∀ (pre ps₁ : List (FSMessage F × ℕ)) (m : FSMessage F) (n : ℕ) (ps₂ : List (FSMessage F × ℕ)),
      ∀ j < n, I ++ spongeRounds (pre ++ ps₁ ++ [(m, j)]) ∈ elemQueries I pre (ps₁ ++ (m, n) :: ps₂)
  | pre, [], m, n, ps₂, j, hj => by
    simp only [List.nil_append, elemQueries, List.mem_append, List.mem_map, List.mem_range,
      List.append_nil]
    exact Or.inl ⟨j, hj, rfl⟩
  | pre, (m', n') :: ps₁, m, n, ps₂, j, hj => by
    simp only [List.cons_append, elemQueries, List.mem_append]
    refine Or.inr ?_
    simpa using mem_elemQueries I (pre ++ [(m', n')]) ps₁ m n ps₂ j hj

namespace OracleProver

variable (A : OracleProver F) (cnt : V3Stmt F → V2Challenge → ℕ) (Q : ℕ)

/-- The statement prefix after `A`'s log. -/
def spongeInit (log : QueryLog F) : Transcript F :=
  v3Init (A.stmt log).1 (A.stmt log).2

/-- The squeezes after `A`'s log, each message with its number of elements. -/
def spongeShape (log : QueryLog F) : List (FSMessage F × ℕ) :=
  v2Challenges.map fun c => ((A.out log).msgBefore c, cnt (A.stmt log) c)

/-- The sponge state before element `j` of squeeze `c`, after the statement. -/
def spongeQuery (log : QueryLog F) (c : V2Challenge) (j : ℕ) : Transcript F :=
  A.spongeInit log ++
    spongeRounds ((A.spongeShape cnt log).take (c.prefixAbsorbs - 1) ++ [((A.out log).msgBefore c, j)])

/-- The verifier's challenges after `A`'s log : each element the oracle's answer at its
sponge state. -/
def spongeChal (H : Transcript F → F) (log : QueryLog F) (c : V2Challenge) : List F :=
  (List.range (cnt (A.stmt log) c)).map fun j => H (A.spongeQuery cnt log c j)

/-- `A`'s `Q` queries, then the verifier's, one per element at its sponge state. -/
def spongeNext (log : QueryLog F) : Transcript F :=
  if log.length < Q then A.next log
  else (elemQueries (A.spongeInit (log.take Q)) [] (A.spongeShape cnt (log.take Q))).getD
    (log.length - Q) []

/-- On the table `T`, `A`'s output after its `Q` queries fools the verifier. -/
def SpongeFools (D : List (Transcript F)) (S : Finset F) (T : List F) : Prop :=
  V3Batch.Fools S (A.stmt (tableRun A.next (tableAns D T) Q))
    (A.batch (tableRun A.next (tableAns D T) Q)) (A.out (tableRun A.next (tableAns D T) Q))
    (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))

theorem spongeShape_split (log : QueryLog F) (c : V2Challenge) :
    A.spongeShape cnt log = (A.spongeShape cnt log).take (c.prefixAbsorbs - 1) ++
      ((A.out log).msgBefore c, cnt (A.stmt log) c) ::
        (A.spongeShape cnt log).drop c.prefixAbsorbs := by
  cases c <;> rfl

theorem spongeQuery_mem (log : QueryLog F) (c : V2Challenge) {j : ℕ} (hj : j < cnt (A.stmt log) c) :
    A.spongeQuery cnt log c j ∈ elemQueries (A.spongeInit log) [] (A.spongeShape cnt log) := by
  have := mem_elemQueries (A.spongeInit log) [] ((A.spongeShape cnt log).take (c.prefixAbsorbs - 1))
    ((A.out log).msgBefore c) _ ((A.spongeShape cnt log).drop c.prefixAbsorbs) j hj
  rw [List.nil_append, ← A.spongeShape_split cnt log c] at this
  exact this

theorem history_spongeChal (H : Transcript F → F) (log : QueryLog F) (c : V2Challenge) {j : ℕ}
    (hj : j ≤ cnt (A.stmt log) c) :
    (A.out log).history (A.spongeChal cnt H log) c j =
      readRounds H (A.spongeInit log) []
        ((A.spongeShape cnt log).take (c.prefixAbsorbs - 1) ++ [((A.out log).msgBefore c, j)]) := by
  have hr : (A.out log).rounds (A.spongeChal cnt H log) =
      readRounds H (A.spongeInit log) [] (A.spongeShape cnt log) := by
    simp [V2Transcript.rounds, spongeChal, spongeQuery, spongeShape, v2Challenges, readRounds,
      V2Challenge.prefixAbsorbs]
  have hlen : ((A.spongeShape cnt log).take (c.prefixAbsorbs - 1)).length =
      c.prefixAbsorbs - 1 := by
    cases c <;> simp [spongeShape, v2Challenges, V2Challenge.prefixAbsorbs]
  rw [V2Transcript.history, hr, A.spongeShape_split cnt log c, readRounds_append, readRounds_append,
    List.nil_append, List.take_append_of_le_length (by rw [length_readRounds, hlen]),
    List.take_of_length_le (by rw [length_readRounds, hlen]), ← A.spongeShape_split cnt log c]
  simp only [readRounds, spongeChal, spongeQuery, List.nil_append, ← List.map_take, List.take_range,
    Nat.min_eq_left hj]

end OracleProver

variable {G1 : Type*} [AddCommGroup G1] [Module F G1]

namespace AlgebraicProver

variable (A : AlgebraicProver F) (Q : ℕ)

/-- The batch represented with the query after `log` : `A.rep log` for one of `A`'s
queries, `A`'s output batch for the verifier's. -/
def spongeRep (log : QueryLog F) : V3Batch F :=
  if log.length < Q then A.rep log else A.batch (log.take Q)

/-- On the table `T`, a batch `A` represents with one of its queries and its output
batch have two different polynomials with the same value at `τ` among what the first
`k` messages fix. -/
def SpongeClashes (D : List (Transcript F)) (τ : F) (T : List F) : Prop :=
  ∃ m < Q, ∃ k, Clash τ ((A.rep (tableRun A.next (tableAns D T) m)).absorbed k).committed
    ((A.batch (tableRun A.next (tableAns D T) Q)).absorbed k).committed

/-- A clash is a trapdoor break. -/
theorem SpongeClashes.trapdoorBreak {D : List (Transcript F)} {τ : F} {T : List F}
    (h : A.SpongeClashes Q D τ T) : ∃ br : TrapdoorBreak F, br.holds τ := by
  obtain ⟨_, _, _, hc⟩ := h
  exact Varuna.Clash.trapdoorBreak hc

end AlgebraicProver

namespace V3Batch

/-- Fiat–Shamir knowledge soundness of the V3 batch against an algebraic prover and
the sponge's queries, counting form.

The oracle is a table on the domain `D`, which holds the verifier's sponge states on
every table. The prover `A` makes `Q` queries; with each one that decodes as a
statement followed by sponge rounds whose messages encode some batch, it gives a batch
representing them (`rep`), as in `algebraic_soundness`. The verifier squeezes
`cnt s c` elements for each squeeze `c` of the statement `s`, at most `V` in all, each
the table's answer at its sponge state. Then at most `(Q + V) · b · | S | ^(n-1)` of the
` | S | ^n` tables, `n` the length of `D`, give an output the verifier accepts while the
relation fails and no represented batch clashes with the output batch; a clash is a trapdoor break
(`AlgebraicProver.SpongeClashes.trapdoorBreak`). -/
theorem sponge_soundness (S : Finset F) {b : ℕ} (hb : 1 ≤ b) (A : AlgebraicProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ) (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V)
    (D : List (Transcript F))
    (hD : ∀ T ∈ tapes S D.length, ∀ q ∈ elemQueries (A.spongeInit (tableRun A.next (tableAns D T) Q))
      [] (A.spongeShape cnt (tableRun A.next (tableAns D T) Q)), q ∈ D)
    (g : G1) (hg : g ≠ 0) (τ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g τ = (P'.absorbed k).commitments g τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s ps (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds ps → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log))
    (hdeg : ∀ log chal, ((A.batch log).withChallenges chal).ResidualsBounded chal b)
    [DecidablePred fun T => A.SpongeFools cnt Q D S T ∧ ¬A.SpongeClashes Q D τ T] :
    ((tapes S D.length).filter fun T =>
        A.SpongeFools cnt Q D S T ∧ ¬A.SpongeClashes Q D τ T).card ≤
      (Q + V) * b * S.card ^ (D.length - 1) := by
  classical
  refine (card_le_card fun T hT => ?_).trans (table_charge D S (A.spongeNext cnt Q)
    (fun log q H => spongeBad (fun s : V3Stmt F => v3Init s.1 s.2) V3StmtWF
      (fun _ hist => repBad S b (A.spongeRep Q log) hist) q H) b
    (fun _ q H => card_spongeBad_le _ _ (fun _ _ => card_repBad_le S b _ _) q H)
    (fun _ q _ _ hH => spongeBad_congr _ _ _ q hH) (Q + V))
  obtain ⟨hTt, ⟨hacc, hnot⟩, hnc⟩ := mem_filter.1 hT
  refine mem_filter.2 ⟨hTt, ?_⟩
  unfold TableHit
  set H := tableAns D T
  set L := tableRun A.next H Q
  set chal := A.spongeChal cnt H L
  -- A squeezed element in its bad set.
  have hbr : outputBreaks (prefixBad (A.out L) ((A.batch L).badAt S chal)) (A.out L) chal =
      true := by
    by_contra hne
    exact hnot (holds_of_accepts hacc (Bool.eq_false_iff.mpr hne))
  obtain ⟨c, -, hc⟩ := List.any_eq_true.mp hbr
  obtain ⟨j, hj, hbad⟩ := (hitsB_iff _ _ _).mp hc
  rw [List.nil_append, prefixBad_elemBefore hacc.msg] at hbad
  have hjc : j < cnt (A.stmt L) c := by simpa [chal, OracleProver.spongeChal] using hj
  set ps := (A.spongeShape cnt L).take (c.prefixAbsorbs - 1) ++ [((A.out L).msgBefore c, j)]
  set q := A.spongeQuery cnt L c j
  have hHq : chal c = (List.range (cnt (A.stmt L) c)).map fun j => H (A.spongeQuery cnt L c j) :=
    rfl
  have hqj : (chal c)[j] = H q := by simp [hHq, q]
  have hhist := A.history_spongeChal cnt H L c hjc.le
  -- The verifier asks `q`.
  have hnext : ∀ log : QueryLog F, log.length < Q → A.spongeNext cnt Q log = A.next log :=
    fun _ h => if_pos h
  have hrunQ : tableRun (A.spongeNext cnt Q) H Q = L := tableRun_congr_next hnext H Q le_rfl
  have hmem := A.spongeQuery_mem cnt L c hjc
  obtain ⟨p, hp, hpq⟩ := List.getElem_of_mem hmem
  have hpV : p < V := by
    rw [length_elemQueries] at hp
    have hsum : ((A.spongeShape cnt L).map Prod.snd).sum = (v2Challenges.map (cnt (A.stmt L))).sum :=
      by simp [OracleProver.spongeShape, Function.comp_def]
    exact lt_of_lt_of_le (hsum ▸ hp) (hV _)
  have hask : ∃ i, i < Q + V ∧ A.spongeNext cnt Q (tableRun (A.spongeNext cnt Q) H i) = q := by
    refine ⟨Q + p, by omega, ?_⟩
    have hlen := length_tableRun (A.spongeNext cnt Q) H (Q + p)
    have htake : (tableRun (A.spongeNext cnt Q) H (Q + p)).take Q = L := by
      rw [take_tableRun _ _ (by omega), hrunQ]
    rw [OracleProver.spongeNext, if_neg (by omega), htake, hlen, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ hp, hpq]
  obtain ⟨hi0, hq0⟩ := Nat.find_spec hask
  have hmin : ∀ i < Nat.find hask, A.spongeNext cnt Q (tableRun (A.spongeNext cnt Q) H i) ≠ q :=
    fun i hi h => Nat.find_min hask hi ⟨by omega, h⟩
  refine ⟨Nat.find hask, hi0, by rw [hq0]; exact hD T hTt q hmem, fun i hi => by
    rw [hq0]; exact hmin i hi, ?_⟩
  rw [hq0]
  -- Its bad set is the output batch's at the element.
  set log0 := tableRun (A.spongeNext cnt Q) H (Nat.find hask)
  have hlog0 : log0.length = Nat.find hask := length_tableRun _ _ _
  have hP : ((A.spongeRep Q log0).absorbed c.prefixAbsorbs).normal =
      ((A.batch L).absorbed c.prefixAbsorbs).normal := by
    unfold AlgebraicProver.spongeRep
    rw [hlog0]
    split_ifs with hlt
    · have hrun0 : log0 = tableRun A.next H (Nat.find hask) := tableRun_congr_next hnext H _ hlt.le
      have hq' : A.next log0 = v3Init (A.stmt L).1 (A.stmt L).2 ++ spongeRounds ps := by
        rw [← hnext _ (by rw [hlog0]; exact hlt)]
        exact hq0
      have hk : ps.length = c.prefixAbsorbs := by
        rw [← length_readRounds H (A.spongeInit L) [] ps, ← hhist, V2Transcript.length_history]
      have hm : ps.map Prod.fst = msgs ps.length (A.batch L) := by
        rw [← map_fst_readRounds H (A.spongeInit L) [] ps, ← hhist, V2Transcript.map_fst_history,
          (hout L).2, hk]
      obtain ⟨hidx, hmsg⟩ := hrep _ (A.stmt L) ps (A.batch L) (by rw [hlog0]; exact hlt) hq'
        (hstmt L).2 (hout L).1 hm
      rw [hm, hk] at hmsg
      obtain ⟨hshape, hcom⟩ := hmsgs _ _ _ (hidx.trans (hout L).1.symm) hmsg.symm
      refine normal_eq_of hshape (eq_of_not_clash (map_eval_eq_of_commitments hg hcom) ?_)
      intro hcl
      exact hnc ⟨Nat.find hask, hlt, c.prefixAbsorbs, by rw [← hrun0]; exact hcl⟩
    · rw [take_tableRun _ _ (by omega), hrunQ]
  have hsb : spongeBad (fun s : V3Stmt F => v3Init s.1 s.2) V3StmtWF
      (fun _ hist => repBad S b (A.spongeRep Q log0) hist) q H =
        repBad S b (A.spongeRep Q log0) ((A.out L).history chal c j) :=
    (spongeBad_eq (enc := fun s : V3Stmt F => v3Init s.1 s.2) (WF := V3StmtWF)
      (fun _ _ _ _ hs hs' h => v3Init_append_inj hs hs' h) _ (hstmt L).2 ps H).trans
      (congrArg (repBad S b (A.spongeRep Q log0)) hhist).symm
  show H q ∈ spongeBad (fun s : V3Stmt F => v3Init s.1 s.2) V3StmtWF
    (fun _ hist => repBad S b (A.spongeRep Q log0) hist) q H
  rw [hsb, repBad_history hP S b (A.out L) chal j (card_badAt_le hb (hdeg _ _) S c _), ← hqj]
  exact hbad

/-- `sponge_soundness` with `b` computed from `DegreeBounds`, as in
`adaptive_soundness_concrete`. -/
theorem sponge_soundness_concrete (S : Finset F) (d : DegreeBounds) (hX : 1 ≤ d.X)
    (A : AlgebraicProver F) (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ)
    (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V) (D : List (Transcript F))
    (hD : ∀ T ∈ tapes S D.length, ∀ q ∈ elemQueries (A.spongeInit (tableRun A.next (tableAns D T) Q))
      [] (A.spongeShape cnt (tableRun A.next (tableAns D T) Q)), q ∈ D)
    (g : G1) (hg : g ≠ 0) (τ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g τ = (P'.absorbed k).commitments g τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s ps (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds ps → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log))
    (hW : ∀ log, (A.batch log).Within d)
    [DecidablePred fun T => A.SpongeFools cnt Q D S T ∧ ¬A.SpongeClashes Q D τ T] :
    ((tapes S D.length).filter fun T =>
        A.SpongeFools cnt Q D S T ∧ ¬A.SpongeClashes Q D τ T).card ≤
      (Q + V) * d.b * S.card ^ (D.length - 1) :=
  sponge_soundness S d.one_le_b A cnt Q V hV D hD g hg τ msgs hmsgs idx hstmt hout hrep
    fun log chal => ((hW log).withChallenges chal).residualsBounded hX chal

end V3Batch

end Varuna