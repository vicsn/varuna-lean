/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Mathlib.Data.List.GetD
import Varuna.Probability

/-!
# Several weights from one squeeze

snarkVM draws a round's batch weights one field element after another, with
no absorb in between : the instance combiners `τ_{i,j}` and circuit
combiners `ν_i` of `sample_batch_combiners` (`verifier.rs:50-76`), then the
`η`s (`verifier.rs:193-208`), and the `δ`s (`verifier.rs:241-246`). Each
weight is a product of drawn elements (`ν_i τ_{i,j}` for the rowcheck), so a
combination of claims is affine in each drawn element with the others fixed
(`CoordAffine`).

Round by round over the drawn elements : a prefix is *live* when some
completion leaves the combination nonzero somewhere on the domain. At most
one next element ends liveness (`WeightDraw.card_bad_le_one`), and a lucky
draw, one that cancels a live combination on the whole domain, passes a step
that does (`WeightDraw.exists_bad_of_lucky`). Over all tapes, `k` drawn
elements are lucky on at most `k · | S | ^{k-1}` (`WeightDraw.card_lucky_le`).

Weights are monomials in the drawn elements (`schemeWeights`). If no two
monomials use the same positions, a live claim makes the start live
(`exists_weightedSum_scheme_ne_zero`), so `inspectBatchOn`'s lucky event is a
lucky draw. `combinerScheme` is snarkVM's `ν_i τ_{i,j}`, `prepareThirdScheme`
multiplies in the `η`s, and `flatScheme` is the `δ`s.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Round by round over the drawn elements -/

/-- `p` is affine in each drawn element, the others fixed. -/
def CoordAffine (p : List F → F) : Prop :=
  ∀ pre rest : List F, ∃ A B : F, ∀ u, p (pre ++ u :: rest) = A + u * B

/-- `k` drawn elements weighting claims on the points `D` : `comb x ws` is the
combination at `x` once `ws` is drawn. -/
structure WeightDraw (F : Type*) where
  /-- Number of drawn elements. -/
  k : ℕ
  /-- Points the combination is checked on. -/
  D : List F
  /-- The combination at a point, given the drawn elements. -/
  comb : F → List F → F

namespace WeightDraw

/-- Some completion of the drawn prefix `pre` leaves the combination nonzero on `D`. -/
def Live (d : WeightDraw F) (pre : List F) : Prop :=
  ∃ rest : List F, (pre ++ rest).length = d.k ∧ ∃ x ∈ d.D, d.comb x (pre ++ rest) ≠ 0

/-- The drawn elements `ws` cancel a live combination on all of `D`. -/
def Lucky (d : WeightDraw F) (ws : List F) : Prop :=
  ws.length = d.k ∧ d.Live [] ∧ ∀ x ∈ d.D, d.comb x ws = 0

/-- Next elements of `S` that end liveness after the drawn prefix `pre`. -/
noncomputable def bad (d : WeightDraw F) (S : Finset F) (pre : List F) : Finset F := by
  classical
  exact S.filter fun v => pre.length < d.k ∧ d.Live pre ∧ ¬d.Live (pre ++ [v])

theorem mem_bad {d : WeightDraw F} {S : Finset F} {pre : List F} {v : F} :
    v ∈ d.bad S pre ↔
      v ∈ S ∧ pre.length < d.k ∧ d.Live pre ∧ ¬d.Live (pre ++ [v]) := by
  classical
  unfold bad
  exact mem_filter

/-- At most one next element ends liveness : two would make the combination
constant zero in that element, on a completion where it is nonzero. -/
theorem card_bad_le_one (d : WeightDraw F) (hd : ∀ x ∈ d.D, CoordAffine (d.comb x))
    (S : Finset F) (pre : List F) : (d.bad S pre).card ≤ 1 := by
  refine card_le_one.mpr fun v hv v' hv' => ?_
  obtain ⟨-, hlt, ⟨rest, hlen, x, hx, hne⟩, hdead⟩ := mem_bad.mp hv
  obtain ⟨-, -, -, hdead'⟩ := mem_bad.mp hv'
  obtain ⟨u, rest, rfl⟩ : ∃ u rest', rest = u :: rest' := by
    rcases rest with _ | ⟨u, rest'⟩
    · simp at hlen
      omega
    · exact ⟨u, rest', rfl⟩
  obtain ⟨A, B, hAB⟩ := hd x hx pre rest
  have hzero : ∀ w, ¬d.Live (pre ++ [w]) → A + w * B = 0 := by
    intro w hw
    by_contra h
    refine hw ⟨rest, by simp at hlen ⊢; omega, x, hx, ?_⟩
    rwa [List.append_assoc, List.singleton_append, hAB]
  have h₁ := hzero v hdead
  have h₂ := hzero v' hdead'
  by_contra hvv
  have hB : B = 0 := by
    have h : (v - v') * B = 0 := by linear_combination h₁ - h₂
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hvv)
  apply hne
  rw [hAB, hB]
  simpa [hB] using h₁

/-- A lucky draw passes a step that ends liveness : the start is live and the
full draw is not. -/
theorem exists_bad_of_lucky (d : WeightDraw F) {S : Finset F} {ws : List F} (hl : d.Lucky ws)
    (hS : ∀ a ∈ ws, a ∈ S) : ∃ j, ∃ h : j < ws.length, ws[j] ∈ d.bad S (ws.take j) := by
  classical
  obtain ⟨hlen, hlive, hzero⟩ := hl
  have hend : ¬d.Live (ws.take ws.length) := by
    rw [List.take_length]
    rintro ⟨rest, hrest, x, hx, hne⟩
    have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hrest; omega)
    subst hnil
    rw [List.append_nil] at hne
    exact hne (hzero x hx)
  have hex : ∃ m, ¬d.Live (ws.take m) := ⟨_, hend⟩
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero fun h0 =>
    Nat.find_spec hex (by rw [h0, List.take_zero]; exact hlive)
  have hle : Nat.find hex ≤ ws.length := Nat.find_min' hex hend
  have hjlt : j < ws.length := by omega
  refine ⟨j, hjlt, mem_bad.mpr ⟨hS _ (List.getElem_mem hjlt), by simp; omega,
    not_not.mp (Nat.find_min hex (by omega)), ?_⟩⟩
  have hfind := Nat.find_spec hex
  rwa [hj, List.take_add_one, List.getElem?_eq_getElem hjlt, Option.toList_some] at hfind

/-- Over all tapes of `k` drawn elements, at most `k · | S | ^{k-1}` are lucky. -/
theorem card_lucky_le (d : WeightDraw F) (hd : ∀ x ∈ d.D, CoordAffine (d.comb x))
    (S : Finset F) [DecidablePred d.Lucky] :
    ((tapes S d.k).filter d.Lucky).card ≤ d.k * S.card ^ (d.k - 1) := by
  have hb : ∀ pre, (S.filter (· ∈ d.bad S pre)).card ≤ (fun _ => 1) pre.length :=
    fun pre => (card_filter_mem_le _ _).trans (d.card_bad_le_one hd S pre)
  refine (card_le_card fun ws hws => ?_).trans
    ((card_hits_le S (d.bad S) (fun _ => 1) hb d.k []).trans (by simp))
  obtain ⟨hmem, hl⟩ := mem_filter.mp hws
  obtain ⟨j, hj, hbad⟩ := d.exists_bad_of_lucky hl (mem_tapes hmem).2
  exact mem_filter.mpr ⟨hmem, (hitsB_iff _ _ _).mpr ⟨j, hj, by simpa using hbad⟩⟩

end WeightDraw

/-! ## Weights as monomials in the drawn elements -/

/-- The product of the drawn elements at the positions `m`; the empty product is
the weight `1`. -/
def monoEval (ws : List F) (m : List ℕ) : F :=
  (m.map fun i => ws.getD i 0).prod

/-- The weights of a scheme of monomials. -/
def schemeWeights (sch : List (List ℕ)) (ws : List F) : List F :=
  sch.map (monoEval ws)

@[simp] theorem monoEval_nil (ws : List F) : monoEval ws [] = 1 :=
  rfl

@[simp] theorem monoEval_cons (ws : List F) (i : ℕ) (m : List ℕ) :
    monoEval ws (i :: m) = ws.getD i 0 * monoEval ws m := by
  simp [monoEval]

theorem coordAffine_const (c : F) : CoordAffine fun _ : List F => c :=
  fun _ _ => ⟨c, 0, fun _ => by ring⟩

theorem CoordAffine.add {p q : List F → F} (hp : CoordAffine p) (hq : CoordAffine q) :
    CoordAffine fun ws => p ws + q ws := by
  intro pre rest
  obtain ⟨A, B, h⟩ := hp pre rest
  obtain ⟨A', B', h'⟩ := hq pre rest
  exact ⟨A + A', B + B', fun u => by dsimp only; rw [h, h']; ring⟩

theorem CoordAffine.mul_const {p : List F → F} (hp : CoordAffine p) (c : F) :
    CoordAffine fun ws => p ws * c := by
  intro pre rest
  obtain ⟨A, B, h⟩ := hp pre rest
  exact ⟨A * c, B * c, fun u => by dsimp only; rw [h]; ring⟩

/-- Away from position `|pre|`, the drawn elements do not see `u`. -/
theorem getD_append_cons_of_ne (pre rest : List F) (u : F) {i : ℕ} (hi : i ≠ pre.length) :
    (pre ++ u :: rest).getD i 0 = (pre ++ 0 :: rest).getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [show pre.length + j + 1 - pre.length = j + 1 by omega]

/-- A monomial in distinct positions is affine in each drawn element. -/
theorem coordAffine_monoEval {m : List ℕ} (hm : m.Nodup) :
    CoordAffine fun ws : List F => monoEval ws m := by
  intro pre rest
  by_cases hq : pre.length ∈ m
  · refine ⟨0, ((m.erase pre.length).map fun i => (pre ++ (0 : F) :: rest).getD i 0).prod,
      fun u => ?_⟩
    dsimp only
    rw [monoEval, ← List.prod_map_erase _ hq,
      List.map_congr_left fun i hi => getD_append_cons_of_ne pre rest u (hm.mem_erase_iff.mp hi).1]
    simp
  · refine ⟨monoEval (pre ++ 0 :: rest) m, 0, fun u => ?_⟩
    dsimp only
    rw [mul_zero, add_zero, monoEval, monoEval,
      List.map_congr_left fun i hi => getD_append_cons_of_ne pre rest u fun h => hq (h ▸ hi)]

theorem coordAffine_weightedSum_map {fs : List (List F → F)} (hfs : ∀ f ∈ fs, CoordAffine f) :
    ∀ c : List F, CoordAffine fun ws => weightedSum (fs.map (· ws)) c := by
  induction fs with
  | nil => intro c; simpa using coordAffine_const (0 : F)
  | cons f fs ih =>
    intro c
    cases c with
    | nil => simpa using coordAffine_const (0 : F)
    | cons a c =>
      simpa using ((hfs f (by simp)).mul_const a).add
        (ih (fun g hg => hfs g (by simp [hg])) c)

/-- A combination with monomial weights in distinct positions is affine in each
drawn element. -/
theorem coordAffine_scheme {sch : List (List ℕ)} (hsch : ∀ m ∈ sch, m.Nodup) (c : List F) :
    CoordAffine fun ws : List F => weightedSum (schemeWeights sch ws) c := by
  have := coordAffine_weightedSum_map (fs := sch.map fun m (ws : List F) => monoEval ws m)
    (by simpa using fun m hm => coordAffine_monoEval (hsch m hm)) c
  simpa [schemeWeights, List.map_map, Function.comp_def] using this

/-- A scheme over `k` drawn elements : every monomial is a set of distinct positions
below `k`, and no two monomials are the same set. -/
structure SchemeValid (k : ℕ) (sch : List (List ℕ)) : Prop where
  nodup : ∀ m ∈ sch, m.Nodup
  lt : ∀ m ∈ sch, ∀ i ∈ m, i < k
  distinct : (sch.map List.toFinset).Nodup

theorem weightedSum_eq_sum_getD : ∀ ws cs : List F,
    weightedSum ws cs = ∑ l ∈ range cs.length, ws.getD l 0 * cs.getD l 0
  | [], cs => by simp
  | _ :: _, [] => by simp
  | w :: ws, c :: cs => by
    rw [weightedSum_cons, weightedSum_eq_sum_getD ws cs, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The tape with `1` at the positions in `T` and `0` elsewhere. -/
def indicatorTape (k : ℕ) (T : List ℕ) : List F :=
  (List.range k).map fun i => if i ∈ T then 1 else 0

theorem monoEval_indicatorTape {k : ℕ} {T : List ℕ} :
    ∀ {m : List ℕ}, (∀ i ∈ m, i < k) →
      monoEval (indicatorTape k T : List F) m = if ∀ i ∈ m, i ∈ T then 1 else 0
  | [], _ => by simp
  | i :: m, hm => by
    have hi : (indicatorTape k T : List F).getD i 0 = if i ∈ T then 1 else 0 := by
      simp [indicatorTape, List.getD_eq_getElem?_getD, hm i (by simp)]
    rw [monoEval_cons, hi, monoEval_indicatorTape fun j hj => hm j (by simp [hj])]
    by_cases hiT : i ∈ T <;> simp [hiT]

theorem getD_schemeWeights {sch : List (List ℕ)} (ws : List F) {l : ℕ} (hl : l < sch.length) :
    (schemeWeights sch ws).getD l 0 = monoEval ws (sch.getD l []) := by
  simp [schemeWeights, List.getD_eq_getElem?_getD, hl]

theorem getD_mem {sch : List (List ℕ)} {l : ℕ} (hl : l < sch.length) :
    sch.getD l [] ∈ sch := by
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem hl

/-- With distinct monomials, a live claim makes the combination nonzero for some
draw : put `1` on the positions of the smallest monomial whose claim is live. -/
theorem exists_weightedSum_scheme_ne_zero {k : ℕ} {sch : List (List ℕ)} (hv : SchemeValid k sch)
    {c : List F} (hlen : c.length ≤ sch.length) (hlive : ∃ a ∈ c, a ≠ 0) :
    ∃ ws : List F, ws.length = k ∧ weightedSum (schemeWeights sch ws) c ≠ 0 := by
  classical
  have hex : ∃ n, ∃ l < c.length, c.getD l 0 ≠ 0 ∧ (sch.getD l []).length = n := by
    obtain ⟨a, ha, hne⟩ := hlive
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
    exact ⟨_, l, hl, by simpa [List.getD_eq_getElem?_getD, hl] using hne, rfl⟩
  obtain ⟨l₀, hl₀, hc₀, hn₀⟩ := Nat.find_spec hex
  have hl₀' : l₀ < sch.length := hl₀.trans_le hlen
  refine ⟨indicatorTape k (sch.getD l₀ []), by simp [indicatorTape], ?_⟩
  rw [weightedSum_eq_sum_getD, sum_eq_single l₀]
  · rw [getD_schemeWeights _ hl₀', monoEval_indicatorTape (hv.lt _ (getD_mem hl₀')),
      if_pos fun _ h => h, one_mul]
    exact hc₀
  · intro l hl hne
    have hl' : l < sch.length := (mem_range.mp hl).trans_le hlen
    by_cases hcl : c.getD l 0 = 0
    · rw [hcl, mul_zero]
    rw [getD_schemeWeights _ hl', monoEval_indicatorTape (hv.lt _ (getD_mem hl')), if_neg,
      zero_mul]
    intro hsub
    have hmin : (sch.getD l₀ []).length ≤ (sch.getD l []).length := by
      rw [hn₀]
      exact Nat.find_min' hex ⟨l, mem_range.mp hl, hcl, rfl⟩
    have heq : (sch.getD l []).toFinset = (sch.getD l₀ []).toFinset := by
      refine eq_of_subset_of_card_le (fun i hi => ?_) ?_
      · simpa using hsub i (by simpa using hi)
      · rw [List.toFinset_card_of_nodup (hv.nodup _ (getD_mem hl₀')),
          List.toFinset_card_of_nodup (hv.nodup _ (getD_mem hl'))]
        exact hmin
    apply hne
    refine (hv.distinct.getElem_inj_iff (i := l) (j := l₀) (hi := by simpa using hl')
      (hj := by simpa using hl₀')).mp ?_
    rw [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hl₀'] at heq
    simpa using heq
  · intro h
    exact absurd (mem_range.mpr hl₀) h

/-- The weights of scheme `sch` on `k` drawn elements, combining `claims x` on `D`. -/
def schemeDraw (k : ℕ) (sch : List (List ℕ)) (D : List F) (claims : F → List F) :
    WeightDraw F where
  k := k
  D := D
  comb x ws := weightedSum (schemeWeights sch ws) (claims x)

theorem schemeDraw_coordAffine {k : ℕ} {sch : List (List ℕ)} (hsch : ∀ m ∈ sch, m.Nodup)
    (D : List F) (claims : F → List F) :
    ∀ x ∈ (schemeDraw k sch D claims).D, CoordAffine ((schemeDraw k sch D claims).comb x) :=
  fun x _ => coordAffine_scheme hsch (claims x)

/-- `inspectBatchOn`'s lucky event on the scheme's weights is a lucky draw. -/
theorem schemeDraw_lucky {k : ℕ} {sch : List (List ℕ)} (hv : SchemeValid k sch) {D : List F}
    {claims : F → List F} (hlen : ∀ x ∈ D, (claims x).length ≤ sch.length) {ws : List F}
    (hws : ws.length = k) (h : inspectBatchOn D (schemeWeights sch ws) claims ≠ none) :
    (schemeDraw k sch D claims).Lucky ws := by
  obtain ⟨hacc, x, hx, a, ha, hne⟩ := (inspectBatchOn_ne_none_iff _ _ _).1 h
  obtain ⟨ws', hws', hne'⟩ := exists_weightedSum_scheme_ne_zero hv (hlen x hx) ⟨a, ha, hne⟩
  exact ⟨hws, ⟨ws', by simpa [schemeDraw] using hws', x, hx, by simpa [schemeDraw] using hne'⟩,
    hacc⟩

/-- Over all tapes of `k` drawn elements, the scheme's weights are lucky on all of
`D` for at most `k · | S | ^{k-1}`. -/
theorem card_filter_inspectBatchOn_scheme_le {k : ℕ} {sch : List (List ℕ)}
    (hv : SchemeValid k sch) (D : List F) (claims : F → List F)
    (hlen : ∀ x ∈ D, (claims x).length ≤ sch.length) (S : Finset F) :
    ((tapes S k).filter fun ws => inspectBatchOn D (schemeWeights sch ws) claims ≠ none).card ≤
      k * S.card ^ (k - 1) := by
  classical
  refine (card_le_card fun ws hws => ?_).trans
    ((schemeDraw k sch D claims).card_lucky_le (schemeDraw_coordAffine hv.nodup D claims) S)
  obtain ⟨hmem, h⟩ := mem_filter.mp hws
  exact mem_filter.mpr ⟨hmem, schemeDraw_lucky hv hlen (mem_tapes hmem).1 h⟩

/-- Scalar claims, as `inspectBatch` combines them : over all tapes of `k` drawn
elements, the scheme's weights are lucky for at most `k · | S | ^{k-1}`. -/
theorem card_filter_inspectBatch_scheme_le {k : ℕ} {sch : List (List ℕ)}
    (hv : SchemeValid k sch) (cs : List F) (hlen : cs.length ≤ sch.length) (S : Finset F) :
    ((tapes S k).filter fun ws => inspectBatch (schemeWeights sch ws) cs ≠ none).card ≤
      k * S.card ^ (k - 1) := by
  refine (card_le_card fun ws hws => ?_).trans
    (card_filter_inspectBatchOn_scheme_le hv [0] (fun _ => cs) (fun _ _ => hlen) S)
  obtain ⟨hmem, h⟩ := mem_filter.mp hws
  obtain ⟨hzero, hlive⟩ := (inspectBatch_ne_none_iff _ _).1 h
  exact mem_filter.mpr ⟨hmem, (inspectBatchOn_ne_none_iff _ _ _).2
    ⟨by simpa using hzero, 0, by simp, hlive⟩⟩

/-! ## snarkVM's schemes -/

/-- `w₀, …, w_{k-1}` : one drawn element per weight (the V3 `η`s). -/
def freeScheme (k : ℕ) : List (List ℕ) :=
  (List.range k).map fun i => [i]

/-- `1, w₀, …, w_{k-1}` : a leading `1`, then one drawn element per weight. -/
def flatScheme (k : ℕ) : List (List ℕ) :=
  [] :: freeScheme k

/-- Monomial `m` read `o` positions further on. -/
def shiftMono (o : ℕ) (m : List ℕ) : List ℕ :=
  m.map (o + ·)

/-- `sch₁` on the first `k₁` drawn elements, then `sch₂` on the rest. -/
def appendScheme (k₁ : ℕ) (sch₁ sch₂ : List (List ℕ)) : List (List ℕ) :=
  sch₁ ++ sch₂.map (shiftMono k₁)

/-- Every product of a weight of `sch₁`, on the first `k₁` drawn elements, and a
weight of `sch₂`, on the rest. -/
def productScheme (k₁ : ℕ) (sch₁ sch₂ : List (List ℕ)) : List (List ℕ) :=
  sch₁.flatMap fun m => sch₂.map fun m' => m ++ shiftMono k₁ m'

theorem schemeWeights_freeScheme (ws : List F) :
    schemeWeights (freeScheme ws.length) ws = ws := by
  refine List.ext_getElem (by simp [schemeWeights, freeScheme]) fun i _ h₂ => ?_
  simp [schemeWeights, freeScheme, List.getElem?_eq_getElem h₂]

theorem schemeWeights_flatScheme (ws : List F) :
    schemeWeights (flatScheme ws.length) ws = 1 :: ws := by
  simp only [flatScheme, schemeWeights, List.map_cons, monoEval_nil]
  exact congrArg _ (schemeWeights_freeScheme ws)

theorem schemeValid_nil (k : ℕ) : SchemeValid k [] :=
  ⟨by simp, by simp, by simp⟩

theorem freeScheme_valid (k : ℕ) : SchemeValid k (freeScheme k) where
  nodup := by simp [freeScheme]
  lt := by simp [freeScheme]
  distinct := by
    rw [freeScheme, List.map_map]
    exact List.nodup_range.map fun i j h => by simpa using h

theorem flatScheme_valid (k : ℕ) : SchemeValid k (flatScheme k) where
  nodup := by simp [flatScheme, freeScheme]
  lt := by simp [flatScheme, freeScheme]
  distinct := by
    rw [flatScheme, List.map_cons, List.nodup_cons]
    exact ⟨by simp [freeScheme], (freeScheme_valid k).distinct⟩

theorem toFinset_shiftMono (o : ℕ) (m : List ℕ) :
    (shiftMono o m).toFinset = m.toFinset.image (o + ·) := by
  ext i
  simp [shiftMono]

/-- Positions below `k₁` and positions shifted past `k₁` never mix. -/
theorem union_image_add_inj {k₁ : ℕ} {A A' B B' : Finset ℕ} (hA : ∀ i ∈ A, i < k₁)
    (hA' : ∀ i ∈ A', i < k₁) (h : A ∪ B.image (k₁ + ·) = A' ∪ B'.image (k₁ + ·)) :
    A = A' ∧ B = B' := by
  have key : ∀ i,
      (i ∈ A ∨ ∃ j ∈ B, k₁ + j = i) ↔ (i ∈ A' ∨ ∃ j ∈ B', k₁ + j = i) := by
    intro i
    simpa using congrArg (i ∈ ·) h
  refine ⟨Finset.ext fun i => ⟨fun hi => ?_, fun hi => ?_⟩,
    Finset.ext fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · rcases (key i).1 (Or.inl hi) with h | ⟨j, -, rfl⟩
    · exact h
    · exact absurd (hA _ hi) (by omega)
  · rcases (key i).2 (Or.inl hi) with h | ⟨j, -, rfl⟩
    · exact h
    · exact absurd (hA' _ hi) (by omega)
  · rcases (key (k₁ + j)).1 (Or.inr ⟨j, hj, rfl⟩) with h | ⟨j', hj', hjj⟩
    · exact absurd (hA' _ h) (by omega)
    · rwa [show j = j' by omega]
  · rcases (key (k₁ + j)).2 (Or.inr ⟨j, hj, rfl⟩) with h | ⟨j', hj', hjj⟩
    · exact absurd (hA _ h) (by omega)
    · rwa [show j = j' by omega]

theorem SchemeValid.append {k₁ k₂ : ℕ} {sch₁ sch₂ : List (List ℕ)} (h₁ : SchemeValid k₁ sch₁)
    (h₂ : SchemeValid k₂ sch₂) (hne : [] ∉ sch₂) :
    SchemeValid (k₁ + k₂) (appendScheme k₁ sch₁ sch₂) where
  nodup := by
    simp only [appendScheme, List.mem_append, List.mem_map]
    rintro m (hm | ⟨m', hm', rfl⟩)
    · exact h₁.nodup m hm
    · exact (h₂.nodup m' hm').map (add_right_injective k₁)
  lt := by
    simp only [appendScheme, List.mem_append, List.mem_map]
    rintro m (hm | ⟨m', hm', rfl⟩) i hi
    · exact (h₁.lt m hm i hi).trans_le (Nat.le_add_right _ _)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have := h₂.lt m' hm' j hj
      omega
  distinct := by
    rw [appendScheme, List.map_append, List.nodup_append, List.map_map]
    refine ⟨h₁.distinct, ?_, ?_⟩
    · have : List.toFinset ∘ shiftMono k₁ =
          (fun s : Finset ℕ => s.image (k₁ + ·)) ∘ List.toFinset := by
        funext m
        simp [toFinset_shiftMono]
      rw [this, ← List.map_map]
      exact h₂.distinct.map (Finset.image_injective (add_right_injective k₁))
    · simp only [List.mem_map, Function.comp_apply]
      rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩ heq
      have hnil : m' = [] := List.eq_nil_iff_forall_not_mem.mpr fun j hj => by
        have hmem : k₁ + j ∈ m.toFinset := heq ▸ by simp [shiftMono, hj]
        have := h₁.lt m hm _ (List.mem_toFinset.mp hmem)
        omega
      exact hne (hnil ▸ hm')

theorem SchemeValid.product {k₁ k₂ : ℕ} {sch₁ sch₂ : List (List ℕ)} (h₁ : SchemeValid k₁ sch₁)
    (h₂ : SchemeValid k₂ sch₂) : SchemeValid (k₁ + k₂) (productScheme k₁ sch₁ sch₂) where
  nodup := by
    simp only [productScheme, List.mem_flatMap, List.mem_map]
    rintro _ ⟨m, hm, m', hm', rfl⟩
    rw [List.nodup_append]
    refine ⟨h₁.nodup m hm, (h₂.nodup m' hm').map (add_right_injective k₁), ?_⟩
    intro i hi j hj
    obtain ⟨j', -, rfl⟩ := List.mem_map.mp hj
    have := h₁.lt m hm i hi
    omega
  lt := by
    simp only [productScheme, List.mem_flatMap, List.mem_map]
    rintro _ ⟨m, hm, m', hm', rfl⟩ i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact (h₁.lt m hm i hi).trans_le (Nat.le_add_right _ _)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have := h₂.lt m' hm' j hj
      omega
  distinct := by
    have hA : ∀ m ∈ sch₁, ∀ i ∈ m.toFinset, i < k₁ :=
      fun m hm i hi => h₁.lt m hm i (List.mem_toFinset.mp hi)
    have hunion : ∀ m m' : List ℕ,
        (m ++ shiftMono k₁ m').toFinset = m.toFinset ∪ m'.toFinset.image (k₁ + ·) := by
      intro m m'
      rw [List.toFinset_append, toFinset_shiftMono]
    rw [productScheme, List.map_flatMap, List.nodup_flatMap]
    refine ⟨fun m hm => ?_, ?_⟩
    · have : (List.toFinset ∘ fun m' => m ++ shiftMono k₁ m') =
          (fun B => m.toFinset ∪ B.image (k₁ + ·)) ∘ List.toFinset := by
        funext m'
        exact hunion m m'
      rw [List.map_map, this, ← List.map_map]
      exact h₂.distinct.map fun B B' h => (union_image_add_inj (hA m hm) (hA m hm) h).2
    · refine (List.pairwise_map.mp h₁.distinct).imp_of_mem fun {m n} hm hn hne X hX hX' => ?_
      simp only [List.map_map, List.mem_map, Function.comp_apply] at hX hX'
      obtain ⟨m', -, rfl⟩ := hX
      obtain ⟨n', -, heq⟩ := hX'
      rw [hunion, hunion] at heq
      exact hne (union_image_add_inj (hA n hn) (hA m hm) heq).1.symm

/-- A circuit after the first, with `m` instances, draws `τ_{i,1}, …, τ_{i,m-1}` and
then `ν_i`; its weights are `ν_i, ν_i τ_{i,1}, …, ν_i τ_{i,m-1}`. -/
def laterCircuitScheme (m : ℕ) : List (List ℕ) :=
  productScheme (m - 1) (flatScheme (m - 1)) (freeScheme 1)

/-- The circuits after the first, in order. -/
def laterCircuitsScheme : List ℕ → List (List ℕ)
  | [] => []
  | m :: ms => appendScheme (m - 1 + 1) (laterCircuitScheme m) (laterCircuitsScheme ms)

/-- Elements the circuits after the first draw. -/
def laterCircuitsDraws : List ℕ → ℕ
  | [] => 0
  | m :: ms => m - 1 + 1 + laterCircuitsDraws ms

/-- snarkVM's batch weights `ν_i τ_{i,j}` for circuits with `sizes` instances each
(`sample_batch_combiners`, `verifier.rs:50-76`) : circuit `i` draws
`τ_{i,1}, …, τ_{i,m_i-1}` and then, after the first circuit, `ν_i`, with
`τ_{i,0} = ν_0 = 1`. The weights run over the instances in order. -/
def combinerScheme : List ℕ → List (List ℕ)
  | [] => []
  | m :: ms => appendScheme (m - 1) (flatScheme (m - 1)) (laterCircuitsScheme ms)

/-- Elements `sample_batch_combiners` draws for circuits with `sizes` instances. -/
def combinerDraws : List ℕ → ℕ
  | [] => 0
  | m :: ms => m - 1 + laterCircuitsDraws ms

/-- Two circuits of two instances draw `τ_{0,1}, τ_{1,1}, ν_1`. -/
theorem combinerScheme_two_two : combinerScheme [2, 2] = [[], [0], [2], [1, 2]] := by
  decide

/-- The four instances of two circuits of two instances are weighted
`1, τ_{0,1}, ν_1, τ_{1,1} ν_1`. -/
theorem schemeWeights_combinerScheme_two_two (τ₀₁ τ₁₁ ν₁ : F) :
    schemeWeights (combinerScheme [2, 2]) [τ₀₁, τ₁₁, ν₁] =
      [1, τ₀₁, ν₁, τ₁₁ * ν₁] := by
  rw [combinerScheme_two_two]
  simp [schemeWeights]

theorem nil_not_mem_laterCircuitScheme (m : ℕ) : [] ∉ laterCircuitScheme m := by
  simp [laterCircuitScheme, productScheme, freeScheme, shiftMono]

theorem nil_not_mem_laterCircuitsScheme : ∀ ms : List ℕ, [] ∉ laterCircuitsScheme ms
  | [] => by simp [laterCircuitsScheme]
  | m :: ms => by
    simp only [laterCircuitsScheme, appendScheme, List.mem_append, List.mem_map, not_or,
      not_exists, not_and]
    refine ⟨nil_not_mem_laterCircuitScheme m, fun m' hm' h => ?_⟩
    have hnil : m' = [] := by simpa [shiftMono] using h
    exact nil_not_mem_laterCircuitsScheme ms (hnil ▸ hm')

theorem laterCircuitScheme_valid (m : ℕ) : SchemeValid (m - 1 + 1) (laterCircuitScheme m) :=
  (flatScheme_valid (m - 1)).product (freeScheme_valid 1)

theorem laterCircuitsScheme_valid :
    ∀ ms : List ℕ, SchemeValid (laterCircuitsDraws ms) (laterCircuitsScheme ms)
  | [] => schemeValid_nil 0
  | m :: ms => (laterCircuitScheme_valid m).append (laterCircuitsScheme_valid ms)
    (nil_not_mem_laterCircuitsScheme ms)

/-- snarkVM's combiners form a valid scheme : no two instances get the same weight. -/
theorem combinerScheme_valid :
    ∀ sizes : List ℕ, SchemeValid (combinerDraws sizes) (combinerScheme sizes)
  | [] => schemeValid_nil 0
  | m :: ms => (flatScheme_valid (m - 1)).append (laterCircuitsScheme_valid ms)
    (nil_not_mem_laterCircuitsScheme ms)

/-- The prepare-third draw (`verifier.rs:193-208`) : the third-round combiners as in
`combinerScheme`, then the `η`s by `etas` (`freeScheme 3` in V3, `flatScheme 2` in
V2). Instance `(i, j)` and matrix `M` are weighted `ν_i τ_{i,j} η_M`. -/
def prepareThirdScheme (sizes : List ℕ) (etas : List (List ℕ)) : List (List ℕ) :=
  productScheme (combinerDraws sizes) (combinerScheme sizes) etas

theorem prepareThirdScheme_valid (sizes : List ℕ) {kη : ℕ} {etas : List (List ℕ)}
    (hη : SchemeValid kη etas) :
    SchemeValid (combinerDraws sizes + kη) (prepareThirdScheme sizes etas) :=
  (combinerScheme_valid sizes).product hη

/-- The `δ`s for `n` circuits (`verifier.rs:241-246`) : `δ_{A,0} = 1`, then
`δ_{B,0}, δ_{C,0}, δ_{A,1}, δ_{B,1}, δ_{C,1}, …`, one drawn element each. -/
def deltaScheme (n : ℕ) : List (List ℕ) :=
  flatScheme (3 * n - 1)

theorem deltaScheme_valid (n : ℕ) : SchemeValid (3 * n - 1) (deltaScheme n) :=
  flatScheme_valid _

theorem length_appendScheme (k₁ : ℕ) (sch₁ sch₂ : List (List ℕ)) :
    (appendScheme k₁ sch₁ sch₂).length = sch₁.length + sch₂.length := by
  simp [appendScheme]

theorem length_productScheme (k₁ : ℕ) (sch₁ sch₂ : List (List ℕ)) :
    (productScheme k₁ sch₁ sch₂).length = sch₁.length * sch₂.length := by
  induction sch₁ with
  | nil => simp [productScheme]
  | cons m sch₁ ih =>
    simp only [productScheme, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem length_laterCircuitsScheme :
    ∀ ms : List ℕ, (laterCircuitsScheme ms).length = (ms.map (· - 1 + 1)).sum
  | [] => rfl
  | m :: ms => by
    rw [laterCircuitsScheme, length_appendScheme, length_laterCircuitsScheme ms,
      laterCircuitScheme, length_productScheme]
    simp [flatScheme, freeScheme]

/-- One weight per instance (a circuit has at least one). -/
theorem length_combinerScheme :
    ∀ sizes : List ℕ, (combinerScheme sizes).length = (sizes.map (· - 1 + 1)).sum
  | [] => rfl
  | m :: ms => by
    rw [combinerScheme, length_appendScheme, length_laterCircuitsScheme]
    simp [flatScheme, freeScheme]

/-- The first-round draw : the batched rowcheck over the instances `cs` (circuits
with `sizes` instances, in order), weighted by snarkVM's `ν_i τ_{i,j}` and checked
on all of `H`. -/
noncomputable def rowcheckDraw (H : EvalDomain F) (sizes : List ℕ)
    (cs : List (EvalDomain F × F[X])) : WeightDraw F :=
  schemeDraw (combinerDraws sizes) (combinerScheme sizes) H.nodeList (batchedClaims H cs)

theorem rowcheckDraw_coordAffine (H : EvalDomain F) (sizes : List ℕ)
    (cs : List (EvalDomain F × F[X])) :
    ∀ x ∈ (rowcheckDraw H sizes cs).D, CoordAffine ((rowcheckDraw H sizes cs).comb x) :=
  schemeDraw_coordAffine (combinerScheme_valid sizes).nodup _ _

/-- The lucky event of `batchedZerocheck_extract` on snarkVM's weights is a lucky
first-round draw. -/
theorem rowcheckDraw_lucky {H : EvalDomain F} {sizes : List ℕ} {cs : List (EvalDomain F × F[X])}
    (hcs : cs.length ≤ (sizes.map (· - 1 + 1)).sum) {ws : List F}
    (hws : ws.length = combinerDraws sizes)
    (h : inspectBatchOn H.nodeList (schemeWeights (combinerScheme sizes) ws)
      (batchedClaims H cs) ≠ none) :
    (rowcheckDraw H sizes cs).Lucky ws :=
  schemeDraw_lucky (combinerScheme_valid sizes)
    (fun x _ => by simpa [batchedClaims, length_combinerScheme] using hcs) hws h

/-- The batched rowcheck over circuits with `sizes` instances, each instance
weighted by snarkVM's `ν_i τ_{i,j}` : over all draws of the first-round
combiners, at most `k · | S | ^{k-1}` are lucky on all of `H`, with `k` the
number of drawn elements. -/
theorem card_filter_batchedZerocheck_combiners_le (H : EvalDomain F) (sizes : List ℕ)
    (cs : List (EvalDomain F × F[X])) (hcs : cs.length ≤ (sizes.map (· - 1 + 1)).sum)
    (S : Finset F) :
    ((tapes S (combinerDraws sizes)).filter fun ws =>
      inspectBatchOn H.nodeList (schemeWeights (combinerScheme sizes) ws)
        (batchedClaims H cs) ≠ none).card ≤
      combinerDraws sizes * S.card ^ (combinerDraws sizes - 1) :=
  card_filter_inspectBatchOn_scheme_le (combinerScheme_valid sizes) _ _
    (fun x _ => by simpa [batchedClaims, length_combinerScheme] using hcs) S

theorem length_deltaScheme (n : ℕ) : (deltaScheme n).length = 3 * n - 1 + 1 := by
  simp [deltaScheme, flatScheme, freeScheme]

/-- The fourth-round draw : the batched matrix sumcheck over the numerators `cs`
of `n` circuits (three per circuit, `A, B, C` in order), weighted by snarkVM's
`δ`s and checked on all of the largest nonzero domain `K`. -/
noncomputable def deltaDraw (K : EvalDomain F) (n : ℕ) (cs : List (EvalDomain F × F[X])) :
    WeightDraw F :=
  schemeDraw (3 * n - 1) (deltaScheme n) K.nodeList (batchedClaims K cs)

theorem deltaDraw_coordAffine (K : EvalDomain F) (n : ℕ) (cs : List (EvalDomain F × F[X])) :
    ∀ x ∈ (deltaDraw K n cs).D, CoordAffine ((deltaDraw K n cs).comb x) :=
  schemeDraw_coordAffine (deltaScheme_valid n).nodup _ _

/-- The lucky event of `batchedMatrix_extract` on snarkVM's `δ`s is a lucky
fourth-round draw. -/
theorem deltaDraw_lucky {K : EvalDomain F} {n : ℕ} {cs : List (EvalDomain F × F[X])}
    (hcs : cs.length ≤ 3 * n - 1 + 1) {ws : List F} (hws : ws.length = 3 * n - 1)
    (h : inspectBatchOn K.nodeList (schemeWeights (deltaScheme n) ws) (batchedClaims K cs) ≠
      none) :
    (deltaDraw K n cs).Lucky ws :=
  schemeDraw_lucky (deltaScheme_valid n)
    (fun x _ => by simpa [batchedClaims, length_deltaScheme] using hcs) hws h

/-- The batched matrix sumcheck over `n` circuits, each matrix weighted by its
`δ` : over all draws of the `3n − 1` squeezed `δ`s, at most
`(3n − 1) · | S | ^{3n-2}` are lucky on all of `K`. -/
theorem card_filter_batchedMatrix_deltas_le (K : EvalDomain F) (n : ℕ)
    (cs : List (EvalDomain F × F[X])) (hcs : cs.length ≤ 3 * n - 1 + 1) (S : Finset F) :
    ((tapes S (3 * n - 1)).filter fun ws =>
      inspectBatchOn K.nodeList (schemeWeights (deltaScheme n) ws)
        (batchedClaims K cs) ≠ none).card ≤
      (3 * n - 1) * S.card ^ (3 * n - 1 - 1) :=
  card_filter_inspectBatchOn_scheme_le (deltaScheme_valid n) _ _
    (fun x _ => by simpa [batchedClaims, length_deltaScheme] using hcs) S

/-- Weight `1` on the first claim, then `w η_A, w η_B, w η_C` for each `w` of `ws`. -/
def etaWeights (ws : List F) (ηA ηB ηC : F) : List F :=
  1 :: ws.flatMap fun w => [w * ηA, w * ηB, w * ηC]

/-- snarkVM's V3 lineval weights (`ahp.rs:316-363`) : `1` on the mask sum, then
`μ_i ρ_{i,j} η_M` on matrix `M` of instance `(i, j)`, from the prepare-third
draw. -/
def linevalScheme (sizes : List ℕ) : List (List ℕ) :=
  [] :: prepareThirdScheme sizes (freeScheme 3)

theorem SchemeValid.cons_nil {k : ℕ} {sch : List (List ℕ)} (h : SchemeValid k sch)
    (hne : [] ∉ sch) : SchemeValid k ([] :: sch) where
  nodup m hm := by
    rcases List.mem_cons.mp hm with rfl | hm
    exacts [List.nodup_nil, h.nodup m hm]
  lt m hm := by
    rcases List.mem_cons.mp hm with rfl | hm
    exacts [by simp, h.lt m hm]
  distinct := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, h.distinct⟩
    obtain ⟨m, hm, hm0⟩ := List.mem_map.mp hmem
    exact hne ((List.toFinset_eq_empty_iff m).mp (by simpa using hm0) ▸ hm)

theorem nil_not_mem_prepareThirdScheme (sizes : List ℕ) :
    [] ∉ prepareThirdScheme sizes (freeScheme 3) := by
  simp [prepareThirdScheme, productScheme, freeScheme, shiftMono]

theorem linevalScheme_valid (sizes : List ℕ) :
    SchemeValid (combinerDraws sizes + 3) (linevalScheme sizes) :=
  (prepareThirdScheme_valid sizes (freeScheme_valid 3)).cons_nil
    (nil_not_mem_prepareThirdScheme sizes)

theorem length_linevalScheme (sizes : List ℕ) :
    (linevalScheme sizes).length = (sizes.map (· - 1 + 1)).sum * 3 + 1 := by
  simp [linevalScheme, prepareThirdScheme, length_productScheme, length_combinerScheme,
    freeScheme]

/-- The lineval weights are the third-round combiners times the `η`s, after a `1`. -/
theorem schemeWeights_linevalScheme (sizes : List ℕ) (ws : List F) :
    schemeWeights (linevalScheme sizes) ws =
      etaWeights (schemeWeights (combinerScheme sizes) ws) (ws.getD (combinerDraws sizes) 0)
        (ws.getD (combinerDraws sizes + 1) 0) (ws.getD (combinerDraws sizes + 2) 0) := by
  simp [linevalScheme, etaWeights, schemeWeights, prepareThirdScheme, productScheme, freeScheme,
    shiftMono, List.map_flatMap, List.flatMap_map, monoEval, List.range_succ]

/-- The prepare-third draw : the lineval claims `cs` (the mask sum, then three per
instance), weighted by `linevalScheme`. -/
noncomputable def linevalDraw (sizes : List ℕ) (cs : List F) : WeightDraw F :=
  schemeDraw (combinerDraws sizes + 3) (linevalScheme sizes) [0] fun _ => cs

theorem linevalDraw_coordAffine (sizes : List ℕ) (cs : List F) :
    ∀ x ∈ (linevalDraw sizes cs).D, CoordAffine ((linevalDraw sizes cs).comb x) :=
  schemeDraw_coordAffine (linevalScheme_valid sizes).nodup _ _

/-- The lucky event of the batched lineval on snarkVM's weights is a lucky
prepare-third draw. -/
theorem linevalDraw_lucky {sizes : List ℕ} {cs : List F}
    (hcs : cs.length ≤ (sizes.map (· - 1 + 1)).sum * 3 + 1) {ws : List F}
    (hws : ws.length = combinerDraws sizes + 3)
    (h : inspectBatch (schemeWeights (linevalScheme sizes) ws) cs ≠ none) :
    (linevalDraw sizes cs).Lucky ws := by
  obtain ⟨hzero, hlive⟩ := (inspectBatch_ne_none_iff _ _).1 h
  exact schemeDraw_lucky (linevalScheme_valid sizes)
    (fun _ _ => by rwa [length_linevalScheme]) hws
    ((inspectBatchOn_ne_none_iff _ _ _).2 ⟨by simpa using hzero, 0, by simp, hlive⟩)

/-- The batched lineval over circuits with `sizes` instances : over all draws of
the prepare-third elements, at most `k · | S | ^{k-1}` are lucky, with `k` the
number of combiners plus the three `η`s. -/
theorem card_filter_lineval_weights_le (sizes : List ℕ) (cs : List F)
    (hcs : cs.length ≤ (sizes.map (· - 1 + 1)).sum * 3 + 1) (S : Finset F) :
    ((tapes S (combinerDraws sizes + 3)).filter fun ws =>
      inspectBatch (schemeWeights (linevalScheme sizes) ws) cs ≠ none).card ≤
      (combinerDraws sizes + 3) * S.card ^ (combinerDraws sizes + 3 - 1) :=
  card_filter_inspectBatch_scheme_le (linevalScheme_valid sizes) cs
    (by rwa [length_linevalScheme]) S

end Varuna