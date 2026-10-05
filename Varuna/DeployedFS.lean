/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.SpongeFS
import Varuna.BatchCheck

/-!
# Fiat–Shamir for the deployed verifier

`sponge_soundness` counts the six squeezes of the V3 transcript. snarkVM's verifier also
squeezes the batch check's challenges from the same sponge. After the six rounds it absorbs
the evaluations message, the opened `g₁(β)` and every `g_M(γ)` (`proof.rs:204-211`,
`varuna.rs:1066`). For each query point it squeezes one short challenge per opened
polynomial, then one it drops. The randomizers come from a copy of the sponge taken before
those squeezes and fed the KZG proofs (`sonic_pc/mod.rs:347-420`). Each short challenge is
`short` of the oracle's answer at its sponge state.

Each of these queries gets a bad set (`pcBad`) : the short values that end liveness of its
point's draw after the point's challenges before it, or of the randomizers' draw on the
defects at `τ`. The bad set reads the batch represented with the query only through what the
six messages fix (`pcBadOf_absorbed`), and the oracle only off other queries
(`pcBadOf_congr`). A lucky batch check puts one answer in its bad set
(`DeployedProver.exists_pcBadOf`), and `table_charge` counts these hits as it counts the six
squeezes' (`V3Batch.pc_hit`).

`V3Batch.deployed_soundness` : the deployed verifier accepts an output whose relation fails,
with no trapdoor break, on at most the two table charges together.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## What `batch_check` reads of a batch -/

/-- The circuit with its instances' opened `ŵ(β)` cleared. -/
def BatchCircuit.clearVw (c : BatchCircuit F) : BatchCircuit F :=
  { c with insts := c.insts.map fun x => { x with vw := 0 } }

namespace V3Batch

/-- The opened values the verifier absorbs before `batch_check` (`proof.rs:204-211`,
`varuna.rs:1066`) : `g₁(β)`, then every circuit's `g_A(γ)`, every `g_B(γ)`, and every
`g_C(γ)`. -/
def evalValues (P : V3Batch F) : List F :=
  P.vG1 :: (P.circuits.map BatchCircuit.vgA ++ P.circuits.map BatchCircuit.vgB ++
    P.circuits.map BatchCircuit.vgC)

/-- The evaluations message. -/
def evalMsg (P : V3Batch F) : FSMessage F :=
  .fields P.evalValues

/-- `P` with the opened values read off the evaluations message. -/
def withEvals (P : V3Batch F) : FSMessage F → V3Batch F
  | .fields vs => { P with
      vG1 := vs.getD 0 0
      circuits := P.circuits.mapIdx fun i c => { c with
        vgA := vs.getD (i + 1) 0
        vgB := vs.getD (i + P.circuits.length + 1) 0
        vgC := vs.getD (i + 2 * P.circuits.length + 1) 0 } }
  | _ => P

/-- What `batch_check` reads of `P` once the evaluations message `m` is absorbed : what
the six messages fix, the challenges `chal`, and the values `m` carries. -/
noncomputable def pcView (P : V3Batch F) (chal : V2Challenge → List F) (m : FSMessage F) :
    V3Batch F :=
  (((P.absorbed 6).normal).withChallenges chal).withEvals m

/-- The query points read only the challenges, the committed polynomials as polynomials,
the clear sums, and the opened `g₁(β)` and `g_M(γ)`. -/
theorem pcPoints_congr {P₁ P₂ : V3Batch F} (hα : P₁.α = P₂.α) (hβ : P₁.β = P₂.β)
    (hγ : P₁.γ = P₂.γ) (hηA : P₁.ηA = P₂.ηA) (hηB : P₁.ηB = P₂.ηB) (hηC : P₁.ηC = P₂.ηC)
    (hR : P₁.R = P₂.R) (hCd : P₁.Cd = P₂.Cd) (hK : P₁.K = P₂.K) (hmode : P₁.mode = P₂.mode)
    (hmask : P₁.mask = P₂.mask) (h0 : toPoly P₁.h0rep = toPoly P₂.h0rep) (h1 : P₁.h1 = P₂.h1)
    (hg1 : P₁.g1 = P₂.g1) (h2 : P₁.h2 = P₂.h2) (hv : P₁.vG1 = P₂.vG1)
    (hc : P₁.circuits = P₂.circuits.map BatchCircuit.clearVw) (chal : V2Challenge → List F)
    (qs : List F[X]) : P₁.pcPoints chal qs = P₂.pcPoints chal qs := by
  have hinst :
      P₁.instances = P₂.instances.map fun p => (p.1.clearVw, { p.2 with vw := 0 }) := by
    simp [instances, hc, BatchCircuit.clearVw, List.flatMap_map, List.map_flatMap,
      Function.comp_def]
  have hsizes : P₁.sizes = P₂.sizes := by
    simp [sizes, hc, BatchCircuit.clearVw, Function.comp_def]
  simp only [pcPoints, rowLC, linLC, matLC, gOpenings, linSum, rowWeights, linWeights,
    deltaWeights, hinst, hsizes, hα, hβ, hγ, hηA, hηB, hηC, hR, hCd, hK, hmode, hmask, h0, h1,
    hg1, h2, hv, hc, List.map_map, Function.comp_def, List.flatMap_map, List.length_map,
    BatchCircuit.clearVw, BatchCircuit.matrixLCs]

theorem getD_evalValues_A (P : V3Batch F) {i : ℕ} (hi : i < P.circuits.length) :
    P.evalValues.getD (i + 1) 0 = P.circuits[i].vgA := by
  rw [evalValues, List.getD_cons_succ, List.append_assoc,
    List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map]

theorem getD_evalValues_B (P : V3Batch F) {i : ℕ} (hi : i < P.circuits.length) :
    P.evalValues.getD (i + P.circuits.length + 1) 0 = P.circuits[i].vgB := by
  rw [evalValues, List.getD_cons_succ, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp), List.length_map, Nat.add_sub_cancel,
    List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map]

theorem getD_evalValues_C (P : V3Batch F) {i : ℕ} (hi : i < P.circuits.length) :
    P.evalValues.getD (i + 2 * P.circuits.length + 1) 0 = P.circuits[i].vgC := by
  rw [evalValues, List.getD_cons_succ, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp; omega), List.length_map,
    List.getD_append_right _ _ _ _ (by simp; omega), List.length_map,
    show i + 2 * P.circuits.length - P.circuits.length - P.circuits.length = i by omega,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem circuits_pcView (P : V3Batch F) (chal : V2Challenge → List F) :
    (P.pcView chal P.evalMsg).circuits = P.circuits.map BatchCircuit.clearVw := by
  simp only [pcView, evalMsg, withEvals, withChallenges, normal, absorbed, upTo]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have hi : i < P.circuits.length := by simpa using h₂
  simp only [List.getElem_mapIdx, List.getElem_map, List.length_map, getD_evalValues_A P hi,
    getD_evalValues_B P hi, getD_evalValues_C P hi]
  simp [BatchCircuit.upTo, BatchInstance.upTo, BatchCircuit.clearVw]

/-- `pcView` of a batch's own evaluations message gives `batch_check` the batch's points. -/
theorem pcPoints_pcView (P : V3Batch F) (chal : V2Challenge → List F) (qs : List F[X]) :
    (P.pcView chal P.evalMsg).pcPoints chal qs = (P.withChallenges chal).pcPoints chal qs := by
  have hs : ((P.absorbed 6).normal).sizes = P.sizes := by
    show ((P.withChallenges fun _ => []).upTo 6).sizes = P.sizes
    rw [sizes_upTo]
    rfl
  refine pcPoints_congr (P₁ := P.pcView chal P.evalMsg) (P₂ := P.withChallenges chal)
    rfl rfl rfl
    (congrArg (fun l => (chal .prepareThird).getD (combinerDraws l) 0) hs)
    (congrArg (fun l => (chal .prepareThird).getD (combinerDraws l + 1) 0) hs)
    (congrArg (fun l => (chal .prepareThird).getD (combinerDraws l + 2) 0) hs) rfl rfl rfl rfl
    ?_ ?_ ?_ ?_ ?_ ?_ (circuits_pcView P chal) chal qs
  all_goals simp [pcView, evalMsg, withEvals, withChallenges, absorbed, normal, upTo,
    toPoly_coeffList, evalValues]

theorem map_opened_pcPoints (P : V3Batch F) (chal : V2Challenge → List F) (qs qs' : List F[X]) :
    (P.pcPoints chal qs).map (fun o => o.opened) = (P.pcPoints chal qs').map fun o => o.opened :=
  rfl

theorem map_opened_length_pcPoints (P : V3Batch F) (chal : V2Challenge → List F)
    (qs qs' : List F[X]) :
    (P.pcPoints chal qs).map (fun o => o.opened.length) =
      (P.pcPoints chal qs').map fun o => o.opened.length :=
  rfl

end V3Batch

/-! ## The squeezes of `batch_check` -/

/-- Where each point's challenges start in the squeeze after the evaluations message :
`α`'s at `0`, `β`'s at `2`, `γ`'s at `5`. One element is squeezed and dropped after each
point's (`sonic_pc/mod.rs:412`). -/
def pcOffset : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | _ => 5

/-- The point and position of element `e` of that squeeze. -/
def pcLocate (e : ℕ) : ℕ × ℕ :=
  if e < 2 then (0, e) else if e < 5 then (1, e - 2) else (2, e - 5)

theorem pcLocate_offset {p i : ℕ} (hp : p < 3) (h0 : p = 0 → i = 0) (h1 : p = 1 → i < 2) :
    pcLocate (pcOffset p + i) = (p, i) := by
  obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  · obtain rfl := h0 rfl
    rfl
  · have := h1 rfl
    simp only [pcLocate, pcOffset]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1
    omega
  · simp only [pcLocate, pcOffset]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
    omega

theorem pcOffset_locate (e : ℕ) : pcOffset (pcLocate e).1 + (pcLocate e).2 = e := by
  unfold pcLocate
  split_ifs <;> simp only [pcOffset] <;> omega

/-- The sponge state before element `e` of the squeeze after the evaluations message
`m`, the six rounds `ps` and the statement `I` before it. -/
def xiState (I : Transcript F) (ps : List (FSMessage F × ℕ)) (m : FSMessage F) (e : ℕ) :
    Transcript F :=
  I ++ spongeRounds (ps ++ [(m, e)])

/-- The private sponge's state before its element `j` : a copy of the sponge after `m`,
taken before any challenge is squeezed, then the proofs' message `m'`
(`sonic_pc/mod.rs:373-376`). -/
def rState (I : Transcript F) (ps : List (FSMessage F × ℕ)) (m m' : FSMessage F) (j : ℕ) :
    Transcript F :=
  I ++ spongeRounds (ps ++ [(m, 0), (m', j)])

section Squeezes

variable (short : F → F)

/-- Each point's combination challenges, `ns[p]` at point `p`, each the short element
`short` reads off the oracle's answer at its state (`accumulate_elems`). -/
def pcXis (H : Transcript F → F) (I : Transcript F) (ps : List (FSMessage F × ℕ))
    (m : FSMessage F) (ns : List ℕ) : List (List F) :=
  (List.range ns.length).map fun p => (List.range (ns.getD p 0)).map fun i =>
    short (H (xiState I ps m (pcOffset p + i)))

/-- The randomizers of the points at `β` and `γ`. The point at `α` has `1`, and the third
randomizer squeezed is not used. -/
def pcRands (H : Transcript F → F) (I : Transcript F) (ps : List (FSMessage F × ℕ))
    (m m' : FSMessage F) : List F :=
  (List.range 2).map fun j => short (H (rState I ps m m' j))

theorem length_pcXis (H : Transcript F → F) (I : Transcript F) (ps : List (FSMessage F × ℕ))
    (m : FSMessage F) (ns : List ℕ) : (pcXis short H I ps m ns).length = ns.length := by
  simp [pcXis]

theorem getElem_pcXis (H : Transcript F → F) (I : Transcript F) (ps : List (FSMessage F × ℕ))
    (m : FSMessage F) (ns : List ℕ) {p : ℕ} (hp : p < (pcXis short H I ps m ns).length) :
    (pcXis short H I ps m ns)[p] = (List.range (ns.getD p 0)).map fun i =>
      short (H (xiState I ps m (pcOffset p + i))) := by
  simp [pcXis]

/-- The challenges before element `i` of point `p` read the oracle only at the states of
those elements. -/
theorem take_pcXis_congr {H H' : Transcript F → F} (I : Transcript F)
    (ps : List (FSMessage F × ℕ)) (m : FSMessage F) (ns : List ℕ) (p i : ℕ)
    (hH : ∀ i' < i, H (xiState I ps m (pcOffset p + i')) = H' (xiState I ps m (pcOffset p + i'))) :
    ((pcXis short H I ps m ns).getD p []).take i =
      ((pcXis short H' I ps m ns).getD p []).take i := by
  rcases Nat.lt_or_ge p ns.length with hp | hp
  · rw [List.getD_eq_getElem _ _ (by rwa [length_pcXis]),
      List.getD_eq_getElem _ _ (by rwa [length_pcXis]), getElem_pcXis, getElem_pcXis,
      ← List.map_take, ← List.map_take, List.take_range]
    exact List.map_congr_left fun i' hi' => by
      rw [hH i' (by simp at hi'; omega)]
  · rw [List.getD_eq_default _ _ (by rwa [length_pcXis]),
      List.getD_eq_default _ _ (by rwa [length_pcXis])]

/-- A point's challenges, one per opened polynomial, weighting its discrepancies. -/
def xiDraw (ds : List F) : WeightDraw F :=
  schemeDraw ds.length (freeScheme ds.length) [0] fun _ => ds

/-- The randomizers `1, r₁, r₂` weighting the three defects. -/
def rDraw (cs : List F) : WeightDraw F :=
  schemeDraw 2 (flatScheme 2) [0] fun _ => cs

theorem xiDraw_lucky {ds ξ : List F} (hlen : ξ.length = ds.length)
    (h : inspectBatch ξ ds ≠ none) : (xiDraw ds).Lucky ξ := by
  obtain ⟨hzero, hlive⟩ := (inspectBatch_ne_none_iff _ _).1 h
  refine schemeDraw_lucky (freeScheme_valid _) (by simp [freeScheme]) hlen ?_
  rw [← hlen, schemeWeights_freeScheme]
  exact (inspectBatchOn_ne_none_iff _ _ _).2 ⟨by simpa using hzero, 0, by simp, hlive⟩

theorem rDraw_lucky {cs rs : List F} (hcs : cs.length ≤ 3) (hlen : rs.length = 2)
    (h : inspectBatch (1 :: rs) cs ≠ none) : (rDraw cs).Lucky rs := by
  obtain ⟨hzero, hlive⟩ := (inspectBatch_ne_none_iff _ _).1 h
  refine schemeDraw_lucky (flatScheme_valid _) (by simpa [flatScheme, freeScheme] using hcs)
    hlen ?_
  rw [← hlen, schemeWeights_flatScheme]
  exact (inspectBatchOn_ne_none_iff _ _ _).2 ⟨by simpa using hzero, 0, by simp, hlive⟩

theorem card_bad_xiDraw_le (ds : List F) (S : Finset F) (pre : List F) :
    ((xiDraw ds).bad S pre).card ≤ 1 :=
  WeightDraw.card_bad_le_one _ (schemeDraw_coordAffine (freeScheme_valid _).nodup _ _) S pre

theorem card_bad_rDraw_le (cs : List F) (S : Finset F) (pre : List F) :
    ((rDraw cs).bad S pre).card ≤ 1 :=
  WeightDraw.card_bad_le_one _ (schemeDraw_coordAffine (flatScheme_valid _).nodup _ _) S pre

/-- At most `m` elements of `S` per short value give at most `m` per bad short value. -/
theorem card_filter_short_le {S : Finset F} {m : ℕ}
    (hm : ∀ x, (S.filter fun a => short a = x).card ≤ m) (B : Finset F) :
    (S.filter fun a => short a ∈ B).card ≤ B.card * m := by
  calc (S.filter fun a => short a ∈ B).card
      ≤ (B.biUnion fun x => S.filter fun a => short a = x).card :=
        card_le_card fun a ha => by
          obtain ⟨haS, hB⟩ := mem_filter.1 ha
          exact mem_biUnion.2 ⟨short a, hB, mem_filter.2 ⟨haS, rfl⟩⟩
    _ ≤ ∑ x ∈ B, (S.filter fun a => short a = x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ B, m := sum_le_sum fun x _ => hm x
    _ = B.card * m := by rw [sum_const, smul_eq_mul]

/-! ## The bad sets of `batch_check`'s squeezes -/

variable (S : Finset F) (τ : F) (dl : FSMessage F → List F)

/-- The bad set of a `batch_check` squeeze at the state the statement `s` and the rounds
`x` give, for the batch `R` represented with the query; the six rounds before give the
challenges. A further round `(m, e)` is element `e` after the evaluations message `m` :
the bad set is that of its point's draw on the point's discrepancies, after the point's
challenges before it. Rounds `(m, 0), (m', j)` are randomizer `j` after `m` and the proofs'
message `m'` : the bad set is that of the randomizers' draw on the defects at `τ`, with
the proofs' values at `τ` read off `m'` by `dl`. Short elements are read off `H`, and an
answer is bad when its short element is. -/
noncomputable def pcBadOf (R : V3Batch F) (s : V3Stmt F) (x : List (FSMessage F × ℕ))
    (H : Transcript F → F) : Finset F :=
  let I := v3Init s.1 s.2
  let chal := histChal (readRounds H I [] (x.take 6))
  match x.drop 6 with
  | [(m, e)] =>
    let os := (R.pcView chal m).pcPoints chal []
    S.filter fun a => short a ∈
      (xiDraw ((os.getD (pcLocate e).1 ⟨0, [], 0⟩).discrepancies)).bad (S.image short)
        (((pcXis short H I (x.take 6) m (os.map fun o => o.opened.length)).getD
          (pcLocate e).1 []).take (pcLocate e).2)
  | [(m, 0), (m', j)] =>
    let os := (R.pcView chal m).pcPoints chal ((dl m').map C)
    S.filter fun a => short a ∈
      (rDraw (defectsAt τ os (pcXis short H I (x.take 6) m (os.map fun o => o.opened.length)))).bad
        (S.image short) ((pcRands short H I (x.take 6) m m').take j)
  | _ => ∅

open Classical in
/-- `pcBadOf` read off a query decoded as a well-formed statement's encoding followed by
sponge rounds. -/
noncomputable def pcBad (R : V3Batch F) (q : Transcript F) (H : Transcript F → F) : Finset F :=
  if h : ∃ x : V3Stmt F × List (FSMessage F × ℕ),
      V3StmtWF x.1 ∧ q = v3Init x.1.1 x.1.2 ++ spongeRounds x.2 then
    pcBadOf short S τ dl R h.choose.1 h.choose.2 H
  else ∅

theorem pcBad_eq (R : V3Batch F) {s : V3Stmt F} (hs : V3StmtWF s) (x : List (FSMessage F × ℕ))
    (H : Transcript F → F) :
    pcBad short S τ dl R (v3Init s.1 s.2 ++ spongeRounds x) H = pcBadOf short S τ dl R s x H := by
  have h : ∃ y : V3Stmt F × List (FSMessage F × ℕ),
      V3StmtWF y.1 ∧ v3Init s.1 s.2 ++ spongeRounds x = v3Init y.1.1 y.1.2 ++ spongeRounds y.2 :=
    ⟨(s, x), hs, rfl⟩
  rw [pcBad, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  obtain ⟨e1, e2⟩ := v3Init_append_inj hs h1 h2
  rw [← e1, ← spongeRounds_injective e2]

theorem card_pcBad_le {m : ℕ} (hm : ∀ x, (S.filter fun a => short a = x).card ≤ m)
    (R : V3Batch F) (q : Transcript F) (H : Transcript F → F) :
    (S.filter (· ∈ pcBad short S τ dl R q H)).card ≤ m := by
  refine (card_filter_mem_le _ _).trans ?_
  unfold pcBad
  split
  · simp only [pcBadOf]
    split
    · exact (card_filter_short_le short hm _).trans
        (by simpa using Nat.mul_le_mul_right m (card_bad_xiDraw_le _ _ _))
    · exact (card_filter_short_le short hm _).trans
        (by simpa using Nat.mul_le_mul_right m (card_bad_rDraw_le _ _ _))
    · simp
  · simp

/-- The bad set reads the oracle only off the query's own state. -/
theorem pcBadOf_congr (R : V3Batch F) (s : V3Stmt F) (x : List (FSMessage F × ℕ))
    {H H' : Transcript F → F} (hH : ∀ q', q' ≠ v3Init s.1 s.2 ++ spongeRounds x → H q' = H' q') :
    pcBadOf short S τ dl R s x H = pcBadOf short S τ dl R s x H' := by
  have hsplit : ∀ y, x.drop 6 = y → x = x.take 6 ++ y := fun y h => by
    rw [← h, List.take_append_drop]
  have hchal : 7 ≤ x.length →
      readRounds H (v3Init s.1 s.2) [] (x.take 6) =
        readRounds H' (v3Init s.1 s.2) [] (x.take 6) := by
    intro hx
    refine readRounds_congr _ hH [] _ fun ps₁ m n ps₂ hps j _ heq => ?_
    have h1 := congrArg List.length (spongeRounds_injective (List.append_cancel_left heq))
    have h2 := congrArg List.length hps
    simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil,
      List.length_take] at h1 h2
    omega
  simp only [pcBadOf]
  split
  next m e hx =>
    have hx7 := hsplit _ hx
    have hlen : x.length = 7 := by
      have := congrArg List.length hx
      simp only [List.length_drop, List.length_cons, List.length_nil] at this
      omega
    rw [hchal (by omega), take_pcXis_congr short (H' := H') _ _ _ _ _ _ fun i' hi' => hH _ ?_]
    intro heq
    have h := List.append_cancel_left ((spongeRounds_injective
      (List.append_cancel_left heq)).trans hx7)
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
    have := pcOffset_locate e
    omega
  next m m' j hx =>
    have hx8 := hsplit _ hx
    have hlen : x.length = 8 := by
      have := congrArg List.length hx
      simp only [List.length_drop, List.length_cons, List.length_nil] at this
      omega
    have hxi : ∀ ns, pcXis short H (v3Init s.1 s.2) (x.take 6) m ns =
        pcXis short H' (v3Init s.1 s.2) (x.take 6) m ns := by
      intro ns
      simp only [pcXis]
      refine List.map_congr_left fun p _ => List.map_congr_left fun i _ => ?_
      refine congrArg short (hH _ fun heq => ?_)
      have h := congrArg List.length ((spongeRounds_injective
        (List.append_cancel_left heq)).trans hx8)
      simp at h
    have hr : (pcRands short H (v3Init s.1 s.2) (x.take 6) m m').take j =
        (pcRands short H' (v3Init s.1 s.2) (x.take 6) m m').take j := by
      simp only [pcRands, ← List.map_take, List.take_range]
      refine List.map_congr_left fun j' hj' => congrArg short (hH _ fun heq => ?_)
      have h := List.append_cancel_left ((spongeRounds_injective
        (List.append_cancel_left heq)).trans hx8)
      simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
      simp only [List.mem_range] at hj'
      omega
    rw [hchal (by omega), hxi, hr]
  next => rfl

theorem pcBad_congr (R : V3Batch F) (q : Transcript F) {H H' : Transcript F → F}
    (hH : ∀ q', q' ≠ q → H q' = H' q') :
    pcBad short S τ dl R q H = pcBad short S τ dl R q H' := by
  unfold pcBad
  split
  · next h =>
    obtain ⟨-, hq⟩ := h.choose_spec
    exact pcBadOf_congr short S τ dl R _ _ fun q' hq' => hH q' (by rw [hq]; exact hq')
  · rfl

/-- `pcBadOf` reads the represented batch only through what the six messages fix. -/
theorem pcBadOf_absorbed {R R' : V3Batch F} (h : (R.absorbed 6).normal = (R'.absorbed 6).normal)
    (s : V3Stmt F) (x : List (FSMessage F × ℕ)) (H : Transcript F → F) :
    pcBadOf short S τ dl R s x H = pcBadOf short S τ dl R' s x H := by
  unfold pcBadOf V3Batch.pcView
  rw [h]

theorem mem_pcBadOf_xi {R : V3Batch F} {s : V3Stmt F} {ps : List (FSMessage F × ℕ)}
    {m : FSMessage F} {H : Transcript F → F} {chal : V2Challenge → List F} (hps : ps.length = 6)
    (hchal : histChal (readRounds H (v3Init s.1 s.2) [] ps) = chal) {p i : ℕ} (hp : p < 3)
    (h0 : p = 0 → i = 0) (h1 : p = 1 → i < 2) {a : F} (ha : a ∈ S)
    (hbad : short a ∈ (xiDraw (((R.pcView chal m).pcPoints chal []).getD p
        ⟨0, [], 0⟩).discrepancies).bad (S.image short)
      (((pcXis short H (v3Init s.1 s.2) ps m
        (((R.pcView chal m).pcPoints chal []).map fun o => o.opened.length)).getD p []).take i)) :
    a ∈ pcBadOf short S τ dl R s (ps ++ [(m, pcOffset p + i)]) H := by
  have ht : (ps ++ [(m, pcOffset p + i)]).take 6 = ps := List.take_left' hps
  have hd : (ps ++ [(m, pcOffset p + i)]).drop 6 = [(m, pcOffset p + i)] := List.drop_left' hps
  unfold pcBadOf
  rw [hd, ht]
  dsimp only
  rw [hchal, pcLocate_offset hp h0 h1]
  exact mem_filter.2 ⟨ha, hbad⟩

theorem mem_pcBadOf_r {R : V3Batch F} {s : V3Stmt F} {ps : List (FSMessage F × ℕ)}
    {m m' : FSMessage F} {H : Transcript F → F} {chal : V2Challenge → List F} (hps : ps.length = 6)
    (hchal : histChal (readRounds H (v3Init s.1 s.2) [] ps) = chal) {j : ℕ} {a : F} (ha : a ∈ S)
    (hbad : short a ∈ (rDraw (defectsAt τ ((R.pcView chal m).pcPoints chal ((dl m').map C))
        (pcXis short H (v3Init s.1 s.2) ps m
          (((R.pcView chal m).pcPoints chal ((dl m').map C)).map fun o => o.opened.length)))).bad
      (S.image short) ((pcRands short H (v3Init s.1 s.2) ps m m').take j)) :
    a ∈ pcBadOf short S τ dl R s (ps ++ [(m, 0), (m', j)]) H := by
  have ht : (ps ++ [(m, 0), (m', j)]).take 6 = ps := List.take_left' hps
  have hd : (ps ++ [(m, 0), (m', j)]).drop 6 = [(m, 0), (m', j)] := List.drop_left' hps
  unfold pcBadOf
  rw [hd, ht]
  dsimp only
  rw [hchal]
  exact mem_filter.2 ⟨ha, hbad⟩

end Squeezes

theorem eval_getD_map_C (τ : F) (qs : List F[X]) (j : ℕ) :
    (((qs.map (eval τ)).map C).getD j 0).eval τ = (qs.getD j 0).eval τ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map]
  cases qs[j]? <;> simp

/-- The defects at `τ` read the proofs only through their values at `τ`. -/
theorem V3Batch.defectsAt_pcPoints_congr (P : V3Batch F) (chal : V2Challenge → List F) {τ : F}
    {qs qs' : List F[X]} (h : ∀ j, (qs.getD j 0).eval τ = (qs'.getD j 0).eval τ)
    (ξs : List (List F)) :
    defectsAt τ (P.pcPoints chal qs) ξs = defectsAt τ (P.pcPoints chal qs') ξs := by
  have h' : ∀ j, eval τ (qs[j]?.getD 0) = eval τ (qs'[j]?.getD 0) := fun j => by
    simpa [List.getD_eq_getElem?_getD] using h j
  rcases ξs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp [defectsAt, V3Batch.pcPoints, PointOpening.defect, h']

theorem V3Batch.length_gOpenings (P : V3Batch F) : P.gOpenings.length = 3 * P.circuits.length := by
  simp only [gOpenings, List.length_flatMap, List.length_cons, List.length_nil]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

theorem tableAns_mem {S : Finset F} {D : List (Transcript F)} {T : List F}
    (hT : T ∈ tapes S D.length) {q : Transcript F} (hq : q ∈ D) : tableAns D T q ∈ S := by
  have hlt : D.idxOf q < T.length := by
    rw [(mem_tapes hT).1]
    exact List.idxOf_lt_length_of_mem hq
  simp only [tableAns, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact (mem_tapes hT).2 _ (List.getElem_mem hlt)

/-! ## The deployed prover and verifier -/

/-- An algebraic V3 prover that also gives the polynomials behind its three KZG proofs. -/
structure DeployedProver (F : Type*) [Field F] extends AlgebraicProver F where
  proofs : QueryLog F → List F[X]

namespace DeployedProver

variable (A : DeployedProver F) (cnt : V3Stmt F → V2Challenge → ℕ) (Q : ℕ) (short : F → F)
  (τ : F) (pfMsg : List F → FSMessage F)

/-- The proofs' message after `A`'s log : the proofs' values at `τ`, as their group
elements give them, encoded by `pfMsg`. -/
def proofsMsg (log : QueryLog F) : FSMessage F :=
  pfMsg ((A.proofs log).map (eval τ))

/-- `batch_check`'s query points after `A`'s log, the challenges read off `H`. -/
noncomputable def points (H : Transcript F → F) (log : QueryLog F) : List (PointOpening F) :=
  ((A.batch log).withChallenges (A.spongeChal cnt H log)).pcPoints (A.spongeChal cnt H log)
    (A.proofs log)

/-- The points' combination challenges after `A`'s log, read off `H`. -/
noncomputable def xis (H : Transcript F → F) (log : QueryLog F) : List (List F) :=
  pcXis short H (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg
    ((A.points cnt H log).map fun o => o.opened.length)

/-- The randomizers after `A`'s log, read off `H`. -/
def rands (H : Transcript F → F) (log : QueryLog F) : List F :=
  1 :: pcRands short H (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg
    (A.proofsMsg τ pfMsg log)

/-- The verifier's `batch_check` queries after `A`'s log : every element of the squeeze
after the evaluations message, then the private sponge's three. -/
def pcQueries (log : QueryLog F) : List (Transcript F) :=
  (List.range (3 * (A.batch log).circuits.length + 7)).map
      (xiState (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg) ++
    (List.range 3).map (rState (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg
      (A.proofsMsg τ pfMsg log))

/-- `A`'s `Q` queries, then the verifier's `batch_check` queries. -/
def pcNext (log : QueryLog F) : Transcript F :=
  if log.length < Q then A.next log
  else (A.pcQueries cnt τ pfMsg (log.take Q)).getD (log.length - Q) []

/-- The bad set of a `batch_check` query after `log`, for the batch represented with it. -/
noncomputable def pcRB (S : Finset F) (dl : FSMessage F → List F) (log : QueryLog F)
    (q : Transcript F) (H : Transcript F → F) : Finset F :=
  pcBad short S τ dl (A.spongeRep Q log) q H

/-- On the table `T`, `A`'s output after its `Q` queries passes the deployed verifier and
the relation fails. -/
def DeployedFools (D : List (Transcript F)) (S : Finset F) (T : List F) : Prop :=
  ((A.batch (tableRun A.next (tableAns D T) Q)).withChallenges
      (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))).DeployedAccepts S
      (A.out (tableRun A.next (tableAns D T) Q))
      (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.stmt (tableRun A.next (tableAns D T) Q)).2 τ (A.proofs (tableRun A.next (tableAns D T) Q))
      (A.xis cnt short (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.rands cnt short τ pfMsg (tableAns D T) (tableRun A.next (tableAns D T) Q)) ∧
    ¬((A.batch (tableRun A.next (tableAns D T) Q)).withChallenges
      (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))).Holds
      (A.out (tableRun A.next (tableAns D T) Q))

/-- On the table `T`, a point's defect is a nonzero polynomial with root `τ`. -/
def PCBreaks (D : List (Transcript F)) (T : List F) : Prop :=
  PCBreak τ (A.points cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))
    (A.xis cnt short (tableAns D T) (tableRun A.next (tableAns D T) Q))

/-- A defect with root `τ` is a trapdoor break. -/
theorem PCBreaks.trapdoorBreak {D : List (Transcript F)} {T : List F}
    (h : A.PCBreaks cnt Q short τ D T) : ∃ br : TrapdoorBreak F, br.holds τ :=
  Varuna.PCBreak.trapdoorBreak h

theorem length_spongeShape (log : QueryLog F) : (A.spongeShape cnt log).length = 6 := by
  simp [OracleProver.spongeShape, v2Challenges]

theorem histChal_spongeShape (H : Transcript F → F) (log : QueryLog F) :
    histChal (readRounds H (v3Init (A.stmt log).1 (A.stmt log).2) [] (A.spongeShape cnt log)) =
      A.spongeChal cnt H log := by
  have h := A.rounds_spongeChal cnt H log
  simp only [OracleProver.spongeInit] at h
  rw [← h]
  funext c
  cases c <;> rfl

theorem map_fst_spongeShape (log : QueryLog F) :
    (A.spongeShape cnt log).map Prod.fst = (A.out log).messages := by
  simp [OracleProver.spongeShape, v2Challenges, V2Transcript.messages, V2Transcript.msgBefore]

/-- A lucky batch check puts the answer at one of the verifier's `batch_check` queries in
the bad set of that query for the output batch. -/
theorem exists_pcBadOf (S : Finset F) (dl : FSMessage F → List F)
    (hdl : ∀ ws, dl (pfMsg ws) = ws) (H : Transcript F → F) (log : QueryLog F)
    (hS : ∀ q ∈ A.pcQueries cnt τ pfMsg log, H q ∈ S)
    (hl : PCLucky τ (A.points cnt H log) (A.xis cnt short H log) (A.rands cnt short τ pfMsg H log)) :
    ∃ tail, A.spongeInit log ++ spongeRounds (A.spongeShape cnt log ++ tail) ∈
        A.pcQueries cnt τ pfMsg log ∧
      H (A.spongeInit log ++ spongeRounds (A.spongeShape cnt log ++ tail)) ∈
        pcBadOf short S τ dl (A.batch log) (A.stmt log) (A.spongeShape cnt log ++ tail) H := by
  have hps := A.length_spongeShape cnt log
  have hchal := A.histChal_spongeShape cnt H log
  have hlen3 : (A.points cnt H log).length = 3 := rfl
  rcases hl with hr | ⟨p, hp, hp', hξ⟩
  · set cs := defectsAt τ (A.points cnt H log) (A.xis cnt short H log)
    have hcs : cs.length ≤ 3 := by
      simp only [cs, defectsAt, List.length_zipWith, hlen3]
      omega
    have hluck := rDraw_lucky hcs (by simp [pcRands]) hr
    have hS' : ∀ a ∈ pcRands short H (A.spongeInit log) (A.spongeShape cnt log)
        (A.batch log).evalMsg (A.proofsMsg τ pfMsg log), a ∈ S.image short := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      exact mem_image_of_mem short (hS _ (List.mem_append_right _
        (List.mem_map.2 ⟨j, by simp at hj ⊢; omega, rfl⟩)))
    obtain ⟨j, hj, hbad⟩ := WeightDraw.exists_bad_of_lucky _ hluck hS'
    have hj2 : j < 2 := by simpa [pcRands] using hj
    have hmem : A.spongeInit log ++ spongeRounds (A.spongeShape cnt log ++
        [((A.batch log).evalMsg, 0), (A.proofsMsg τ pfMsg log, j)]) ∈ A.pcQueries cnt τ pfMsg log :=
      List.mem_append_right _ (List.mem_map.2 ⟨j, by simp; omega, rfl⟩)
    refine ⟨_, hmem, mem_pcBadOf_r short S τ dl hps hchal (hS _ hmem) ?_⟩
    have hrj : (pcRands short H (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg
        (A.proofsMsg τ pfMsg log))[j] = short (H (A.spongeInit log ++ spongeRounds
          (A.spongeShape cnt log ++
            [((A.batch log).evalMsg, 0), (A.proofsMsg τ pfMsg log, j)]))) := by
      simp [pcRands, rState]
    rw [V3Batch.pcPoints_pcView,
      show dl (A.proofsMsg τ pfMsg log) = (A.proofs log).map (eval τ) from hdl _,
      V3Batch.defectsAt_pcPoints_congr _ _ (eval_getD_map_C τ (A.proofs log)),
      V3Batch.map_opened_length_pcPoints _ _ _ (A.proofs log), ← hrj]
    exact hbad
  · set os := A.points cnt H log
    set ξs := A.xis cnt short H log
    have hξp : ξs[p] = (List.range ((os.map fun o => o.opened.length).getD p 0)).map fun i =>
        short (H (xiState (A.spongeInit log) (A.spongeShape cnt log) (A.batch log).evalMsg
          (pcOffset p + i))) :=
      getElem_pcXis short _ _ _ _ _ hp'
    have hlen : ξs[p].length = os[p].discrepancies.length := by
      rw [hξp]
      simp [PointOpening.discrepancies, List.getElem?_eq_getElem hp]
      rfl
    have hrange : ∀ i < (os.map fun o => o.opened.length).getD p 0,
        pcOffset p + i < 3 * (A.batch log).circuits.length + 7 := by
      intro i hi
      have hp3 : p < 3 := hp
      obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
      · simp [os, points, V3Batch.pcPoints, pcOffset] at hi ⊢
        omega
      · simp [os, points, V3Batch.pcPoints, pcOffset] at hi ⊢
        omega
      · simp only [os, points, V3Batch.pcPoints, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero, List.length_append, V3Batch.length_gOpenings, List.length_cons,
          List.length_nil] at hi
        simp only [pcOffset]
        have : ((A.batch log).withChallenges (A.spongeChal cnt H log)).circuits.length =
          (A.batch log).circuits.length := rfl
        omega
    have hS' : ∀ a ∈ ξs[p], a ∈ S.image short := by
      intro a ha
      rw [hξp] at ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      exact mem_image_of_mem short (hS _ (List.mem_append_left _
        (List.mem_map.2 ⟨pcOffset p + i, List.mem_range.2 (hrange i (by simpa using hi)), rfl⟩)))
    obtain ⟨i, hi, hbad⟩ := WeightDraw.exists_bad_of_lucky _ (xiDraw_lucky hlen hξ) hS'
    have hi' : i < (os.map fun o => o.opened.length).getD p 0 := by
      rw [hξp] at hi
      simpa using hi
    have hmem : A.spongeInit log ++ spongeRounds (A.spongeShape cnt log ++
        [((A.batch log).evalMsg, pcOffset p + i)]) ∈ A.pcQueries cnt τ pfMsg log :=
      List.mem_append_left _ (List.mem_map.2 ⟨pcOffset p + i, List.mem_range.2 (hrange i hi'), rfl⟩)
    have hp3 : p < 3 := hp
    have h0 : p = 0 → i = 0 := by
      rintro rfl
      simp [os, points, V3Batch.pcPoints] at hi'
      omega
    have h1 : p = 1 → i < 2 := by
      rintro rfl
      simpa [os, points, V3Batch.pcPoints] using hi'
    refine ⟨_, hmem, mem_pcBadOf_xi short S τ dl hps hchal hp3 h0 h1 (hS _ hmem) ?_⟩
    rw [V3Batch.pcPoints_pcView]
    have hdisc : ((((A.batch log).withChallenges (A.spongeChal cnt H log)).pcPoints
        (A.spongeChal cnt H log) []).getD p ⟨0, [], 0⟩).discrepancies =
          os[p].discrepancies := by
      obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega
      all_goals rfl
    rw [hdisc, V3Batch.map_opened_length_pcPoints _ _ [] (A.proofs log),
      List.getD_eq_getElem _ _ (by rw [length_pcXis, List.length_map]; exact hp)]
    have hξi : ξs[p][i] = short (H (A.spongeInit log ++ spongeRounds (A.spongeShape cnt log ++
        [((A.batch log).evalMsg, pcOffset p + i)]))) :=
      (List.getElem_of_eq hξp hi).trans (by simp [xiState])
    rw [← hξi]
    exact hbad

end DeployedProver

namespace V3Batch

variable {G1 : Type*} [AddCommGroup G1] [Module F G1]

/-- The hit `deployed_soundness` charges for the batch check. On a table where the batch
check passes by luck and no represented batch clashes with the output batch, one of the
first `Q + V'` queries, `A`'s then the verifier's `batch_check` queries, is in `D`, asked
for the first time, and answered in its bad set. -/
theorem pc_hit (S : Finset F) (short : F → F) (A : DeployedProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V' : ℕ)
    (hV' : ∀ log, 3 * (A.batch log).circuits.length + 10 ≤ V')
    (D : List (Transcript F)) (g : G1) (hg : g ≠ 0) (κ τ : F) (pfMsg : List F → FSMessage F)
    (dl : FSMessage F → List F) (hdl : ∀ ws, dl (pfMsg ws) = ws)
    (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g κ τ = (P'.absorbed k).commitments g κ τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s ps ps' (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds (ps ++ ps') → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log))
    {T : List F} (hTt : T ∈ tapes S D.length)
    (hD : ∀ q ∈ A.pcQueries cnt τ pfMsg (tableRun A.next (tableAns D T) Q), q ∈ D)
    (hl : PCLucky τ (A.points cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.xis cnt short (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.rands cnt short τ pfMsg (tableAns D T) (tableRun A.next (tableAns D T) Q)))
    (hnc : ¬A.SpongeClashes Q D τ κ T) :
    ∃ i < Q + V', TableHit D (A.pcNext cnt Q τ pfMsg) (A.pcRB Q short τ S dl) T i := by
  unfold TableHit
  set H := tableAns D T
  set L := tableRun A.next H Q
  obtain ⟨tail, hmem, hbad⟩ := A.exists_pcBadOf cnt short τ pfMsg S dl hdl H L
    (fun q hq => tableAns_mem hTt (hD q hq)) hl
  set ps := A.spongeShape cnt L
  set q := A.spongeInit L ++ spongeRounds (ps ++ tail)
  -- The verifier asks `q`.
  have hnext : ∀ log : QueryLog F, log.length < Q → A.pcNext cnt Q τ pfMsg log = A.next log :=
    fun _ h => if_pos h
  have hrunQ : tableRun (A.pcNext cnt Q τ pfMsg) H Q = L := tableRun_congr_next hnext H Q le_rfl
  obtain ⟨p, hp, hpq⟩ := List.getElem_of_mem hmem
  have hpV : p < V' := by
    have hlen : (A.pcQueries cnt τ pfMsg L).length = 3 * (A.batch L).circuits.length + 10 := by
      simp only [DeployedProver.pcQueries, List.length_append, List.length_map, List.length_range]
    have := hV' L
    omega
  have hask : ∃ i, i < Q + V' ∧
      A.pcNext cnt Q τ pfMsg (tableRun (A.pcNext cnt Q τ pfMsg) H i) = q := by
    refine ⟨Q + p, by omega, ?_⟩
    have hlen := length_tableRun (A.pcNext cnt Q τ pfMsg) H (Q + p)
    have htake : (tableRun (A.pcNext cnt Q τ pfMsg) H (Q + p)).take Q = L := by
      rw [take_tableRun _ _ (by omega), hrunQ]
    rw [DeployedProver.pcNext, if_neg (by omega), htake, hlen, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ hp, hpq]
  obtain ⟨hi0, hq0⟩ := Nat.find_spec hask
  have hmin : ∀ i < Nat.find hask,
      A.pcNext cnt Q τ pfMsg (tableRun (A.pcNext cnt Q τ pfMsg) H i) ≠ q :=
    fun i hi h => Nat.find_min hask hi ⟨by omega, h⟩
  refine ⟨Nat.find hask, hi0, by rw [hq0]; exact hD q hmem, fun i hi => by
    rw [hq0]; exact hmin i hi, ?_⟩
  rw [hq0]
  -- Its bad set is the output batch's.
  set log0 := tableRun (A.pcNext cnt Q τ pfMsg) H (Nat.find hask)
  have hlog0 : log0.length = Nat.find hask := length_tableRun _ _ _
  have hP : ((A.spongeRep Q log0).absorbed 6).normal = ((A.batch L).absorbed 6).normal := by
    unfold AlgebraicProver.spongeRep
    rw [hlog0]
    split_ifs with hlt
    · have hrun0 : log0 = tableRun A.next H (Nat.find hask) := tableRun_congr_next hnext H _ hlt.le
      have hq' : A.next log0 = v3Init (A.stmt L).1 (A.stmt L).2 ++ spongeRounds (ps ++ tail) := by
        rw [← hnext _ (by rw [hlog0]; exact hlt)]
        exact hq0
      have hk : ps.length = 6 := A.length_spongeShape cnt L
      have hm : ps.map Prod.fst = msgs ps.length (A.batch L) := by
        rw [A.map_fst_spongeShape, hk, ← (hout L).2 6,
          List.take_of_length_le (by simp [V2Transcript.messages])]
      obtain ⟨hidx, hmsg⟩ :=
        hrep _ (A.stmt L) ps tail (A.batch L) (by rw [hlog0]; exact hlt) hq' (hstmt L).2
          (hout L).1 hm
      rw [hm, hk] at hmsg
      obtain ⟨hshape, hcom⟩ := hmsgs _ _ _ (hidx.trans (hout L).1.symm) hmsg.symm
      refine normal_eq_of hshape (eq_of_not_clash (map_eval_eq_of_commitments hg hcom) ?_)
      intro hcl
      exact hnc ⟨Nat.find hask, hlt, 6, by rw [← hrun0]; exact hcl⟩
    · rw [take_tableRun _ _ (by omega), hrunQ]
  show H q ∈ pcBad short S τ dl (A.spongeRep Q log0)
    (v3Init (A.stmt L).1 (A.stmt L).2 ++ spongeRounds (ps ++ tail)) H
  rw [pcBad_eq short S τ dl _ (hstmt L).2, pcBadOf_absorbed short S τ dl hP]
  exact hbad

/-- Fiat–Shamir knowledge soundness of the V3 batch as snarkVM verifies it, counting form.

As `sponge_soundness`, with the batch check in place of correct openings. After the six
rounds the verifier absorbs the evaluations message. For each point it squeezes one
short challenge per opened polynomial, then one more that it drops. A copy of the
sponge, taken before those squeezes and fed the proofs' message, gives the randomizers
(`sonic_pc/mod.rs:347-420`). `short` maps an answer to its short element, with at most
`m` elements of `S` per short value. `A` also gives the polynomials behind its three KZG
proofs, and `pfMsg` encodes their values at `τ` injectively. `D` holds all the
verifier's queries, at most `V` for the six squeezes and `V'` for `batch_check`. Then at
most `((Q + V) · b + (Q + V') · m) · | S | ^(n-1)` of the ` | S | ^n` tables, `n` the
length of `D`, give an output the deployed verifier accepts while the relation fails,
with no clash and no defect with root `τ`. A clash is an SRS break, with `κ` the discrete
log of `gamma_g` (`AlgebraicProver.SpongeClashes.trapdoorBreak`), and a defect with root
`τ` a trapdoor break (`DeployedProver.PCBreaks.trapdoorBreak`). -/
theorem deployed_soundness (S : Finset F) {b m : ℕ} (hb : 1 ≤ b) (short : F → F)
    (hm : ∀ x, (S.filter fun a => short a = x).card ≤ m) (A : DeployedProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V V' : ℕ) (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V)
    (hV' : ∀ log, 3 * (A.batch log).circuits.length + 10 ≤ V') (D : List (Transcript F)) (τ : F)
    (pfMsg : List F → FSMessage F) (hpf : Function.Injective pfMsg)
    (hD : ∀ T ∈ tapes S D.length, ∀ q ∈ elemQueries (A.spongeInit (tableRun A.next (tableAns D T) Q))
      [] (A.spongeShape cnt (tableRun A.next (tableAns D T) Q)) ++
        A.pcQueries cnt τ pfMsg (tableRun A.next (tableAns D T) Q), q ∈ D)
    (g : G1) (hg : g ≠ 0) (κ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g κ τ = (P'.absorbed k).commitments g κ τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s ps ps' (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds (ps ++ ps') → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log))
    (hdeg : ∀ log chal, ((A.batch log).withChallenges chal).ResidualsBounded chal b)
    [DecidablePred fun T => A.DeployedFools cnt Q short τ pfMsg D S T ∧
      ¬A.SpongeClashes Q D τ κ T ∧ ¬A.PCBreaks cnt Q short τ D T] :
    ((tapes S D.length).filter fun T => A.DeployedFools cnt Q short τ pfMsg D S T ∧
        ¬A.SpongeClashes Q D τ κ T ∧ ¬A.PCBreaks cnt Q short τ D T).card ≤
      ((Q + V) * b + (Q + V') * m) * S.card ^ (D.length - 1) := by
  classical
  set dl : FSMessage F → List F := Function.invFun pfMsg
  have hdl : ∀ ws, dl (pfMsg ws) = ws := Function.leftInverse_invFun hpf
  have hrep' : ∀ log s ps (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds ps → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log) :=
    fun log s ps P hl hq hs h0 hm =>
      hrep log s ps [] P hl (by rw [List.append_nil]; exact hq) hs h0 hm
  have h1 := table_charge D S (A.spongeNext cnt Q) (A.spongeRB Q S b) b
    (fun _ q H => card_spongeBad_le _ _ (fun _ _ => card_repBad_le S b _ _) q H)
    (fun _ q _ _ hH => spongeBad_congr _ _ _ q hH) (Q + V)
  have h2 := table_charge D S (A.pcNext cnt Q τ pfMsg) (A.pcRB Q short τ S dl) m
    (fun _ q H => card_pcBad_le short S τ dl hm _ q H)
    (fun _ q _ _ hH => pcBad_congr short S τ dl _ q hH) (Q + V')
  refine (card_le_card fun T hT => ?_).trans
    ((card_union_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring)))
  obtain ⟨hTt, ⟨hacc, hnot⟩, hnc, hpb⟩ := mem_filter.1 hT
  have hDT := hD T hTt
  by_cases hbr : outputBreaks (prefixBad (A.out (tableRun A.next (tableAns D T) Q))
      ((A.batch (tableRun A.next (tableAns D T) Q)).badAt S
        (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))))
      (A.out (tableRun A.next (tableAns D T) Q))
      (A.spongeChal cnt (tableAns D T) (tableRun A.next (tableAns D T) Q)) = true
  · exact mem_union_left _ (mem_filter.2 ⟨hTt, sponge_hit S hb A.toAlgebraicProver cnt Q V hV D g
      hg κ τ msgs hmsgs idx hstmt hout hrep' hdeg (fun q hq => hDT q (List.mem_append_left _ hq))
      hacc.msg hbr hnc⟩)
  by_cases hl : PCLucky τ (A.points cnt (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.xis cnt short (tableAns D T) (tableRun A.next (tableAns D T) Q))
      (A.rands cnt short τ pfMsg (tableAns D T) (tableRun A.next (tableAns D T) Q))
  · exact mem_union_right _ (mem_filter.2 ⟨hTt, pc_hit S short A cnt Q V' hV' D g hg κ τ pfMsg dl
      hdl msgs hmsgs idx hstmt hout hrep hTt (fun q hq => hDT q (List.mem_append_right _ hq)) hl
      hnc⟩)
  · exact absurd (holds_of_deployedAccepts hacc (Bool.eq_false_iff.mpr hbr) hl hpb) hnot

/-- `deployed_soundness` with `b` computed from `DegreeBounds`, as in
`sponge_soundness_concrete`. -/
theorem deployed_soundness_concrete (S : Finset F) (d : DegreeBounds) (hX : 1 ≤ d.X) {m : ℕ}
    (short : F → F) (hm : ∀ x, (S.filter fun a => short a = x).card ≤ m)
    (A : DeployedProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V V' : ℕ) (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V)
    (hV' : ∀ log, 3 * (A.batch log).circuits.length + 10 ≤ V') (D : List (Transcript F)) (τ : F)
    (pfMsg : List F → FSMessage F) (hpf : Function.Injective pfMsg)
    (hD : ∀ T ∈ tapes S D.length, ∀ q ∈ elemQueries (A.spongeInit (tableRun A.next (tableAns D T) Q))
      [] (A.spongeShape cnt (tableRun A.next (tableAns D T) Q)) ++
        A.pcQueries cnt τ pfMsg (tableRun A.next (tableAns D T) Q), q ∈ D)
    (g : G1) (hg : g ≠ 0) (κ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g κ τ = (P'.absorbed k).commitments g κ τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s ps ps' (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ spongeRounds (ps ++ ps') → V3StmtWF s →
      P.absorbed 0 = idx s → ps.map Prod.fst = msgs ps.length P →
      (A.rep log).absorbed 0 = idx s ∧ ps.map Prod.fst = msgs ps.length (A.rep log))
    (hW : ∀ log, (A.batch log).Within d)
    [DecidablePred fun T => A.DeployedFools cnt Q short τ pfMsg D S T ∧
      ¬A.SpongeClashes Q D τ κ T ∧ ¬A.PCBreaks cnt Q short τ D T] :
    ((tapes S D.length).filter fun T => A.DeployedFools cnt Q short τ pfMsg D S T ∧
        ¬A.SpongeClashes Q D τ κ T ∧ ¬A.PCBreaks cnt Q short τ D T).card ≤
      ((Q + V) * d.b + (Q + V') * m) * S.card ^ (D.length - 1) :=
  deployed_soundness S d.one_le_b short hm A cnt Q V V' hV hV' D τ pfMsg hpf hD g hg κ msgs hmsgs
    idx hstmt hout hrep fun log chal => ((hW log).withChallenges chal).residualsBounded hX chal

end V3Batch

end Varuna