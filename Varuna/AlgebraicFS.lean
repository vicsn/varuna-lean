/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchFS

/-!
# Algebraic extraction at query time

`V3Batch.oracle_soundness` reads the prover's batch off its messages with an
extractor (`ExtractsBefore`), so the polynomial behind a commitment is treated as a
function of the commitment : the binding floor. An algebraic prover instead gives,
with each query, the batch it represents : the polynomials behind the commitments
in the query, and what the query carries in the clear (`AlgebraicProver`).

The bad set of a query is then read off that batch (`repBad`), a function of the
tape entries before the query, which `card_hits_le` still charges
(`fs_view_rounds_charge`).

A batch is what its messages carry in the clear (`V3Batch.shape`) and the
representations of its commitments (`V3Batch.committed`). A commitment is represented
over the SRS powers of `g` and of `gamma_g = κ g` : a pair `(a, b)` of polynomials, the
element `(a(τ) + κ b(τ)) · g`. Along `g` it is the polynomial, shifted by `X^{M−d}` with
a part below the shift when it has degree bound `d` (`g₁` and the `g_M`), and along
`gamma_g` its blinding. The two determine the batch up to the representation of `h₀`
and the low parts' multiples of the shift (`V3Batch.normal_eq_of`), which no bad set
reads (`V3Batch.badAt_normal`). Equal messages give the same clear part and the same
commitments. So the batch represented with a query and the output batch, on the same
messages, have the same bad set unless two different representations give the same
element (`Clash`). A clash is a nonzero `A(X) + Y B(X)` with root `(τ, κ)`
(`Clash.trapdoorBreak`).

`V3Batch.algebraic_soundness` : on the tapes with no clash, at most
`(Q + V) · b · | S | ^{Q+V-1}` give a run on which the verifier accepts while the
relation fails.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Bad sets that read the view -/

/-- `fs_rounds_charge` with bad sets that also read the adversary's view, the tape
entries before the query. If on the tapes of `E` some query decodes as a well-formed
statement's encoding followed by rounds, and its answer is in the bad set of that
view, statement and history, at most `Q · b · | S | ^{Q-1}` tapes yield `E`. -/
theorem fs_view_rounds_charge {Stmt : Type*} (enc : Stmt → Transcript F) (WF : Stmt → Prop)
    (hinj : ∀ s s' rs rs', WF s → WF s' → NoLoneField rs → NoLoneField rs' →
      enc s ++ encodeRounds rs = enc s' ++ encodeRounds rs' → s = s' ∧ rs = rs')
    (S : Finset F) (A : FSAdversary F) (RB : List F → Stmt → List (Round F) → Finset F) (b : ℕ)
    (hb : ∀ v s rs, (S.filter (· ∈ RB v s rs)).card ≤ b) (Q : ℕ) (E : List F → Prop)
    [DecidablePred E]
    (hE : ∀ tape ∈ tapes S Q, E tape → ∃ s rs, WF s ∧ NoLoneField rs ∧
      ∃ i, ∃ hi : i < tape.length, A.query (tape.take i) = enc s ++ encodeRounds rs ∧
        tape[i] ∈ RB (tape.take i) s rs) :
    ((tapes S Q).filter E).card ≤ Q * b * S.card ^ (Q - 1) := by
  have h := card_hits_le S (fun v => queryBad enc WF (RB v) (A.query v)) (fun _ => b)
    (fun v => card_filter_queryBad_le (hb v) _) Q []
  simp only [sum_const, card_range, smul_eq_mul] at h
  refine (card_le_card fun tape htape => ?_).trans h
  obtain ⟨hmem, he⟩ := mem_filter.mp htape
  obtain ⟨s, rs, hs, hrs, i, hi, hq, hbad⟩ := hE tape hmem he
  refine mem_filter.mpr ⟨hmem, (hitsB_iff _ _ _).mpr ⟨i, hi, ?_⟩⟩
  rw [List.nil_append, hq, queryBad_eq hinj (RB _) hs hrs]
  exact hbad

/-! ## A batch from its clear part and its polynomials -/

namespace BatchInstance

/-- The instance with `ŵ` cleared. -/
noncomputable def shape (x : BatchInstance F) : BatchInstance F :=
  { x with w := 0 }

theorem eq_of_shape {x x' : BatchInstance F} (h : x.shape = x'.shape) (hw : x.w = x'.w) :
    x = x' :=
  calc x = { x.shape with w := x.w } := rfl
    _ = { x'.shape with w := x'.w } := by rw [h, hw]
    _ = x' := rfl

theorem list_eq_of_shape : ∀ {xs ys : List (BatchInstance F)}, xs.map shape = ys.map shape →
    xs.map w = ys.map w → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hw => by
    simp only [List.map_cons, List.cons.injEq] at h hw
    rw [eq_of_shape h.1 hw.1, list_eq_of_shape h.2 hw.2]

end BatchInstance

namespace BatchCircuit

/-- The circuit with its instances' `ŵ` and its matrix `g`s cleared. -/
noncomputable def shape (c : BatchCircuit F) : BatchCircuit F :=
  { c with gA := 0, gB := 0, gC := 0, insts := c.insts.map BatchInstance.shape }

/-- The circuit's committed polynomials : each instance's `ŵ`, then the matrix `g`s. -/
def committed (c : BatchCircuit F) : List F[X] :=
  c.insts.map BatchInstance.w ++ [c.gA, c.gB, c.gC]

theorem length_committed_of_shape {c c' : BatchCircuit F} (h : c.shape = c'.shape) :
    c.committed.length = c'.committed.length := by
  have := congrArg (fun c => c.insts.length) h
  simp only [shape, List.length_map] at this
  simp [committed, this]

theorem eq_of_shape {c c' : BatchCircuit F} (h : c.shape = c'.shape)
    (hp : c.committed = c'.committed) : c = c' := by
  have hlen : (c.insts.map BatchInstance.w).length = (c'.insts.map BatchInstance.w).length := by
    have := length_committed_of_shape h
    simp only [committed, List.length_append] at this
    simpa using this
  obtain ⟨hw, hg⟩ := List.append_inj hp hlen
  simp only [List.cons.injEq, and_true] at hg
  obtain ⟨hA, hB, hC⟩ := hg
  have hi : c.insts = c'.insts :=
    BatchInstance.list_eq_of_shape (congrArg BatchCircuit.insts h) hw
  calc c = { c.shape with gA := c.gA, gB := c.gB, gC := c.gC, insts := c.insts } := rfl
    _ = { c'.shape with gA := c'.gA, gB := c'.gB, gC := c'.gC, insts := c'.insts } := by
      rw [h, hA, hB, hC, hi]
    _ = c' := rfl

end BatchCircuit

/-- A polynomial committed with degree bound `n − 2` under an SRS whose largest power is
`M` : shifted by `X^{M−(n−2)}`, with `l` below the shift (`sonic_pc/mod.rs:233-240`). -/
noncomputable def shiftedRep (M n : ℕ) (p l : F[X]) : F[X] :=
  X ^ (M - (n - 2)) * p + l %ₘ X ^ (M - (n - 2))

theorem shiftedRep_inj {M n : ℕ} {p p' l l' : F[X]} (h : shiftedRep M n p l = shiftedRep M n p' l') :
    p = p' ∧ l %ₘ X ^ (M - (n - 2)) = l' %ₘ X ^ (M - (n - 2)) :=
  shift_add_modByMonic_inj h

namespace CircuitExtra

variable (M : ℕ) (c : BatchCircuit F) (x : CircuitExtra F)

/-- One blinding per instance, `0` past the given list. -/
noncomputable def wBlinds : List F[X] :=
  (List.range c.insts.length).map (x.wBlind.getD · 0)

/-- The commitment data with as many `ŵ` blindings as instances and the low parts reduced
below their shifts. -/
noncomputable def normal : CircuitExtra F :=
  { wBlind := x.wBlinds c
    gALow := x.gALow %ₘ X ^ (M - (c.KA.n - 2))
    gBLow := x.gBLow %ₘ X ^ (M - (c.KB.n - 2))
    gCLow := x.gCLow %ₘ X ^ (M - (c.KC.n - 2))
    gABlind := x.gABlind
    gBBlind := x.gBBlind
    gCBlind := x.gCBlind }

end CircuitExtra

namespace BatchCircuit

variable (M : ℕ) (c : BatchCircuit F) (x : CircuitExtra F)

/-- The representations of the circuit's commitments : each instance's `ŵ` with its
blinding, then each matrix `g`, with degree bound the size of `K_M` less 2
(`fourth.rs:65-67`). -/
noncomputable def reps : List (F[X] × F[X]) :=
  (c.insts.map BatchInstance.w).zip (x.wBlinds c) ++
    [(shiftedRep M c.KA.n c.gA x.gALow, x.gABlind), (shiftedRep M c.KB.n c.gB x.gBLow, x.gBBlind),
      (shiftedRep M c.KC.n c.gC x.gCLow, x.gCBlind)]

theorem length_reps : (c.reps M x).length = c.insts.length + 3 := by
  simp [reps, CircuitExtra.wBlinds]

theorem eq_of_reps {c c' : BatchCircuit F} {x x' : CircuitExtra F} (h : c.shape = c'.shape)
    (hp : c.reps M x = c'.reps M x') : c = c' ∧ x.normal M c = x'.normal M c' := by
  have hn : c.insts.length = c'.insts.length := by
    simpa [shape] using congrArg (fun c => c.insts.length) h
  have hlen : ((c.insts.map BatchInstance.w).zip (x.wBlinds c)).length =
      ((c'.insts.map BatchInstance.w).zip (x'.wBlinds c')).length := by
    simp [CircuitExtra.wBlinds, hn]
  obtain ⟨hz, hg⟩ := List.append_inj hp hlen
  have hu := congrArg List.unzip hz
  rw [List.unzip_zip (by simp [CircuitExtra.wBlinds]),
    List.unzip_zip (by simp [CircuitExtra.wBlinds])] at hu
  obtain ⟨hw, hb⟩ := Prod.mk.inj hu
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hg
  obtain ⟨⟨hA, hAb⟩, ⟨hB, hBb⟩, ⟨hC, hCb⟩⟩ := hg
  have hK : c.KA = c'.KA ∧ c.KB = c'.KB ∧ c.KC = c'.KC :=
    show c.shape.KA = c'.shape.KA ∧ c.shape.KB = c'.shape.KB ∧ c.shape.KC = c'.shape.KC by
      rw [h]; exact ⟨rfl, rfl, rfl⟩
  rw [hK.1] at hA
  rw [hK.2.1] at hB
  rw [hK.2.2] at hC
  obtain ⟨hA, hAl⟩ := shiftedRep_inj hA
  obtain ⟨hB, hBl⟩ := shiftedRep_inj hB
  obtain ⟨hC, hCl⟩ := shiftedRep_inj hC
  have hcc : c = c' := eq_of_shape h (by rw [committed, committed, hw, hA, hB, hC])
  subst hcc
  refine ⟨rfl, ?_⟩
  simp only [CircuitExtra.normal, hb, hAl, hBl, hCl, hAb, hBb, hCb]

end BatchCircuit

/-- `cs`'s circuits and commitment data determine the circuits, and the data up to
`normal`, from the circuits' clear parts and the representations of their commitments. -/
theorem circuitReps_eq (M : ℕ) :
    ∀ {cs cs' : List (BatchCircuit F × CircuitExtra F)},
      cs.map (fun p => p.1.shape) = cs'.map (fun p => p.1.shape) →
      cs.flatMap (fun p => p.1.reps M p.2) = cs'.flatMap (fun p => p.1.reps M p.2) →
      cs.map Prod.fst = cs'.map Prod.fst ∧
        cs.map (fun p => p.2.normal M p.1) = cs'.map fun p => p.2.normal M p.1
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: cs, p' :: cs', h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.flatMap_cons] at hp
    have hlen : (p.1.reps M p.2).length = (p'.1.reps M p'.2).length := by
      rw [BatchCircuit.length_reps, BatchCircuit.length_reps]
      simpa [BatchCircuit.shape] using congrArg (fun c => c.insts.length) h.1
    obtain ⟨h1, h2⟩ := List.append_inj hp hlen
    obtain ⟨e1, e2⟩ := BatchCircuit.eq_of_reps M h.1 h1
    obtain ⟨e3, e4⟩ := circuitReps_eq M h.2 h2
    simp only [List.map_cons]
    exact ⟨by rw [e1, e3], by rw [e2, e4]⟩

namespace V3Batch

/-- The batch with every committed polynomial and its commitment data cleared : the
index, the public inputs, the sums its messages carry in the clear, the challenges, and
the opened values. -/
noncomputable def shape (P : V3Batch F) : V3Batch F :=
  { P with
    circuits := P.circuits.map BatchCircuit.shape
    mask := 0
    h0rep := []
    h1 := 0
    g1 := 0
    h2 := 0
    ext := {} }

/-- Each circuit with its commitment data, the default past the given list. -/
noncomputable def circuitsExt (P : V3Batch F) : List (BatchCircuit F × CircuitExtra F) :=
  P.circuits.mapIdx fun i c => (c, P.ext.circuits.getD i {})

theorem map_fst_circuitsExt (P : V3Batch F) : P.circuitsExt.map Prod.fst = P.circuits :=
  List.ext_getElem (by simp [circuitsExt]) fun i _ _ => by simp [circuitsExt]

theorem map_shape_circuitsExt (P : V3Batch F) :
    P.circuitsExt.map (fun p => p.1.shape) = P.circuits.map BatchCircuit.shape := by
  rw [← map_fst_circuitsExt P, List.map_map]
  rfl

/-- The representations of the commitments : the mask, `h₀`, `h₁`, `g₁` with degree
bound the size of `C` less 2 (`third.rs:60`), `h₂`, then each circuit's, each with its
blinding. -/
noncomputable def committed (P : V3Batch F) : List (F[X] × F[X]) :=
  (P.mask, P.ext.maskBlind) :: (toPoly P.h0rep, P.ext.h0Blind) :: (P.h1, P.ext.h1Blind) ::
    (shiftedRep P.srsMax P.Cd.n P.g1 P.ext.g1Low, P.ext.g1Blind) :: (P.h2, P.ext.h2Blind) ::
      P.circuitsExt.flatMap fun p => p.1.reps P.srsMax p.2

/-- The batch with `h₀` represented by its coefficients and the commitment data in
normal form. -/
noncomputable def normal (P : V3Batch F) : V3Batch F :=
  { P with
    h0rep := coeffList (toPoly P.h0rep)
    ext := { P.ext with
      g1Low := P.ext.g1Low %ₘ X ^ (P.srsMax - (P.Cd.n - 2))
      circuits := P.circuitsExt.map fun p => p.2.normal P.srsMax p.1 } }

/-- The clear part and the representations of the commitments determine the batch, up
to the representation of `h₀` and the normal form of the commitment data. -/
theorem normal_eq_of {P P' : V3Batch F} (h : P.shape = P'.shape)
    (hp : P.committed = P'.committed) : P.normal = P'.normal := by
  simp only [committed, List.cons.injEq, Prod.mk.injEq] at hp
  obtain ⟨⟨hm, hmb⟩, ⟨h0, h0b⟩, ⟨h1, h1b⟩, ⟨hg1, hg1b⟩, ⟨h2, h2b⟩, hc⟩ := hp
  have hM : P.srsMax = P'.srsMax := show P.shape.srsMax = P'.shape.srsMax by rw [h]
  have hCd : P.Cd = P'.Cd := show P.shape.Cd = P'.shape.Cd by rw [h]
  rw [hM, hCd] at hg1
  obtain ⟨hg1, hg1l⟩ := shiftedRep_inj hg1
  rw [hM] at hc
  obtain ⟨hcs, hce⟩ := circuitReps_eq P'.srsMax
    (by rw [map_shape_circuitsExt, map_shape_circuitsExt]; exact congrArg V3Batch.circuits h) hc
  rw [map_fst_circuitsExt, map_fst_circuitsExt] at hcs
  calc P.normal = { P.shape with
          circuits := P.circuits, mask := P.mask, h0rep := coeffList (toPoly P.h0rep),
          h1 := P.h1, g1 := P.g1, h2 := P.h2,
          ext :=
            { maskBlind := P.ext.maskBlind, h0Blind := P.ext.h0Blind, h1Blind := P.ext.h1Blind
              g1Low := P.ext.g1Low %ₘ X ^ (P.srsMax - (P.Cd.n - 2))
              g1Blind := P.ext.g1Blind, h2Blind := P.ext.h2Blind
              circuits := P.circuitsExt.map fun p => p.2.normal P.srsMax p.1 } } := rfl
    _ = { P'.shape with
          circuits := P'.circuits, mask := P'.mask, h0rep := coeffList (toPoly P'.h0rep),
          h1 := P'.h1, g1 := P'.g1, h2 := P'.h2,
          ext :=
            { maskBlind := P'.ext.maskBlind, h0Blind := P'.ext.h0Blind, h1Blind := P'.ext.h1Blind
              g1Low := P'.ext.g1Low %ₘ X ^ (P'.srsMax - (P'.Cd.n - 2))
              g1Blind := P'.ext.g1Blind, h2Blind := P'.ext.h2Blind
              circuits := P'.circuitsExt.map fun p => p.2.normal P'.srsMax p.1 } } := by
      rw [h, hcs, hm, hmb, h0, h0b, h1, h1b, hg1, hg1b, h2, h2b, hM, hCd, hg1l, hce]
    _ = P'.normal := rfl

theorem squeezeBad_normal (P : V3Batch F) (S : Finset F) (chal : V2Challenge → List F) :
    P.normal.squeezeBad S chal = P.squeezeBad S chal := by
  have h : toPoly P.normal.h0rep = toPoly P.h0rep := toPoly_coeffList _
  unfold squeezeBad rowResidual
  rw [h]
  rfl

/-- No bad set reads the representation of `h₀` or the commitment data. -/
theorem badAt_normal (P : V3Batch F) (S : Finset F) (chal : V2Challenge → List F)
    (c : V2Challenge) (w : List F) : P.normal.badAt S chal c w = P.badAt S chal c w :=
  congrFun (congrFun (squeezeBad_normal (P.withChallenges chal) S chal) c) w

end V3Batch

/-! ## Commitments and clashes -/

/-- Two different representations at the same position of `ps` and `qs` of the same
element. -/
def Clash (τ κ : F) (ps qs : List (F[X] × F[X])) : Prop :=
  ∃ i, ∃ hp : i < ps.length, ∃ hq : i < qs.length,
    ps[i] ≠ qs[i] ∧ repEval τ κ ps[i] = repEval τ κ qs[i]

/-- A clash is an SRS break : the difference is nonzero and vanishes at `(τ, κ)`. -/
theorem Clash.trapdoorBreak {τ κ : F} {ps qs : List (F[X] × F[X])} (h : Clash τ κ ps qs) :
    ∃ br : SRSBreak F, br.holds τ κ := by
  obtain ⟨i, hp, hq, hne, hev⟩ := h
  refine SRSBreak.of_polys (A := ps[i].1 - qs[i].1) (B := ps[i].2 - qs[i].2) ?_ ?_
  · by_contra h0
    push Not at h0
    exact hne (Prod.ext (sub_eq_zero.mp h0.1) (sub_eq_zero.mp h0.2))
  · simp only [repEval] at hev
    simp only [eval_sub]
    linear_combination hev

theorem eq_of_not_clash {τ κ : F} {ps qs : List (F[X] × F[X])}
    (h : ps.map (repEval τ κ) = qs.map (repEval τ κ)) (hnc : ¬Clash τ κ ps qs) :
    ps = qs := by
  have hlen : ps.length = qs.length := by simpa using congrArg List.length h
  refine List.ext_getElem hlen fun i hp hq => ?_
  by_contra hne
  refine hnc ⟨i, hp, hq, hne, ?_⟩
  have := congrArg (fun l => l[i]?) h
  simpa [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hq] using this

variable {G1 : Type*} [AddCommGroup G1] [Module F G1]

/-- The commitments `(a(τ) + κ b(τ)) · g` the batch's messages carry, with `gamma_g = κ g`. -/
noncomputable def V3Batch.commitments (g : G1) (κ τ : F) (P : V3Batch F) : List G1 :=
  P.committed.map fun r => repEval τ κ r • g

theorem V3Batch.map_eval_eq_of_commitments {g : G1} (hg : g ≠ 0) {κ τ : F} {P P' : V3Batch F}
    (h : P.commitments g κ τ = P'.commitments g κ τ) :
    P.committed.map (repEval τ κ) = P'.committed.map (repEval τ κ) := by
  have hmap : ∀ Q : V3Batch F,
      Q.commitments g κ τ = (Q.committed.map (repEval τ κ)).map fun x => x • g := fun Q => by
    simp [V3Batch.commitments, Function.comp_def]
  rw [hmap, hmap] at h
  exact List.map_injective_iff.mpr (smul_left_injective F hg) h

/-! ## The bad set of the represented batch -/

/-- The bad set of a history for the batch `P` represented with the query : `P`'s bad
set at the squeeze after the history's last message, with the history's squeezes as
challenges; kept if it has at most `b` elements. -/
noncomputable def repBad (S : Finset F) (b : ℕ) (P : V3Batch F) (hist : List (Round F)) :
    Finset F :=
  match squeezeAfter hist.length with
  | some c =>
    if (P.badAt S (histChal hist) c (histChal hist c)).card ≤ b then
      P.badAt S (histChal hist) c (histChal hist c)
    else ∅
  | none => ∅

theorem card_repBad_le (S : Finset F) (b : ℕ) (P : V3Batch F) (hist : List (Round F)) :
    (S.filter (· ∈ repBad S b P hist)).card ≤ b := by
  unfold repBad
  split
  · split_ifs with h
    · exact (card_filter_mem_le _ _).trans h
    · simp
  · simp

/-- At an element's history, the bad set of a batch that agrees with `B` on what the
messages before it fix is `B`'s bad set at that element, if that has at most `b`
elements. -/
theorem repBad_history {P B : V3Batch F} {c : V2Challenge}
    (hP : (P.absorbed c.prefixAbsorbs).normal = (B.absorbed c.prefixAbsorbs).normal)
    (S : Finset F) (b : ℕ) (t : V2Transcript F) (chal : V2Challenge → List F) (j : ℕ)
    (hcard : (B.badAt S chal c ((chal c).take j)).card ≤ b) :
    repBad S b P (t.history chal c j) = B.badAt S chal c ((chal c).take j) := by
  have key : P.badAt S (histChal (t.history chal c j)) c ((chal c).take j) =
      B.badAt S chal c ((chal c).take j) := by
    rw [← V3Batch.badAt_absorbed P, ← V3Batch.badAt_normal (P.absorbed c.prefixAbsorbs), hP,
      V3Batch.badAt_normal, V3Batch.badAt_absorbed]
    exact V3Batch.badAt_congr _ _ (fun c' hc' => t.histChal_history_lt chal hc' j) _
  rw [repBad, t.length_history, squeezeAfter_prefixAbsorbs]
  simp only
  rw [t.histChal_history_self, key, if_pos hcard]

/-! ## Algebraic soundness -/

/-- An algebraic V3 prover against a random oracle with memory : with each query it
gives the batch it represents, the polynomials behind the commitments in the query
and what the query carries in the clear. -/
structure AlgebraicProver (F : Type*) [Field F] extends OracleProver F where
  rep : QueryLog F → V3Batch F

namespace AlgebraicProver

variable (A : AlgebraicProver F) (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ)

/-- The batch represented with the query asked once the tape entries `v` are used :
`A.rep` of the log so far for one of `A`'s queries, `A`'s output batch for the
verifier's. -/
noncomputable def repAt (v : List F) : V3Batch F :=
  if (memoRun (withVerifier A.next Q (A.verifier cnt)) (Q + V) [] v).1.length < Q then
    A.rep (memoRun (withVerifier A.next Q (A.verifier cnt)) (Q + V) [] v).1
  else A.batch ((memoRun (withVerifier A.next Q (A.verifier cnt)) (Q + V) [] v).1.take Q)

/-- On `tape`, a batch `A` represents with one of its queries and its output batch
have two different representations of the same element among what the first `k`
messages fix. -/
def Clashes (τ κ : F) (tape : List F) : Prop :=
  ∃ m < Q, ∃ k, Clash τ κ ((A.rep ((A.run cnt Q V tape).take m)).absorbed k).committed
    ((A.batch (A.view cnt Q V tape)).absorbed k).committed

/-- A clash is an SRS break. -/
theorem Clashes.trapdoorBreak {τ κ : F} {tape : List F} (h : A.Clashes cnt Q V τ κ tape) :
    ∃ br : SRSBreak F, br.holds τ κ := by
  obtain ⟨_, _, _, hc⟩ := h
  exact Varuna.Clash.trapdoorBreak hc

end AlgebraicProver

namespace V3Batch

/-- Fiat–Shamir knowledge soundness of the V3 batch against an algebraic prover and
a random oracle with memory, counting form.

The prover `A` makes `Q` queries, and with each one whose messages encode some batch
it gives a batch representing them (`rep`). The first `k` messages of a batch are
`msgs k`; given the index, they determine what the first `k` messages fix in the
clear and the commitments, with `gamma_g = κ g` (the encoding floor). The output batch has the
statement's index `idx` and the output's messages. The verifier recomputes the
challenges with at most `V` queries. Then at most `(Q + V) · b · | S | ^{Q+V-1}` of the
` | S | ^{Q+V}` tapes give a run on which the verifier accepts while the relation
fails and no represented batch clashes with the output batch; a clash is an SRS break
(`AlgebraicProver.Clashes.trapdoorBreak`). -/
theorem algebraic_soundness (S : Finset F) {b : ℕ} (hb : 1 ≤ b) (A : AlgebraicProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ) (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V)
    (g : G1) (hg : g ≠ 0) (κ τ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g κ τ = (P'.absorbed k).commitments g κ τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s hist (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ encodeRounds hist → V3StmtWF s → NoLoneField hist →
      P.absorbed 0 = idx s → hist.map Prod.fst = msgs hist.length P →
      (A.rep log).absorbed 0 = idx s ∧ hist.map Prod.fst = msgs hist.length (A.rep log))
    (hdeg : ∀ log chal, ((A.batch log).withChallenges chal).ResidualsBounded chal b)
    [DecidablePred fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ κ tape] :
    ((tapes S (Q + V)).filter fun tape =>
        A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ κ tape).card ≤
      (Q + V) * b * S.card ^ (Q + V - 1) := by
  refine fs_view_rounds_charge (fun s => v3Init s.1 s.2) V3StmtWF
    (fun _ _ _ _ hs hs' hr hr' h => v3Init_rounds_inj hs hs' hr hr' h) S
    (memoAdversary (withVerifier A.next Q (A.verifier cnt)) (Q + V))
    (fun v _ hist => repBad S b (A.repAt cnt Q V v) hist) b
    (fun v _ hist => card_repBad_le S b _ hist) (Q + V)
    (fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ κ tape)
    fun tape htape ⟨hfool, hnc⟩ => ?_
  obtain ⟨hacc, hnot⟩ := hfool
  have hlen : (A.run cnt Q V tape).length = Q + V :=
    length_runLog A.next Q (A.verifier cnt) V (mem_tapes htape).1
  -- A squeezed element in its bad set.
  have hbr : outputBreaks (prefixBad (A.out (A.view cnt Q V tape))
      ((A.batch (A.view cnt Q V tape)).badAt S (A.chal cnt Q V tape)))
      (A.out (A.view cnt Q V tape)) (A.chal cnt Q V tape) = true := by
    by_contra hne
    exact hnot (holds_of_accepts hacc (Bool.eq_false_iff.mpr hne))
  obtain ⟨c, -, hc⟩ := List.any_eq_true.mp hbr
  obtain ⟨j, hj, hbad⟩ := (hitsB_iff _ _ _).mp hc
  rw [List.nil_append, prefixBad_elemBefore hacc.msg] at hbad
  -- The query that answered it.
  have hrfq : RoundsFromQueries (memoAdversary (withVerifier A.next Q (A.verifier cnt)) (Q + V))
      tape (v3Init (A.stmt (A.view cnt Q V tape)).1 (A.stmt (A.view cnt Q V tape)).2)
      ((A.out (A.view cnt Q V tape)).rounds (A.chal cnt Q V tape)) := by
    rw [OracleProver.chal, V2Transcript.rounds_splitSqueezes]
    refine roundsFromQueries_runLog A.next Q (A.verifier cnt) V
      (fun log => v3Init (A.stmt log).1 (A.stmt log).2)
      (fun log => v2Challenges.map fun c => ((A.out log).msgBefore c, cnt (A.stmt log) c))
      (fun _ => rfl) tape rfl ?_
    simp only [List.map_map, Function.comp_def, List.length_map, List.length_drop]
    exact (hV _).trans (by omega)
  obtain ⟨i, hi, hq, ha⟩ := hrfq _ _ _ _ ((A.out (A.view cnt Q V tape)).rounds_split _ c) j hj
  have hnl := V2Transcript.noLoneField_rounds hacc.msg (A.chal cnt Q V tape)
  have hnlh : NoLoneField ((A.out (A.view cnt Q V tape)).history (A.chal cnt Q V tape) c j) := by
    intro p hp x
    rcases List.mem_append.mp hp with hp | hp
    · exact hnl p (List.mem_of_mem_take hp) x
    · rw [List.mem_singleton.mp hp]
      refine hnl ((A.out (A.view cnt Q V tape)).msgBefore c, A.chal cnt Q V tape c) ?_ x
      rw [(A.out (A.view cnt Q V tape)).rounds_split _ c]
      simp
  refine ⟨A.stmt (A.view cnt Q V tape), _, (hstmt _).2, hnlh, i, hi, hq, ?_⟩
  rw [ha]
  show _ ∈ repBad S b (A.repAt cnt Q V (tape.take i)) _
  rw [repBad_history ?_ S b _ _ j (card_badAt_le hb (hdeg _ _) S c _)]
  · exact hbad
  -- The batch represented with that query fixes what the output batch fixes.
  generalize hLi : (memoRun (withVerifier A.next Q (A.verifier cnt)) (Q + V) [] (tape.take i)).1 =
    Li
  have hpre : Li = (A.run cnt Q V tape).take Li.length := by
    rw [← hLi]
    exact List.prefix_iff_eq_take.mp (memoRun_take_prefix _ _ _ _ _)
  have hstop := memoRun_snd_eq _ _ _ _ (memoRun_snd_of_query hq (by simp [v3Init]))
  rw [hLi] at hstop
  unfold AlgebraicProver.repAt
  rw [hLi]
  split_ifs with hlt
  · rw [withVerifier, if_pos hlt] at hstop
    have hk := (A.out (A.view cnt Q V tape)).length_history (A.chal cnt Q V tape) c j
    have hm : ((A.out (A.view cnt Q V tape)).history (A.chal cnt Q V tape) c j).map Prod.fst =
        msgs c.prefixAbsorbs (A.batch (A.view cnt Q V tape)) := by
      rw [V2Transcript.map_fst_history, (hout _).2]
    obtain ⟨hidx, hmsg⟩ := hrep Li (A.stmt (A.view cnt Q V tape))
      ((A.out (A.view cnt Q V tape)).history (A.chal cnt Q V tape) c j) _ hlt hstop.symm
      (hstmt _).2 hnlh (hout _).1 (by rw [hk]; exact hm)
    rw [hk, hm] at hmsg
    obtain ⟨hshape, hcom⟩ := hmsgs _ _ _ (hidx.trans (hout _).1.symm) hmsg.symm
    refine normal_eq_of hshape (eq_of_not_clash (map_eval_eq_of_commitments hg hcom) ?_)
    intro hcl
    exact hnc ⟨Li.length, hlt, c.prefixAbsorbs, by rw [← hpre]; exact hcl⟩
  · have : Li.take Q = A.view cnt Q V tape := by
      rw [hpre, List.take_take, Nat.min_eq_left (by omega)]
      rfl
    rw [this]

/-- `algebraic_soundness` with `b` computed from `DegreeBounds`, as in
`adaptive_soundness_concrete`. -/
theorem algebraic_soundness_concrete (S : Finset F) (d : DegreeBounds) (hX : 1 ≤ d.X)
    (A : AlgebraicProver F) (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ)
    (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V) (g : G1) (hg : g ≠ 0) (κ τ : F)
    (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g κ τ = (P'.absorbed k).commitments g κ τ)
    (idx : V3Stmt F → V3Batch F)
    (hstmt : ∀ log,
      (A.out log).init = v3Init (A.stmt log).1 (A.stmt log).2 ∧ V3StmtWF (A.stmt log))
    (hout : ∀ log, (A.batch log).absorbed 0 = idx (A.stmt log) ∧
      ∀ k, (A.out log).messages.take k = msgs k (A.batch log))
    (hrep : ∀ log s hist (P : V3Batch F), log.length < Q →
      A.next log = v3Init s.1 s.2 ++ encodeRounds hist → V3StmtWF s → NoLoneField hist →
      P.absorbed 0 = idx s → hist.map Prod.fst = msgs hist.length P →
      (A.rep log).absorbed 0 = idx s ∧ hist.map Prod.fst = msgs hist.length (A.rep log))
    (hW : ∀ log, (A.batch log).Within d)
    [DecidablePred fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ κ tape] :
    ((tapes S (Q + V)).filter fun tape =>
        A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ κ tape).card ≤
      (Q + V) * d.b * S.card ^ (Q + V - 1) :=
  algebraic_soundness S d.one_le_b A cnt Q V hV g hg κ τ msgs hmsgs idx hstmt hout hrep
    fun log chal => ((hW log).withChallenges chal).residualsBounded hX chal

end V3Batch

end Varuna