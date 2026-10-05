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

A batch is what its messages carry in the clear (`V3Batch.shape`) and its committed
polynomials (`V3Batch.committed`). The two determine it up to the representation of
`h₀` (`V3Batch.normal_eq_of`), which no bad set reads (`V3Batch.badAt_normal`). Equal
messages give the same clear part and the same commitments `p(τ) · g`. So the batch
represented with a query and the output batch, on the same messages, have the same
bad set unless two different polynomials have the same value at `τ` (`Clash`). A
clash is a trapdoor break (`Clash.trapdoorBreak`).

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

theorem list_eq_of_shape : ∀ {cs cs' : List (BatchCircuit F)}, cs.map shape = cs'.map shape →
    cs.flatMap committed = cs'.flatMap committed → cs = cs'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, c' :: cs', h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.flatMap_cons] at hp
    obtain ⟨h1, h2⟩ := List.append_inj hp (length_committed_of_shape h.1)
    rw [eq_of_shape h.1 h1, list_eq_of_shape h.2 h2]

end BatchCircuit

namespace V3Batch

/-- The batch with every committed polynomial cleared : the index, the public
inputs, the sums its messages carry in the clear, the challenges, and the opened
values. -/
noncomputable def shape (P : V3Batch F) : V3Batch F :=
  { P with
    circuits := P.circuits.map BatchCircuit.shape
    mask := 0
    h0rep := []
    h1 := 0
    g1 := 0
    h2 := 0 }

/-- The committed polynomials : the mask, `h₀`, `h₁`, `g₁`, `h₂`, then each circuit's. -/
noncomputable def committed (P : V3Batch F) : List F[X] :=
  P.mask :: toPoly P.h0rep :: P.h1 :: P.g1 :: P.h2 :: P.circuits.flatMap BatchCircuit.committed

/-- The batch with `h₀` represented by its coefficients. -/
noncomputable def normal (P : V3Batch F) : V3Batch F :=
  { P with h0rep := coeffList (toPoly P.h0rep) }

/-- The clear part and the committed polynomials determine the batch, up to the
representation of `h₀`. -/
theorem normal_eq_of {P P' : V3Batch F} (h : P.shape = P'.shape)
    (hp : P.committed = P'.committed) : P.normal = P'.normal := by
  simp only [committed, List.cons.injEq] at hp
  obtain ⟨hm, h0, h1, hg1, h2, hc⟩ := hp
  have hcs : P.circuits = P'.circuits :=
    BatchCircuit.list_eq_of_shape (congrArg V3Batch.circuits h) hc
  calc P.normal = { P.shape with
          circuits := P.circuits, mask := P.mask, h0rep := coeffList (toPoly P.h0rep),
          h1 := P.h1, g1 := P.g1, h2 := P.h2 } := rfl
    _ = { P'.shape with
          circuits := P'.circuits, mask := P'.mask, h0rep := coeffList (toPoly P'.h0rep),
          h1 := P'.h1, g1 := P'.g1, h2 := P'.h2 } := by rw [h, hcs, hm, h0, h1, hg1, h2]
    _ = P'.normal := rfl

theorem squeezeBad_normal (P : V3Batch F) (S : Finset F) (chal : V2Challenge → List F) :
    P.normal.squeezeBad S chal = P.squeezeBad S chal := by
  have h : toPoly P.normal.h0rep = toPoly P.h0rep := toPoly_coeffList _
  unfold squeezeBad rowResidual
  rw [h]
  rfl

/-- No bad set reads the representation of `h₀`. -/
theorem badAt_normal (P : V3Batch F) (S : Finset F) (chal : V2Challenge → List F)
    (c : V2Challenge) (w : List F) : P.normal.badAt S chal c w = P.badAt S chal c w :=
  congrFun (congrFun (squeezeBad_normal (P.withChallenges chal) S chal) c) w

end V3Batch

/-! ## Commitments and clashes -/

/-- Two different polynomials at the same position of `ps` and `qs` with the same
value at `τ`. -/
def Clash (τ : F) (ps qs : List F[X]) : Prop :=
  ∃ i, ∃ hp : i < ps.length, ∃ hq : i < qs.length, ps[i] ≠ qs[i] ∧ ps[i].eval τ = qs[i].eval τ

/-- A clash is a trapdoor break : the difference is nonzero and vanishes at `τ`. -/
theorem Clash.trapdoorBreak {τ : F} {ps qs : List F[X]} (h : Clash τ ps qs) :
    ∃ br : TrapdoorBreak F, br.holds τ := by
  obtain ⟨i, hp, hq, hne, hev⟩ := h
  refine ⟨⟨coeffList (ps[i] - qs[i])⟩, ?_, ?_⟩
  · rw [toPoly_coeffList]
    exact sub_ne_zero.mpr hne
  · rw [toPoly_coeffList, eval_sub, hev, sub_self]

theorem eq_of_not_clash {τ : F} {ps qs : List F[X]} (h : ps.map (eval τ) = qs.map (eval τ))
    (hnc : ¬Clash τ ps qs) : ps = qs := by
  have hlen : ps.length = qs.length := by simpa using congrArg List.length h
  refine List.ext_getElem hlen fun i hp hq => ?_
  by_contra hne
  refine hnc ⟨i, hp, hq, hne, ?_⟩
  have := congrArg (fun l => l[i]?) h
  simpa [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hq] using this

variable {G1 : Type*} [AddCommGroup G1] [Module F G1]

/-- The commitments `p(τ) · g` of the batch's committed polynomials. -/
noncomputable def V3Batch.commitments (g : G1) (τ : F) (P : V3Batch F) : List G1 :=
  P.committed.map fun p => p.eval τ • g

theorem V3Batch.map_eval_eq_of_commitments {g : G1} (hg : g ≠ 0) {τ : F} {P P' : V3Batch F}
    (h : P.commitments g τ = P'.commitments g τ) :
    P.committed.map (eval τ) = P'.committed.map (eval τ) := by
  have hmap : ∀ Q : V3Batch F,
      Q.commitments g τ = (Q.committed.map (eval τ)).map fun x => x • g := fun Q => by
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
have two different polynomials with the same value at `τ` among what the first `k`
messages fix. -/
def Clashes (τ : F) (tape : List F) : Prop :=
  ∃ m < Q, ∃ k, Clash τ ((A.rep ((A.run cnt Q V tape).take m)).absorbed k).committed
    ((A.batch (A.view cnt Q V tape)).absorbed k).committed

/-- A clash is a trapdoor break. -/
theorem Clashes.trapdoorBreak {τ : F} {tape : List F} (h : A.Clashes cnt Q V τ tape) :
    ∃ br : TrapdoorBreak F, br.holds τ := by
  obtain ⟨_, _, _, hc⟩ := h
  exact Varuna.Clash.trapdoorBreak hc

end AlgebraicProver

namespace V3Batch

/-- Fiat–Shamir knowledge soundness of the V3 batch against an algebraic prover and
a random oracle with memory, counting form.

The prover `A` makes `Q` queries, and with each one whose messages encode some batch
it gives a batch representing them (`rep`). The first `k` messages of a batch are
`msgs k`; given the index, they determine what the first `k` messages fix in the
clear and the commitments `p(τ) · g` (the encoding floor). The output batch has the
statement's index `idx` and the output's messages. The verifier recomputes the
challenges with at most `V` queries. Then at most `(Q + V) · b · | S | ^{Q+V-1}` of the
` | S | ^{Q+V}` tapes give a run on which the verifier accepts while the relation
fails and no represented batch clashes with the output batch; a clash is a trapdoor
break (`AlgebraicProver.Clashes.trapdoorBreak`). -/
theorem algebraic_soundness (S : Finset F) {b : ℕ} (hb : 1 ≤ b) (A : AlgebraicProver F)
    (cnt : V3Stmt F → V2Challenge → ℕ) (Q V : ℕ) (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V)
    (g : G1) (hg : g ≠ 0) (τ : F) (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g τ = (P'.absorbed k).commitments g τ)
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
    [DecidablePred fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ tape] :
    ((tapes S (Q + V)).filter fun tape =>
        A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ tape).card ≤
      (Q + V) * b * S.card ^ (Q + V - 1) := by
  refine fs_view_rounds_charge (fun s => v3Init s.1 s.2) V3StmtWF
    (fun _ _ _ _ hs hs' hr hr' h => v3Init_rounds_inj hs hs' hr hr' h) S
    (memoAdversary (withVerifier A.next Q (A.verifier cnt)) (Q + V))
    (fun v _ hist => repBad S b (A.repAt cnt Q V v) hist) b
    (fun v _ hist => card_repBad_le S b _ hist) (Q + V)
    (fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ tape)
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
    (hV : ∀ s, (v2Challenges.map (cnt s)).sum ≤ V) (g : G1) (hg : g ≠ 0) (τ : F)
    (msgs : ℕ → V3Batch F → List (FSMessage F))
    (hmsgs : ∀ k (P P' : V3Batch F), P.absorbed 0 = P'.absorbed 0 → msgs k P = msgs k P' →
      (P.absorbed k).shape = (P'.absorbed k).shape ∧
        (P.absorbed k).commitments g τ = (P'.absorbed k).commitments g τ)
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
    [DecidablePred fun tape => A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ tape] :
    ((tapes S (Q + V)).filter fun tape =>
        A.Fools cnt Q V S tape ∧ ¬A.Clashes cnt Q V τ tape).card ≤
      (Q + V) * d.b * S.card ^ (Q + V - 1) :=
  algebraic_soundness S d.one_le_b A cnt Q V hV g hg τ msgs hmsgs idx hstmt hout hrep
    fun log chal => ((hW log).withChallenges chal).residualsBounded hX chal

end V3Batch

end Varuna