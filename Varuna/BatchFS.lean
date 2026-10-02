/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AdaptiveFS
import Varuna.BatchDegree

/-!
# Adaptive Fiat–Shamir for the V3 batch

`V3Batch.sound_of_transcript` holds for a transcript with no break. This file counts
the tapes on which an adaptive prover gets a transcript accepted for a false
statement.

The batch is read off the prover's messages by an extractor `ext` : the
polynomial behind each commitment (the algebraic representation; that it is a
function of the commitment is the binding floor). The one requirement on `ext`
is that it reads each piece of data from the message that carries it in
snarkVM's absorb order (`varuna.rs`) : `ŵ` and the mask from the first-round
message, `h₀` from the second, the prepare-third sums from the prepare-third
message, `g₁, h₁` from the third, the matrix `g`s and sums from the fourth, `h₂`
from the fifth. `V3Batch.upTo k` keeps what the first `k` messages fix, and the
requirement is `(ext s (msgs.take k)).upTo k = (ext s msgs).upTo k`.

The challenges are the squeezes, read as the verifier reads them
(`withChallenges`). Each squeeze's bad set then reads only data absorbed before it
(`squeezeBad_upTo`) and challenges squeezed before it (`badAt_congr`), so it is a
function of the statement and the history (`batchBad`, `batchBad_history`).
`fs_rounds_charge` charges it per query. `batchBad` keeps a bad set only if it has
at most `b` elements, so the charge holds for any `ext`; the prover's own batch
has its bad sets that small when its residuals have degree at most `b`.

`V3Batch.adaptive_soundness` : if every squeezed element was answered on one of
the adversary's `Q` queries, at most `Q · b · | S | ^{Q-1}` of the ` | S | ^Q` tapes
yield a transcript the verifier accepts while the relation fails, where `b ≥ 1`
bounds the degrees of the three batched residuals of the prover's batch.
`V3Batch.adaptive_soundness_concrete` takes `b` from `DegreeBounds` : `D` SRS
powers and the largest domains (`Varuna.BatchDegree`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Rounds of a V3 transcript -/

/-- The message absorbed just before squeeze `c`. -/
def V2Transcript.msgBefore (t : V2Transcript F) : V2Challenge → FSMessage F
  | .firstCombiners => t.first
  | .alpha => t.second
  | .prepareThird => t.prepareThird
  | .beta => t.third
  | .deltas => t.fourth
  | .gamma => t.fifth

/-- A V3 transcript as rounds : each message, then the squeeze after it. -/
def V2Transcript.rounds (t : V2Transcript F) (chal : V2Challenge → List F) : List (Round F) :=
  v2Challenges.map fun c => (t.msgBefore c, chal c)

/-- The history of element `j` of squeeze `c` : the rounds before `c`, then `c`'s
message and its first `j` elements. -/
def V2Transcript.history (t : V2Transcript F) (chal : V2Challenge → List F) (c : V2Challenge)
    (j : ℕ) : List (Round F) :=
  (t.rounds chal).take (c.prefixAbsorbs - 1) ++ [(t.msgBefore c, (chal c).take j)]

theorem V2Transcript.rounds_split (t : V2Transcript F) (chal : V2Challenge → List F)
    (c : V2Challenge) :
    t.rounds chal = (t.rounds chal).take (c.prefixAbsorbs - 1) ++
      (t.msgBefore c, chal c) :: (t.rounds chal).drop c.prefixAbsorbs := by
  cases c <;> rfl

theorem V2Transcript.noLoneField_rounds {t : V2Transcript F}
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) (chal : V2Challenge → List F) :
    NoLoneField (t.rounds chal) := by
  intro p hp x h
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
  have h' : t.msgBefore c = .field x := h
  apply hmsg x
  rw [← h']
  cases c <;> simp [V2Transcript.messages, V2Transcript.msgBefore]

/-- The squeeze after the `k`-th message. -/
def squeezeAfter : ℕ → Option V2Challenge
  | 1 => some .firstCombiners
  | 2 => some .alpha
  | 3 => some .prepareThird
  | 4 => some .beta
  | 5 => some .deltas
  | 6 => some .gamma
  | _ => none

theorem squeezeAfter_prefixAbsorbs (c : V2Challenge) : squeezeAfter c.prefixAbsorbs = some c := by
  cases c <;> rfl

/-- The squeezes of a history : round `k`'s elements at the `k`-th squeeze, none
after the last. -/
def histChal (hist : List (Round F)) (c : V2Challenge) : List F :=
  (hist.map Prod.snd).getD (c.prefixAbsorbs - 1) []

namespace V2Transcript

variable (t : V2Transcript F) (chal : V2Challenge → List F)

theorem length_history (c : V2Challenge) (j : ℕ) : (t.history chal c j).length = c.prefixAbsorbs :=
  by
  cases c <;> simp [history, rounds, v2Challenges, V2Challenge.prefixAbsorbs]

theorem map_fst_history (c : V2Challenge) (j : ℕ) :
    (t.history chal c j).map Prod.fst = t.messages.take c.prefixAbsorbs := by
  cases c <;> simp [history, rounds, v2Challenges, V2Challenge.prefixAbsorbs, messages, msgBefore]

theorem histChal_history_self (c : V2Challenge) (j : ℕ) :
    histChal (t.history chal c j) c = (chal c).take j := by
  cases c <;> simp [histChal, history, rounds, v2Challenges, V2Challenge.prefixAbsorbs]

theorem histChal_history_lt {c c' : V2Challenge} (h : c'.prefixAbsorbs < c.prefixAbsorbs)
    (j : ℕ) : histChal (t.history chal c j) c' = chal c' := by
  cases c <;> cases c' <;>
    simp_all [histChal, history, rounds, v2Challenges, V2Challenge.prefixAbsorbs]

end V2Transcript

/-! ## What the first `k` messages fix -/

/-- The instance as the first `k` messages fix it : `ŵ` from the first-round
message, the prepare-third sums from the prepare-third message. No message carries
the opened `ŵ(β)`. -/
noncomputable def BatchInstance.upTo (k : ℕ) (x : BatchInstance F) : BatchInstance F :=
  { x with
    w := if 1 ≤ k then x.w else 0
    σA := if 3 ≤ k then x.σA else 0
    σB := if 3 ≤ k then x.σB else 0
    σC := if 3 ≤ k then x.σC else 0
    vw := 0 }

/-- The circuit as the first `k` messages fix it : the matrix `g`s and sums from the
fourth-round message (the fifth absorbed). No message carries the opened `g_M(γ)`. -/
noncomputable def BatchCircuit.upTo (k : ℕ) (c : BatchCircuit F) : BatchCircuit F :=
  { c with
    gA := if 5 ≤ k then c.gA else 0
    gB := if 5 ≤ k then c.gB else 0
    gC := if 5 ≤ k then c.gC else 0
    σmA := if 5 ≤ k then c.σmA else 0
    σmB := if 5 ≤ k then c.σmB else 0
    σmC := if 5 ≤ k then c.σmC else 0
    vgA := 0
    vgB := 0
    vgC := 0
    insts := c.insts.map (BatchInstance.upTo k) }

namespace BatchCircuit

variable {k : ℕ} (c : BatchCircuit F) (x : BatchInstance F)

theorem zhat_upTo (hk : 1 ≤ k) : (c.upTo k).zhat (x.upTo k) = c.zhat x := by
  simp [zhat, upTo, BatchInstance.upTo, hk]

theorem rowPoly_upTo (hk : 1 ≤ k) : (c.upTo k).rowPoly (x.upTo k) = c.rowPoly x := by
  rw [rowPoly, zhat_upTo c x hk]
  rfl

theorem target_upTo (hk : 1 ≤ k) (M : SparseMatrix F) (α : F) :
    (c.upTo k).target (x.upTo k) M α = c.target x M α := by
  rw [target, zhat_upTo c x hk]
  rfl

theorem linPoly_upTo (hk : 1 ≤ k) (α ηA ηB ηC : F) :
    (c.upTo k).linPoly (x.upTo k) α ηA ηB ηC = c.linPoly x α ηA ηB ηC := by
  rw [linPoly, zhat_upTo c x hk]
  rfl

theorem matrixTerms_upTo (hk : 5 ≤ k) (α β : F) : (c.upTo k).matrixTerms α β = c.matrixTerms α β :=
  by
  simp [matrixTerms, upTo, hk]

end BatchCircuit

namespace V3Batch

/-- The batch as the first `k` messages fix it, in snarkVM's absorb order : `ŵ` and
the mask from the first-round message, `h₀` from the second, the prepare-third sums
from the prepare-third message, `g₁, h₁` from the third, the matrix `g`s and sums
from the fourth, `h₂` from the fifth. The index, the public inputs, and the
challenges are kept; the opened values, which no message carries, are cleared. -/
noncomputable def upTo (k : ℕ) (P : V3Batch F) : V3Batch F :=
  { P with
    circuits := P.circuits.map (BatchCircuit.upTo k)
    mask := if 1 ≤ k then P.mask else 0
    h0rep := if 2 ≤ k then P.h0rep else []
    vH0 := 0
    h1 := if 4 ≤ k then P.h1 else 0
    g1 := if 4 ≤ k then P.g1 else 0
    h2 := if 6 ≤ k then P.h2 else 0
    vMask := 0
    vH1 := 0
    vG1 := 0
    vH2 := 0 }

/-- The batch with its challenges read off the squeezes, as the verifier reads them. -/
def withChallenges (P : V3Batch F) (chal : V2Challenge → List F) : V3Batch F :=
  { P with
    α := (chal .alpha).headD 0
    β := (chal .beta).headD 0
    γ := (chal .gamma).headD 0
    ηA := (chal .prepareThird).getD (combinerDraws P.sizes) 0
    ηB := (chal .prepareThird).getD (combinerDraws P.sizes + 1) 0
    ηC := (chal .prepareThird).getD (combinerDraws P.sizes + 2) 0 }

variable {k : ℕ} (P : V3Batch F)

theorem sizes_upTo : (P.upTo k).sizes = P.sizes := by
  simp [sizes, upTo, BatchCircuit.upTo, Function.comp_def]

theorem instances_upTo :
    (P.upTo k).instances = P.instances.map fun p => (p.1.upTo k, p.2.upTo k) := by
  simp [instances, upTo, BatchCircuit.upTo, List.flatMap_map, List.map_flatMap,
    Function.comp_def]

theorem rowClaims_upTo (hk : 1 ≤ k) : (P.upTo k).rowClaims = P.rowClaims := by
  simp only [rowClaims, instances_upTo, List.map_map, Function.comp_def,
    BatchCircuit.rowPoly_upTo _ _ hk]
  rfl

theorem e_upTo (hk : 1 ≤ k) : (P.upTo k).e = P.e := by
  simp [e, upTo, hk]

theorem linClaims_upTo (hk : 3 ≤ k) : (P.upTo k).linClaims = P.linClaims := by
  rw [linClaims, linClaims, e_upTo P (by omega), instances_upTo, List.flatMap_map]
  refine congrArg (P.e :: ·) (flatMap_congr_mem fun p _ => ?_)
  simp only [BatchCircuit.target_upTo _ _ (show 1 ≤ k by omega)]
  simp [BatchInstance.upTo, BatchCircuit.upTo, upTo, hk]

theorem rowWeights_upTo (chal : V2Challenge → List F) :
    (P.upTo k).rowWeights chal = P.rowWeights chal := by
  rw [rowWeights, rowWeights, sizes_upTo]

theorem linWeights_upTo (chal : V2Challenge → List F) :
    (P.upTo k).linWeights chal = P.linWeights chal := by
  rw [linWeights, linWeights, sizes_upTo]

theorem deltaWeights_upTo (chal : V2Challenge → List F) :
    (P.upTo k).deltaWeights chal = P.deltaWeights chal := by
  simp [deltaWeights, upTo]

theorem rowResidual_upTo (hk : 2 ≤ k) (ws : List F) :
    (P.upTo k).rowResidual ws = P.rowResidual ws := by
  rw [rowResidual, rowResidual, rowClaims_upTo P (by omega)]
  simp [upTo, hk]

theorem linSum_upTo (hk : 3 ≤ k) (ws : List F) : (P.upTo k).linSum ws = P.linSum ws := by
  rw [linSum, linSum, instances_upTo, List.map_map]
  simp [BatchInstance.upTo, upTo, hk, Function.comp_def]

theorem linResidual_upTo (hk : 4 ≤ k) (ws : List F) :
    (P.upTo k).linResidual ws = P.linResidual ws := by
  rw [linResidual, linResidual, linWitness, linWitness, linSum_upTo P (by omega), linevalPoly,
    linevalPoly, instances_upTo, List.map_map]
  simp only [Function.comp_def, BatchCircuit.linPoly_upTo _ _ (show 1 ≤ k by omega)]
  simp [upTo, hk, BatchCircuit.upTo, show 1 ≤ k by omega]

theorem matrixTerms_upTo (hk : 5 ≤ k) : (P.upTo k).matrixTerms = P.matrixTerms := by
  simp only [matrixTerms, upTo, List.flatMap_map, BatchCircuit.matrixTerms_upTo _ hk]

/-- A squeeze's bad set reads only data absorbed before it. -/
theorem squeezeBad_upTo (S : Finset F) (chal : V2Challenge → List F) (c : V2Challenge)
    (w : List F) : (P.upTo c.prefixAbsorbs).squeezeBad S chal c w = P.squeezeBad S chal c w := by
  cases c with
  | firstCombiners =>
    show (rowcheckDraw _ _ _).bad S w = (rowcheckDraw _ _ _).bad S w
    simp only [V2Challenge.prefixAbsorbs]
    rw [sizes_upTo, rowClaims_upTo P le_rfl]
    rfl
  | alpha =>
    show szAt S _ w = szAt S _ w
    simp only [V2Challenge.prefixAbsorbs]
    rw [rowWeights_upTo, rowResidual_upTo P le_rfl]
  | prepareThird =>
    show (linevalDraw _ _).bad S w = (linevalDraw _ _).bad S w
    simp only [V2Challenge.prefixAbsorbs]
    rw [sizes_upTo, linClaims_upTo P le_rfl]
  | beta =>
    show szAt S _ w = szAt S _ w
    simp only [V2Challenge.prefixAbsorbs]
    rw [linWeights_upTo, linResidual_upTo P le_rfl]
  | deltas =>
    show (deltaDraw _ _ _).bad S w = (deltaDraw _ _ _).bad S w
    simp only [V2Challenge.prefixAbsorbs]
    rw [matrixTerms_upTo P le_rfl]
    simp [upTo]
  | gamma =>
    show szAt S _ w = szAt S _ w
    simp only [V2Challenge.prefixAbsorbs]
    rw [deltaWeights_upTo, matrixTerms_upTo P (by decide)]
    simp [upTo]

theorem upTo_withChallenges (chal : V2Challenge → List F) :
    (P.withChallenges chal).upTo k = (P.upTo k).withChallenges chal := by
  rw [withChallenges, withChallenges, sizes_upTo]
  rfl

/-- `Q`'s bad set at squeeze `c`, its challenges and weights read off `chal`. -/
noncomputable def badAt (Q : V3Batch F) (S : Finset F) (chal : V2Challenge → List F) :
    V2Challenge → List F → Finset F :=
  (Q.withChallenges chal).squeezeBad S chal

/-- What the first `k` messages fix : `upTo k`, with the challenges cleared. -/
noncomputable def absorbed (k : ℕ) (P : V3Batch F) : V3Batch F :=
  (P.withChallenges fun _ => []).upTo k

/-- A squeeze's bad set reads only what the messages before it fix. -/
theorem badAt_absorbed (S : Finset F) (chal : V2Challenge → List F) (c : V2Challenge)
    (w : List F) : (P.absorbed c.prefixAbsorbs).badAt S chal c w = P.badAt S chal c w := by
  unfold badAt absorbed
  rw [← upTo_withChallenges]
  exact squeezeBad_upTo (P.withChallenges chal) S chal c w

theorem Within.withChallenges {Q : V3Batch F} {d : DegreeBounds} (hW : Q.Within d)
    (chal : V2Challenge → List F) : (Q.withChallenges chal).Within d :=
  ⟨hW.R, hW.Cd, hW.K, hW.circR, hW.circC, hW.circX, hW.circK, hW.w, hW.mask, hW.h0, hW.h1,
    hW.g1, hW.g, hW.h2⟩

/-- With its three residuals at most `b ≥ 1`, every squeeze's bad set has at most
`b` elements. -/
theorem card_badAt_le {Q : V3Batch F} {chal : V2Challenge → List F} {b : ℕ} (hb : 1 ≤ b)
    (h : (Q.withChallenges chal).ResidualsBounded chal b) (S : Finset F) (c : V2Challenge)
    (w : List F) : (Q.badAt S chal c w).card ≤ b := by
  obtain ⟨h1, h2, h3⟩ := h
  exact squeezeBad_card S _ _ _ _ _ _ (rowcheckDraw_coordAffine _ _ _)
    (linevalDraw_coordAffine _ _) (deltaDraw_coordAffine _ _ _) h1 h2 h3 hb c w

/-- A squeeze's bad set reads only challenges squeezed before it. -/
theorem badAt_congr (Q : V3Batch F) (S : Finset F) {chal chal' : V2Challenge → List F}
    {c : V2Challenge} (h : ∀ c', c'.prefixAbsorbs < c.prefixAbsorbs → chal c' = chal' c')
    (w : List F) : Q.badAt S chal c w = Q.badAt S chal' c w := by
  cases c with
  | firstCombiners => rfl
  | alpha =>
    have h1 := h .firstCombiners (by decide)
    show szAt S _ w = szAt S _ w
    simp only [rowWeights, h1]
    rfl
  | prepareThird =>
    have h2 := h .alpha (by decide)
    show (linevalDraw _ _).bad S w = (linevalDraw _ _).bad S w
    simp only [linClaims, withChallenges, h2]
    rfl
  | beta =>
    have h2 := h .alpha (by decide)
    have h3 := h .prepareThird (by decide)
    show szAt S _ w = szAt S _ w
    simp only [linWeights, linResidual, linevalPoly, linWitness, linSum, withChallenges, h2, h3]
    rfl
  | deltas =>
    have h2 := h .alpha (by decide)
    have h4 := h .beta (by decide)
    show (deltaDraw _ _ _).bad S w = (deltaDraw _ _ _).bad S w
    simp only [matrixTerms, withChallenges, h2, h4]
  | gamma =>
    have h2 := h .alpha (by decide)
    have h4 := h .beta (by decide)
    have h5 := h .deltas (by decide)
    show szAt S _ w = szAt S _ w
    simp only [deltaWeights, matrixTerms, withChallenges, h2, h4, h5]

end V3Batch

/-! ## The batch bad set of a history -/

/-- The batch bad set of a history : at the squeeze after its last message, for the
batch `ext` reads off the statement and the history's messages, with the history's
squeezes as challenges; kept if it has at most `b` elements. -/
noncomputable def batchBad (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F)
    (b : ℕ) (s : V3Stmt F) (hist : List (Round F)) : Finset F :=
  match squeezeAfter hist.length with
  | some c =>
    if ((ext s (hist.map Prod.fst)).badAt S (histChal hist) c (histChal hist c)).card ≤ b then
      (ext s (hist.map Prod.fst)).badAt S (histChal hist) c (histChal hist c)
    else ∅
  | none => ∅

/-- `ext` reads off the statement and the messages before each squeeze what they fix
of `B`. -/
def ExtractsBefore (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (s : V3Stmt F)
    (t : V2Transcript F) (B : V3Batch F) : Prop :=
  ∀ c : V2Challenge, B.absorbed c.prefixAbsorbs =
    (ext s (t.messages.take c.prefixAbsorbs)).absorbed c.prefixAbsorbs

/-- At an element's history, the batch bad set is `B`'s bad set at that element, if
that has at most `b` elements. -/
theorem batchBad_history {ext : V3Stmt F → List (FSMessage F) → V3Batch F} {s : V3Stmt F}
    {t : V2Transcript F} {B : V3Batch F} (hB : ExtractsBefore ext s t B) (S : Finset F) (b : ℕ)
    (chal : V2Challenge → List F) (c : V2Challenge) (j : ℕ)
    (hcard : (B.badAt S chal c ((chal c).take j)).card ≤ b) :
    batchBad ext S b s (t.history chal c j) = B.badAt S chal c ((chal c).take j) := by
  have key : (ext s (t.messages.take c.prefixAbsorbs)).badAt S (histChal (t.history chal c j)) c
      ((chal c).take j) = B.badAt S chal c ((chal c).take j) := by
    rw [← V3Batch.badAt_absorbed, ← hB, V3Batch.badAt_absorbed]
    exact V3Batch.badAt_congr _ _ (fun c' hc' => t.histChal_history_lt chal hc' j) _
  rw [batchBad, t.length_history, squeezeAfter_prefixAbsorbs]
  simp only
  rw [t.map_fst_history, t.histChal_history_self, key, if_pos hcard]

theorem card_batchBad_le (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F)
    (b : ℕ) (s : V3Stmt F) (hist : List (Round F)) :
    (S.filter (· ∈ batchBad ext S b s hist)).card ≤ b := by
  unfold batchBad
  split
  · split_ifs with h
    · exact (card_filter_mem_le _ _).trans h
    · simp
  · simp

/-- A break of the output against `B`'s bad sets is a break of its rounds against
the history bad sets, when `B`'s residuals have degree at most `b ≥ 1`. -/
theorem roundsBreak_of_outputBreaks {ext : V3Stmt F → List (FSMessage F) → V3Batch F}
    {s : V3Stmt F} {t : V2Transcript F} {B : V3Batch F} (hB : ExtractsBefore ext s t B)
    (hmsg : ∀ x, FSMessage.field x ∉ t.messages) (S : Finset F) {b : ℕ} (hb : 1 ≤ b)
    {chal : V2Challenge → List F} (hres : (B.withChallenges chal).ResidualsBounded chal b)
    (h : outputBreaks (prefixBad t (B.badAt S chal)) t chal = true) :
    RoundsBreak (batchBad ext S b s) (t.rounds chal) := by
  obtain ⟨c, -, hc⟩ := List.any_eq_true.mp h
  obtain ⟨j, hj, hbad⟩ := (hitsB_iff _ _ _).mp hc
  rw [List.nil_append, prefixBad_elemBefore hmsg] at hbad
  refine ⟨_, _, _, _, t.rounds_split chal c, j, hj, ?_⟩
  show (chal c)[j] ∈ batchBad ext S b s (t.history chal c j)
  rw [batchBad_history hB S b chal c j (V3Batch.card_badAt_le hb hres S c _)]
  exact hbad

/-! ## Adaptive soundness -/

namespace V3Batch

/-- The V3 verifier's checks of `P` on transcript `t` with squeezes `chal`, as
`sound_of_transcript` takes them. -/
structure Accepts (P : V3Batch F) (S : Finset F) (t : V2Transcript F)
    (chal : V2Challenge → List F) (comms : List (List F)) : Prop where
  init : t.init = v3Init P.statement comms
  msg : ∀ x, FSMessage.field x ∉ t.messages
  inS : ∀ c, ∀ a ∈ chal c, a ∈ S
  alpha : chal .alpha = [P.α]
  beta : chal .beta = [P.β]
  gamma : chal .gamma = [P.γ]
  nu : (chal .firstCombiners).length = combinerDraws P.sizes
  eta : (chal .prepareThird).length = combinerDraws P.sizes + 3
  etaA : P.ηA = (chal .prepareThird).getD (combinerDraws P.sizes) 0
  etaB : P.ηB = (chal .prepareThird).getD (combinerDraws P.sizes + 1) 0
  etaC : P.ηC = (chal .prepareThird).getD (combinerDraws P.sizes + 2) 0
  delta : (chal .deltas).length = 3 * P.circuits.length - 1
  dvdR : ∀ c ∈ P.circuits, c.R.n ∣ P.R.n
  dvdC : ∀ c ∈ P.circuits, c.Cd.n ∣ P.Cd.n
  dvdK : ∀ t ∈ P.matrixTerms, t.K.n ∣ P.K.n
  valid : ∀ t ∈ P.matrixTerms, t.Valid
  gen : ∀ c ∈ P.circuits, c.Xd.ω = c.Cd.ω ^ (c.Cd.n / c.Xd.n)
  h0 : inspectOpening P.h0rep [] P.α P.vH0 = none
  openings : P.Openings
  row : P.rowEval (P.rowWeights chal) = 0
  lin : P.linOpenedEval (P.linWeights chal) = 0
  degL : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n
  mat : P.matOpenedEval (P.deltaWeights chal) = 0

/-- The relation `sound_of_transcript` concludes : the transcript binds exactly `P`'s
statement, the mask sum is zero, and every instance has `ẑ` equal to its public
input on the input domain and satisfies `Az ∘ Bz = Cz` on its constraint domain. -/
def Holds (P : V3Batch F) (t : V2Transcript F) : Prop :=
  (∀ inputs comms', t.init = v3Init inputs comms' → inputs = P.statement) ∧ P.e = 0 ∧
    ∀ p ∈ P.instances,
      (∀ k < p.1.Xd.n, (p.1.zhat p.2).eval
        (p.1.Cd.node (reindexBySubdomain p.1.Cd.n p.1.Xd.n k)) = p.2.x.getD k 0) ∧
      ∀ r, r < p.1.R.n →
        mzRow p.1.Cd p.1.A (p.1.zhat p.2) r * mzRow p.1.Cd p.1.B (p.1.zhat p.2) r =
          mzRow p.1.Cd p.1.Cm (p.1.zhat p.2) r

theorem holds_of_accepts {P : V3Batch F} {S : Finset F} {t : V2Transcript F}
    {chal : V2Challenge → List F} {comms : List (List F)} (h : P.Accepts S t chal comms)
    (hnb : outputBreaks (prefixBad t (P.squeezeBad S chal)) t chal = false) : P.Holds t :=
  P.sound_of_transcript S t chal comms h.init h.msg h.inS h.alpha h.beta h.gamma h.nu h.eta
    h.etaA h.etaB h.etaC h.delta hnb h.dvdR h.dvdC h.dvdK h.valid h.gen h.h0 h.openings h.row
    h.lin h.degL h.mat

/-- The output fools the verifier : it accepts the batch `B` with its challenges read
off `chal`, and the relation fails. -/
def Fools (S : Finset F) (s : V3Stmt F) (B : V3Batch F) (t : V2Transcript F)
    (chal : V2Challenge → List F) : Prop :=
  (B.withChallenges chal).Accepts S t chal s.2 ∧ ¬(B.withChallenges chal).Holds t

/-- Fiat–Shamir soundness of the V3 batch against an adaptive prover, counting form.

On each tape the prover outputs a statement, a transcript, and a batch `B` : the
polynomials and sums behind its messages and the values it opens, every message
picked after the challenges before it. `ext` reads off the statement and the
messages before each squeeze what they fix of `B` (`ExtractsBefore`); `b ≥ 1` bounds
the degrees of `B`'s three batched residuals. If every squeezed element was
answered on one of the adversary's `Q` queries, at most `Q · b · | S | ^{Q-1}` of the
` | S | ^Q` tapes yield an output the verifier accepts while the relation fails :
knowledge error `Q · b / | S | `. -/
theorem adaptive_soundness (ext : V3Stmt F → List (FSMessage F) → V3Batch F) (S : Finset F)
    {b : ℕ} (hb : 1 ≤ b) (A : FSAdversary F) (Q : ℕ) (stmt : List F → V3Stmt F)
    (B : List F → V3Batch F) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → List F)
    (hstmt : ∀ tape ∈ tapes S Q,
      (out tape).init = v3Init (stmt tape).1 (stmt tape).2 ∧ V3StmtWF (stmt tape))
    (hB : ∀ tape ∈ tapes S Q, ExtractsBefore ext (stmt tape) (out tape) (B tape))
    (hcons : ∀ tape ∈ tapes S Q,
      RoundsFromQueries A tape (out tape).init ((out tape).rounds (chal tape)))
    (hdeg : ∀ tape ∈ tapes S Q,
      ((B tape).withChallenges (chal tape)).ResidualsBounded (chal tape) b)
    [DecidablePred fun tape => Fools S (stmt tape) (B tape) (out tape) (chal tape)] :
    ((tapes S Q).filter fun tape => Fools S (stmt tape) (B tape) (out tape) (chal tape)).card ≤
      Q * b * S.card ^ (Q - 1) := by
  refine fs_rounds_charge (fun s => v3Init s.1 s.2) V3StmtWF
    (fun _ _ _ _ hs hs' hr hr' h => v3Init_rounds_inj hs hs' hr hr' h) S A (batchBad ext S b) b
    (card_batchBad_le ext S b) Q stmt (fun tape => (out tape).rounds (chal tape))
    (fun tape h => (hstmt tape h).1 ▸ hcons tape h) _ fun tape h hf => ?_
  obtain ⟨hacc, hnot⟩ := hf
  refine ⟨(hstmt tape h).2, V2Transcript.noLoneField_rounds hacc.msg _,
    roundsBreak_of_outputBreaks (hB tape h) hacc.msg S hb (hdeg tape h) ?_⟩
  by_contra hne
  exact hnot (holds_of_accepts hacc (Bool.eq_false_iff.mpr hne))

/-- `adaptive_soundness` with `b` computed. Every polynomial the prover commits to
has degree below `d.D`, the SRS's number of powers, and every domain is at most
`d`'s sizes (`Within`); then `b = max(d_R, d_L, d_M, 1)` with
`d_R = max(2R − 2, D + R − 1)`, `d_L = D + C + X − 2`, `d_M = D + K − 1`. -/
theorem adaptive_soundness_concrete (ext : V3Stmt F → List (FSMessage F) → V3Batch F)
    (S : Finset F) (d : DegreeBounds) (hX : 1 ≤ d.X) (A : FSAdversary F) (Q : ℕ)
    (stmt : List F → V3Stmt F) (B : List F → V3Batch F) (out : List F → V2Transcript F)
    (chal : List F → V2Challenge → List F)
    (hstmt : ∀ tape ∈ tapes S Q,
      (out tape).init = v3Init (stmt tape).1 (stmt tape).2 ∧ V3StmtWF (stmt tape))
    (hB : ∀ tape ∈ tapes S Q, ExtractsBefore ext (stmt tape) (out tape) (B tape))
    (hcons : ∀ tape ∈ tapes S Q,
      RoundsFromQueries A tape (out tape).init ((out tape).rounds (chal tape)))
    (hW : ∀ tape ∈ tapes S Q, (B tape).Within d)
    [DecidablePred fun tape => Fools S (stmt tape) (B tape) (out tape) (chal tape)] :
    ((tapes S Q).filter fun tape => Fools S (stmt tape) (B tape) (out tape) (chal tape)).card ≤
      Q * d.b * S.card ^ (Q - 1) :=
  adaptive_soundness ext S d.one_le_b A Q stmt B out chal hstmt hB hcons fun tape h =>
    ((hW tape h).withChallenges (chal tape)).residualsBounded hX (chal tape)

end V3Batch

end Varuna