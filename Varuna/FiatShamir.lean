/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.AHP

/-!
# Fiat–Shamir schedule (VarunaVersion.V2)

The deployed sponge is Poseidon; identifying it with a programmable random
oracle is a floor. This module records the *schedule* snarkVM actually
runs, as an absorb/squeeze transcript, and proves :

* each challenge is a function of the prefix *before* that squeeze
* V2 inserts the 2025 extra round (`prepare_third`) that V1 does not
* a fork of two transcripts that share a prefix and differ at a squeeze
  is computed data (`inspectFork`)

Forks and collisions are computed data. Query charging of those breaks is
`Varuna.FSBound`. `Varuna.BatchFS` derives every V3 squeeze's bad set from
its query, the history before it.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace Varuna

variable {F : Type*} [Field F]

/-- snarkVM `VarunaVersion`. The formalization targets `V3`. -/
inductive VarunaVersion where
  /-- Original schedule: `η_b, η_c` squeezed with `α`. -/
  | V1
  /-- Extra `prepare_third` round; `η_b, η_c` delayed; `η_A` fixed to `1`. -/
  | V2
  /-- V2 schedule, with `η_A` squeezed after the mask commitment and the sums. -/
  | V3
  deriving DecidableEq, Repr

/-- Messages absorbed into the sponge (typed, post-decoding). -/
inductive FSMessage (F : Type*) where
  /-- Domain-separator / protocol-name bytes. -/
  | tag (s : String)
  /-- A single field element (challenge or claimed sum). -/
  | field (x : F)
  /-- A vector of field elements (public inputs, combiners, …). -/
  | fields (xs : List F)
  /-- A size absorbed as bytes (snarkVM batch sizes, `u64` little-endian). -/
  | size (n : Nat)
  deriving DecidableEq, Repr

/-- Transcript: messages in absorb order. -/
abbrev Transcript (F : Type*) := List (FSMessage F)

/-- Programmable random oracle: next field element from a prefix.
Identifying Poseidon with this map is a floor. -/
abbrev RO (F : Type*) := Transcript F → F

/-- Squeeze `n` field elements by feeding the growing prefix. -/
def squeezeN (ro : RO F) (pre : Transcript F) : Nat → List F
  | 0 => []
  | n + 1 =>
    let x := ro pre
    x :: squeezeN ro (pre ++ [FSMessage.field x]) n

/-- Squeezing zero elements yields the empty list. -/
@[simp] theorem squeezeN_zero (ro : RO F) (pre : Transcript F) :
    squeezeN ro pre 0 = [] :=
  rfl

/-- The first squeezed element is `ro pre`. -/
theorem squeezeN_succ_head (ro : RO F) (pre : Transcript F) (n : Nat) :
    (squeezeN ro pre (n + 1)).head? = some (ro pre) :=
  rfl

/-- V2 verifier squeezes, in order. -/
inductive V2Challenge where
  /-- First-round batch combiners (after first-oracle commitments). -/
  | firstCombiners
  /-- `α` only (V2 does not squeeze `η_b, η_c` here). -/
  | alpha
  /-- Extra round: third-round combiners plus `η_b, η_c`. -/
  | prepareThird
  /-- `β` (variable-domain lineval). -/
  | beta
  /-- `δ_A, δ_B, δ_C` matrix-sumcheck combiners. -/
  | deltas
  /-- `γ` (nonzero-domain matrix sumcheck). -/
  | gamma
  deriving DecidableEq, Repr

/-- Absorb steps that precede each V2 squeeze. Index in this list is the
number of prover messages already in the transcript. -/
def V2Challenge.prefixAbsorbs : V2Challenge → Nat
  | .firstCombiners => 1
  | .alpha => 2
  | .prepareThird => 3
  | .beta => 4
  | .deltas => 5
  | .gamma => 6

/-- V2 has an extra absorb/squeeze pair that V1 skips. -/
def V2Challenge.isExtraRound : V2Challenge → Bool
  | .prepareThird => true
  | _ => false

/-- The extra round is present on the V2 schedule. -/
@[simp] theorem prepareThird_isExtraRound :
    V2Challenge.prepareThird.isExtraRound = true :=
  rfl

/-- Later squeezes see a strictly longer absorb prefix. -/
theorem alpha_before_prepareThird :
    V2Challenge.alpha.prefixAbsorbs < V2Challenge.prepareThird.prefixAbsorbs :=
  Nat.lt_succ_self _

/-- `α` is squeezed before `β`. -/
theorem alpha_before_beta :
    V2Challenge.alpha.prefixAbsorbs < V2Challenge.beta.prefixAbsorbs := by
  decide

/-- `β` is squeezed before `γ`. -/
theorem beta_before_gamma :
    V2Challenge.beta.prefixAbsorbs < V2Challenge.gamma.prefixAbsorbs := by
  decide

/-- A well-formed V2 transcript is an absorb-then-squeeze spine. We store
the prover messages (one list entry per absorb step) and derive challenges
from `ro`. -/
structure V2Transcript (F : Type*) where
  /-- Init bytes and public inputs (before any prover oracle). -/
  init : List (FSMessage F)
  /-- First-round commitments. -/
  first : FSMessage F
  /-- Second-round commitments (`h₀`). -/
  second : FSMessage F
  /-- Prepare-third sums (V2 extra round). -/
  prepareThird : FSMessage F
  /-- Third-round commitments (`g₁, h₁`). -/
  third : FSMessage F
  /-- Fourth-round commitments and matrix sums. -/
  fourth : FSMessage F
  /-- Fifth-round commitments (`h₂`). -/
  fifth : FSMessage F

/-- Prefix of a V2 transcript immediately before the named squeeze. -/
def V2Transcript.before (t : V2Transcript F) : V2Challenge → Transcript F
  | .firstCombiners => t.init ++ [t.first]
  | .alpha => t.init ++ [t.first, t.second]
  | .prepareThird => t.init ++ [t.first, t.second, t.prepareThird]
  | .beta => t.init ++ [t.first, t.second, t.prepareThird, t.third]
  | .deltas => t.init ++ [t.first, t.second, t.prepareThird, t.third, t.fourth]
  | .gamma => t.init ++ [t.first, t.second, t.prepareThird, t.third, t.fourth, t.fifth]

/-- Challenge squeezed at a V2 step. -/
def V2Transcript.challenge (ro : RO F) (t : V2Transcript F) (c : V2Challenge) : F :=
  ro (t.before c)

/-- The challenge depends only on the prefix at that step. -/
theorem challenge_eq_ro (ro : RO F) (t : V2Transcript F) (c : V2Challenge) :
    t.challenge ro c = ro (t.before c) :=
  rfl

/-- The `α` prefix is a prefix of the prepare-third prefix (extra round comes later). -/
theorem alpha_prefix_isPrefix (t : V2Transcript F) :
    List.IsPrefix (t.before .alpha) (t.before .prepareThird) := by
  simpa [V2Transcript.before, List.append_assoc] using
    (List.prefix_append (t.init ++ [t.first, t.second]) [t.prepareThird])

/-- The `α` prefix is a prefix of the `β` prefix. -/
theorem alpha_prefix_isPrefix_beta (t : V2Transcript F) :
    List.IsPrefix (t.before .alpha) (t.before .beta) := by
  simpa [V2Transcript.before, List.append_assoc] using
    (List.prefix_append (t.init ++ [t.first, t.second]) [t.prepareThird, t.third])

/-- Two transcripts that agree on the prefix of `c` yield the same challenge. -/
theorem challenge_of_same_prefix (ro : RO F) (t₁ t₂ : V2Transcript F)
    (c : V2Challenge) (h : t₁.before c = t₂.before c) :
    t₁.challenge ro c = t₂.challenge ro c := by
  simp [V2Transcript.challenge, h]

/-- Fork data: two oracles that disagree at one prefix (rewind / programming). -/
structure FSFork (F : Type*) where
  /-- Shared transcript prefix at the forked squeeze. -/
  pre : Transcript F
  /-- First oracle output. -/
  ch₁ : F
  /-- Second oracle output. -/
  ch₂ : F

/-- Inspect two oracles at a prefix: `some` iff they output distinct challenges. -/
def inspectFork [DecidableEq F] (ro₁ ro₂ : RO F) (pre : Transcript F) :
    Option (FSFork F) :=
  if ro₁ pre ≠ ro₂ pre then some ⟨pre, ro₁ pre, ro₂ pre⟩ else none

/-- Distinct oracle outputs at the same prefix are a fork. -/
theorem inspectFork_some [DecidableEq F] {ro₁ ro₂ : RO F} {pre : Transcript F}
    (hd : ro₁ pre ≠ ro₂ pre) :
    inspectFork ro₁ ro₂ pre = some ⟨pre, ro₁ pre, ro₂ pre⟩ := by
  simp [inspectFork, hd]

/-- Identical oracle outputs are not a fork. -/
theorem inspectFork_none_of_eq [DecidableEq F] {ro₁ ro₂ : RO F} {pre : Transcript F}
    (h : ro₁ pre = ro₂ pre) : inspectFork ro₁ ro₂ pre = none := by
  simp [inspectFork, h]

/-- A returned fork really has distinct challenges. -/
theorem inspectFork_distinct [DecidableEq F] {ro₁ ro₂ : RO F} {pre : Transcript F}
    {fk : FSFork F} (h : inspectFork ro₁ ro₂ pre = some fk) : fk.ch₁ ≠ fk.ch₂ := by
  simp [inspectFork] at h
  rcases h with ⟨hd, rfl⟩
  exact hd

/-- RO collision data: two distinct prefixes that squeeze to the same value. -/
structure ROCollision (F : Type*) where
  /-- First prefix. -/
  t₁ : Transcript F
  /-- Second prefix. -/
  t₂ : Transcript F

/-- Inspect two prefixes for a collision of `ro`. -/
def inspectCollision [DecidableEq F] (ro : RO F) (t₁ t₂ : Transcript F) :
    Option (ROCollision F) :=
  if t₁ ≠ t₂ ∧ ro t₁ = ro t₂ then some ⟨t₁, t₂⟩ else none

/-- Distinct prefixes with equal RO output are a collision. -/
theorem inspectCollision_some [DecidableEq F] {ro : RO F} {t₁ t₂ : Transcript F}
    (hne : t₁ ≠ t₂) (heq : ro t₁ = ro t₂) :
    inspectCollision ro t₁ t₂ = some ⟨t₁, t₂⟩ := by
  simp [inspectCollision, hne, heq]

/-- A returned collision has distinct prefixes. -/
theorem inspectCollision_ne [DecidableEq F] {ro : RO F} {t₁ t₂ : Transcript F}
    {c : ROCollision F} (h : inspectCollision ro t₁ t₂ = some c) :
    c.t₁ ≠ c.t₂ := by
  simp [inspectCollision] at h
  rcases h with ⟨⟨hne, _⟩, rfl⟩
  exact hne

/-- Number of squeezes equals the requested count. -/
theorem squeezeN_length (ro : RO F) (pre : Transcript F) (n : Nat) :
    (squeezeN ro pre n).length = n := by
  induction n generalizing pre with
  | zero => rfl
  | succ n ih => simp [squeezeN, ih]

/-- Prefix length is init plus the number of absorbed prover messages. -/
theorem before_length (t : V2Transcript F) (c : V2Challenge) :
    (t.before c).length = t.init.length + c.prefixAbsorbs := by
  cases c <;> simp [V2Transcript.before, V2Challenge.prefixAbsorbs]

/-- V2 second-round squeeze count is 1 (`α` only). -/
def v2SecondRoundSqueezeCount : Nat := 1

/-- V1 second-round squeeze count is 3 (`α, η_b, η_c`). -/
def v1SecondRoundSqueezeCount : Nat := 3

/-- V2 squeezes a single challenge in the second verifier round. -/
@[simp] theorem v2SecondRoundSqueezeCount_eq : v2SecondRoundSqueezeCount = 1 :=
  rfl

/-- V1 squeezes three challenges in the second verifier round. -/
@[simp] theorem v1SecondRoundSqueezeCount_eq : v1SecondRoundSqueezeCount = 3 :=
  rfl

/-- Squeeze count of the second verifier round, by version. -/
def secondRoundSqueezeCount : VarunaVersion → Nat
  | .V1 => v1SecondRoundSqueezeCount
  | .V2 => v2SecondRoundSqueezeCount
  | .V3 => v2SecondRoundSqueezeCount

/-- V2 second-round squeeze count is strictly smaller than V1. -/
theorem v2_secondRound_lt_v1 :
    secondRoundSqueezeCount .V2 < secondRoundSqueezeCount .V1 := by
  decide

/-- Whether the version includes the extra prepare-third round. -/
def hasPrepareThird : VarunaVersion → Bool
  | .V1 => false
  | .V2 => true
  | .V3 => true

/-- V2 has the extra round. -/
@[simp] theorem hasPrepareThird_V2 : hasPrepareThird .V2 = true :=
  rfl

/-- V3 has the extra round. -/
@[simp] theorem hasPrepareThird_V3 : hasPrepareThird .V3 = true :=
  rfl

/-- V1 does not have the extra round. -/
@[simp] theorem hasPrepareThird_V1 : hasPrepareThird .V1 = false :=
  rfl

end Varuna