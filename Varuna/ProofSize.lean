/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Match

/-!
# Proof size

Element counts of snarkVM's `Proof` (`snark/varuna/data_structures/proof.rs`)
for `i` circuits and `J` instances in total :

* `Commitments` : `w` per instance, `mask_poly` in ZK mode, `h_0`, `g_1`,
  `h_1`, `g_a, g_b, g_c` per circuit, `h_2`;
* `pc_proof` : one KZG proof per query point (`α, β, γ`), each a `G1`
  witness plus `random_v` in ZK mode;
* `Evaluations` : `g_1(β)` and `g_a, g_b, g_c` per circuit;
* `third_msg` : `sum_a, sum_b, sum_c` per instance; `fourth_msg` : per circuit.

The spec (`varuna-spec-prod.tex`, Efficiency) states `9 G1 + 10 F` for one
proof and `(5 + j + 3i) G1 + (1 + 9i) F` for a batch. Its `G1` count is the
commitments alone, and its `F` count agrees with snarkVM only when there
is one instance per circuit (`spec_batch_scalars_iff`).
-/

namespace Varuna

/-- Batch shape: circuits, total instances, and whether the proof is hiding (ZK). -/
structure ProofShape where
  /-- Number of circuits `i`. -/
  circuits : Nat
  /-- Total number of instances `J`. -/
  instances : Nat
  /-- Hiding (ZK) mode. -/
  zk : Bool

/-- `G1` commitments in `Commitments`. -/
def ProofShape.commitments (s : ProofShape) : Nat :=
  s.instances + (if s.zk then 1 else 0) + 3 + 3 * s.circuits + 1

/-- `G1` witnesses in `pc_proof`: one per query point. -/
def ProofShape.kzgWitnesses (_ : ProofShape) : Nat :=
  queryChallengeNames.length

/-- Scalars in `Evaluations`, `third_msg`, and `fourth_msg`. -/
def ProofShape.scalars (s : ProofShape) : Nat :=
  (1 + 3 * s.circuits) + 3 * s.instances + 3 * s.circuits

/-- `random_v` scalars in `pc_proof` (ZK only). -/
def ProofShape.randomV (s : ProofShape) : Nat :=
  if s.zk then queryChallengeNames.length else 0

/-- Total `G1` elements. -/
def ProofShape.g1 (s : ProofShape) : Nat :=
  s.commitments + s.kzgWitnesses

/-- Total field elements. -/
def ProofShape.fr (s : ProofShape) : Nat :=
  s.scalars + s.randomV

/-- `G1` count: `J + 3i + 8` in ZK mode, `J + 3i + 7` otherwise. -/
theorem ProofShape.g1_eq (s : ProofShape) :
    s.g1 = s.instances + 3 * s.circuits + if s.zk then 8 else 7 := by
  cases h : s.zk <;> simp [g1, commitments, kzgWitnesses, queryChallengeNames, h] <;> omega

/-- Field count: `1 + 6i + 3J`, plus `3` in ZK mode. -/
theorem ProofShape.fr_eq (s : ProofShape) :
    s.fr = 1 + 6 * s.circuits + 3 * s.instances + if s.zk then 3 else 0 := by
  cases h : s.zk <;> simp [fr, scalars, randomV, queryChallengeNames, h] <;> omega

/-- The spec's single-proof `9 G1 + 10 F` is the ZK commitments and the scalars
without `random_v`; the full proof has `12 G1 + 13 F`. -/
theorem spec_single_proof :
    let s : ProofShape := ⟨1, 1, true⟩
    s.commitments = 9 ∧ s.scalars = 10 ∧ s.g1 = 12 ∧ s.fr = 13 := by
  decide

/-- The spec's batch `G1` count `5 + j + 3i` is the ZK commitment count. -/
theorem spec_batch_commitments (i J : Nat) :
    (⟨i, J, true⟩ : ProofShape).commitments = 5 + J + 3 * i := by
  simp [ProofShape.commitments]
  omega

/-- The spec's batch `F` count `1 + 9i` matches snarkVM's scalars only when `J = i`. -/
theorem spec_batch_scalars_iff (i J : Nat) :
    (⟨i, J, true⟩ : ProofShape).scalars = 1 + 9 * i ↔ J = i := by
  simp [ProofShape.scalars]
  omega

end Varuna