/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.BatchFS

/-!
# The batched pairing check

snarkVM's verifier does not open `h₀`, the mask, `h₁`, `ŵ`, or `h₂` one by one. Its query
set (`ahp/verifier/messages.rs:100-140`) is the rowcheck LC at `α`, `g₁` and the lineval
LC at `β`, and every circuit's `g_A, g_B, g_C` and the matrix LC at `γ`, each LC opened
to `0` (`ahp.rs:179-404`). `batch_check` (`sonic_pc/mod.rs:347-420`) combines the
openings at each point with one challenge per polynomial (`accumulate_elems`), and the
points with randomizers `1, r₁, r₂`. One pairing product checks the lot (`pcCheck`).

`pcCheck` is that product as `check_elems` assembles it : each commitment against the
G2 shift of its degree bound, and each proof's `random_v` along `gamma_g`. Against
representations over the powers of `g` and `gamma_g`, a well-formed key makes it
`(Σ_j r_j c_j) · e(g, h)` (`pcProduct_toGroup`). Unless the randomizers are lucky every
`c_j` is zero. Then, unless the trapdoor is `0` or a nonzero pair of polynomials has root
`(τ, κ)` (`RepBreak.srsBreak`), the KZG defect
`D_j = Σ_i ξ_{j,i} p_{j,i} − Σ_i ξ_{j,i} v_{j,i} − (X − z_j) q_j` of the polynomials above
the shifts is zero (`RepPoint.defect_eq_zero_of_cleared`). `D_j = 0` gives
`Σ_i ξ_{j,i} (p_{j,i}(z_j) − v_{j,i}) = 0`, so unless the `ξ_j` are lucky every claim is
correct (`pcCheck_extract`). `batchCheck_extract` is the same argument on the reading
`Σ_j r_j D_j(τ) = 0`, where a nonzero `D_j` with root `τ` is a trapdoor break
(`PCBreak.trapdoorBreak`).

`V3Batch.holds_of_deployedAccepts` : the V3 checks with the batch check in place of
correct openings (`DeployedAccepts`), no break of the transcript, no lucky combination,
and no trapdoor break give the relation.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## One pairing product over the query points -/

/-- One query point of `batch_check`, read against the algebraic representations : the
point, each opened polynomial with its claimed value, and the polynomial behind the
point's KZG proof. -/
structure PointOpening (F : Type*) [Field F] where
  z : F
  opened : List (F[X] × F)
  proof : F[X]

namespace PointOpening

variable (o : PointOpening F)

/-- The KZG defect of the point with combination challenges `ξ` :
`Σ ξ_i p_i − Σ ξ_i v_i − (X − z) q`. -/
noncomputable def defect (ξ : List F) : F[X] :=
  weightedSumPoly ξ (o.opened.map Prod.fst) - C (weightedSum ξ (o.opened.map Prod.snd)) -
    (X - C o.z) * o.proof

/-- Each opened polynomial's value at the point less its claimed value. -/
noncomputable def discrepancies : List F :=
  o.opened.map fun pv => pv.1.eval o.z - pv.2

theorem eval_defect_z (ξ : List F) : (o.defect ξ).eval o.z = weightedSum ξ o.discrepancies := by
  rw [discrepancies, weightedSum_map_sub (fun pv : F[X] × F => pv.1.eval o.z) Prod.snd, defect]
  simp [eval_weightedSumPoly, List.map_map, Function.comp_def]

/-- A zero defect whose challenges cancel no wrong claim makes every claim correct. -/
theorem claims_of_defect_eq_zero {ξ : List F} (hd : o.defect ξ = 0)
    (hξ : inspectBatch ξ o.discrepancies = none) : ∀ pv ∈ o.opened, pv.2 = pv.1.eval o.z := by
  intro pv hpv
  have hsum : weightedSum ξ o.discrepancies = 0 := by
    rw [← eval_defect_z, hd, eval_zero]
  have h0 := inspectBatch_accepts hsum hξ _
    (List.mem_map_of_mem (f := fun pv : F[X] × F => pv.1.eval o.z - pv.2) hpv)
  exact (sub_eq_zero.mp h0).symm

end PointOpening

/-- The defects at `τ`, point by point. -/
noncomputable def defectsAt (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) : List F :=
  List.zipWith (fun o ξ => (o.defect ξ).eval τ) os ξs

/-- The batch check passes by luck : the randomizers `rs` cancel nonzero defects at `τ`, or
some point's challenges cancel a wrong claim. -/
def PCLucky (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) (rs : List F) : Prop :=
  inspectBatch rs (defectsAt τ os ξs) ≠ none ∨
    ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
      inspectBatch ξs[j] os[j].discrepancies ≠ none

/-- Some point's defect is a nonzero polynomial with root `τ`. -/
def PCBreak (τ : F) (os : List (PointOpening F)) (ξs : List (List F)) : Prop :=
  ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
    os[j].defect ξs[j] ≠ 0 ∧ (os[j].defect ξs[j]).eval τ = 0

/-- A defect with root `τ` is a trapdoor break. -/
theorem PCBreak.trapdoorBreak {τ : F} {os : List (PointOpening F)} {ξs : List (List F)}
    (h : PCBreak τ os ξs) : ∃ br : TrapdoorBreak F, br.holds τ := by
  obtain ⟨j, hj, hj', hne, hev⟩ := h
  refine ⟨⟨coeffList (os[j].defect ξs[j])⟩, ?_, ?_⟩
  · rw [toPoly_coeffList]
    exact hne
  · rw [toPoly_coeffList]
    exact hev

/-- Batch-check extraction. If the randomized defects at `τ` sum to zero, nothing is lucky,
and no defect is a nonzero polynomial with root `τ`, every claimed value is its
polynomial's value at the point. -/
theorem batchCheck_extract {τ : F} {os : List (PointOpening F)} {ξs : List (List F)}
    {rs : List F} (hlen : os.length ≤ ξs.length) (hcheck : weightedSum rs (defectsAt τ os ξs) = 0)
    (hl : ¬PCLucky τ os ξs rs) (hbr : ¬PCBreak τ os ξs) :
    ∀ o ∈ os, ∀ pv ∈ o.opened, pv.2 = pv.1.eval o.z := by
  intro o ho pv hpv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
  have hj' : j < ξs.length := by omega
  have hr : inspectBatch rs (defectsAt τ os ξs) = none := by
    by_contra h
    exact hl (Or.inl h)
  have hτ : (os[j].defect ξs[j]).eval τ = 0 := by
    refine inspectBatch_accepts hcheck hr _ ?_
    have hlt : j < (defectsAt τ os ξs).length := by
      simp only [defectsAt, List.length_zipWith]
      omega
    have hmem := List.getElem_mem hlt
    have heq : (defectsAt τ os ξs)[j] = (os[j].defect ξs[j]).eval τ := by
      simp [defectsAt]
    rw [heq] at hmem
    exact hmem
  have hzero : os[j].defect ξs[j] = 0 := by
    by_contra hne
    exact hbr ⟨j, hj, hj', hne, hτ⟩
  have hξ : inspectBatch ξs[j] os[j].discrepancies = none := by
    by_contra h
    exact hl (Or.inr ⟨j, hj, hj', h⟩)
  exact os[j].claims_of_defect_eq_zero hzero hξ pv hpv

/-! ## The pairing product

`check_elems` pairs the combined commitments of each degree bound against that bound's
shift in G2, and the adjusted witness and the witness against `h` and `beta_h`. Against
representations over the powers of `g` and `gamma_g = κ g`, a well-formed key makes the
product `(Σ_j r_j c_j) · e(g, h)`, with `c_j` the scalar of point `j`
(`pcProduct_toGroup`). Cleared of the shifts' inverses, `τ^M c_j` is the value at
`(τ, κ)` of a pair of polynomials (`RepPoint.eval_cleared`). Along `g` that pair is
`X^M` times the KZG defect of the polynomials above the shifts, plus a part of degree
below `M` (`RepPoint.cleared_fst`), so it is zero only if the defect is
(`RepPoint.defect_eq_zero_of_cleared`). -/

section Pairing

variable {G1 G2 GT : Type*} [AddCommGroup G1] [AddCommGroup G2] [AddCommGroup GT]
  [Module F G1] [Module F G2] [Module F GT]

/-- The verifier key `batch_check` reads : `g` and `gamma_g` in G1, `h` and `beta_h` in
G2, the SRS's largest power `M`, and for each degree bound `d` its shift in G2
(`prepared_negative_powers_of_beta_h`, `parameters/src/mainnet/powers.rs:80-86`). -/
structure BatchKey (G1 G2 : Type*) where
  g : G1
  gammaG : G1
  h : G2
  betaH : G2
  negPowH : ℕ → G2
  maxDegree : ℕ

/-- A key from an SRS with trapdoor `τ` and `gamma_g = κ g` : the shift for degree bound
`d` is `τ^{−(M−d)} h`. -/
def BatchKey.wellFormed (key : BatchKey G1 G2) (τ κ : F) : Prop :=
  key.betaH = τ • key.h ∧ key.gammaG = κ • key.g ∧
    ∀ d, key.negPowH d = (τ ^ (key.maxDegree - d))⁻¹ • key.h

/-- The shift of a commitment with degree bound `b` under an SRS whose largest power is
`M` : `M − d` for bound `d`, `0` without one (`sonic_pc/mod.rs:105`). -/
def boundShift (M : ℕ) : Option ℕ → ℕ
  | none => 0
  | some d => M - d

theorem boundShift_le (M : ℕ) : ∀ b, boundShift M b ≤ M
  | none => Nat.zero_le _
  | some _ => Nat.sub_le _ _

/-- The G2 element a commitment with degree bound `b` is paired with. -/
def BatchKey.shiftH (key : BatchKey G1 G2) : Option ℕ → G2
  | none => key.h
  | some d => key.negPowH d

theorem BatchKey.shiftH_eq {key : BatchKey G1 G2} {τ κ : F} (hwf : key.wellFormed τ κ) :
    ∀ b, key.shiftH b = (τ ^ boundShift key.maxDegree b)⁻¹ • key.h
  | none => by simp [shiftH, boundShift]
  | some d => hwf.2.2 d

/-- An opened label of a `batch_check` point : its commitment, its degree bound, and its
claimed value. -/
structure PCTerm (G1 F : Type*) where
  comm : G1
  bound : Option ℕ
  value : F

/-- A `batch_check` query point : the point, its opened labels in label order, and its
KZG proof, the witness `w` and `random_v`. -/
structure PCPoint (G1 F : Type*) where
  z : F
  terms : List (PCTerm G1 F)
  w : G1
  rv : F

/-- The point's part of the pairing product with challenges `ξ` and randomizer `r`
(`accumulate_elems`) : each commitment scaled by `r ξ_i` against its shift, less
`r (v g − z w + random_v gamma_g)` against `h` and `r w` against `beta_h`, with
`v = Σ ξ_i v_i`. -/
def PCPoint.pairing (e : Pairing F G1 G2 GT) (key : BatchKey G1 G2) (o : PCPoint G1 F)
    (ξ : List F) (r : F) : GT :=
  (List.zipWith (fun t x => e.pair ((r * x) • t.comm) (key.shiftH t.bound)) o.terms ξ).sum -
    e.pair (r • (weightedSum ξ (o.terms.map PCTerm.value) • key.g - o.z • o.w +
      o.rv • key.gammaG)) key.h -
    e.pair (r • o.w) key.betaH

/-- The pairing product of the points with challenges `ξs` and randomizers `rs`. -/
def pcProduct (e : Pairing F G1 G2 GT) (key : BatchKey G1 G2) :
    List (PCPoint G1 F) → List (List F) → List F → GT
  | o :: os, ξ :: ξs, r :: rs => o.pairing e key ξ r + pcProduct e key os ξs rs
  | _, _, _ => 0

/-- `batch_check`'s pairing check (`check_elems`) : the product is the identity.
`check_elems` adds the commitments of one degree bound, and the points' adjusted
witnesses and witnesses, before pairing them, which bilinearity makes this sum. -/
def pcCheck (e : Pairing F G1 G2 GT) (key : BatchKey G1 G2) (os : List (PCPoint G1 F))
    (ξs : List (List F)) (rs : List F) : Prop :=
  pcProduct e key os ξs rs = 0

/-- An opened label against the algebraic representations : the representation of its
commitment over the powers of `g` and of `gamma_g`, its degree bound, and its claimed
value. An LC's commitment combines its terms' (`check_combinations`), so its
representation combines theirs. -/
structure RepTerm (F : Type*) [Field F] where
  rep : F[X] × F[X]
  bound : Option ℕ
  value : F

/-- A query point against the algebraic representations : the point, its opened labels,
the representation of the proof's witness, and `random_v`. -/
structure RepPoint (F : Type*) [Field F] where
  z : F
  terms : List (RepTerm F)
  w : F[X] × F[X]
  rv : F

namespace RepPoint

variable (M : ℕ) (τ κ : F) (o : RepPoint F)

/-- The point's group elements, with `gamma_g = κ g`. -/
noncomputable def toGroup (g : G1) : PCPoint G1 F where
  z := o.z
  terms := o.terms.map fun t => ⟨repEval τ κ t.rep • g, t.bound, t.value⟩
  w := repEval τ κ o.w • g
  rv := o.rv

/-- The point's scalar : its part of the pairing product, over `e(g, h)`, with
randomizer `1`. -/
noncomputable def scalar (ξ : List F) : F :=
  weightedSum ξ (o.terms.map fun t => (τ ^ boundShift M t.bound)⁻¹ * repEval τ κ t.rep) -
    weightedSum ξ (o.terms.map RepTerm.value) - κ * o.rv - (τ - o.z) * repEval τ κ o.w

/-- What the point opens : each commitment's polynomial above its shift, with its claimed
value, and the witness's polynomial along `g`. -/
noncomputable def opening : PointOpening F :=
  ⟨o.z, o.terms.map fun t => (t.rep.1 /ₘ X ^ boundShift M t.bound, t.value), o.w.1⟩

/-- `τ^M` times the scalar, as a pair of polynomials to evaluate at `(τ, κ)`. -/
noncomputable def cleared (ξ : List F) : F[X] × F[X] :=
  (weightedSumPoly ξ (o.terms.map fun t => X ^ (M - boundShift M t.bound) * t.rep.1) -
      X ^ M * (C (weightedSum ξ (o.terms.map RepTerm.value)) + (X - C o.z) * o.w.1),
    weightedSumPoly ξ (o.terms.map fun t => X ^ (M - boundShift M t.bound) * t.rep.2) -
      X ^ M * (C o.rv + (X - C o.z) * o.w.2))

end RepPoint

/-- The points' scalars with their challenges. -/
noncomputable def scalarsAt (M : ℕ) (τ κ : F) (os : List (RepPoint F)) (ξs : List (List F)) :
    List F :=
  List.zipWith (fun o ξ => o.scalar M τ κ ξ) os ξs

theorem RepPoint.pairing_toGroup (e : Pairing F G1 G2 GT) {key : BatchKey G1 G2} {τ κ : F}
    (hwf : key.wellFormed τ κ) (o : RepPoint F) (ξ : List F) (r : F) :
    (o.toGroup τ κ key.g).pairing e key ξ r =
      (r * o.scalar key.maxDegree τ κ ξ) • e.pair key.g key.h := by
  have hterms : ∀ (ts : List (RepTerm F)) (ξ : List F),
      (List.zipWith (fun t x => e.pair ((r * x) • t.comm) (key.shiftH t.bound))
          (ts.map fun t => (⟨repEval τ κ t.rep • key.g, t.bound, t.value⟩ : PCTerm G1 F))
          ξ).sum =
        (r * weightedSum ξ (ts.map fun t =>
            (τ ^ boundShift key.maxDegree t.bound)⁻¹ * repEval τ κ t.rep)) •
          e.pair key.g key.h := by
    intro ts
    induction ts with
    | nil => intro ξ; simp
    | cons t ts ih =>
      intro ξ
      cases ξ with
      | nil => simp
      | cons x ξ =>
        simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, weightedSum_cons, ih]
        rw [key.shiftH_eq hwf, smul_smul, e.map_smul_left, e.map_smul_right, smul_smul,
          ← add_smul]
        congr 1
        ring
  have hadj : r • (weightedSum ξ (o.terms.map RepTerm.value) • key.g -
      o.z • (repEval τ κ o.w • key.g) + o.rv • (κ • key.g)) =
      (r * (weightedSum ξ (o.terms.map RepTerm.value) - o.z * repEval τ κ o.w + o.rv * κ)) •
        key.g := by
    module
  simp only [PCPoint.pairing, toGroup, hterms, List.map_map, Function.comp_def]
  rw [hwf.1, hwf.2.1, hadj, e.map_smul_left, smul_smul, e.map_smul_left, e.map_smul_right,
    smul_smul, ← sub_smul, ← sub_smul]
  congr 1
  simp only [scalar]
  ring

/-- Against the representations, a well-formed key makes the pairing product the
randomized scalars times `e(g, h)`. -/
theorem pcProduct_toGroup (e : Pairing F G1 G2 GT) {key : BatchKey G1 G2} {τ κ : F}
    (hwf : key.wellFormed τ κ) :
    ∀ (os : List (RepPoint F)) (ξs : List (List F)) (rs : List F),
      pcProduct e key (os.map fun o => o.toGroup τ κ key.g) ξs rs =
        weightedSum rs (scalarsAt key.maxDegree τ κ os ξs) • e.pair key.g key.h
  | [], _, _ => by simp [pcProduct, scalarsAt]
  | _ :: _, [], _ => by simp [pcProduct, scalarsAt]
  | _ :: _, _ :: _, [] => by simp [pcProduct]
  | o :: os, ξ :: ξs, r :: rs => by
    simp only [List.map_cons, pcProduct, scalarsAt, List.zipWith_cons_cons, weightedSum_cons]
    rw [RepPoint.pairing_toGroup e hwf, add_smul]
    exact congrArg _ (pcProduct_toGroup e hwf os ξs rs)

/-- An accepted pairing check on algebraic elements : the randomized scalars sum to
zero. -/
theorem weightedSum_scalarsAt_of_pcCheck (e : Pairing F G1 G2 GT) {key : BatchKey G1 G2}
    {τ κ : F} (hwf : key.wellFormed τ κ) (hgh : e.pair key.g key.h ≠ 0) {os : List (RepPoint F)}
    {ξs : List (List F)} {rs : List F}
    (h : pcCheck e key (os.map fun o => o.toGroup τ κ key.g) ξs rs) :
    weightedSum rs (scalarsAt key.maxDegree τ κ os ξs) = 0 :=
  eq_zero_of_smul_eq_zero ((pcProduct_toGroup e hwf os ξs rs).symm.trans h) hgh

/-- `Σ ξ_i (f_i + κ g_i) = c Σ ξ_i h_i` once each `f_i + κ g_i = c h_i`. -/
theorem weightedSum_map_add_mul {α : Type*} (κ c : F) (f g h : α → F)
    (hfg : ∀ t, f t + κ * g t = c * h t) :
    ∀ (ξ : List F) (ts : List α),
      weightedSum ξ (ts.map f) + κ * weightedSum ξ (ts.map g) = c * weightedSum ξ (ts.map h)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: ξ, t :: ts => by
    simp only [List.map_cons, weightedSum_cons]
    linear_combination x * hfg t + weightedSum_map_add_mul κ c f g h hfg ξ ts

theorem weightedSumPoly_map_add {α : Type*} (f g : α → F[X]) :
    ∀ (ξ : List F) (ts : List α),
      weightedSumPoly ξ (ts.map fun t => f t + g t) =
        weightedSumPoly ξ (ts.map f) + weightedSumPoly ξ (ts.map g)
  | [], _ => by simp
  | _ :: _, [] => by simp [weightedSumPoly]
  | x :: ξ, t :: ts => by
    simp only [List.map_cons, weightedSumPoly, weightedSumPoly_map_add f g ξ ts]
    ring

theorem weightedSumPoly_map_mul_left {α : Type*} (p : F[X]) (f : α → F[X]) :
    ∀ (ξ : List F) (ts : List α),
      weightedSumPoly ξ (ts.map fun t => p * f t) = p * weightedSumPoly ξ (ts.map f)
  | [], _ => by simp
  | _ :: _, [] => by simp [weightedSumPoly]
  | x :: ξ, t :: ts => by
    simp only [List.map_cons, weightedSumPoly, weightedSumPoly_map_mul_left p f ξ ts]
    ring

theorem degree_weightedSumPoly_lt {M : ℕ} :
    ∀ (ξ : List F) (ps : List F[X]), (∀ p ∈ ps, p.degree < M) →
      (weightedSumPoly ξ ps).degree < M
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [weightedSumPoly]
  | x :: ξ, p :: ps, h => by
    simp only [weightedSumPoly]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · rw [← smul_eq_C_mul]
      exact lt_of_le_of_lt (degree_smul_le _ _) (h p (by simp))
    · exact degree_weightedSumPoly_lt ξ ps fun q hq => h q (by simp [hq])

namespace RepPoint

variable {M : ℕ} {τ κ : F}

theorem eval_cleared (hτ : τ ≠ 0) (o : RepPoint F) (ξ : List F) :
    repEval τ κ (o.cleared M ξ) = τ ^ M * o.scalar M τ κ ξ := by
  have hpt : ∀ t : RepTerm F,
      (X ^ (M - boundShift M t.bound) * t.rep.1).eval τ +
          κ * (X ^ (M - boundShift M t.bound) * t.rep.2).eval τ =
        τ ^ M * ((τ ^ boundShift M t.bound)⁻¹ * repEval τ κ t.rep) := by
    intro t
    have hs : τ ^ M = τ ^ (M - boundShift M t.bound) * τ ^ boundShift M t.bound := by
      rw [← pow_add, Nat.sub_add_cancel (boundShift_le M t.bound)]
    have hne : τ ^ boundShift M t.bound ≠ 0 := pow_ne_zero _ hτ
    simp only [eval_mul, eval_pow, eval_X, repEval]
    rw [hs]
    field_simp
  have hsum := weightedSum_map_add_mul κ (τ ^ M) _ _ _ hpt ξ o.terms
  simp only [repEval, cleared, eval_sub, eval_weightedSumPoly, eval_mul, eval_pow, eval_X,
    eval_add, eval_C, List.map_map, Function.comp_def] at hsum ⊢
  simp only [scalar, repEval]
  linear_combination hsum

/-- Along `g`, the cleared pair is `X^M` times the defect of what the point opens, plus
the parts below the shifts, each lifted by `X^{M−s}`. -/
theorem cleared_fst (o : RepPoint F) (ξ : List F) :
    (o.cleared M ξ).1 = X ^ M * (o.opening M).defect ξ +
      weightedSumPoly ξ (o.terms.map fun t =>
        X ^ (M - boundShift M t.bound) * (t.rep.1 %ₘ X ^ boundShift M t.bound)) := by
  have hpt : ∀ t : RepTerm F, X ^ (M - boundShift M t.bound) * t.rep.1 =
      X ^ M * (t.rep.1 /ₘ X ^ boundShift M t.bound) +
        X ^ (M - boundShift M t.bound) * (t.rep.1 %ₘ X ^ boundShift M t.bound) := by
    intro t
    have hs : (X : F[X]) ^ M = X ^ (M - boundShift M t.bound) * X ^ boundShift M t.bound := by
      rw [← pow_add, Nat.sub_add_cancel (boundShift_le M t.bound)]
    conv_lhs => rw [← modByMonic_add_div t.rep.1 (X ^ boundShift M t.bound)]
    rw [hs]
    ring
  simp only [cleared, opening, PointOpening.defect, List.map_map, Function.comp_def]
  rw [List.map_congr_left fun t _ => hpt t, weightedSumPoly_map_add,
    weightedSumPoly_map_mul_left]
  ring

theorem degree_low_lt (o : RepPoint F) (ξ : List F) :
    (weightedSumPoly ξ (o.terms.map fun t =>
      X ^ (M - boundShift M t.bound) * (t.rep.1 %ₘ X ^ boundShift M t.bound))).degree < M := by
  refine degree_weightedSumPoly_lt ξ _ fun p hp => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hp
  set s := boundShift M t.bound
  by_cases h0 : t.rep.1 %ₘ X ^ s = 0
  · rw [h0, mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hlt : (t.rep.1 %ₘ X ^ s).degree < s := by
      simpa using degree_modByMonic_lt t.rep.1 (monic_X_pow s)
    rw [degree_eq_natDegree h0] at hlt
    rw [degree_mul, degree_X_pow, degree_eq_natDegree h0]
    have hlt' : (t.rep.1 %ₘ X ^ s).natDegree < s := by exact_mod_cast hlt
    have hsM : s ≤ M := boundShift_le M t.bound
    exact_mod_cast (show M - s + (t.rep.1 %ₘ X ^ s).natDegree < M by omega)

/-- A zero cleared pair along `g` makes the defect of what the point opens zero. -/
theorem defect_eq_zero_of_cleared (o : RepPoint F) (ξ : List F) (h : (o.cleared M ξ).1 = 0) :
    (o.opening M).defect ξ = 0 := by
  by_contra hD
  rw [cleared_fst] at h
  have heq : X ^ M * (o.opening M).defect ξ = -weightedSumPoly ξ (o.terms.map fun t =>
      X ^ (M - boundShift M t.bound) * (t.rep.1 %ₘ X ^ boundShift M t.bound)) := by
    linear_combination h
  have hge : (M : WithBot ℕ) ≤ (X ^ M * (o.opening M).defect ξ).degree := by
    rw [degree_mul, degree_X_pow]
    exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hD)
  rw [heq, degree_neg] at hge
  exact absurd (o.degree_low_lt ξ) (not_lt.mpr hge)

end RepPoint

/-- The batch check passes by luck : the randomizers `rs` cancel nonzero scalars, or some
point's challenges cancel a wrong claim. -/
def RepLucky (M : ℕ) (τ κ : F) (os : List (RepPoint F)) (ξs : List (List F)) (rs : List F) :
    Prop :=
  inspectBatch rs (scalarsAt M τ κ os ξs) ≠ none ∨
    ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
      inspectBatch ξs[j] (os[j].opening M).discrepancies ≠ none

/-- The SRS is broken at the points : the trapdoor is `0`, or some point's cleared pair is
nonzero with root `(τ, κ)`. -/
def RepBreak (M : ℕ) (τ κ : F) (os : List (RepPoint F)) (ξs : List (List F)) : Prop :=
  τ = 0 ∨ ∃ j, ∃ hj : j < os.length, ∃ hj' : j < ξs.length,
    os[j].cleared M ξs[j] ≠ 0 ∧ repEval τ κ (os[j].cleared M ξs[j]) = 0

/-- A break at the points is an SRS break. -/
theorem RepBreak.srsBreak {M : ℕ} {τ κ : F} {os : List (RepPoint F)} {ξs : List (List F)}
    (h : RepBreak M τ κ os ξs) : ∃ br : SRSBreak F, br.holds τ κ := by
  rcases h with rfl | ⟨j, hj, hj', hne, hev⟩
  · exact SRSBreak.of_trapdoor_zero κ
  · refine SRSBreak.of_polys ?_ hev
    by_contra h0
    push Not at h0
    exact hne (Prod.ext h0.1 h0.2)

/-- Pairing-check extraction against the representations. If the randomized scalars sum to
zero, nothing is lucky, and the SRS is not broken at the points, every claimed value is
the value of its polynomial above the shift. -/
theorem repCheck_extract {M : ℕ} {τ κ : F} {os : List (RepPoint F)} {ξs : List (List F)}
    {rs : List F} (hlen : os.length ≤ ξs.length)
    (hcheck : weightedSum rs (scalarsAt M τ κ os ξs) = 0) (hl : ¬RepLucky M τ κ os ξs rs)
    (hbr : ¬RepBreak M τ κ os ξs) :
    ∀ o ∈ os, ∀ pv ∈ (o.opening M).opened, pv.2 = pv.1.eval o.z := by
  intro o ho pv hpv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
  have hj' : j < ξs.length := by omega
  have hτ : τ ≠ 0 := fun h => hbr (Or.inl h)
  have hr : inspectBatch rs (scalarsAt M τ κ os ξs) = none := by
    by_contra h
    exact hl (Or.inl h)
  have hsc : os[j].scalar M τ κ ξs[j] = 0 := by
    refine inspectBatch_accepts hcheck hr _ ?_
    have hlt : j < (scalarsAt M τ κ os ξs).length := by
      simp only [scalarsAt, List.length_zipWith]
      omega
    have hmem := List.getElem_mem hlt
    simpa [scalarsAt] using hmem
  have hcl : os[j].cleared M ξs[j] = 0 := by
    by_contra hne
    exact hbr (Or.inr ⟨j, hj, hj', hne, by rw [RepPoint.eval_cleared hτ, hsc, mul_zero]⟩)
  have hξ : inspectBatch ξs[j] (os[j].opening M).discrepancies = none := by
    by_contra h
    exact hl (Or.inr ⟨j, hj, hj', h⟩)
  exact (os[j].opening M).claims_of_defect_eq_zero
    (os[j].defect_eq_zero_of_cleared ξs[j] (by rw [hcl]; rfl)) hξ pv hpv

/-- Batch-check extraction at the group level. If the pairing check accepts on algebraic
elements under a well-formed key, nothing is lucky, and the SRS is not broken at the
points, every claimed value is the value of its polynomial above the shift. -/
theorem pcCheck_extract (e : Pairing F G1 G2 GT) {key : BatchKey G1 G2} {τ κ : F}
    (hwf : key.wellFormed τ κ) (hgh : e.pair key.g key.h ≠ 0) {os : List (RepPoint F)}
    {ξs : List (List F)} {rs : List F} (hlen : os.length ≤ ξs.length)
    (hcheck : pcCheck e key (os.map fun o => o.toGroup τ κ key.g) ξs rs)
    (hl : ¬RepLucky key.maxDegree τ κ os ξs rs) (hbr : ¬RepBreak key.maxDegree τ κ os ξs) :
    ∀ o ∈ os, ∀ pv ∈ (o.opening key.maxDegree).opened, pv.2 = pv.1.eval o.z :=
  repCheck_extract hlen (weightedSum_scalarsAt_of_pcCheck e hwf hgh hcheck) hl hbr

end Pairing

/-! ## The V3 query set -/

/-- A matrix term's `matrix_sumcheck` LC term `s(γ) (a − (γ vg + σ) b)`, with `g(γ)` read
as `vg` (`ahp.rs:407-422`). -/
noncomputable def MatrixTerm.lcAt (K : EvalDomain F) (t : MatrixTerm F) (γ vg : F) : F[X] :=
  C ((selectorPoly K t.K).eval γ) * (t.a - C (γ * vg + t.σ) * t.b)

theorem MatrixTerm.eval_lcAt (K : EvalDomain F) (t : MatrixTerm F) (γ vg : F) :
    (t.lcAt K γ vg).eval γ = t.summandAt K γ vg := by
  simp only [lcAt, summandAt, eval_mul, eval_C, eval_sub]
  ring

/-- The circuit's three `matrix_sumcheck` LC terms, `A, B, C` in order, with the opened
`g_M(γ)`. -/
noncomputable def BatchCircuit.matrixLCs (c : BatchCircuit F) (K : EvalDomain F) (α β γ : F) :
    List F[X] :=
  [MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KA, c.A, α, β, c.gA, c.σmA⟩ γ c.vgA,
    MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KB, c.B, α, β, c.gB, c.σmB⟩ γ c.vgB,
    MatrixTerm.lcAt K ⟨c.R, c.Cd, c.KC, c.Cm, α, β, c.gC, c.σmC⟩ γ c.vgC]

namespace V3Batch

variable (P : V3Batch F)

/-- snarkVM's `rowcheck_zerocheck` (`ahp.rs:246-271`) as a polynomial : the prepare-third
sums as a constant, less `v_R(α) h₀`. -/
noncomputable def rowLC (ws : List F) : F[X] :=
  C (weightedSum ws (P.instances.map fun p =>
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC))) -
    C (P.R.vanishing.eval P.α) * toPoly P.h0rep

/-- snarkVM's `lineval_sumcheck` (`ahp.rs:314-355`) as a polynomial : the mask, each
instance's `x̂(β) + v_X(β) ŵ` with its weight, less `v_C(β) h₁` and the constants
`β g₁(β)`, read off the claimed value, and the batch sum. -/
noncomputable def linLC (ws : List F) : F[X] :=
  maskPoly P.mode P.mask +
      weightedSumPoly ws (P.instances.map fun p =>
        C ((selectorPoly P.Cd p.1.Cd).eval P.β *
            (P.ηA * ((p.1.KA.n : F) * p.1.σmA) + P.ηB * ((p.1.KB.n : F) * p.1.σmB) +
              P.ηC * ((p.1.KC.n : F) * p.1.σmC))) *
          (C ((p.1.Xd.interpolate fun k => p.2.x.getD k 0).eval P.β) +
            C (p.1.Xd.vanishing.eval P.β) * p.2.w)) -
    C (P.Cd.vanishing.eval P.β) * P.h1 - C (P.β * P.vG1 + P.linSum ws * P.Cd.sizeInv)

/-- snarkVM's `matrix_sumcheck` (`ahp.rs:363-402`) as a polynomial : every matrix term,
`δ`-weighted, with the opened `g_M(γ)`, less `v_K(γ) h₂`. -/
noncomputable def matLC (δs : List F) : F[X] :=
  weightedSumPoly δs (P.circuits.flatMap fun c => c.matrixLCs P.K P.α P.β P.γ) -
    C (P.K.vanishing.eval P.γ) * P.h2

/-- Every circuit's opened `g_A(γ), g_B(γ), g_C(γ)`, in label order (`circuit_{id}_g_a_…`
sorts before `matrix_sumcheck`). -/
def gOpenings : List (F[X] × F) :=
  P.circuits.flatMap fun c => [(c.gA, c.vgA), (c.gB, c.vgB), (c.gC, c.vgC)]

/-- `batch_check`'s query points in order (`messages.rs:100-140`) : the rowcheck LC at `α`;
`g₁` and the lineval LC at `β`; the `g_M` and the matrix LC at `γ`. Each LC opens to `0`;
the weights are read off `chal`, and `qs` are the polynomials behind the KZG proofs. -/
noncomputable def pcPoints (chal : V2Challenge → List F) (qs : List F[X]) :
    List (PointOpening F) :=
  [⟨P.α, [(P.rowLC (P.rowWeights chal), 0)], qs.getD 0 0⟩,
    ⟨P.β, [(P.g1, P.vG1), (P.linLC (P.linWeights chal), 0)], qs.getD 1 0⟩,
    ⟨P.γ, P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)], qs.getD 2 0⟩]

theorem eval_rowLC (ws : List F) :
    (P.rowLC ws).eval P.α = weightedSum ws (P.instances.map fun p =>
      (selectorPoly P.R p.1.R).eval P.α * (p.2.σA * p.2.σB - p.2.σC)) -
        evalCoeffs P.h0rep P.α * P.R.vanishing.eval P.α := by
  simp only [rowLC, eval_sub, eval_C, eval_mul, eval_toPoly]
  ring

theorem eval_linLC {ws : List F} (hg : P.vG1 = P.g1.eval P.β) :
    (P.linLC ws).eval P.β = P.linEval ws := by
  simp only [linLC, linEval, eval_add, eval_sub, eval_mul, eval_C, eval_weightedSumPoly,
    List.map_map, Function.comp_def, BatchCircuit.zhat, eval_assignmentPoly, hg, mul_assoc]
  ring

theorem eval_matLC {δs : List F}
    (hg : ∀ c ∈ P.circuits, c.vgA = c.gA.eval P.γ ∧ c.vgB = c.gB.eval P.γ ∧ c.vgC = c.gC.eval P.γ) :
    (P.matLC δs).eval P.γ = batchedMatrixEval P.K δs P.matrixTerms P.h2 P.γ := by
  have hc : ∀ c ∈ P.circuits, (c.matrixLCs P.K P.α P.β P.γ).map (fun q => q.eval P.γ) =
      (c.matrixTerms P.α P.β).map fun t => (selectorPoly P.K t.K).eval P.γ *
        (t.a.eval P.γ - t.b.eval P.γ * (P.γ * t.g.eval P.γ + t.σ)) := by
    intro c hc
    obtain ⟨hA, hB, hC⟩ := hg c hc
    simp only [BatchCircuit.matrixLCs, BatchCircuit.matrixTerms, List.map_cons, List.map_nil,
      MatrixTerm.eval_lcAt, MatrixTerm.summandAt, hA, hB, hC]
  rw [matLC, eval_sub, eval_weightedSumPoly, List.map_flatMap, flatMap_congr_mem hc,
    batchedMatrixEval, matrixTerms, List.map_flatMap]
  simp only [eval_mul, eval_C]
  ring

/-- The V3 verifier's checks of `P` as snarkVM runs them : those of `Accepts` but the
openings and the three LC equations, which the batch check over `pcPoints` replaces. The
check reads the randomizers `rs`, each point's combination challenges `ξs`, and the
polynomials `qs` behind the KZG proofs, against the trapdoor `τ`. -/
structure DeployedAccepts (P : V3Batch F) (S : Finset F) (t : V2Transcript F)
    (chal : V2Challenge → List F) (comms : List (List F)) (τ : F) (qs : List F[X])
    (ξs : List (List F)) (rs : List F) : Prop where
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
  degL : (X * P.g1 + C (P.linSum (P.linWeights chal) * P.Cd.sizeInv)).natDegree < P.Cd.n
  points : ξs.length = 3
  check : weightedSum rs (defectsAt τ (P.pcPoints chal qs) ξs) = 0

/-- The relation from the deployed checks : with no squeezed element in its bad set, no
lucky combination in the batch check, and no trapdoor break, the transcript's batch
satisfies `Holds`. -/
theorem holds_of_deployedAccepts {P : V3Batch F} {S : Finset F} {t : V2Transcript F}
    {chal : V2Challenge → List F} {comms : List (List F)} {τ : F} {qs : List F[X]}
    {ξs : List (List F)} {rs : List F} (h : P.DeployedAccepts S t chal comms τ qs ξs rs)
    (hnb : outputBreaks (prefixBad t (P.squeezeBad S chal)) t chal = false)
    (hl : ¬PCLucky τ (P.pcPoints chal qs) ξs rs) (hbr : ¬PCBreak τ (P.pcPoints chal qs) ξs) :
    P.Holds t := by
  have hpt : ∀ o ∈ P.pcPoints chal qs, ∀ pv ∈ o.opened, pv.2 = pv.1.eval o.z :=
    batchCheck_extract (by simp [pcPoints, h.points]) h.check hl hbr
  have hα := hpt ⟨P.α, [(P.rowLC (P.rowWeights chal), 0)], qs.getD 0 0⟩ (by simp [pcPoints])
  have hβ := hpt ⟨P.β, [(P.g1, P.vG1), (P.linLC (P.linWeights chal), 0)], qs.getD 1 0⟩
    (by simp [pcPoints])
  have hγ := hpt ⟨P.γ, P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)], qs.getD 2 0⟩
    (by simp [pcPoints])
  have hrow : (0 : F) = (P.rowLC (P.rowWeights chal)).eval P.α :=
    hα (P.rowLC (P.rowWeights chal), 0) (by simp)
  have hg1 : P.vG1 = P.g1.eval P.β := hβ (P.g1, P.vG1) (by simp)
  have hlin : (0 : F) = (P.linLC (P.linWeights chal)).eval P.β :=
    hβ (P.linLC (P.linWeights chal), 0) (by simp)
  have hmat : (0 : F) = (P.matLC (P.deltaWeights chal)).eval P.γ :=
    hγ (P.matLC (P.deltaWeights chal), 0) (by simp)
  have hgM : ∀ c ∈ P.circuits,
      c.vgA = c.gA.eval P.γ ∧ c.vgB = c.gB.eval P.γ ∧ c.vgC = c.gC.eval P.γ := by
    intro c hc
    have hmem : ∀ pv ∈ [(c.gA, c.vgA), (c.gB, c.vgB), (c.gC, c.vgC)],
        pv ∈ P.gOpenings ++ [(P.matLC (P.deltaWeights chal), 0)] :=
      fun pv hpv => List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hpv⟩)
    exact ⟨hγ (c.gA, c.vgA) (hmem _ (by simp)), hγ (c.gB, c.vgB) (hmem _ (by simp)),
      hγ (c.gC, c.vgC) (hmem _ (by simp))⟩
  exact V3Batch.sound_of_transcript_evals { P with vH0 := evalCoeffs P.h0rep P.α } S t chal comms
    h.init h.msg h.inS h.alpha h.beta h.gamma h.nu h.eta h.etaA h.etaB h.etaC h.delta hnb h.dvdR
    h.dvdC h.dvdK h.valid h.gen (inspectOpening_honest P.h0rep [] P.α)
    ((P.eval_rowLC _).symm.trans hrow.symm) ((P.eval_linLC hg1).symm.trans hlin.symm) h.degL
    ((P.eval_matLC hgM).symm.trans hmat.symm)

end V3Batch

end Varuna