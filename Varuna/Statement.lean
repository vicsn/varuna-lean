/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Varuna.Batching

/-!
# Statement binding

Fiat–Shamir is only sound if the transcript binds the statement before the
first challenge. snarkVM's `init_sponge` (`snark/varuna/varuna.rs`) absorbs
the protocol name, then for each circuit its batch size and every
instance's public inputs, then the circuit commitments. `v2Init` models
that prefix; `v2Init_injective` shows it determines the public inputs, so
two statements with different inputs never share a challenge prefix
(`before_ne_of_inputs_ne`), and equal challenges at different prefixes are
an RO collision.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Varuna

variable {F : Type*} [Field F]

/-! ## The `init_sponge` prefix -/

/-- snarkVM `PROTOCOL_NAME`. -/
def protocolName : String :=
  "VARUNA-2023"

/-- Per-circuit block: batch size, then one field vector per instance. -/
def inputBlocks : List (List (List F)) → Transcript F
  | [] => []
  | xs :: rest => (.size xs.length :: xs.map FSMessage.fields) ++ inputBlocks rest

/-- The V2 initial transcript for public inputs `inputs` (per circuit, per
instance) and circuit commitments `comms`. -/
def v2Init (inputs : List (List (List F))) (comms : List (List F)) : Transcript F :=
  .tag protocolName :: (inputBlocks inputs ++ comms.map FSMessage.fields)

/-- Mapping into `fields` is injective. -/
theorem map_fields_injective : Function.Injective (List.map (FSMessage.fields (F := F))) :=
  List.map_injective_iff.mpr fun _ _ h => by cases h; rfl

/-- The input blocks are self-delimiting: equal prefixes followed by commitment
vectors force equal inputs and equal tails. -/
theorem inputBlocks_append_inj :
    ∀ (a b : List (List (List F))) (r s : List (List F)),
      inputBlocks a ++ r.map FSMessage.fields = inputBlocks b ++ s.map FSMessage.fields →
        a = b ∧ r = s
  | [], [], r, s, h => ⟨rfl, map_fields_injective (by simpa [inputBlocks] using h)⟩
  | [], ys :: b, r, s, h => by
    cases r with
    | nil => simp [inputBlocks] at h
    | cons x r => simp [inputBlocks] at h
  | xs :: a, [], r, s, h => by
    cases s with
    | nil => simp [inputBlocks] at h
    | cons y s => simp [inputBlocks] at h
  | xs :: a, ys :: b, r, s, h => by
    simp only [inputBlocks, List.cons_append, List.append_assoc, List.cons.injEq,
      FSMessage.size.injEq] at h
    obtain ⟨hlen, h⟩ := h
    have hmap : xs.map FSMessage.fields = ys.map FSMessage.fields := by
      have := congrArg (List.take xs.length) h
      simpa [List.take_left', hlen] using this
    have hxy : xs = ys := map_fields_injective hmap
    subst hxy
    have ⟨hab, hrs⟩ := inputBlocks_append_inj a b r s (List.append_cancel_left h)
    exact ⟨by rw [hab], hrs⟩

/-- The initial transcript determines the public inputs and commitments. -/
theorem v2Init_injective {i₁ i₂ : List (List (List F))} {c₁ c₂ : List (List F)}
    (h : v2Init i₁ c₁ = v2Init i₂ c₂) : i₁ = i₂ ∧ c₁ = c₂ := by
  simp only [v2Init, List.cons.injEq, true_and] at h
  exact inputBlocks_append_inj i₁ i₂ c₁ c₂ h

/-- Every challenge prefix starts with the initial transcript. -/
theorem init_isPrefix_before (t : V2Transcript F) (c : V2Challenge) :
    List.IsPrefix t.init (t.before c) := by
  cases c <;> exact List.prefix_append _ _

/-- Different public inputs never share a challenge prefix. -/
theorem before_ne_of_inputs_ne {t₁ t₂ : V2Transcript F} {i₁ i₂ : List (List (List F))}
    {comms : List (List F)} (h₁ : t₁.init = v2Init i₁ comms) (h₂ : t₂.init = v2Init i₂ comms)
    (hne : i₁ ≠ i₂) (c : V2Challenge) : t₁.before c ≠ t₂.before c := by
  intro heq
  have hlen : t₁.init.length = t₂.init.length := by
    have := congrArg List.length heq
    rw [before_length, before_length] at this
    omega
  have hpre₁ := init_isPrefix_before t₁ c
  have hpre₂ := init_isPrefix_before t₂ c
  rw [heq] at hpre₁
  have hinit : t₁.init = t₂.init :=
    List.prefix_of_prefix_length_le hpre₁ hpre₂ (le_of_eq hlen)
    |>.eq_of_length hlen
  rw [h₁, h₂] at hinit
  exact hne (v2Init_injective hinit).1

/-- Equal challenges for two statements with different inputs are an RO collision. -/
theorem collision_of_inputs_ne [DecidableEq F] (ro : RO F) {t₁ t₂ : V2Transcript F}
    {i₁ i₂ : List (List (List F))} {comms : List (List F)} (h₁ : t₁.init = v2Init i₁ comms)
    (h₂ : t₂.init = v2Init i₂ comms) (hne : i₁ ≠ i₂) (c : V2Challenge)
    (heq : t₁.challenge ro c = t₂.challenge ro c) :
    inspectCollision ro (t₁.before c) (t₂.before c) = some ⟨t₁.before c, t₂.before c⟩ :=
  inspectCollision_some (before_ne_of_inputs_ne h₁ h₂ hne c) heq

end Varuna