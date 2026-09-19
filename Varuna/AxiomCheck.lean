/-
Copyright (c) 2026 Provable Inc.
Licensed under the Apache License, Version 2.0; see LICENSE.md for details.
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.NoncomputableAttr

/-!
# Build-checked axiom census

Ironwood’s `assert_axioms` / `assert_computable` make the trusted base of
an advertised endpoint a kernel-checked fact rather than a comment.
This module is the corresponding elaborator for Varuna.

* `assert_axioms Foo` fails unless `Foo` depends only on `propext`,
  `Classical.choice`, and `Quot.sound` (in particular : no `sorryAx`).
* `assert_computable Foo` additionally requires `Foo` to be a `def`
  that is not marked `noncomputable`, and allows only `propext` and
  `Quot.sound` (no `Classical.choice` on the computational path).
-/

open Lean Elab Command

namespace Varuna.AxiomCheck

/-- The standard classical trusted base. -/
def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms permitted on a computable `def` (no choice on the data path). -/
def computableAxioms : Array Name :=
  #[``propext, ``Quot.sound]

/-- Fail if `name` depends on any axiom outside `allowed`. -/
def checkAxioms (n : Ident) (name : Name) (allowed : Array Name) : CommandElabM Unit := do
  let axs ← collectAxioms name
  let unexpected := axs.filter fun ax => !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axiom(s): {unexpected.toList}"

/-- Fail unless `name` is a `def` that is not tagged `noncomputable`. -/
def checkComputableDef (n : Ident) (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  match info with
  | .defnInfo _ => pure ()
  | .thmInfo _ => throwError "{n} is a theorem; `assert_computable` requires a `def`"
  | _ => throwError "{n} is not a definition"
  if isNoncomputable (← getEnv) name then
    throwError "{n} is marked `noncomputable`"

/-- Bound `n` to the standard classical axiom set. -/
syntax "assert_axioms " ident : command

elab_rules : command
  | `(command | assert_axioms $n) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    checkAxioms n name standardAxioms

/-- Bound `n` to a computable `def` with no `Classical.choice`. -/
syntax "assert_computable " ident : command

elab_rules : command
  | `(command | assert_computable $n) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
    checkComputableDef n name
    checkAxioms n name computableAxioms

end Varuna.AxiomCheck