-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

module

meta import Lean
import PalomarSolution
import QPRigidity.NonVacuity
import QPRigidity.AdversarialTests

/-!
# Exhaustive Whole-Package Axiom Sweep (`SweepAllAxioms.lean`)

Uses Lean 4's `Lean.collectAxioms` metaprogramming API to audit EVERY single constant
whose namespace begins with `QPRigidity`, `Challenge`, `Solution`, or `PalomarSolution`
(not merely hand-listed headline theorems!), aborting with an error if ANY declaration
depends on `sorryAx`, any `_native` axiom, or any custom axiom outside
`{propext, Classical.choice, Quot.sound}`.
-/

open Lean

private def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

private def isProjectDecl (n : Name) : Bool :=
  match n.getRoot with
  | `QPRigidity | `Challenge | `Solution | `PalomarSolution => true
  | _ => false

run_meta do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut bad : Array (Name × List Name) := #[]
  for (declName, _) in env.constants.map₁.toList do
    if isProjectDecl declName && !declName.isInternal then
      checked := checked + 1
      let axs ← collectAxioms declName
      let illegal := axs.toList.filter fun ax => !allowedAxioms.contains ax
      if !illegal.isEmpty then
        bad := bad.push (declName, illegal)
  if !bad.isEmpty then
    throwError m!"UNAUTHORIZED AXIOMS DETECTED IN PROJECT DECLARATIONS: {bad}"
  IO.println s!"[SWEEP-OK] Exhaustively audited {checked} project declarations: 0 unauthorized axioms (strictly within [propext, Classical.choice, Quot.sound])."
