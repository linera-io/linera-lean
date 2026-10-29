import LeanLinera
import LeanLineraTest

/-!
Print the axioms of every theorem in the project and fail if any theorem
depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
Run with `lake env lean scripts/Axioms.lean`.
-/

open Lean Elab Command in
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × List Name) := #[]
  let mut count := 0
  for (n, ci) in env.constants.map₁.toList do
    unless n.getRoot == `LeanLinera || n.getRoot == `LeanLineraTest do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    let axs ← collectAxioms n
    let extra := axs.toList.filter (fun a => !allowed.contains a)
    if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"audited {count} theorems"
  if bad.isEmpty then
    logInfo "all theorems use only propext, Classical.choice, Quot.sound"
  else
    for (n, ax) in bad do
      logError m!"{n} depends on {ax}"

#audit_axioms
