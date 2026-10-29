import Linera.Protocol

/-!
# A four-validator model

Four validators of equal power, `f = 1`, validator `3` Byzantine; two
owners; three blocks. The quorum size is `3`. Used by every witness.
-/

namespace LineraTest

open Linera

/-- The validators. -/
abbrev V := Fin 4
/-- The owners. -/
abbrev Owner := Fin 2
/-- The blocks. -/
abbrev Block := Fin 3

/-- Equal power, `f = 1`, validator `3` Byzantine. -/
def W : Weighted V where
  weight := fun _ => 1
  f := 1
  byzantine := {3}
  byz_le := by decide
  three_f_lt := by decide

instance : QuorumSystem V := W.toQuorumSystem

/-- Two multi-leader rounds (`0`, `1`), then single-leader rounds with a
round-robin leader; every block valid; no fast round. -/
def slowCfg : Config Owner Block where
  fast := false
  super := 0
  k := 2
  leader := fun r => ⟨r % 2, Nat.mod_lt _ (by decide)⟩
  Valid := fun _ => True

/-- A fast round `0` led by super owner `0`, then multi-leader rounds `1`
and `2`, then single-leader rounds. -/
def fastCfg : Config Owner Block := { slowCfg with fast := true }

/-- Run honest inputs from the initial state and evaluate a decidable
property of the result; `false` if any input is refused. -/
def check (cfg : Config Owner Block) (inputs : List (V × Input Owner Block))
    (p : State V Owner Block → Prop) [DecidablePred p] : Bool :=
  match run cfg inputs State.init with
  | some s => decide (p s)
  | none => false

end LineraTest
