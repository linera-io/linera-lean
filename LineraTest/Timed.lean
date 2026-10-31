import Linera.Chain.Timed
import LineraTest.Node

/-!
# Timed run witnesses

A run on the two-chain ledger of `LineraTest.Node`: chain `0`'s block is
stored at tick `0`, delivered to chain `1` at tick `1`, chain `1`'s block
is executed at tick `2`, then nothing. A delivery attempted before the
sender block is stored is refused and the view does not change.
-/

namespace LineraTest

open Linera

/-- Store chain `0`'s block, deliver it to `1`, execute `1`, then idle. -/
def acts : ℕ → Option (Node.Act (Fin 2))
  | 0 => some (.preprocess 0 0)
  | 1 => some (.deliver 0 1)
  | 2 => some (.execute 1)
  | _ => none

/-- The run attempting `acts`. -/
def run : Node.Run L := Node.Run.ofActs L acts

/-- The delivery counter of `0` to `1` moves at tick `1`, when the sender block is stored. -/
theorem run_delivered :
    (run.st 1).delivered 0 1 = 0 ∧ (run.st 1).Holds 0 0 ∧ (run.st 2).delivered 0 1 = 1 := by
  decide

/-- At tick `3` the inbox of `1` for `0` is empty with both cursors past `b₀`. -/
theorem run_inbox : (run.st 3).inboxes 1 0 = ⟨b₀.cursor.succ, b₀.cursor.succ, [], []⟩ := by
  decide

/-- Delivering first is refused: the view at tick `1` is still the initial one. -/
theorem run_refused :
    ((Node.Run.ofActs L fun _ => some (.deliver 0 1)).st 1).delivered 0 1 = 0 := by
  decide

end LineraTest
