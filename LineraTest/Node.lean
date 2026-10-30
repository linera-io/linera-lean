import Linera.Chain.Node

/-!
# Node witnesses

Two chains: chain `0` sends one bundle to chain `1` in its block `0`, and
chain `1` consumes it in its block `0`. Delivering before executing, or
executing by anticipation before delivering, ends in the same inbox.
-/

namespace LineraTest

open Linera

/-- The bundle sent by chain `0` at height `0`. -/
def b₀ : Bundle ℕ := ⟨0, 0, [⟨.simple, false, 7⟩]⟩

/-- The two-chain ledger. -/
def L : Ledger (Fin 2) (Fin 1) ℕ := fun c h =>
  if c = 0 ∧ h = 0 then some ⟨[], [(1, b₀)], fun _ => [1, 2]⟩
  else if c = 1 ∧ h = 0 then some ⟨[(0, b₀, .accept)], [], fun _ => []⟩
  else none

/-- Execute chain `0`, deliver to chain `1`, execute chain `1`. -/
def viaDelivery : Option (Node (Fin 2) ℕ) :=
  (Node.execute L Node.init 0).bind fun N => (Node.deliver L N 0 1).bind fun N => Node.execute L N 1

/-- Execute chain `0`, execute chain `1` by anticipation, then deliver. -/
def viaAnticipation : Option (Node (Fin 2) ℕ) :=
  (Node.execute L Node.init 0).bind fun N => (Node.execute L N 1).bind fun N => Node.deliver L N 0 1

/-- The inbox of `1` for `0` in both runs is empty with both cursors past `b₀`. -/
theorem inbox_after :
    viaDelivery.map (·.inboxes 1 0) = some ⟨b₀.cursor.succ, b₀.cursor.succ, [], []⟩ ∧
    viaAnticipation.map (·.inboxes 1 0) = some ⟨b₀.cursor.succ, b₀.cursor.succ, [], []⟩ := by
  decide

/-- Delivery before the sender block is stored is refused. -/
theorem deliver_needs_block : Node.deliver L Node.init 0 1 = none := by decide

end LineraTest
