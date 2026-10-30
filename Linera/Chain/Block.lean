import Linera.Chain.Inbox

/-!
# Blocks and the ledger

For the cross-chain layer a certified block is reduced to what the other
chains see of it: the bundles it consumes (with an accept or reject
action), the bundles it sends, and the events it emits per stream. The
*ledger* is the function from a chain and a height to its certified block,
if any — unique by the per-height safety theorem (`safety`), which is the
only consensus fact this layer uses.
-/

namespace Linera

/-- What a recipient block does with a bundle (`MessageAction`). -/
inductive MessageAction
  /-- Execute the messages. -/
  | accept
  /-- Do not execute them; tracked messages bounce. -/
  | reject
  deriving DecidableEq, Repr

/-- A certified block, as seen across chains. -/
structure Block (Chain Stream Payload : Type*) where
  /-- The bundles consumed, each with its sender and the action taken. -/
  incoming : List (Chain × Bundle Payload × MessageAction)
  /-- The bundles sent, each with its recipient. -/
  outgoing : List (Chain × Bundle Payload)
  /-- The events emitted, per stream, in order. -/
  events : Stream → List Payload

/-- The ledger: the certified block of each chain at each height, if any. -/
abbrev Ledger (Chain Stream Payload : Type*) := Chain → ℕ → Option (Block Chain Stream Payload)

namespace Ledger

variable {Chain Stream Payload : Type*} [DecidableEq Chain]
variable (L : Ledger Chain Stream Payload)

/-- The bundles sent by chain `s` at height `h` to chain `r`. -/
def sendsTo (s r : Chain) (h : ℕ) : List (Bundle Payload) :=
  match L s h with
  | some B => (B.outgoing.filter (fun x => decide (x.1 = r))).map (·.2)
  | none => []

/-- The bundles consumed by chain `r` at height `h` from sender `s`. -/
def receivesFrom (r s : Chain) (h : ℕ) : List (Bundle Payload) :=
  match L r h with
  | some B => (B.incoming.filter (fun x => decide (x.1 = s))).map (·.2.1)
  | none => []

/-- The bundles sent by `s` to `r` in heights below `n`, in order. -/
def addsUpTo (s r : Chain) (n : ℕ) : List (Bundle Payload) :=
  (List.range n).flatMap (L.sendsTo s r)

/-- The bundles consumed by `r` from `s` in heights below `n`, in order. -/
def removesUpTo (r s : Chain) (n : ℕ) : List (Bundle Payload) :=
  (List.range n).flatMap (L.receivesFrom r s)

theorem addsUpTo_succ (s r : Chain) (n : ℕ) :
    L.addsUpTo s r (n + 1) = L.addsUpTo s r n ++ L.sendsTo s r n := by
  simp [addsUpTo, List.range_succ]

theorem removesUpTo_succ (r s : Chain) (n : ℕ) :
    L.removesUpTo r s (n + 1) = L.removesUpTo r s n ++ L.receivesFrom r s n := by
  simp [removesUpTo, List.range_succ]

/-- A block consumes nothing from a sender absent from its incoming list. -/
theorem receivesFrom_eq_nil {r s : Chain} {h : ℕ} {B : Block Chain Stream Payload}
    (hB : L r h = some B) (hs : ∀ x ∈ B.incoming, x.1 ≠ s) : L.receivesFrom r s h = [] := by
  simp only [receivesFrom, hB, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  simpa using hs x hx

end Ledger

end Linera
