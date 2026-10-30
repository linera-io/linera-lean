import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.Basic

/-!
# Cross-chain messages: cursors, kinds, bundles

The vocabulary of `communication.tex` (Messages) as the implementation
has it (`linera-chain/src/data_types/mod.rs`, `linera-execution/src/lib.rs`):
a certified sender block at height `h` produces, per recipient, *bundles*
`(h, transaction index, messages)`; each posted message has a kind and a
grant; a bundle is *skippable* iff every message in it is `Simple` or
`Bouncing` with zero grant (`PostedMessage::is_skippable`).

Bundles are ordered by their *cursor* `(height, index)`, lexicographically
(`linera_base::data_types::Cursor`). Payloads are opaque.
-/

namespace Linera

/-- A cursor `(height, transaction index)`, ordered lexicographically. -/
abbrev Cursor := ℕ ×ₗ ℕ

instance : Repr Cursor := ⟨fun c _ => repr (ofLex c)⟩

namespace Cursor

/-- The cursor `(h, i)`. -/
def mk (h i : ℕ) : Cursor := toLex (h, i)

/-- The height of a cursor. -/
def height (c : Cursor) : ℕ := (ofLex c).1

/-- The transaction index of a cursor. -/
def index (c : Cursor) : ℕ := (ofLex c).2

/-- The cursor after `c`: same height, next index (`Cursor::try_add_one`).
Every cursor above `c` is at or above `c.succ`. -/
def succ (c : Cursor) : Cursor := toLex (c.height, c.index + 1)

/-- The least cursor. -/
def zero : Cursor := toLex (0, 0)

theorem lt_iff {a b : Cursor} :
    a < b ↔ a.height < b.height ∨ (a.height = b.height ∧ a.index < b.index) :=
  Prod.Lex.lt_iff

theorem le_iff {a b : Cursor} :
    a ≤ b ↔ a.height < b.height ∨ (a.height = b.height ∧ a.index ≤ b.index) :=
  Prod.Lex.le_iff

/-- `c < d` iff `c.succ ≤ d`. -/
theorem lt_iff_succ_le {c d : Cursor} : c < d ↔ c.succ ≤ d := by
  rw [lt_iff, le_iff]
  simp only [succ, height, index, ofLex_toLex]
  omega

theorem zero_le (c : Cursor) : zero ≤ c := by
  rw [le_iff]; simp only [zero, height, index, ofLex_toLex]; omega

theorem lt_succ_self (c : Cursor) : c < c.succ := lt_iff_succ_le.2 le_rfl

end Cursor

/-- The kind of a posted message (`MessageKind`). -/
inductive MessageKind
  /-- May be skipped or rejected. -/
  | simple
  /-- May be neither skipped nor rejected. -/
  | «protected»
  /-- May be rejected but not skipped; a receipt bounces back on rejection. -/
  | tracked
  /-- The receipt of a rejected tracked message. -/
  | bouncing
  deriving DecidableEq, Repr

/-- A posted message: its kind, whether it carries a non-zero grant, and
an opaque payload. -/
structure Posted (Payload : Type*) where
  /-- The kind. -/
  kind : MessageKind
  /-- Whether the grant is non-zero. -/
  hasGrant : Bool
  /-- The payload. -/
  payload : Payload
  deriving DecidableEq, Repr

/-- A message may be skipped iff it is `Simple` or `Bouncing` with no
grant (`PostedMessage::is_skippable`). -/
def Posted.skippable {Payload : Type*} (m : Posted Payload) : Bool :=
  match m.kind with
  | .«protected» | .tracked => false
  | .simple | .bouncing => !m.hasGrant

/-- A bundle: the messages of one transaction of a certified sender block,
with the block height and the transaction index (`MessageBundle`; the
certificate hash and timestamp are elided). -/
structure Bundle (Payload : Type*) where
  /-- The sender block's height. -/
  height : ℕ
  /-- The index of the sending transaction in the block. -/
  index : ℕ
  /-- The messages. -/
  messages : List (Posted Payload)
  deriving DecidableEq, Repr

namespace Bundle

variable {Payload : Type*}

/-- The cursor `(height, index)`. -/
def cursor (b : Bundle Payload) : Cursor := Cursor.mk b.height b.index

/-- A bundle may be skipped iff every message in it may (`MessageBundle::is_skippable`). -/
def skippable (b : Bundle Payload) : Bool := b.messages.all Posted.skippable

end Bundle

end Linera
