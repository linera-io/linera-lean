import Linera.Chain.Inbox

/-!
# Inbox witnesses

The scenarios of `linera-chain/src/unit_tests/inbox_tests.rs`, replayed on
the Lean inbox by `decide`. Payloads are naturals; the certificate hash is
elided, so the "non-matching hash" assertions have no counterpart.
-/

namespace LineraTest

open Linera Linera.Inbox

/-- A skippable bundle with one `Simple` message. -/
def sk (h i x : ℕ) : Bundle ℕ := ⟨h, i, [⟨.simple, false, x⟩]⟩

/-- An unskippable bundle with one `Protected` message. -/
def un (h i x : ℕ) : Bundle ℕ := ⟨h, i, [⟨.«protected», false, x⟩]⟩

/-- Apply a script: an operation marked `true` must succeed, one marked
`false` must fail and leave the inbox unchanged. -/
def script (I : Inbox ℕ) : List (Op ℕ × Bool) → Option (Inbox ℕ)
  | [] => some I
  | (op, true) :: rest => (I.step op).bind (script · rest)
  | (op, false) :: rest => match I.step op with | none => script I rest | some _ => none

/-- The inbox has both queues empty. -/
def empty (I : Inbox ℕ) : Prop := I.added = [] ∧ I.removed = []

instance : DecidablePred empty := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A script succeeds and ends with both queues empty. -/
def endsEmpty (ops : List (Op ℕ × Bool)) : Bool :=
  match script init ops with
  | some I => decide (empty I)
  | none => false

/-- `test_inbox_add_then_remove_skippable`. -/
theorem add_then_remove_skippable : endsEmpty
    [(.add (sk 0 0 0), true), (.remove (sk 0 0 0), true),
     (.add (sk 0 0 0), false), (.remove (sk 0 0 0), false),
     (.add (sk 0 1 1), true), (.add (sk 1 0 2), true),
     (.remove (sk 0 1 0), false),
     (.remove (sk 1 0 2), true)] = true := by decide

/-- `test_inbox_remove_then_add_skippable`. -/
theorem remove_then_add_skippable : endsEmpty
    [(.remove (sk 0 0 0), true), (.add (sk 0 0 0), true),
     (.remove (sk 0 0 0), false), (.add (sk 0 0 0), false),
     (.remove (sk 0 1 1), true), (.remove (sk 1 1 3), true),
     (.add (sk 0 1 0), false),
     (.add (sk 1 0 2), false),
     (.add (sk 0 1 1), true),
     (.add (un 1 0 2), false),
     (.add (sk 1 0 2), true), (.add (sk 1 1 3), true)] = true := by decide

/-- `test_inbox_add_then_remove_unskippable`. -/
theorem add_then_remove_unskippable : endsEmpty
    [(.add (un 0 0 0), true), (.remove (un 0 0 0), true),
     (.add (un 0 0 0), false), (.remove (un 0 0 0), false),
     (.add (un 0 1 1), true), (.add (un 1 0 2), true),
     (.remove (un 0 1 0), false),
     (.remove (un 1 0 2), false),
     (.remove (un 0 1 1), true), (.remove (un 1 0 2), true)] = true := by decide

/-- `test_inbox_remove_then_add_unskippable`. -/
theorem remove_then_add_unskippable : endsEmpty
    [(.remove (un 0 0 0), true), (.add (un 0 0 0), true),
     (.remove (un 0 0 0), false), (.add (un 0 0 0), false),
     (.remove (un 0 1 1), true), (.remove (un 1 1 3), true),
     (.add (un 0 1 0), false),
     (.add (un 1 1 3), false),
     (.add (un 0 1 1), true),
     (.add (un 1 0 2), false),
     (.add (un 1 1 3), true)] = true := by decide

/-- `test_inbox_add_then_remove_mixed` (first part). -/
theorem add_then_remove_mixed : endsEmpty
    [(.add (un 0 1 1), true), (.add (sk 1 0 2), true),
     (.remove (sk 0 1 1), false),
     (.remove (sk 1 0 2), false),
     (.remove (un 0 1 1), true), (.remove (sk 1 0 2), true)] = true := by decide

/-- Order-independence on a concrete pair of interleavings: delivering
`b₀, b₁` then consuming `b₁` gives the same inbox as consuming `b₁` by
anticipation then delivering `b₀, b₁`, when `b₀` is skippable. -/
theorem interleavings_agree :
    run init [.add (sk 0 0 0), .add (sk 0 1 1), .remove (sk 0 1 1)] =
      run init [.remove (sk 0 1 1), .add (sk 0 0 0), .add (sk 0 1 1)] := by decide

end LineraTest
