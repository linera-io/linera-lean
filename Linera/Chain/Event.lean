import Linera.Chain.Block

/-!
# Events and streams

`communication.tex` (Events): a stream `(c, app, name)` is an append-only
log on the publisher chain `c`; the events emitted by a certified block get
contiguous indices continuing the stream. A validator *holds* an event once
it has stored the certified block that emitted it (execution or
preprocessing: `chain_worker/state.rs`, `write_events`). A subscriber block
runs `UpdateStream(publisher, stream, next)`, valid at a validator iff the
application is subscribed with a recorded index below `next` and the
validator holds event `next − 1` (`linera-execution/src/system.rs`,
`UpdateStream`, `EventsNotFound`).

Stream identifiers are a type parameter; the application that owns a
stream is part of its identifier, and subscriptions are keyed by the
subscribing application.
-/

namespace Linera

namespace Ledger

variable {Chain Stream Payload : Type*}
variable (L : Ledger Chain Stream Payload)

/-- The events emitted by chain `c` to stream `st` at height `h`. -/
def eventsAt (c : Chain) (st : Stream) (h : ℕ) : List Payload :=
  match L c h with
  | some B => B.events st
  | none => []

/-- The number of events of stream `st` on chain `c` in heights below `h`:
the index of the first event emitted at height `h`. -/
def countBefore (c : Chain) (st : Stream) : ℕ → ℕ
  | 0 => 0
  | h + 1 => countBefore c st h + (L.eventsAt c st h).length

theorem countBefore_mono (c : Chain) (st : Stream) {h h' : ℕ} (hle : h ≤ h') :
    L.countBefore c st h ≤ L.countBefore c st h' := by
  induction hle with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

/-- The event of index `i` of stream `st`, if emitted at height `h`. -/
def eventIn (c : Chain) (st : Stream) (h i : ℕ) : Option Payload :=
  (L.eventsAt c st h)[i - L.countBefore c st h]?

/-- Height `h` emits event `i` of stream `st`. -/
def EmitsAt (c : Chain) (st : Stream) (h i : ℕ) : Prop :=
  L.countBefore c st h ≤ i ∧ i < L.countBefore c st (h + 1)

/-- Each index is emitted at one height: the index ranges of distinct heights
are disjoint. -/
theorem EmitsAt.unique {c : Chain} {st : Stream} {h₁ h₂ i : ℕ}
    (h₁e : L.EmitsAt c st h₁ i) (h₂e : L.EmitsAt c st h₂ i) : h₁ = h₂ := by
  obtain ⟨a₁, b₁⟩ := h₁e
  obtain ⟨a₂, b₂⟩ := h₂e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := L.countBefore_mono c st (by omega : h₁ + 1 ≤ h₂)
    omega
  · have := L.countBefore_mono c st (by omega : h₂ + 1 ≤ h₁)
    omega

/-- An emitted index has a payload. -/
theorem EmitsAt.eventIn_isSome {c : Chain} {st : Stream} {h i : ℕ}
    (he : L.EmitsAt c st h i) : (L.eventIn c st h i).isSome := by
  simp only [eventIn, isSome_getElem?]
  simp only [EmitsAt, countBefore] at he
  omega

/-- A validator that has stored the blocks at heights `S` of chain `c`
holds event `i` of stream `st` iff one of them emitted it. -/
def Held (S : Set ℕ) (c : Chain) (st : Stream) (i : ℕ) : Prop :=
  ∃ h ∈ S, L.EmitsAt c st h i

theorem Held.mono {S S' : Set ℕ} (hS : S ⊆ S') {c : Chain} {st : Stream} {i : ℕ}
    (h : L.Held S c st i) : L.Held S' c st i :=
  let ⟨h, hS', he⟩ := h; ⟨h, hS hS', he⟩

/-- The payload of a held event, by its emitting height. -/
noncomputable def Held.payload {S : Set ℕ} {c : Chain} {st : Stream} {i : ℕ}
    (h : L.Held S c st i) : Payload :=
  Option.get _ (EmitsAt.eventIn_isSome L h.choose_spec.2)

/-- **Event consistency**: two validators that both hold event `i` of a
stream, whatever blocks each has stored, hold the same payload. -/
theorem Held.payload_eq {S S' : Set ℕ} {c : Chain} {st : Stream} {i : ℕ}
    (h : L.Held S c st i) (h' : L.Held S' c st i) : h.payload = h'.payload := by
  have heq : h.choose = h'.choose := EmitsAt.unique L h.choose_spec.2 h'.choose_spec.2
  have key : ∀ (h₁ h₂ : ℕ) (e₁ : (L.eventIn c st h₁ i).isSome) (e₂ : (L.eventIn c st h₂ i).isSome),
      h₁ = h₂ → Option.get _ e₁ = Option.get _ e₂ := by
    rintro h₁ h₂ e₁ e₂ rfl; rfl
  exact key _ _ _ _ heq

end Ledger

/-- A stream update `UpdateStream(publisher, stream, next)` run by application
`app` of the subscriber. -/
structure StreamUpdate (Chain Stream App : Type*) where
  /-- The publisher chain. -/
  publisher : Chain
  /-- The stream. -/
  stream : Stream
  /-- The subscribing application. -/
  app : App
  /-- The index after the last event processed by this update. -/
  next : ℕ

namespace StreamUpdate

variable {Chain Stream App : Type*}

/-- The update is valid at a validator holding `held` whose subscriber chain
records `subs` (the next index per subscription): the application is
subscribed with a recorded index below `next`, and the validator holds
event `next − 1`. -/
def Ok (held : Chain → Stream → ℕ → Prop) (subs : Chain → Stream → App → Option ℕ)
    (u : StreamUpdate Chain Stream App) : Prop :=
  ∃ i, subs u.publisher u.stream u.app = some i ∧ i < u.next ∧
    held u.publisher u.stream (u.next - 1)

/-- Validity only grows with the events held. -/
theorem Ok.mono {held held' : Chain → Stream → ℕ → Prop}
    (hh : ∀ c st i, held c st i → held' c st i) {subs : Chain → Stream → App → Option ℕ}
    {u : StreamUpdate Chain Stream App} (h : Ok held subs u) : Ok held' subs u :=
  let ⟨i, hs, hi, hd⟩ := h; ⟨i, hs, hi, hh _ _ _ hd⟩

end StreamUpdate

end Linera
