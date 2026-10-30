import Linera.Chain.Event
import Mathlib.Data.Finset.Basic

/-!
# A validator's view of several chains

A validator stores certified blocks of every chain and keeps, per
recipient chain and sender, an inbox fed by its *own* copies of the
sender's blocks (`communication.tex`, Message lifecycle: "the same
validator's worker that processed `B_s` derives `m` from its own persisted
outbox and delivers it to the worker holding `c_r`"). Nothing here involves
another validator: the only shared object is the ledger.

* `executed c`: the recipient prefix of chain `c` the validator has
  executed; executing a block consumes its incoming bundles
  (`remove_bundles_from_inboxes`).
* `preprocessed c`: further heights of `c` whose certified blocks are stored
  without execution (`preprocess_certified_block`); they feed the outbox and
  the event store.
* `delivered s r`: the next height of `s` whose bundles to `r` the
  validator's worker for `s` will push to its worker for `r`
  (`next_height_to_schedule`, `UpdateRecipient`).
* `inboxes r s`: the inbox of `r` for `s`.

`inbox_eq_of_counters` is the cross-validator **inbox consistency**
theorem: two validators that have executed the same prefix of `r` and
delivered the same prefix of `s` to `r` have the same inbox, whatever the
interleaving of executions and deliveries on each. Delivery lags behind the
certificates held (it is an asynchronous internal RPC), so inboxes of
validators holding the same certificates agree only once deliveries have
caught up: that eventual statement belongs to a timed layer.
-/

namespace Linera

variable {Chain Stream Payload : Type*} [DecidableEq Chain] [DecidableEq Payload]

/-- A validator's view of all chains. -/
structure Node (Chain Payload : Type*) where
  /-- The next height to execute, per chain. -/
  executed : Chain → ℕ
  /-- Heights stored without execution, per chain. -/
  preprocessed : Chain → Finset ℕ
  /-- `delivered s r`: the next height of `s` to deliver to `r`. -/
  delivered : Chain → Chain → ℕ
  /-- `inboxes r s`: the inbox of recipient `r` for sender `s`. -/
  inboxes : Chain → Chain → Inbox Payload

namespace Node

/-- Update a binary function at one point. -/
def upd2 {α β γ : Type*} [DecidableEq α] [DecidableEq β] (f : α → β → γ) (a : α) (b : β) (v : γ) :
    α → β → γ :=
  fun a' b' => if a' = a ∧ b' = b then v else f a' b'

theorem upd2_same {α β γ : Type*} [DecidableEq α] [DecidableEq β] (f : α → β → γ) (a : α) (b : β)
    (v : γ) : upd2 f a b v a b = v := by simp [upd2]

theorem upd2_ne {α β γ : Type*} [DecidableEq α] [DecidableEq β] (f : α → β → γ) {a a' : α}
    {b b' : β} (v : γ) (h : ¬ (a' = a ∧ b' = b)) : upd2 f a b v a' b' = f a' b' := by
  simp [upd2, h]

/-- The initial view: nothing executed, stored or delivered. -/
def init : Node Chain Payload := ⟨fun _ => 0, fun _ => ∅, fun _ _ => 0, fun _ _ => Inbox.init⟩

/-- The validator stores the certified block of `c` at height `h`. -/
def Holds (N : Node Chain Payload) (c : Chain) (h : ℕ) : Prop :=
  h < N.executed c ∨ h ∈ N.preprocessed c

instance (N : Node Chain Payload) (c : Chain) (h : ℕ) : Decidable (N.Holds c h) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The heights of `c` the validator stores. -/
def stored (N : Node Chain Payload) (c : Chain) : Set ℕ := {h | N.Holds c h}

variable (L : Ledger Chain Stream Payload)

/-- Execute the next certified block of `c`: consume its incoming bundles
from the inboxes of `c`, sender by sender, in block order. Fails if there
is no such block or a consumption is refused. -/
def execute (N : Node Chain Payload) (c : Chain) : Option (Node Chain Payload) :=
  match L c (N.executed c) with
  | none => none
  | some B =>
    let run := fun s =>
      (N.inboxes c s).run ((L.receivesFrom c s (N.executed c)).map Inbox.Op.remove)
    if B.incoming.all (fun x => (run x.1).isSome) then
      some { N with
        executed := Function.update N.executed c (N.executed c + 1)
        inboxes := fun r s => if r = c then (run s).getD (N.inboxes c s) else N.inboxes r s }
    else none

/-- Store the certified block of `c` at height `h` without executing it. -/
def preprocess (N : Node Chain Payload) (c : Chain) (h : ℕ) : Option (Node Chain Payload) :=
  match L c h with
  | none => none
  | some _ => some { N with
      preprocessed := Function.update N.preprocessed c (insert h (N.preprocessed c)) }

/-- Deliver the bundles of the next stored block of `s` to the inbox of
`r`: the validator's own copy of the sender block feeds the recipient's
inbox. Fails if the block is not stored or a delivery is refused. -/
def deliver (N : Node Chain Payload) (s r : Chain) : Option (Node Chain Payload) :=
  if N.Holds s (N.delivered s r) then
    match (N.inboxes r s).run ((L.sendsTo s r (N.delivered s r)).map Inbox.Op.add) with
    | none => none
    | some I => some { N with
        delivered := upd2 N.delivered s r (N.delivered s r + 1)
        inboxes := upd2 N.inboxes r s I }
  else none

/-- The views reachable from `init` by executions, preprocessings and
deliveries. -/
inductive Reach : Node Chain Payload → Prop
  /-- The initial view. -/
  | init : Reach init
  /-- Execute a block. -/
  | execute {N N' : Node Chain Payload} (h : Reach N) (c : Chain) (hs : execute L N c = some N') :
    Reach N'
  /-- Store a block. -/
  | preprocess {N N' : Node Chain Payload} (h : Reach N) (c : Chain) (k : ℕ)
    (hs : preprocess L N c k = some N') : Reach N'
  /-- Deliver a block's bundles. -/
  | deliver {N N' : Node Chain Payload} (h : Reach N) (s r : Chain)
    (hs : deliver L N s r = some N') : Reach N'

/-- A proposal of chain `c` consuming the bundles of `B` is acceptable at
this validator only if every bundle is present in its inbox
(`remove_bundles_from_inboxes` with `must_be_present`). -/
def Present (N : Node Chain Payload) (c : Chain) (B : Block Chain Stream Payload) : Prop :=
  ∀ x ∈ B.incoming, x.2.1 ∈ (N.inboxes c x.1).added

/-- The events of stream `st` on chain `c` this validator holds. -/
def Held (N : Node Chain Payload) (c : Chain) (st : Stream) (i : ℕ) : Prop :=
  L.Held (N.stored c) c st i

/-! ### The inbox invariant -/

/-- Every inbox is the result of a succeeding run whose delivered bundles
are those of the sender prefix delivered and whose consumed bundles are
those of the recipient prefix executed. -/
def Inv (N : Node Chain Payload) : Prop :=
  ∀ r s, ∃ ops : List (Inbox.Op Payload), Inbox.init.run ops = some (N.inboxes r s) ∧
    Inbox.adds ops = L.addsUpTo s r (N.delivered s r) ∧
    Inbox.removes ops = L.removesUpTo r s (N.executed r)

theorem Inv.init : Inv L (init : Node Chain Payload) := by
  intro r s
  exact ⟨[], rfl, rfl, rfl⟩

theorem Inv.execute {N N' : Node Chain Payload} (hI : Inv L N) {c : Chain}
    (h : execute L N c = some N') : Inv L N' := by
  intro r s
  unfold Node.execute at h
  rcases hB : L c (N.executed c) with _ | B
  · simp [hB] at h
  simp only [hB] at h
  split at h
  · rename_i hall
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨ops, hrun, hadds, hrem⟩ := hI r s
    by_cases hrc : r = c
    · subst hrc
      -- the inbox of `r` for `s` after consuming the block's bundles from `s`
      have hsome : ((N.inboxes r s).run ((L.receivesFrom r s (N.executed r)).map
          Inbox.Op.remove)).isSome := by
        by_cases hmem : ∃ x ∈ B.incoming, x.1 = s
        · obtain ⟨x, hx, rfl⟩ := hmem
          have := List.all_eq_true.1 hall x hx
          simpa using this
        · have hmem' : ∀ x ∈ B.incoming, x.1 ≠ s := fun x hx hxs => hmem ⟨x, hx, hxs⟩
          rw [L.receivesFrom_eq_nil hB hmem']
          simp [Inbox.run]
      obtain ⟨I', hI'⟩ := Option.isSome_iff_exists.1 hsome
      refine ⟨ops ++ (L.receivesFrom r s (N.executed r)).map Inbox.Op.remove, ?_, ?_, ?_⟩
      · simp only [ite_true, hI', Option.getD_some]
        rw [Inbox.run_append, hrun, Option.bind_some, hI']
      · simp [Inbox.adds_append, Inbox.adds_map_remove, hadds]
      · simp [Inbox.removes_append, Inbox.removes_map_remove, hrem, Function.update_self,
          L.removesUpTo_succ]
    · refine ⟨ops, ?_, hadds, ?_⟩
      · dsimp only; simp only [hrc, ↓reduceIte]; exact hrun
      · dsimp only; rw [Function.update_of_ne hrc]; exact hrem
  · exact absurd h (by simp)

theorem Inv.preprocess {N N' : Node Chain Payload} (hI : Inv L N) {c : Chain} {k : ℕ}
    (h : preprocess L N c k = some N') : Inv L N' := by
  unfold Node.preprocess at h
  rcases hB : L c k with _ | B
  · simp [hB] at h
  · simp only [hB, Option.some.injEq] at h
    subst h
    exact hI

theorem Inv.deliver {N N' : Node Chain Payload} (hI : Inv L N) {s r : Chain}
    (h : deliver L N s r = some N') : Inv L N' := by
  intro r' s'
  unfold Node.deliver at h
  split at h
  · rcases hrun : (N.inboxes r s).run ((L.sendsTo s r (N.delivered s r)).map Inbox.Op.add)
      with _ | I
    · simp [hrun] at h
    simp only [hrun, Option.some.injEq] at h
    subst h
    obtain ⟨ops, hrun₀, hadds, hrem⟩ := hI r' s'
    by_cases hrs : r' = r ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hrs
      refine ⟨ops ++ (L.sendsTo s' r' (N.delivered s' r')).map Inbox.Op.add, ?_, ?_, ?_⟩
      · simp only [upd2_same]
        rw [Inbox.run_append, hrun₀, Option.bind_some, hrun]
      · simp [Inbox.adds_append, Inbox.adds_map_add, hadds, upd2_same, L.addsUpTo_succ]
      · simp [Inbox.removes_append, Inbox.removes_map_add, hrem]
    · refine ⟨ops, ?_, ?_, hrem⟩
      · simp [upd2_ne _ _ hrs, hrun₀]
      · simp [upd2_ne _ _ (fun h => hrs ⟨h.2, h.1⟩), hadds]
  · exact absurd h (by simp)

theorem Reach.inv {N : Node Chain Payload} (h : Reach L N) : Inv L N := by
  induction h with
  | init => exact Inv.init L
  | execute _ _ hs ih => exact ih.execute L hs
  | preprocess _ _ _ hs ih => exact ih.preprocess L hs
  | deliver _ _ _ hs ih => exact ih.deliver L hs

/-- Every inbox of a reachable view is in canonical form: determined by the
delivered and executed prefixes. -/
theorem Reach.inboxes_eq {N : Node Chain Payload} (h : Reach L N) (r s : Chain) :
    N.inboxes r s = Inbox.canonical (L.addsUpTo s r (N.delivered s r))
      (L.removesUpTo r s (N.executed r)) := by
  obtain ⟨ops, hrun, hadds, hrem⟩ := h.inv L r s
  rw [Inbox.run_eq_canonical hrun, hadds, hrem]

/-- **Inbox consistency**: two validators that have executed the same
prefix of `r` and delivered the same prefix of `s` to `r` have the same
inbox of `r` for `s`, whatever the order in which each executed and
delivered. -/
theorem inbox_eq_of_counters {N₁ N₂ : Node Chain Payload} (h₁ : Reach L N₁) (h₂ : Reach L N₂)
    {r s : Chain} (he : N₁.executed r = N₂.executed r) (hd : N₁.delivered s r = N₂.delivered s r) :
    N₁.inboxes r s = N₂.inboxes r s := by
  rw [h₁.inboxes_eq, h₂.inboxes_eq, he, hd]

omit [DecidableEq Chain] [DecidableEq Payload] in
/-- The events held only grow. -/
theorem held_mono {N N' : Node Chain Payload}
    (he : ∀ c, N.executed c ≤ N'.executed c) (hp : ∀ c, N.preprocessed c ⊆ N'.preprocessed c)
    {c : Chain} {st : Stream} {i : ℕ} (h : N.Held L c st i) : N'.Held L c st i := by
  refine Ledger.Held.mono L ?_ h
  intro k hk
  rcases hk with hk | hk
  · exact Or.inl (lt_of_lt_of_le hk (he c))
  · exact Or.inr (hp c hk)

end Node

end Linera
