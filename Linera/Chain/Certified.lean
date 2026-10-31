import Linera.Chain.Node
import Linera.Safety.Safety

/-!
# Certified ledgers: no forgery and exactly-once consumption

A validator accepts a proposal consuming bundles only if they are in its
inbox and are consumed in order (`remove_bundles_from_inboxes` with
`must_be_present`); a block is certified only with an honest vote. So
every certified block passed this check at some reachable view of an
honest validator (`Ledger.Accepted`), and from the inbox invariants:

* **no forgery** (`Ledger.no_forgery`): a bundle consumed by a certified
  block was sent by a certified block of its sender;
* **exactly once** (`Ledger.exactly_once`, `Ledger.receivesFrom_nodup`):
  a bundle is consumed by at most one certified block of its recipient,
  and once in it.

`Ledger.accepted_of_confirmed` derives `Accepted` from the per-height
consensus: a confirmed block satisfies the validity predicate
(`confCert_valid`), and the validity predicate of the instance deciding
height `h` of chain `c` implies the cross-chain check at a reachable view
with `c` executed up to `h`. The consensus model has one validity
predicate per instance while the cross-chain check is validator-local;
the weakest global predicate implied by every honest local check,
`fun B => ∃ N, Reach L N ∧ N.executed c = h ∧ N.Accepts c B`, is the
intended instantiation, and only safety is claimed through it.
-/

namespace Linera

variable {Chain Stream Payload : Type*} [DecidableEq Chain] [DecidableEq Payload]

namespace Node

variable (L : Ledger Chain Stream Payload)

/-- The cross-chain validity check of a proposal `B` for chain `c` at a
validator: every consumed bundle is in its inbox, and consuming them,
sender by sender, succeeds. -/
def Accepts (N : Node Chain Payload) (c : Chain) (B : Block Chain Stream Payload) : Prop :=
  N.Present c B ∧ ∀ s, ((N.inboxes c s).run ((B.consumedFrom s).map Inbox.Op.remove)).isSome

/-- A bundle in an inbox was sent by a certified block of the sender. -/
theorem Reach.added_sent {N : Node Chain Payload} (h : Reach L N) {r s : Chain}
    {b : Bundle Payload} (hb : b ∈ (N.inboxes r s).added) :
    ∃ k Bs, L s k = some Bs ∧ (r, b) ∈ Bs.outgoing := by
  rw [h.inboxes_eq L] at hb
  simp only [Inbox.canonical, List.mem_filter] at hb
  obtain ⟨hb, -⟩ := hb
  simp only [Ledger.addsUpTo, List.mem_flatMap, List.mem_range] at hb
  obtain ⟨k, -, hb⟩ := hb
  unfold Ledger.sendsTo at hb
  rcases hB : L s k with _ | Bs
  · simp [hB] at hb
  · simp only [hB, List.mem_map, List.mem_filter, decide_eq_true_eq] at hb
    obtain ⟨x, ⟨hx, hx1⟩, hx2⟩ := hb
    refine ⟨k, Bs, hB, ?_⟩
    have : x = (r, b) := Prod.ext hx1 hx2
    rw [← this]; exact hx

/-- Consuming the bundles of an accepted block continues the sorted
consumption sequence of the chain. -/
theorem Reach.consumed_sorted {N : Node Chain Payload} (h : Reach L N) {c : Chain}
    {B : Block Chain Stream Payload} (hB : N.Accepts c B) (s : Chain) :
    Inbox.Sorted (L.removesUpTo c s (N.executed c) ++ B.consumedFrom s) := by
  obtain ⟨ops, hrun, -, hrem⟩ := h.inv L c s
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (hB.2 s)
  have hsA := Inbox.sorted_adds hrun
  have hsR := Inbox.sorted_removes hrun
  rw [Inbox.run_eq_canonical hrun] at hI
  have := (Inbox.run_sorted _ hsA hsR hI).2
  rwa [Inbox.removes_map_remove, hrem] at this

end Node

namespace Ledger

variable (L : Ledger Chain Stream Payload)

/-- Every block of the ledger passed the cross-chain validity check at a
reachable view of a validator with the chain executed up to its height. -/
def Accepted : Prop :=
  ∀ c h B, L c h = some B →
    ∃ N : Node Chain Payload, Node.Reach L N ∧ N.executed c = h ∧ N.Accepts c B

/-- **No forgery**: a bundle consumed by a certified block was sent by a
certified block of its sender. -/
theorem no_forgery (hA : L.Accepted) {r : Chain} {h : ℕ} {B : Block Chain Stream Payload}
    (hB : L r h = some B) {x : Chain × Bundle Payload × MessageAction} (hx : x ∈ B.incoming) :
    ∃ k Bs, L x.1 k = some Bs ∧ (r, x.2.1) ∈ Bs.outgoing := by
  obtain ⟨N, hN, -, hP, -⟩ := hA r h B hB
  exact hN.added_sent L (hP x hx)

/-- The consumptions of `r` from `s` up to a certified height have
strictly increasing cursors. -/
theorem removesUpTo_sorted (hA : L.Accepted) {r : Chain} {h : ℕ} {B : Block Chain Stream Payload}
    (hB : L r h = some B) (s : Chain) : Inbox.Sorted (L.removesUpTo r s (h + 1)) := by
  obtain ⟨N, hN, he, hAcc⟩ := hA r h B hB
  have := hN.consumed_sorted L hAcc s
  rw [he] at this
  rwa [removesUpTo_succ, receivesFrom_of_some L hB]

/-- A certified block consumes a bundle at most once. -/
theorem receivesFrom_nodup (hA : L.Accepted) {r : Chain} {h : ℕ} {B : Block Chain Stream Payload}
    (hB : L r h = some B) (s : Chain) : (L.receivesFrom r s h).Nodup := by
  have hs := L.removesUpTo_sorted hA hB s
  rw [removesUpTo_succ, Inbox.Sorted, List.pairwise_append] at hs
  exact hs.2.1.imp fun hab heq => by rw [heq] at hab; exact lt_irrefl _ hab

omit [DecidableEq Payload] in
/-- In a sorted consumption sequence, a bundle is consumed at one height only. -/
theorem height_eq_of_sorted {r s : Chain} : ∀ {n : ℕ}, Inbox.Sorted (L.removesUpTo r s n) →
    ∀ {h₁ h₂ : ℕ}, h₁ < h₂ → h₂ < n → ∀ {b : Bundle Payload},
    b ∈ L.receivesFrom r s h₁ → b ∈ L.receivesFrom r s h₂ → False := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro hs h₁ h₂ h₁₂ h₂n b hb₁ hb₂
    rw [removesUpTo_succ, Inbox.Sorted, List.pairwise_append] at hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 h₂n with h₂n | rfl
    · exact ih hs.1 h₁₂ h₂n hb₁ hb₂
    · have hmem : b ∈ L.removesUpTo r s h₂ := by
        simp only [removesUpTo, List.mem_flatMap, List.mem_range]
        exact ⟨h₁, h₁₂, hb₁⟩
      exact lt_irrefl _ (hs.2.2 b hmem b hb₂)

/-- **Exactly once**: a bundle is consumed by at most one certified block
of its recipient. -/
theorem exactly_once (hA : L.Accepted) {r s : Chain} {h₁ h₂ : ℕ}
    {B₁ B₂ : Block Chain Stream Payload} (hB₁ : L r h₁ = some B₁) (hB₂ : L r h₂ = some B₂)
    {b : Bundle Payload} (hb₁ : b ∈ L.receivesFrom r s h₁) (hb₂ : b ∈ L.receivesFrom r s h₂) :
    h₁ = h₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact L.height_eq_of_sorted (L.removesUpTo_sorted hA hB₂ s) hlt (Nat.lt_succ_self _) hb₁ hb₂
  · exact L.height_eq_of_sorted (L.removesUpTo_sorted hA hB₁ s) hlt (Nat.lt_succ_self _) hb₂ hb₁

section Consensus

variable {V Owner : Type*} [Fintype V] [DecidableEq V] [QuorumSystem V] [DecidableEq Owner]
  [DecidableEq (Block Chain Stream Payload)]

/-- **The ledger of a certified chain is accepted**: if every height of
every chain is decided by a consensus instance whose validity predicate
implies the cross-chain check at a reachable view, and the ledger records
only confirmed blocks, then every block of the ledger was accepted. -/
theorem accepted_of_confirmed (cfg : Chain → ℕ → Config Owner (Block Chain Stream Payload))
    (st : Chain → ℕ → State V Owner (Block Chain Stream Payload))
    (hreach : ∀ c h, Reachable (cfg c h) (st c h))
    (hvalid : ∀ c h B, (cfg c h).Valid B →
      ∃ N : Node Chain Payload, Node.Reach L N ∧ N.executed c = h ∧ N.Accepts c B)
    (hconf : ∀ c h B, L c h = some B → ∃ r, (st c h).ConfCert B r) : L.Accepted := by
  intro c h B hB
  obtain ⟨r, hr⟩ := hconf c h B hB
  exact hvalid c h B (confCert_valid (hreach c h) hr)

end Consensus

end Ledger

end Linera
