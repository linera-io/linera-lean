import Linera.Chain.Node

/-!
# Timed runs of a validator and eventual inbox consistency

A validator's cross-chain layer runs on a tick counter, as the consensus
executions do (`Liveness/Timed/Exec.lean`): at each tick at most one
action — an execution, a preprocessing or an internal delivery — is
attempted, and applied if accepted. Deliveries are asynchronous internal
requests (`UpdateRecipient`, retried until `ConfirmUpdatedRecipient`), so
a validator storing a sender block need not have fed the recipient's inbox
yet. The delivery environment bounds this lag after a stabilisation time
`GST`: a stored sender block whose turn has come is delivered within `Δ`
ticks.

The main result, `eventual_inbox_consistency`, is the **eventual inbox
consistency** statement of `communication.tex`: once two validators store
the first `H` blocks of a sender chain, which then stalls at `H` in both
views, their inboxes for that sender agree, at every tick from `H · Δ`
after stabilisation at which they have executed the same prefix of the
recipient.
-/

namespace Linera.Node

variable {Chain Stream Payload : Type*} [DecidableEq Chain] [DecidableEq Payload]
variable (L : Ledger Chain Stream Payload)

/-- One action of a validator's cross-chain layer. -/
inductive Act (Chain : Type*)
  /-- Execute the next block of `c`. -/
  | execute (c : Chain)
  /-- Store the block of `c` at height `h` without executing it. -/
  | preprocess (c : Chain) (h : ℕ)
  /-- Deliver the next bundles of `s` to `r`. -/
  | deliver (s r : Chain)

/-- Apply an action. -/
def apply (N : Node Chain Payload) : Act Chain → Option (Node Chain Payload)
  | .execute c => execute L N c
  | .preprocess c h => preprocess L N c h
  | .deliver s r => deliver L N s r

/-- One tick: the attempted action if accepted, else nothing. -/
def stepOpt (N : Node Chain Payload) : Option (Act Chain) → Node Chain Payload
  | none => N
  | some a => (apply L N a).getD N

/-- A timed run of a validator's cross-chain layer. -/
structure Run where
  /-- The view at each tick. -/
  st : ℕ → Node Chain Payload
  /-- The action attempted at each tick, if any. -/
  act : ℕ → Option (Act Chain)
  /-- The run starts from the initial view. -/
  zero : st 0 = init
  /-- Each tick applies the attempted action, if accepted. -/
  succ : ∀ t, st (t + 1) = stepOpt L (st t) (act t)

/-- The run that attempts a given action at each tick. -/
def Run.ofActs (act : ℕ → Option (Act Chain)) : Run L where
  st := fun t => Nat.rec init (fun t N => stepOpt L N (act t)) t
  act := act
  zero := rfl
  succ := fun _ => rfl

namespace Run

variable {L} (ex : Run L)

/-- Every view of a run is reachable. -/
theorem reach (t : ℕ) : Reach L (ex.st t) := by
  induction t with
  | zero => rw [ex.zero]; exact Reach.init
  | succ t ih =>
    rw [ex.succ]
    rcases ex.act t with _ | a
    · exact ih
    · simp only [stepOpt]
      rcases hap : apply L (ex.st t) a with _ | N'
      · exact ih
      · simp only [Option.getD_some]
        cases a with
        | execute c => exact ih.execute c hap
        | preprocess c h => exact ih.preprocess c h hap
        | deliver s r => exact ih.deliver s r hap

/-- Executed prefixes, stored heights and delivery counters only grow at each tick. -/
theorem mono_succ (t : ℕ) :
    (∀ c, (ex.st t).executed c ≤ (ex.st (t + 1)).executed c) ∧
    (∀ c, (ex.st t).preprocessed c ⊆ (ex.st (t + 1)).preprocessed c) ∧
    (∀ s r, (ex.st t).delivered s r ≤ (ex.st (t + 1)).delivered s r) := by
  rw [ex.succ]
  rcases ex.act t with _ | a
  · exact ⟨fun _ => le_rfl, fun _ => subset_rfl, fun _ _ => le_rfl⟩
  simp only [stepOpt]
  rcases hap : apply L (ex.st t) a with _ | N'
  · exact ⟨fun _ => le_rfl, fun _ => subset_rfl, fun _ _ => le_rfl⟩
  simp only [Option.getD_some]
  cases a with
  | execute c =>
    obtain ⟨he, hp, hd⟩ := execute_spec L hap
    refine ⟨fun c' => ?_, fun c' => by simp [hp], fun s r => by simp [hd]⟩
    rw [he]
    by_cases hc : c' = c
    · subst hc; simp
    · simp [Function.update_of_ne hc]
  | preprocess c k =>
    obtain ⟨he, hp, hd⟩ := preprocess_spec L hap
    refine ⟨fun c' => by simp [he], fun c' => ?_, fun s r => by simp [hd]⟩
    rw [hp]
    by_cases hc : c' = c
    · subst hc; simp [Function.update_self]
    · simp [Function.update_of_ne hc]
  | deliver s r =>
    obtain ⟨_, he, hp, hd⟩ := deliver_spec L hap
    refine ⟨fun c' => by simp [he], fun c' => by simp [hp], fun s' r' => ?_⟩
    rw [hd]
    by_cases hsr : s' = s ∧ r' = r
    · obtain ⟨rfl, rfl⟩ := hsr; rw [upd2_same]; exact Nat.le_succ _
    · rw [upd2_ne _ _ hsr]

/-- Executed prefixes only grow. -/
theorem executed_mono {t t' : ℕ} (h : t ≤ t') (c : Chain) :
    (ex.st t).executed c ≤ (ex.st t').executed c := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih ((ex.mono_succ _).1 c)

/-- Stored heights only grow. -/
theorem preprocessed_mono {t t' : ℕ} (h : t ≤ t') (c : Chain) :
    (ex.st t).preprocessed c ⊆ (ex.st t').preprocessed c := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans ((ex.mono_succ _).2.1 c)

/-- Delivery counters only grow. -/
theorem delivered_mono {t t' : ℕ} (h : t ≤ t') (s r : Chain) :
    (ex.st t).delivered s r ≤ (ex.st t').delivered s r := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih ((ex.mono_succ _).2.2 s r)

/-- A stored block stays stored. -/
theorem holds_mono {t t' : ℕ} (h : t ≤ t') {c : Chain} {k : ℕ} (hk : (ex.st t).Holds c k) :
    (ex.st t').Holds c k :=
  Holds.mono (ex.executed_mono h) (ex.preprocessed_mono h) hk

/-- The delivery environment of a run: after `GST`, a stored sender block
whose turn has come is delivered within `Δ` ticks. -/
structure Env where
  /-- The stabilisation time of the validator's internal delivery. -/
  GST : ℕ
  /-- The delivery delay bound after `GST`. -/
  Δ : ℕ
  /-- A stored sender block whose turn has come is delivered within `Δ`. -/
  deliver : ∀ t, GST ≤ t → ∀ s r, (ex.st t).Holds s ((ex.st t).delivered s r) →
    ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧ (ex.st t).delivered s r < (ex.st t').delivered s r

/-- After `GST`, once the first `H` blocks of `s` are stored, the
deliveries to `r` reach height `H` within `k · Δ` ticks, where `k` bounds
the heights still to deliver. -/
theorem delivered_reaches (env : ex.Env) {s r : Chain} {H : ℕ} :
    ∀ k t, env.GST ≤ t → (∀ h < H, (ex.st t).Holds s h) → H ≤ (ex.st t).delivered s r + k →
    ∃ t', t ≤ t' ∧ t' ≤ t + k * env.Δ ∧ H ≤ (ex.st t').delivered s r := by
  intro k
  induction k with
  | zero => intro t _ _ hk; exact ⟨t, le_rfl, by simp, by simpa using hk⟩
  | succ k ih =>
    intro t ht hH hk
    by_cases hdone : H ≤ (ex.st t).delivered s r
    · exact ⟨t, le_rfl, Nat.le_add_right _ _, hdone⟩
    · have hlt : (ex.st t).delivered s r < H := Nat.lt_of_not_le hdone
      obtain ⟨t₁, ht₁, ht₁', hinc⟩ := env.deliver t ht s r (hH _ hlt)
      obtain ⟨t', htt', ht'', hH'⟩ := ih t₁ (le_trans ht ht₁)
        (fun h hh => ex.holds_mono ht₁ (hH h hh)) (by omega)
      refine ⟨t', le_trans ht₁ htt', ?_, hH'⟩
      rw [Nat.succ_mul]
      omega

/-- Once the first `H` blocks of `s` are stored at a stabilised tick `T`
and the block at `H` never is, the deliveries to `r` stand at exactly `H`
from `T + H · Δ` on. -/
theorem delivered_eq (env : ex.Env) {s r : Chain} {H T : ℕ} (hT : env.GST ≤ T)
    (hbelow : ∀ h < H, (ex.st T).Holds s h) (hstall : ∀ t, T ≤ t → ¬ (ex.st t).Holds s H) :
    ∀ t, T + H * env.Δ ≤ t → (ex.st t).delivered s r = H := by
  intro t ht
  obtain ⟨t', hTt', ht'', hH⟩ := ex.delivered_reaches env H T hT hbelow (by omega)
  have hTt : T ≤ t := le_trans (Nat.le_add_right _ _) ht
  apply le_antisymm
  · by_contra hlt
    exact hstall t hTt ((ex.reach t).holds_below L s r H (Nat.lt_of_not_le hlt))
  · exact le_trans hH (ex.delivered_mono (by omega) s r)

/-- From `T + H · Δ` on, the inbox of `r` for `s` is the canonical inbox of
the `H` stored sender blocks and the executed recipient prefix. -/
theorem inbox_eventually (env : ex.Env) {s r : Chain} {H T : ℕ} (hT : env.GST ≤ T)
    (hbelow : ∀ h < H, (ex.st T).Holds s h) (hstall : ∀ t, T ≤ t → ¬ (ex.st t).Holds s H) :
    ∀ t, T + H * env.Δ ≤ t → (ex.st t).inboxes r s =
      Inbox.canonical (L.addsUpTo s r H) (L.removesUpTo r s ((ex.st t).executed r)) := by
  intro t ht
  rw [(ex.reach t).inboxes_eq L, ex.delivered_eq env hT hbelow hstall t ht]

end Run

/-- **Eventual inbox consistency**: two validators that store the first
`H` blocks of `s` at stabilised ticks `T₁`, `T₂`, and never the block at
`H`, have the same inbox of `r` for `s` at every tick from `T₁ + H · Δ₁`
and `T₂ + H · Δ₂` on at which they have executed the same prefix of `r`,
whatever the interleaving of executions and deliveries on each. -/
theorem eventual_inbox_consistency {ex₁ ex₂ : Run L} (env₁ : ex₁.Env) (env₂ : ex₂.Env)
    {s r : Chain} {H T₁ T₂ : ℕ}
    (hT₁ : env₁.GST ≤ T₁) (hb₁ : ∀ h < H, (ex₁.st T₁).Holds s h)
    (hs₁ : ∀ t, T₁ ≤ t → ¬ (ex₁.st t).Holds s H)
    (hT₂ : env₂.GST ≤ T₂) (hb₂ : ∀ h < H, (ex₂.st T₂).Holds s h)
    (hs₂ : ∀ t, T₂ ≤ t → ¬ (ex₂.st t).Holds s H) :
    ∀ t, T₁ + H * env₁.Δ ≤ t → T₂ + H * env₂.Δ ≤ t →
      (ex₁.st t).executed r = (ex₂.st t).executed r →
      (ex₁.st t).inboxes r s = (ex₂.st t).inboxes r s := by
  intro t h₁ h₂ he
  rw [ex₁.inbox_eventually env₁ hT₁ hb₁ hs₁ t h₁, ex₂.inbox_eventually env₂ hT₂ hb₂ hs₂ t h₂, he]

end Linera.Node
