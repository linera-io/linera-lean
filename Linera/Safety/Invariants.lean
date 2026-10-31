import Linera.Protocol

/-!
# The inductive invariant

`VInv cfg s v` collects, for an honest validator `v`, what its local state
and its honest signatures satisfy in every reachable state: every
validation vote is bounded by the latest validation vote or the locking
block, and every confirmation by the locking block (so votes are cast in
increasing rounds and at most once per round); votes are at or below the
current round; a confirmation outside the fast round is backed by a
validation certificate; no validation vote is cast in the fast round; the
lock is the latest confirmation; the locking block, when a certificate, is
one; and every validation vote carries its ghost justification `ValGhost`
— the paper's Lemma lock-validate stated at the moment of signing. `Inv`
is the conjunction over honest validators.

This file defines the invariant and proves it at the initial state and
across steps of *other* validators. `Preservation.lean` proves it across
the acting validator's own handlers.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Block]

open State

/-- The justification of the proposal a vote answered. -/
def Sig.just (e : Sig V Owner Block) : Just Block :=
  match e.prop with
  | some P => P.just
  | none => .none

/-- Ghost justification of an honest validation vote `e` by `v` for `B` in
round `r`: it answered an eligible proposal; a carried certificate is for
`B`, predates `r` and exists; a lock on another block was released by a
certificate from a strictly later round; the lock recorded at signing was
a confirmation by `v` from before `r`; and every confirmation by `v` from
before `r` is at or below that lock. -/
structure ValGhost (cfg : Config Owner Block) (s : State V Owner Block) (v : V)
    (e : Sig V Owner Block) (B : Block) (r : Round) : Prop where
  /-- The vote answered a valid proposal of `B` in `r` by an eligible owner. -/
  prop_elig : ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.Eligible r P.owner ∧
    cfg.Valid P.block
  /-- A carried certificate certifies `B`, predates `r`, and exists. -/
  cert_ok : ∀ B' ρ, e.just = .cert B' ρ → B' = B ∧ ρ < r ∧ s.ValCert B' ρ
  /-- A lock on a different block was released by a strictly later certificate. -/
  unlock : ∀ lk ∈ e.lockAt, lk.1 ≠ B → ∃ ρ, e.just = .cert B ρ ∧ lk.2 < ρ
  /-- The lock at signing was a confirmation by `v` from an earlier round. -/
  lockAt_conf : ∀ lk ∈ e.lockAt, lk.2 < r ∧ s.HSig v (.conf lk.1 lk.2)
  /-- Every confirmation by `v` from before `r` is at or below the lock at signing. -/
  conf_le_lockAt : ∀ B₀ r₀, s.HSig v (.conf B₀ r₀) → r₀ < r → ∃ lk ∈ e.lockAt, r₀ ≤ lk.2

/-- The invariant at one honest validator. -/
structure VInv (cfg : Config Owner Block) (s : State V Owner Block) (v : V) : Prop where
  /-- Every validation vote is at or below the latest validation vote or the locking block. -/
  val_bound : ∀ B ρ, s.HSig v (.val B ρ) →
    (∃ vv ∈ (s.locals v).valVote, ρ ≤ vv.2) ∨ (∃ lb ∈ (s.locals v).lb, ρ ≤ lb.round)
  /-- Every confirmation vote is at or below the locking block. -/
  conf_bound : ∀ B ρ, s.HSig v (.conf B ρ) → ∃ lb ∈ (s.locals v).lb, ρ ≤ lb.round
  /-- Validation votes are at or below the current round. -/
  val_le_cur : ∀ B ρ, s.HSig v (.val B ρ) → ρ ≤ (s.locals v).cur
  /-- Confirmation votes are at or below the current round. -/
  conf_le_cur : ∀ B ρ, s.HSig v (.conf B ρ) → ρ ≤ (s.locals v).cur
  /-- Timeout votes are at or below the current round. -/
  time_le_cur : ∀ ρ, s.HSig v (.time ρ) → ρ ≤ (s.locals v).cur
  /-- The latest validation vote was signed. -/
  valVote_sig : ∀ vv ∈ (s.locals v).valVote, s.HSig v (.val vv.1 vv.2)
  /-- The latest timeout vote was signed. -/
  timeoutVote_sig : ∀ τ ∈ (s.locals v).timeoutVote, s.HSig v (.time τ)
  /-- A recorded timeout certificate is below the current round. -/
  tc_lt_cur : ∀ τ ∈ (s.locals v).tc, τ < (s.locals v).cur
  /-- At most one validation vote per round. -/
  val_unique : ∀ B₁ B₂ ρ, s.HSig v (.val B₁ ρ) → s.HSig v (.val B₂ ρ) → B₁ = B₂
  /-- At most one confirmation vote per round. -/
  conf_unique : ∀ B₁ B₂ ρ, s.HSig v (.conf B₁ ρ) → s.HSig v (.conf B₂ ρ) → B₁ = B₂
  /-- A confirmation vote outside the fast round follows a validation certificate. -/
  conf_valCert : ∀ B ρ, s.HSig v (.conf B ρ) → ¬ cfg.IsFast ρ → s.ValCert B ρ
  /-- No validation vote in the fast round. -/
  val_not_fast : ∀ B ρ, s.HSig v (.val B ρ) → ¬ cfg.IsFast ρ
  /-- The lock is a confirmation by `v`. -/
  lock_conf : ∀ lk ∈ (s.locals v).lock, s.HSig v (.conf lk.1 lk.2)
  /-- Every confirmation by `v` is at or below the lock. -/
  conf_le_lock : ∀ B ρ, s.HSig v (.conf B ρ) → ∃ lk ∈ (s.locals v).lock, ρ ≤ lk.2
  /-- A locking block that is a certificate exists. -/
  lb_cert : ∀ B ρ, (s.locals v).lb = some (.cert B ρ) → s.ValCert B ρ
  /-- With a fast-round proposal as locking block, the lock, if any, is on its block. -/
  lock_fast : ∀ lk ∈ (s.locals v).lock, ∀ B', (s.locals v).lb = some (.fast B') → lk.1 = B'
  /-- Every validation vote carries its ghost justification. -/
  val_ghost : ∀ e ∈ s.log, e.signer = v → ∀ B r, e.msg = .val B r → ValGhost cfg s v e B r
  /-- A confirmation vote in the fast round answered a valid proposal by the super owner. -/
  fast_elig : ∀ e ∈ s.log, e.signer = v → ∀ B r, e.msg = .conf B r → cfg.IsFast r →
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.FastEligible r P.owner ∧
      cfg.Valid P.block
  /-- A finalized block has a confirmation certificate. -/
  finalized_cert : ∀ B, (s.locals v).finalized = some B → ∃ r, s.ConfCert B r

/-- The invariant at every honest validator. -/
def Inv (cfg : Config Owner Block) (s : State V Owner Block) : Prop :=
  ∀ v ∈ Q.honest, VInv cfg s v

/-! ## The initial state -/

omit [Fintype V] [DecidableEq V] Q [DecidableEq Block] in
@[simp] theorem HSig_init (v : V) (m : Msg Block) :
    ¬ (State.init : State V Owner Block).HSig v m := by
  simp [HSig, State.init]

theorem VInv.init (cfg : Config Owner Block) (v : V) :
    VInv cfg (State.init : State V Owner Block) v where
  val_bound B ρ h := absurd h (HSig_init v _)
  conf_bound B ρ h := absurd h (HSig_init v _)
  val_le_cur B ρ h := absurd h (HSig_init v _)
  conf_le_cur B ρ h := absurd h (HSig_init v _)
  time_le_cur ρ h := absurd h (HSig_init v _)
  valVote_sig vv h := by simp [State.init, Local.init] at h
  timeoutVote_sig τ h := by simp [State.init, Local.init] at h
  tc_lt_cur τ h := by simp [State.init, Local.init] at h
  val_unique B₁ B₂ ρ h := absurd h (HSig_init v _)
  conf_unique B₁ B₂ ρ h := absurd h (HSig_init v _)
  conf_valCert B ρ h := absurd h (HSig_init v _)
  val_not_fast B ρ h := absurd h (HSig_init v _)
  lock_conf lk h := by simp [State.init, Local.init] at h
  conf_le_lock B ρ h := absurd h (HSig_init v _)
  lb_cert B ρ h := by simp [State.init, Local.init] at h
  lock_fast lk h := by simp [State.init, Local.init] at h
  val_ghost e he := by simp [State.init] at he
  fast_elig e he := by simp [State.init] at he
  finalized_cert B h := by simp [State.init, Local.init] at h

theorem Inv.init (cfg : Config Owner Block) : Inv cfg (State.init : State V Owner Block) :=
  fun v _ => VInv.init cfg v

/-! ## Frame lemmas: steps of another validator -/

omit [Fintype V] [DecidableEq V] Q [DecidableEq Block] in
/-- A signature by someone else does not change `v`'s signatures. -/
theorem HSig_sign_of_ne {s : State V Owner Block} {e : Sig V Owner Block} {v : V}
    (h : e.signer ≠ v) (m : Msg Block) : (s.sign e).HSig v m ↔ s.HSig v m := by
  rw [HSig_sign]
  constructor
  · rintro (h' | ⟨h', _⟩)
    · exact h'
    · exact absurd h' h
  · exact Or.inl

omit [Fintype V] [DecidableEq V] Q [DecidableEq Block] in
/-- A signature on another message does not change `v`'s signatures on `m`. -/
theorem HSig_sign_of_msg_ne {s : State V Owner Block} {e : Sig V Owner Block} {v : V}
    {m : Msg Block} (h : e.msg ≠ m) : (s.sign e).HSig v m ↔ s.HSig v m := by
  rw [HSig_sign]
  constructor
  · rintro (h' | ⟨_, h'⟩)
    · exact h'
    · exact absurd h' h
  · exact Or.inl

omit [Fintype V] [DecidableEq V] Q [DecidableEq Block] in
/-- The signer of a new entry has signed it. -/
theorem HSig_sign_self (s : State V Owner Block) (e : Sig V Owner Block) :
    (s.sign e).HSig e.signer e.msg := (HSig_sign s e _ _).2 (Or.inr ⟨rfl, rfl⟩)

/-- The ghost justification of a vote in `r` persists under any signature
whose confirmation round, if any, is at least `r`. -/
theorem ValGhost.sign {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {e e' : Sig V Owner Block} {B : Block} {r : Round} (hg : ValGhost cfg s v e B r)
    (h : ∀ B₀ r₀, e'.msg = .conf B₀ r₀ → r ≤ r₀) : ValGhost cfg (s.sign e') v e B r where
  prop_elig := hg.prop_elig
  cert_ok B' ρ hc := let ⟨h₁, h₂, h₃⟩ := hg.cert_ok B' ρ hc; ⟨h₁, h₂, h₃.sign e'⟩
  unlock := hg.unlock
  lockAt_conf lk hlk := let ⟨h₁, h₂⟩ := hg.lockAt_conf lk hlk; ⟨h₁, h₂.sign e'⟩
  conf_le_lockAt B₀ r₀ hc hr := by
    rcases (HSig_sign s e' v _).1 hc with hc | ⟨_, hm⟩
    · exact hg.conf_le_lockAt B₀ r₀ hc hr
    · exact absurd hr (not_lt.2 (h B₀ r₀ hm))

/-- The ghost justification persists under a signature by someone else. -/
theorem ValGhost.sign_of_ne {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {e e' : Sig V Owner Block} {B : Block} {r : Round} (hg : ValGhost cfg s v e B r)
    (h : e'.signer ≠ v) : ValGhost cfg (s.sign e') v e B r where
  prop_elig := hg.prop_elig
  cert_ok B' ρ hc := let ⟨h₁, h₂, h₃⟩ := hg.cert_ok B' ρ hc; ⟨h₁, h₂, h₃.sign e'⟩
  unlock := hg.unlock
  lockAt_conf lk hlk := let ⟨h₁, h₂⟩ := hg.lockAt_conf lk hlk; ⟨h₁, h₂.sign e'⟩
  conf_le_lockAt B₀ r₀ hc := hg.conf_le_lockAt B₀ r₀ ((HSig_sign_of_ne h _).1 hc)

/-- The ghost justification does not depend on local states. -/
theorem ValGhost.set {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {e : Sig V Owner Block} {B : Block} {r : Round} (hg : ValGhost cfg s v e B r) (w : V)
    (l : Local Block) : ValGhost cfg (s.set w l) v e B r where
  prop_elig := hg.prop_elig
  cert_ok := hg.cert_ok
  unlock := hg.unlock
  lockAt_conf := hg.lockAt_conf
  conf_le_lockAt := hg.conf_le_lockAt

/-- The invariant at `v` persists under a signature by someone else. -/
theorem VInv.sign_of_ne {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {e : Sig V Owner Block} (h : e.signer ≠ v) : VInv cfg (s.sign e) v where
  val_bound B ρ hs := by
    simp only [locals_sign]; exact hv.val_bound B ρ ((HSig_sign_of_ne h _).1 hs)
  conf_bound B ρ hs := by
    simp only [locals_sign]; exact hv.conf_bound B ρ ((HSig_sign_of_ne h _).1 hs)
  val_le_cur B ρ hs := hv.val_le_cur B ρ ((HSig_sign_of_ne h _).1 hs)
  conf_le_cur B ρ hs := hv.conf_le_cur B ρ ((HSig_sign_of_ne h _).1 hs)
  time_le_cur ρ hs := hv.time_le_cur ρ ((HSig_sign_of_ne h _).1 hs)
  valVote_sig vv hvv := (hv.valVote_sig vv hvv).sign e
  timeoutVote_sig τ hτ := (hv.timeoutVote_sig τ hτ).sign e
  tc_lt_cur := hv.tc_lt_cur
  val_unique B₁ B₂ ρ h₁ h₂ :=
    hv.val_unique B₁ B₂ ρ ((HSig_sign_of_ne h _).1 h₁) ((HSig_sign_of_ne h _).1 h₂)
  conf_unique B₁ B₂ ρ h₁ h₂ :=
    hv.conf_unique B₁ B₂ ρ ((HSig_sign_of_ne h _).1 h₁) ((HSig_sign_of_ne h _).1 h₂)
  conf_valCert B ρ hs hf := (hv.conf_valCert B ρ ((HSig_sign_of_ne h _).1 hs) hf).sign e
  val_not_fast B ρ hs := hv.val_not_fast B ρ ((HSig_sign_of_ne h _).1 hs)
  lock_conf lk hlk := (hv.lock_conf lk hlk).sign e
  conf_le_lock B ρ hs := hv.conf_le_lock B ρ ((HSig_sign_of_ne h _).1 hs)
  lb_cert B ρ hl := (hv.lb_cert B ρ hl).sign e
  lock_fast := hv.lock_fast
  val_ghost e' he' hs B r hm := by
    simp only [log_sign, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact (hv.val_ghost e' he' hs B r hm).sign_of_ne h
    · exact absurd hs h
  fast_elig e' he' hs B r hm hf := by
    simp only [log_sign, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hv.fast_elig e' he' hs B r hm hf
    · exact absurd hs h
  finalized_cert B hf := let ⟨r, hr⟩ := hv.finalized_cert B hf; ⟨r, hr.sign e⟩

/-- The invariant at `v` persists under a local update of someone else. -/
theorem VInv.set_of_ne {cfg : Config Owner Block} {s : State V Owner Block} {v w : V}
    (hv : VInv cfg s v) (h : v ≠ w) (l : Local Block) : VInv cfg (s.set w l) v where
  val_bound B ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.val_bound B ρ hs
  conf_bound B ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.conf_bound B ρ hs
  val_le_cur B ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.val_le_cur B ρ hs
  conf_le_cur B ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.conf_le_cur B ρ hs
  time_le_cur ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.time_le_cur ρ hs
  valVote_sig vv hvv := by rw [locals_set_of_ne _ _ h] at hvv; exact hv.valVote_sig vv hvv
  timeoutVote_sig τ hτ := by rw [locals_set_of_ne _ _ h] at hτ; exact hv.timeoutVote_sig τ hτ
  tc_lt_cur τ hτ := by rw [locals_set_of_ne _ _ h] at hτ ⊢; exact hv.tc_lt_cur τ hτ
  val_unique := hv.val_unique
  conf_unique := hv.conf_unique
  conf_valCert := hv.conf_valCert
  val_not_fast := hv.val_not_fast
  lock_conf lk hlk := by rw [locals_set_of_ne _ _ h] at hlk; exact hv.lock_conf lk hlk
  conf_le_lock B ρ hs := by rw [locals_set_of_ne _ _ h]; exact hv.conf_le_lock B ρ hs
  lb_cert B ρ hl := by rw [locals_set_of_ne _ _ h] at hl; exact hv.lb_cert B ρ hl
  lock_fast lk hlk B' hl := by
    rw [locals_set_of_ne _ _ h] at hlk hl; exact hv.lock_fast lk hlk B' hl
  val_ghost e he hs B r hm := (hv.val_ghost e he hs B r hm).set w l
  fast_elig := hv.fast_elig
  finalized_cert B hf := by rw [locals_set_of_ne _ _ h] at hf; exact hv.finalized_cert B hf

end Linera
