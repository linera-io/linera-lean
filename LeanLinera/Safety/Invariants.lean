import LeanLinera.Protocol

/-!
# The inductive invariant

`VInv cfg s v` collects, for an honest validator `v`, what its local state
and its honest signatures satisfy in every reachable state: the vote flags
reflect the log; votes are cast at or below the current round and at most
once per round; a confirmation vote outside the fast round is backed by a
validation certificate; no validation vote is cast in the fast round; the
lock is the latest confirmation; and every validation vote carries its
ghost justification `ValGhost` — the paper's Lemma lock-validate stated at
the moment of signing. `Inv` is the conjunction over honest validators.

This file defines the invariant and proves it at the initial state and
across steps of *other* validators. `Preservation.lean` proves it across
the acting validator's own handlers.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Block]

open State

/-- The certificate carried by the proposal a vote answered. -/
def Sig.cert (e : Sig V Owner Block) : Option (Block × Round) := e.prop.bind (·.cert)

/-- Ghost justification of an honest validation vote `e` by `v` for `B` in
round `r`: the carried certificate is for `B`, predates `r` and exists; a
lock on another block was released by it; the lock recorded at signing was
a confirmation by `v` from before `r`; and every confirmation by `v` from
before `r` is at or below that lock. -/
structure ValGhost (cfg : Config Owner Block) (s : State V Owner Block) (v : V)
    (e : Sig V Owner Block) (B : Block) (r : Round) : Prop where
  /-- The vote answered a proposal of `B` in `r` by an eligible owner. -/
  prop_elig : ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.Eligible r P.owner
  /-- The carried certificate certifies `B`, predates `r`, and exists. -/
  cert_ok : ∀ c ∈ e.cert, c.1 = B ∧ c.2 < r ∧ s.ValCert c.1 c.2
  /-- A lock on a different block was released by the carried certificate. -/
  unlock : ∀ lk ∈ e.lockAt, lk.1 ≠ B → ∃ c ∈ e.cert, lk.2 ≤ c.2
  /-- The lock at signing was a confirmation by `v` from an earlier round. -/
  lockAt_conf : ∀ lk ∈ e.lockAt, lk.2 < r ∧ s.HSig v (.conf lk.1 lk.2)
  /-- Every confirmation by `v` from before `r` is at or below the lock at signing. -/
  conf_le_lockAt : ∀ B₀ r₀, s.HSig v (.conf B₀ r₀) → r₀ < r → ∃ lk ∈ e.lockAt, r₀ ≤ lk.2

/-- The invariant at one honest validator. -/
structure VInv (cfg : Config Owner Block) (s : State V Owner Block) (v : V) : Prop where
  /-- `votedVal[r]` records a validation vote in `r`. -/
  votedVal_iff : ∀ r, (s.locals v).votedVal r = true ↔ ∃ B, s.HSig v (.val B r)
  /-- `votedConf[r]` records a confirmation vote in `r`. -/
  votedConf_iff : ∀ r, (s.locals v).votedConf r = true ↔ ∃ B, s.HSig v (.conf B r)
  /-- Validation votes are at or below the current round. -/
  val_le_cur : ∀ B r, s.HSig v (.val B r) → r ≤ (s.locals v).cur
  /-- Confirmation votes are at or below the current round. -/
  conf_le_cur : ∀ B r, s.HSig v (.conf B r) → r ≤ (s.locals v).cur
  /-- At most one validation vote per round. -/
  val_unique : ∀ B₁ B₂ r, s.HSig v (.val B₁ r) → s.HSig v (.val B₂ r) → B₁ = B₂
  /-- At most one confirmation vote per round. -/
  conf_unique : ∀ B₁ B₂ r, s.HSig v (.conf B₁ r) → s.HSig v (.conf B₂ r) → B₁ = B₂
  /-- A confirmation vote outside the fast round follows a validation certificate. -/
  conf_valCert : ∀ B r, s.HSig v (.conf B r) → ¬ cfg.IsFast r → s.ValCert B r
  /-- No validation vote in the fast round. -/
  val_not_fast : ∀ B r, s.HSig v (.val B r) → ¬ cfg.IsFast r
  /-- The lock is a confirmation by `v`. -/
  lock_conf : ∀ lk ∈ (s.locals v).lock, s.HSig v (.conf lk.1 lk.2)
  /-- The lock is at or below the current round. -/
  lock_le_cur : ∀ lk ∈ (s.locals v).lock, lk.2 ≤ (s.locals v).cur
  /-- Every confirmation by `v` is at or below the lock. -/
  conf_le_lock : ∀ B r, s.HSig v (.conf B r) → ∃ lk ∈ (s.locals v).lock, r ≤ lk.2
  /-- Every validation vote carries its ghost justification. -/
  val_ghost : ∀ e ∈ s.log, e.signer = v → ∀ B r, e.msg = .val B r → ValGhost cfg s v e B r
  /-- A confirmation vote in the fast round answered a proposal by the super owner. -/
  fast_elig : ∀ e ∈ s.log, e.signer = v → ∀ B r, e.msg = .conf B r → cfg.IsFast r →
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.FastEligible r P.owner
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
  votedVal_iff r := by simp [State.init, Local.init, HSig]
  votedConf_iff r := by simp [State.init, Local.init, HSig]
  val_le_cur B r h := absurd h (HSig_init v _)
  conf_le_cur B r h := absurd h (HSig_init v _)
  val_unique B₁ B₂ r h := absurd h (HSig_init v _)
  conf_unique B₁ B₂ r h := absurd h (HSig_init v _)
  conf_valCert B r h := absurd h (HSig_init v _)
  val_not_fast B r h := absurd h (HSig_init v _)
  lock_conf lk h := by simp [State.init, Local.init] at h
  lock_le_cur lk h := by simp [State.init, Local.init] at h
  conf_le_lock B r h := absurd h (HSig_init v _)
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
  cert_ok c hc := let ⟨h₁, h₂, h₃⟩ := hg.cert_ok c hc; ⟨h₁, h₂, h₃.sign e'⟩
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
  cert_ok c hc := let ⟨h₁, h₂, h₃⟩ := hg.cert_ok c hc; ⟨h₁, h₂, h₃.sign e'⟩
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
  votedVal_iff r := by simp only [locals_sign, HSig_sign_of_ne h]; exact hv.votedVal_iff r
  votedConf_iff r := by simp only [locals_sign, HSig_sign_of_ne h]; exact hv.votedConf_iff r
  val_le_cur B r hs := hv.val_le_cur B r ((HSig_sign_of_ne h _).1 hs)
  conf_le_cur B r hs := hv.conf_le_cur B r ((HSig_sign_of_ne h _).1 hs)
  val_unique B₁ B₂ r h₁ h₂ :=
    hv.val_unique B₁ B₂ r ((HSig_sign_of_ne h _).1 h₁) ((HSig_sign_of_ne h _).1 h₂)
  conf_unique B₁ B₂ r h₁ h₂ :=
    hv.conf_unique B₁ B₂ r ((HSig_sign_of_ne h _).1 h₁) ((HSig_sign_of_ne h _).1 h₂)
  conf_valCert B r hs hf := (hv.conf_valCert B r ((HSig_sign_of_ne h _).1 hs) hf).sign e
  val_not_fast B r hs := hv.val_not_fast B r ((HSig_sign_of_ne h _).1 hs)
  lock_conf lk hlk := (hv.lock_conf lk hlk).sign e
  lock_le_cur := hv.lock_le_cur
  conf_le_lock B r hs := hv.conf_le_lock B r ((HSig_sign_of_ne h _).1 hs)
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
  votedVal_iff r := by rw [locals_set_of_ne _ _ h]; exact hv.votedVal_iff r
  votedConf_iff r := by rw [locals_set_of_ne _ _ h]; exact hv.votedConf_iff r
  val_le_cur B r hs := by rw [locals_set_of_ne _ _ h]; exact hv.val_le_cur B r hs
  conf_le_cur B r hs := by rw [locals_set_of_ne _ _ h]; exact hv.conf_le_cur B r hs
  val_unique := hv.val_unique
  conf_unique := hv.conf_unique
  conf_valCert := hv.conf_valCert
  val_not_fast := hv.val_not_fast
  lock_conf lk hlk := by rw [locals_set_of_ne _ _ h] at hlk; exact hv.lock_conf lk hlk
  lock_le_cur lk hlk := by rw [locals_set_of_ne _ _ h] at hlk ⊢; exact hv.lock_le_cur lk hlk
  conf_le_lock B r hs := by rw [locals_set_of_ne _ _ h]; exact hv.conf_le_lock B r hs
  val_ghost e he hs B r hm := (hv.val_ghost e he hs B r hm).set w l
  fast_elig := hv.fast_elig
  finalized_cert B hf := by rw [locals_set_of_ne _ _ h] at hf; exact hv.finalized_cert B hf

end LeanLinera
