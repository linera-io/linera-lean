import Linera.Validator
import Mathlib.Logic.Relation

/-!
# The per-height protocol as a transition system

The global state is the local state of every validator together with the
log of honest signatures. Signatures are unforgeable, so a Byzantine
validator's signature on any message is available at any time, while an
honest one exists only if a handler produced it; `Signed` says exactly
this, and a certificate `HasCert s m` is a quorum of signers of `m`. A
certificate is never a datum: a handler that receives one is a step whose
precondition is that the certificate exists. The log grows only, so
certificates persist (`HasCert.mono`).

Each honest signature carries two ghost fields, the signer's lock and the
proposal answered, so that the paper's arguments about "the moment of
signing" become invariants of the current state.

Steps are taken by honest validators only; Byzantine ones need none. The
untimed model lets a timeout be signed at any moment, so it includes every
behaviour of the timed protocol and the safety theorems carry over.
-/

namespace Linera

variable {V Owner Block : Type*}

/-- An honest signature with its ghost justification. -/
structure Sig (V Owner Block : Type*) where
  /-- The signer. -/
  signer : V
  /-- The signed message. -/
  msg : Msg Block
  /-- Ghost: the signer's lock when it signed. -/
  lockAt : Option (Block × Round)
  /-- Ghost: the proposal this vote answered, for validation and fast votes. -/
  prop : Option (Proposal Owner Block)
  deriving DecidableEq

/-- The global state of one height. -/
structure State (V Owner Block : Type*) where
  /-- Every validator's local state. -/
  locals : V → Local Block
  /-- The honest signatures, in order of signing. -/
  log : List (Sig V Owner Block)

namespace State

/-- The initial state: every validator at round `0`, nothing signed. -/
def init : State V Owner Block := ⟨fun _ => Local.init, []⟩

/-- Replace one validator's local state. -/
def set [DecidableEq V] (s : State V Owner Block) (v : V) (l : Local Block) :
    State V Owner Block :=
  { s with locals := Function.update s.locals v l }

/-- Append a signature. -/
def sign (s : State V Owner Block) (e : Sig V Owner Block) : State V Owner Block :=
  { s with log := s.log ++ [e] }

/-- An honest signature of `v` on `m` is in the log. -/
def HSig (s : State V Owner Block) (v : V) (m : Msg Block) : Prop :=
  ∃ e ∈ s.log, e.signer = v ∧ e.msg = m

/-! ### Basic lemmas -/

section Basic

variable [DecidableEq V]

@[simp] theorem locals_set_self (s : State V Owner Block) (v : V) (l : Local Block) :
    (s.set v l).locals v = l := by simp [set]

@[simp] theorem locals_set_of_ne (s : State V Owner Block) {v w : V} (l : Local Block)
    (h : w ≠ v) : (s.set v l).locals w = s.locals w := by simp [set, h]

@[simp] theorem log_set (s : State V Owner Block) (v : V) (l : Local Block) :
    (s.set v l).log = s.log := rfl

theorem HSig_set (s : State V Owner Block) (w : V) (l : Local Block) (v : V) (m : Msg Block) :
    (s.set w l).HSig v m ↔ s.HSig v m := Iff.rfl

end Basic

@[simp] theorem log_sign (s : State V Owner Block) (e : Sig V Owner Block) :
    (s.sign e).log = s.log ++ [e] := rfl

@[simp] theorem locals_sign (s : State V Owner Block) (e : Sig V Owner Block) :
    (s.sign e).locals = s.locals := rfl

theorem HSig_sign (s : State V Owner Block) (e : Sig V Owner Block) (v : V) (m : Msg Block) :
    (s.sign e).HSig v m ↔ s.HSig v m ∨ (e.signer = v ∧ e.msg = m) := by
  simp only [HSig, log_sign, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨e', he' | he', h⟩
    · exact Or.inl ⟨e', he', h⟩
    · subst he'; exact Or.inr h
  · rintro (⟨e', he', h⟩ | h)
    · exact ⟨e', Or.inl he', h⟩
    · exact ⟨e, Or.inr rfl, h⟩

theorem HSig.sign {s : State V Owner Block} {v : V} {m : Msg Block} (h : s.HSig v m)
    (e : Sig V Owner Block) : (s.sign e).HSig v m := (HSig_sign s e v m).2 (Or.inl h)

/-! ### Certificates -/

section Cert

variable [Fintype V] [DecidableEq V] [Q : QuorumSystem V] [DecidableEq Block]

/-- `v`'s signature on `m` is available: `v` is Byzantine, or honest and signed it. -/
def Signed (s : State V Owner Block) (v : V) (m : Msg Block) : Prop :=
  v ∉ Q.honest ∨ ∃ e ∈ s.log, e.signer = v ∧ e.msg = m

instance (s : State V Owner Block) (v : V) (m : Msg Block) : Decidable (s.Signed v m) := by
  unfold Signed; infer_instance

/-- The validators whose signature on `m` is available. -/
def signers (s : State V Owner Block) (m : Msg Block) : Finset V :=
  Finset.univ.filter (fun v => s.Signed v m)

/-- A certificate on `m` exists: its signers form a quorum. -/
def HasCert (s : State V Owner Block) (m : Msg Block) : Prop := Q.Quorum (s.signers m)

instance (s : State V Owner Block) (m : Msg Block) : Decidable (s.HasCert m) :=
  Q.decQuorum _

/-- `ValCert(B, r)` exists. -/
abbrev ValCert (s : State V Owner Block) (B : Block) (r : Round) : Prop := s.HasCert (.val B r)

/-- `ConfCert(B, r)` exists. -/
abbrev ConfCert (s : State V Owner Block) (B : Block) (r : Round) : Prop := s.HasCert (.conf B r)

/-- `TimeoutCert(r)` exists. -/
abbrev TimeoutCert (s : State V Owner Block) (r : Round) : Prop := s.HasCert (.time r)

omit [DecidableEq Block] in
theorem Signed_of_HSig {s : State V Owner Block} {v : V} {m : Msg Block} (h : s.HSig v m) :
    s.Signed v m := Or.inr h

omit [DecidableEq Block] in
/-- An honest validator's available signature is in the log. -/
theorem HSig_of_Signed {s : State V Owner Block} {v : V} {m : Msg Block} (hv : v ∈ Q.honest)
    (h : s.Signed v m) : s.HSig v m := h.resolve_left (not_not.2 hv)

theorem mem_signers {s : State V Owner Block} {v : V} {m : Msg Block} :
    v ∈ s.signers m ↔ s.Signed v m := by simp [signers]

/-- Certificates persist when a signature is added. -/
theorem HasCert.sign {s : State V Owner Block} {m : Msg Block} (h : s.HasCert m)
    (e : Sig V Owner Block) : (s.sign e).HasCert m := by
  refine Q.quorum_mono ?_ h
  intro v hv
  rw [mem_signers] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (HSig.sign hv e)

/-- Certificates do not depend on local states. -/
theorem HasCert_set (s : State V Owner Block) (w : V) (l : Local Block) (m : Msg Block) :
    (s.set w l).HasCert m ↔ s.HasCert m := Iff.rfl

/-- A certificate has an honest signer in the log. -/
theorem HasCert.exists_honest_HSig {s : State V Owner Block} {m : Msg Block} (h : s.HasCert m) :
    ∃ v ∈ Q.honest, s.HSig v m := by
  obtain ⟨v, hv, hh⟩ := Q.exists_honest_mem h
  exact ⟨v, hh, HSig_of_Signed hh (mem_signers.1 hv)⟩

/-- Two certificates share an honest signer in the log. -/
theorem HasCert.exists_honest_HSig_inter {s : State V Owner Block} {m₁ m₂ : Msg Block}
    (h₁ : s.HasCert m₁) (h₂ : s.HasCert m₂) : ∃ v ∈ Q.honest, s.HSig v m₁ ∧ s.HSig v m₂ := by
  obtain ⟨v, hv, hh⟩ := Q.exists_honest_mem_inter h₁ h₂
  rw [Finset.mem_inter, mem_signers, mem_signers] at hv
  exact ⟨v, hh, HSig_of_Signed hh hv.1, HSig_of_Signed hh hv.2⟩

end Cert

end State

variable [Fintype V] [DecidableEq V] [Q : QuorumSystem V] [DecidableEq Owner] [DecidableEq Block]

/-- The inputs a validator reacts to. A certificate input is accepted only
if the certificate exists in the current state. -/
inductive Input (Owner Block : Type*)
  /-- A block proposal, two-phase or fast according to its round. -/
  | proposal (P : Proposal Owner Block)
  /-- A validation certificate `ValCert(B, r)`. -/
  | valCert (B : Block) (r : Round)
  /-- A confirmation certificate `ConfCert(B, r)`. -/
  | confCert (B : Block) (r : Round)
  /-- A local timeout of round `r`. -/
  | timeout (r : Round)
  /-- A timeout certificate `TimeoutCert(r)`. -/
  | timeoutCert (r : Round)
  deriving DecidableEq

/-- The carried certificate of a justification exists in `s`. -/
def State.JustCert (s : State V Owner Block) : Just Block → Prop
  | .none => True
  | .cert B' ρ => s.ValCert B' ρ
  | .fast => True

instance (s : State V Owner Block) (j : Just Block) : Decidable (s.JustCert j) := by
  unfold State.JustCert; split <;> infer_instance

open State in
/-- One handler invocation at validator `v`; `none` when the input is
refused or has no effect. A two-phase proposal that passes every check but
validity or the lock rule still advances the round (Alg. on_proposal,
line 12, note). -/
def step (cfg : Config Owner Block) (s : State V Owner Block) (v : V) :
    Input Owner Block → Option (State V Owner Block)
  | .proposal P =>
    let l := s.locals v
    if cfg.IsFast P.round then
      if l.fastOk cfg P then
        some ((s.set v (l.afterFast P)).sign ⟨v, .conf P.block P.round, l.lock, some P⟩)
      else none
    else
      if l.preOk cfg P ∧ s.JustCert P.just then
        if l.lockOk cfg P ∧ cfg.Valid P.block then
          some ((s.set v (l.afterVal P)).sign ⟨v, .val P.block P.round, l.lock, some P⟩)
        else some (s.set v (l.afterBump P))
      else none
  | .valCert B r =>
    let l := s.locals v
    if s.ValCert B r ∧ l.valCertOk B r then
      let s₁ := s.set v (l.afterValCert B r)
      some (if l.confVotes r then s₁.sign ⟨v, .conf B r, l.lock, none⟩ else s₁)
    else none
  | .confCert B r =>
    let l := s.locals v
    if s.ConfCert B r ∧ l.finalized = none then some (s.set v (l.afterConfCert B)) else none
  | .timeout r =>
    let l := s.locals v
    if l.timeoutOk r then
      some ((s.set v (l.afterTimeout r)).sign ⟨v, .time r, l.lock, none⟩)
    else none
  | .timeoutCert r =>
    let l := s.locals v
    if s.TimeoutCert r ∧ l.tcOk r then some (s.set v (l.afterTimeoutCert r)) else none

/-- A step of an honest validator. -/
def Step (cfg : Config Owner Block) (s s' : State V Owner Block) : Prop :=
  ∃ v ∈ Q.honest, ∃ i, step cfg s v i = some s'

/-- The reachable states of a height. -/
def Reachable (cfg : Config Owner Block) : State V Owner Block → Prop :=
  Relation.ReflTransGen (Step cfg) State.init

/-- Run a list of honest inputs from a state; `none` if any is refused. -/
def run (cfg : Config Owner Block) : List (V × Input Owner Block) → State V Owner Block →
    Option (State V Owner Block)
  | [], s => some s
  | (v, i) :: rest, s => (step cfg s v i).bind (run cfg rest)

/-- A run of honest inputs from a reachable state ends in a reachable state. -/
theorem Reachable.of_run (cfg : Config Owner Block) {s s' : State V Owner Block}
    (hs : Reachable cfg s) (inputs : List (V × Input Owner Block))
    (hv : ∀ p ∈ inputs, p.1 ∈ Q.honest) (h : run cfg inputs s = some s') : Reachable cfg s' := by
  induction inputs generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst h; exact hs
  | cons p rest ih =>
    obtain ⟨v, i⟩ := p
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    have hstep : Step cfg s s₁ := ⟨v, hv (v, i) (by simp), i, h₁⟩
    exact ih (Relation.ReflTransGen.tail hs hstep) (fun p hp => hv p (by simp [hp])) h₂

end Linera
