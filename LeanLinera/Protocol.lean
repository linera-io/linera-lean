import LeanLinera.Validator
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

namespace LeanLinera

variable {V : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
variable {Owner Block : Type*} [DecidableEq Owner] [DecidableEq Block]

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
def set (s : State V Owner Block) (v : V) (l : Local Block) : State V Owner Block :=
  { s with locals := Function.update s.locals v l }

/-- Append a signature. -/
def sign (s : State V Owner Block) (e : Sig V Owner Block) : State V Owner Block :=
  { s with log := s.log ++ [e] }

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

end State

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

open State in
/-- One handler invocation at validator `v`; `none` when the input is
refused or has no effect. -/
def step (cfg : Config Owner Block) (s : State V Owner Block) (v : V) :
    Input Owner Block → Option (State V Owner Block)
  | .proposal P =>
    let l := s.locals v
    if cfg.IsFast P.round then
      if l.fastOk cfg P then
        some ((s.set v (l.afterFast P)).sign ⟨v, .conf P.block P.round, l.lock, some P⟩)
      else none
    else
      if l.proposalOk cfg P ∧ ∀ c ∈ P.cert, s.ValCert c.1 c.2 then
        some ((s.set v (l.afterProposal P)).sign ⟨v, .val P.block P.round, l.lock, some P⟩)
      else none
  | .valCert B r =>
    let l := s.locals v
    if s.ValCert B r ∧ l.valCertOk r then
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
    if s.TimeoutCert r ∧ l.finalized = none then some (s.set v (l.afterTimeoutCert r)) else none

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

end LeanLinera
