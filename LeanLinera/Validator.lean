import LeanLinera.Messages

/-!
# A validator's per-height state and handlers

The local state of `consensus.tex` (`r_cur`, the lock, the three per-round
vote flags, the `knownValCert` store) and the five handlers, each as a guard
and an update: `OnProposal` (Alg. on_proposal), the fast path of a fast
round, `OnCertificate` (on_certificate), `OnConfirmationCertificate`,
`OnProposalTimeout` (on_timeout, without the deadline: in the untimed model
a validator may time out any round at or above its current one) and
`OnCertificateTimeout` (on_timeout_certificate). Certificate existence is
not a local matter and is checked by the step relation of `Protocol.lean`.
-/

namespace LeanLinera

/-- A validator's state for one height. -/
structure Local (Block : Type*) where
  /-- The current round `r_cur`. -/
  cur : Round := 0
  /-- The lock `(B, r_ℓ)`, if any. -/
  lock : Option (Block × Round) := none
  /-- `votedVal[r]`. -/
  votedVal : Round → Bool := fun _ => false
  /-- `votedConf[r]`. -/
  votedConf : Round → Bool := fun _ => false
  /-- `timedOut[r]`. -/
  timedOut : Round → Bool := fun _ => false
  /-- `knownValCert[r]`, served to clients only. -/
  knownVal : Round → Option Block := fun _ => none
  /-- The finalized block, once a confirmation certificate was accepted. -/
  finalized : Option Block := none

namespace Local

variable {Owner Block : Type*} [DecidableEq Owner] [DecidableEq Block]

/-- The initial state of a height. -/
def init : Local Block := {}

/-- Alg. on_proposal, lines 3–12, for a two-phase round. The certificate
`P.cert`, if present, must additionally exist (checked in `Protocol.lean`). -/
def proposalOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  l.finalized = none ∧
  cfg.Eligible P.round P.owner ∧
  P.round = l.cur ∧
  cfg.Valid P.block ∧
  (∀ c ∈ P.cert, c.1 = P.block ∧ c.2 < P.round) ∧
  (∀ lk ∈ l.lock, lk.1 ≠ P.block → ∃ c ∈ P.cert, lk.2 ≤ c.2) ∧
  l.votedVal P.round = false ∧ l.votedConf P.round = false ∧ l.timedOut P.round = false

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.proposalOk cfg P) := by
  unfold proposalOk; infer_instance

/-- Alg. on_proposal, line 15: record the validation vote. -/
def afterProposal (l : Local Block) (P : Proposal Owner Block) : Local Block :=
  { l with votedVal := Function.update l.votedVal P.round true }

/-- Alg. on_certificate, line 9: adopt `(B, r)` as the lock if there is
none or it is from a lower round. -/
def bumpLock (l : Local Block) (B : Block) (r : Round) : Option (Block × Round) :=
  match l.lock with
  | none => some (B, r)
  | some lk => if lk.2 < r then some (B, r) else some lk

/-- The fast path of a fast round: a well-formed proposal from the super
owner in the current round receives a confirmation vote directly, unless
the validator has already confirmed or timed out in that round. -/
def fastOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  l.finalized = none ∧
  cfg.FastEligible P.round P.owner ∧
  P.round = l.cur ∧
  cfg.Valid P.block ∧
  l.votedConf P.round = false ∧ l.timedOut P.round = false

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.fastOk cfg P) := by
  unfold fastOk; infer_instance

/-- After a fast confirmation vote: record it and lock on the block. -/
def afterFast (l : Local Block) (P : Proposal Owner Block) : Local Block :=
  { l with votedConf := Function.update l.votedConf P.round true,
           lock := l.bumpLock P.block P.round }

/-- Alg. on_certificate, line 2: certificates for stale rounds are ignored. -/
def valCertOk (l : Local Block) (r : Round) : Prop := l.finalized = none ∧ l.cur ≤ r

instance (l : Local Block) (r : Round) : Decidable (l.valCertOk r) := by
  unfold valCertOk; infer_instance

/-- Alg. on_certificate, line 5: whether a confirmation vote is signed. -/
def confVotes (l : Local Block) (r : Round) : Prop :=
  l.votedConf r = false ∧ l.timedOut r = false

instance (l : Local Block) (r : Round) : Decidable (l.confVotes r) := by
  unfold confVotes; infer_instance

/-- Alg. on_certificate, lines 3–10: advance the round and store the
certificate; then, if no confirmation or timeout was issued in `r`, record
the confirmation vote and update the lock. -/
def afterValCert (l : Local Block) (B : Block) (r : Round) : Local Block :=
  let l₁ := { l with cur := r, knownVal := Function.update l.knownVal r (some B) }
  if l.confVotes r then
    { l₁ with votedConf := Function.update l₁.votedConf r true, lock := l₁.bumpLock B r }
  else l₁

/-- Alg. on_confirmation_certificate: finalize. -/
def afterConfCert (l : Local Block) (B : Block) : Local Block :=
  { l with finalized := some B }

/-- Alg. on_timeout, lines 2–3: not a stale round, not already timed out.
The local deadline is absent from the untimed model. -/
def timeoutOk (l : Local Block) (r : Round) : Prop :=
  l.finalized = none ∧ l.cur ≤ r ∧ l.timedOut r = false

instance (l : Local Block) (r : Round) : Decidable (l.timeoutOk r) := by
  unfold timeoutOk; infer_instance

/-- Alg. on_timeout, line 7: record the timeout vote. -/
def afterTimeout (l : Local Block) (r : Round) : Local Block :=
  { l with timedOut := Function.update l.timedOut r true }

/-- Alg. on_timeout_certificate: record the timeout and, if the round is
current or newer, advance to `r + 1`. -/
def afterTimeoutCert (l : Local Block) (r : Round) : Local Block :=
  let l₁ := { l with timedOut := Function.update l.timedOut r true }
  if l.cur ≤ r then { l₁ with cur := r + 1 } else l₁

end Local

end LeanLinera
