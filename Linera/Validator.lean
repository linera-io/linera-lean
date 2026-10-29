import Linera.Messages

/-!
# A validator's per-height state and handlers

The local state of `consensus.tex` (`r_cur`, the latest validation vote,
the lock, the locking block, the latest timeout vote and certificate) and
the handlers, each as a guard and an update: `OnProposal` (Alg.
on_proposal) in its two-phase and fast forms, `OnCertificate`
(on_certificate), `OnConfirmationCertificate`, `OnProposalTimeout`
(on_timeout, without the deadline: in the untimed model a validator may
time out its current round at any moment) and `OnCertificateTimeout`
(on_timeout_certificate). Certificate existence is not a local matter and
is checked by the step relation of `Protocol.lean`.
-/

namespace Linera

/-- The locking block `lb`: the highest validation certificate seen, or
the fast-round proposal of a block. -/
inductive Locking (Block : Type*)
  /-- `ValCert(B, ρ)`. -/
  | cert (B : Block) (ρ : Round)
  /-- The fast-round proposal of `B`. -/
  | fast (B : Block)
  deriving DecidableEq, Repr

/-- The round of a locking block; the fast round is `0`. -/
def Locking.round {Block : Type*} : Locking Block → Round
  | .cert _ ρ => ρ
  | .fast _ => 0

/-- The block of a locking block. -/
def Locking.block {Block : Type*} : Locking Block → Block
  | .cert B _ => B
  | .fast B => B

/-- A validator's state for one height. -/
structure Local (Block : Type*) where
  /-- The current round `r_cur`. -/
  cur : Round := 0
  /-- The latest validation vote `valVote`. -/
  valVote : Option (Block × Round) := none
  /-- The lock: the latest confirmation vote `(B, r_ℓ)`. -/
  lock : Option (Block × Round) := none
  /-- The locking block `lb`, served to clients. -/
  lb : Option (Locking Block) := none
  /-- The latest timeout vote. -/
  timeoutVote : Option Round := none
  /-- The latest timeout certificate's round `tc`. -/
  tc : Option Round := none
  /-- The finalized block, once a confirmation certificate was accepted. -/
  finalized : Option Block := none

namespace Local

variable {Owner Block : Type*} [DecidableEq Owner] [DecidableEq Block]

/-- The initial state of a height. -/
def init : Local Block := {}

/-- Alg. on_proposal, line 4: the justification is well formed. -/
def JustOk (cfg : Config Owner Block) (P : Proposal Owner Block) : Prop :=
  match P.just with
  | .none => True
  | .cert B' ρ => B' = P.block ∧ ρ < P.round
  | .fast => cfg.fast = true ∧ ¬ cfg.IsFast P.round

instance (cfg : Config Owner Block) (P : Proposal Owner Block) : Decidable (JustOk cfg P) := by
  unfold JustOk; split <;> infer_instance

/-- Alg. on_proposal, lines 5–8: the round rule for a two-phase proposal.
Rounds up to `r_SL` may be skipped; later ones must be current. -/
def roundOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  if P.round ≤ cfg.firstSL then
    l.cur ≤ P.round ∧ (¬ cfg.IsFast l.cur ∨ P.owner = cfg.super)
  else P.round = l.cur

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.roundOk cfg P) := by
  unfold roundOk; infer_instance

/-- Alg. on_proposal, lines 3–11 except validity and the lock rule: what a
two-phase proposal must pass for the validator to take note of it (and
advance its round), whether or not it then votes. -/
def preOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  l.finalized = none ∧
  cfg.Eligible P.round P.owner ∧
  JustOk cfg P ∧
  l.roundOk cfg P ∧
  (∀ vv ∈ l.valVote, vv.2 < P.round) ∧
  (∀ lb ∈ l.lb, lb.round < P.round)

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.preOk cfg P) := by
  unfold preOk; infer_instance

/-- Alg. on_proposal, line 12: the lock rule against one lock `lk`. A
different block needs a certificate from a round strictly after the lock;
the same block needs one from a round at least the lock's, or the
fast-round signature if the lock is a fast-round confirmation. -/
def lockCond (cfg : Config Owner Block) (P : Proposal Owner Block) (lk : Block × Round) : Prop :=
  match P.just with
  | .none => False
  | .cert B' ρ => B' = P.block ∧ ((P.block = lk.1 ∧ lk.2 ≤ ρ) ∨ (P.block ≠ lk.1 ∧ lk.2 < ρ))
  | .fast => cfg.IsFast lk.2 ∧ P.block = lk.1

instance (cfg : Config Owner Block) (P : Proposal Owner Block) (lk : Block × Round) :
    Decidable (lockCond cfg P lk) := by
  unfold lockCond; split <;> infer_instance

/-- Alg. on_proposal, line 12: the lock rule. -/
def lockOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  ∀ lk ∈ l.lock, lockCond cfg P lk

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.lockOk cfg P) := by
  unfold lockOk; infer_instance

/-- Alg. on_proposal, lines 15–18: the locking block after a justification. -/
def lbAfter (l : Local Block) (P : Proposal Owner Block) : Option (Locking Block) :=
  match P.just, l.lb with
  | .cert B' ρ, none => some (.cert B' ρ)
  | .cert B' ρ, some lb => if lb.round < ρ then some (.cert B' ρ) else some lb
  | .fast, none => some (.fast P.block)
  | _, lb => lb

/-- Alg. on_proposal, lines 15–19 and 22: the state after a validation vote. -/
def afterVal (l : Local Block) (P : Proposal Owner Block) : Local Block :=
  { l with lb := l.lbAfter P, cur := max l.cur P.round, valVote := some (P.block, P.round) }

/-- Alg. on_proposal, line 19 only: the state after taking note of a
proposal without voting (the lock rule or validity failed). -/
def afterBump (l : Local Block) (P : Proposal Owner Block) : Local Block :=
  { l with cur := max l.cur P.round }

/-- The fast path: a valid fresh proposal by the super owner in the fast
round, at a validator that has cast no vote. -/
def fastOk (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) : Prop :=
  l.finalized = none ∧ cfg.FastEligible P.round P.owner ∧ cfg.Valid P.block ∧
  P.just = .none ∧ l.valVote = none ∧ l.lb = none ∧ l.lock = none

instance (cfg : Config Owner Block) (l : Local Block) (P : Proposal Owner Block) :
    Decidable (l.fastOk cfg P) := by
  unfold fastOk; infer_instance

/-- Alg. on_proposal, lines 18–21: after a fast confirmation vote. -/
def afterFast (l : Local Block) (P : Proposal Owner Block) : Local Block :=
  { l with lb := some (.fast P.block), cur := max l.cur P.round,
           lock := some (P.block, P.round), valVote := none }

/-- Alg. on_certificate, lines 2–4: the certificate is relevant. -/
def valCertOk (l : Local Block) (B : Block) (r : Round) : Prop :=
  l.finalized = none ∧ l.lock ≠ some (B, r) ∧
  (∀ vv ∈ l.valVote, vv.2 ≤ r) ∧ (∀ lb ∈ l.lb, lb.round < r)

instance (l : Local Block) (B : Block) (r : Round) : Decidable (l.valCertOk B r) := by
  unfold valCertOk; infer_instance

/-- Alg. on_certificate, line 7: whether a confirmation vote is signed. -/
def confVotes (l : Local Block) (r : Round) : Prop := l.cur ≤ r

instance (l : Local Block) (r : Round) : Decidable (l.confVotes r) := by
  unfold confVotes; infer_instance

/-- Alg. on_certificate, lines 5–10: record the locking block and advance
the round; if the round is now current, record the confirmation vote. -/
def afterValCert (l : Local Block) (B : Block) (r : Round) : Local Block :=
  let l₁ := { l with lb := some (.cert B r), cur := max l.cur r }
  if l.confVotes r then { l₁ with lock := some (B, r), valVote := none } else l₁

/-- Alg. on_confirmation_certificate: finalize. -/
def afterConfCert (l : Local Block) (B : Block) : Local Block :=
  { l with finalized := some B }

/-- Alg. on_timeout, lines 2–4: the current round, not yet timed out.
The local deadline is absent from the untimed model. -/
def timeoutOk (l : Local Block) (r : Round) : Prop :=
  l.finalized = none ∧ r = l.cur ∧ l.timeoutVote ≠ some r

instance (l : Local Block) (r : Round) : Decidable (l.timeoutOk r) := by
  unfold timeoutOk; infer_instance

/-- Alg. on_timeout, line 7: record the timeout vote. -/
def afterTimeout (l : Local Block) (r : Round) : Local Block :=
  { l with timeoutVote := some r }

/-- Alg. on_timeout_certificate, line 2: the certificate is newer than the known one. -/
def tcOk (l : Local Block) (r : Round) : Prop :=
  l.finalized = none ∧ ∀ t ∈ l.tc, t < r

instance (l : Local Block) (r : Round) : Decidable (l.tcOk r) := by
  unfold tcOk; infer_instance

/-- Alg. on_timeout_certificate, lines 3–4: record it and advance to `r + 1`. -/
def afterTimeoutCert (l : Local Block) (r : Round) : Local Block :=
  { l with tc := some r, cur := max l.cur (r + 1) }

end Local

end Linera
