import LeanLinera.Committee

/-!
# Rounds, messages, proposals, and the per-chain configuration

The vocabulary of `consensus.tex`: the three signed messages `Val(B,r)`,
`Conf(B,r)`, `Time(r)`; a proposal `P = (r, B, O, C, o)` with the execution
output `O` elided (it is checked by a validity predicate and plays no role in
agreement); and the configuration that fixes which owner may propose in
which round — an optional fast round `0` with a super owner
(`appendix.tex`, Fast Round), `k` multi-leader rounds, then round-robin
single-leader rounds (Single-Leader Rounds).
-/

namespace LeanLinera

/-- Round numbers. -/
abbrev Round := ℕ

/-- The three kinds of signed vote. -/
inductive Msg (Block : Type*)
  /-- A validation vote `Val(B,r)`. -/
  | val (B : Block) (r : Round)
  /-- A confirmation vote `Conf(B,r)`. -/
  | conf (B : Block) (r : Round)
  /-- A timeout vote `Time(r)`. -/
  | time (r : Round)
  deriving DecidableEq, Repr

/-- A block proposal: the round, the block, an optional earlier validation
certificate `(B', r')` the proposer attaches, and the proposing owner. -/
structure Proposal (Owner Block : Type*) where
  /-- The round proposed in. -/
  round : Round
  /-- The proposed block. -/
  block : Block
  /-- An optional validation certificate `ValCert(B', r')` carried by the proposal. -/
  cert : Option (Block × Round)
  /-- The proposing owner. -/
  owner : Owner
  deriving DecidableEq, Repr

/-- Per-chain configuration of the proposal schedule and of block validity. -/
structure Config (Owner Block : Type*) where
  /-- Whether round `0` is a fast round. -/
  fast : Bool
  /-- The super owner, the sole proposer of a fast round. -/
  super : Owner
  /-- Rounds below `k` (other than a fast round) are multi-leader. -/
  k : ℕ
  /-- The designated leader of a single-leader round. -/
  leader : Round → Owner
  /-- Block validity as checked by honest validators (`O = Exec(B)` and structural checks). -/
  Valid : Block → Prop
  /-- Validity is decidable. -/
  [decValid : DecidablePred Valid]

namespace Config

variable {Owner Block : Type*} [DecidableEq Owner] (cfg : Config Owner Block)

instance : DecidablePred cfg.Valid := cfg.decValid

/-- Round `r` is the fast round: round `0` of a chain with a fast round. -/
def IsFast (r : Round) : Prop := cfg.fast = true ∧ r = 0

instance (r : Round) : Decidable (cfg.IsFast r) := inferInstanceAs (Decidable (_ ∧ _))

/-- `o ∈ Eligible(r)` for a two-phase round: every owner while `r < k`,
only `L_r` afterwards; nobody in the fast round, which takes the fast path. -/
def Eligible (r : Round) (o : Owner) : Prop :=
  ¬ cfg.IsFast r ∧ (r < cfg.k ∨ o = cfg.leader r)

instance (r : Round) (o : Owner) : Decidable (cfg.Eligible r o) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The super owner is the sole proposer of the fast round. -/
def FastEligible (r : Round) (o : Owner) : Prop := cfg.IsFast r ∧ o = cfg.super

instance (r : Round) (o : Owner) : Decidable (cfg.FastEligible r o) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Config

end LeanLinera
