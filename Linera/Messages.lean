import Linera.Committee

/-!
# Rounds, messages, proposals, and the per-chain configuration

The vocabulary of `consensus.tex`: the three signed messages `Val(B,r)`,
`Conf(B,r)`, `Time(r)`; a proposal `P = (r, B, O, J, o)` with the execution
output `O` elided (it is checked by a validity predicate and plays no role
in agreement) and a justification `J`; and the configuration that fixes
which owner may propose in which round — an optional fast round `0` with a
super owner, `k` multi-leader rounds, then single-leader rounds with a
designated leader (`appendix.tex`, Fast Round and Single-Leader Rounds).
-/

namespace Linera

/-- Round numbers. A notation rather than an `abbrev`, so that `omega`
sees every round as a natural number. -/
notation "Round" => ℕ

/-- The three kinds of signed vote. -/
inductive Msg (Block : Type*)
  /-- A validation vote `Val(B,r)`. -/
  | val (B : Block) (r : Round)
  /-- A confirmation vote `Conf(B,r)`. -/
  | conf (B : Block) (r : Round)
  /-- A timeout vote `Time(r)`. -/
  | time (r : Round)
  deriving DecidableEq, Repr

/-- The justification `J` of a proposal: none for a fresh block; a
validation certificate `ValCert(B', ρ)` for a re-proposal; or `Fast`, the
super owner's signature on the fast-round proposal of the block. -/
inductive Just (Block : Type*)
  /-- A fresh block. -/
  | none
  /-- `ValCert(B', ρ)`, to be checked against the proposal. -/
  | cert (B' : Block) (ρ : Round)
  /-- The super owner's fast-round signature on the proposed block. -/
  | fast
  deriving DecidableEq, Repr

/-- A block proposal: the round, the block, the justification, and the
proposing owner. -/
structure Proposal (Owner Block : Type*) where
  /-- The round proposed in. -/
  round : Round
  /-- The proposed block. -/
  block : Block
  /-- The justification. -/
  just : Just Block
  /-- The proposing owner. -/
  owner : Owner
  deriving DecidableEq, Repr

/-- Per-chain configuration of the proposal schedule and of block validity. -/
structure Config (Owner Block : Type*) where
  /-- Whether the chain has a super owner, hence a fast round `0`. -/
  fast : Bool
  /-- The super owner, the sole proposer of the fast round. -/
  super : Owner
  /-- The number of multi-leader rounds. -/
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

/-- Round `r` is the fast round: round `0` of a chain with a super owner. -/
def IsFast (r : Round) : Prop := cfg.fast = true ∧ r = 0

instance (r : Round) : Decidable (cfg.IsFast r) := inferInstanceAs (Decidable (_ ∧ _))

/-- The first multi-leader round: `1` after a fast round, else `0`. -/
def firstMulti : Round := if cfg.fast then 1 else 0

/-- The first single-leader round `r_SL`. -/
def firstSL : Round := cfg.firstMulti + cfg.k

/-- Round `r` is multi-leader. -/
def IsMulti (r : Round) : Prop := cfg.firstMulti ≤ r ∧ r < cfg.firstSL

instance (r : Round) : Decidable (cfg.IsMulti r) := inferInstanceAs (Decidable (_ ∧ _))

/-- Round `r` is single-leader. -/
def IsSingle (r : Round) : Prop := cfg.firstSL ≤ r

instance (r : Round) : Decidable (cfg.IsSingle r) := inferInstanceAs (Decidable (_ ≤ _))

/-- `o ∈ Eligible(r)`: the super owner in every round; every owner in a
multi-leader round; the leader in a single-leader round. -/
def Eligible (r : Round) (o : Owner) : Prop :=
  (cfg.fast = true ∧ o = cfg.super) ∨ cfg.IsMulti r ∨ (cfg.IsSingle r ∧ o = cfg.leader r)

instance (r : Round) (o : Owner) : Decidable (cfg.Eligible r o) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The super owner is the sole proposer of the fast round. -/
def FastEligible (r : Round) (o : Owner) : Prop := cfg.IsFast r ∧ o = cfg.super

instance (r : Round) (o : Owner) : Decidable (cfg.FastEligible r o) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Config

end Linera
