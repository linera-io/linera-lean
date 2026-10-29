import LeanLineraTest.Model

/-!
# Witness executions

Concrete runs on the four-validator model, checked by `decide`:

* a two-phase round `0` that finalizes block `1`;
* a fast round `0` that finalizes block `1` with confirmation votes only;
* a clashed multi-leader round skipped by a proposal for the next round,
  with no timeout;
* a lock refusing a conflicting proposal (while still advancing the
  round), and the same block accepted once re-proposed with its
  certificate;
* a timed-out round advanced by a timeout certificate.
-/

namespace LeanLineraTest

open LeanLinera

set_option maxRecDepth 4096

/-- Owner `0` proposes block `1` in round `0`. -/
def P₁ : Proposal Owner Block := ⟨0, 1, .none, 0⟩

/-- The sunny two-phase round: three validation votes, the certificate to
each validator, three confirmation votes, two validators finalize. -/
def sunny : List (V × Input Owner Block) :=
  [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁),
   (0, .valCert 1 0), (1, .valCert 1 0), (2, .valCert 1 0),
   (0, .confCert 1 0), (1, .confCert 1 0)]

/-- The sunny run yields `ConfCert(1, 0)` and finalizes block `1`. -/
theorem sunny_confirms :
    check slowCfg sunny (fun s => s.ConfCert 1 0 ∧ (s.locals 0).finalized = some 1 ∧
      (s.locals 2).finalized = none) = true := by
  decide

/-- Before the certificate, no confirmation certificate exists: the
Byzantine validator alone cannot make one. -/
theorem sunny_prefix_no_confcert :
    check slowCfg (sunny.take 3) (fun s => s.ValCert 1 0 ∧ ¬ s.ConfCert 1 0) = true := by
  decide

/-- A two-phase proposal is refused in a fast round, and the fast path
finalizes with confirmation votes only, recording the fast proposal as
the locking block. -/
theorem fast_confirms :
    check fastCfg [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁), (0, .confCert 1 0)]
      (fun s => s.ConfCert 1 0 ∧ ¬ s.ValCert 1 0 ∧ (s.locals 0).finalized = some 1 ∧
        (s.locals 1).lb = some (.fast 1)) = true := by
  decide

/-- The fast path is unavailable under `slowCfg`: the same inputs do not
finalize (round `0` is two-phase and a confirmation certificate needs
confirmation votes). -/
theorem slow_no_fast :
    check slowCfg [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁)]
      (fun s => ¬ s.ConfCert 1 0) = true := by
  decide

/-- Owner `1` proposes block `2` in round `0`, clashing with `P₁`. -/
def P₂₀ : Proposal Owner Block := ⟨0, 2, .none, 1⟩

/-- Owner `1` proposes block `2` in round `1` without a certificate. -/
def P₂ : Proposal Owner Block := ⟨1, 2, .none, 1⟩

/-- **A clashed multi-leader round is skipped without a timeout.**
Validators `0`, `1` validated `P₁` and validator `2` validated `P₂₀` in
round `0`; owner `1`'s proposal for round `1` is accepted by all three,
which advance to round `1`, and finalizes. -/
theorem clash_skipped :
    check slowCfg
      [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₂₀),
       (0, .proposal P₂), (1, .proposal P₂), (2, .proposal P₂),
       (0, .valCert 2 1), (1, .valCert 2 1), (2, .valCert 2 1)]
      (fun s => s.ConfCert 2 1 ∧ (s.locals 0).cur = 1 ∧ s.ValCert 1 0 ∧ ¬ s.ValCert 2 0) =
      true := by
  decide

/-- Round `0` validates and confirms block `1` at validators `0` and `1`
only (validator `2` validated it but never saw the certificate). -/
def lockedRound : List (V × Input Owner Block) :=
  [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁),
   (0, .valCert 1 0), (1, .valCert 1 0)]

/-- Owner `1` re-proposes block `1` in round `1` with `ValCert(1, 0)`. -/
def P₁' : Proposal Owner Block := ⟨1, 1, .cert 1 0, 1⟩

/-- Validator `0`, locked on `(1, 0)`, refuses to validate the conflicting
proposal but still advances to round `1`; validator `2`, unlocked,
validates it. -/
theorem lock_refuses :
    check slowCfg (lockedRound ++ [(0, .proposal P₂), (2, .proposal P₂)])
      (fun s => (s.locals 0).valVote = none ∧ (s.locals 0).cur = 1 ∧
        (s.locals 0).lock = some (1, 0) ∧ (s.locals 2).valVote = some (2, 1)) = true := by
  decide

/-- The re-proposal of the locked block, carrying its certificate, is
accepted by every honest validator and the height finalizes in round `1`. -/
theorem reproposal_confirms :
    check slowCfg (lockedRound ++
      [(0, .proposal P₁'), (1, .proposal P₁'), (2, .proposal P₁'),
       (0, .valCert 1 1), (1, .valCert 1 1), (2, .valCert 1 1)])
      (fun s => s.ConfCert 1 1) = true := by
  decide

/-- A single-leader round ends only by a timeout certificate: after
rounds `0` and `1` are skipped, the validators time out round `2` and
advance to round `3` on the certificate; the leader of round `3` is
owner `1` and its proposal is accepted. -/
theorem timeout_advances :
    check slowCfg
      [(0, .proposal ⟨2, 1, .none, 0⟩), (1, .proposal ⟨2, 1, .none, 0⟩),
       (2, .proposal ⟨2, 1, .none, 0⟩),
       (0, .timeout 2), (1, .timeout 2), (2, .timeout 2),
       (0, .timeoutCert 2), (1, .timeoutCert 2), (2, .timeoutCert 2),
       (0, .proposal ⟨3, 2, .none, 1⟩)]
      (fun s => (s.locals 0).cur = 3 ∧ (s.locals 0).valVote = some (2, 3) ∧
        (s.locals 1).cur = 3 ∧ s.TimeoutCert 2) = true := by
  decide

/-- A proposal for a later single-leader round is refused without a timeout
certificate, and a timeout vote is refused for a non-current round. -/
theorem single_leader_not_skipped :
    run slowCfg [(0, .proposal ⟨2, 1, .none, 0⟩), (0, .proposal ⟨3, 2, .none, 1⟩)]
      (State.init : State V Owner Block) = none ∧
    run slowCfg [((0 : V), .timeout 1)] (State.init : State V Owner Block) = none := by
  decide

end LeanLineraTest
