import LeanLineraTest.Model

/-!
# Witness executions

Concrete runs on the four-validator model, checked by `decide`:

* a two-phase round `0` that finalizes block `1`;
* a fast round `0` that finalizes block `1` with confirmation votes only;
* a lock refusing a conflicting proposal after a timeout, and the same
  proposal accepted once it carries the unlocking certificate.
-/

namespace LeanLineraTest

open LeanLinera

set_option maxRecDepth 4096

/-- Owner `0` proposes block `1` in round `0`. -/
def P₁ : Proposal Owner Block := ⟨0, 1, none, 0⟩

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
finalizes with confirmation votes only. -/
theorem fast_confirms :
    check fastCfg [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁), (0, .confCert 1 0)]
      (fun s => s.ConfCert 1 0 ∧ ¬ s.ValCert 1 0 ∧ (s.locals 0).finalized = some 1) = true := by
  decide

/-- The fast path is unavailable under `slowCfg`: the same inputs do not
finalize (round `0` is two-phase and a confirmation certificate needs
confirmation votes). -/
theorem slow_no_fast :
    check slowCfg [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁)]
      (fun s => ¬ s.ConfCert 1 0) = true := by
  decide

/-- Round `0` validates and confirms block `1` at validators `0` and `1`
only; the round then times out and everyone moves to round `1`. -/
def lockedRound : List (V × Input Owner Block) :=
  [(0, .proposal P₁), (1, .proposal P₁), (2, .proposal P₁),
   (0, .valCert 1 0), (1, .valCert 1 0),
   (0, .timeout 0), (1, .timeout 0), (2, .timeout 0),
   (0, .timeoutCert 0), (1, .timeoutCert 0), (2, .timeoutCert 0)]

/-- Owner `1` proposes a conflicting block `2` in round `1` without a certificate. -/
def P₂ : Proposal Owner Block := ⟨1, 2, none, 1⟩

/-- Owner `1` re-proposes block `1` in round `1` with `ValCert(1, 0)`. -/
def P₁' : Proposal Owner Block := ⟨1, 1, some (1, 0), 1⟩

/-- Validator `0`, locked on `(1, 0)`, refuses the conflicting proposal;
validator `2`, unlocked, accepts it. -/
theorem lock_refuses :
    run slowCfg (lockedRound ++ [(0, .proposal P₂)]) State.init = none ∧
    check slowCfg (lockedRound ++ [(2, .proposal P₂)])
      (fun s => (s.locals 2).votedVal 1 = true ∧ (s.locals 0).lock = some (1, 0)) = true := by
  decide

/-- The re-proposal of the locked block, carrying its certificate, is
accepted by every honest validator and the height finalizes in round `1`. -/
theorem reproposal_confirms :
    check slowCfg (lockedRound ++
      [(0, .proposal P₁'), (1, .proposal P₁'), (2, .proposal P₁'),
       (0, .valCert 1 1), (1, .valCert 1 1), (2, .valCert 1 1)])
      (fun s => s.ConfCert 1 1) = true := by
  decide

end LeanLineraTest
