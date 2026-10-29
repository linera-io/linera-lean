import LeanLinera.Safety.Safety
import LeanLinera.Safety.Monotone
import LeanLinera.Liveness.Core

/-!
# Timed executions

Time is a tick counter. A timed execution is a state sequence with at most
one honest step per tick, starting from the initial state. A validator's
*entry* into its current round is the first tick at which it held that
round, and its *deadline* is the entry plus the round's duration (Alg.
on_timeout_certificate, the arming rule): a timeout vote may only be
attempted once the deadline has passed. Everything else — which input is
attempted when — is the adversary's choice; the environment assumptions
that constrain it after the global stabilisation time are in
`Obligations.lean`.

The file ends with the lemma the view-change argument rests on: a
validator past a single-leader round `r` got there through a timeout
certificate for `r` that existed strictly earlier.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-- Round durations (`consensus.tex`, Timeouts): the fast round lasts
`fastDur` if set; the last multi-leader round `base`; the `j`-th
single-leader round `base + j · inc`; other multi-leader rounds have no
deadline. -/
structure Timeouts where
  /-- Duration of the last multi-leader round and of the first single-leader round. -/
  base : ℕ
  /-- Increment per single-leader round. -/
  inc : ℕ
  /-- Duration of the fast round, if it times out. -/
  fastDur : Option ℕ

/-- The duration of round `r`, if it has a deadline. -/
def Timeouts.dur (tm : Timeouts) (cfg : Config Owner Block) (r : Round) : Option ℕ :=
  if cfg.IsFast r then tm.fastDur
  else if cfg.IsSingle r then some (tm.base + (r - cfg.firstSL) * tm.inc)
  else if r + 1 = cfg.firstSL then some tm.base
  else none

/-- One tick: an honest step if one is attempted and accepted, else nothing. -/
def stepOpt (cfg : Config Owner Block) (s : State V Owner Block) :
    Option (V × Input Owner Block) → State V Owner Block
  | none => s
  | some (v, i) => (step cfg s v i).getD s

open Classical in
/-- The first tick at which `v` held the round it holds at `t`. -/
noncomputable def entryAt (st : ℕ → State V Owner Block) (v : V) (t : ℕ) : ℕ :=
  Nat.find (⟨t, rfl⟩ : ∃ t', ((st t').locals v).cur = ((st t).locals v).cur)

/-- A timed execution. -/
structure TExec (cfg : Config Owner Block) (tm : Timeouts) where
  /-- The state at each tick. -/
  st : ℕ → State V Owner Block
  /-- The step attempted at each tick, if any. -/
  act : ℕ → Option (V × Input Owner Block)
  /-- The execution starts in the initial state. -/
  zero : st 0 = State.init
  /-- Each tick applies the attempted step, if accepted. -/
  succ : ∀ t, st (t + 1) = stepOpt cfg (st t) (act t)
  /-- Only honest validators take steps. -/
  honest : ∀ t v i, act t = some (v, i) → v ∈ Q.honest
  /-- A timeout vote is attempted only once the deadline of the current round has passed. -/
  timeout_ok : ∀ t v r, act t = some (v, .timeout r) →
    ∃ d, tm.dur cfg ((st t).locals v).cur = some d ∧ entryAt st v t + d ≤ t

namespace TExec

variable {cfg : Config Owner Block} {tm : Timeouts} (ex : TExec (V := V) cfg tm)

/-- The current round of `v` at tick `t`. -/
def cur (v : V) (t : ℕ) : Round := ((ex.st t).locals v).cur

/-- `v`'s entry into its current round at `t`. -/
noncomputable def entry (v : V) (t : ℕ) : ℕ := entryAt ex.st v t

/-- Every state of the execution is reachable. -/
theorem reachable (t : ℕ) : Reachable cfg (ex.st t) := by
  induction t with
  | zero => rw [ex.zero]; exact Relation.ReflTransGen.refl
  | succ t ih =>
    rw [ex.succ]
    rcases hact : ex.act t with _ | ⟨v, i⟩
    · exact ih
    · simp only [stepOpt]
      rcases hs : step cfg (ex.st t) v i with _ | s'
      · exact ih
      · exact Relation.ReflTransGen.tail ih ⟨v, ex.honest t v i hact, i, hs⟩

/-- The invariant holds at every tick. -/
theorem inv (t : ℕ) : Inv cfg (ex.st t) := Inv.reachable (ex.reachable t)

/-- The current round never decreases. -/
theorem cur_mono_succ (v : V) (t : ℕ) : ex.cur v t ≤ ex.cur v (t + 1) := by
  unfold cur
  rw [ex.succ]
  rcases hact : ex.act t with _ | ⟨w, i⟩
  · exact le_rfl
  · simp only [stepOpt]
    rcases hs : step cfg (ex.st t) w i with _ | s'
    · exact le_rfl
    · exact step_cur_le hs v

/-- The current round never decreases. -/
theorem cur_mono (v : V) {t t' : ℕ} (h : t ≤ t') : ex.cur v t ≤ ex.cur v t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (ex.cur_mono_succ v _)

/-- Signatures persist. -/
theorem HSig_mono {v : V} {m : Msg Block} {t t' : ℕ} (h : t ≤ t')
    (hs : (ex.st t).HSig v m) : (ex.st t').HSig v m := by
  induction h with
  | refl => exact hs
  | step _ ih =>
    rw [ex.succ]
    rcases hact : ex.act _ with _ | ⟨w, i⟩
    · exact ih
    · simp only [stepOpt]
      rcases hst : step cfg (ex.st _) w i with _ | s'
      · exact ih
      · exact step_HSig hst ih

/-- Certificates persist. -/
theorem HasCert_mono {m : Msg Block} {t t' : ℕ} (h : t ≤ t') (hs : (ex.st t).HasCert m) :
    (ex.st t').HasCert m := by
  induction h with
  | refl => exact hs
  | step _ ih =>
    rw [ex.succ]
    rcases hact : ex.act _ with _ | ⟨w, i⟩
    · exact ih
    · simp only [stepOpt]
      rcases hst : step cfg (ex.st _) w i with _ | s'
      · exact ih
      · exact step_HasCert hst ih

/-- Finalization persists. -/
theorem finalized_mono {v : V} {B : Block} {t t' : ℕ} (h : t ≤ t')
    (hf : ((ex.st t).locals v).finalized = some B) : ((ex.st t').locals v).finalized = some B := by
  induction h with
  | refl => exact hf
  | step _ ih =>
    rw [ex.succ]
    rcases hact : ex.act _ with _ | ⟨w, i⟩
    · exact ih
    · simp only [stepOpt]
      rcases hst : step cfg (ex.st _) w i with _ | s'
      · exact ih
      · by_cases hwv : v = w
        · subst hwv; rw [step_none_of_finalized ih] at hst; cases hst
        · simp only [Option.getD_some]; rw [step_locals_of_ne hst hwv]; exact ih

/-! ### Entry and deadline -/

/-- The entry is at or before `t`. -/
theorem entry_le (v : V) (t : ℕ) : ex.entry v t ≤ t := by
  unfold entry entryAt
  exact Nat.find_min' _ rfl

/-- At the entry, `v` holds its round at `t`. -/
theorem cur_entry (v : V) (t : ℕ) : ex.cur v (ex.entry v t) = ex.cur v t := by
  unfold entry entryAt cur
  exact Nat.find_spec (⟨t, rfl⟩ : ∃ t', ((ex.st t').locals v).cur = ((ex.st t).locals v).cur)

/-- Before the entry, `v` held a lower round. -/
theorem cur_lt_of_lt_entry (v : V) {t t' : ℕ} (h : t' < ex.entry v t) :
    ex.cur v t' < ex.cur v t := by
  have hne : ex.cur v t' ≠ ex.cur v t := by
    unfold entry entryAt at h
    exact Nat.find_min (m := t') _ h
  have hle : ex.cur v t' ≤ ex.cur v t :=
    ex.cur_mono v ((h.le).trans (ex.entry_le v t))
  exact lt_of_le_of_ne hle hne

/-- Between the entry and `t`, `v` holds its round at `t`. -/
theorem cur_of_entry_le (v : V) {t u : ℕ} (h₁ : ex.entry v t ≤ u) (h₂ : u ≤ t) :
    ex.cur v u = ex.cur v t :=
  le_antisymm (ex.cur_mono v h₂) (by rw [← ex.cur_entry v t]; exact ex.cur_mono v h₁)

/-- A validator that held its round of `t` already at `u ≤ t` entered it by `u`. -/
theorem entry_le_of_cur_eq (v : V) {t u : ℕ} (h : ex.cur v u = ex.cur v t) :
    ex.entry v t ≤ u := by
  by_contra hlt
  push Not at hlt
  exact absurd h (ne_of_lt (ex.cur_lt_of_lt_entry v hlt))

/-- The entry of a round is after any tick at which the validator held a lower round. -/
theorem lt_entry_of_cur_lt (v : V) {t u : ℕ} (h : ex.cur v u < ex.cur v t) : u < ex.entry v t := by
  by_contra hle
  push Not at hle
  have hut : u ≤ t := by
    by_contra h'; push Not at h'
    exact absurd (ex.cur_mono v h'.le) (not_le.2 h)
  rw [ex.cur_of_entry_le v hle hut] at h
  exact lt_irrefl _ h

/-! ### Moving past a single-leader round -/

/-- Either every honest validator is still at or below the single-leader
round `r` at tick `t`, or a timeout certificate for `r` existed strictly
before `t`. Proposals cannot carry a validator past `r`, certificates come
from signers who were already there, and a timeout certificate for a
higher round would need signers who were already past `r`. -/
theorem le_round_or_tc (hr : cfg.IsSingle r) (t : ℕ) :
    (∀ w ∈ Q.honest, ex.cur w t ≤ r) ∨ ∃ t' < t, (ex.st t').TimeoutCert r := by
  induction t with
  | zero =>
    left; intro w _
    unfold cur; rw [ex.zero]; simp [State.init, Local.init]
  | succ t ih =>
    rcases ih with ih | ⟨t', ht', htc⟩
    · by_cases htc : (ex.st t).TimeoutCert r
      · exact Or.inr ⟨t, Nat.lt_succ_self t, htc⟩
      left
      intro w hw
      unfold cur
      rw [ex.succ]
      rcases hact : ex.act t with _ | ⟨v, i⟩
      · exact ih w hw
      simp only [stepOpt]
      rcases hst : step cfg (ex.st t) v i with _ | s'
      · exact ih w hw
      simp only [Option.getD_some]
      by_cases hwv : w = v
      swap
      · rw [step_locals_of_ne hst hwv]; exact ih w hw
      subst hwv
      have hinv := ex.inv t
      cases i with
      | proposal P =>
        rw [LeanLinera.step] at hst
        split_ifs at hst with hf hok hpre hacc <;> simp only [Option.some.injEq] at hst <;>
          subst hst
        · -- fast: the round is unchanged
          simp only [locals_sign, locals_set_self, Local.afterFast]
          have := hf.2
          exact (max_le (ih w hw) (by omega))
        · simp only [locals_sign, locals_set_self, Local.afterVal]
          refine max_le (ih w hw) ?_
          have hro := hpre.1.2.2.2.1
          unfold Local.roundOk at hro
          split_ifs at hro with hle
          · exact hle.trans hr
          · exact hro ▸ ih w hw
        · simp only [locals_set_self, Local.afterBump]
          refine max_le (ih w hw) ?_
          have hro := hpre.1.2.2.2.1
          unfold Local.roundOk at hro
          split_ifs at hro with hle
          · exact hle.trans hr
          · exact hro ▸ ih w hw
      | valCert B ρ =>
        rw [LeanLinera.step] at hst
        have hcur : (((ex.st t).locals w).afterValCert B ρ).cur =
            max ((ex.st t).locals w).cur ρ := by
          simp only [Local.afterValCert]; split_ifs <;> rfl
        split_ifs at hst with hok hcv <;> simp only [Option.some.injEq] at hst <;> subst hst <;>
          obtain ⟨u, hu, hsig⟩ := hok.1.exists_honest_HSig <;>
          have hρ : ρ ≤ ex.cur u t := (hinv u hu).val_le_cur B ρ hsig
        · simp only [locals_sign, locals_set_self, hcur]
          exact max_le (ih w hw) (hρ.trans (ih u hu))
        · simp only [locals_set_self, hcur]
          exact max_le (ih w hw) (hρ.trans (ih u hu))
      | confCert B ρ =>
        rw [LeanLinera.step] at hst
        split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
        simp only [locals_set_self, Local.afterConfCert]
        exact ih w hw
      | timeout ρ =>
        rw [LeanLinera.step] at hst
        split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
        simp only [locals_sign, locals_set_self, Local.afterTimeout]
        exact ih w hw
      | timeoutCert ρ =>
        rw [LeanLinera.step] at hst
        split_ifs at hst with hok; simp only [Option.some.injEq] at hst; subst hst
        simp only [locals_set_self, Local.afterTimeoutCert]
        refine max_le (ih w hw) ?_
        obtain ⟨u, hu, hsig⟩ := hok.1.exists_honest_HSig
        have hρ : ρ ≤ ex.cur u t := (hinv u hu).time_le_cur ρ hsig
        have hρr : ρ ≤ r := hρ.trans (ih u hu)
        rcases Nat.lt_or_eq_of_le hρr with hlt | rfl
        · omega
        · exact absurd hok.1 htc
    · exact Or.inr ⟨t', ht'.trans (Nat.lt_succ_self t), htc⟩

/-- A validator past a single-leader round `r` got there through a timeout
certificate for `r` that existed strictly earlier. -/
theorem exists_tc_of_gt (hr : cfg.IsSingle r) {w : V} (hw : w ∈ Q.honest) {t : ℕ}
    (h : r < ex.cur w t) : ∃ t' < t, (ex.st t').TimeoutCert r := by
  rcases ex.le_round_or_tc hr t with hall | htc
  · exact absurd (hall w hw) (not_le.2 h)
  · exact htc

end TExec

end LeanLinera
