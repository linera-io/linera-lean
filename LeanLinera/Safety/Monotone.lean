import LeanLinera.Liveness.Runs
import LeanLinera.Safety.Invariants

/-!
# Monotonicity of the per-validator state

The paper's Lemma vote-monotone (the current round and the lock round
never decrease) and Lemma no-further-votes (a finalized validator takes
no further step), as properties of single steps.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-- **No further votes after finality** (paper, Lemma no-further-votes):
once a validator has finalized, every handler refuses every input. -/
theorem step_none_of_finalized {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {B : Block} (hfin : (s.locals v).finalized = some B) (i : Input Owner Block) :
    step cfg s v i = none := by
  cases i <;> simp [LeanLinera.step, Local.fastOk, Local.preOk, Local.valCertOk,
    Local.timeoutOk, Local.tcOk, hfin]

/-- **The current round never decreases** (paper, Lemma vote-monotone). -/
theorem step_cur_le {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') (w : V) :
    (s.locals w).cur ≤ (s'.locals w).cur := by
  by_cases hwv : w = v
  · subst hwv
    cases i with
    | proposal P =>
      rw [LeanLinera.step] at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
        simp [Local.afterFast, Local.afterVal, Local.afterBump]
    | valCert B r =>
      rw [LeanLinera.step] at h
      have hcur : ((s.locals w).afterValCert B r).cur = max (s.locals w).cur r := by
        simp only [Local.afterValCert]; split_ifs <;> rfl
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
        simp only [locals_sign, locals_set_self, hcur, le_max_left]
    | confCert B r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp [Local.afterConfCert]
    | timeout r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp [Local.afterTimeout]
    | timeoutCert r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp [Local.afterTimeoutCert]
  · rw [step_locals_of_ne h hwv]

/-- **The lock round never decreases** (paper, Lemma vote-monotone), at an
honest validator in a state satisfying the invariant: a new lock is a
confirmation in a round above the locking block, hence above the old lock. -/
theorem step_lock_le {cfg : Config Owner Block} {s s' : State V Owner Block} (hs : Inv cfg s)
    {v : V} {i : Input Owner Block} (h : step cfg s v i = some s') {w : V} (hw : w ∈ Q.honest) :
    ∀ lk ∈ (s.locals w).lock, ∃ lk' ∈ (s'.locals w).lock, lk.2 ≤ lk'.2 := by
  by_cases hwv : w = v
  · subst hwv
    have hvi := hs w hw
    cases i with
    | proposal P =>
      rw [LeanLinera.step] at h
      split_ifs at h with hf hok hpre hacc <;> simp only [Option.some.injEq] at h <;> subst h
      · intro lk hlk; rw [hok.2.2.2.2.2.2] at hlk; exact absurd hlk (Option.not_mem_none _)
      · simp only [locals_sign, locals_set_self, Local.afterVal]
        exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
      · simp only [locals_set_self, Local.afterBump]
        exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
    | valCert B r =>
      rw [LeanLinera.step] at h
      split_ifs at h with h₁ h₂ <;> simp only [Option.some.injEq] at h <;> subst h
      · have hlk : ((s.locals w).afterValCert B r).lock = some (B, r) := by
          simp [Local.afterValCert, h₂]
        simp only [locals_sign, locals_set_self, hlk]
        intro lk hlk'
        refine ⟨(B, r), rfl, ?_⟩
        obtain ⟨lb, hl, hle⟩ := hvi.conf_bound lk.1 lk.2 (hvi.lock_conf lk hlk')
        exact hle.trans (h₁.2.2.2.2 lb hl).le
      · have hlk : ((s.locals w).afterValCert B r).lock = (s.locals w).lock := by
          simp [Local.afterValCert, h₂]
        simp only [locals_set_self, hlk]
        exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
    | confCert B r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [locals_set_self, Local.afterConfCert]
      exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
    | timeout r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [locals_sign, locals_set_self, Local.afterTimeout]
      exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
    | timeoutCert r =>
      rw [LeanLinera.step] at h
      split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [locals_set_self, Local.afterTimeoutCert]
      exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
  · rw [step_locals_of_ne h hwv]
    exact fun lk hlk => ⟨lk, hlk, le_rfl⟩

end LeanLinera
