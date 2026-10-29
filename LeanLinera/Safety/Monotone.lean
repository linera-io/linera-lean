import LeanLinera.Liveness.Runs

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
  cases i <;> simp [LeanLinera.step, Local.fastOk, Local.proposalOk, Local.valCertOk,
    Local.timeoutOk, hfin]

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- Bumping a lock never lowers its round. -/
theorem Local.bumpLock_ge (l : Local Block) (B : Block) (r : Round) :
    ∀ lk ∈ l.lock, ∃ lk' ∈ l.bumpLock B r, lk.2 ≤ lk'.2 := by
  intro lk hlk
  unfold Local.bumpLock
  rw [Option.mem_def] at hlk
  rw [hlk]
  change ∃ lk' ∈ (if lk.2 < r then some (B, r) else some lk), lk.2 ≤ lk'.2
  split_ifs with h
  · exact ⟨(B, r), rfl, h.le⟩
  · exact ⟨lk, rfl, le_rfl⟩

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
        simp [Local.afterFast, Local.afterProposal]
    | valCert B r =>
      rw [LeanLinera.step] at h
      have hcur : ((s.locals w).afterValCert B r).cur = r := by
        simp only [Local.afterValCert]; split_ifs <;> rfl
      split_ifs at h with h₁ h₂ <;> simp only [Option.some.injEq] at h <;> subst h <;>
        simp only [locals_sign, locals_set_self, hcur] <;> exact h₁.2.2
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
      simp only [locals_set_self, Local.afterTimeoutCert]
      split_ifs with hle
      · exact hle.trans (Nat.le_succ r)
      · exact le_rfl
  · rw [step_locals_of_ne h hwv]

/-- **The lock round never decreases** (paper, Lemma vote-monotone). -/
theorem step_lock_le {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') (w : V) :
    ∀ lk ∈ (s.locals w).lock, ∃ lk' ∈ (s'.locals w).lock, lk.2 ≤ lk'.2 := by
  by_cases hwv : w = v
  · subst hwv
    cases i with
    | proposal P =>
      rw [LeanLinera.step] at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
      · simp only [locals_sign, locals_set_self, Local.afterFast]
        exact Local.bumpLock_ge _ _ _
      · simp only [locals_sign, locals_set_self, Local.afterProposal]
        exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
    | valCert B r =>
      rw [LeanLinera.step] at h
      split_ifs at h with h₁ h₂ <;> simp only [Option.some.injEq] at h <;> subst h
      · have hlk : ((s.locals w).afterValCert B r).lock = (s.locals w).bumpLock B r := by
          simp [Local.afterValCert, h₂, Local.bumpLock]
        simp only [locals_sign, locals_set_self, hlk]
        exact Local.bumpLock_ge _ _ _
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
      split_ifs <;> exact fun lk hlk => ⟨lk, hlk, le_rfl⟩
  · rw [step_locals_of_ne h hwv]
    exact fun lk hlk => ⟨lk, hlk, le_rfl⟩

end LeanLinera
