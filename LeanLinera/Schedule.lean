import LeanLinera.Messages
import Mathlib.Tactic.Linarith

/-!
# The proposal schedule

Single-leader rounds have exactly one eligible owner, the designated
leader; with a round-robin leader over finitely many owners, every owner
is the sole eligible proposer in infinitely many rounds (`appendix.tex`,
Lemma honest-single-leader, for the single-leader regime `r ≥ k`).
-/

namespace LeanLinera

variable {Owner Block : Type*}

/-- In a single-leader round, the leader is the only eligible owner. -/
theorem Config.eligible_iff_of_k_le (cfg : Config Owner Block) {r : Round} (hk : cfg.k ≤ r)
    (hf : ¬ cfg.IsFast r) (o : Owner) : cfg.Eligible r o ↔ o = cfg.leader r := by
  unfold Config.Eligible
  constructor
  · rintro ⟨_, h | h⟩
    · omega
    · exact h
  · intro h; exact ⟨hf, Or.inr h⟩

/-- In a multi-leader round, every owner is eligible. -/
theorem Config.eligible_of_lt_k (cfg : Config Owner Block) {r : Round} (hk : r < cfg.k)
    (hf : ¬ cfg.IsFast r) (o : Owner) : cfg.Eligible r o := ⟨hf, Or.inl hk⟩

/-- The round-robin leader over `m` owners. -/
def roundRobin (m : ℕ) [NeZero m] (r : Round) : Fin m := ⟨r % m, Nat.mod_lt _ (NeZero.pos m)⟩

/-- Every owner leads a round at or after any given round. -/
theorem roundRobin_exists_ge (m : ℕ) [NeZero m] (o : Fin m) (N : ℕ) :
    ∃ r, N ≤ r ∧ roundRobin m r = o := by
  refine ⟨o.val + (N + 1) * m, ?_, ?_⟩
  · have hm := NeZero.pos m
    nlinarith
  · apply Fin.ext
    simp only [roundRobin, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt o.isLt

/-- With a round-robin leader, every owner is the sole eligible proposer in
some single-leader round at or after any given round. -/
theorem Config.exists_sole_eligible (cfg : Config (Fin m) Block) [NeZero m]
    (hl : cfg.leader = roundRobin m) (o : Fin m) (N : ℕ) :
    ∃ r, N ≤ r ∧ cfg.k ≤ r ∧ ∀ o', cfg.Eligible r o' ↔ o' = o := by
  obtain ⟨r, hr, hro⟩ := roundRobin_exists_ge m o (max (max N cfg.k) 1)
  have hN : N ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hr)
  have hk : cfg.k ≤ r := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hr)
  have h1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hf : ¬ cfg.IsFast r := fun h => by have := h.2; omega
  refine ⟨r, hN, hk, fun o' => ?_⟩
  rw [cfg.eligible_iff_of_k_le hk hf, hl, hro]

end LeanLinera
