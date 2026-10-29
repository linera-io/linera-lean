import Linera.Messages
import Mathlib.Tactic.Linarith

/-!
# The proposal schedule

In a single-leader round the eligible owners are the designated leader
and the super owner, if any; in a multi-leader round every owner. With a
round-robin leader over finitely many owners and no super owner, every
owner is the sole eligible proposer in infinitely many single-leader
rounds (`appendix.tex`, Lemma honest-single-leader). The implementation's
stake-weighted pseudo-random schedule is a parameter `leader` here; the
property it must satisfy is the conclusion of `roundRobin_exists_ge`.
-/

namespace Linera

variable {Owner Block : Type*}

/-- Multi-leader and single-leader rounds are disjoint. -/
theorem Config.not_isMulti_of_isSingle (cfg : Config Owner Block) {r : Round}
    (h : cfg.IsSingle r) : ¬ cfg.IsMulti r := by
  rintro ⟨_, h'⟩; exact absurd h (not_le.2 h')

/-- In a single-leader round, the eligible owners are the leader and the super owner. -/
theorem Config.eligible_iff_single (cfg : Config Owner Block) {r : Round} (hr : cfg.IsSingle r)
    (o : Owner) : cfg.Eligible r o ↔ (cfg.fast = true ∧ o = cfg.super) ∨ o = cfg.leader r := by
  unfold Config.Eligible
  constructor
  · rintro (h | h | ⟨_, h⟩)
    · exact Or.inl h
    · exact absurd h (cfg.not_isMulti_of_isSingle hr)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hr, h⟩)

/-- In a multi-leader round, every owner is eligible. -/
theorem Config.eligible_of_isMulti (cfg : Config Owner Block) {r : Round} (hr : cfg.IsMulti r)
    (o : Owner) : cfg.Eligible r o := Or.inr (Or.inl hr)

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

/-- With a round-robin leader and no super owner, every owner is the sole
eligible proposer in some single-leader round at or after any given round. -/
theorem Config.exists_sole_eligible (cfg : Config (Fin m) Block) [NeZero m]
    (hl : cfg.leader = roundRobin m) (hnf : cfg.fast = false) (o : Fin m) (N : ℕ) :
    ∃ r, N ≤ r ∧ cfg.IsSingle r ∧ ∀ o', cfg.Eligible r o' ↔ o' = o := by
  obtain ⟨r, hr, hro⟩ := roundRobin_exists_ge m o (max N cfg.firstSL)
  have hN : N ≤ r := le_trans (le_max_left _ _) hr
  have hs : cfg.IsSingle r := le_trans (le_max_right _ _) hr
  refine ⟨r, hN, hs, fun o' => ?_⟩
  rw [cfg.eligible_iff_single hs, hl, hro, hnf]
  simp

end Linera
