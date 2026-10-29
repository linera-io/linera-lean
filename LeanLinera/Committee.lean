import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

/-!
# Validators, quorums, and quorum intersection

The protocol is stated over an abstract quorum system: a set of honest
validators and a `Quorum` predicate such that two quorums always share an
honest validator. This is the whole of what the safety proofs use. The
paper's stake-weighted committee (`model.tex`: total power `n`, Byzantine
power at most `f`, `3f < n`, quorum any power `≥ n − f`) is an instance,
`Weighted.toQuorumSystem`, and counting is the special case `weight = 1`.
-/

namespace LeanLinera

/-- An abstract quorum system over the validators `V`. -/
class QuorumSystem (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The quorums: the sets of validators whose signatures form a certificate. -/
  Quorum : Finset V → Prop
  /-- The honest validators. Everything else is Byzantine. -/
  honest : Finset V
  /-- A superset of a quorum is a quorum. -/
  quorum_mono : ∀ {A B : Finset V}, A ⊆ B → Quorum A → Quorum B
  /-- The honest validators alone form a quorum. -/
  quorum_honest : Quorum honest
  /-- Two quorums share an honest validator. -/
  exists_honest_mem_inter : ∀ {A B : Finset V}, Quorum A → Quorum B → ∃ v ∈ A ∩ B, v ∈ honest
  /-- Quorum membership is decidable, so concrete executions run by `decide`. -/
  [decQuorum : DecidablePred Quorum]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The stake-weighted committee -/

/-- The paper's committee: voting power `weight`, Byzantine power at most
`f`, with `3f` strictly below the total power `n`. -/
structure Weighted (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Voting power of each validator. -/
  weight : V → ℕ
  /-- The bound on Byzantine power. -/
  f : ℕ
  /-- The Byzantine validators. -/
  byzantine : Finset V
  /-- Byzantine power is at most `f`. -/
  byz_le : ∑ v ∈ byzantine, weight v ≤ f
  /-- `3f < n`. -/
  three_f_lt : 3 * f < ∑ v, weight v

namespace Weighted

variable (W : Weighted V)

/-- The voting power of a set of validators. -/
def wt (S : Finset V) : ℕ := ∑ v ∈ S, W.weight v

/-- The total voting power `n`. -/
def n : ℕ := ∑ v, W.weight v

/-- A quorum: voting power at least `n − f`. -/
def Quorum (S : Finset V) : Prop := W.n - W.f ≤ W.wt S

instance : DecidablePred W.Quorum := fun _ => Nat.decLe _ _

/-- The honest validators, the complement of the Byzantine set. -/
def honest : Finset V := W.byzantineᶜ

/-- Power is monotone under inclusion. -/
theorem wt_mono {A B : Finset V} (h : A ⊆ B) : W.wt A ≤ W.wt B :=
  Finset.sum_le_sum_of_subset h

/-- Power is at most the total `n`. -/
theorem wt_le_n (S : Finset V) : W.wt S ≤ W.n :=
  W.wt_mono (Finset.subset_univ S)

/-- Inclusion–exclusion for power. -/
theorem wt_union_add_wt_inter (A B : Finset V) :
    W.wt (A ∪ B) + W.wt (A ∩ B) = W.wt A + W.wt B :=
  Finset.sum_union_inter

/-- A set splits into its honest and Byzantine parts. -/
theorem wt_inter_honest_add_wt_inter_byz (S : Finset V) :
    W.wt (S ∩ W.honest) + W.wt (S ∩ W.byzantine) = W.wt S := by
  unfold wt honest
  rw [← Finset.sum_union]
  · congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  · rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_inter, Finset.mem_compl] at hv hv'
    exact hv.2 hv'.2

/-- Power of a set that is entirely Byzantine is at most `f`. -/
theorem wt_le_f_of_subset_byz {S : Finset V} (h : S ⊆ W.byzantine) : W.wt S ≤ W.f :=
  (W.wt_mono h).trans W.byz_le

/-- The honest validators carry at least `n − f` of the power, hence form a quorum. -/
theorem quorum_honest : W.Quorum W.honest := by
  unfold Quorum
  have h := W.wt_inter_honest_add_wt_inter_byz Finset.univ
  simp only [Finset.univ_inter] at h
  have hb : W.wt W.byzantine ≤ W.f := W.byz_le
  have hn : W.wt Finset.univ = W.n := rfl
  omega

/-- **Honest mass in a certificate** (paper, Lemma honest-mass): a quorum
carries at least `n − 2f` honest power. -/
theorem honest_wt_of_quorum {S : Finset V} (hS : W.Quorum S) :
    W.n - 2 * W.f ≤ W.wt (S ∩ W.honest) := by
  have h := W.wt_inter_honest_add_wt_inter_byz S
  have hb : W.wt (S ∩ W.byzantine) ≤ W.f :=
    W.wt_le_f_of_subset_byz Finset.inter_subset_right
  unfold Quorum at hS
  omega

/-- **Quorum intersection**: two quorums share at least `n − 2f > f` power,
so they share an honest validator. The paper's safety proof intersects the
honest masses of two certificates instead; that step is not valid in
general (two honest sets of power `n − 2f` can be disjoint when there is no
Byzantine power and `n ≤ 4f`), and this is the lemma it needs. -/
theorem exists_honest_mem_inter {A B : Finset V} (hA : W.Quorum A) (hB : W.Quorum B) :
    ∃ v ∈ A ∩ B, v ∈ W.honest := by
  by_contra hno
  push Not at hno
  have hsub : A ∩ B ⊆ W.byzantine := by
    intro v hv
    have := hno v hv
    simpa [honest] using this
  have h1 := W.wt_le_f_of_subset_byz hsub
  have h2 := W.wt_union_add_wt_inter A B
  have h3 := W.wt_le_n (A ∪ B)
  have h4 := W.three_f_lt
  unfold Quorum at hA hB
  change 3 * W.f < W.n at h4
  omega

/-- The quorum system of a weighted committee. -/
@[instance_reducible]
def toQuorumSystem : QuorumSystem V where
  Quorum := W.Quorum
  honest := W.honest
  quorum_mono h hA := le_trans hA (W.wt_mono h)
  quorum_honest := W.quorum_honest
  exists_honest_mem_inter := W.exists_honest_mem_inter
  decQuorum := inferInstance

end Weighted

/-! ## Consequences of the abstract axioms -/

namespace QuorumSystem

variable [Q : QuorumSystem V]

/-- A quorum contains an honest validator. -/
theorem exists_honest_mem {A : Finset V} (hA : Q.Quorum A) : ∃ v ∈ A, v ∈ Q.honest := by
  obtain ⟨v, hv, hh⟩ := Q.exists_honest_mem_inter hA hA
  exact ⟨v, (Finset.mem_inter.1 hv).1, hh⟩

/-- The Byzantine validators alone never form a quorum. -/
theorem not_quorum_of_subset_byz {A : Finset V} (h : ∀ v ∈ A, v ∉ Q.honest) : ¬ Q.Quorum A := by
  intro hA
  obtain ⟨v, hv, hh⟩ := Q.exists_honest_mem hA
  exact h v hv hh

end QuorumSystem

end LeanLinera
