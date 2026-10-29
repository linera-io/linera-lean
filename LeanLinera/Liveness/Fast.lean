import LeanLinera.Liveness.Runs

/-!
# Liveness of a fast round

With a super owner, an honest super owner finalizes in one round trip and
with no timing assumption beyond the obvious one: every honest validator
has cast no vote yet when the proposal reaches it. Delivering the proposal
to every honest validator then yields a confirmation certificate
(`appendix.tex`, Fast Round). A fast proposal is accepted whatever the
validator's current round, so timing out the fast round does not by
itself prevent this.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-- A fast proposal the validator accepts. -/
theorem step_fast {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {P : Proposal Owner Block} (hf : cfg.IsFast P.round) (hok : (s.locals v).fastOk cfg P) :
    step cfg s v (.proposal P) = some ((s.set v ((s.locals v).afterFast P)).sign
      ⟨v, .conf P.block P.round, (s.locals v).lock, some P⟩) := by
  rw [LeanLinera.step, ite_eq_left hf, ite_eq_left hok]

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- A validator that has cast no vote accepts a valid fresh proposal by
the super owner in the fast round. -/
theorem Local.fastOk_of_fresh {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hf : cfg.IsFast P.round) (ho : P.owner = cfg.super) (hvalid : cfg.Valid P.block)
    (hj : P.just = .none) {l : Local Block} (hvv : l.valVote = none) (hlb : l.lb = none)
    (hlk : l.lock = none) (hfin : l.finalized = none) : l.fastOk cfg P :=
  ⟨hfin, ⟨hf, ho⟩, hvalid, hj, hvv, hlb, hlk⟩

/-- Readiness for the fast proposal `P`: honest, and the fast path accepts. -/
def FastReady (cfg : Config Owner Block) (P : Proposal Owner Block) (s : State V Owner Block)
    (v : V) : Prop :=
  v ∈ Q.honest ∧ (s.locals v).fastOk cfg P

/-- **Fast-round finalization.** Delivering the super owner's proposal to
every honest validator (listed without duplicates in `L`), each of them
ready for it, yields `ConfCert(B, 0)` in one round trip. -/
theorem fast_round_confirms {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hf : cfg.IsFast P.round) (L : List V) (hnd : L.Nodup) (hall : ∀ v ∈ Q.honest, v ∈ L)
    {s : State V Owner Block} (hready : ∀ v ∈ L, FastReady cfg P s v) :
    ∃ s', run cfg (L.map fun v => (v, .proposal P)) s = some s' ∧
      s'.ConfCert P.block P.round := by
  obtain ⟨s', hrun, hsig⟩ := run_each (.proposal P) (.conf P.block P.round) (FastReady cfg P)
    (fun s v ⟨_, hok⟩ => ⟨_, step_fast hf hok, (HSig_sign _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩)
    (fun s s' v w hst hwv ⟨hw, hok⟩ => ⟨hw, by rw [step_locals_of_ne hst hwv]; exact hok⟩)
    L hnd s hready
  exact ⟨s', hrun, HasCert_of_honest (fun v hv => hsig v (hall v hv))⟩

/-- **Fast-round liveness from the start of a height.** An honest super
owner's valid proposal, delivered to every honest validator before any of
them votes, finalizes in one round trip; the resulting state is reachable. -/
theorem fast_round_finalizes {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hf : cfg.IsFast P.round) (ho : P.owner = cfg.super) (hvalid : cfg.Valid P.block)
    (hj : P.just = .none) (L : List V) (hnd : L.Nodup) (hall : ∀ v ∈ Q.honest, v ∈ L)
    (hL : ∀ v ∈ L, v ∈ Q.honest) :
    ∃ s', run cfg (L.map fun v => (v, .proposal P)) State.init = some s' ∧
      s'.ConfCert P.block P.round ∧ Reachable cfg s' := by
  obtain ⟨s', hrun, hc⟩ := fast_round_confirms hf L hnd hall (s := State.init)
    (fun v hv => ⟨hL v hv, Local.fastOk_of_fresh hf ho hvalid hj
      (by simp [State.init, Local.init]) (by simp [State.init, Local.init])
      (by simp [State.init, Local.init]) (by simp [State.init, Local.init])⟩)
  refine ⟨s', hrun, hc, Reachable.of_run cfg Relation.ReflTransGen.refl _ ?_ hrun⟩
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  exact hL v hv

end LeanLinera
