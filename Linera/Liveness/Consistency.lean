import Linera.Safety.Safety
import Linera.Liveness.Runs

/-!
# Eventual consistency

The `model.tex` requirement: if an honest validator has confirmed a
block, then all honest validators will eventually confirm it, assuming
the block and its certificate remain available for relaying. In the
model, "available for relaying" is the existence of the confirmation
certificate; delivering it to every honest validator that has not
finalized yet finalizes the same block everywhere, since any validator
that had already finalized did so on a block with its own confirmation
certificate, which safety identifies with this one.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-- A confirmation certificate the validator accepts. -/
theorem step_confCert {cfg : Config Owner Block} {s : State V Owner Block} {v : V} {B : Block}
    {r : Round} (hcert : s.ConfCert B r) (hfin : (s.locals v).finalized = none) :
    step cfg s v (.confCert B r) = some (s.set v ((s.locals v).afterConfCert B)) := by
  rw [Linera.step, ite_eq_left ⟨hcert, hfin⟩]

/-- Readiness to finalize `B`: honest, the certificate exists, not finalized. -/
def FinReady (B : Block) (r : Round) (s : State V Owner Block) (v : V) : Prop :=
  v ∈ Q.honest ∧ s.ConfCert B r ∧ (s.locals v).finalized = none

/-- **Eventual consistency** (`model.tex`): once `ConfCert(B, r)` exists in a
reachable state, delivering it to every honest validator that has not yet
finalized (listed without duplicates in `L`) leaves every honest validator
finalized on `B`; the resulting state is reachable. -/
theorem eventual_consistency {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Reachable cfg s) {B : Block} {r : Round} (hcert : s.ConfCert B r) (L : List V)
    (hnd : L.Nodup) (hL : ∀ v ∈ L, v ∈ Q.honest)
    (hall : ∀ v ∈ Q.honest, (s.locals v).finalized = none → v ∈ L)
    (hfresh : ∀ v ∈ L, (s.locals v).finalized = none) :
    ∃ s', run cfg (L.map fun v => (v, .confCert B r)) s = some s' ∧ Reachable cfg s' ∧
      ∀ v ∈ Q.honest, (s'.locals v).finalized = some B := by
  -- every listed validator finalizes `B`
  have key : ∀ (M : List V), M.Nodup → ∀ t : State V Owner Block, Reachable cfg t →
      (∀ v ∈ M, FinReady B r t v) →
      (∀ v ∈ Q.honest, v ∉ M → (t.locals v).finalized = some B) →
      ∃ t', run cfg (M.map fun v => (v, .confCert B r)) t = some t' ∧ Reachable cfg t' ∧
        ∀ v ∈ Q.honest, (t'.locals v).finalized = some B := by
    intro M
    induction M with
    | nil =>
      intro _ t ht _ hdone
      exact ⟨t, rfl, ht, fun v hv => hdone v hv List.not_mem_nil⟩
    | cons v M ih =>
      intro hnd t ht hready hdone
      rw [List.nodup_cons] at hnd
      obtain ⟨hv, hc, hfin⟩ := hready v (List.mem_cons_self ..)
      have hstep := step_confCert (cfg := cfg) hc hfin
      set t₁ := t.set v ((t.locals v).afterConfCert B) with ht₁
      have ht₁r : Reachable cfg t₁ := Relation.ReflTransGen.tail ht ⟨v, hv, _, hstep⟩
      obtain ⟨t', h', ht'r, hfin'⟩ := ih hnd.2 t₁ ht₁r
        (fun w hw => by
          have hwv : w ≠ v := fun h => hnd.1 (h ▸ hw)
          obtain ⟨hw', hc', hf'⟩ := hready w (List.mem_cons_of_mem _ hw)
          refine ⟨hw', step_HasCert hstep hc', ?_⟩
          rw [ht₁, locals_set_of_ne _ _ hwv]; exact hf')
        (fun w hw hwM => by
          by_cases hwv : w = v
          · subst hwv; rw [ht₁, locals_set_self]; rfl
          · rw [ht₁, locals_set_of_ne _ _ hwv]
            refine hdone w hw (fun h => ?_)
            rw [List.mem_cons] at h
            rcases h with h | h
            · exact hwv h
            · exact hwM h)
      refine ⟨t', ?_, ht'r, hfin'⟩
      simp only [List.map_cons, run, hstep, Option.bind_some]
      exact h'
  refine key L hnd s hs (fun v hv => ⟨hL v hv, hcert, hfresh v hv⟩) ?_
  -- a validator not listed has already finalized, necessarily on `B`
  intro v hv hvL
  rcases h : (s.locals v).finalized with _ | B'
  · exact absurd (hall v hv h) hvL
  · obtain ⟨r', hc'⟩ := ((Inv.reachable hs) v hv).finalized_cert B' h
    rw [(Inv.reachable hs).confCert_unique hc' hcert]

end Linera
