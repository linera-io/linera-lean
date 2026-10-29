import Linera.Protocol

/-!
# Ghost fields are erasable

The honest signature record `Sig` carries two ghost fields, `lockAt` and
`prop`, that the proofs read and no handler does. This file makes that a
theorem: the erasure of a state keeps the local states and, of each
signature, only the signer and the message; certificates depend only on
the erasure (`HasCert_of_erase`), and so does every step
(`step_erase`). An implementation therefore stores nothing for the ghost
fields.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-- A signature without its ghost fields. -/
def Sig.erase (e : Sig V Owner Block) : V × Msg Block := (e.signer, e.msg)

/-- A state without ghost fields. -/
def State.erase (s : State V Owner Block) : (V → Local Block) × List (V × Msg Block) :=
  (s.locals, s.log.map Sig.erase)

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- Honest signatures depend only on the erasure. -/
theorem HSig_of_erase {s s' : State V Owner Block} (h : s.erase = s'.erase) (v : V)
    (m : Msg Block) : s.HSig v m ↔ s'.HSig v m := by
  have hl : s.log.map Sig.erase = s'.log.map Sig.erase := congrArg Prod.snd h
  have key : ∀ (l : List (Sig V Owner Block)), (∃ e ∈ l, e.signer = v ∧ e.msg = m) ↔
      (v, m) ∈ l.map Sig.erase := by
    intro l
    rw [List.mem_map]
    constructor
    · rintro ⟨e, he, h₁, h₂⟩; exact ⟨e, he, by simp [Sig.erase, h₁, h₂]⟩
    · rintro ⟨e, he, h⟩
      simp only [Sig.erase, Prod.mk.injEq] at h
      exact ⟨e, he, h.1, h.2⟩
  unfold HSig
  rw [key, key, hl]

omit [DecidableEq Owner] in
/-- Certificates depend only on the erasure. -/
theorem HasCert_of_erase {s s' : State V Owner Block} (h : s.erase = s'.erase) (m : Msg Block) :
    s.HasCert m ↔ s'.HasCert m := by
  have hsig : s.signers m = s'.signers m := by
    unfold signers
    refine Finset.filter_congr (fun v _ => ?_)
    unfold Signed
    exact or_congr Iff.rfl (HSig_of_erase h v m)
  unfold HasCert
  rw [hsig]

omit [Fintype V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- The erasure of an updated state. -/
theorem erase_set (s : State V Owner Block) (v : V) (l : Local Block) :
    (s.set v l).erase = (Function.update s.locals v l, s.log.map Sig.erase) := rfl

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- The erasure of a signed state. -/
theorem erase_sign (s : State V Owner Block) (e : Sig V Owner Block) :
    (s.sign e).erase = (s.locals, s.log.map Sig.erase ++ [(e.signer, e.msg)]) := by
  simp [State.erase, State.sign, Sig.erase]

/-- **Ghost-field erasure**: the erasure of a step's result depends only
on the erasure of its input. No handler reads a ghost field. -/
theorem step_erase (cfg : Config Owner Block) {s s' : State V Owner Block} (h : s.erase = s'.erase)
    (v : V) (i : Input Owner Block) :
    (step cfg s v i).map State.erase = (step cfg s' v i).map State.erase := by
  have hloc : s.locals = s'.locals := congrArg Prod.fst h
  have hlog : s.log.map Sig.erase = s'.log.map Sig.erase := congrArg Prod.snd h
  have hcert : ∀ m, s.HasCert m ↔ s'.HasCert m := HasCert_of_erase h
  have hjc : ∀ j, s.JustCert j ↔ s'.JustCert j := by
    intro j; cases j <;> simp [State.JustCert, hcert]
  cases i with
  | proposal P =>
    simp only [step, hloc, hjc]
    split_ifs <;> simp [State.set, State.sign, State.erase, Sig.erase, hloc, hlog]
  | valCert B r =>
    simp only [step, hloc, hcert]
    split_ifs <;> simp [State.set, State.sign, State.erase, Sig.erase, hloc, hlog]
  | confCert B r =>
    simp only [step, hloc, hcert]
    split_ifs <;> simp [State.set, State.erase, hloc, hlog]
  | timeout r =>
    simp only [step, hloc]
    split_ifs <;> simp [State.set, State.sign, State.erase, Sig.erase, hloc, hlog]
  | timeoutCert r =>
    simp only [step, hloc, hcert]
    split_ifs <;> simp [State.set, State.erase, hloc, hlog]

end Linera
