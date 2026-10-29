import Linera.Safety.Preservation

/-!
# Safety

The paper's safety results (`appendix.tex`, Lemmas unique-valcert,
conf-needs-val and lock-validate, Theorem safety) and the `model.tex`
requirements of Safety and Authenticity, derived from the invariant on
reachable states. Every statement is over the untimed model, hence with
no timing assumption, and holds with the fast round enabled or not.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Block]

open State

omit [Fintype V] [DecidableEq V] Q [DecidableEq Block] in
/-- A round above another round is not the fast round. -/
theorem Config.not_isFast_of_lt {cfg : Config Owner Block} {r r' : Round} (h : r < r') :
    ¬ cfg.IsFast r' := by
  rintro ⟨_, h0⟩; omega

section Inv

variable {cfg : Config Owner Block} {s : State V Owner Block} (hs : Inv cfg s)
include hs

/-- Two confirmation certificates in one round are for the same block. -/
theorem Inv.confCert_unique_round {B₁ B₂ : Block} {r : Round} (h₁ : s.ConfCert B₁ r)
    (h₂ : s.ConfCert B₂ r) : B₁ = B₂ := by
  obtain ⟨v, hv, hs₁, hs₂⟩ := h₁.exists_honest_HSig_inter h₂
  exact (hs v hv).conf_unique B₁ B₂ r hs₁ hs₂

/-- **Confirmation needs validation** (paper, Lemma conf-needs-val): a
confirmation certificate outside the fast round rests on a validation
certificate for the same block and round. -/
theorem Inv.valCert_of_confCert {B : Block} {r : Round} (h : s.ConfCert B r)
    (hf : ¬ cfg.IsFast r) : s.ValCert B r := by
  obtain ⟨v, hv, hsig⟩ := h.exists_honest_HSig
  exact (hs v hv).conf_valCert B r hsig hf

/-- **The locked block is protected**: once `ConfCert(B, r)` exists, every
validation certificate from a later round is for `B`. This is the paper's
minimal-round argument in Theorem safety, by strong induction on the later
round. -/
theorem Inv.valCert_eq_of_confCert {B : Block} {r : Round} (hc : s.ConfCert B r) :
    ∀ r' B', r < r' → s.ValCert B' r' → B' = B := by
  intro r'
  induction r' using Nat.strong_induction_on with
  | _ r' ih =>
  intro B' hlt hval
  by_contra hne
  obtain ⟨v, hv, hconf, hval'⟩ := hc.exists_honest_HSig_inter hval
  have hvi := hs v hv
  obtain ⟨e, he, hsig, hmsg⟩ := hval'
  have hg := hvi.val_ghost e he hsig B' r' hmsg
  -- the lock at signing was at a round in `[r, r')`
  obtain ⟨lk, hlk, hrlk⟩ := hg.conf_le_lockAt B r hconf hlt
  obtain ⟨hlk_lt, hlk_conf⟩ := hg.lockAt_conf lk hlk
  -- and it was on `B`
  have hlkB : lk.1 = B := by
    rcases Nat.eq_or_lt_of_le hrlk with heq | hlt'
    · have hconf' : s.HSig v (.conf B lk.2) := heq ▸ hconf
      exact hvi.conf_unique lk.1 B lk.2 hlk_conf hconf'
    · have hvc := hvi.conf_valCert lk.1 lk.2 hlk_conf (Config.not_isFast_of_lt hlt')
      exact ih lk.2 hlk_lt lk.1 hlt' hvc
  -- so the vote carried `ValCert(B', ρ)` with `r ≤ r_ℓ < ρ < r'`
  obtain ⟨ρ, hj, hρ⟩ := hg.unlock lk hlk (by rw [hlkB]; exact fun h => hne h.symm)
  obtain ⟨_, hρlt, hcval⟩ := hg.cert_ok B' ρ hj
  exact hne (ih ρ hρlt B' (hrlk.trans_lt hρ) hcval)

/-- **Safety** (paper, Theorem safety): two confirmation certificates at a
height are for the same block. -/
theorem Inv.confCert_unique {B₁ B₂ : Block} {r₁ r₂ : Round} (h₁ : s.ConfCert B₁ r₁)
    (h₂ : s.ConfCert B₂ r₂) : B₁ = B₂ := by
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · exact (hs.valCert_eq_of_confCert h₁ r₂ B₂ hlt
      (hs.valCert_of_confCert h₂ (Config.not_isFast_of_lt hlt))).symm
  · subst heq; exact hs.confCert_unique_round h₁ h₂
  · exact hs.valCert_eq_of_confCert h₂ r₁ B₁ hgt
      (hs.valCert_of_confCert h₁ (Config.not_isFast_of_lt hgt))

end Inv

section Reachable

variable [DecidableEq Owner] {cfg : Config Owner Block} {s : State V Owner Block}
  (hr : Reachable cfg s)
include hr

/-- **Safety** on reachable states: no two conflicting blocks both obtain
confirmation certificates at a height, whatever the Byzantine validators
and owners do and with no timing assumption. -/
theorem safety {B₁ B₂ : Block} {r₁ r₂ : Round} (h₁ : s.ConfCert B₁ r₁)
    (h₂ : s.ConfCert B₂ r₂) : B₁ = B₂ :=
  (Inv.reachable hr).confCert_unique h₁ h₂

/-- **Safety requirement** (`model.tex`): no two honest validators finalize
different blocks at the same height. -/
theorem finalized_agree {v w : V} (hv : v ∈ Q.honest) (hw : w ∈ Q.honest) {B₁ B₂ : Block}
    (h₁ : (s.locals v).finalized = some B₁) (h₂ : (s.locals w).finalized = some B₂) :
    B₁ = B₂ := by
  have hs := Inv.reachable hr
  obtain ⟨r₁, hc₁⟩ := (hs v hv).finalized_cert B₁ h₁
  obtain ⟨r₂, hc₂⟩ := (hs w hw).finalized_cert B₂ h₂
  exact hs.confCert_unique hc₁ hc₂

/-- **Unique validation per round** on reachable states. -/
theorem valCert_unique {B₁ B₂ : Block} {r : Round} (h₁ : s.ValCert B₁ r) (h₂ : s.ValCert B₂ r) :
    B₁ = B₂ :=
  (Inv.reachable hr).valCert_unique h₁ h₂

/-- **No validation certificate in the fast round** on reachable states. -/
theorem not_valCert_fast {B : Block} {r : Round} (hf : cfg.IsFast r) : ¬ s.ValCert B r :=
  fun h => (Inv.reachable hr).not_valCert_fast hf h

/-- **Authenticity** (`model.tex`): an honest validation vote answers a
valid proposal by an owner eligible in that round. -/
theorem vote_of_eligible {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B : Block} {r : Round} (hm : e.msg = .val B r) :
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.Eligible r P.owner ∧
      cfg.Valid P.block :=
  (((Inv.reachable hr) e.signer hv).val_ghost e he rfl B r hm).prop_elig

/-- **Authenticity** in the fast round: an honest confirmation vote there
answers a proposal by the super owner. -/
theorem fast_vote_of_super {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B : Block} {r : Round} (hm : e.msg = .conf B r) (hf : cfg.IsFast r) :
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.FastEligible r P.owner :=
  ((Inv.reachable hr) e.signer hv).fast_elig e he rfl B r hm hf

/-- **Lock safety at validation** (paper, Lemma lock-validate): an honest
validation vote for `B'` in `r` cast while locked on `(B, r_ℓ)` with
`B ≠ B'` carried `ValCert(B', ρ)` with `r_ℓ < ρ < r`. -/
theorem lock_validate {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B' : Block} {r : Round} (hm : e.msg = .val B' r) {B : Block} {rℓ : Round}
    (hlk : e.lockAt = some (B, rℓ)) (hne : B ≠ B') :
    ∃ ρ, e.just = .cert B' ρ ∧ rℓ < ρ ∧ ρ < r ∧ s.ValCert B' ρ := by
  have hg := ((Inv.reachable hr) e.signer hv).val_ghost e he rfl B' r hm
  obtain ⟨ρ, hj, hlt⟩ := hg.unlock (B, rℓ) (by rw [hlk]; rfl) hne
  obtain ⟨_, hρlt, hcval⟩ := hg.cert_ok B' ρ hj
  exact ⟨ρ, hj, hlt, hρlt, hcval⟩

end Reachable

end Linera
