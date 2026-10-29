import LeanLinera.Safety.Preservation
import LeanLinera.Liveness.Runs

/-!
# The protocol core of liveness: a good round finalizes

A two-phase round `r` in which every honest validator is fresh (at `r`,
every vote, lock and locking block below `r`) and the proposer's proposal
is well-formed, eligible and passes every honest lock finalizes in two
round trips: validation votes to a validation certificate, then
confirmation votes to a confirmation certificate
(`good_round_confirms`). This is the untimed content of the paper's Lemma
progress; what the timed layer must supply is exactly the freshness of
every honest validator when each message reaches it.

The paper's proposal rule — re-propose the block of the newest locking
block reported by the validators, with it as justification, or any valid
block if there is none — yields a proposal that passes every honest lock
(`acceptable_of_highest_lb`, `acceptable_of_fast_lb`,
`acceptable_of_no_lock`).
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-! ## The validation phase -/

/-- A two-phase proposal the validator validates. -/
theorem step_val {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {P : Proposal Owner Block} (hnf : ¬ cfg.IsFast P.round) (hpre : (s.locals v).preOk cfg P)
    (hjc : s.JustCert P.just) (hlock : (s.locals v).lockOk cfg P) (hvalid : cfg.Valid P.block) :
    step cfg s v (.proposal P) = some ((s.set v ((s.locals v).afterVal P)).sign
      ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩) := by
  rw [LeanLinera.step, ite_eq_right hnf, ite_eq_left ⟨hpre, hjc⟩, ite_eq_left ⟨hlock, hvalid⟩]

/-- Any accepted two-phase proposal updates the validator by `afterVal` or `afterBump`. -/
theorem step_proposal_locals_self {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {P : Proposal Owner Block} (hnf : ¬ cfg.IsFast P.round)
    (h : step cfg s v (.proposal P) = some s') :
    s'.locals v = (s.locals v).afterVal P ∨ s'.locals v = (s.locals v).afterBump P := by
  rw [LeanLinera.step, ite_eq_right hnf] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

/-- Certificates in a justification persist across a step. -/
theorem step_JustCert {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') {j : Just Block}
    (hj : s.JustCert j) : s'.JustCert j := by
  cases j with
  | none => trivial
  | cert B' ρ => exact step_HasCert h hj
  | fast => trivial

/-- Readiness to validate `P`: honest, the guards hold, the carried
certificate exists, the lock rule and validity hold. -/
def ValReady (cfg : Config Owner Block) (P : Proposal Owner Block) (s : State V Owner Block)
    (v : V) : Prop :=
  v ∈ Q.honest ∧ (s.locals v).preOk cfg P ∧ s.JustCert P.just ∧ (s.locals v).lockOk cfg P ∧
    cfg.Valid P.block

/-- Delivering `P` to every honest validator ready for it yields `ValCert(B, r)`. -/
theorem val_phase {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hnf : ¬ cfg.IsFast P.round) (L : List V) (hnd : L.Nodup) (hall : ∀ v ∈ Q.honest, v ∈ L)
    {s : State V Owner Block} (hready : ∀ v ∈ L, ValReady cfg P s v) :
    ∃ s', run cfg (L.map fun v => (v, .proposal P)) s = some s' ∧ s'.ValCert P.block P.round := by
  obtain ⟨s', hrun, hsig⟩ := run_each (.proposal P) (.val P.block P.round) (ValReady cfg P)
    (fun s v ⟨_, hpre, hjc, hlock, hvalid⟩ =>
      ⟨_, step_val hnf hpre hjc hlock hvalid, (HSig_sign _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩)
    (fun s s' v w hst hwv ⟨hw, hpre, hjc, hlock, hvalid⟩ =>
      ⟨hw, by rw [step_locals_of_ne hst hwv]; exact hpre, step_JustCert hst hjc,
        by rw [step_locals_of_ne hst hwv]; exact hlock, hvalid⟩)
    L hnd s hready
  exact ⟨s', hrun, HasCert_of_honest (fun v hv => hsig v (hall v hv))⟩

/-! ## The confirmation phase -/

/-- A validation certificate the validator confirms. -/
theorem step_conf {cfg : Config Owner Block} {s : State V Owner Block} {v : V} {B : Block}
    {r : Round} (hcert : s.ValCert B r) (hok : (s.locals v).valCertOk B r)
    (hcv : (s.locals v).confVotes r) :
    step cfg s v (.valCert B r) = some ((s.set v ((s.locals v).afterValCert B r)).sign
      ⟨v, .conf B r, (s.locals v).lock, none⟩) := by
  rw [LeanLinera.step, ite_eq_left ⟨hcert, hok⟩]
  simp only [ite_eq_left hcv]

/-- Readiness to confirm `B` in `r`: honest, the certificate exists, it is
relevant, and the round is at or above the validator's. -/
def ConfReady (B : Block) (r : Round) (s : State V Owner Block) (v : V) : Prop :=
  v ∈ Q.honest ∧ s.ValCert B r ∧ (s.locals v).valCertOk B r ∧ (s.locals v).confVotes r

/-- Delivering `ValCert(B, r)` to every honest validator ready for it yields `ConfCert(B, r)`. -/
theorem conf_phase {cfg : Config Owner Block} {B : Block} {r : Round} (L : List V) (hnd : L.Nodup)
    (hall : ∀ v ∈ Q.honest, v ∈ L) {s : State V Owner Block}
    (hready : ∀ v ∈ L, ConfReady B r s v) :
    ∃ s', run cfg (L.map fun v => (v, .valCert B r)) s = some s' ∧ s'.ConfCert B r := by
  obtain ⟨s', hrun, hsig⟩ := run_each (cfg := cfg) (.valCert B r) (.conf B r) (ConfReady B r)
    (fun s v ⟨_, hc, hok, hcv⟩ =>
      ⟨_, step_conf hc hok hcv, (HSig_sign _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩)
    (fun s s' v w hst hwv ⟨hw, hc, hok, hcv⟩ =>
      ⟨hw, step_HasCert hst hc, by rw [step_locals_of_ne hst hwv]; exact hok,
        by rw [step_locals_of_ne hst hwv]; exact hcv⟩)
    L hnd s hready
  exact ⟨s', hrun, HasCert_of_honest (fun v hv => hsig v (hall v hv))⟩

/-! ## A good round -/

/-- A validator is fresh at `r`: in round `r`, with its latest validation
vote, its lock and its locking block all from rounds below `r`, and not
finalized. -/
def Local.Fresh (r : Round) (l : Local Block) : Prop :=
  l.cur = r ∧ (∀ vv ∈ l.valVote, vv.2 < r) ∧ (∀ lb ∈ l.lb, lb.round < r) ∧
    (∀ lk ∈ l.lock, lk.2 < r) ∧ l.finalized = none

/-- A validator is mid-round at `r`: in round `r`, with its latest
validation vote at or below `r`, its lock and locking block below `r`,
and not finalized. This is what the validation phase leaves behind and
what the confirmation phase needs. -/
def Local.Mid (r : Round) (l : Local Block) : Prop :=
  l.cur = r ∧ (∀ vv ∈ l.valVote, vv.2 ≤ r) ∧ (∀ lb ∈ l.lb, lb.round < r) ∧
    (∀ lk ∈ l.lock, lk.2 < r) ∧ l.finalized = none

/-- A well-formed proposal for round `r` in state `s`: eligible, valid,
with a well-formed justification whose certificate exists. -/
structure Proposal.WellFormed (cfg : Config Owner Block) (s : State V Owner Block) (r : Round)
    (P : Proposal Owner Block) : Prop where
  /-- The proposal is for `r`. -/
  round : P.round = r
  /-- `r` is a two-phase round. -/
  not_fast : ¬ cfg.IsFast r
  /-- The proposer is eligible. -/
  elig : cfg.Eligible r P.owner
  /-- The block is valid. -/
  valid : cfg.Valid P.block
  /-- The justification is well formed. -/
  just : Local.JustOk cfg P
  /-- The carried certificate, if any, exists. -/
  cert : s.JustCert P.just

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- The locking block after a well-formed justification for `r` stays below `r`. -/
theorem Local.lbAfter_lt {cfg : Config Owner Block} {P : Proposal Owner Block} {r : Round}
    (hr : P.round = r) (hj : Local.JustOk cfg P) (hnf : ¬ cfg.IsFast r) {l : Local Block}
    (hlb : ∀ lb ∈ l.lb, lb.round < r) : ∀ lb' ∈ l.lbAfter P, lb'.round < r := by
  intro lb' hlb'
  unfold Local.lbAfter at hlb'
  unfold Local.JustOk at hj
  rcases hjust : P.just with _ | ⟨B', ρ⟩ | _ <;> rw [hjust] at hlb' hj
  · exact hlb lb' hlb'
  · rcases hl : l.lb with _ | lb₀ <;> rw [hl] at hlb'
    · rw [Option.mem_def, Option.some.injEq] at hlb'
      subst hlb'; exact hr ▸ hj.2
    · change lb' ∈ (if lb₀.round < ρ then some (.cert B' ρ) else some lb₀) at hlb'
      split_ifs at hlb'
      · rw [Option.mem_def, Option.some.injEq] at hlb'
        subst hlb'; exact hr ▸ hj.2
      · rw [Option.mem_def, Option.some.injEq] at hlb'
        subst hlb'; exact hlb _ (by rw [hl]; rfl)
  · rcases hl : l.lb with _ | lb₀ <;> rw [hl] at hlb'
    · rw [Option.mem_def, Option.some.injEq] at hlb'
      subst hlb'
      change 0 < r
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exact absurd ⟨hj.1, h0⟩ hnf
      · exact h0
    · change lb' ∈ some lb₀ at hlb'
      exact hlb lb' (by rw [hl]; exact hlb')

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- Fresh implies mid-round. -/
theorem Local.Fresh.mid {r : Round} {l : Local Block} (hf : l.Fresh r) : l.Mid r :=
  ⟨hf.1, fun vv hvv => (hf.2.1 vv hvv).le, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

omit [DecidableEq Owner] in
/-- A validation vote on a well-formed proposal keeps a validator mid-round. -/
theorem Local.Mid.afterVal {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) {l : Local Block} (hm : l.Mid r) :
    (l.afterVal P).Mid r := by
  obtain ⟨hcur, _, hlb, hlk, hfin⟩ := hm
  refine ⟨by simp [Local.afterVal, hcur, hP.round], ?_, ?_, hlk, hfin⟩
  · intro vv hvv
    simp only [Local.afterVal, Option.mem_def, Option.some.injEq] at hvv
    subst hvv; exact hP.round.le
  · exact Local.lbAfter_lt hP.round hP.just hP.not_fast hlb

omit [DecidableEq Owner] in
/-- Noting a well-formed proposal keeps a validator mid-round. -/
theorem Local.Mid.afterBump {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) {l : Local Block} (hm : l.Mid r) :
    (l.afterBump P).Mid r := by
  obtain ⟨hcur, hvv, hlb, hlk, hfin⟩ := hm
  exact ⟨by simp [Local.afterBump, hcur, hP.round], hvv, hlb, hlk, hfin⟩

omit [DecidableEq Owner] in
/-- A fresh validator passes the pre-checks of a well-formed proposal. -/
theorem Local.preOk_of_fresh {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) {l : Local Block} (hf : l.Fresh r) :
    l.preOk cfg P := by
  obtain ⟨hcur, hvv, hlb, _, hfin⟩ := hf
  refine ⟨hfin, hP.round ▸ hP.elig, hP.just, ?_, hP.round ▸ hvv, hP.round ▸ hlb⟩
  unfold Local.roundOk
  rw [hP.round, hcur]
  split_ifs
  · exact ⟨le_rfl, Or.inl hP.not_fast⟩
  · rfl

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- A mid-round validator is ready to confirm the round's block. -/
theorem Local.Mid.valCertOk {r : Round} {l : Local Block} (hm : l.Mid r) (B : Block) :
    l.valCertOk B r ∧ l.confVotes r := by
  obtain ⟨hcur, hvv, hlb, hlk, hfin⟩ := hm
  refine ⟨⟨hfin, ?_, hvv, hlb⟩, hcur.le⟩
  intro h
  exact lt_irrefl _ (hlk (B, r) (by rw [h]; rfl))

/-- **A good round finalizes** (the untimed core of the paper's Lemma
progress). In a two-phase round `r` where every honest validator (listed
without duplicates in `L`) is fresh, a well-formed proposal that passes
every honest lock, delivered to all, yields a validation certificate; that
certificate, delivered to all, yields a confirmation certificate. -/
theorem good_round_confirms {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) (L : List V) (hnd : L.Nodup)
    (hall : ∀ v ∈ Q.honest, v ∈ L) (hL : ∀ v ∈ L, v ∈ Q.honest)
    (hfresh : ∀ v ∈ L, (s.locals v).Fresh r) (hacc : ∀ v ∈ L, (s.locals v).lockOk cfg P) :
    ∃ s', run cfg (L.map (fun v => (v, .proposal P)) ++ L.map (fun v => (v, .valCert P.block r)))
      s = some s' ∧ s'.ConfCert P.block r := by
  have hnf : ¬ cfg.IsFast P.round := hP.round ▸ hP.not_fast
  -- validation phase
  obtain ⟨s₁, hrun₁, hval⟩ := val_phase hnf L hnd hall (s := s) (fun v hv =>
    ⟨hL v hv, Local.preOk_of_fresh hP (hfresh v hv), hP.cert, hacc v hv, hP.valid⟩)
  rw [hP.round] at hval
  -- every honest validator is mid-round, hence ready to confirm
  have hkeep : ∀ v ∈ L, (s₁.locals v).Mid r := by
    refine run_preserve (fun t => ∀ v ∈ L, (t.locals v).Mid r) hrun₁ ?_
      (fun v hv => (hfresh v hv).mid)
    intro p hp t t' hst hR w hw
    rw [List.mem_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    by_cases hwu : w = u
    · subst hwu
      rcases step_proposal_locals_self hnf hst with hl | hl <;> rw [hl]
      · exact (hR w hw).afterVal hP
      · exact (hR w hw).afterBump hP
    · rw [step_locals_of_ne hst hwu]
      exact hR w hw
  -- confirmation phase
  obtain ⟨s₂, hrun₂, hconf⟩ := conf_phase (cfg := cfg) L hnd hall (s := s₁) (fun v hv =>
    ⟨hL v hv, hval, ((hkeep v hv).valCertOk P.block).1, ((hkeep v hv).valCertOk P.block).2⟩)
  refine ⟨s₂, ?_, hconf⟩
  rw [run_append, hrun₁, Option.bind_some]
  exact hrun₂

/-! ## The paper's proposal rule -/

omit [DecidableEq Owner] in
/-- In a state where every honest validator is fresh at `r`, every
validation certificate is from a round below `r`. -/
theorem valCert_lt_of_fresh {cfg : Config Owner Block} {s : State V Owner Block} (hs : Inv cfg s)
    {r : Round} (hfresh : ∀ v ∈ Q.honest, (s.locals v).Fresh r) {B : Block} {ρ : Round}
    (h : s.ValCert B ρ) : ρ < r := by
  obtain ⟨v, hv, hsig⟩ := h.exists_honest_HSig
  rcases (hs v hv).val_bound B ρ hsig with ⟨vv, hvv, hle⟩ | ⟨lb, hlb, hle⟩
  · exact hle.trans_lt ((hfresh v hv).2.1 vv hvv)
  · exact hle.trans_lt ((hfresh v hv).2.2.1 lb hlb)

omit [DecidableEq Owner] in
/-- **The paper's re-proposal rule passes every lock** (Alg.
client_propose, Lemma progress): if `ValCert(B, ρ)` is the newest locking
block reported by any honest validator, then proposing `B` with it as
justification passes every honest lock. -/
theorem acceptable_of_highest_lb {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Inv cfg s) {B : Block} {ρ : Round} {w : V} (hw : w ∈ Q.honest)
    (hlbw : (s.locals w).lb = some (.cert B ρ))
    (hmax : ∀ v ∈ Q.honest, ∀ lb ∈ (s.locals v).lb, lb.round ≤ ρ)
    (P : Proposal Owner Block) (hj : P.just = .cert B ρ) (hB : P.block = B) :
    ∀ v ∈ Q.honest, (s.locals v).lockOk cfg P := by
  intro v hv lk hlk
  have hvi := hs v hv
  have hconf := hvi.lock_conf lk hlk
  obtain ⟨lb, hlb, hle⟩ := hvi.conf_bound lk.1 lk.2 hconf
  have hle' : lk.2 ≤ ρ := hle.trans (hmax v hv lb hlb)
  have hcertB : s.ValCert B ρ := (hs w hw).lb_cert B ρ hlbw
  unfold Local.lockCond
  rw [hj]
  refine ⟨hB.symm, ?_⟩
  by_cases hBlk : P.block = lk.1
  · exact Or.inl ⟨hBlk, hle'⟩
  · refine Or.inr ⟨hBlk, lt_of_le_of_ne hle' ?_⟩
    intro heq
    subst heq
    by_cases hf : cfg.IsFast lk.2
    · exact hs.not_valCert_fast hf hcertB
    · have hcert' := hvi.conf_valCert lk.1 lk.2 hconf hf
      exact hBlk (hB ▸ hs.valCert_unique hcertB hcert')

omit [DecidableEq Owner] [DecidableEq Block] in
/-- **Re-proposing the fast block passes every lock**: if every honest lock
is a fast-round confirmation of `B`, then proposing `B` with the
fast-round signature passes every honest lock. -/
theorem acceptable_of_fast_lb {cfg : Config Owner Block} {s : State V Owner Block} {B : Block}
    (hlk : ∀ v ∈ Q.honest, ∀ lk ∈ (s.locals v).lock, lk.1 = B ∧ cfg.IsFast lk.2)
    (P : Proposal Owner Block) (hj : P.just = .fast) (hB : P.block = B) :
    ∀ v ∈ Q.honest, (s.locals v).lockOk cfg P := by
  intro v hv lk hlk'
  unfold Local.lockCond
  rw [hj]
  exact ⟨(hlk v hv lk hlk').2, hB ▸ (hlk v hv lk hlk').1.symm⟩

omit [DecidableEq Owner] [DecidableEq Block] in
/-- **With no honest lock, any proposal passes the lock rule** (the "no
locking block learned" branch of Alg. client_propose). -/
theorem acceptable_of_no_lock {cfg : Config Owner Block} {s : State V Owner Block}
    (hnolock : ∀ v ∈ Q.honest, (s.locals v).lock = none) (P : Proposal Owner Block) :
    ∀ v ∈ Q.honest, (s.locals v).lockOk cfg P := by
  intro v hv lk hlk
  rw [hnolock v hv] at hlk
  exact absurd hlk (Option.not_mem_none _)

omit [DecidableEq Owner] in
/-- The newest locking block, re-proposed with itself as justification, is
a well-formed proposal for a fresh two-phase round. -/
theorem wellFormed_of_highest_lb {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Inv cfg s) {r : Round} (hnf : ¬ cfg.IsFast r)
    (hfresh : ∀ v ∈ Q.honest, (s.locals v).Fresh r) {B : Block} {ρ : Round} {w : V}
    (hw : w ∈ Q.honest) (hlbw : (s.locals w).lb = some (.cert B ρ)) {o : Owner}
    (helig : cfg.Eligible r o) (hvalid : cfg.Valid B) :
    (⟨r, B, .cert B ρ, o⟩ : Proposal Owner Block).WellFormed cfg s r where
  round := rfl
  not_fast := hnf
  elig := helig
  valid := hvalid
  just := ⟨rfl, valCert_lt_of_fresh hs hfresh ((hs w hw).lb_cert B ρ hlbw)⟩
  cert := (hs w hw).lb_cert B ρ hlbw

end LeanLinera
