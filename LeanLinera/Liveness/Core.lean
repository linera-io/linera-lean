import LeanLinera.Safety.Preservation
import LeanLinera.Liveness.Runs

/-!
# The protocol core of liveness: a good round finalizes

A two-phase round `r` in which every honest validator is fresh (at `r`,
nothing voted or timed out in `r`) and the proposer's proposal is
well-formed, eligible and acceptable to every honest lock finalizes in two
round trips: validation votes to a validation certificate, then
confirmation votes to a confirmation certificate
(`good_round_confirms`). This is the untimed content of the paper's Lemma
progress; what the timed layer must supply is exactly the freshness of
every honest validator when each message reaches it.

The paper's proposal rule — re-propose the block of the highest-round
validation certificate reported by the validators, with that certificate,
or any valid block if none — yields an acceptable proposal whenever every
honest lock comes from a two-phase round (`acceptable_of_highest_known`).
A lock taken in a fast round is invisible to the `knownValCert` query and
is not covered; see `docs/design.md`.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-! ## The validation phase -/

/-- A two-phase proposal the validator accepts. -/
theorem step_val {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {P : Proposal Owner Block} (hnf : ¬ cfg.IsFast P.round) (hok : (s.locals v).proposalOk cfg P)
    (hc : ∀ c ∈ P.cert, s.ValCert c.1 c.2) :
    step cfg s v (.proposal P) = some ((s.set v ((s.locals v).afterProposal P)).sign
      ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩) := by
  rw [LeanLinera.step, ite_eq_right hnf, ite_eq_left ⟨hok, hc⟩]

/-- Any accepted two-phase proposal updates the validator by `afterProposal`. -/
theorem step_proposal_locals_self {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {P : Proposal Owner Block} (hnf : ¬ cfg.IsFast P.round)
    (h : step cfg s v (.proposal P) = some s') :
    s'.locals v = (s.locals v).afterProposal P := by
  rw [LeanLinera.step, ite_eq_right hnf] at h
  split_ifs at h
  simp only [Option.some.injEq] at h; subst h
  simp

/-- Readiness to validate `P`: honest, the guards hold, the carried
certificate exists. -/
def ValReady (cfg : Config Owner Block) (P : Proposal Owner Block) (s : State V Owner Block)
    (v : V) : Prop :=
  v ∈ Q.honest ∧ (s.locals v).proposalOk cfg P ∧ ∀ c ∈ P.cert, s.ValCert c.1 c.2

/-- Delivering `P` to every honest validator ready for it yields `ValCert(B, r)`. -/
theorem val_phase {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hnf : ¬ cfg.IsFast P.round) (L : List V) (hnd : L.Nodup) (hall : ∀ v ∈ Q.honest, v ∈ L)
    {s : State V Owner Block} (hready : ∀ v ∈ L, ValReady cfg P s v) :
    ∃ s', run cfg (L.map fun v => (v, .proposal P)) s = some s' ∧ s'.ValCert P.block P.round := by
  obtain ⟨s', hrun, hsig⟩ := run_each (.proposal P) (.val P.block P.round) (ValReady cfg P)
    (fun s v ⟨_, hok, hc⟩ => ⟨_, step_val hnf hok hc, (HSig_sign _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩)
    (fun s s' v w hst hwv ⟨hw, hok, hc⟩ =>
      ⟨hw, by rw [step_locals_of_ne hst hwv]; exact hok, fun c hc' => step_HasCert hst (hc c hc')⟩)
    L hnd s hready
  exact ⟨s', hrun, HasCert_of_honest (fun v hv => hsig v (hall v hv))⟩

/-! ## The confirmation phase -/

/-- A validation certificate the validator confirms. -/
theorem step_conf {cfg : Config Owner Block} {s : State V Owner Block} {v : V} {B : Block}
    {r : Round} (hcert : s.ValCert B r) (hok : (s.locals v).valCertOk r)
    (hcv : (s.locals v).confVotes r) :
    step cfg s v (.valCert B r) = some ((s.set v ((s.locals v).afterValCert B r)).sign
      ⟨v, .conf B r, (s.locals v).lock, none⟩) := by
  rw [LeanLinera.step, ite_eq_left ⟨hcert, hok⟩]
  simp only [ite_eq_left hcv]

/-- Readiness to confirm `B` in `r`: honest, the certificate exists, the
round is not stale, nothing confirmed or timed out in it. -/
def ConfReady (B : Block) (r : Round) (s : State V Owner Block) (v : V) : Prop :=
  v ∈ Q.honest ∧ s.ValCert B r ∧ (s.locals v).valCertOk r ∧ (s.locals v).confVotes r

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

/-- A validator is fresh at `r`: in round `r` with nothing voted or timed
out there, and not finalized. -/
def Local.Fresh (r : Round) (l : Local Block) : Prop :=
  l.cur = r ∧ l.votedVal r = false ∧ l.votedConf r = false ∧ l.timedOut r = false ∧
    l.finalized = none

/-- The proposal `P` passes the validator's lock check. -/
def Local.Acceptable (P : Proposal Owner Block) (l : Local Block) : Prop :=
  ∀ lk ∈ l.lock, lk.1 ≠ P.block → ∃ c ∈ P.cert, lk.2 ≤ c.2

/-- A well-formed proposal for round `r` in state `s`: eligible, valid,
and its certificate (if any) is for the block, predates `r` and exists. -/
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
  /-- The carried certificate is for the block, predates `r`, and exists. -/
  cert : ∀ c ∈ P.cert, c.1 = P.block ∧ c.2 < r ∧ s.ValCert c.1 c.2

omit [DecidableEq Owner] in
/-- A fresh validator accepts a well-formed proposal that passes its lock. -/
theorem Local.proposalOk_of_fresh {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) {l : Local Block} (hf : l.Fresh r)
    (ha : l.Acceptable P) : l.proposalOk cfg P := by
  obtain ⟨hcur, hvv, hvc, hto, hfin⟩ := hf
  refine ⟨hfin, hP.round ▸ hP.elig, by rw [hP.round, hcur], hP.valid,
    fun c hc => ⟨(hP.cert c hc).1, hP.round ▸ (hP.cert c hc).2.1⟩, ha, ?_, ?_, ?_⟩ <;>
    rw [hP.round] <;> assumption

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- Freshness for confirmation survives the validation phase. -/
theorem Local.Fresh.afterProposal {r : Round} {l : Local Block} (hf : l.Fresh r)
    (P : Proposal Owner Block) :
    (l.afterProposal P).cur = r ∧ (l.afterProposal P).votedConf r = false ∧
      (l.afterProposal P).timedOut r = false ∧ (l.afterProposal P).finalized = none :=
  ⟨hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

/-- **A good round finalizes** (the untimed core of the paper's Lemma
progress). In a two-phase round `r` where every honest validator (listed
without duplicates in `L`) is fresh, a well-formed proposal acceptable to
every honest lock, delivered to all, yields a validation certificate; that
certificate, delivered to all, yields a confirmation certificate. -/
theorem good_round_confirms {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) (L : List V) (hnd : L.Nodup)
    (hall : ∀ v ∈ Q.honest, v ∈ L) (hL : ∀ v ∈ L, v ∈ Q.honest)
    (hfresh : ∀ v ∈ L, (s.locals v).Fresh r) (hacc : ∀ v ∈ L, (s.locals v).Acceptable P) :
    ∃ s', run cfg (L.map (fun v => (v, .proposal P)) ++ L.map (fun v => (v, .valCert P.block r)))
      s = some s' ∧ s'.ConfCert P.block r := by
  have hnf : ¬ cfg.IsFast P.round := hP.round ▸ hP.not_fast
  -- validation phase
  obtain ⟨s₁, hrun₁, hval⟩ := val_phase hnf L hnd hall (s := s) (fun v hv =>
    ⟨hL v hv, Local.proposalOk_of_fresh hP (hfresh v hv) (hacc v hv),
      fun c hc => (hP.cert c hc).2.2⟩)
  rw [hP.round] at hval
  -- every honest validator is still ready to confirm
  have hkeep : ∀ v ∈ L, (s₁.locals v).cur = r ∧ (s₁.locals v).votedConf r = false ∧
      (s₁.locals v).timedOut r = false ∧ (s₁.locals v).finalized = none := by
    refine run_preserve (fun t => ∀ v ∈ L, (t.locals v).cur = r ∧ (t.locals v).votedConf r = false ∧
      (t.locals v).timedOut r = false ∧ (t.locals v).finalized = none) hrun₁ ?_
      (fun v hv => ⟨(hfresh v hv).1, (hfresh v hv).2.2.1, (hfresh v hv).2.2.2.1,
        (hfresh v hv).2.2.2.2⟩)
    intro p hp t t' hst hR w hw
    rw [List.mem_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    by_cases hwu : w = u
    · subst hwu
      rw [step_proposal_locals_self hnf hst]
      exact hR w hw
    · rw [step_locals_of_ne hst hwu]
      exact hR w hw
  -- confirmation phase
  obtain ⟨s₂, hrun₂, hconf⟩ := conf_phase (cfg := cfg) L hnd hall (s := s₁) (fun v hv =>
    ⟨hL v hv, hval, ⟨(hkeep v hv).2.2.2, (hkeep v hv).1.le⟩, (hkeep v hv).2.1, (hkeep v hv).2.2.1⟩)
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
  have hle := (hs v hv).val_le_cur B ρ hsig
  rw [(hfresh v hv).1] at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · exact hlt
  · exfalso
    have := ((hs v hv).votedVal_iff ρ).2 ⟨B, hsig⟩
    rw [(hfresh v hv).2.1] at this
    exact Bool.false_ne_true this

omit [DecidableEq Owner] in
/-- **The paper's re-proposal rule is acceptable** (Alg. client_propose,
Lemma progress): if `(B, r'')` is the highest-round entry of any honest
validator's `knownValCert`, and no honest validator holds a lock from a
fast round, then proposing `B` with `ValCert(B, r'')` passes every honest
lock. -/
theorem acceptable_of_highest_known {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Inv cfg s) {B : Block} {r'' : Round}
    (hmax : ∀ v ∈ Q.honest, ∀ ρ B', (s.locals v).knownVal ρ = some B' → ρ ≤ r'')
    (hnofast : ∀ v ∈ Q.honest, ∀ lk ∈ (s.locals v).lock, ¬ cfg.IsFast lk.2)
    (P : Proposal Owner Block) (hc : P.cert = some (B, r'')) :
    ∀ v ∈ Q.honest, (s.locals v).Acceptable P := by
  intro v hv lk hlk _
  have hk := (hs v hv).lock_known lk hlk (hnofast v hv lk hlk)
  exact ⟨(B, r''), by rw [hc]; rfl, hmax v hv lk.2 lk.1 hk⟩

omit [DecidableEq Owner] in
/-- The highest known certificate, re-proposed, is a well-formed proposal
for a fresh two-phase round. -/
theorem wellFormed_of_highest_known {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Inv cfg s) {r : Round} (hnf : ¬ cfg.IsFast r)
    (hfresh : ∀ v ∈ Q.honest, (s.locals v).Fresh r) {B : Block} {r'' : Round} {w : V}
    (hw : w ∈ Q.honest) (hknown : (s.locals w).knownVal r'' = some B) {o : Owner}
    (helig : cfg.Eligible r o) (hvalid : cfg.Valid B) :
    (⟨r, B, some (B, r''), o⟩ : Proposal Owner Block).WellFormed cfg s r where
  round := rfl
  not_fast := hnf
  elig := helig
  valid := hvalid
  cert c hc := by
    rw [Option.mem_def, Option.some.injEq] at hc
    subst hc
    have hcert := (hs w hw).knownVal_cert r'' B hknown
    exact ⟨rfl, valCert_lt_of_fresh hs hfresh hcert, hcert⟩

omit [DecidableEq Owner] [DecidableEq Block] in
/-- **With no honest lock, any valid block is acceptable** without a
certificate (the "no certificate learned" branch of Alg. client_propose). -/
theorem acceptable_of_no_lock {s : State V Owner Block}
    (hnolock : ∀ v ∈ Q.honest, (s.locals v).lock = none) (P : Proposal Owner Block) :
    ∀ v ∈ Q.honest, (s.locals v).Acceptable P := by
  intro v hv lk hlk
  rw [hnolock v hv] at hlk
  exact absurd hlk (Option.not_mem_none _)

end LeanLinera
