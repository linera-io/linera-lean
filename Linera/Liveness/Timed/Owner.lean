import Linera.Liveness.Timed.Liveness
import Mathlib.Data.Finset.Max

/-!
# The honest owner and the network

The obligations of `Env` abstract the owner's loop into constants. This
file states the owner as a strategy and the network as a delivery bound,
and discharges the obligations. The owner's *view* at tick `t` is the
state at tick `t − Δ`: after the global stabilisation time, every honest
validator's state is at most `Δ` old when the owner reads it. From its
view the owner *wants* a bounded set of messages delivered
(`Want`, Alg. client_propose):

* a timeout vote from every validator whose deadline has passed;
* the newest timeout certificate it can hold — one recorded by an honest
  validator, or formed from every honest validator's timeout vote — to
  every validator;
* once every honest validator is in a single-leader round it is eligible
  in, its proposal for that round, built by the re-proposal rule from the
  first view in which everyone was in the round, to every validator;
* a validation certificate it can hold for that round — every honest
  validator voted for it, or one reports it as its locking block — to
  every validator.

The network obligation `deliver` says every wanted message is attempted
by its validator within `Δ`, unless it has become stale (a timeout
request for a round the validator has left; a timeout vote is only
attempted after the deadline, so a stale request is dropped). The owner's
proposals are the only proposals signed by it (`honest_sends`).
`OwnerEnv.toEnv` then yields an `Env` with `Δ` and `L` both `2Δ + 1`,
and `OwnerEnv.liveness` follows.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

namespace TExec

variable {cfg : Config Owner Block} {tm : Timeouts}

/-- The honest owner's static data. -/
structure OwnerData (cfg : Config Owner Block) where
  /-- The owner. -/
  o : Owner
  /-- The owner's own block for each round, proposed when nothing is to be re-proposed. -/
  fresh : Round → Block
  /-- Own blocks are valid. -/
  fresh_valid : ∀ r, cfg.Valid (fresh r)
  /-- The super owner's fast block, if any. -/
  fastBlock : Option Block
  /-- The fast block is valid. -/
  fast_valid : ∀ B, fastBlock = some B → cfg.Valid B

/-- Every honest validator is in round `r`. -/
def AllAt (s : State V Owner Block) (r : Round) : Prop := ∀ v ∈ Q.honest, (s.locals v).cur = r

/-- A timeout certificate the owner can hold: recorded by an honest
validator, or formed from every honest validator's timeout vote. -/
def Known (s : State V Owner Block) (τ : Round) : Prop :=
  (∃ v ∈ Q.honest, (s.locals v).tc = some τ) ∨ ∀ v ∈ Q.honest, s.HSig v (.time τ)

/-- The newest timeout certificate the owner can hold. -/
def KnownMax (s : State V Owner Block) (τ : Round) : Prop :=
  Known s τ ∧ ∀ τ', Known s τ' → τ' ≤ τ

/-- A proposal for `r` by the re-proposal rule from the view `s`. -/
def RuleProposal (cfg : Config Owner Block) (ow : OwnerData cfg) (s : State V Owner Block)
    (r : Round) (P : Proposal Owner Block) : Prop :=
  P.round = r ∧ P.owner = ow.o ∧ cfg.Valid P.block ∧ JustRule cfg s P

open Classical in
/-- The owner's proposal for `r` from the view `s`: one by the re-proposal
rule if there is one, else its own block. -/
noncomputable def mkProposal (cfg : Config Owner Block) (ow : OwnerData cfg)
    (s : State V Owner Block) (r : Round) : Proposal Owner Block :=
  if h : ∃ P, RuleProposal cfg ow s r P then Classical.choose h else ⟨r, ow.fresh r, .none, ow.o⟩

omit [DecidableEq Owner] [DecidableEq Block] in
theorem mkProposal_round (ow : OwnerData cfg) (s : State V Owner Block) (r : Round) :
    (mkProposal cfg ow s r).round = r := by
  unfold mkProposal
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · rfl

omit [DecidableEq Owner] [DecidableEq Block] in
theorem mkProposal_owner (ow : OwnerData cfg) (s : State V Owner Block) (r : Round) :
    (mkProposal cfg ow s r).owner = ow.o := by
  unfold mkProposal
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · rfl

omit [DecidableEq Owner] [DecidableEq Block] in
theorem mkProposal_spec (ow : OwnerData cfg) (s : State V Owner Block) (r : Round)
    (h : ∃ P, RuleProposal cfg ow s r P) : RuleProposal cfg ow s r (mkProposal cfg ow s r) := by
  unfold mkProposal
  rw [dite_eq_left h]
  exact Classical.choose_spec h

omit [DecidableEq Owner] in
/-- A validated block is valid. -/
theorem valid_of_valCert {s : State V Owner Block} (hs : Inv cfg s) {B : Block} {ρ : Round}
    (h : s.ValCert B ρ) : cfg.Valid B := by
  obtain ⟨v, hv, e, he, hsg, hm⟩ := h.exists_honest_HSig
  obtain ⟨P, _, hB, _, _, hval⟩ := ((hs v hv).val_ghost e he hsg B ρ hm).prop_elig
  exact hB ▸ hval

omit [DecidableEq Owner] in
open Classical in
/-- **The re-proposal rule always applies**: in a state satisfying the
invariant whose fast locking blocks all carry the super owner's block,
some proposal follows the rule. -/
theorem exists_ruleProposal (ow : OwnerData cfg) {s : State V Owner Block} (hs : Inv cfg s)
    (hfb : ∀ v B', (s.locals v).lb = some (.fast B') → ow.fastBlock = some B' ∧ cfg.fast = true)
    (r : Round) : ∃ P, RuleProposal cfg ow s r P := by
  -- the honest validators holding a certificate as locking block
  let certs := Q.honest.filter (fun v => ∃ B ρ, (s.locals v).lb = some (.cert B ρ))
  let lbRound : V → ℕ := fun v => ((s.locals v).lb.map Locking.round).getD 0
  by_cases hc : certs.Nonempty
  · obtain ⟨w, hw, hmax⟩ := certs.exists_max_image lbRound hc
    obtain ⟨hwh, B, ρ, hlb⟩ := Finset.mem_filter.1 hw
    refine ⟨⟨r, B, .cert B ρ, ow.o⟩, rfl, rfl, valid_of_valCert hs ((hs w hwh).lb_cert B ρ hlb),
      Or.inl ⟨B, ρ, w, hwh, hlb, ?_, rfl, rfl⟩⟩
    intro v hv lb hlb'
    rw [Option.mem_def] at hlb'
    have hρ : lbRound w = ρ := by simp [lbRound, hlb, Locking.round]
    rcases lb with ⟨B', ρ'⟩ | B'
    · have hv' : v ∈ certs := Finset.mem_filter.2 ⟨hv, B', ρ', hlb'⟩
      have := hmax v hv'
      rw [hρ] at this
      simpa [lbRound, hlb', Locking.round] using this
    · change 0 ≤ ρ; exact Nat.zero_le _
  · have hnocert : ∀ v ∈ Q.honest, ∀ B ρ, (s.locals v).lb ≠ some (.cert B ρ) := by
      intro v hv B ρ h
      exact hc ⟨v, Finset.mem_filter.2 ⟨hv, B, ρ, h⟩⟩
    by_cases hf : ∃ w ∈ Q.honest, ∃ B, (s.locals w).lb = some (.fast B)
    · obtain ⟨w, hw, B, hlb⟩ := hf
      obtain ⟨hfbB, hfast⟩ := hfb w B hlb
      refine ⟨⟨r, B, .fast, ow.o⟩, rfl, rfl, ow.fast_valid B hfbB,
        Or.inr (Or.inl ⟨B, w, hw, hlb, ?_, rfl, rfl, hfast⟩)⟩
      intro v hv
      rcases hl : (s.locals v).lb with _ | ⟨B', ρ'⟩ | B'
      · exact Or.inl rfl
      · exact absurd hl (hnocert v hv B' ρ')
      · right
        obtain ⟨h₁, _⟩ := hfb v B' hl
        rw [hfbB, Option.some.injEq] at h₁
        rw [h₁]
    · push Not at hf
      refine ⟨⟨r, ow.fresh r, .none, ow.o⟩, rfl, rfl, ow.fresh_valid r,
        Or.inr (Or.inr ⟨?_, rfl⟩)⟩
      intro v hv
      rcases hl : (s.locals v).lb with _ | ⟨B', ρ'⟩ | B'
      · rfl
      · exact absurd hl (hnocert v hv B' ρ')
      · exact absurd hl (hf v hv B')

variable (ex : TExec (V := V) cfg tm)

open Classical in
/-- The first tick at which every honest validator is in `r`, if any. -/
noncomputable def firstAll (r : Round) : ℕ :=
  if h : ∃ u, AllAt (ex.st u) r then Nat.find h else 0

/-- The owner's proposal for round `r`: by the rule, from the first view in
which every honest validator was in `r`. -/
noncomputable def prop (ow : OwnerData cfg) (r : Round) : Proposal Owner Block :=
  mkProposal cfg ow (ex.st (ex.firstAll r)) r

/-- The owner's proposal for `r` is for `r`. -/
theorem prop_round (ow : OwnerData cfg) (r : Round) : (ex.prop ow r).round = r :=
  mkProposal_round ow _ r

/-- What the owner wants delivered to `v` when its view is the state at tick `u`. -/
def Want (ow : OwnerData cfg) (u : ℕ) (v : V) (i : Input Owner Block) : Prop :=
  v ∈ Q.honest ∧
  ((∃ d, i = .timeout (ex.cur v u) ∧ tm.dur cfg (ex.cur v u) = some d ∧
      ex.entry v u + d ≤ u) ∨
   (∃ τ, i = .timeoutCert τ ∧ KnownMax (ex.st u) τ) ∨
   (∃ r, i = .proposal (ex.prop ow r) ∧ cfg.IsSingle r ∧ cfg.Eligible r ow.o ∧
      AllAt (ex.st u) r) ∨
   (∃ B r, i = .valCert B r ∧ AllAt (ex.st u) r ∧
      ((∀ w ∈ Q.honest, (ex.st u).HSig w (.val B r)) ∨
        ∃ w ∈ Q.honest, ((ex.st u).locals w).lb = some (.cert B r))))

/-- A message no longer relevant: a timeout request for a round the validator has left. -/
def Stale (s : State V Owner Block) (v : V) : Input Owner Block → Prop
  | .timeout ρ => (s.locals v).cur ≠ ρ
  | _ => False

/-- The honest owner and the network. -/
structure OwnerEnv where
  /-- The owner. -/
  ow : OwnerData cfg
  /-- The global stabilisation time. -/
  GST : ℕ
  /-- The delay bound after `GST`: the owner's view is at most `Δ` old, and a wanted
  message is attempted within `Δ`. -/
  Δ : ℕ
  /-- A wanted message is attempted by its validator within `Δ`, unless stale. -/
  deliver : ∀ t, GST ≤ t → ∀ v ∈ Q.honest, ∀ i, ex.Want ow (t - Δ) v i →
    ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧ (ex.act t' = some (v, i) ∨ Stale (ex.st t') v i)
  /-- Every proposal signed by the owner was wanted by it. -/
  honest_sends : ∀ t v P, ex.act t = some (v, .proposal P) → P.owner = ow.o →
    ∃ t', t' ≤ t ∧ ex.Want ow (t' - Δ) v (.proposal P)
  /-- A multi-leader round is left within `2Δ + 1`. -/
  leave_multi : ∀ t, GST ≤ t → ∀ v ∈ Q.honest, ex.cur v t < cfg.firstSL →
    ∃ t', t ≤ t' ∧ t' ≤ t + (2 * Δ + 1) ∧ (ex.cur v t < ex.cur v t' ∨ ex.Done t')
  /-- The owner is the sole leader of single-leader rounds beyond any bound. -/
  leader : ∀ N, ∃ r, N ≤ r ∧ cfg.IsSingle r ∧ ∀ o', cfg.Eligible r o' ↔ o' = ow.o
  /-- Round durations grow. -/
  inc_pos : 0 < tm.inc
  /-- The super owner does not equivocate. -/
  fast_honest : ∀ t v P, ex.act t = some (v, .proposal P) →
    (cfg.IsFast P.round ∨ P.just = .fast) → ow.fastBlock = some P.block
  /-- No fast-round proposal is still in flight after `GST`. -/
  fast_quiet : ∀ t, GST ≤ t → ∀ v P, ex.act t = some (v, .proposal P) → ¬ cfg.IsFast P.round

variable {ex}

omit [DecidableEq Owner] in
/-- Timeout rounds the owner can hold are bounded by the honest validators' rounds. -/
theorem Known.le_sup {s : State V Owner Block} (hs : Inv cfg s) {τ : Round} (h : Known s τ) :
    τ ≤ Q.honest.sup (fun v => (s.locals v).cur) := by
  rcases h with ⟨v, hv, htc⟩ | hsig
  · exact ((hs v hv).tc_lt_cur τ htc).le.trans
      (Finset.le_sup (f := fun v => (s.locals v).cur) hv)
  · obtain ⟨v, hv, _⟩ := Q.exists_honest_mem Q.quorum_honest
    exact ((hs v hv).time_le_cur τ (hsig v hv)).trans
      (Finset.le_sup (f := fun v => (s.locals v).cur) hv)

omit [DecidableEq Owner] in
open Classical in
/-- A certificate the owner can hold has a newest one above it. -/
theorem exists_knownMax {s : State V Owner Block} (hs : Inv cfg s) {τ : Round} (h : Known s τ) :
    ∃ τ', KnownMax s τ' ∧ τ ≤ τ' := by
  set n := Q.honest.sup (fun v => (s.locals v).cur) with hn
  refine ⟨Nat.findGreatest (Known s) n, ⟨Nat.findGreatest_spec (h.le_sup hs) h, ?_⟩,
    Nat.le_findGreatest (h.le_sup hs) h⟩
  intro τ' h'
  exact Nat.le_findGreatest (h'.le_sup hs) h'

/-- A certificate the owner can hold exists. -/
theorem Known.cert {t : ℕ} {τ : Round} (h : Known (ex.st t) τ) : (ex.st t).TimeoutCert τ := by
  rcases h with ⟨v, _, htc⟩ | hsig
  · exact ex.tc_field_cert t v τ htc
  · exact HasCert_of_honest hsig

/-- The view at tick `t + Δ` is the state at `t`. -/
theorem view_add (t Δ : ℕ) : t + Δ - Δ = t := Nat.add_sub_cancel t Δ

/-- **An owner and a network give an environment.** -/
noncomputable def OwnerEnv.toEnv (oe : OwnerEnv ex) : ex.Env where
  GST := oe.GST
  Δ := 2 * oe.Δ + 1
  L := 2 * oe.Δ + 1
  o := oe.ow.o
  prop := fun r => some (ex.prop oe.ow r)
  owner_prop := by
    intro t v P hact ho
    obtain ⟨t', _, hv, hw⟩ := oe.honest_sends t v P hact ho
    rcases hw with ⟨d, hi, _⟩ | ⟨τ, hi, _⟩ | ⟨r, hi, _⟩ | ⟨B, r, hi, _⟩
    · cases hi
    · cases hi
    · simp only [Input.proposal.injEq] at hi
      subst hi
      rw [ex.prop_round]
    · cases hi
  leave_multi := oe.leave_multi
  timeout := by
    intro t hg v hv d hd hdead
    obtain ⟨t', ht', ht'', h⟩ := oe.deliver (t + oe.Δ) (by omega) v hv (.timeout (ex.cur v t))
      (by rw [view_add]; exact ⟨hv, Or.inl ⟨d, rfl, hd, hdead⟩⟩)
    by_cases hmv : ex.cur v t < ex.cur v t'
    · exact ⟨t', by omega, by omega, Or.inr (Or.inl hmv)⟩
    have hcur : ex.cur v t' = ex.cur v t := le_antisymm (not_lt.1 hmv) (ex.cur_mono v (by omega))
    rcases h with hact | hst
    · by_cases hfin : ∃ B, ((ex.st t').locals v).finalized = some B
      · obtain ⟨B, hB⟩ := hfin
        exact ⟨t', by omega, by omega, Or.inr (Or.inr (ex.done_of_finalized hv hB))⟩
      push Not at hfin
      by_cases htv : ((ex.st t').locals v).timeoutVote = some (ex.cur v t)
      · exact ⟨t', by omega, by omega, Or.inl ((ex.inv t' v hv).timeoutVote_sig _ htv)⟩
      have hok : ((ex.st t').locals v).timeoutOk (ex.cur v t) :=
        ⟨Option.eq_none_iff_forall_ne_some.2 hfin, hcur.symm, htv⟩
      refine ⟨t' + 1, by omega, by omega, Or.inl ?_⟩
      rw [ex.succ, hact]
      simp only [stepOpt, Linera.step, ite_eq_left hok, Option.getD_some]
      rw [HSig_sign]; exact Or.inr ⟨rfl, rfl⟩
    · exact absurd hcur hst
  tc_known := by
    intro t hg v hv τ hτ w hw
    obtain ⟨τ', hmax, hle⟩ := exists_knownMax (ex.inv t) (Or.inl ⟨v, hv, hτ⟩)
    obtain ⟨t', ht', ht'', h⟩ := oe.deliver (t + oe.Δ) (by omega) w hw (.timeoutCert τ')
      (by rw [view_add]; exact ⟨hw, Or.inr (Or.inl ⟨τ', rfl, hmax⟩)⟩)
    rcases h with hact | hst
    swap
    · exact absurd hst id
    by_cases hfin : ∃ B, ((ex.st t').locals w).finalized = some B
    · obtain ⟨B, hB⟩ := hfin
      exact ⟨t', by omega, by omega, Or.inr (ex.done_of_finalized hw hB)⟩
    push Not at hfin
    by_cases hold : ∃ τ'' ∈ ((ex.st t').locals w).tc, τ' ≤ τ''
    · obtain ⟨τ'', htc'', hle''⟩ := hold
      have := (ex.inv t' w hw).tc_lt_cur τ'' htc''
      change τ'' < ex.cur w t' at this
      exact ⟨t', by omega, by omega, Or.inl (by omega)⟩
    push Not at hold
    have hok : ((ex.st t').locals w).tcOk τ' := ⟨Option.eq_none_iff_forall_ne_some.2 hfin, hold⟩
    have hcert : (ex.st t').TimeoutCert τ' := ex.HasCert_mono (by omega) hmax.1.cert
    have hc : (ex.st t').TimeoutCert τ' ∧ ((ex.st t').locals w).tcOk τ' := ⟨hcert, hok⟩
    refine ⟨t' + 1, by omega, by omega, Or.inl ?_⟩
    change τ < ((ex.st (t' + 1)).locals w).cur
    rw [ex.succ, hact]
    simp only [stepOpt, Linera.step, ite_eq_left hc, Option.getD_some,
      locals_set_self, Local.afterTimeoutCert]
    omega
  tc_honest := by
    intro t hg τ hsig w hw
    obtain ⟨τ', hmax, hle⟩ := exists_knownMax (ex.inv t) (Or.inr hsig)
    obtain ⟨t', ht', ht'', h⟩ := oe.deliver (t + oe.Δ) (by omega) w hw (.timeoutCert τ')
      (by rw [view_add]; exact ⟨hw, Or.inr (Or.inl ⟨τ', rfl, hmax⟩)⟩)
    rcases h with hact | hst
    swap
    · exact absurd hst id
    by_cases hfin : ∃ B, ((ex.st t').locals w).finalized = some B
    · obtain ⟨B, hB⟩ := hfin
      exact ⟨t', by omega, by omega, Or.inr (ex.done_of_finalized hw hB)⟩
    push Not at hfin
    by_cases hold : ∃ τ'' ∈ ((ex.st t').locals w).tc, τ' ≤ τ''
    · obtain ⟨τ'', htc'', hle''⟩ := hold
      have := (ex.inv t' w hw).tc_lt_cur τ'' htc''
      change τ'' < ex.cur w t' at this
      exact ⟨t', by omega, by omega, Or.inl (by omega)⟩
    push Not at hold
    have hok : ((ex.st t').locals w).tcOk τ' := ⟨Option.eq_none_iff_forall_ne_some.2 hfin, hold⟩
    have hcert : (ex.st t').TimeoutCert τ' := ex.HasCert_mono (by omega) hmax.1.cert
    have hc : (ex.st t').TimeoutCert τ' ∧ ((ex.st t').locals w).tcOk τ' := ⟨hcert, hok⟩
    refine ⟨t' + 1, by omega, by omega, Or.inl ?_⟩
    change τ < ((ex.st (t' + 1)).locals w).cur
    rw [ex.succ, hact]
    simp only [stepOpt, Linera.step, ite_eq_left hc, Option.getD_some,
      locals_set_self, Local.afterTimeoutCert]
    omega
  propose := by
    classical
    intro t hg r hr hsole hall _
    have hex : ∃ u, AllAt (ex.st u) r := ⟨t, hall⟩
    have hfirst : ex.firstAll r = Nat.find hex := by unfold firstAll; rw [dite_eq_left hex]
    have hall₀ : AllAt (ex.st (ex.firstAll r)) r := by rw [hfirst]; exact Nat.find_spec hex
    have hle₀ : ex.firstAll r ≤ t := by rw [hfirst]; exact Nat.find_min' hex hall
    have hmin₀ : ∀ u, AllAt (ex.st u) r → ex.firstAll r ≤ u := by
      intro u hu; rw [hfirst]; exact Nat.find_min' hex hu
    have hrule := mkProposal_spec oe.ow (ex.st (ex.firstAll r)) r
      (exists_ruleProposal oe.ow (ex.inv _) (ex.lb_fast_block' oe.fast_honest _) r)
    obtain ⟨hPr, hPo, hPv, hjust⟩ := hrule
    refine ⟨ex.prop oe.ow r, ex.firstAll r, hall₀, by omega, rfl, hPr, hPo, hPv, hjust, ?_, ?_⟩
    · intro v hv
      obtain ⟨t', ht', ht'', h⟩ := oe.deliver (t + oe.Δ) (by omega) v hv
        (.proposal (ex.prop oe.ow r))
        (by rw [view_add]; exact ⟨hv, Or.inr (Or.inr (Or.inl ⟨r, rfl, hr, (hsole _).2 rfl, hall⟩))⟩)
      rcases h with hact | hst
      · exact ⟨t', by omega, by omega, hact⟩
      · exact absurd hst id
    · intro t' ht' v hact
      obtain ⟨t'', ht'', hv', hw⟩ := oe.honest_sends t' v _ hact hPo
      rcases hw with ⟨d, hi, _⟩ | ⟨τ, hi, _⟩ | ⟨r', hi, _, _, hall'⟩ | ⟨B, r'', hi, _⟩
      · cases hi
      · cases hi
      · simp only [Input.proposal.injEq] at hi
        have hr' : r' = r := by
          have h1 : (ex.prop oe.ow r').round = r' := ex.prop_round oe.ow r'
          rw [← hi] at h1
          exact h1.symm.trans hPr
        subst hr'
        have := hmin₀ _ hall'
        omega
      · cases hi
  cert := by
    intro t hg r hr hsole B hall hev v hv
    obtain ⟨t', ht', ht'', h⟩ := oe.deliver (t + oe.Δ) (by omega) v hv (.valCert B r)
      (by rw [view_add]; exact ⟨hv, Or.inr (Or.inr (Or.inr ⟨B, r, rfl, hall, hev⟩))⟩)
    rcases h with hact | hst
    · exact ⟨t', by omega, by omega, hact⟩
    · exact absurd hst id
  leader := oe.leader
  inc_pos := oe.inc_pos
  fastBlock := oe.ow.fastBlock
  fast_honest := oe.fast_honest
  fast_quiet := oe.fast_quiet

/-- **Liveness with the owner's loop and the network as the only
assumptions** (paper, Theorem liveness). -/
theorem OwnerEnv.liveness (oe : OwnerEnv ex) : ∃ t, ex.Done t := oe.toEnv.liveness

end TExec

end Linera
