import Linera.Liveness.Timed.Env

/-!
# Liveness under partial synchrony

The paper's Theorem liveness for the timed model: under the environment
`Env`, some block is eventually confirmed. The proof follows the paper:

* **round growth** (`reach_round`): every round is eventually reached by
  every honest validator — multi-leader rounds are left within `L`, and a
  single-leader round is left within its duration plus `2Δ`, because its
  deadline passes at every honest validator, each then signs a timeout
  vote, the certificate forms, and it reaches everyone;
* **a long enough honest round**: the schedule gives a single-leader round
  `r` led solely by the honest owner, beyond every round held at `GST`,
  and long enough (`d ≥ Δ + 2L + 2`, by linear growth); the first timeout
  certificate for `r − 1` appears after `GST`, every honest validator
  enters `r` within `Δ` of it, and none can leave `r` before `d` ticks
  after it, since timeout votes need the deadline;
* **progress** (`WinAt`, the window invariant): in that window every honest
  validator keeps the lock and latest vote it had when the owner read the
  locking blocks, or has validated the owner's block, or has confirmed
  it; so the proposal is accepted by all (`good_round_confirms`'s
  freshness and the re-proposal rule), the validation certificate forms,
  is delivered, and every honest validator confirms.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

namespace TExec

variable {cfg : Config Owner Block} {tm : Timeouts} {ex : TExec (V := V) cfg tm} (env : ex.Env)

/-! ## Round growth -/

/-- After a timeout certificate recorded by an honest validator, every
honest validator passes its round within `Δ`, or a block is confirmed. -/
theorem Env.all_gt_of_known {t : ℕ} (hg : env.GST ≤ t) {v : V} (hv : v ∈ Q.honest) {τ : ℕ}
    (hτ : τ ∈ ((ex.st t).locals v).tc) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ w ∈ Q.honest, τ < ex.cur w t') := by
  refine ⟨t + env.Δ, Nat.le_add_right _ _, ?_⟩
  by_cases hd : ex.Done (t + env.Δ)
  · exact Or.inl hd
  · right
    intro w hw
    obtain ⟨t', _, ht', h⟩ := env.tc_known t hg v hv τ hτ w hw
    rcases h with h | h
    · exact h.trans_le (ex.cur_mono w ht')
    · exact absurd (Done.mono ex ht' h) hd

/-- After every honest validator signed a timeout vote for `τ`, every
honest validator passes `τ` within `Δ`, or a block is confirmed. -/
theorem Env.all_gt_of_signed {t τ : ℕ} (hg : env.GST ≤ t)
    (hsig : ∀ v ∈ Q.honest, (ex.st t).HSig v (.time τ)) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ w ∈ Q.honest, τ < ex.cur w t') := by
  refine ⟨t + env.Δ, Nat.le_add_right _ _, ?_⟩
  by_cases hd : ex.Done (t + env.Δ)
  · exact Or.inl hd
  · right
    intro w hw
    obtain ⟨t', _, ht', h⟩ := env.tc_honest t hg τ hsig w hw
    rcases h with h | h
    · exact h.trans_le (ex.cur_mono w ht')
    · exact absurd (Done.mono ex ht' h) hd

/-- Some honest validator past the single-leader round `r` means some
honest validator recorded a timeout certificate for at least `r`, after
which everyone passes `r` within `Δ`, or a block is confirmed. -/
theorem Env.all_gt_of_past {r t : ℕ} (hr : cfg.IsSingle r) (hg : env.GST ≤ t) {w : V}
    (hw : w ∈ Q.honest) (hlt : r < ex.cur w t) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ v ∈ Q.honest, r < ex.cur v t') := by
  rcases ex.le_round_or_tc_field hr t with h | ⟨w', hw', τ, hτ, hrτ⟩
  · exact absurd (h w hw) (not_le.2 hlt)
  · obtain ⟨t', ht', h⟩ := env.all_gt_of_known hg hw' hτ
    exact ⟨t', ht', h.imp id (fun h v hv => hrτ.trans_lt (h v hv))⟩

/-- A single-leader round is passed by every honest validator, or a block
is confirmed (paper, Lemma round-growth). -/
theorem Env.advance_single {r t : ℕ} (hr : cfg.IsSingle r) (hg : env.GST ≤ t)
    (hall : ∀ v ∈ Q.honest, r ≤ ex.cur v t) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ v ∈ Q.honest, r < ex.cur v t') := by
  by_cases hex : ∃ w ∈ Q.honest, r < ex.cur w t
  · obtain ⟨w, hw, hlt⟩ := hex
    exact env.all_gt_of_past hr hg hw hlt
  push Not at hex
  have heq : ∀ v ∈ Q.honest, ex.cur v t = r := fun v hv => le_antisymm (hex v hv) (hall v hv)
  obtain ⟨d, hd⟩ : ∃ d, tm.dur cfg r = some d := ⟨_, dur_single hr⟩
  -- at `T`, every honest validator has signed `Time(r)`, passed `r`, or confirmed
  have hT : ∀ v ∈ Q.honest, (ex.st (t + d + env.Δ)).HSig v (.time r) ∨
      r < ex.cur v (t + d + env.Δ) ∨ ex.Done (t + d + env.Δ) := by
    intro v hv
    by_cases hlt : r < ex.cur v (t + d)
    · exact Or.inr (Or.inl (hlt.trans_le (ex.cur_mono v (Nat.le_add_right _ _))))
    have hcur : ex.cur v (t + d) = r :=
      le_antisymm (not_lt.1 hlt) ((hall v hv).trans (ex.cur_mono v (Nat.le_add_right _ _)))
    have hentry : ex.entry v (t + d) ≤ t := ex.entry_le_of_cur_eq v (by rw [heq v hv, hcur])
    obtain ⟨t', _, ht'', h⟩ := env.timeout (t + d) (hg.trans (Nat.le_add_right _ _)) v hv d
      (by rw [hcur]; exact hd) (by omega)
    rw [hcur] at h
    rcases h with h | h | h
    · exact Or.inl (ex.HSig_mono (by omega) h)
    · exact Or.inr (Or.inl (h.trans_le (ex.cur_mono v (by omega))))
    · exact Or.inr (Or.inr (Done.mono ex (by omega) h))
  by_cases hdone : ex.Done (t + d + env.Δ)
  · exact ⟨_, by omega, Or.inl hdone⟩
  by_cases hex' : ∃ w ∈ Q.honest, r < ex.cur w (t + d + env.Δ)
  · obtain ⟨w, hw, hlt⟩ := hex'
    obtain ⟨t', ht', h⟩ := env.all_gt_of_past hr (t := t + d + env.Δ) (by omega) hw hlt
    exact ⟨t', by omega, h⟩
  push Not at hex'
  have hsig : ∀ v ∈ Q.honest, (ex.st (t + d + env.Δ)).HSig v (.time r) := by
    intro v hv
    rcases hT v hv with h | h | h
    · exact h
    · exact absurd h (not_lt.2 (hex' v hv))
    · exact absurd h hdone
  obtain ⟨t', ht', h⟩ := env.all_gt_of_signed (t := t + d + env.Δ) (by omega) hsig
  exact ⟨t', by omega, h⟩

/-- A multi-leader round is passed by every honest validator of a list, or
a block is confirmed. -/
theorem Env.advance_multi_list {r t : ℕ} (hr : r < cfg.firstSL) (hg : env.GST ≤ t)
    (L : List V) (hL : ∀ v ∈ L, v ∈ Q.honest) (hall : ∀ v ∈ L, r ≤ ex.cur v t) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ v ∈ L, r < ex.cur v t') := by
  induction L with
  | nil => exact ⟨t, le_rfl, Or.inr (fun v hv => absurd hv List.not_mem_nil)⟩
  | cons v L ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
      (fun w hw => hall w (List.mem_cons_of_mem _ hw))
    rcases h₁ with h₁ | h₁
    · exact ⟨t₁, ht₁, Or.inl h₁⟩
    have hv := hL v (List.mem_cons_self ..)
    by_cases hlt : r < ex.cur v t₁
    · refine ⟨t₁, ht₁, Or.inr (fun w hw => ?_)⟩
      rw [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hlt
      · exact h₁ w hw
    have hcur : ex.cur v t₁ = r :=
      le_antisymm (not_lt.1 hlt) ((hall v (List.mem_cons_self ..)).trans (ex.cur_mono v ht₁))
    obtain ⟨t₂, ht₂, _, h₂⟩ := env.leave_multi t₁ (hg.trans ht₁) v hv (hcur ▸ hr)
    refine ⟨t₂, ht₁.trans ht₂, ?_⟩
    rcases h₂ with h₂ | h₂
    · right
      intro w hw
      rw [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [hcur] at h₂; exact h₂
      · exact (h₁ w hw).trans_le (ex.cur_mono w ht₂)
    · exact Or.inl h₂

/-- **Eventual round growth**: every round is eventually reached by every
honest validator, or a block is confirmed. -/
theorem Env.reach_round (r : ℕ) :
    ∃ t, env.GST ≤ t ∧ (ex.Done t ∨ ∀ v ∈ Q.honest, r ≤ ex.cur v t) := by
  induction r with
  | zero => exact ⟨env.GST, le_rfl, Or.inr (fun v _ => Nat.zero_le _)⟩
  | succ r ih =>
    obtain ⟨t, hg, h⟩ := ih
    rcases h with h | h
    · exact ⟨t, hg, Or.inl h⟩
    by_cases hr : cfg.IsSingle r
    · obtain ⟨t', ht', h'⟩ := env.advance_single hr hg h
      exact ⟨t', hg.trans ht', h'.imp id (fun h' v hv => h' v hv)⟩
    · have hr' : r < cfg.firstSL := not_le.1 hr
      obtain ⟨L, _, hall, hL⟩ := exists_honest_list (V := V)
      obtain ⟨t', ht', h'⟩ := env.advance_multi_list hr' hg L hL (fun v hv => h v (hL v hv))
      exact ⟨t', hg.trans ht', h'.imp id (fun h' v hv => h' v (hall v hv))⟩

/-! ## The window invariant of the good round -/

/-- In the good round `r`, relative to the state `s₀` in which the owner
read the locking blocks: the validator still has the lock and latest
validation vote of `s₀` and a locking block below `r`; or it has validated
the owner's block `P.block` in `r` (and its locking block is below `r`);
or it has confirmed it. -/
def WinAt (s₀ s : State V Owner Block) (P : Proposal Owner Block) (r : Round) (v : V) : Prop :=
  ((s.locals v).lock = (s₀.locals v).lock ∧ (s.locals v).valVote = (s₀.locals v).valVote ∧
    ∀ lb ∈ (s.locals v).lb, lb.round < r) ∨
  (s.HSig v (.val P.block r) ∧ (s.locals v).valVote = some (P.block, r) ∧
    ∀ lb ∈ (s.locals v).lb, lb.round < r) ∨
  s.HSig v (.conf P.block r)

/-- The window invariant is kept by every step, as long as every honest
validator is at or below `r`, `v` is at `r`, and every validation vote in
`r` is for `P.block`. -/
theorem winAt_step {s₀ s s' : State V Owner Block} {P : Proposal Owner Block} {r : Round}
    (hr : cfg.firstSL < r) (hnf : ¬ cfg.IsFast r) (hs : Inv cfg s) {v : V} (hv : v ∈ Q.honest)
    (hcur : (s.locals v).cur = r) (hle : ∀ w ∈ Q.honest, (s.locals w).cur ≤ r)
    {w : V} {i : Input Owner Block} (hst : step cfg s w i = some s')
    (hq : ∀ P', i = .proposal P' → ¬ cfg.IsFast P'.round)
    (hvalP : ∀ u ∈ Q.honest, ∀ B, s'.HSig u (.val B r) → B = P.block)
    (hwin : WinAt s₀ s P r v) : WinAt s₀ s' P r v := by
  by_cases hwv : w = v
  swap
  · -- another validator: `v`'s local state is unchanged and signatures persist
    have hl := step_locals_of_ne hst (Ne.symm hwv)
    unfold WinAt at hwin ⊢
    rw [hl]
    rcases hwin with h | ⟨h₁, h₂, h₃⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨step_HSig hst h₁, h₂, h₃⟩)
    · exact Or.inr (Or.inr (step_HSig hst h))
  subst hwv
  cases i with
  | proposal P' =>
    rw [Linera.step] at hst
    split_ifs at hst with hf hok hpre hacc <;> simp only [Option.some.injEq] at hst <;> subst hst
    · exact absurd hf (hq P' rfl)
    · -- validated: the proposal is for `r` and for `P.block`
      have hro := hpre.1.2.2.2.1
      unfold Local.roundOk at hro
      have hPr : P'.round = r := by
        split_ifs at hro with hle'
        · rw [hcur] at hro; omega
        · rw [hro, hcur]
      have hsig : ((s.set w ((s.locals w).afterVal P')).sign
          ⟨w, .val P'.block P'.round, (s.locals w).lock, some P'⟩).HSig w (.val P'.block r) := by
        rw [HSig_sign]; exact Or.inr ⟨rfl, by rw [hPr]⟩
      have hB : P'.block = P.block := hvalP w hv P'.block hsig
      unfold WinAt at hwin ⊢
      rcases hwin with ⟨_, _, hlb⟩ | ⟨_, hvv, _⟩ | h
      · right; left
        refine ⟨hB ▸ hsig, ?_, ?_⟩
        · simp only [locals_sign, locals_set_self, Local.afterVal, hB, hPr]
        · simp only [locals_sign, locals_set_self, Local.afterVal]
          exact Local.lbAfter_lt hPr hpre.1.2.2.1 hnf hlb
      · exfalso
        have := hpre.1.2.2.2.2.1 (P.block, r) (by rw [hvv]; rfl)
        rw [hPr] at this; exact lt_irrefl _ this
      · exact Or.inr (Or.inr (h.sign _))
    · -- noted without a vote: only the round changes
      unfold WinAt at hwin ⊢
      simp only [locals_set_self, Local.afterBump]
      exact hwin
  | valCert B' ρ =>
    rw [Linera.step] at hst
    split_ifs at hst with hok hcv <;> simp only [Option.some.injEq] at hst <;> subst hst
    · -- a confirmation in `r` for `P.block`
      have hρ : ρ = r := by
        have h1 : r ≤ ρ := by
          have := hcv; unfold Local.confVotes at this; rw [hcur] at this; exact this
        obtain ⟨u, hu, hsig⟩ := hok.1.exists_honest_HSig
        have h2 := (hs u hu).val_le_cur B' ρ hsig
        exact le_antisymm (h2.trans (hle u hu)) h1
      subst hρ
      obtain ⟨u, hu, hsigu⟩ := hok.1.exists_honest_HSig
      have hB : B' = P.block := hvalP u hu B' (hsigu.sign _)
      unfold WinAt
      right; right
      rw [← hB, HSig_sign]
      exact Or.inr ⟨rfl, rfl⟩
    · -- recorded without a vote: a locking block below `r`
      have hρ : ρ < r := by
        have := hcv; unfold Local.confVotes at this; rw [hcur] at this; exact not_le.1 this
      unfold WinAt at hwin ⊢
      simp only [locals_set_self, Local.afterValCert, ite_eq_right hcv]
      rcases hwin with ⟨h₁, h₂, _⟩ | ⟨h₁, h₂, _⟩ | h
      · left
        refine ⟨h₁, h₂, ?_⟩
        intro lb hlb
        simp only [Option.mem_def, Option.some.injEq] at hlb
        subst hlb; exact hρ
      · right; left
        refine ⟨h₁, h₂, ?_⟩
        intro lb hlb
        simp only [Option.mem_def, Option.some.injEq] at hlb
        subst hlb; exact hρ
      · exact Or.inr (Or.inr h)
  | confCert B' ρ =>
    rw [Linera.step] at hst
    split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
    unfold WinAt at hwin ⊢
    simp only [locals_set_self, Local.afterConfCert]
    exact hwin
  | timeout ρ =>
    rw [Linera.step] at hst
    split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
    unfold WinAt at hwin ⊢
    simp only [locals_sign, locals_set_self, Local.afterTimeout]
    rcases hwin with h | ⟨h₁, h₂, h₃⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h₁.sign _, h₂, h₃⟩)
    · exact Or.inr (Or.inr (h.sign _))
  | timeoutCert ρ =>
    rw [Linera.step] at hst
    split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
    unfold WinAt at hwin ⊢
    simp only [locals_set_self, Local.afterTimeoutCert]
    exact hwin

/-! ## The liveness theorem -/

include env in
/-- **Liveness** (paper, Theorem liveness): under the environment — an
honest active owner, partial synchrony after `GST`, a schedule that
designates the owner as sole leader beyond any round, growing round
durations, and a super owner that does not equivocate — some block is
eventually confirmed. -/
theorem Env.liveness : ∃ t, ex.Done t := by
  classical
  obtain ⟨w₀, hw₀, _⟩ := Q.exists_honest_mem Q.quorum_honest
  -- rounds held at GST are bounded
  have hRle : ∀ v ∈ Q.honest, ex.cur v env.GST ≤ Q.honest.sup (fun v => ex.cur v env.GST) :=
    fun v hv => Finset.le_sup (f := fun v => ex.cur v env.GST) hv
  set R := Q.honest.sup (fun v => ex.cur v env.GST) with hR
  -- the good round: led solely by the owner, beyond every round held at GST, and long
  obtain ⟨r, hrN, hrs, hsole⟩ := env.leader (max (R + 2) (cfg.firstSL + env.Δ + 2 * env.L + 3))
  have hR2 : R + 2 ≤ r := (le_max_left _ _).trans hrN
  have hrSL : cfg.firstSL + env.Δ + 2 * env.L + 3 ≤ r := (le_max_right _ _).trans hrN
  have hr1 : cfg.firstSL < r := by omega
  obtain ⟨d, hd⟩ : ∃ d, tm.dur cfg r = some d := ⟨_, dur_single hrs⟩
  have hdbig : env.Δ + 2 * env.L + 3 ≤ d := by
    rw [dur_single hrs] at hd
    simp only [Option.some.injEq] at hd
    have h2 : r - cfg.firstSL ≤ (r - cfg.firstSL) * tm.inc :=
      Nat.le_mul_of_pos_right _ env.inc_pos
    omega
  have hrs' : cfg.IsSingle (r - 1) := by unfold Config.IsSingle at *; omega
  have hnfr : ¬ cfg.IsFast r := not_isFast_of_isSingle hrs
  -- every honest validator reaches `r`
  obtain ⟨t, _, ht⟩ := env.reach_round r
  rcases ht with ht | ht
  · exact ⟨t, ht⟩
  -- the first tick at which some honest validator holds `r`
  have hex : ∃ t', ∃ v ∈ Q.honest, r ≤ ex.cur v t' := ⟨t, w₀, hw₀, ht w₀ hw₀⟩
  obtain ⟨tc, ⟨w₁, hw₁, hw₁r⟩, htc_min⟩ : ∃ tc, (∃ v ∈ Q.honest, r ≤ ex.cur v tc) ∧
      ∀ u, (∃ v ∈ Q.honest, r ≤ ex.cur v u) → tc ≤ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun u hu => Nat.find_min' hex hu⟩
  -- it is after GST
  have htc_gst : env.GST < tc := by
    by_contra hle; push Not at hle
    have h2 := ex.cur_mono w₁ hle
    have h3 := hRle w₁ hw₁
    omega
  -- a validator at or beyond `r` entered it at or after `tc`
  have hentry_ge : ∀ v ∈ Q.honest, ∀ u, r ≤ ex.cur v u → tc ≤ ex.entry v u := by
    intro v hv u hu
    have hce := ex.cur_entry v u
    exact htc_min _ ⟨v, hv, by rw [hce]; exact hu⟩
  -- no honest timeout vote for `r` until `tc + d`
  have hno_time : ∀ u, u ≤ tc + d → ∀ v ∈ Q.honest, ¬ (ex.st u).HSig v (.time r) := by
    intro u hu v hv hsig
    obtain ⟨u', hu', hact, hcur⟩ := ex.log_time_act u v r hsig
    obtain ⟨d', hd', hdead⟩ := ex.timeout_ok u' v r hact
    change tm.dur cfg (ex.cur v u') = some d' at hd'
    rw [hcur, hd] at hd'
    simp only [Option.some.injEq] at hd'
    subst hd'
    have hdead' : ex.entry v u' + d ≤ u' := hdead
    have := hentry_ge v hv u' hcur.ge
    omega
  -- hence nobody is beyond `r` until `tc + d`
  have hle_r : ∀ u, u ≤ tc + d → ∀ v ∈ Q.honest, ex.cur v u ≤ r := by
    intro u hu v hv
    rcases ex.le_round_or_tc hrs u with h | ⟨t', ht', htc'⟩
    · exact h v hv
    · obtain ⟨u', hu', hsig⟩ := htc'.exists_honest_HSig
      exact absurd hsig (hno_time t' (by omega) u' hu')
  -- everybody is at `r` from `tc + Δ` on, unless done: `w₁` passed `r - 1`, so some honest
  -- validator recorded a timeout certificate for at least `r - 1`, which reaches everyone
  have hat : ∀ v ∈ Q.honest, r ≤ ex.cur v (tc + env.Δ) ∨ ex.Done (tc + env.Δ) := by
    intro v hv
    rcases ex.le_round_or_tc_field hrs' tc with h | ⟨w', hw', τ, hτ, hrτ⟩
    · exact absurd (h w₁ hw₁) (by omega)
    obtain ⟨t', _, ht'', h⟩ := env.tc_known tc htc_gst.le w' hw' τ hτ v hv
    rcases h with h | h
    · left; have := ex.cur_mono v ht''; omega
    · right; exact Done.mono ex ht'' h
  by_cases hdone₁ : ex.Done (tc + env.Δ)
  · exact ⟨_, hdone₁⟩
  have hcur_w : ∀ u, tc + env.Δ ≤ u → u ≤ tc + d → ∀ v ∈ Q.honest, ex.cur v u = r := by
    intro u hu₁ hu₂ v hv
    refine le_antisymm (hle_r u hu₂ v hv) ?_
    rcases hat v hv with h | h
    · exact h.trans (ex.cur_mono v hu₁)
    · exact absurd h hdone₁
  -- the owner's proposal
  obtain ⟨P, tq, hcurq, htq₂, hprop, hPr, hPo, hPv, hrule, hatt, hbefore⟩ :=
    env.propose (tc + env.Δ) (by omega) r hrs hsole
      (fun v hv => hcur_w _ le_rfl (by omega) v hv) hdone₁
  have htq_d : tq ≤ tc + d := by omega
  -- everybody stays at `r` from `tq` to `tc + d`
  have hcur_w' : ∀ u, tq ≤ u → u ≤ tc + d → ∀ v ∈ Q.honest, ex.cur v u = r := by
    intro u hu₁ hu₂ v hv
    exact le_antisymm (hle_r u hu₂ v hv) ((hcurq v hv).symm ▸ ex.cur_mono v hu₁)
  -- `tq` is after GST, since nobody held `r` at GST
  have htq_gst : env.GST < tq := by
    by_contra hle; push Not at hle
    have h2 := ex.cur_mono w₀ hle
    have h3 := hRle w₀ hw₀
    have h4 := hcurq w₀ hw₀
    omega
  -- every honest validation vote in `r` is for `P.block`, and none exists before `tq`
  have hvalP : ∀ u, ∀ v ∈ Q.honest, ∀ B, (ex.st u).HSig v (.val B r) → B = P.block := by
    intro u v hv B h
    obtain ⟨P', _, hP', hB, _, _, _⟩ := ex.val_of_sole env hsole hv h
    rw [hprop, Option.some.injEq] at hP'; subst hP'; exact hB.symm
  have hno_val : ∀ u, u ≤ tq → ∀ v ∈ Q.honest, ∀ B, ¬ (ex.st u).HSig v (.val B r) := by
    intro u hu v hv B h
    obtain ⟨P', t', hP', _, _, ht', hact⟩ := ex.val_of_sole env hsole hv h
    rw [hprop, Option.some.injEq] at hP'; subst hP'
    exact hbefore t' (by omega) v hact
  -- locking blocks at `tq` are below `r`
  have hlb_lt : ∀ v ∈ Q.honest, ∀ lb ∈ ((ex.st tq).locals v).lb, lb.round < r := by
    intro v hv lb hlb
    rcases lb with ⟨B, ρ⟩ | B
    · have hc := (ex.inv tq v hv).lb_cert B ρ hlb
      obtain ⟨u, hu, hsig⟩ := hc.exists_honest_HSig
      have h1 : ρ ≤ ex.cur u tq := (ex.inv tq u hu).val_le_cur B ρ hsig
      rw [hcurq u hu] at h1
      rcases Nat.lt_or_eq_of_le h1 with h | rfl
      · exact h
      · exact absurd hsig (hno_val tq le_rfl u hu B)
    · change 0 < r; omega
  -- the proposal is well formed from `tq` on
  have hwf : ∀ u, tq ≤ u → P.WellFormed cfg (ex.st u) r := by
    intro u hu
    refine ⟨hPr, hnfr, (hsole P.owner).2 hPo, hPv, ?_, ?_⟩
    · unfold Local.JustOk
      rcases hrule with ⟨B, ρ, w, hw, hlbw, _, hj, hB⟩ | ⟨B, w, hw, hlbw, _, hj, hB, hfast⟩ |
        ⟨_, hj⟩
      · rw [hj]; exact ⟨hB.symm, by rw [hPr]; exact hlb_lt w hw _ hlbw⟩
      · rw [hj]; exact ⟨hfast, hPr ▸ hnfr⟩
      · rw [hj]; trivial
    · rcases hrule with ⟨B, ρ, w, hw, hlbw, _, hj, hB⟩ | ⟨B, w, hw, hlbw, _, hj, hB, hfast⟩ |
        ⟨_, hj⟩
      · unfold State.JustCert; rw [hj]
        exact ex.HasCert_mono hu ((ex.inv tq w hw).lb_cert B ρ hlbw)
      · unfold State.JustCert; rw [hj]; trivial
      · unfold State.JustCert; rw [hj]; trivial
  -- the proposal passes every lock as of `tq`
  have hacc_tq : ∀ v ∈ Q.honest, ((ex.st tq).locals v).lockOk cfg P := by
    rcases hrule with ⟨B, ρ, w, hw, hlbw, hmax, hj, hB⟩ | ⟨B, w, hw, hlbw, hall, hj, hB, hfast⟩ |
      ⟨hnone, hj⟩
    · exact acceptable_of_highest_lb (ex.inv tq) hw hlbw hmax P hj hB
    · refine acceptable_of_fast_lb (cfg := cfg) ?_ P hj hB
      intro v hv lk hlk
      have hvi := ex.inv tq v hv
      obtain ⟨lb, hlb, hle⟩ := hvi.conf_bound lk.1 lk.2 (hvi.lock_conf lk hlk)
      rcases hall v hv with hn | hf
      · rw [hn] at hlb; exact absurd hlb (Option.not_mem_none _)
      · rw [hf, Option.mem_def, Option.some.injEq] at hlb
        subst hlb
        have h0 : lk.2 = 0 := Nat.le_zero.1 hle
        exact ⟨hvi.lock_fast lk hlk B hf, ⟨hfast, h0⟩⟩
    · intro v hv lk hlk
      obtain ⟨lb, hlb, _⟩ :=
        (ex.inv tq v hv).conf_bound lk.1 lk.2 ((ex.inv tq v hv).lock_conf lk hlk)
      rw [hnone v hv] at hlb; exact absurd hlb (Option.not_mem_none _)
  -- the window invariant throughout `[tq, tc + d]`
  have hwin : ∀ v ∈ Q.honest, ∀ u, tq ≤ u → u ≤ tc + d →
      WinAt (ex.st tq) (ex.st u) P r v := by
    intro v hv u hu₁ hu₂
    induction u, hu₁ using Nat.le_induction with
    | base => exact Or.inl ⟨rfl, rfl, hlb_lt v hv⟩
    | succ u hu ih =>
      have ih := ih (by omega)
      rw [ex.succ]
      rcases hact : ex.act u with _ | ⟨w, i⟩
      · exact ih
      simp only [stepOpt]
      rcases hst : step cfg (ex.st u) w i with _ | s'
      · exact ih
      simp only [Option.getD_some]
      refine winAt_step hr1 hnfr (ex.inv u) hv (hcur_w' u (by omega) (by omega) v hv)
        (fun w' hw' => hle_r u (by omega) w' hw') hst
        (fun P' hi => by subst hi; exact env.fast_quiet u (by omega) w P' hact) ?_ ih
      intro u' hu' B h
      have : (ex.st (u + 1)).HSig u' (.val B r) := by
        rw [ex.succ, hact]; simp only [stepOpt, hst, Option.getD_some]; exact h
      exact hvalP (u + 1) u' hu' B this
  -- after every honest validator attempted the proposal: validated, confirmed, or done
  have hatt' : ∀ v ∈ Q.honest, (ex.st (tc + env.Δ + env.L + 1)).HSig v (.val P.block r) ∨
      (ex.st (tc + env.Δ + env.L + 1)).HSig v (.conf P.block r) ∨
      ex.Done (tc + env.Δ + env.L + 1) := by
    intro v hv
    obtain ⟨tv, htv₁, htv₂, hactv⟩ := hatt v hv
    have hw := hwin v hv tv htv₁ (by omega)
    have hmono : tv + 1 ≤ tc + env.Δ + env.L + 1 := by omega
    rcases hw with ⟨hlk, hvv, hlb⟩ | ⟨h, _, _⟩ | h
    · -- fresh: the step validates
      by_cases hfin : ∃ B, ((ex.st tv).locals v).finalized = some B
      · obtain ⟨B, hB⟩ := hfin
        exact Or.inr (Or.inr (Done.mono ex (by omega) (ex.done_of_finalized hv hB)))
      push Not at hfin
      have hfresh : ((ex.st tv).locals v).Fresh r := by
        refine ⟨hcur_w' tv (by omega) (by omega) v hv, ?_, hlb, ?_,
          Option.eq_none_iff_forall_ne_some.2 hfin⟩
        · intro vv hvv'
          rw [hvv] at hvv'
          have hs := (ex.inv tq v hv).valVote_sig vv hvv'
          have h1 : vv.2 ≤ ex.cur v tq := (ex.inv tq v hv).val_le_cur vv.1 vv.2 hs
          rw [hcurq v hv] at h1
          rcases Nat.lt_or_eq_of_le h1 with h | h
          · exact h
          · rw [h] at hs; exact absurd hs (hno_val tq le_rfl v hv vv.1)
        · intro lk hlk'
          rw [hlk] at hlk'
          obtain ⟨lb, hlb', hle⟩ :=
            (ex.inv tq v hv).conf_bound lk.1 lk.2 ((ex.inv tq v hv).lock_conf lk hlk')
          exact hle.trans_lt (hlb_lt v hv lb hlb')
      have hlock : ((ex.st tv).locals v).lockOk cfg P := by
        unfold Local.lockOk; rw [hlk]; exact hacc_tq v hv
      have hstep := step_val (by rw [hPr]; exact hnfr)
        (Local.preOk_of_fresh (hwf tv htv₁) hfresh) (hwf tv htv₁).cert hlock hPv
      have hsig : (ex.st (tv + 1)).HSig v (.val P.block r) := by
        rw [ex.succ, hactv]; simp only [stepOpt, hstep, Option.getD_some]
        rw [HSig_sign]; exact Or.inr ⟨rfl, by rw [hPr]⟩
      exact Or.inl (ex.HSig_mono hmono hsig)
    · exact Or.inl (ex.HSig_mono (by omega) h)
    · exact Or.inr (Or.inl (ex.HSig_mono (by omega) h))
  by_cases hdone₃ : ex.Done (tc + env.Δ + env.L + 1)
  · exact ⟨_, hdone₃⟩
  -- the owner can hold the validation certificate: every honest validator voted, or one
  -- confirmed and reports it as its locking block
  have hvc : (ex.st (tc + env.Δ + env.L + 1)).ValCert P.block r := by
    by_cases hall : ∀ v ∈ Q.honest, (ex.st (tc + env.Δ + env.L + 1)).HSig v (.val P.block r)
    · exact HasCert_of_honest hall
    · push Not at hall
      obtain ⟨v, hv, hnv⟩ := hall
      rcases hatt' v hv with h | h | h
      · exact absurd h hnv
      · exact (ex.inv _ v hv).conf_valCert P.block r h hnfr
      · exact absurd h hdone₃
  have hevid : (∀ v ∈ Q.honest, (ex.st (tc + env.Δ + env.L + 1)).HSig v (.val P.block r)) ∨
      ∃ v ∈ Q.honest, ((ex.st (tc + env.Δ + env.L + 1)).locals v).lb = some (.cert P.block r) := by
    by_cases hall : ∀ v ∈ Q.honest, (ex.st (tc + env.Δ + env.L + 1)).HSig v (.val P.block r)
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨v, hv, hnv⟩ := hall
      right
      refine ⟨v, hv, ?_⟩
      rcases hatt' v hv with h | h | h
      · exact absurd h hnv
      · -- a confirmation in `r` makes the locking block a certificate of round `r`
        have hvi := ex.inv (tc + env.Δ + env.L + 1) v hv
        obtain ⟨lb, hlb, hle⟩ := hvi.conf_bound P.block r h
        rw [Option.mem_def] at hlb
        rcases lb with ⟨B', ρ⟩ | B'
        · have hcert' := hvi.lb_cert B' ρ hlb
          obtain ⟨u, hu, hsig⟩ := hcert'.exists_honest_HSig
          have h1 : ρ ≤ ex.cur u _ := (ex.inv _ u hu).val_le_cur B' ρ hsig
          rw [hcur_w' _ (by omega) (by omega) u hu] at h1
          have hρ : ρ = r := le_antisymm h1 hle
          subst hρ
          rw [(ex.inv _).valCert_unique hcert' hvc] at hlb
          exact hlb
        · change r ≤ 0 at hle; omega
      · exact absurd h hdone₃
  -- it reaches everyone, and everyone confirms
  have hconf : ∀ v ∈ Q.honest, (ex.st (tc + env.Δ + 2 * env.L + 2)).HSig v (.conf P.block r) ∨
      ex.Done (tc + env.Δ + 2 * env.L + 2) := by
    intro v hv
    obtain ⟨tv, htv₁, htv₂, hactv⟩ := env.cert _ (by omega) r hrs hsole P.block
      (fun w hw => hcur_w' _ (by omega) (by omega) w hw) hevid v hv
    have hw := hwin v hv tv (by omega) (by omega)
    have hmono : tv + 1 ≤ tc + env.Δ + 2 * env.L + 2 := by omega
    by_cases hc : (ex.st tv).HSig v (.conf P.block r)
    · exact Or.inl (ex.HSig_mono (by omega) hc)
    by_cases hfin : ∃ B, ((ex.st tv).locals v).finalized = some B
    · obtain ⟨B, hB⟩ := hfin
      exact Or.inr (Done.mono ex (by omega) (ex.done_of_finalized hv hB))
    push Not at hfin
    have hlb : ∀ lb ∈ ((ex.st tv).locals v).lb, lb.round < r := by
      rcases hw with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h
      · exact h
      · exact h
      · exact absurd h hc
    have hvv : ∀ vv ∈ ((ex.st tv).locals v).valVote, vv.2 ≤ r := by
      intro vv hvv'
      have h1 := (ex.inv tv v hv).val_le_cur vv.1 vv.2 ((ex.inv tv v hv).valVote_sig vv hvv')
      change vv.2 ≤ ex.cur v tv at h1
      rw [hcur_w' tv (by omega) (by omega) v hv] at h1
      exact h1
    have hok : ((ex.st tv).locals v).valCertOk P.block r := by
      refine ⟨Option.eq_none_iff_forall_ne_some.2 hfin, ?_, hvv, hlb⟩
      intro hlk
      exact hc ((ex.inv tv v hv).lock_conf (P.block, r) (by rw [hlk]; rfl))
    have hcv : ((ex.st tv).locals v).confVotes r := by
      change ex.cur v tv ≤ r; rw [hcur_w' tv (by omega) (by omega) v hv]
    have hstep := step_conf (cfg := cfg) (ex.HasCert_mono (by omega) hvc) hok hcv
    have hsig : (ex.st (tv + 1)).HSig v (.conf P.block r) := by
      rw [ex.succ, hactv]; simp only [stepOpt, hstep, Option.getD_some]
      rw [HSig_sign]; exact Or.inr ⟨rfl, rfl⟩
    exact Or.inl (ex.HSig_mono hmono hsig)
  by_cases hdone₄ : ex.Done (tc + env.Δ + 2 * env.L + 2)
  · exact ⟨_, hdone₄⟩
  refine ⟨tc + env.Δ + 2 * env.L + 2, P.block, r, HasCert_of_honest ?_⟩
  intro v hv
  rcases hconf v hv with h | h
  · exact h
  · exact absurd h hdone₄

end TExec

end Linera
