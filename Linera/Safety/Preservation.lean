import Linera.Safety.Invariants

/-!
# Preservation of the invariant across the acting validator's handlers

Four generic lemmas cover the shapes a handler can take at the acting
validator `v` — a local update with no signature (`VInv.set_self`), a
timeout vote (`VInv.sign_time`), a validation vote (`VInv.sign_val`) and a
confirmation vote (`VInv.sign_conf`, shared by the fast path and
`OnCertificate`) — and `Inv.step` dispatches the five inputs to them, with
the frame lemmas of `Invariants.lean` for every other validator.
`Inv.reachable` then establishes the invariant on every reachable state.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-! ## Local helpers -/

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- The locking block after a justification is at least as recent. -/
theorem Local.lbAfter_ge (l : Local Block) (P : Proposal Owner Block) :
    ∀ lb ∈ l.lb, ∃ lb' ∈ l.lbAfter P, lb.round ≤ lb'.round := by
  intro lb hlb
  rw [Option.mem_def] at hlb
  unfold Local.lbAfter
  rcases P.just with _ | ⟨B', ρ⟩ | _
  · exact ⟨lb, by rw [hlb]; rfl, le_rfl⟩
  · rw [hlb]
    change ∃ lb' ∈ (if lb.round < ρ then some (.cert B' ρ) else some lb), lb.round ≤ lb'.round
    split_ifs with h
    · exact ⟨.cert B' ρ, rfl, h.le⟩
    · exact ⟨lb, rfl, le_rfl⟩
  · exact ⟨lb, by rw [hlb]; rfl, le_rfl⟩

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- A certificate locking block after a justification is the old one or the carried one. -/
theorem Local.lbAfter_cert (l : Local Block) (P : Proposal Owner Block) {B' : Block} {ρ : Round}
    (h : l.lbAfter P = some (.cert B' ρ)) :
    l.lb = some (.cert B' ρ) ∨ P.just = .cert B' ρ := by
  unfold Local.lbAfter at h
  rcases hj : P.just with _ | ⟨B'', ρ'⟩ | _ <;> rw [hj] at h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · exact absurd h (by simp)
    · exact Or.inl h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · simp only [Option.some.injEq, Locking.cert.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Or.inr rfl
    · change (if lb.round < ρ' then some (.cert B'' ρ') else some lb) = _ at h
      split_ifs at h
      · simp only [Option.some.injEq, Locking.cert.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact Or.inr rfl
      · exact Or.inl h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · exact absurd h (by simp)
    · exact Or.inl h

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- A fast locking block after a justification is the old one, or was set from none. -/
theorem Local.lbAfter_fast (l : Local Block) (P : Proposal Owner Block) {B' : Block}
    (h : l.lbAfter P = some (.fast B')) :
    l.lb = some (.fast B') ∨ (l.lb = none ∧ P.just = .fast ∧ B' = P.block) := by
  unfold Local.lbAfter at h
  rcases hj : P.just with _ | ⟨B'', ρ'⟩ | _ <;> rw [hj] at h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · exact absurd h (by simp)
    · exact Or.inl h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · exact absurd h (by simp)
    · change (if lb.round < ρ' then some (.cert B'' ρ') else some lb) = _ at h
      split_ifs at h
      · exact absurd h (by simp)
      · exact Or.inl h
  · rcases hl : l.lb with _ | lb <;> rw [hl] at h
    · simp only [Option.some.injEq, Locking.fast.injEq] at h
      exact Or.inr ⟨rfl, rfl, h.symm⟩
    · exact Or.inl h

/-! ## Generic shapes -/

omit [DecidableEq Owner] in
/-- A local update at `v` that keeps the latest validation vote and the
lock, does not lower the round or the locking block, replaces the locking
block only by a certificate, and finalizes only on a certificate. -/
theorem VInv.set_self {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block}
    (hvv : l'.valVote = (s.locals v).valVote) (hlk : l'.lock = (s.locals v).lock)
    (hcur : (s.locals v).cur ≤ l'.cur)
    (hfin : ∀ B, l'.finalized = some B → (s.locals v).finalized = some B ∨ ∃ r, s.ConfCert B r)
    (hlb : ∀ lb ∈ (s.locals v).lb, ∃ lb' ∈ l'.lb, lb.round ≤ lb'.round)
    (hlbc : ∀ B ρ, l'.lb = some (.cert B ρ) → (s.locals v).lb = some (.cert B ρ) ∨ s.ValCert B ρ)
    (hlbf : ∀ B', l'.lb = some (.fast B') → (s.locals v).lb = some (.fast B'))
    (htv : l'.timeoutVote = (s.locals v).timeoutVote)
    (htc : ∀ τ ∈ l'.tc, τ ∈ (s.locals v).tc ∨ τ < l'.cur) :
    VInv cfg (s.set v l') v where
  val_bound B ρ h := by
    rw [locals_set_self, hvv]
    rcases hv.val_bound B ρ h with h | ⟨lb, hl, hle⟩
    · exact Or.inl h
    · obtain ⟨lb', hl', hle'⟩ := hlb lb hl
      exact Or.inr ⟨lb', hl', hle.trans hle'⟩
  conf_bound B ρ h := by
    rw [locals_set_self]
    obtain ⟨lb, hl, hle⟩ := hv.conf_bound B ρ h
    obtain ⟨lb', hl', hle'⟩ := hlb lb hl
    exact ⟨lb', hl', hle.trans hle'⟩
  val_le_cur B ρ h := by rw [locals_set_self]; exact (hv.val_le_cur B ρ h).trans hcur
  conf_le_cur B ρ h := by rw [locals_set_self]; exact (hv.conf_le_cur B ρ h).trans hcur
  time_le_cur ρ h := by rw [locals_set_self]; exact (hv.time_le_cur ρ h).trans hcur
  valVote_sig vv h := by rw [locals_set_self, hvv] at h; exact hv.valVote_sig vv h
  timeoutVote_sig τ h := by rw [locals_set_self, htv] at h; exact hv.timeoutVote_sig τ h
  tc_lt_cur τ h := by
    rw [locals_set_self] at h ⊢
    rcases htc τ h with h | h
    · exact (hv.tc_lt_cur τ h).trans_le hcur
    · exact h
  val_unique := hv.val_unique
  conf_unique := hv.conf_unique
  conf_valCert := hv.conf_valCert
  val_not_fast := hv.val_not_fast
  lock_conf lk h := by rw [locals_set_self, hlk] at h; exact hv.lock_conf lk h
  conf_le_lock B ρ h := by rw [locals_set_self, hlk]; exact hv.conf_le_lock B ρ h
  lb_cert B ρ h := by
    rw [locals_set_self] at h
    rcases hlbc B ρ h with h | h
    · exact hv.lb_cert B ρ h
    · exact h
  lock_fast lk' hlk' B' hl := by
    rw [locals_set_self, hlk] at hlk'; rw [locals_set_self] at hl
    exact hv.lock_fast lk' hlk' B' (hlbf B' hl)
  val_ghost e he hs B r hm := (hv.val_ghost e he hs B r hm).set v l'
  fast_elig := hv.fast_elig
  finalized_cert B h := by
    rw [locals_set_self] at h
    rcases hfin B h with h | h
    · exact hv.finalized_cert B h
    · exact h

omit [DecidableEq Owner] in
/-- `v` signs a timeout vote and keeps everything else. -/
theorem VInv.sign_time {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block} (r : Round) (lk : Option (Block × Round))
    (hr : r = (s.locals v).cur)
    (hvv : l'.valVote = (s.locals v).valVote) (hlk : l'.lock = (s.locals v).lock)
    (hcur : l'.cur = (s.locals v).cur) (hfin : l'.finalized = (s.locals v).finalized)
    (hlb : l'.lb = (s.locals v).lb) (htv : l'.timeoutVote = some r)
    (htc : l'.tc = (s.locals v).tc) :
    VInv cfg ((s.set v l').sign ⟨v, .time r, lk, none⟩) v := by
  have hval : ∀ B r', ((s.set v l').sign ⟨v, .time r, lk, none⟩).HSig v (.val B r') ↔
      s.HSig v (.val B r') := fun B r' => HSig_sign_of_msg_ne (by simp)
  have hconf : ∀ B r', ((s.set v l').sign ⟨v, .time r, lk, none⟩).HSig v (.conf B r') ↔
      s.HSig v (.conf B r') := fun B r' => HSig_sign_of_msg_ne (by simp)
  have htime : ∀ r', ((s.set v l').sign ⟨v, .time r, lk, none⟩).HSig v (.time r') ↔
      s.HSig v (.time r') ∨ r = r' := by
    intro r'; rw [HSig_sign, HSig_set]; simp
  exact {
    val_bound := fun B ρ h => by
      simp only [locals_sign, locals_set_self, hvv, hlb]; exact hv.val_bound B ρ ((hval _ _).1 h)
    conf_bound := fun B ρ h => by
      simp only [locals_sign, locals_set_self, hlb]; exact hv.conf_bound B ρ ((hconf _ _).1 h)
    val_le_cur := fun B r' h => by
      simp only [locals_sign, locals_set_self, hcur]; exact hv.val_le_cur B r' ((hval B r').1 h)
    conf_le_cur := fun B r' h => by
      simp only [locals_sign, locals_set_self, hcur]; exact hv.conf_le_cur B r' ((hconf B r').1 h)
    time_le_cur := fun r' h => by
      simp only [locals_sign, locals_set_self, hcur]
      rcases (htime r').1 h with h | rfl
      · exact hv.time_le_cur r' h
      · exact hr.le
    valVote_sig := fun vv h => by
      simp only [locals_sign, locals_set_self, hvv] at h
      exact (hval _ _).2 (hv.valVote_sig vv h)
    timeoutVote_sig := fun τ h => by
      simp only [locals_sign, locals_set_self, htv, Option.mem_def, Option.some.injEq] at h
      rw [← h]; exact (htime _).2 (Or.inr rfl)
    tc_lt_cur := fun τ h => by
      simp only [locals_sign, locals_set_self, htc, hcur] at h ⊢; exact hv.tc_lt_cur τ h
    val_unique := fun B₁ B₂ r' h₁ h₂ => hv.val_unique B₁ B₂ r' ((hval _ _).1 h₁) ((hval _ _).1 h₂)
    conf_unique := fun B₁ B₂ r' h₁ h₂ =>
      hv.conf_unique B₁ B₂ r' ((hconf _ _).1 h₁) ((hconf _ _).1 h₂)
    conf_valCert := fun B r' h hf => (hv.conf_valCert B r' ((hconf _ _).1 h) hf).sign _
    val_not_fast := fun B r' h => hv.val_not_fast B r' ((hval _ _).1 h)
    lock_conf := fun lk' h => by
      simp only [locals_sign, locals_set_self, hlk] at h; exact (hconf _ _).2 (hv.lock_conf lk' h)
    conf_le_lock := fun B r' h => by
      simp only [locals_sign, locals_set_self, hlk]; exact hv.conf_le_lock B r' ((hconf _ _).1 h)
    lb_cert := fun B ρ h => by
      simp only [locals_sign, locals_set_self, hlb] at h; exact (hv.lb_cert B ρ h).sign _
    lock_fast := fun lk' hlk' B' hl => by
      simp only [locals_sign, locals_set_self, hlk, hlb] at hlk' hl
      exact hv.lock_fast lk' hlk' B' hl
    val_ghost := fun e he hs B r' hm => by
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact ((hv.val_ghost e he hs B r' hm).set v l').sign (fun _ _ h => by cases h)
      · cases hm
    fast_elig := fun e he hs B r' hm hf => by
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hv.fast_elig e he hs B r' hm hf
      · cases hm
    finalized_cert := fun B h => by
      simp only [locals_sign, locals_set_self, hfin] at h
      obtain ⟨r', hr'⟩ := hv.finalized_cert B h; exact ⟨r', hr'.sign _⟩ }

omit [DecidableEq Owner] in
/-- `v` signs a validation vote for a two-phase proposal (Alg. on_proposal). -/
theorem VInv.sign_val {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {P : Proposal Owner Block}
    (hpre : (s.locals v).preOk cfg P) (hjc : s.JustCert P.just)
    (hlock : (s.locals v).lockOk cfg P) (hvalid : cfg.Valid P.block) (hnf : ¬ cfg.IsFast P.round) :
    VInv cfg ((s.set v ((s.locals v).afterVal P)).sign
      ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩) v := by
  obtain ⟨hfin, helig, hjust, _, hvv, hlb⟩ := hpre
  obtain ⟨e, he⟩ : ∃ e : Sig V Owner Block,
      e = ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩ := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = (s.set v ((s.locals v).afterVal P)).sign e := ⟨_, rfl⟩
  rw [← he, ← hs']
  have hsig : ∀ m, s'.HSig v m ↔ s.HSig v m ∨ Msg.val P.block P.round = m := by
    intro m; rw [hs', HSig_sign, HSig_set, he]; simp
  have hval : ∀ B r, s'.HSig v (.val B r) ↔ s.HSig v (.val B r) ∨ (P.block = B ∧ P.round = r) := by
    intro B r; rw [hsig]; simp
  have hconf : ∀ B r, s'.HSig v (.conf B r) ↔ s.HSig v (.conf B r) := by
    intro B r; rw [hsig]; simp
  have htime : ∀ r, s'.HSig v (.time r) ↔ s.HSig v (.time r) := by
    intro r; rw [hsig]; simp
  have hloc : s'.locals v = (s.locals v).afterVal P := by simp [hs']
  have hcur : ((s.locals v).afterVal P).cur = max (s.locals v).cur P.round := rfl
  have hlk : ((s.locals v).afterVal P).lock = (s.locals v).lock := rfl
  have hfin' : ((s.locals v).afterVal P).finalized = (s.locals v).finalized := rfl
  have hvv' : ((s.locals v).afterVal P).valVote = some (P.block, P.round) := rfl
  have hlb' : ((s.locals v).afterVal P).lb = (s.locals v).lbAfter P := rfl
  have htv' : ((s.locals v).afterVal P).timeoutVote = (s.locals v).timeoutVote := rfl
  have htc' : ((s.locals v).afterVal P).tc = (s.locals v).tc := rfl
  -- every earlier validation vote is below `P.round`
  have hval_lt : ∀ B ρ, s.HSig v (.val B ρ) → ρ < P.round := by
    intro B ρ h
    rcases hv.val_bound B ρ h with ⟨vv, hvv₁, hle⟩ | ⟨lb, hlb₁, hle⟩
    · exact hle.trans_lt (hvv vv hvv₁)
    · exact hle.trans_lt (hlb lb hlb₁)
  exact {
    val_bound := fun B ρ h => by
      rw [hloc, hvv']
      left
      refine ⟨(P.block, P.round), rfl, ?_⟩
      rcases (hval _ _).1 h with h | ⟨_, rfl⟩
      · exact (hval_lt B ρ h).le
      · exact le_rfl
    conf_bound := fun B ρ h => by
      rw [hloc, hlb']
      obtain ⟨lb, hl, hle⟩ := hv.conf_bound B ρ ((hconf _ _).1 h)
      obtain ⟨lb', hl', hle'⟩ := (s.locals v).lbAfter_ge P lb hl
      exact ⟨lb', hl', hle.trans hle'⟩
    val_le_cur := fun B ρ h => by
      rw [hloc, hcur]
      rcases (hval _ _).1 h with h | ⟨_, rfl⟩
      · exact (hv.val_le_cur B ρ h).trans (le_max_left _ _)
      · exact le_max_right _ _
    conf_le_cur := fun B ρ h => by
      rw [hloc, hcur]; exact (hv.conf_le_cur B ρ ((hconf _ _).1 h)).trans (le_max_left _ _)
    time_le_cur := fun ρ h => by
      rw [hloc, hcur]; exact (hv.time_le_cur ρ ((htime _).1 h)).trans (le_max_left _ _)
    valVote_sig := fun vv h => by
      rw [hloc, hvv', Option.mem_def, Option.some.injEq] at h
      subst h; exact (hval _ _).2 (Or.inr ⟨rfl, rfl⟩)
    timeoutVote_sig := fun τ h => by
      rw [hloc, htv'] at h; exact (htime _).2 (hv.timeoutVote_sig τ h)
    tc_lt_cur := fun τ h => by
      rw [hloc, htc'] at h; rw [hloc, hcur]; exact (hv.tc_lt_cur τ h).trans_le (le_max_left _ _)
    val_unique := fun B₁ B₂ ρ h₁ h₂ => by
      rcases (hval _ _).1 h₁ with h₁ | ⟨hB₁, hr₁⟩
      · rcases (hval _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · exact hv.val_unique B₁ B₂ ρ h₁ h₂
        · subst hr₂; exact absurd (hval_lt B₁ _ h₁) (lt_irrefl _)
      · rcases (hval _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · subst hr₁; exact absurd (hval_lt B₂ _ h₂) (lt_irrefl _)
        · rw [← hB₁, ← hB₂]
    conf_unique := fun B₁ B₂ ρ h₁ h₂ =>
      hv.conf_unique B₁ B₂ ρ ((hconf _ _).1 h₁) ((hconf _ _).1 h₂)
    conf_valCert := fun B ρ h hf => by
      rw [hs']; exact (hv.conf_valCert B ρ ((hconf _ _).1 h) hf).sign _
    val_not_fast := fun B ρ h => by
      rcases (hval _ _).1 h with h | ⟨_, rfl⟩
      · exact hv.val_not_fast B ρ h
      · exact hnf
    lock_conf := fun lk h => by rw [hloc, hlk] at h; exact (hconf _ _).2 (hv.lock_conf lk h)
    conf_le_lock := fun B ρ h => by rw [hloc, hlk]; exact hv.conf_le_lock B ρ ((hconf _ _).1 h)
    lb_cert := fun B ρ h => by
      rw [hloc, hlb'] at h
      rw [hs']
      rcases (s.locals v).lbAfter_cert P h with h | h
      · exact (hv.lb_cert B ρ h).sign _
      · have := hjc; unfold State.JustCert at this; rw [h] at this; exact this.sign _
    lock_fast := fun lk hlk' B' hl => by
      rw [hloc, hlk] at hlk'; rw [hloc, hlb'] at hl
      rcases (s.locals v).lbAfter_fast P hl with hl | ⟨hnone, _⟩
      · exact hv.lock_fast lk hlk' B' hl
      · exfalso
        obtain ⟨lb, hlb₀, _⟩ := hv.conf_bound lk.1 lk.2 (hv.lock_conf lk hlk')
        rw [hnone] at hlb₀; exact Option.not_mem_none _ hlb₀
    val_ghost := fun e' he' hs B r hm => by
      rw [hs'] at he'
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | he''
      · rw [hs']
        exact ((hv.val_ghost e' he' hs B r hm).set v _).sign (fun _ _ h => by rw [he] at h; cases h)
      · -- the new entry
        obtain rfl := he''.symm
        rw [he] at hm
        simp only [Msg.val.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        have hjust' : e.just = P.just := by rw [he]; rfl
        exact {
          prop_elig := ⟨P, by rw [he], rfl, rfl, helig, hvalid⟩
          cert_ok := fun B' ρ hc => by
            rw [hjust'] at hc
            have hj := hjust
            unfold Local.JustOk at hj; rw [hc] at hj
            have hc' := hjc
            unfold State.JustCert at hc'; rw [hc] at hc'
            rw [hs']
            exact ⟨hj.1, hj.2, hc'.sign _⟩
          unlock := fun lk hlk hne => by
            rw [he] at hlk
            rw [hjust']
            have hl := hlock lk hlk
            unfold Local.lockCond at hl
            rcases hj : P.just with _ | ⟨B', ρ⟩ | _ <;> rw [hj] at hl
            · exact absurd hl id
            · obtain ⟨rfl, h | h⟩ := hl
              · exact absurd h.1.symm hne
              · exact ⟨ρ, rfl, h.2⟩
            · exact absurd hl.2.symm hne
          lockAt_conf := fun lk hlk => by
            rw [he] at hlk
            refine ⟨?_, (hconf _ _).2 (hv.lock_conf lk hlk)⟩
            obtain ⟨lb, hl, hle⟩ := hv.conf_bound lk.1 lk.2 (hv.lock_conf lk hlk)
            exact hle.trans_lt (hlb lb hl)
          conf_le_lockAt := fun B₀ r₀ hc₀ _ => by
            rw [he]
            exact hv.conf_le_lock B₀ r₀ ((hconf _ _).1 hc₀) }
    fast_elig := fun e' he' hs B r hm hf => by
      rw [hs'] at he'
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact hv.fast_elig e' he' hs B r hm hf
      · rw [he] at hm; cases hm
    finalized_cert := fun B h => by
      rw [hloc, hfin'] at h
      obtain ⟨r, hr'⟩ := hv.finalized_cert B h
      rw [hs']; exact ⟨r, hr'.sign _⟩ }

omit [DecidableEq Owner] in
/-- `v` signs a confirmation vote for `B` in round `r`, locking on it and
taking a locking block of round `r`: the fast path, or Alg. on_certificate. -/
theorem VInv.sign_conf {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block} {B : Block} {r : Round}
    (pr : Option (Proposal Owner Block)) {lbNew : Locking Block}
    (hvv : l'.valVote = none) (hlk : l'.lock = some (B, r))
    (hlb : l'.lb = some lbNew) (hlbr : lbNew.round = r)
    (hlbc : ∀ B' ρ, lbNew = .cert B' ρ → s.ValCert B' ρ)
    (hlbf : ∀ B', lbNew = .fast B' → B = B')
    (htv : l'.timeoutVote = (s.locals v).timeoutVote) (htc : l'.tc = (s.locals v).tc)
    (hcur : (s.locals v).cur ≤ l'.cur) (hrcur : r ≤ l'.cur)
    (hfin : l'.finalized = (s.locals v).finalized)
    (hvalle : ∀ vv ∈ (s.locals v).valVote, vv.2 ≤ r)
    (hlble : ∀ lb ∈ (s.locals v).lb, lb.round < r)
    (hvcert : ¬ cfg.IsFast r → s.ValCert B r)
    (hpr : cfg.IsFast r → ∃ P, pr = some P ∧ P.block = B ∧ P.round = r ∧
      cfg.FastEligible r P.owner) :
    VInv cfg ((s.set v l').sign ⟨v, .conf B r, (s.locals v).lock, pr⟩) v := by
  obtain ⟨e, he⟩ : ∃ e : Sig V Owner Block, e = ⟨v, .conf B r, (s.locals v).lock, pr⟩ := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = (s.set v l').sign e := ⟨_, rfl⟩
  rw [← he, ← hs']
  have hsig : ∀ m, s'.HSig v m ↔ s.HSig v m ∨ Msg.conf B r = m := by
    intro m; rw [hs', HSig_sign, HSig_set, he]; simp
  have hval : ∀ B' r', s'.HSig v (.val B' r') ↔ s.HSig v (.val B' r') := by
    intro B' r'; rw [hsig]; simp
  have hconf : ∀ B' r', s'.HSig v (.conf B' r') ↔ s.HSig v (.conf B' r') ∨ (B = B' ∧ r = r') := by
    intro B' r'; rw [hsig]; simp
  have htime : ∀ r', s'.HSig v (.time r') ↔ s.HSig v (.time r') := by
    intro r'; rw [hsig]; simp
  have hloc : s'.locals v = l' := by simp [hs']
  -- every earlier vote is at or below `r`, confirmations strictly
  have hval_le : ∀ B' ρ, s.HSig v (.val B' ρ) → ρ ≤ r := by
    intro B' ρ h
    rcases hv.val_bound B' ρ h with ⟨vv, hvv₁, hle⟩ | ⟨lb, hlb₁, hle⟩
    · exact hle.trans (hvalle vv hvv₁)
    · exact hle.trans (hlble lb hlb₁).le
  have hconf_lt : ∀ B' ρ, s.HSig v (.conf B' ρ) → ρ < r := by
    intro B' ρ h
    obtain ⟨lb, hlb₁, hle⟩ := hv.conf_bound B' ρ h
    exact hle.trans_lt (hlble lb hlb₁)
  exact {
    val_bound := fun B' ρ h => by
      rw [hloc, hlb]
      exact Or.inr ⟨lbNew, rfl, hlbr ▸ hval_le B' ρ ((hval _ _).1 h)⟩
    conf_bound := fun B' ρ h => by
      rw [hloc, hlb]
      refine ⟨lbNew, rfl, ?_⟩
      rw [hlbr]
      rcases (hconf _ _).1 h with h | ⟨_, rfl⟩
      · exact (hconf_lt B' ρ h).le
      · exact le_rfl
    val_le_cur := fun B' ρ h => by
      rw [hloc]; exact (hv.val_le_cur B' ρ ((hval _ _).1 h)).trans hcur
    conf_le_cur := fun B' ρ h => by
      rw [hloc]
      rcases (hconf _ _).1 h with h | ⟨_, rfl⟩
      · exact (hv.conf_le_cur B' ρ h).trans hcur
      · exact hrcur
    time_le_cur := fun ρ h => by
      rw [hloc]; exact (hv.time_le_cur ρ ((htime _).1 h)).trans hcur
    valVote_sig := fun vv h => by
      rw [hloc, hvv] at h; exact absurd h (Option.not_mem_none _)
    timeoutVote_sig := fun τ h => by
      rw [hloc, htv] at h; exact (htime _).2 (hv.timeoutVote_sig τ h)
    tc_lt_cur := fun τ h => by
      rw [hloc, htc] at h; rw [hloc]; exact (hv.tc_lt_cur τ h).trans_le hcur
    val_unique := fun B₁ B₂ ρ h₁ h₂ => hv.val_unique B₁ B₂ ρ ((hval _ _).1 h₁) ((hval _ _).1 h₂)
    conf_unique := fun B₁ B₂ ρ h₁ h₂ => by
      rcases (hconf _ _).1 h₁ with h₁ | ⟨hB₁, hr₁⟩
      · rcases (hconf _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · exact hv.conf_unique B₁ B₂ ρ h₁ h₂
        · subst hr₂; exact absurd (hconf_lt B₁ _ h₁) (lt_irrefl _)
      · rcases (hconf _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · subst hr₁; exact absurd (hconf_lt B₂ _ h₂) (lt_irrefl _)
        · rw [← hB₁, ← hB₂]
    conf_valCert := fun B' ρ h hf => by
      rw [hs']
      rcases (hconf _ _).1 h with h | ⟨rfl, rfl⟩
      · exact (hv.conf_valCert B' ρ h hf).sign _
      · exact (hvcert hf).sign _
    val_not_fast := fun B' ρ h => hv.val_not_fast B' ρ ((hval _ _).1 h)
    lock_conf := fun lk h => by
      rw [hloc, hlk, Option.mem_def, Option.some.injEq] at h
      subst h
      exact (hconf _ _).2 (Or.inr ⟨rfl, rfl⟩)
    conf_le_lock := fun B' ρ h => by
      rw [hloc, hlk]
      refine ⟨(B, r), rfl, ?_⟩
      rcases (hconf _ _).1 h with h | ⟨_, rfl⟩
      · exact (hconf_lt B' ρ h).le
      · exact le_rfl
    lb_cert := fun B' ρ h => by
      rw [hloc, hlb, Option.some.injEq] at h
      rw [hs']; exact (hlbc B' ρ h).sign _
    lock_fast := fun lk hlk' B' hl => by
      rw [hloc, hlk, Option.mem_def, Option.some.injEq] at hlk'
      rw [hloc, hlb, Option.some.injEq] at hl
      subst hlk'; exact hlbf B' hl
    val_ghost := fun e' he' hs B' r' hm => by
      rw [hs'] at he' ⊢
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · refine ((hv.val_ghost e' he' hs B' r' hm).set v _).sign (fun B₀ r₀ h₀ => ?_)
        rw [he] at h₀
        simp only [Msg.conf.injEq] at h₀
        obtain ⟨_, rfl⟩ := h₀
        exact hval_le B' r' ⟨e', he', hs, hm⟩
      · rw [he] at hm; cases hm
    fast_elig := fun e' he' hs B' r' hm hf => by
      rw [hs'] at he'
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact hv.fast_elig e' he' hs B' r' hm hf
      · rw [he] at hm ⊢
        simp only [Msg.conf.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hpr hf
    finalized_cert := fun B' h => by
      rw [hloc, hfin] at h
      obtain ⟨r', hr'⟩ := hv.finalized_cert B' h
      rw [hs']; exact ⟨r', hr'.sign _⟩ }

omit [DecidableEq Owner] in
/-- No validation certificate exists in the fast round: honest validators
cast no validation vote there, and the Byzantine ones alone are no quorum. -/
theorem Inv.not_valCert_fast {cfg : Config Owner Block} {s : State V Owner Block} (hs : Inv cfg s)
    {B : Block} {r : Round} (hf : cfg.IsFast r) (h : s.ValCert B r) : False := by
  obtain ⟨v, hv, hsig⟩ := h.exists_honest_HSig
  exact (hs v hv).val_not_fast B r hsig hf

omit [DecidableEq Owner] in
/-- **Unique validation per round** (paper, Lemma unique-valcert): two
validation certificates in one round share an honest signer, who votes once. -/
theorem Inv.valCert_unique {cfg : Config Owner Block} {s : State V Owner Block} (hs : Inv cfg s)
    {B₁ B₂ : Block} {r : Round} (h₁ : s.ValCert B₁ r) (h₂ : s.ValCert B₂ r) : B₁ = B₂ := by
  obtain ⟨v, hv, hs₁, hs₂⟩ := h₁.exists_honest_HSig_inter h₂
  exact (hs v hv).val_unique B₁ B₂ r hs₁ hs₂

/-! ## The step lemma -/

/-- The invariant is preserved by every step of an honest validator. -/
theorem Inv.step {cfg : Config Owner Block} {s s' : State V Owner Block} (hs : Inv cfg s)
    {v : V} (hv : v ∈ Q.honest) {i : Input Owner Block} (h : step cfg s v i = some s') :
    Inv cfg s' := by
  have hvi := hs v hv
  have frame_sign : ∀ (l' : Local Block) (e : Sig V Owner Block), e.signer = v →
      VInv cfg ((s.set v l').sign e) v → Inv cfg ((s.set v l').sign e) := by
    intro l' e he hv' w hw
    by_cases hwv : w = v
    · subst hwv; exact hv'
    · exact ((hs w hw).set_of_ne hwv l').sign_of_ne (by rw [he]; exact Ne.symm hwv)
  have frame_set : ∀ (l' : Local Block), VInv cfg (s.set v l') v → Inv cfg (s.set v l') := by
    intro l' hv' w hw
    by_cases hwv : w = v
    · subst hwv; exact hv'
    · exact (hs w hw).set_of_ne hwv l'
  cases i with
  | proposal P =>
    rw [Linera.step] at h
    split_ifs at h with hf hok hpre hacc
    · -- fast path
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨_, hfe, _, _, hvv, hlb, hlk⟩ := hok
      have hr0 : P.round = 0 := hf.2
      refine frame_sign _ _ rfl (hvi.sign_conf (some P) (lbNew := .fast P.block) rfl rfl rfl
        (by simp [Locking.round, hr0]) (fun _ _ h => by cases h) (fun _ h => by cases h; rfl) rfl
        rfl (le_max_left _ _)
        (le_max_right _ _) rfl ?_ ?_ (fun hnf => absurd hf hnf)
        (fun _ => ⟨P, rfl, rfl, rfl, hfe⟩))
      · intro vv hvv'; rw [hvv] at hvv'; exact absurd hvv' (Option.not_mem_none _)
      · intro lb hlb'; rw [hlb] at hlb'; exact absurd hlb' (Option.not_mem_none _)
    · -- two-phase proposal, validated
      simp only [Option.some.injEq] at h; subst h
      exact frame_sign _ _ rfl (hvi.sign_val hpre.1 hpre.2 hacc.1 hacc.2 hf)
    · -- two-phase proposal, noted without a vote
      simp only [Option.some.injEq] at h; subst h
      refine frame_set _ (hvi.set_self rfl rfl (le_max_left _ _) (fun _ h => Or.inl h)
        (fun lb hl => ⟨lb, hl, le_rfl⟩) (fun _ _ h => Or.inl h) (fun _ h => h) rfl
        (fun _ h => Or.inl h))
  | valCert B r =>
    rw [Linera.step] at h
    split_ifs at h with hok hcv
    · -- a confirmation vote is signed
      obtain ⟨hcert, _, _, hvalle, hlble⟩ := hok
      simp only [Option.some.injEq] at h; subst h
      refine frame_sign _ _ rfl (hvi.sign_conf none (lbNew := .cert B r) ?_ ?_ ?_ rfl
        (fun B' ρ h => by cases h; exact hcert) (fun _ h => by cases h) ?_ ?_ ?_ ?_ ?_ hvalle hlble
        (fun _ => hcert) (fun hf => absurd hcert (hs.not_valCert_fast hf)))
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
    · -- the round advances without a vote
      obtain ⟨hcert, _, _, _, hlble⟩ := hok
      simp only [Option.some.injEq] at h; subst h
      refine frame_set _ (hvi.set_self ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · intro B' h'; left; simpa [Local.afterValCert, hcv] using h'
      · intro lb hl
        refine ⟨.cert B r, by simp [Local.afterValCert, hcv], ?_⟩
        exact (hlble lb hl).le
      · intro B' ρ h'
        have hlbEq : ((s.locals v).afterValCert B r).lb = some (.cert B r) := by
          simp [Local.afterValCert, hcv]
        rw [hlbEq, Option.some.injEq, Locking.cert.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact Or.inr hcert
      · intro B' h'
        have hlbEq : ((s.locals v).afterValCert B r).lb = some (.cert B r) := by
          simp [Local.afterValCert, hcv]
        rw [hlbEq] at h'; cases h'
      · simp [Local.afterValCert, hcv]
      · intro τ h'; left; simpa [Local.afterValCert, hcv] using h'
  | confCert B r =>
    rw [Linera.step] at h
    split_ifs at h with hok
    obtain ⟨hcert, _⟩ := hok
    simp only [Option.some.injEq] at h; subst h
    refine frame_set _ (hvi.set_self rfl rfl le_rfl ?_ (fun lb hl => ⟨lb, hl, le_rfl⟩)
      (fun _ _ h => Or.inl h) (fun _ h => h) rfl (fun _ h => Or.inl h))
    intro B' h'
    simp only [Local.afterConfCert, Option.some.injEq] at h'
    subst h'; exact Or.inr ⟨r, hcert⟩
  | timeout r =>
    rw [Linera.step] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h; subst h
    exact frame_sign _ _ rfl (hvi.sign_time r _ hok.2.1 rfl rfl rfl rfl rfl rfl rfl)
  | timeoutCert r =>
    rw [Linera.step] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h; subst h
    refine frame_set _ (hvi.set_self rfl rfl (le_max_left _ _) (fun _ h => Or.inl h)
      (fun lb hl => ⟨lb, hl, le_rfl⟩) (fun _ _ h => Or.inl h) (fun _ h => h) rfl ?_)
    intro τ h
    simp only [Local.afterTimeoutCert, Option.mem_def, Option.some.injEq] at h
    subst h; right; simp [Local.afterTimeoutCert]

/-- The invariant holds in every reachable state. -/
theorem Inv.reachable {cfg : Config Owner Block} {s : State V Owner Block}
    (h : Reachable cfg s) : Inv cfg s := by
  induction h with
  | refl => exact Inv.init cfg
  | tail _ hstep ih =>
    obtain ⟨v, hv, i, hi⟩ := hstep
    exact ih.step hv hi

end Linera
