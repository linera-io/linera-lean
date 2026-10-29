import LeanLinera.Safety.Invariants

/-!
# Preservation of the invariant across the acting validator's handlers

Four generic lemmas cover the shapes a handler can take at the acting
validator `v` — a local update with no signature (`VInv.set_self`), a
timeout vote (`VInv.sign_time`), a validation vote (`VInv.sign_val`) and a
confirmation vote (`VInv.sign_conf`, shared by the fast path and
`OnCertificate`) — and `Inv.step` dispatches the five inputs to them, with
the frame lemmas of `Invariants.lean` for every other validator. `Inv.reachable`
then establishes the invariant on every reachable state.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

/-! ## Generic shapes -/

omit [DecidableEq Owner] in
/-- A local update at `v` that keeps the vote flags and the lock, does not
lower the round, and finalizes only on a certificate. -/
theorem VInv.set_self {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block}
    (hvv : l'.votedVal = (s.locals v).votedVal) (hvc : l'.votedConf = (s.locals v).votedConf)
    (hlk : l'.lock = (s.locals v).lock) (hcur : (s.locals v).cur ≤ l'.cur)
    (hfin : ∀ B, l'.finalized = some B → (s.locals v).finalized = some B ∨ ∃ r, s.ConfCert B r)
    (hkn : ∀ r B, l'.knownVal r = some B → (s.locals v).knownVal r = some B ∨ s.ValCert B r)
    (hkn' : ∀ r B, (s.locals v).knownVal r = some B → l'.knownVal r = some B) :
    VInv cfg (s.set v l') v where
  votedVal_iff r := by rw [locals_set_self, hvv]; exact hv.votedVal_iff r
  votedConf_iff r := by rw [locals_set_self, hvc]; exact hv.votedConf_iff r
  val_le_cur B r h := by rw [locals_set_self]; exact (hv.val_le_cur B r h).trans hcur
  conf_le_cur B r h := by rw [locals_set_self]; exact (hv.conf_le_cur B r h).trans hcur
  val_unique := hv.val_unique
  conf_unique := hv.conf_unique
  conf_valCert := hv.conf_valCert
  val_not_fast := hv.val_not_fast
  lock_conf lk h := by rw [locals_set_self, hlk] at h; exact hv.lock_conf lk h
  lock_le_cur lk h := by
    rw [locals_set_self, hlk] at h; rw [locals_set_self]; exact (hv.lock_le_cur lk h).trans hcur
  conf_le_lock B r h := by rw [locals_set_self, hlk]; exact hv.conf_le_lock B r h
  val_ghost e he hs B r hm := (hv.val_ghost e he hs B r hm).set v l'
  fast_elig := hv.fast_elig
  finalized_cert B h := by
    rw [locals_set_self] at h
    rcases hfin B h with h | h
    · exact hv.finalized_cert B h
    · exact h
  knownVal_cert r B h := by
    rw [locals_set_self] at h
    rcases hkn r B h with h | h
    · exact hv.knownVal_cert r B h
    · exact h
  lock_known lk h hf := by
    rw [locals_set_self, hlk] at h; rw [locals_set_self]
    exact hkn' _ _ (hv.lock_known lk h hf)

omit [DecidableEq Owner] in
/-- `v` signs a timeout vote and keeps everything else. -/
theorem VInv.sign_time {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block} (r : Round) (lk : Option (Block × Round))
    (hvv : l'.votedVal = (s.locals v).votedVal) (hvc : l'.votedConf = (s.locals v).votedConf)
    (hlk : l'.lock = (s.locals v).lock) (hcur : l'.cur = (s.locals v).cur)
    (hfin : l'.finalized = (s.locals v).finalized) (hkn : l'.knownVal = (s.locals v).knownVal) :
    VInv cfg ((s.set v l').sign ⟨v, .time r, lk, none⟩) v := by
  have hval : ∀ B r', ((s.set v l').sign ⟨v, .time r, lk, none⟩).HSig v (.val B r') ↔
      s.HSig v (.val B r') := fun B r' => HSig_sign_of_msg_ne (by simp)
  have hconf : ∀ B r', ((s.set v l').sign ⟨v, .time r, lk, none⟩).HSig v (.conf B r') ↔
      s.HSig v (.conf B r') := fun B r' => HSig_sign_of_msg_ne (by simp)
  exact {
    votedVal_iff := fun r' => by
      simp only [locals_sign, locals_set_self, hvv, hval]; exact hv.votedVal_iff r'
    votedConf_iff := fun r' => by
      simp only [locals_sign, locals_set_self, hvc, hconf]; exact hv.votedConf_iff r'
    val_le_cur := fun B r' h => by
      simp only [locals_sign, locals_set_self, hcur]; exact hv.val_le_cur B r' ((hval B r').1 h)
    conf_le_cur := fun B r' h => by
      simp only [locals_sign, locals_set_self, hcur]; exact hv.conf_le_cur B r' ((hconf B r').1 h)
    val_unique := fun B₁ B₂ r' h₁ h₂ => hv.val_unique B₁ B₂ r' ((hval _ _).1 h₁) ((hval _ _).1 h₂)
    conf_unique := fun B₁ B₂ r' h₁ h₂ =>
      hv.conf_unique B₁ B₂ r' ((hconf _ _).1 h₁) ((hconf _ _).1 h₂)
    conf_valCert := fun B r' h hf => (hv.conf_valCert B r' ((hconf _ _).1 h) hf).sign _
    val_not_fast := fun B r' h => hv.val_not_fast B r' ((hval _ _).1 h)
    lock_conf := fun lk' h => by
      simp only [locals_sign, locals_set_self, hlk] at h; exact (hv.lock_conf lk' h).sign _
    lock_le_cur := fun lk' h => by
      simp only [locals_sign, locals_set_self, hlk, hcur] at h ⊢; exact hv.lock_le_cur lk' h
    conf_le_lock := fun B r' h => by
      simp only [locals_sign, locals_set_self, hlk]; exact hv.conf_le_lock B r' ((hconf _ _).1 h)
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
      obtain ⟨r', hr'⟩ := hv.finalized_cert B h; exact ⟨r', hr'.sign _⟩
    knownVal_cert := fun r' B h => by
      simp only [locals_sign, locals_set_self, hkn] at h
      exact (hv.knownVal_cert r' B h).sign _
    lock_known := fun lk' h hf => by
      simp only [locals_sign, locals_set_self, hlk, hkn] at h ⊢
      exact hv.lock_known lk' h hf }

omit [DecidableEq Owner] in
/-- `v` signs a validation vote for a two-phase proposal (Alg. on_proposal). -/
theorem VInv.sign_val {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {P : Proposal Owner Block}
    (hok : (s.locals v).proposalOk cfg P) (hc : ∀ c ∈ P.cert, s.ValCert c.1 c.2)
    (hnf : ¬ cfg.IsFast P.round) :
    VInv cfg ((s.set v ((s.locals v).afterProposal P)).sign
      ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩) v := by
  obtain ⟨hfin, helig, hr, _, hcert, hlock, hvv, hvc, _⟩ := hok
  obtain ⟨e, he⟩ : ∃ e : Sig V Owner Block,
      e = ⟨v, .val P.block P.round, (s.locals v).lock, some P⟩ := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = (s.set v ((s.locals v).afterProposal P)).sign e := ⟨_, rfl⟩
  rw [← he, ← hs']
  have hsig : ∀ m, s'.HSig v m ↔ s.HSig v m ∨ Msg.val P.block P.round = m := by
    intro m; rw [hs', HSig_sign, HSig_set, he]; simp
  have hval : ∀ B r, s'.HSig v (.val B r) ↔ s.HSig v (.val B r) ∨ (P.block = B ∧ P.round = r) := by
    intro B r; rw [hsig]; simp
  have hconf : ∀ B r, s'.HSig v (.conf B r) ↔ s.HSig v (.conf B r) := by
    intro B r; rw [hsig]; simp
  have hloc : s'.locals v = (s.locals v).afterProposal P := by simp [hs']
  have hcur : ((s.locals v).afterProposal P).cur = (s.locals v).cur := rfl
  have hlk : ((s.locals v).afterProposal P).lock = (s.locals v).lock := rfl
  have hfin' : ((s.locals v).afterProposal P).finalized = (s.locals v).finalized := rfl
  have hvc' : ((s.locals v).afterProposal P).votedConf = (s.locals v).votedConf := rfl
  have hkn : ((s.locals v).afterProposal P).knownVal = (s.locals v).knownVal := rfl
  exact {
    votedVal_iff := fun r => by
      rw [hloc]
      simp only [Local.afterProposal, Function.update_apply]
      constructor
      · intro h
        split_ifs at h with hr'
        · exact ⟨P.block, (hval _ _).2 (Or.inr ⟨rfl, hr'.symm⟩)⟩
        · obtain ⟨B, hB⟩ := (hv.votedVal_iff r).1 h
          exact ⟨B, (hval _ _).2 (Or.inl hB)⟩
      · rintro ⟨B, hB⟩
        rcases (hval _ _).1 hB with hB | ⟨_, rfl⟩
        · split_ifs with hr'
          · rfl
          · exact (hv.votedVal_iff r).2 ⟨B, hB⟩
        · simp
    votedConf_iff := fun r => by rw [hloc, hvc']; simp only [hconf]; exact hv.votedConf_iff r
    val_le_cur := fun B r h => by
      rw [hloc, hcur]
      rcases (hval _ _).1 h with h | ⟨_, rfl⟩
      · exact hv.val_le_cur B r h
      · exact hr.le
    conf_le_cur := fun B r h => by rw [hloc, hcur]; exact hv.conf_le_cur B r ((hconf _ _).1 h)
    val_unique := fun B₁ B₂ r h₁ h₂ => by
      rcases (hval _ _).1 h₁ with h₁ | ⟨hB₁, hr₁⟩
      · rcases (hval _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · exact hv.val_unique B₁ B₂ r h₁ h₂
        · subst hr₂; exact absurd ((hv.votedVal_iff _).2 ⟨B₁, h₁⟩) (by simp [hvv])
      · rcases (hval _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · subst hr₁; exact absurd ((hv.votedVal_iff _).2 ⟨B₂, h₂⟩) (by simp [hvv])
        · rw [← hB₁, ← hB₂]
    conf_unique := fun B₁ B₂ r h₁ h₂ =>
      hv.conf_unique B₁ B₂ r ((hconf _ _).1 h₁) ((hconf _ _).1 h₂)
    conf_valCert := fun B r h hf => by
      rw [hs']; exact (hv.conf_valCert B r ((hconf _ _).1 h) hf).sign _
    val_not_fast := fun B r h => by
      rcases (hval _ _).1 h with h | ⟨_, rfl⟩
      · exact hv.val_not_fast B r h
      · exact hnf
    lock_conf := fun lk h => by rw [hloc, hlk] at h; exact (hconf _ _).2 (hv.lock_conf lk h)
    lock_le_cur := fun lk h => by rw [hloc, hlk] at h; rw [hloc, hcur]; exact hv.lock_le_cur lk h
    conf_le_lock := fun B r h => by rw [hloc, hlk]; exact hv.conf_le_lock B r ((hconf _ _).1 h)
    val_ghost := fun e' he' hs B r hm => by
      rw [hs'] at he'
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · rw [hs']
        exact ((hv.val_ghost e' he' hs B r hm).set v _).sign (fun _ _ h => by rw [he] at h; cases h)
      · -- the new entry
        rw [he] at hm
        simp only [Msg.val.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact {
          prop_elig := ⟨P, by rw [he], rfl, rfl, helig⟩
          cert_ok := fun c hc' => by
            rw [he] at hc'
            simp only [Sig.cert, Option.bind_some] at hc'
            rw [hs']
            exact ⟨(hcert c hc').1, (hcert c hc').2, (hc c hc').sign _⟩
          unlock := fun lk hlk hne => by
            rw [he] at hlk ⊢
            simp only [Sig.cert, Option.bind_some]
            exact hlock lk hlk hne
          lockAt_conf := fun lk hlk => by
            rw [he] at hlk
            refine ⟨?_, (hconf _ _).2 (hv.lock_conf lk hlk)⟩
            have hle := hv.lock_le_cur lk hlk
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact hr ▸ hlt
            · exfalso
              have := (hv.votedConf_iff lk.2).2 ⟨lk.1, hv.lock_conf lk hlk⟩
              rw [heq, ← hr] at this
              simp [hvc] at this
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
      rw [hs']; exact ⟨r, hr'.sign _⟩
    knownVal_cert := fun r B h => by
      rw [hloc, hkn] at h; rw [hs']; exact (hv.knownVal_cert r B h).sign _
    lock_known := fun lk h hf => by
      rw [hloc, hlk] at h; rw [hloc, hkn]; exact hv.lock_known lk h hf }

omit [DecidableEq Owner] in
/-- `v` signs a confirmation vote for `B` in round `r`, advancing to `r`
and bumping its lock: the fast path, or Alg. on_certificate. -/
theorem VInv.sign_conf {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    (hv : VInv cfg s v) {l' : Local Block} {B : Block} {r : Round}
    (pr : Option (Proposal Owner Block))
    (hvv : l'.votedVal = (s.locals v).votedVal)
    (hvc : l'.votedConf = Function.update (s.locals v).votedConf r true)
    (hlk : l'.lock = (s.locals v).bumpLock B r) (hcur : l'.cur = r) (hle : (s.locals v).cur ≤ r)
    (hfin : l'.finalized = (s.locals v).finalized)
    (hnc : (s.locals v).votedConf r = false) (hvcert : ¬ cfg.IsFast r → s.ValCert B r)
    (hpr : cfg.IsFast r → ∃ P, pr = some P ∧ P.block = B ∧ P.round = r ∧
      cfg.FastEligible r P.owner)
    (hkn : ∀ r' B', l'.knownVal r' = some B' → (s.locals v).knownVal r' = some B' ∨
      (B' = B ∧ r' = r ∧ s.ValCert B r))
    (hknr : ¬ cfg.IsFast r → l'.knownVal r = some B) :
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
  have hloc : s'.locals v = l' := by simp [hs']
  -- the old lock, if any, is below `r` or equal to it; equal is excluded by `hnc`
  have hlock_lt : ∀ lk ∈ (s.locals v).lock, lk.2 < r := by
    intro lk hlk
    rcases Nat.lt_or_eq_of_le ((hv.lock_le_cur lk hlk).trans hle) with hlt | heq
    · exact hlt
    · exfalso
      have := (hv.votedConf_iff lk.2).2 ⟨lk.1, hv.lock_conf lk hlk⟩
      rw [heq] at this; simp [hnc] at this
  have hbump : l'.lock = some (B, r) := by
    rw [hlk]
    unfold Local.bumpLock
    cases hl : (s.locals v).lock with
    | none => rfl
    | some lk => simp [hlock_lt lk (by rw [hl]; rfl)]
  exact {
    votedVal_iff := fun r' => by rw [hloc, hvv]; simp only [hval]; exact hv.votedVal_iff r'
    votedConf_iff := fun r' => by
      rw [hloc, hvc]
      simp only [Function.update_apply]
      constructor
      · intro h
        split_ifs at h with hr'
        · exact ⟨B, (hconf _ _).2 (Or.inr ⟨rfl, hr'.symm⟩)⟩
        · obtain ⟨B', hB⟩ := (hv.votedConf_iff r').1 h
          exact ⟨B', (hconf _ _).2 (Or.inl hB)⟩
      · rintro ⟨B', hB⟩
        rcases (hconf _ _).1 hB with hB | ⟨_, rfl⟩
        · split_ifs with hr'
          · rfl
          · exact (hv.votedConf_iff r').2 ⟨B', hB⟩
        · simp
    val_le_cur := fun B' r' h => by
      rw [hloc, hcur]; exact (hv.val_le_cur B' r' ((hval _ _).1 h)).trans hle
    conf_le_cur := fun B' r' h => by
      rw [hloc, hcur]
      rcases (hconf _ _).1 h with h | ⟨_, rfl⟩
      · exact (hv.conf_le_cur B' r' h).trans hle
      · exact le_rfl
    val_unique := fun B₁ B₂ r' h₁ h₂ => hv.val_unique B₁ B₂ r' ((hval _ _).1 h₁) ((hval _ _).1 h₂)
    conf_unique := fun B₁ B₂ r' h₁ h₂ => by
      rcases (hconf _ _).1 h₁ with h₁ | ⟨hB₁, hr₁⟩
      · rcases (hconf _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · exact hv.conf_unique B₁ B₂ r' h₁ h₂
        · subst hr₂; exact absurd ((hv.votedConf_iff _).2 ⟨B₁, h₁⟩) (by simp [hnc])
      · rcases (hconf _ _).1 h₂ with h₂ | ⟨hB₂, hr₂⟩
        · subst hr₁; exact absurd ((hv.votedConf_iff _).2 ⟨B₂, h₂⟩) (by simp [hnc])
        · rw [← hB₁, ← hB₂]
    conf_valCert := fun B' r' h hf => by
      rw [hs']
      rcases (hconf _ _).1 h with h | ⟨rfl, rfl⟩
      · exact (hv.conf_valCert B' r' h hf).sign _
      · exact (hvcert hf).sign _
    lock_conf := fun lk h => by
      rw [hloc, hbump, Option.mem_def, Option.some.injEq] at h
      subst h
      exact (hconf _ _).2 (Or.inr ⟨rfl, rfl⟩)
    val_not_fast := fun B' r' h => hv.val_not_fast B' r' ((hval _ _).1 h)
    lock_le_cur := fun lk h => by
      rw [hloc, hbump, Option.mem_def, Option.some.injEq] at h
      subst h; rw [hloc, hcur]
    conf_le_lock := fun B' r' h => by
      rw [hloc, hbump]
      refine ⟨(B, r), rfl, ?_⟩
      rcases (hconf _ _).1 h with h | ⟨_, rfl⟩
      · obtain ⟨lk, hlk, hle'⟩ := hv.conf_le_lock B' r' h
        exact hle'.trans (hlock_lt lk hlk).le
      · exact le_rfl
    val_ghost := fun e' he' hs B' r' hm => by
      rw [hs'] at he' ⊢
      simp only [log_sign, log_set, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · refine ((hv.val_ghost e' he' hs B' r' hm).set v _).sign (fun B₀ r₀ h₀ => ?_)
        rw [he] at h₀
        simp only [Msg.conf.injEq] at h₀
        obtain ⟨_, rfl⟩ := h₀
        exact (hv.val_le_cur B' r' ⟨e', he', hs, hm⟩).trans hle
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
      rw [hs']; exact ⟨r', hr'.sign _⟩
    knownVal_cert := fun r' B' h => by
      rw [hloc] at h; rw [hs']
      rcases hkn r' B' h with h | ⟨rfl, rfl, hc⟩
      · exact (hv.knownVal_cert r' B' h).sign _
      · exact hc.sign _
    lock_known := fun lk h hf => by
      rw [hloc, hbump, Option.mem_def, Option.some.injEq] at h
      subst h; rw [hloc]; exact hknr hf }

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
  -- the three shapes a successor takes
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
    rw [LeanLinera.step] at h
    split_ifs at h with hf hok hok'
    · -- fast path
      rw [Option.some.injEq] at h; subst h
      obtain ⟨_, hfe, hr, _, hnc, _⟩ := hok
      refine frame_sign _ _ rfl (hvi.sign_conf (some P) rfl rfl rfl hr.symm hr.ge rfl hnc ?_
        (fun _ => ⟨P, rfl, rfl, rfl, hfe⟩) (fun _ _ h => Or.inl h) (fun hnf => absurd hf hnf))
      intro hnf; exact absurd hf hnf
    · obtain ⟨hok, hc⟩ := hok'
      rw [Option.some.injEq] at h; subst h
      exact frame_sign _ _ rfl (hvi.sign_val hok hc hf)
  | valCert B r =>
    rw [LeanLinera.step] at h
    split_ifs at h with hok hcv
    · -- a confirmation vote is signed
      obtain ⟨hcert, _, hle⟩ := hok
      have hnc := hcv.1
      simp only [Option.some.injEq] at h; subst h
      have hknEq : ((s.locals v).afterValCert B r).knownVal =
          Function.update (s.locals v).knownVal r (some B) := by simp [Local.afterValCert, hcv]
      refine frame_sign _ _ rfl (hvi.sign_conf none ?_ ?_ ?_ ?_ hle ?_ hnc (fun _ => hcert)
        (fun hf => absurd hcert (hs.not_valCert_fast hf)) ?_ ?_)
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv, Local.bumpLock]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · intro r' B' h'
        rw [hknEq, Function.update_apply] at h'
        split_ifs at h' with hr'
        · right; simp only [Option.some.injEq] at h'; exact ⟨h'.symm, hr', hcert⟩
        · left; exact h'
      · intro _; simp [hknEq]
    · -- the round advances without a vote
      obtain ⟨hcert, _, hle⟩ := hok
      simp only [Option.some.injEq] at h; subst h
      have hknEq : ((s.locals v).afterValCert B r).knownVal =
          Function.update (s.locals v).knownVal r (some B) := by simp [Local.afterValCert, hcv]
      refine frame_set _ (hvi.set_self ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv]
      · simp [Local.afterValCert, hcv, hle]
      · intro B' h'; left; simpa [Local.afterValCert, hcv] using h'
      · intro r' B' h'
        rw [hknEq, Function.update_apply] at h'
        split_ifs at h' with hr'
        · right; simp only [Option.some.injEq] at h'; subst h'; subst hr'; exact hcert
        · left; exact h'
      · intro r' B' h'
        rw [hknEq, Function.update_apply]
        split_ifs with hr'
        · subst hr'; rw [hs.valCert_unique hcert (hvi.knownVal_cert _ B' h')]
        · exact h'
  | confCert B r =>
    rw [LeanLinera.step] at h
    split_ifs at h with hok
    · obtain ⟨hcert, _⟩ := hok
      rw [Option.some.injEq] at h; subst h
      refine frame_set _ (hvi.set_self rfl rfl rfl le_rfl ?_ (fun _ _ h => Or.inl h)
        (fun _ _ h => h))
      intro B' h'
      simp only [Local.afterConfCert, Option.some.injEq] at h'
      subst h'; exact Or.inr ⟨r, hcert⟩
  | timeout r =>
    rw [LeanLinera.step] at h
    split_ifs at h with hok
    · rw [Option.some.injEq] at h; subst h
      exact frame_sign _ _ rfl (hvi.sign_time r _ rfl rfl rfl rfl rfl rfl)
  | timeoutCert r =>
    rw [LeanLinera.step] at h
    split_ifs at h with hok
    · rw [Option.some.injEq] at h; subst h
      refine frame_set _ (hvi.set_self ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · simp only [Local.afterTimeoutCert]; split_ifs <;> rfl
      · simp only [Local.afterTimeoutCert]; split_ifs <;> rfl
      · simp only [Local.afterTimeoutCert]; split_ifs <;> rfl
      · simp only [Local.afterTimeoutCert]; split_ifs with hle
        · exact hle.trans (Nat.le_succ r)
        · exact le_rfl
      · intro B' h'; left; simp only [Local.afterTimeoutCert] at h'; split_ifs at h' <;> exact h'
      · intro r' B' h'; left; simp only [Local.afterTimeoutCert] at h'; split_ifs at h' <;> exact h'
      · intro r' B' h'; simp only [Local.afterTimeoutCert]; split_ifs <;> exact h'

/-- The invariant holds in every reachable state. -/
theorem Inv.reachable {cfg : Config Owner Block} {s : State V Owner Block}
    (h : Reachable cfg s) : Inv cfg s := by
  induction h with
  | refl => exact Inv.init cfg
  | tail _ hstep ih =>
    obtain ⟨v, hv, i, hi⟩ := hstep
    exact ih.step hv hi

end LeanLinera
