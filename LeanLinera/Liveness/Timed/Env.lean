import LeanLinera.Liveness.Timed.Exec
import LeanLinera.Schedule

/-!
# The environment: partial synchrony and the honest owner

The assumptions of the paper's liveness theorem, as obligations on a
timed execution after a global stabilisation time `GST` with delay bound
`Δ` and an owner-side latency bound `L`:

* **leave_multi**: a validator in a multi-leader round leaves it within
  `L` (the honest owner proposes in the next round on a clash; Alg.
  client_propose, Lemma round-growth);
* **timeout**: a validator whose deadline has passed signs a timeout vote
  within `Δ` (the owner requests it; Alg. on_timeout);
* **tc_known**, **tc_honest**: a timeout certificate recorded by an honest
  validator, or formed from every honest validator's timeout vote, reaches
  every honest validator within `Δ` (the owner adopts, assembles and
  forwards it; Alg. on_timeout_certificate);
* **propose**: once every honest validator is in a single-leader round
  led solely by the honest owner, the owner's proposal — built by the
  re-proposal rule from the locking blocks read at some `t_q` — is
  attempted by every honest validator within `L`, and not before `t_q`;
* **cert**: a validation certificate for the owner's block in such a
  round is attempted by every honest validator within `L` (the owner
  forwards it, or finalizes the locking block);
* **leader**: the schedule designates the honest owner as sole leader of
  single-leader rounds beyond any bound (Lemma honest-single-leader);
* **inc_pos**: round durations grow (Lemma long-rounds);
* **fast_honest**, **fast_quiet**: the super owner, if any, proposes a
  single fast block and no fast-round proposal is still in flight after
  `GST` (Theorem liveness's hypothesis that no super owner equivocates).

Each obligation allows the escape "a block has been confirmed", since a
finalized validator takes no further step.
-/

namespace LeanLinera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

namespace TExec

variable {cfg : Config Owner Block} {tm : Timeouts} (ex : TExec (V := V) cfg tm)

/-- A block has been confirmed by tick `t`. -/
def Done (t : ℕ) : Prop := ∃ B r, (ex.st t).ConfCert B r

/-- Confirmation persists. -/
theorem Done.mono {t t' : ℕ} (h : t ≤ t') (hd : ex.Done t) : ex.Done t' :=
  let ⟨B, r, hc⟩ := hd; ⟨B, r, ex.HasCert_mono h hc⟩

/-- A finalized honest validator means a block has been confirmed. -/
theorem done_of_finalized {t : ℕ} {v : V} (hv : v ∈ Q.honest) {B : Block}
    (h : ((ex.st t).locals v).finalized = some B) : ex.Done t :=
  let ⟨r, hr⟩ := (ex.inv t v hv).finalized_cert B h; ⟨B, r, hr⟩

/-- The paper's re-proposal rule (Alg. client_propose, lines 13–15):
re-propose the newest locking block with itself as justification — a
validation certificate, or the fast-round proposal with the super owner's
signature — or a fresh block if no honest validator holds one. -/
def JustRule (cfg : Config Owner Block) (s : State V Owner Block) (P : Proposal Owner Block) :
    Prop :=
  (∃ B ρ w, w ∈ Q.honest ∧ (s.locals w).lb = some (.cert B ρ) ∧
    (∀ v ∈ Q.honest, ∀ lb ∈ (s.locals v).lb, lb.round ≤ ρ) ∧ P.just = .cert B ρ ∧ P.block = B) ∨
  (∃ B w, w ∈ Q.honest ∧ (s.locals w).lb = some (.fast B) ∧
    (∀ v ∈ Q.honest, (s.locals v).lb = none ∨ (s.locals v).lb = some (.fast B)) ∧
    P.just = .fast ∧ P.block = B ∧ cfg.fast = true) ∨
  ((∀ v ∈ Q.honest, (s.locals v).lb = none) ∧ P.just = .none)

/-- The environment of a timed execution. -/
structure Env where
  /-- The global stabilisation time. -/
  GST : ℕ
  /-- The message delay bound after `GST`. -/
  Δ : ℕ
  /-- The owner-side latency bound after `GST`. -/
  L : ℕ
  /-- The honest, active owner. -/
  o : Owner
  /-- The owner's proposal for each round, if any. -/
  prop : Round → Option (Proposal Owner Block)
  /-- An honest owner proposes at most one block per round. -/
  owner_prop : ∀ t v P, ex.act t = some (v, .proposal P) → P.owner = o → prop P.round = some P
  /-- A multi-leader round is left within `L`. -/
  leave_multi : ∀ t, GST ≤ t → ∀ v ∈ Q.honest, ex.cur v t < cfg.firstSL →
    ∃ t', t ≤ t' ∧ t' ≤ t + L ∧ (ex.cur v t < ex.cur v t' ∨ ex.Done t')
  /-- A passed deadline yields a timeout vote within `Δ`. -/
  timeout : ∀ t, GST ≤ t → ∀ v ∈ Q.honest, ∀ d, tm.dur cfg (ex.cur v t) = some d →
    ex.entry v t + d ≤ t → ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧
      ((ex.st t').HSig v (.time (ex.cur v t)) ∨ ex.cur v t < ex.cur v t' ∨ ex.Done t')
  /-- A timeout certificate recorded by an honest validator reaches every honest
  validator within `Δ` (the owner adopts and forwards it). -/
  tc_known : ∀ t, GST ≤ t → ∀ v ∈ Q.honest, ∀ τ ∈ ((ex.st t).locals v).tc, ∀ w ∈ Q.honest,
    ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧ (τ < ex.cur w t' ∨ ex.Done t')
  /-- Timeout votes from every honest validator form a certificate that reaches every
  honest validator within `Δ` (the owner assembles and forwards it). -/
  tc_honest : ∀ t, GST ≤ t → ∀ τ, (∀ v ∈ Q.honest, (ex.st t).HSig v (.time τ)) →
    ∀ w ∈ Q.honest, ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧ (τ < ex.cur w t' ∨ ex.Done t')
  /-- The owner's proposal in a round it leads solely reaches everyone within `L`. It
  is built by the re-proposal rule from the locking blocks at a tick `t_q` at which
  every honest validator was in the round, and attempted only from `t_q` on. -/
  propose : ∀ t, GST ≤ t → ∀ r, cfg.IsSingle r → (∀ o', cfg.Eligible r o' ↔ o' = o) →
    (∀ v ∈ Q.honest, ex.cur v t = r) → ¬ ex.Done t →
    ∃ P t_q, (∀ v ∈ Q.honest, ex.cur v t_q = r) ∧ t_q ≤ t + L ∧ prop r = some P ∧
      P.round = r ∧ P.owner = o ∧ cfg.Valid P.block ∧ JustRule cfg (ex.st t_q) P ∧
      (∀ v ∈ Q.honest, ∃ t', t_q ≤ t' ∧ t' ≤ t + L ∧ ex.act t' = some (v, .proposal P)) ∧
      (∀ t' < t_q, ∀ v, ex.act t' ≠ some (v, .proposal P))
  /-- A validation certificate for a block in a round the owner leads solely, once every
  honest validator is in the round and the owner can hold the certificate (every honest
  validator voted for it, or one reports it as its locking block), reaches everyone
  within `L`. -/
  cert : ∀ t, GST ≤ t → ∀ r, cfg.IsSingle r → (∀ o', cfg.Eligible r o' ↔ o' = o) → ∀ B,
    (∀ v ∈ Q.honest, ex.cur v t = r) →
    ((∀ v ∈ Q.honest, (ex.st t).HSig v (.val B r)) ∨
      ∃ v ∈ Q.honest, ((ex.st t).locals v).lb = some (.cert B r)) →
    ∀ v ∈ Q.honest, ∃ t', t ≤ t' ∧ t' ≤ t + L ∧ ex.act t' = some (v, .valCert B r)
  /-- The owner is the sole leader of single-leader rounds beyond any bound. -/
  leader : ∀ N, ∃ r, N ≤ r ∧ cfg.IsSingle r ∧ ∀ o', cfg.Eligible r o' ↔ o' = o
  /-- Round durations grow. -/
  inc_pos : 0 < tm.inc
  /-- The super owner's fast block, if any. -/
  fastBlock : Option Block
  /-- The super owner does not equivocate: every fast-round proposal, and every
  re-proposal carrying the fast-round signature, is of its one fast block. -/
  fast_honest : ∀ t v P, ex.act t = some (v, .proposal P) →
    (cfg.IsFast P.round ∨ P.just = .fast) → fastBlock = some P.block
  /-- No fast-round proposal is still in flight after `GST`. -/
  fast_quiet : ∀ t, GST ≤ t → ∀ v P, ex.act t = some (v, .proposal P) → ¬ cfg.IsFast P.round

/-! ### Consequences -/

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- A single-leader round is not the fast round. -/
theorem not_isFast_of_isSingle {r : Round} (hr : cfg.IsSingle r) : ¬ cfg.IsFast r := by
  rintro ⟨h1, h0⟩
  unfold Config.IsSingle Config.firstSL Config.firstMulti at hr
  rw [h1] at hr; simp at hr; omega

omit [DecidableEq Owner] [DecidableEq Block] in
/-- A single-leader round has a duration, growing with its index. -/
theorem dur_single {r : Round} (hr : cfg.IsSingle r) :
    tm.dur cfg r = some (tm.base + (r - cfg.firstSL) * tm.inc) := by
  unfold Timeouts.dur
  rw [ite_eq_right (not_isFast_of_isSingle hr), ite_eq_left hr]

/-- Every log entry answering a proposal was created by an attempt of that proposal. -/
theorem log_entry_act (t : ℕ) : ∀ e ∈ (ex.st t).log, ∀ P, e.prop = some P →
    ∃ t' < t, ex.act t' = some (e.signer, .proposal P) := by
  induction t with
  | zero =>
    intro e he; rw [ex.zero] at he; simp [State.init] at he
  | succ t ih =>
    intro e he P hP
    rw [ex.succ] at he
    rcases hact : ex.act t with _ | ⟨v, i⟩ <;> rw [hact] at he
    · obtain ⟨t', ht', h⟩ := ih e he P hP; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    simp only [stepOpt] at he
    rcases hst : step cfg (ex.st t) v i with _ | s' <;> rw [hst] at he
    · obtain ⟨t', ht', h⟩ := ih e he P hP; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    simp only [Option.getD_some] at he
    rcases step_log hst with hl | ⟨e', hl⟩
    · rw [hl] at he
      obtain ⟨t', ht', h⟩ := ih e he P hP; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    · rw [hl, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · obtain ⟨t', ht', h⟩ := ih e he P hP; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
      · -- the new entry: only a proposal step creates an entry with a proposal
        cases i with
        | proposal P' =>
          rw [LeanLinera.step] at hst
          split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst
          · simp only [log_sign, log_set, List.append_cancel_left_eq, List.cons.injEq,
              and_true] at hl
            subst hl; simp only [Option.some.injEq] at hP; subst hP
            exact ⟨t, Nat.lt_succ_self t, hact⟩
          · simp only [log_sign, log_set, List.append_cancel_left_eq, List.cons.injEq,
              and_true] at hl
            subst hl; simp only [Option.some.injEq] at hP; subst hP
            exact ⟨t, Nat.lt_succ_self t, hact⟩
          · simp at hl
        | valCert B r =>
          rw [LeanLinera.step] at hst
          split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst
          · simp only [log_sign, log_set, List.append_cancel_left_eq, List.cons.injEq,
              and_true] at hl
            subst hl; simp at hP
          · simp at hl
        | confCert B r =>
          rw [LeanLinera.step] at hst
          split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst; simp at hl
        | timeout r =>
          rw [LeanLinera.step] at hst
          split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
          simp only [log_sign, log_set, List.append_cancel_left_eq, List.cons.injEq,
            and_true] at hl
          subst hl; simp at hP
        | timeoutCert r =>
          rw [LeanLinera.step] at hst
          split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst; simp at hl

/-- Every timeout vote was created by a timeout step at the signer's current round. -/
theorem log_time_act (t : ℕ) : ∀ v ρ, (ex.st t).HSig v (.time ρ) →
    ∃ t' < t, ex.act t' = some (v, .timeout ρ) ∧ ex.cur v t' = ρ := by
  induction t with
  | zero =>
    intro v ρ h; rw [ex.zero] at h; simp [HSig, State.init] at h
  | succ t ih =>
    intro v ρ h
    rw [ex.succ] at h
    rcases hact : ex.act t with _ | ⟨w, i⟩ <;> rw [hact] at h
    · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    simp only [stepOpt] at h
    rcases hst : step cfg (ex.st t) w i with _ | s' <;> rw [hst] at h
    · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    simp only [Option.getD_some] at h
    cases i with
    | timeout ρ' =>
      rw [LeanLinera.step] at hst
      split_ifs at hst with hok; simp only [Option.some.injEq] at hst; subst hst
      rcases (HSig_sign _ _ _ _).1 h with h | ⟨rfl, hm⟩
      · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
      · simp only [Msg.time.injEq] at hm; subst hm
        exact ⟨t, Nat.lt_succ_self t, hact, hok.2.1.symm⟩
    | proposal P =>
      rw [LeanLinera.step] at hst
      split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst
      · rcases (HSig_sign _ _ _ _).1 h with h | ⟨_, hm⟩
        · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
        · cases hm
      · rcases (HSig_sign _ _ _ _).1 h with h | ⟨_, hm⟩
        · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
        · cases hm
      · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    | valCert B r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst
      · rcases (HSig_sign _ _ _ _).1 h with h | ⟨_, hm⟩
        · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
        · cases hm
      · obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    | confCert B r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩
    | timeoutCert r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      obtain ⟨t', ht', h⟩ := ih v ρ h; exact ⟨t', ht'.trans (Nat.lt_succ_self t), h⟩

/-- In a single-leader round led solely by `o`, every honest validation
vote answers `o`'s proposal for that round. -/
theorem val_of_sole (env : ex.Env) {r : Round} (hsole : ∀ o', cfg.Eligible r o' ↔ o' = env.o)
    {t : ℕ} {v : V} (hv : v ∈ Q.honest) {B : Block} (h : (ex.st t).HSig v (.val B r)) :
    ∃ P t', env.prop r = some P ∧ P.block = B ∧ P.round = r ∧ t' < t ∧
      ex.act t' = some (v, .proposal P) := by
  obtain ⟨e, he, hs, hm⟩ := h
  obtain ⟨P, hP, hB, hr, helig, _⟩ := ((ex.inv t v hv).val_ghost e he hs B r hm).prop_elig
  have ho : P.owner = env.o := (hsole P.owner).1 helig
  obtain ⟨t', ht', hact⟩ := ex.log_entry_act t e he P hP
  rw [hs] at hact
  refine ⟨P, t', ?_, hB, hr, ht', hact⟩
  rw [← hr]; exact env.owner_prop t' v P hact ho

/-- Every fast-round locking block is of the super owner's fast block, and
only a chain with a fast round has one: it was set by confirming a
fast-round proposal or by a proposal carrying the fast-round signature. -/
theorem lb_fast_block' {fb : Option Block}
    (hfh : ∀ t v P, ex.act t = some (v, .proposal P) →
      (cfg.IsFast P.round ∨ P.just = .fast) → fb = some P.block) (t : ℕ) : ∀ v B',
    ((ex.st t).locals v).lb = some (.fast B') → fb = some B' ∧ cfg.fast = true := by
  induction t with
  | zero => intro v B' h; rw [ex.zero] at h; simp [State.init, Local.init] at h
  | succ t ih =>
    intro v B' h
    rw [ex.succ] at h
    rcases hact : ex.act t with _ | ⟨w, i⟩ <;> rw [hact] at h
    · exact ih v B' h
    simp only [stepOpt] at h
    rcases hst : step cfg (ex.st t) w i with _ | s' <;> rw [hst] at h
    · exact ih v B' h
    simp only [Option.getD_some] at h
    by_cases hwv : v = w
    swap
    · rw [step_locals_of_ne hst hwv] at h; exact ih v B' h
    subst hwv
    cases i with
    | proposal P =>
      rw [LeanLinera.step] at hst
      split_ifs at hst with hf hok hpre hacc <;> simp only [Option.some.injEq] at hst <;> subst hst
      · simp only [locals_sign, locals_set_self, Local.afterFast, Option.some.injEq,
          Locking.fast.injEq] at h
        subst h; exact ⟨hfh t v P hact (Or.inl hf), hf.1⟩
      · simp only [locals_sign, locals_set_self, Local.afterVal] at h
        rcases ((ex.st t).locals v).lbAfter_fast P h with h | ⟨_, hj, rfl⟩
        · exact ih v B' h
        · refine ⟨hfh t v P hact (Or.inr hj), ?_⟩
          have hjo := hpre.1.2.2.1
          unfold Local.JustOk at hjo; rw [hj] at hjo; exact hjo.1
      · simp only [locals_set_self, Local.afterBump] at h; exact ih v B' h
    | valCert B r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst with hok hcv <;> simp only [Option.some.injEq] at hst <;> subst hst
      · have : (((ex.st t).locals v).afterValCert B r).lb = some (.cert B r) := by
          simp [Local.afterValCert, hcv]
        simp only [locals_sign, locals_set_self] at h; rw [this] at h; cases h
      · have : (((ex.st t).locals v).afterValCert B r).lb = some (.cert B r) := by
          simp [Local.afterValCert, hcv]
        simp only [locals_set_self] at h; rw [this] at h; cases h
    | confCert B r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_set_self, Local.afterConfCert] at h; exact ih v B' h
    | timeout r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_sign, locals_set_self, Local.afterTimeout] at h; exact ih v B' h
    | timeoutCert r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_set_self, Local.afterTimeoutCert] at h; exact ih v B' h

/-- Every fast-round locking block is of the super owner's fast block. -/
theorem lb_fast_block (env : ex.Env) (t : ℕ) : ∀ v B',
    ((ex.st t).locals v).lb = some (.fast B') → env.fastBlock = some B' ∧ cfg.fast = true :=
  ex.lb_fast_block' env.fast_honest t

/-- A recorded timeout certificate exists. -/
theorem tc_field_cert (t : ℕ) : ∀ v τ, ((ex.st t).locals v).tc = some τ →
    (ex.st t).TimeoutCert τ := by
  induction t with
  | zero => intro v τ h; rw [ex.zero] at h; simp [State.init, Local.init] at h
  | succ t ih =>
    intro v τ h
    rw [ex.succ] at h ⊢
    rcases hact : ex.act t with _ | ⟨w, i⟩ <;> rw [hact] at h
    · exact ih v τ h
    simp only [stepOpt] at h ⊢
    rcases hst : step cfg (ex.st t) w i with _ | s' <;> rw [hst] at h
    · exact ih v τ h
    simp only [Option.getD_some] at h ⊢
    by_cases hwv : v = w
    swap
    · rw [step_locals_of_ne hst hwv] at h; exact step_HasCert hst (ih v τ h)
    subst hwv
    cases i with
    | proposal P =>
      rw [LeanLinera.step] at hst
      split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst <;>
        simp only [locals_sign, locals_set_self, Local.afterFast, Local.afterVal,
          Local.afterBump] at h
      · exact (ih v τ h).sign _
      · exact (ih v τ h).sign _
      · exact ih v τ h
    | valCert B r =>
      rw [LeanLinera.step] at hst
      have htc : (((ex.st t).locals v).afterValCert B r).tc = ((ex.st t).locals v).tc := by
        simp only [Local.afterValCert]; split_ifs <;> rfl
      split_ifs at hst <;> simp only [Option.some.injEq] at hst <;> subst hst <;>
        simp only [locals_sign, locals_set_self, htc] at h
      · exact (ih v τ h).sign _
      · exact ih v τ h
    | confCert B r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_set_self, Local.afterConfCert] at h; exact ih v τ h
    | timeout r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_sign, locals_set_self, Local.afterTimeout] at h; exact (ih v τ h).sign _
    | timeoutCert r =>
      rw [LeanLinera.step] at hst
      split_ifs at hst with hok; simp only [Option.some.injEq] at hst; subst hst
      simp only [locals_set_self, Local.afterTimeoutCert, Option.some.injEq] at h
      subst h; exact hok.1

/-- Lists of honest validators: there is one containing every honest
validator, without duplicates. -/
theorem exists_honest_list : ∃ L : List V, L.Nodup ∧ (∀ v ∈ Q.honest, v ∈ L) ∧
    ∀ v ∈ L, v ∈ Q.honest :=
  ⟨Q.honest.toList, Finset.nodup_toList _, fun _ hv => Finset.mem_toList.2 hv,
    fun _ hv => Finset.mem_toList.1 hv⟩

end TExec

end LeanLinera
