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
* **tc**: a timeout certificate reaches every honest validator within `Δ`
  (the owner adopts and forwards it; Alg. on_timeout_certificate);
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
* **no_fast**: the chain has no fast round (the fast-round extension is
  not covered by the timed theorem).

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

/-- The paper's re-proposal rule (Alg. client_propose, lines 13–15),
without a fast round: re-propose the newest locking block with itself as
justification, or a fresh block if no honest validator holds one. -/
def JustRule (s : State V Owner Block) (P : Proposal Owner Block) : Prop :=
  (∃ B ρ w, w ∈ Q.honest ∧ (s.locals w).lb = some (.cert B ρ) ∧
    (∀ v ∈ Q.honest, ∀ lb ∈ (s.locals v).lb, lb.round ≤ ρ) ∧ P.just = .cert B ρ ∧ P.block = B) ∨
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
  /-- A timeout certificate reaches every honest validator within `Δ`. -/
  tc : ∀ t, GST ≤ t → ∀ r, (ex.st t).TimeoutCert r → ∀ v ∈ Q.honest,
    ∃ t', t ≤ t' ∧ t' ≤ t + Δ ∧ (r < ex.cur v t' ∨ ex.Done t')
  /-- The owner's proposal in a round it leads solely reaches everyone within `L`. -/
  propose : ∀ t, GST ≤ t → ∀ r, cfg.IsSingle r → (∀ o', cfg.Eligible r o' ↔ o' = o) →
    (∀ v ∈ Q.honest, ex.cur v t = r) → ¬ ex.Done t →
    ∃ P t_q, t ≤ t_q ∧ t_q ≤ t + L ∧ prop r = some P ∧ P.round = r ∧ P.owner = o ∧
      cfg.Valid P.block ∧ JustRule (ex.st t_q) P ∧
      (∀ v ∈ Q.honest, ∃ t', t_q ≤ t' ∧ t' ≤ t + L ∧ ex.act t' = some (v, .proposal P)) ∧
      (∀ t' < t_q, ∀ v, ex.act t' ≠ some (v, .proposal P))
  /-- A validation certificate for a block in a round the owner leads solely reaches
  everyone within `L`. -/
  cert : ∀ t, GST ≤ t → ∀ r, cfg.IsSingle r → (∀ o', cfg.Eligible r o' ↔ o' = o) → ∀ B,
    (ex.st t).ValCert B r → ∀ v ∈ Q.honest,
      ∃ t', t ≤ t' ∧ t' ≤ t + L ∧ ex.act t' = some (v, .valCert B r)
  /-- The owner is the sole leader of single-leader rounds beyond any bound. -/
  leader : ∀ N, ∃ r, N ≤ r ∧ cfg.IsSingle r ∧ ∀ o', cfg.Eligible r o' ↔ o' = o
  /-- Round durations grow. -/
  inc_pos : 0 < tm.inc
  /-- No fast round. -/
  no_fast : cfg.fast = false

/-! ### Consequences -/

omit [Fintype V] [DecidableEq V] Q [DecidableEq Owner] [DecidableEq Block] in
/-- Without a fast round, no round is fast. -/
theorem not_isFast_of_no_fast (hnf : cfg.fast = false) (r : Round) : ¬ cfg.IsFast r := by
  rintro ⟨h1, _⟩; rw [hnf] at h1; exact Bool.false_ne_true h1

omit [DecidableEq Owner] [DecidableEq Block] in
/-- A single-leader round has a duration, growing with its index. -/
theorem dur_single (hnf : cfg.fast = false) {r : Round} (hr : cfg.IsSingle r) :
    tm.dur cfg r = some (tm.base + (r - cfg.firstSL) * tm.inc) := by
  unfold Timeouts.dur
  rw [ite_eq_right (not_isFast_of_no_fast hnf r), ite_eq_left hr]

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
  obtain ⟨P, hP, hB, hr, helig⟩ := ((ex.inv t v hv).val_ghost e he hs B r hm).prop_elig
  have ho : P.owner = env.o := (hsole P.owner).1 helig
  obtain ⟨t', ht', hact⟩ := ex.log_entry_act t e he P hP
  rw [hs] at hact
  refine ⟨P, t', ?_, hB, hr, ht', hact⟩
  rw [← hr]; exact env.owner_prop t' v P hact ho

/-- Lists of honest validators: there is one containing every honest
validator, without duplicates. -/
theorem exists_honest_list : ∃ L : List V, L.Nodup ∧ (∀ v ∈ Q.honest, v ∈ L) ∧
    ∀ v ∈ L, v ∈ Q.honest :=
  ⟨Q.honest.toList, Finset.nodup_toList _, fun _ hv => Finset.mem_toList.2 hv,
    fun _ hv => Finset.mem_toList.1 hv⟩

end TExec

end LeanLinera
