import Linera.Protocol

/-!
# Runs of honest inputs

Frame and monotonicity lemmas for a single honest step (it changes only the
acting validator's local state and only extends the log), lifted to runs;
a certificate from every honest signature; and the broadcast lemma
`run_each`: delivering one input to each validator of a duplicate-free
list succeeds, and every one of them signs, as soon as each is ready for it
and readiness is kept by the others' steps.
-/

namespace Linera

variable {V Owner Block : Type*} [Fintype V] [DecidableEq V] [Q : QuorumSystem V]
  [DecidableEq Owner] [DecidableEq Block]

open State

omit [DecidableEq Owner] in
/-- A quorum of honest signatures: the honest validators form a quorum. -/
theorem State.HasCert_of_honest {s : State V Owner Block} {m : Msg Block}
    (h : ∀ v ∈ Q.honest, s.HSig v m) : s.HasCert m := by
  refine Q.quorum_mono ?_ Q.quorum_honest
  intro v hv
  rw [mem_signers]
  exact Signed_of_HSig (h v hv)

/-! ## One step -/

/-- A step at `v` leaves every other local state unchanged. -/
theorem step_locals_of_ne {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') {w : V} (hw : w ≠ v) :
    s'.locals w = s.locals w := by
  cases i with
  | proposal P =>
    rw [Linera.step] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp [locals_set_of_ne _ _ hw]
  | valCert B r =>
    rw [Linera.step] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp [locals_set_of_ne _ _ hw]
  | confCert B r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    simp [locals_set_of_ne _ _ hw]
  | timeout r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    simp [locals_set_of_ne _ _ hw]
  | timeoutCert r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    simp [locals_set_of_ne _ _ hw]

/-- A step only extends the log. -/
theorem step_log {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') :
    s'.log = s.log ∨ ∃ e, s'.log = s.log ++ [e] := by
  cases i with
  | proposal P =>
    rw [Linera.step] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
  | valCert B r =>
    rw [Linera.step] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
  | confCert B r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; simp
  | timeout r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; simp
  | timeoutCert r =>
    rw [Linera.step] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; simp

/-- Signatures persist across a step. -/
theorem step_HSig {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') {w : V} {m : Msg Block}
    (hm : s.HSig w m) : s'.HSig w m := by
  obtain ⟨e, he, hs⟩ := hm
  rcases step_log h with hl | ⟨e', hl⟩
  · exact ⟨e, hl ▸ he, hs⟩
  · exact ⟨e, by rw [hl]; exact List.mem_append_left _ he, hs⟩

/-- Certificates persist across a step. -/
theorem step_HasCert {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') {m : Msg Block}
    (hm : s.HasCert m) : s'.HasCert m := by
  refine Q.quorum_mono ?_ hm
  intro w hw
  rw [mem_signers] at hw ⊢
  rcases hw with hw | hw
  · exact Or.inl hw
  · exact Or.inr (step_HSig h hw)

/-! ## Runs -/

/-- Signatures persist across a run. -/
theorem run_HSig {cfg : Config Owner Block} {L : List (V × Input Owner Block)}
    {s s' : State V Owner Block} (h : run cfg L s = some s') {w : V} {m : Msg Block}
    (hm : s.HSig w m) : s'.HSig w m := by
  induction L generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst h; exact hm
  | cons p rest ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ih h₂ (step_HSig h₁ hm)

/-- Certificates persist across a run. -/
theorem run_HasCert {cfg : Config Owner Block} {L : List (V × Input Owner Block)}
    {s s' : State V Owner Block} (h : run cfg L s = some s') {m : Msg Block}
    (hm : s.HasCert m) : s'.HasCert m := by
  induction L generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst h; exact hm
  | cons p rest ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ih h₂ (step_HasCert h₁ hm)

/-- A run leaves the local state of every validator it does not visit unchanged. -/
theorem run_locals_of_not_mem {cfg : Config Owner Block} {L : List (V × Input Owner Block)}
    {s s' : State V Owner Block} (h : run cfg L s = some s') {w : V}
    (hw : ∀ p ∈ L, p.1 ≠ w) : s'.locals w = s.locals w := by
  induction L generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst h; rfl
  | cons p rest ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    rw [ih h₂ (fun q hq => hw q (List.mem_cons_of_mem _ hq)),
      step_locals_of_ne h₁ (hw p (List.mem_cons_self ..)).symm]

/-- A property kept by every step of a run is kept by the run. -/
theorem run_preserve {cfg : Config Owner Block} (R : State V Owner Block → Prop)
    {L : List (V × Input Owner Block)} {s s' : State V Owner Block} (h : run cfg L s = some s')
    (hstep : ∀ p ∈ L, ∀ t t', step cfg t p.1 p.2 = some t' → R t → R t') (hs : R s) : R s' := by
  induction L generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst h; exact hs
  | cons p rest ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s₁, h₁, h₂⟩ := h
    exact ih h₂ (fun q hq => hstep q (List.mem_cons_of_mem _ hq))
      (hstep p (List.mem_cons_self ..) s s₁ h₁ hs)

/-- Runs compose. -/
theorem run_append {cfg : Config Owner Block} (L₁ L₂ : List (V × Input Owner Block))
    (s : State V Owner Block) :
    run cfg (L₁ ++ L₂) s = (run cfg L₁ s).bind (run cfg L₂) := by
  induction L₁ generalizing s with
  | nil => simp [run]
  | cons p rest ih =>
    simp only [List.cons_append, run, Option.bind_assoc]
    congr 1
    funext s₁
    exact ih s₁

/-- **Broadcast.** Deliver input `i` to each validator of a duplicate-free
list `L`. If every `v ∈ L` is ready (`P s v`), a ready validator's step
succeeds and signs `m`, and readiness of the others survives any step at
`v`, then the run succeeds and every `v ∈ L` has signed `m`. -/
theorem run_each {cfg : Config Owner Block} (i : Input Owner Block) (m : Msg Block)
    (P : State V Owner Block → V → Prop)
    (hstep : ∀ s v, P s v → ∃ s', step cfg s v i = some s' ∧ s'.HSig v m)
    (hkeep : ∀ s s' v w, step cfg s v i = some s' → w ≠ v → P s w → P s' w) :
    ∀ (L : List V), L.Nodup → ∀ s : State V Owner Block, (∀ v ∈ L, P s v) →
      ∃ s', run cfg (L.map fun v => (v, i)) s = some s' ∧ ∀ v ∈ L, s'.HSig v m := by
  intro L
  induction L with
  | nil => intro _ s _; exact ⟨s, rfl, fun v hv => absurd hv (List.not_mem_nil)⟩
  | cons v rest ih =>
    intro hnd s hP
    rw [List.nodup_cons] at hnd
    obtain ⟨s₁, h₁, hsig⟩ := hstep s v (hP v (List.mem_cons_self ..))
    have hP₁ : ∀ w ∈ rest, P s₁ w := fun w hw =>
      hkeep s s₁ v w h₁ (fun hwv => hnd.1 (hwv ▸ hw)) (hP w (List.mem_cons_of_mem _ hw))
    obtain ⟨s', h', hsig'⟩ := ih hnd.2 s₁ hP₁
    refine ⟨s', ?_, ?_⟩
    · simp only [List.map_cons, run, h₁, Option.bind_some]; exact h'
    · intro w hw
      rw [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact run_HSig h' hsig
      · exact hsig' w hw

end Linera
