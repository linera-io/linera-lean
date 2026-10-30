import Linera.Chain.Message
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Induction

/-!
# The inbox

A recipient chain's inbox for one sender, as implemented in
`linera-chain/src/inbox.rs` (`InboxStateView`): two queues of bundles
ordered by cursor and two cursors.

* `nextAdd`: every bundle below it has been added (delivered);
* `nextRemove`: every bundle below it has been removed (consumed by a
  block of the recipient);
* `added`: delivered and waiting to be consumed;
* `removed`: consumed by anticipation (a certified block of the recipient
  consumed them before they were delivered) and waiting to be delivered.

At most one of the queues is non-empty. `add` is `add_bundle` and `remove`
is `remove_bundle`, with their error cases as `none`; the restored-cursor
check for checkpoints is omitted.

The main theorem, `run_eq_canonical`, is the paper's commutativity claim
(`execution_model.tex`, Inbox state) in the form the implementation
satisfies: a succeeding sequence of adds and removes yields an inbox that
depends only on the sequence of added bundles and the sequence of removed
bundles, not on their interleaving.
-/

namespace Linera

variable {Payload : Type*}

/-- The inbox of a recipient for one sender. -/
structure Inbox (Payload : Type*) where
  /-- All bundles below this cursor have been added. -/
  nextAdd : Cursor
  /-- All bundles below this cursor have been removed. -/
  nextRemove : Cursor
  /-- Added, waiting to be removed. -/
  added : List (Bundle Payload)
  /-- Removed by anticipation, waiting to be added. -/
  removed : List (Bundle Payload)
  deriving DecidableEq, Repr

namespace Inbox

/-- The empty inbox. -/
def init : Inbox Payload := ⟨Cursor.zero, Cursor.zero, [], []⟩

/-- Discard the added bundles below `c`, which must all be skippable
(`remove_bundle`, the "Skipping previously received bundle" loop). -/
def dropBelow (c : Cursor) : List (Bundle Payload) → Option (List (Bundle Payload))
  | [] => some []
  | a :: rest =>
    if a.cursor < c then
      if a.skippable then dropBelow c rest else none
    else some (a :: rest)

/-- An inbox operation. -/
inductive Op (Payload : Type*)
  /-- Deliver a bundle. -/
  | add (b : Bundle Payload)
  /-- Consume a bundle. -/
  | remove (b : Bundle Payload)
  deriving DecidableEq, Repr

/-- The bundles added by a sequence of operations, in order. -/
def adds : List (Op Payload) → List (Bundle Payload)
  | [] => []
  | .add b :: rest => b :: adds rest
  | .remove _ :: rest => adds rest

/-- The bundles removed by a sequence of operations, in order. -/
def removes : List (Op Payload) → List (Bundle Payload)
  | [] => []
  | .add _ :: rest => removes rest
  | .remove b :: rest => b :: removes rest

/-! ### Canonical form -/

/-- A list of bundles with strictly increasing cursors. -/
def Sorted (L : List (Bundle Payload)) : Prop := L.Pairwise (fun a b => a.cursor < b.cursor)

/-- The cursor after the last bundle of a list (`Cursor.zero` for `[]`). -/
def after (L : List (Bundle Payload)) : Cursor :=
  L.foldl (fun _ b => b.cursor.succ) Cursor.zero

/-- The inbox determined by the sequence `A` of added bundles and the
sequence `R` of removed bundles: the added bundles not yet removed are
those at or above the cursor after `R`, and symmetrically. -/
def canonical (A R : List (Bundle Payload)) : Inbox Payload where
  nextAdd := after A
  nextRemove := after R
  added := A.filter (fun a => decide (after R ≤ a.cursor))
  removed := R.filter (fun r => decide (after A ≤ r.cursor))

/-! ### Lemmas on `after` and sorted lists -/

theorem after_nil : after ([] : List (Bundle Payload)) = Cursor.zero := rfl

theorem after_append (L : List (Bundle Payload)) (b : Bundle Payload) :
    after (L ++ [b]) = b.cursor.succ := by
  simp [after, List.foldl_append]

/-- Every bundle of a sorted list is below the cursor after it. -/
theorem lt_after_of_mem {L : List (Bundle Payload)} (hL : Sorted L) {a : Bundle Payload}
    (ha : a ∈ L) : a.cursor < after L := by
  induction L using List.reverseRecOn with
  | nil => simp at ha
  | append_singleton L b ih =>
    rw [after_append]
    rw [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have hlt : a.cursor < b.cursor := by
        rw [Sorted, List.pairwise_append] at hL
        exact hL.2.2 a ha b (List.mem_singleton_self b)
      exact hlt.trans (Cursor.lt_succ_self _)
    · exact Cursor.lt_succ_self _

/-- If every bundle of a list is below `c`, so is the cursor after it. -/
theorem after_le_of_forall_lt {L : List (Bundle Payload)} {c : Cursor}
    (h : ∀ a ∈ L, a.cursor < c) : after L ≤ c := by
  induction L using List.reverseRecOn with
  | nil => exact Cursor.zero_le c
  | append_singleton L b _ =>
    rw [after_append]
    exact Cursor.lt_iff_succ_le.1 (h b (by simp))

theorem Sorted.append_singleton {L : List (Bundle Payload)} (hL : Sorted L) {b : Bundle Payload}
    (hb : after L ≤ b.cursor) : Sorted (L ++ [b]) := by
  rw [Sorted, List.pairwise_append]
  refine ⟨hL, List.pairwise_singleton _ _, ?_⟩
  intro a ha b' hb'
  rw [List.mem_singleton] at hb'; subst hb'
  exact (lt_after_of_mem hL ha).trans_le hb

theorem Sorted.filter {L : List (Bundle Payload)} (hL : Sorted L) (p : Bundle Payload → Bool) :
    Sorted (L.filter p) := List.Pairwise.filter p hL

/-- In a sorted list, the elements after the first one at or above `c` are
exactly those above it. -/
theorem filter_tail {L : List (Bundle Payload)} (hL : Sorted L) {c : Cursor}
    {r : Bundle Payload} {rest : List (Bundle Payload)}
    (h : L.filter (fun a => decide (c ≤ a.cursor)) = r :: rest) :
    rest = L.filter (fun a => decide (r.cursor.succ ≤ a.cursor)) := by
  induction L with
  | nil => simp at h
  | cons x L ih =>
    have hx : ∀ y ∈ L, x.cursor < y.cursor := fun _ hy => List.rel_of_pairwise_cons hL hy
    have hL' : Sorted L := List.Pairwise.of_cons hL
    rw [List.filter_cons] at h
    by_cases hcx : c ≤ x.cursor
    · simp only [hcx, decide_true] at h
      obtain ⟨hxr, hLr⟩ := List.cons.inj h
      subst hxr; subst hLr
      rw [List.filter_cons]
      have : ¬ x.cursor.succ ≤ x.cursor := not_le.2 (Cursor.lt_succ_self _)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      have h1 : L.filter (fun a => decide (x.cursor.succ ≤ a.cursor)) = L :=
        List.filter_eq_self.2 (fun y hy => by simpa using Cursor.lt_iff_succ_le.1 (hx y hy))
      have h2 : L.filter (fun a => decide (c ≤ a.cursor)) = L :=
        List.filter_eq_self.2 (fun y hy => by simpa using hcx.trans (hx y hy).le)
      rw [h1, h2]
    · simp only [hcx, decide_false] at h
      rw [ih hL' h, List.filter_cons]
      have hr : c ≤ r.cursor := by
        have := List.of_mem_filter (p := fun a : Bundle Payload => decide (c ≤ a.cursor))
          (h ▸ List.mem_cons_self)
        simpa using this
      have : ¬ r.cursor.succ ≤ x.cursor := by
        rw [← Cursor.lt_iff_succ_le]; exact not_lt.2 ((not_le.1 hcx).le.trans hr)
      simp [this]

/-- Dropping the bundles below `c` from a sorted list, when it succeeds,
leaves exactly those at or above `c`. -/
theorem dropBelow_eq {L : List (Bundle Payload)} (hL : Sorted L) {c : Cursor}
    {L' : List (Bundle Payload)} (h : dropBelow c L = some L') :
    L' = L.filter (fun a => decide (c ≤ a.cursor)) := by
  induction L generalizing L' with
  | nil => simp [dropBelow] at h; simp [h]
  | cons x L ih =>
    have hx : ∀ y ∈ L, x.cursor < y.cursor := fun _ hy => List.rel_of_pairwise_cons hL hy
    have hL' : Sorted L := List.Pairwise.of_cons hL
    rw [dropBelow] at h
    by_cases hxc : x.cursor < c
    · simp only [hxc, ite_true] at h
      split at h
      · rw [ih hL' h, List.filter_cons]; simp [not_le.2 hxc]
      · exact absurd h (by simp)
    · simp only [hxc, ite_false, Option.some.injEq] at h
      subst h
      rw [List.filter_cons]
      simp only [not_lt.1 hxc, decide_true]
      congr 1
      symm
      rw [List.filter_eq_self]
      intro y hy
      simpa using (not_lt.1 hxc).trans (hx y hy).le

theorem canonical_nil_nil : (canonical [] [] : Inbox Payload) = init := rfl

section Ops

variable [DecidableEq Payload]

/-- Consume a bundle (`remove_bundle`). -/
def remove (b : Bundle Payload) (I : Inbox Payload) : Option (Inbox Payload) :=
  if b.cursor < I.nextRemove then none
  else
    match dropBelow b.cursor I.added with
    | none => none
    | some [] =>
      some { I with added := [], removed := I.removed ++ [b], nextRemove := b.cursor.succ }
    | some (a :: rest) =>
      if a = b then some { I with added := rest, nextRemove := b.cursor.succ } else none

/-- Deliver a bundle (`add_bundle`). -/
def add (b : Bundle Payload) (I : Inbox Payload) : Option (Inbox Payload) :=
  if b.cursor < I.nextAdd then none
  else
    match I.removed with
    | r :: rest =>
      if r.cursor = b.cursor then
        if b = r then some { I with removed := rest, nextAdd := b.cursor.succ } else none
      else if b.cursor < r.cursor ∧ b.skippable then some { I with nextAdd := b.cursor.succ }
      else none
    | [] => some { I with added := I.added ++ [b], nextAdd := b.cursor.succ }

/-- Apply one operation. -/
def step (I : Inbox Payload) : Op Payload → Option (Inbox Payload)
  | .add b => I.add b
  | .remove b => I.remove b

/-- Apply a sequence of operations, failing if any fails. -/
def run (I : Inbox Payload) : List (Op Payload) → Option (Inbox Payload)
  | [] => some I
  | op :: rest => (I.step op).bind (run · rest)

/-! ### The step lemmas -/

/-- Delivering `b` to the canonical inbox of `(A, R)` yields the canonical
inbox of `(A ++ [b], R)`. -/
theorem add_canonical {A R : List (Bundle Payload)} (hR : Sorted R)
    {b : Bundle Payload} {I : Inbox Payload} (h : (canonical A R).add b = some I) :
    after A ≤ b.cursor ∧ I = canonical (A ++ [b]) R := by
  unfold add at h
  by_cases hb : b.cursor < (canonical A R).nextAdd
  · simp only [hb, ↓reduceIte] at h; exact absurd h (by simp)
  simp only [hb, ↓reduceIte] at h
  have hb : after A ≤ b.cursor := not_lt.1 hb
  refine ⟨hb, ?_⟩
  have hRf := hR.filter (fun r => decide (after A ≤ r.cursor))
  rcases hfilter : R.filter (fun r => decide (after A ≤ r.cursor)) with _ | ⟨r, rest⟩
  · have hrem : (canonical A R).removed = [] := hfilter
    simp only [hrem, Option.some.injEq] at h
    subst h
    have hall : ∀ y ∈ R, y.cursor < after A := by
      intro y hy
      by_contra hc
      have : y ∈ R.filter (fun r => decide (after A ≤ r.cursor)) :=
        List.mem_filter.2 ⟨hy, by simpa using not_lt.1 hc⟩
      rw [hfilter] at this; simp at this
    simp only [canonical, after_append, Inbox.mk.injEq, true_and]
    constructor
    · rw [List.filter_append, List.filter_singleton]
      have : after R ≤ b.cursor := (after_le_of_forall_lt hall).trans hb
      simp [this]
    · symm
      rw [List.filter_eq_nil_iff]
      intro y hy
      have := (hall y hy).trans_le (hb.trans (Cursor.lt_succ_self _).le)
      simpa using not_le.2 this
  · have hrem : (canonical A R).removed = r :: rest := hfilter
    simp only [hrem] at h
    have hr : ∀ y ∈ R, after A ≤ y.cursor → r.cursor ≤ y.cursor := by
      intro y hy hAy
      have hmem : y ∈ r :: rest := by
        rw [← hfilter]; exact List.mem_filter.2 ⟨hy, by simpa using hAy⟩
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact le_rfl
      · rw [hfilter] at hRf
        exact (List.rel_of_pairwise_cons hRf hmem).le
    have hrR : r ∈ R := List.mem_of_mem_filter (hfilter ▸ List.mem_cons_self)
    split at h
    · rename_i hcur
      split at h
      · rename_i hbr
        subst hbr
        simp only [Option.some.injEq] at h
        subst h
        simp only [canonical, after_append, Inbox.mk.injEq, true_and]
        constructor
        · rw [List.filter_append, List.filter_singleton]
          have : ¬ after R ≤ b.cursor := not_le.2 (lt_after_of_mem hR hrR)
          simp [this]
        · exact filter_tail hR hfilter
      · exact absurd h (by simp)
    · rename_i hcur
      split at h
      · rename_i hlt
        simp only [Option.some.injEq] at h
        subst h
        simp only [canonical, after_append, Inbox.mk.injEq, true_and]
        constructor
        · rw [List.filter_append, List.filter_singleton]
          have : ¬ after R ≤ b.cursor :=
            not_le.2 (hlt.1.trans (lt_after_of_mem hR hrR))
          simp [this]
        · rw [← hfilter]
          apply List.filter_congr
          intro y hy
          simp only [decide_eq_decide]
          constructor
          · intro hAy
            exact Cursor.lt_iff_succ_le.1 (hlt.1.trans_le (hr y hy hAy))
          · intro hby
            by_contra hAy
            have := (not_le.1 hAy).trans_le hb
            exact absurd (Cursor.lt_iff_succ_le.2 hby) (not_lt.2 this.le)
      · exact absurd h (by simp)

/-- Consuming `b` from the canonical inbox of `(A, R)` yields the canonical
inbox of `(A, R ++ [b])`. -/
theorem remove_canonical {A R : List (Bundle Payload)} (hA : Sorted A)
    {b : Bundle Payload} {I : Inbox Payload} (h : (canonical A R).remove b = some I) :
    after R ≤ b.cursor ∧ I = canonical A (R ++ [b]) := by
  unfold remove at h
  by_cases hb : b.cursor < (canonical A R).nextRemove
  · simp only [hb, ↓reduceIte] at h; exact absurd h (by simp)
  simp only [hb, ↓reduceIte] at h
  have hb : after R ≤ b.cursor := not_lt.1 hb
  refine ⟨hb, ?_⟩
  have hAf := hA.filter (fun a => decide (after R ≤ a.cursor))
  have hcongr : (A.filter (fun a => decide (after R ≤ a.cursor))).filter
      (fun a => decide (b.cursor ≤ a.cursor)) =
      A.filter (fun a => decide (b.cursor ≤ a.cursor)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro y _
    by_cases hy : b.cursor ≤ y.cursor
    · simp [hy, hb.trans hy]
    · simp [hy]
  rcases hdrop : dropBelow b.cursor (canonical A R).added with _ | (_ | ⟨a, rest⟩)
  · simp only [hdrop] at h; exact absurd h (by simp)
  · simp only [hdrop, Option.some.injEq] at h
    have hdrop' : dropBelow b.cursor (A.filter (fun a => decide (after R ≤ a.cursor))) =
      some [] := hdrop
    have hL' : [] = A.filter (fun a => decide (b.cursor ≤ a.cursor)) := by
      rw [← hcongr]; exact dropBelow_eq hAf hdrop'
    have hall : ∀ y ∈ A, y.cursor < b.cursor := by
      intro y hy
      by_contra hc
      have : y ∈ A.filter (fun a => decide (b.cursor ≤ a.cursor)) :=
        List.mem_filter.2 ⟨hy, by simpa using not_lt.1 hc⟩
      rw [← hL'] at this; simp at this
    subst h
    simp only [canonical, after_append, Inbox.mk.injEq, true_and]
    constructor
    · symm
      rw [List.filter_eq_nil_iff]
      intro y hy
      have := (hall y hy).trans (Cursor.lt_succ_self _)
      simpa using not_le.2 this
    · rw [List.filter_append, List.filter_singleton]
      have : after A ≤ b.cursor := after_le_of_forall_lt hall
      simp [this]
  · simp only [hdrop] at h
    have hdrop' : dropBelow b.cursor (A.filter (fun a => decide (after R ≤ a.cursor))) =
      some (a :: rest) := hdrop
    have hL' : a :: rest = A.filter (fun a => decide (b.cursor ≤ a.cursor)) := by
      rw [← hcongr]; exact dropBelow_eq hAf hdrop'
    split at h
    · rename_i hab
      subst hab
      simp only [Option.some.injEq] at h
      subst h
      have haA : a ∈ A := List.mem_of_mem_filter (hL' ▸ List.mem_cons_self)
      simp only [canonical, after_append, Inbox.mk.injEq, true_and]
      constructor
      · exact filter_tail hA hL'.symm
      · rw [List.filter_append, List.filter_singleton]
        have : ¬ after A ≤ a.cursor := not_le.2 (lt_after_of_mem hA haA)
        simp [this]
    · exact absurd h (by simp)

/-! ### Order-independence -/

/-- A succeeding run from the canonical inbox of `(A, R)` ends in the
canonical inbox of the extended histories. -/
theorem run_canonical (ops : List (Op Payload)) : ∀ {A R : List (Bundle Payload)},
    Sorted A → Sorted R → ∀ {I : Inbox Payload}, (canonical A R).run ops = some I →
    I = canonical (A ++ adds ops) (R ++ removes ops) := by
  induction ops with
  | nil => intro A R _ _ I h; simp [run] at h; simp [adds, removes, h]
  | cons op rest ih =>
    intro A R hA hR I h
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨I₁, h₁, h₂⟩ := h
    cases op with
    | add b =>
      obtain ⟨hb, rfl⟩ := add_canonical hR h₁
      have := ih (hA.append_singleton hb) hR h₂
      simpa [adds, removes, List.append_assoc] using this
    | remove b =>
      obtain ⟨hb, rfl⟩ := remove_canonical hA h₁
      have := ih hA (hR.append_singleton hb) h₂
      simpa [adds, removes, List.append_assoc] using this

/-- **Inbox order-independence**: a succeeding sequence of deliveries and
consumptions from the empty inbox yields the inbox determined by the
delivered bundles and the consumed bundles alone, whatever their
interleaving. -/
theorem run_eq_canonical {ops : List (Op Payload)} {I : Inbox Payload}
    (h : init.run ops = some I) : I = canonical (adds ops) (removes ops) := by
  have := run_canonical ops (A := []) (R := []) List.Pairwise.nil List.Pairwise.nil
    (by rw [canonical_nil_nil]; exact h)
  simpa using this

/-- Two succeeding interleavings of the same deliveries and the same
consumptions end in the same inbox. -/
theorem run_eq_of_same_history {ops₁ ops₂ : List (Op Payload)} {I₁ I₂ : Inbox Payload}
    (h₁ : init.run ops₁ = some I₁) (h₂ : init.run ops₂ = some I₂)
    (ha : adds ops₁ = adds ops₂) (hr : removes ops₁ = removes ops₂) : I₁ = I₂ := by
  rw [run_eq_canonical h₁, run_eq_canonical h₂, ha, hr]

/-- The delivered bundles of a succeeding run have strictly increasing cursors. -/
theorem sorted_adds {ops : List (Op Payload)} {I : Inbox Payload}
    (h : init.run ops = some I) : Sorted (adds ops) := by
  suffices ∀ {A R : List (Bundle Payload)}, Sorted A → Sorted R → ∀ {I : Inbox Payload},
      (canonical A R).run ops = some I → Sorted (A ++ adds ops) by
    simpa using this (A := []) (R := []) List.Pairwise.nil List.Pairwise.nil
      (by rw [canonical_nil_nil]; exact h)
  clear h I
  induction ops with
  | nil => intro A R hA _ I _; simpa [adds] using hA
  | cons op rest ih =>
    intro A R hA hR I h
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨I₁, h₁, h₂⟩ := h
    cases op with
    | add b =>
      obtain ⟨hb, rfl⟩ := add_canonical hR h₁
      simpa [adds, List.append_assoc] using ih (hA.append_singleton hb) hR h₂
    | remove b =>
      obtain ⟨hb, rfl⟩ := remove_canonical hA h₁
      simpa [adds] using ih hA (hR.append_singleton hb) h₂

end Ops

end Inbox

end Linera
