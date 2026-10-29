# Machine-checked safety and liveness of the Linera per-height consensus

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether this report is faithful to what is proved, has only
> human-plus-LLM review behind it. Read critically.

This report states what `linera-lean` proves about the per-height
consensus protocol of the Linera paper (section Consensus and Appendix
A), as amended on 2026-10-29 to follow the reference implementation
(`linera-protocol`, crates `linera-chain` and `linera-core`). Every
displayed Lean statement is copied verbatim from the sources;
`scripts/statements.py check` verifies this. Every theorem depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`
(`scripts/Axioms.lean`). The mapping from the paper's lemmas to Lean
names, the design, the findings and the comparison with the
implementation are in `design.md`; this report presents the results.

## 1. The model

### 1.1 Validators and quorums

The protocol is stated over an abstract quorum system: a set of honest
validators and a `Quorum` predicate such that any superset of a quorum is
a quorum, the honest validators form a quorum, and two quorums share an
honest validator. This is the whole of what the proofs use.

```lean
class QuorumSystem (V : Type*) [Fintype V] [DecidableEq V]
```

The paper's stake-weighted committee (total power `n`, Byzantine power at
most `f`, `3f < n`, quorum any power at least `n − f`) is an instance,
`Weighted.toQuorumSystem`. Its intersection lemma is the one the safety
proof needs:

```lean
theorem exists_honest_mem_inter {A B : Finset V} (hA : W.Quorum A) (hB : W.Quorum B) :
    ∃ v ∈ A ∩ B, v ∈ W.honest
```

The paper's Lemma honest-mass is also proved, but is not what the safety
argument rests on (design.md, F1):

```lean
theorem honest_wt_of_quorum {S : Finset V} (hS : W.Quorum S) :
    W.n - 2 * W.f ≤ W.wt (S ∩ W.honest)
```

### 1.2 Rounds, proposals, validators

Rounds are natural numbers. A configuration fixes whether round `0` is a
fast round (a super owner exists), the number `k` of multi-leader rounds
that follow, the leader of each single-leader round, and block validity.
A proposal carries a round, a block, a justification (`none`, a
validation certificate, or the super owner's fast-round signature) and
its owner.

A validator's per-height state holds its current round, its latest
validation vote, its lock (its latest confirmation vote), its locking
block (the highest validation certificate it has seen, or the fast-round
proposal it confirmed), its latest timeout vote and timeout certificate,
and the finalized block. The handlers are transcribed from the paper's
Algorithms on_proposal, on_certificate, on_confirmation_certificate,
on_timeout and on_timeout_certificate (`Validator.lean`).

### 1.3 The transition system

The global state is every validator's local state and the log of honest
signatures. A Byzantine validator's signature on any message is available
at any time; an honest one exists only if a handler produced it. A
certificate is a quorum of available signatures, so certificates are
never data: a handler that receives one is a step whose precondition is
that it exists. The step function dispatches one input at one honest
validator:

```lean
def step (cfg : Config Owner Block) (s : State V Owner Block) (v : V) :
    Input Owner Block → Option (State V Owner Block)
```

A proposal that passes every check but validity or the lock rule still
advances the validator's round (Algorithm on_proposal, line 12), as in
the implementation. The untimed model lets a timeout vote be signed for
the current round at any moment, so it includes every behaviour of the
timed protocol, and the safety theorems carry over to it.

Each honest signature carries two ghost fields, the signer's lock and
the proposal answered, which the proofs read and no handler does:

```lean
theorem step_erase (cfg : Config Owner Block) {s s' : State V Owner Block} (h : s.erase = s'.erase)
    (v : V) (i : Input Owner Block) :
    (step cfg s v i).map State.erase = (step cfg s' v i).map State.erase
```

### 1.4 Witnesses

Every definition is exercised on a four-validator model (equal power,
`f = 1`, one Byzantine validator) by `decide` before anything is proved
from it (`LineraTest/`): a two-phase round that finalizes; a fast
round that finalizes with confirmation votes only; a clashed multi-leader
round skipped by a proposal for the next round with no timeout; a lock
refusing a conflicting proposal while still advancing the round, and the
same block accepted once re-proposed with its certificate; a
single-leader round ended only by a timeout certificate.

## 2. Safety

All safety results hold on every reachable state of the untimed model,
with no timing assumption, whatever the Byzantine validators and owners
do, and with the fast round enabled or not.

**Unique validation per round** (paper, Lemma unique-valcert), and none in
the fast round:

```lean
theorem valCert_unique {B₁ B₂ : Block} {r : Round} (h₁ : s.ValCert B₁ r) (h₂ : s.ValCert B₂ r) :
    B₁ = B₂
```

```lean
theorem not_valCert_fast {B : Block} {r : Round} (hf : cfg.IsFast r) : ¬ s.ValCert B r
```

**Lock safety at validation** (paper, Lemma lock-validate): an honest
validation vote for `B'` cast while locked on a different `B` carried a
certificate for `B'` from a round strictly between the lock and the vote:

```lean
theorem lock_validate {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B' : Block} {r : Round} (hm : e.msg = .val B' r) {B : Block} {rl : Round}
    (hlk : e.lockAt = some (B, rl)) (hne : B ≠ B') :
    ∃ ρ, e.just = .cert B' ρ ∧ rl < ρ ∧ ρ < r ∧ s.ValCert B' ρ
```

**The locked block is protected**, the paper's minimal-round argument:

```lean
theorem Inv.valCert_eq_of_confCert {B : Block} {r : Round} (hc : s.ConfCert B r) :
    ∀ r' B', r < r' → s.ValCert B' r' → B' = B
```

**Safety** (paper, Theorem safety):

```lean
theorem safety {B₁ B₂ : Block} {r₁ r₂ : Round} (h₁ : s.ConfCert B₁ r₁)
    (h₂ : s.ConfCert B₂ r₂) : B₁ = B₂
```

**The Safety requirement** of the paper's system model:

```lean
theorem finalized_agree {v w : V} (hv : v ∈ Q.honest) (hw : w ∈ Q.honest) {B₁ B₂ : Block}
    (h₁ : (s.locals v).finalized = some B₁) (h₂ : (s.locals w).finalized = some B₂) :
    B₁ = B₂
```

**Authenticity**: an honest validation vote answers an eligible owner's
proposal, and an honest fast-round confirmation answers the super
owner's:

```lean
theorem vote_of_eligible {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B : Block} {r : Round} (hm : e.msg = .val B r) :
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.Eligible r P.owner
```

```lean
theorem fast_vote_of_super {e : Sig V Owner Block} (he : e ∈ s.log) (hv : e.signer ∈ Q.honest)
    {B : Block} {r : Round} (hm : e.msg = .conf B r) (hf : cfg.IsFast r) :
    ∃ P, e.prop = some P ∧ P.block = B ∧ P.round = r ∧ cfg.FastEligible r P.owner
```

**Monotonicity and finality** (paper, Lemmas vote-monotone and
no-further-votes):

```lean
theorem step_cur_le {cfg : Config Owner Block} {s s' : State V Owner Block} {v : V}
    {i : Input Owner Block} (h : step cfg s v i = some s') (w : V) :
    (s.locals w).cur ≤ (s'.locals w).cur
```

```lean
theorem step_lock_le {cfg : Config Owner Block} {s s' : State V Owner Block} (hs : Inv cfg s)
    {v : V} {i : Input Owner Block} (h : step cfg s v i = some s') {w : V} (hw : w ∈ Q.honest) :
    ∀ lk ∈ (s.locals w).lock, ∃ lk' ∈ (s'.locals w).lock, lk.2 ≤ lk'.2
```

```lean
theorem step_none_of_finalized {cfg : Config Owner Block} {s : State V Owner Block} {v : V}
    {B : Block} (hfin : (s.locals v).finalized = some B) (i : Input Owner Block) :
    step cfg s v i = none
```

The proofs go through an inductive invariant `Inv` on honest validators
(`Safety/Invariants.lean`): every validation vote is at or below the
latest validation vote or the locking block, every confirmation at or
below the locking block (so votes are cast in increasing rounds and at
most once per round); votes are at or below the current round; a
confirmation outside the fast round is backed by a validation
certificate; no validation vote is cast in the fast round; the lock is
the latest confirmation; the locking block, when a certificate, exists;
and every validation vote carries a ghost justification recording the
lock at signing and the certificate carried, which is Lemma
lock-validate stated at the moment of signing.

```lean
def Inv (cfg : Config Owner Block) (s : State V Owner Block) : Prop
```

## 3. Liveness: the untimed core

**Fast-round finalization.** With a super owner, its valid proposal,
delivered to every honest validator before any of them votes, finalizes
in one round trip, and the resulting state is reachable:

```lean
theorem fast_round_finalizes {cfg : Config Owner Block} {P : Proposal Owner Block}
    (hf : cfg.IsFast P.round) (ho : P.owner = cfg.super) (hvalid : cfg.Valid P.block)
    (hj : P.just = .none) (L : List V) (hnd : L.Nodup) (hall : ∀ v ∈ Q.honest, v ∈ L)
    (hL : ∀ v ∈ L, v ∈ Q.honest) :
    ∃ s', run cfg (L.map fun v => (v, .proposal P)) State.init = some s' ∧
      s'.ConfCert P.block P.round ∧ Reachable cfg s'
```

**A good round finalizes** (the untimed content of the paper's Lemma
progress): in a two-phase round `r` where every honest validator is
fresh (at `r`, with every vote, lock and locking block below `r`) and
the proposal is well formed and passes every honest lock, delivering it
to all yields a validation certificate, and delivering that to all yields
a confirmation certificate:

```lean
theorem good_round_confirms {cfg : Config Owner Block} {s : State V Owner Block} {r : Round}
    {P : Proposal Owner Block} (hP : P.WellFormed cfg s r) (L : List V) (hnd : L.Nodup)
    (hall : ∀ v ∈ Q.honest, v ∈ L) (hL : ∀ v ∈ L, v ∈ Q.honest)
    (hfresh : ∀ v ∈ L, (s.locals v).Fresh r) (hacc : ∀ v ∈ L, (s.locals v).lockOk cfg P) :
    ∃ s', run cfg (L.map (fun v => (v, .proposal P)) ++ L.map (fun v => (v, .valCert P.block r)))
      s = some s' ∧ s'.ConfCert P.block r
```

**The re-proposal rule passes every lock** (Algorithm client_propose):
re-proposing the newest locking block reported by any honest validator,
with it as justification, is accepted by every honest lock:

```lean
theorem acceptable_of_highest_lb {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Inv cfg s) {B : Block} {ρ : Round} {w : V} (hw : w ∈ Q.honest)
    (hlbw : (s.locals w).lb = some (.cert B ρ))
    (hmax : ∀ v ∈ Q.honest, ∀ lb ∈ (s.locals v).lb, lb.round ≤ ρ)
    (P : Proposal Owner Block) (hj : P.just = .cert B ρ) (hB : P.block = B) :
    ∀ v ∈ Q.honest, (s.locals v).lockOk cfg P
```

**Eventual consistency** (the system model's requirement): once a
confirmation certificate exists in a reachable state, delivering it to
every honest validator that has not yet finalized leaves every honest
validator finalized on its block, the others having finalized the same
block by safety:

```lean
theorem eventual_consistency {cfg : Config Owner Block} {s : State V Owner Block}
    (hs : Reachable cfg s) {B : Block} {r : Round} (hcert : s.ConfCert B r) (L : List V)
    (hnd : L.Nodup) (hL : ∀ v ∈ L, v ∈ Q.honest)
    (hall : ∀ v ∈ Q.honest, (s.locals v).finalized = none → v ∈ L)
    (hfresh : ∀ v ∈ L, (s.locals v).finalized = none) :
    ∃ s', run cfg (L.map fun v => (v, .confCert B r)) s = some s' ∧ Reachable cfg s' ∧
      ∀ v ∈ Q.honest, (s'.locals v).finalized = some B
```

**The schedule** (paper, Lemma honest-single-leader), for a round-robin
leader and no super owner (a super owner may propose in single-leader
rounds in the implementation, so the sole-leader property needs it to
abstain):

```lean
theorem Config.exists_sole_eligible (cfg : Config (Fin m) Block) [NeZero m]
    (hl : cfg.leader = roundRobin m) (hnf : cfg.fast = false) (o : Fin m) (N : ℕ) :
    ∃ r, N ≤ r ∧ cfg.IsSingle r ∧ ∀ o', cfg.Eligible r o' ↔ o' = o
```

## 4. Liveness under partial synchrony

### 4.1 Timed executions

Time is a tick counter. A timed execution is a state sequence with at
most one honest step per tick. A validator's entry into its current
round is the first tick at which it held it; a timeout vote may be
attempted only once entry plus the round's duration has passed. Durations
follow the paper's Timeouts paragraph: the fast round optionally, the last
multi-leader round `base`, the `j`-th single-leader round `base + j·inc`,
other multi-leader rounds never.

```lean
def Timeouts.dur (tm : Timeouts) (cfg : Config Owner Block) (r : Round) : Option ℕ
```

The lemma the view-change argument rests on: a validator past a
single-leader round got there through a timeout certificate for it that
existed strictly earlier. Proposals cannot carry a validator past such a
round; certificates come from signers who were already there; and a
timeout certificate for a higher round would need signers already past
it.

```lean
theorem exists_tc_of_gt (hr : cfg.IsSingle r) {w : V} (hw : w ∈ Q.honest) {t : ℕ}
    (h : r < ex.cur w t) : ∃ t' < t, (ex.st t').TimeoutCert r
```

### 4.2 The environment

The paper's assumptions are obligations on the execution after a global
stabilisation time `GST`, with delay bound `Δ` and an owner-side latency
bound `L`; each allows the escape "a block has been confirmed".

```lean
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
```

`JustRule` is the paper's re-proposal rule: re-propose the newest
locking block with itself as justification (a validation certificate, or
the fast-round proposal with the super owner's signature), or a fresh
block if no honest validator holds one.

```lean
def JustRule (cfg : Config Owner Block) (s : State V Owner Block) (P : Proposal Owner Block) :
    Prop
```

The obligations `timeout`, `tc_known`, `tc_honest`, `propose` and `cert`
abstract the owner's loop into the constants `Δ` and `L`; section 4.4
discharges them from the loop itself. The fast round is covered under
`fast_honest` and `fast_quiet`: the super owner proposes a single fast
block, and no fast-round proposal is still in flight after `GST`; the
first is the paper's hypothesis that no super owner equivocates.

### 4.3 Round growth and liveness

**Eventual round growth** (paper, Lemma round-growth): every round is
eventually reached by every honest validator, or a block is confirmed.
For a single-leader round the argument is the paper's: its deadline
passes at every honest validator, each signs a timeout vote, the
certificate forms and reaches everyone.

```lean
theorem Env.advance_single {r t : ℕ} (hr : cfg.IsSingle r) (hg : env.GST ≤ t)
    (hall : ∀ v ∈ Q.honest, r ≤ ex.cur v t) :
    ∃ t', t ≤ t' ∧ (ex.Done t' ∨ ∀ v ∈ Q.honest, r < ex.cur v t')
```

```lean
theorem Env.reach_round (r : ℕ) :
    ∃ t, env.GST ≤ t ∧ (ex.Done t ∨ ∀ v ∈ Q.honest, r ≤ ex.cur v t)
```

**The window invariant** of the good round: relative to the state in
which the owner read the locking blocks, every honest validator keeps
the lock and latest validation vote it had, or has validated the owner's
block, or has confirmed it. It is kept by every step while every honest
validator is at or below the round and every validation vote in the
round is for the owner's block:

```lean
theorem winAt_step {s₀ s s' : State V Owner Block} {P : Proposal Owner Block} {r : Round}
    (hr : cfg.firstSL < r) (hnf : ¬ cfg.IsFast r) (hs : Inv cfg s) {v : V} (hv : v ∈ Q.honest)
    (hcur : (s.locals v).cur = r) (hle : ∀ w ∈ Q.honest, (s.locals w).cur ≤ r)
    {w : V} {i : Input Owner Block} (hst : step cfg s w i = some s')
    (hq : ∀ P', i = .proposal P' → ¬ cfg.IsFast P'.round)
    (hvalP : ∀ u ∈ Q.honest, ∀ B, s'.HSig u (.val B r) → B = P.block)
    (hwin : WinAt s₀ s P r v) : WinAt s₀ s' P r v
```

**Liveness** (paper, Theorem liveness), with the fast round allowed and
the hypothesis that the super owner does not equivocate:

```lean
theorem Env.liveness : ∃ t, ex.Done t
```

The good round is a single-leader round led solely by the owner, beyond
every round held at `GST`, with duration at least `Δ + 2L + 2` (Lemma
long-rounds, by linear growth). The first timeout certificate for the
previous round then appears after `GST`; every honest validator enters
the round within `Δ`; none can leave it before the duration, since a
timeout vote needs the deadline and a validator past the round would
need a timeout certificate for it; the proposal, built from the locking
blocks read at `t_q`, passes every lock, because locks are frozen in the
window except by confirming the owner's own block; every honest
validator validates or confirms it, the validation certificate exists,
reaches everyone, and every honest validator confirms.

### 4.4 The owner's loop and the network

`Owner.lean` states the owner as a strategy and the network as a delivery
bound, and derives the environment of 4.2. The owner's view at tick `t`
is the state at `t − Δ`. From its view it wants a bounded set of messages
delivered (Algorithm client_propose): a timeout vote from every validator
whose deadline has passed; the newest timeout certificate it can hold, to
everyone; once every honest validator is in a single-leader round it is
eligible in, its proposal for that round, built by the re-proposal rule
from the first view in which everyone was in the round; and a validation
certificate it can hold for that round.

```lean
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
```

A wanted message is attempted within `Δ` unless stale (a timeout request
for a round the validator has left), and the owner's proposals are the
only proposals signed by it:

```lean
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
```

The re-proposal rule always yields a proposal (`exists_ruleProposal`),
and the owner's proposal for a round is the one built from the first view
in which every honest validator was in it. The derived environment has
`Δ` and `L` both equal to `2Δ + 1`:

```lean
noncomputable def OwnerEnv.toEnv (oe : OwnerEnv ex) : ex.Env
```

```lean
theorem OwnerEnv.liveness (oe : OwnerEnv ex) : ∃ t, ex.Done t := oe.toEnv.liveness
```

What remains assumed about the owner is that it polls continuously (its
view is at most `Δ` old), that it reads every honest validator's locking
block before proposing (design.md, F7; the obligation `deliver` on the
proposal built from such a view), and that it leaves multi-leader rounds
(`leave_multi`).

## 5. What is not covered

The validator fallback rounds and
the pseudo-random leader schedule of the implementation (the schedule is
an abstract parameter with a fairness obligation); open multi-leader
rounds; the unlocking-round attestation; the owner's behaviour in
multi-leader rounds (the obligation `leave_multi`); and an explicit
message layer below the delivery bound `deliver`.
