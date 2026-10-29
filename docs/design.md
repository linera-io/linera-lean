# lean-linera — plan and design

A Lean 4 + Mathlib formalization of the per-height consensus protocol of the
Linera paper (`linera-paper`, §Consensus and Appendix A), in the conventions
of `lean-dag`: kernel-checked statements, standard axioms only, concrete
witnesses before theorems, and a report whose displayed statements are copied
from source.

This document is the plan. It records what will be proved, how the protocol
is modelled, how the proofs are organised, and the places where the paper's
informal arguments are expected to need tightening. Nothing here is proved
yet.

## 1. Target: what the paper claims

The formal content of the paper is Appendix A, resting on the five validator
handlers of §Consensus. The theorems and lemmas, with the Lean name planned
for each:

| Paper | Statement | Lean | Status |
|:---|:---|:---|:---|
| Lem. honest-mass | a certificate carries ≥ `n−2f` honest weight | `Weighted.honest_wt_of_quorum` | done |
| (implicit) quorum intersection | two quorums share an honest validator | `Weighted.exists_honest_mem_inter`, `QuorumSystem.exists_honest_mem_inter` | done |
| Lem. no-further-votes | a finalized validator refuses every input | `step_none_of_finalized` | done |
| Lem. vote-monotone | `r_cur` and the lock round never decrease; votes in increasing rounds | `step_cur_le`, `step_lock_le`, `VInv.val_bound`, `VInv.conf_bound` | done |
| Lem. unique-valcert | at most one block has a `ValCert` per round; none in the fast round | `valCert_unique`, `not_valCert_fast` | done |
| Lem. conf-needs-val | a `ConfCert` outside the fast round rests on a `ValCert` | `Inv.valCert_of_confCert` | done |
| Lem. lock-validate | a Val vote against the lock carries `ValCert(B′,ρ)`, `r_ℓ < ρ < r` | `lock_validate` | done |
| Thm. safety | no two conflicting `ConfCert`s at a height | `safety` | done |
| §Model Safety | no two honest validators finalize different blocks | `finalized_agree` | done |
| §Model Authenticity | an honest Val vote answers an eligible owner's proposal | `vote_of_eligible`, `fast_vote_of_super` | done |
| App. fast-round | safety is preserved when round 0 skips validation | `safety` (the fast round is in the model) | done |
| App. fast-round | an honest super owner finalizes in round 0 in one round trip | `fast_round_finalizes` | done |
| Lem. honest-single-leader | every owner is the sole eligible proposer in a single-leader round after any round (round-robin, no super owner) | `Config.exists_sole_eligible` | done |
| Lem. progress (core) | in a good round the proposal is validated, then confirmed | `good_round_confirms` | done |
| Alg. client_propose rule | the newest locking block re-proposed passes every lock | `acceptable_of_highest_lb`, `acceptable_of_fast_lb`, `acceptable_of_no_lock`, `wellFormed_of_highest_lb` | done |
| Lem. round-growth | every round is eventually reached by every honest validator, or a block is confirmed | `TExec.Env.reach_round` (`advance_single`, `advance_multi_list`) | done |
| Lem. long-rounds | a single-leader round beyond `firstSL + Δ + 2L + 2` lasts long enough (linear durations) | inside `TExec.Env.liveness` (`hdbig`) | done |
| Thm. liveness | an honest active owner + partial synchrony ⇒ a block is confirmed (no fast round) | `TExec.Env.liveness` | done |

Out of scope: cross-chain messaging, execution semantics (`Exec`), ownership
changes between heights (the instance is single-shot, so the owner set is a
parameter), certificate upload and repair (App. B.1), and the Eventual
Consistency requirement, which is a statement about relaying rather than
about the protocol.

## 2. Decisions (confirmed 2026-10-29)

1. **Plain Lean 4 + Mathlib, no Veil.** Veil (checked out at `~/git/veil`)
   would automate inductive-invariant checking by SMT, but its trust base
   includes the solver, it has no liveness story, and it pins its own
   toolchain. The safety invariants below are small enough to prove by hand,
   and the liveness part needs Mathlib-style reasoning about time and
   schedules. Veil remains usable as a scratch tool for *finding* an
   inductive strengthening quickly; nothing in the project would depend on it.
2. **Abstract quorum system, weighted instance.** The proofs use only
   quorum intersection, so the protocol is stated over a class
   `QuorumSystem V` (a `Quorum` predicate on `Finset V`, an `honest`
   predicate, monotonicity, and "two quorums share an honest validator").
   The paper's stake-weighted committee (total power `n`, Byzantine power
   `≤ f`, `3f < n`, quorum `≥ n − f`) is an instance, with counting as the
   special case `weight = 1`; witnesses run by `decide` on the instance.
3. **Safety untimed; liveness in layers by what each needs.** Safety is
   stated over an untimed transition system in which timeouts may be signed
   at any moment, which over-approximates the real protocol and so yields a
   stronger safety theorem. Liveness of a *fast round* (round 0 with a super
   owner) needs only an honest round leader and no timing. Liveness of the
   *slow rounds* (multi-leader, then single-leader) needs the protocol-core
   lemma (untimed: in a good round the honest proposal goes through) plus
   the view changes, which need partial synchrony: an unknown `Δ` after an
   unknown GST, and round timeouts that grow.
4. **Sibling repository `~/git/lean-linera`** (local commits; remote to be
   set up by the user), mirroring `lean-dag`
   (`lakefile.toml`, Mathlib pinned to a release tag, test library of
   concrete witnesses built by default, Makefile, CI). The LaTeX repository
   stays LaTeX. The paper is anonymised (`\sysname` = XYZ); keep the Lean
   repository private until the paper is public.
5. **Toolchain** `leanprover/lean4:v4.35.0` with Mathlib tag `v4.35.0`
   (both exist; the toolchain is already installed in elan). `lake exe cache
   get` fetches Mathlib oleans.

## 3. The model

### 3.1 Committee (`LeanLinera/Committee.lean`)

```lean
class Committee (V : Type*) [Fintype V] [DecidableEq V] where
  weight    : V → ℕ
  f         : ℕ
  byzantine : Finset V
  byz_le    : ∑ v ∈ byzantine, weight v ≤ f
  three_f_lt : 3 * f < ∑ v, weight v
```

`n := ∑ v, weight v`, `Honest := byzantineᶜ`, `Quorum S := n − f ≤ wt S`.
Two lemmas carry every counting argument of the paper:

- `honest_weight_of_quorum : Quorum S → n − 2f ≤ wt (S ∩ Honest)`
  (Lem. honest-mass);
- `exists_honest_mem_inter : Quorum A → Quorum B → ∃ v ∈ A ∩ B, v ∈ Honest`
  (`wt (A ∩ B) ≥ n − 2f > f ≥ wt byzantine`).

Note (finding F1, §7): the second lemma intersects the *quorums* and then
removes the Byzantine weight. Intersecting the honest parts first, as the
paper's safety proof does, is not valid: two honest sets of weight `n−2f`
can be disjoint when `byzantine = ∅` and `n ≤ 4f`.

### 3.2 Messages and certificates (`Messages.lean`)

```lean
inductive Msg (Block : Type)
  | val  (B : Block) (r : ℕ)
  | conf (B : Block) (r : ℕ)
  | time (r : ℕ)
```

Signatures are unforgeable, so a Byzantine validator's signature on any
message may appear at any time, while an honest validator's signature exists
only if its handler produced it. The global state therefore carries only the
honest signature log, and

```lean
def Signed (s : State) (v : V) (m : Msg) : Prop := v ∈ byzantine ∨ (v, m) ∈ s.log
def HasCert (s : State) (m : Msg) : Prop := Quorum (univ.filter (Signed s · m))
```

`ValCert s B r := HasCert s (.val B r)`, likewise `ConfCert`, `TimeoutCert`.
A certificate is never a datum: a handler that "receives `ValCert(B,r)`" is
a step whose precondition is `ValCert s B r`. Since the log is append-only,
`HasCert` is monotone along steps, which is the property every invariant
about certificates rests on.

The paper's "finalized" is `ConfCert`, exactly as Thm. safety states it
("both obtain confirmation certificates"), and independent of any validator
having seen the certificate.

### 3.3 Validator local state and handlers (`Validator.lean`)

*(Amended 2026-10-29 to follow the implementation; the paper's algorithms
were amended in the same way. The text below describes the amended
model.)* The local state is `cur`, `valVote` (latest validation vote),
`lock` (latest confirmation), `lb` (the locking block: the highest
validation certificate seen or the fast-round proposal), `timeoutVote`,
`tc` and `finalized`. A proposal carries a justification `Just`: none, a
certificate, or the fast-round signature. Handlers: `preOk` (eligibility,
well-formed justification, the round rule — rounds up to `r_SL` may be
skipped, later ones must be current — and newer than `valVote` and `lb`),
`lockOk` (the strict lock rule), `afterVal`/`afterBump` (a proposal that
passes `preOk` but fails validity or the lock rule still advances the
round), `fastOk`/`afterFast`, `valCertOk`/`afterValCert` (record the
locking block, advance, confirm only if the round is current),
`timeoutOk` (current round only), `tcOk`/`afterTimeoutCert`. The original
description follows.


Transcribed from the five algorithms, as pure functions
`Local → Input → Option (Local × List Msg)` so that each guard is a line of
the paper:

```lean
structure Local (Block : Type) where
  cur       : ℕ                       -- r_cur
  lock      : Option (Block × ℕ)
  votedVal  : ℕ → Bool
  votedConf : ℕ → Bool
  timedOut  : ℕ → Bool
  knownVal  : ℕ → Option Block        -- knownValCert, served to clients
  finalized : Option Block
```

Handlers: `onProposal`, `onValCert`, `onConfCert`, `onTimeout`,
`onTimeoutCert`. Two details of the paper are kept exactly because the
safety proof depends on them: `onValCert` advances `cur` and stores
`knownVal` *before* the `votedConf ∨ timedOut` check, so a refused
certificate still moves the round; and the lock is updated only after a
Conf vote is signed, from a strictly higher round.

`Exec`/output checking is abstracted to a predicate `Valid : Block → Prop`
enforced on proposals. It plays no role in agreement and only matters for
liveness, where honest proposals are assumed `Valid`.

### 3.4 Global state and steps (`Protocol.lean`)

```lean
structure State where
  locals : V → Local Block
  log    : List (V × Msg)        -- honest signatures
  ghost  : List (ValRecord V Block)
```

`Step s s'` is an inductive relation with one constructor per handler,
applied at an honest `v`, with preconditions: for cert inputs,
`HasCert s …`; for proposals, nothing (any proposal may be delivered) except
the handler's own guards. Byzantine validators have no steps: their
signatures are already available through `Signed`. `Reachable` is the
reflexive-transitive closure from the initial state (all `cur = 0`, no lock,
empty log).

**Ghost records.** The paper's proofs reason about the moment of signing
("when `v` signed `Val(B″,r″)` it was locked on …"). Rather than quantify
over histories, every honest Val vote appends a `ValRecord` carrying the
signer's `lock` and the certificate `C` the proposal carried. Invariants
then speak about records in the current state, which is what makes them
inductive. The record is ghost: handlers do not read it.

For safety, `onTimeout` has no deadline precondition, so any honest
validator may time out any round `r ≥ cur` at any time. This includes every
behaviour of the timed protocol.

**Decidability.** With `[Fintype V] [DecidableEq V] [DecidableEq Block]` and
decidable `Valid`, every precondition is decidable, so a concrete execution
is checked by `decide` (the witness discipline of `lean-dag`).

## 4. Safety: proof architecture (`Safety/`)

*(Amended 2026-10-29.)* The invariant as implemented replaces the
per-round flags by bounds: every validation vote is at or below
`valVote` or `lb.round` (`val_bound`), every confirmation at or below
`lb.round` (`conf_bound`); the lock is the latest confirmation
(`lock_conf`, `conf_le_lock`); `lb_cert`; and the ghost `ValGhost` now
records a strict unlock (`lk.2 < ρ`). The safety proof no longer needs the
`ρ = r` case: the carried certificate's round lies strictly between the
confirmation round and the vote's round, contradicting minimality
directly. The original design follows.


Inductive invariants over `Reachable` states, for honest `v`:

- **I1 (current-round votes).** `(v, val B r) ∈ log → r ≤ cur v`; same for
  `conf`. Together with `Step.round_mono` this is Lem. vote-monotone.
- **I2 (one Val per round).** `(v, val B r), (v, val B' r) ∈ log → B = B'`,
  via `votedVal v r ↔ ∃ B, (v, val B r) ∈ log`.
- **I3 (Conf needs ValCert).** `(v, conf B r) ∈ log → ValCert s B r`.
- **I4 (lock semantics).** `lock v = some (B, rℓ) ↔ (v, conf B rℓ) ∈ log ∧
  ∀ r' > rℓ, ¬ votedConf v r'`; and `lock v = some (B, rℓ) → rℓ ≤ cur v`.
  One Conf per round (`votedConf`) makes the block unique.
- **I5 (unlock certificate, Lem. lock-validate).** For every ghost record
  `⟨v, B', r, some (B, rℓ), C⟩` with `B' ≠ B`: `C = some (B', ρ)`,
  `rℓ ≤ ρ < r`, and `ValCert s B' ρ`.
- **I6 (record reflects history).** For a record `⟨v, B', r, lk, _⟩`: every
  `(v, conf B₁ r₁) ∈ log` with `r₁ < r` has `lk = some (B₀, rℓ)` with
  `r₁ ≤ rℓ`; and `rℓ < r` (a validator that has confirmed in `r` does not
  validate in `r`).

From these, the theorems:

- `valCert_unique` (Lem. unique-valcert): two `ValCert`s at `r` intersect
  in an honest `v` (`exists_honest_mem_inter`), contradicting I2.
- `confCert_unique` (Thm. safety), following the paper's minimal-round
  argument: given `ConfCert B r`, `ValCert B' r'` with `r < r'`, `B ≠ B'`,
  `r'` minimal, pick honest `v` in both quorums; I6 gives `v`'s lock at the
  Val signing as `(B₀, rℓ)` with `r ≤ rℓ < r'`; I4 + I3 give `ValCert B₀ rℓ`,
  so `B₀ = B` by minimality (or by I4 uniqueness when `rℓ = r`); I5 gives
  `ValCert B' ρ` with `r ≤ ρ < r'`; `ρ = r` contradicts `valCert_unique`
  with `ValCert B r` (from I3 on an honest Conf signer); `r < ρ` contradicts
  minimality.
- `finalized_agree`: `finalized v = some B` requires `ConfCert B r` as a
  step precondition.

Each invariant gets a `decide` witness on a 4-validator, `f = 1` model
first, including a model with `byzantine = ∅` to keep F1 honest.

## 5. Liveness: architecture

### 5.1 Schedule (`Schedule.lean`, Phase 3)

Owners `Fin m`, parameter `k`, `leader r := ⟨r % m, _⟩`,
`Eligible r o := r < k ∨ o = leader r`. Lemma: for honest `o`, the set
`{r | k ≤ r ∧ Eligible r = {o}}` is infinite. Pure arithmetic.

### 5.2 Protocol core (`Liveness/Core.lean`, Phase 3)

The owner is modelled by the proposal rule of Alg. client_propose: given
the highest-round `ValCert(B, r″)` among the honest validators' `knownVal`
stores, propose `(B, some (B, r″))`; given none, propose any `Valid` block
with no certificate.

`good_round_confirms`: let `r* ≥ k` with `leader r*` honest, and `s₀`
reachable with every honest validator at `cur = r*`, not yet voted or timed
out at `r*`. Then (a) every honest validator accepts the owner's proposal
(the lock-reasoning lemma: a refusal would need a lock from a round strictly
above `r″`, but locks come only from `ValCert`s, all of which the owner has
seen, and no `ValCert` at a round `< r*` can change a lock once a validator
is at `r*` because `onValCert` rejects stale rounds); (b) after delivery to
all honest validators, `ValCert B r*` holds; (c) after delivering it,
`ConfCert B r*` holds. Stated as the existence of an honest-only step
sequence, and as the universal statement (a) that holds against arbitrary
interleaved adversarial steps that do not time out `r*`.

### 5.3 Timed layer (`Liveness/Timed.lean`, Phase 4)

Executions are indexed by discrete time. Added: `now`, per-validator
deadlines armed at `now + T r` on entering round `r`, an in-flight message
set with send times, and the honest owner's loop as its own state machine
(poll, adopt the highest `TimeoutCert` and `ValCert` learned, forward,
propose, collect). Partial synchrony: a `GST` and `Δ` such that every
message between honest parties sent at `t ≥ GST` is delivered by `t + Δ`;
honest processing is immediate. `T` is a parameter with a growth
hypothesis to be determined by the proof (see F2, F3 in §7).

Theorems: `round_advances` (Lem. round-growth), `exists_long_round`
(Lem. long-rounds), then `finalizes` (Thm. liveness) by combining with
§5.1–5.2. This layer is the largest and is where the paper's argument is
expected to need the most repair; in `lean-dag` the analogous layer took
most of the effort.

## 6. Repository layout

```
lean-linera/
  lakefile.toml  lean-toolchain  lake-manifest.json  Makefile  README.md
  LeanLinera.lean
  LeanLinera/
    Committee.lean      Messages.lean      Validator.lean     Protocol.lean
    Safety/   Invariants.lean  UniqueValCert.lean  Safety.lean
    Schedule.lean
    Liveness/ Core.lean  Timed.lean  Progress.lean  Liveness.lean
  LeanLineraTest/       concrete models and executions, checked by decide
  docs/   design.md (this)  spec.md  target-properties.md  report.md  style.md
  scripts/  axioms.lean (print axioms of every theorem)  extract-decls.py
  .github/workflows/ci.yml
```

Conventions, inherited from `lean-dag/docs/style.md`: one-sentence
docstrings on every public declaration; witness precedes theorem; standard
axioms only, no `sorry`, no `native_decide`; names `X_of_Y`; a protocol
variant in its own namespace. `make check` builds both libraries;
`scripts/axioms.lean` fails the build if any theorem depends on a
non-standard axiom.

## 7. Findings expected to feed back into the paper

Already visible from reading the appendix against the algorithms:

- **F1. Quorum intersection is misstated.** App. A says "any two quorums
  intersect in at least `n−2f > 0` honest voting power". Two quorums
  intersect in at least `n−2f` power, of which at least `n−3f > 0` is
  honest. The safety proof's intersection step then argues from the honest
  masses of two certificates (each `≥ n−2f`); that inference fails when
  `byzantine = ∅` and `n ≤ 4f` (e.g. `n = 4`, `f = 1`: honest sets `{1,2}`
  and `{3,4}`). The conclusion holds; the step should invoke intersection of
  the full quorums. The Lean lemma takes the correct form.
- **F2. Client loop ordering (Lem. progress).** Alg. client_propose queries
  `knownValCert` *before* forwarding `TimeoutCert(r*−1)`. A validator still
  in round `r*−1` can answer the query, then receive a withheld
  `ValCert(B₁, r*−1)` from a Byzantine party, lock on it, then advance to
  `r*`; the honest owner's proposal is refused and round `r*` fails. Once a
  validator is at `r*`, stale certificates no longer change its lock, so
  forwarding the timeout certificate first, waiting, then querying resolves
  it. The paper's "overwhelmingly likely" wait is not a proof-grade
  statement; the timed layer will make the required wait explicit.
- **F3. Required growth of `T r`.** Validators enter a round at different
  times (a Byzantine client may deliver a timeout certificate early to some
  of them). If the honest owner learns timeout certificates only by forming
  them, the entry spread can grow by a constant per round, and "deadlines
  grow without bound" is not sufficient (the spread grows linearly, so `T`
  must grow at least linearly with a slope depending on the unknown `Δ`).
  If the owner adopts any timeout certificate reported by a validator, the
  spread is bounded by a constant and unbounded growth suffices. The timed
  model will fix which owner behaviour is assumed.
- **F4. Lem. honest-single-leader** conflates eligibility with proposing in
  the multi-leader regime; the formal statement is restricted to `r ≥ k`,
  which is all the liveness proof uses.
- **F5.** Liveness needs the honest owner to be *active* (§Model says so;
  Thm. liveness omits it).
- **F7. Reading every honest locking block (modelling note, not a bug).**
  The timed model's obligation `propose` assumes the owner's proposal is
  built from locking blocks that include every honest validator's. The
  implementation collects responses until a quorum is reached and then for
  an extra fraction of the elapsed time (`quorum_grace_period`, in
  `communicate_with_quorum`), so it reads every honest locking block
  whenever the slowest honest response is not much slower than the fastest
  quorum. Against a worst-case adversary with unknown `Δ`, one honest
  response could be delayed past that window in every round and its lock
  then refuses every re-proposal. Production runs with fixed network
  timeouts, which is the accepted stance; the obligation records the
  assumption rather than a defect. (Corrected 2026-10-29: an earlier
  version of this note mistook the fraction for a fixed duration.)
- **F6. Fast-round locks are invisible to the client's query.** A
  confirmation vote in a fast round locks the validator on `(B₀, 0)` with
  no validation certificate, so `knownValCert` never records it. After a
  timed-out fast round, Alg. client_propose cannot learn `B₀`; a proposal
  of another block without a certificate is refused by every validator so
  locked, and one with a certificate from round `0` cannot exist. Liveness
  after a fast round therefore needs the super owner itself to re-propose
  `B₀`, or validators to report their locks (as the implementation does).
  This does not contradict the paper, whose Thm. liveness excludes the
  fast-round extension; `acceptable_of_highest_known` is stated under the
  hypothesis that no honest lock comes from a fast round.

## 7b. Paper versus implementation (`~/git/linera-protocol`, read 2026-10-29)

**Resolution (2026-10-29).** The paper's protocol description and proofs and
the Lean model now follow the implementation on I7–I13 (round-advancing
proposals, strict lock rule on the latest confirmation, locking block
served to clients and bounding proposals, timeout votes for the current
round only, client order and adoption). I1 is reflected as integer rounds
with an optional fast round, `k` multi-leader rounds and single-leader
rounds from `r_SL`; I5 is stated in the paper, not yet in Lean (timed
layer); I2 (validator fallback rounds), I3 (pseudo-random schedule, kept
abstract as `leader`), I4 (open rounds) and I6 (attestations) are
described in the paper or left out, not modelled.

Read against `linera-chain/src/manager.rs` (`ChainManager`),
`linera-core/src/client/chain_client/mod.rs` (proposal loop) and
`linera-base/src/ownership.rs` (rounds and timeouts). The Lean model follows
the paper; each item says what the implementation does instead.

Structure absent from the paper:

- **I1. Round structure.** Rounds are `Fast < MultiLeader(i) < SingleLeader(j)
  < Validator(k)`. Multi-leader rounds have no timeout except the last one;
  a multi-leader round ends as soon as any valid proposal for a later round
  is seen ("multi-leader rounds can always be skipped"), with no timeout
  certificate. The paper gives every round a deadline and advances only on
  certificates.
- **I2. Validator (fallback) rounds.** After `fallback_duration` of an
  unhandled tracked message, validators vote to put the chain in fallback
  mode, where validators themselves are the leaders (`vote_fallback`).
- **I3. Leader selection.** Weighted pseudo-random (`seed` = block height,
  optional `first_leader`), not round-robin. "The honest owner leads
  infinitely often" is then a probabilistic statement, or an assumption on
  the schedule, not a theorem of arithmetic as in `Config.exists_sole_eligible`.
- **I4. Open multi-leader rounds and super owners.** Multi-leader rounds may
  be open to anyone (`open_multi_leader_rounds`); super owners may propose
  in every non-validator round, and may open a later round while the fast
  round has not timed out.
- **I5. Timeouts.** Single-leader round `r` lasts `base_timeout +
  timeout_increment · r`: linear growth with a configured slope (relevant to
  F3). The fast round has its own optional duration.
- **I6. Unlocking-round attestation.** A validation vote signs the round of
  the certificate it relied on and a commitment to that quorum, for
  accountability; this is why the lock rule below is strict.

Validator rules that differ from Algs. on_proposal / on_certificate /
on_timeout:

- **I7. Proposals advance the round.** In multi-leader rounds and the first
  single-leader round a proposal for a round `≥ current_round` is accepted
  and sets the round; the paper requires `r = r_cur`. Later single-leader
  rounds require equality, as in the paper.
- **I8. The lock rule is on the latest confirmed vote, strict for a
  different block.** A proposal of a different block needs a carried
  certificate with `confirmed_vote.round < certificate.round`; the same block
  needs `≤`. The paper has `C.round ≥ lock.r` for a different block.
  Equivalent given unique validation per round (a conflicting certificate at
  the confirmation round cannot exist), so the safety theorem transfers.
- **I9. `locking_block` is not the lock.** It is the highest validated
  certificate seen, updated from carried certificates and from received
  validated-block certificates whether or not the validator votes, and also
  the fast-round proposal when voting to confirm it. Proposals must be
  strictly newer than it. It is what is served to clients; the paper's
  `knownValCert[r]` is a per-round store separate from the lock.
- **I10. Timeout votes.** Only for `round == current_round` (paper: `r ≥
  r_cur`). A timeout vote does not prevent a later confirmation vote in the
  same round; only a timeout certificate (which moves the round) does. The
  paper's on_certificate refuses after `timedOut[r]`. Both are safe; the
  Lean safety proof uses only `votedConf`, not `timedOut`, so dropping the
  guard would not affect it.
- **I11. One vote kept per kind.** Validators keep only the latest
  validation vote and the latest confirmation vote (validation rounds
  strictly increasing; the validation vote is cleared on confirming); the
  paper's per-round flags are equivalent under round monotonicity.

Client side, resolving the Phase 4 questions:

- **I12. Clients learn timeout certificates and locks from validators.**
  `ChainManagerInfo` carries the latest timeout certificate, the locking
  block (fast proposals included) and the validator's latest vote. The
  client adopts the timeout certificate (so the owner behaviour of F3 is the
  second option, with bounded entry spread) and re-proposes the locking
  block, fast proposals as `OriginalProposal::Fast` (which closes F6).
- **I13. Client order.** `process_pending_block`: if the local deadline has
  passed, request a timeout certificate and communicate it to validators;
  then re-read the manager values; if the locking block is in the current
  round, finalize it; else re-propose the locking block or a new block.
  Timeout certificate before query, as F2 requires. The paper's Alg.
  client_propose queries first.

## 8. Phases and order of work

| Phase | Content | Status |
|:---|:---|:---|
| 0 | scaffold: lake project, Mathlib cache, Makefile, CI, axioms script | done |
| 1 | `Committee`, `Messages`, `Validator`, `Protocol`; 4-validator witness executions | done |
| 2 | invariant, `valCert_unique`, `safety`, `finalized_agree`, `vote_of_eligible`, `lock_validate`, monotonicity | done |
| 3 | `Schedule`, `Liveness/Runs`, `Liveness/Fast`, `Liveness/Core` | done |
| 4 | timed layer, round-growth, long-rounds, liveness theorem | done (no fast round) |
| 5 | report.md with statements copied from source (`make report` checks them) | done |

The invariant as implemented (`Safety/Invariants.lean`, `VInv`) has the six
clauses of §4 plus: eligibility ghosts on validation and fast votes (for
Authenticity), and two `knownValCert` clauses (its entries are
certificates; a two-phase lock is recorded there) that the proposal-rule
lemma of Phase 3 consumes.

### Pending notes

- **Ghost-field erasure.** Done (`Safety/Erasure.lean`, `step_erase`):
  states with equal locals and equal `(signer, msg)` logs step to
  successors with equal erasures, so no handler reads a ghost field.
- **Reference implementation.** `~/git/linera-protocol`, notably the
  `linera-core` crate (client proposal loop) and `linera-chain`
  (`ChainManager`, the validator-side per-height state). Consult it for
  protocol questions before asking.

### Phase 4 as implemented (2026-10-29)

`Liveness/Timed/Exec.lean`: time is a tick counter; an execution is a state
sequence with at most one honest step per tick; a validator's entry into
its current round is the first tick at which it held it, and a timeout
vote may be attempted only once entry plus the round's duration has
passed (`Timeouts.dur`: fast round optional, last multi-leader round
`base`, `j`-th single-leader round `base + j·inc`). The key lemma
`le_round_or_tc`: a validator past a single-leader round got there through
a timeout certificate for it that existed strictly earlier.

`Liveness/Timed/Env.lean`: the environment `Env` — `GST`, `Δ`, `L`, the
honest owner `o` and its per-round proposal — with obligations
`leave_multi`, `timeout`, `tc`, `propose`, `cert`, `leader`, `inc_pos`,
`no_fast`, each allowing the escape "a block has been confirmed". The
re-proposal rule `JustRule` is the paper's.

`Liveness/Timed/Liveness.lean`: `Env.reach_round` (round growth), the
window invariant `WinAt` of the good round (`winAt_step`), and
`Env.liveness`. The good round `r` is chosen beyond every round held at
`GST` and with duration `≥ Δ + 2L + 2`; the first timeout certificate for
`r − 1` then appears after `GST`, everyone enters `r` within `Δ`, nobody
can leave before the duration, the proposal read at `t_q` passes every
lock (locks are frozen in the window except by confirming the owner's own
block), and the certificate is confirmed by all.

Not covered by the timed theorem: the fast round (`no_fast`), the
validator fallback rounds, open multi-leader rounds. The obligations
`propose` and `cert` abstract the owner's loop into the constant `L`; a
model of the owner as a state machine with polling and the grace period
would discharge them, under the assumption recorded as F7 below.

### Phase 4 design points settled by the implementation

1. **Owner loop ordering.** Forward `TimeoutCert(r−1)` first, then query
   `knownValCert`, then propose (F2). The paper's order is query first.
2. **How the owner learns timeout certificates.** Either only by forming
   them from timeout votes it collected, or also by adopting any it is
   shown by a validator. The second bounds the round-entry spread by a
   constant and lets `T r → ∞` suffice; the first needs `T` to outgrow a
   linear function of `r` with an unknown slope (F3).
3. **Timer model.** Discrete time; a validator's deadline for `r` is armed
   when it enters `r`; honest processing is immediate; after GST every
   honest-to-honest message is delivered within `Δ`.
4. **Whether to also time the fast round.** The implementation times it
   out; the untimed result `fast_round_finalizes` assumes no honest
   validator has timed out round `0` when the proposal arrives.

Phases 0–2 are the near-term deliverable and back every safety claim of the
paper. Phase 3 backs the protocol-level content of the liveness argument.
Phase 4 is the open-ended part and is where F2 and F3 are settled.

## 9. Decisions taken

All four open points of the first draft were confirmed on 2026-10-29:
repository `~/git/lean-linera` with local commits; abstract weighted quorum
system; safety untimed, fast-round liveness under an honest leader only,
slow-round view changes under partial synchrony; fast and slow rounds both
in the model.
