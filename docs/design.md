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

| Paper | Statement | Lean | Phase |
|:---|:---|:---|:---|
| Lem. honest-mass | a certificate carries ≥ `n−2f` honest weight | `Committee.honest_weight_of_quorum` | 1 |
| (implicit) quorum intersection | two quorums share an honest validator | `Committee.exists_honest_mem_inter` | 1 |
| Lem. no-further-votes | a finalized instance signs nothing more | `Validator.finalized_no_vote` | 2 |
| Lem. vote-monotone | `r_cur` and lock round never decrease; Val/Conf votes are cast at `r_cur` | `Step.round_mono`, `Step.lock_mono`, `Inv.vote_at_cur` | 2 |
| Lem. unique-valcert | at most one block has a `ValCert` per round | `Safety.valCert_unique` | 2 |
| Lem. lock-validate | a Val vote against the lock carries `ValCert(B′,ρ)`, `r_ℓ ≤ ρ < r` | `Inv.unlock_cert` | 2 |
| Thm. safety | no two conflicting `ConfCert`s at a height | `Safety.confCert_unique` | 2 |
| §Model Safety | no two honest validators finalize different blocks | `Safety.finalized_agree` | 2 |
| §Model Authenticity | only an eligible owner's proposal receives a Val vote | `Safety.vote_of_eligible` | 2 |
| Lem. honest-single-leader | infinitely many rounds `r ≥ k` with `L_r` honest | `Schedule.infinitely_many_honest_leader` | 3 |
| Lem. progress (core) | in a good round, every honest validator accepts the honest proposal; a `ConfCert` follows | `Liveness.Core.good_round_confirms` | 3 |
| Lem. round-growth | a round without `ConfCert` yields a `TimeoutCert`; all honest validators advance | `Liveness.Timed.round_advances` | 4 |
| Lem. long-rounds | some round after GST is long enough | `Liveness.Timed.exists_long_round` | 4 |
| Thm. liveness | an honest active owner + partial synchrony ⇒ a block is finalized | `Liveness.finalizes` | 4 |
| App. fast-round | safety is preserved when round 0 skips validation | `Safety.confCert_unique` (fast round is part of the core model) | 2 |
| App. fast-round | an honest super owner finalizes in round 0 without timing | `Liveness.Fast.finalizes` | 3 |

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

## 8. Phases and order of work

| Phase | Content | Size (lines, estimate) |
|:---|:---|:---|
| 0 | scaffold: lake project, Mathlib cache, Makefile, CI, docs skeleton, axioms script | — |
| 1 | `Committee`, `Messages`, `Validator`, `Protocol`; 4-validator witness execution reaching a `ConfCert` | ~800 |
| 2 | invariants I1–I6, `valCert_unique`, `confCert_unique`, `finalized_agree`, `vote_of_eligible`; witnesses incl. `byzantine = ∅` | ~1500 |
| 3 | `Schedule`, `Liveness/Core` | ~800 |
| 4 | timed layer, round-growth, long-rounds, liveness theorem | ~3000+ |
| 5 | report.md with statements copied from source; mapping table of §1 filled in | ~300 |

Phases 0–2 are the near-term deliverable and back every safety claim of the
paper. Phase 3 backs the protocol-level content of the liveness argument.
Phase 4 is the open-ended part and is where F2 and F3 are settled.

## 9. Decisions taken

All four open points of the first draft were confirmed on 2026-10-29:
repository `~/git/lean-linera` with local commits; abstract weighted quorum
system; safety untimed, fast-round liveness under an honest leader only,
slow-round view changes under partial synchrony; fast and slow rounds both
in the model.
