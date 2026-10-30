# linera-lean

A Lean 4 + Mathlib formalization of the per-height consensus protocol of the
Linera paper, as implemented in `linera-protocol`: the validator handlers
(fast round, skippable multi-leader rounds, single-leader rounds, locking
blocks, the strict lock rule), machine-checked safety over an untimed
model, and liveness under an honest leader (fast rounds) and in a good
two-phase round. See `docs/design.md` for the plan, the mapping from the
paper's lemmas to Lean theorems, and the comparison with the
implementation.

Build: `lake exe cache get && lake build` (or `make check`); `make axioms`
checks that every theorem uses only `propext`, `Classical.choice` and
`Quot.sound`.

## Layout

- `Linera/Committee.lean` — abstract quorum system; the stake-weighted
  committee as an instance, with quorum intersection.
- `Messages.lean`, `Validator.lean`, `Protocol.lean` — messages, the
  per-chain configuration, the validator handlers, and the transition system.
- `Safety/` — the inductive invariant, its preservation, monotonicity, and
  the safety theorems (`safety`, `finalized_agree`, `valCert_unique`,
  `lock_validate`, `vote_of_eligible`).
- `Schedule.lean`, `Liveness/` — the proposal schedule, run lemmas, fast-round
  finalization (`fast_round_finalizes`) and the good-round theorem
  (`good_round_confirms`).
- `Liveness/Timed/` — timed executions with deadlines, the environment
  (partial synchrony after `GST`, the honest owner's obligations), round
  growth and the liveness theorem (`TExec.Env.liveness`).
- `Chain/` — cross-chain messages and events: bundles, the two-queue inbox
  of the implementation and its order-independence theorem
  (`Inbox.run_eq_canonical`), the ledger, events and streams
  (`Ledger.Held.payload_eq`), and a validator's view of several chains with
  the inbox consistency theorem (`Node.inbox_eq_of_counters`).
- `LineraTest/` — concrete executions on a four-validator model, the inbox
  scenarios of the implementation's unit tests, and two-chain runs, checked
  by `decide`.
- `docs/design.md` — plan, design, mapping to the paper, findings.
