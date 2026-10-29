# lean-linera

A Lean 4 + Mathlib formalization of the per-height consensus protocol of the
Linera paper: the validator handlers, machine-checked safety over an untimed
model, and liveness under an honest leader (fast rounds) and partial
synchrony (slow rounds). See `docs/design.md` for the plan and the mapping
from the paper's lemmas to Lean theorems.

Build: `lake exe cache get && lake build` (or `make check`).
