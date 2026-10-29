# Development loop for lean-linera.
#
#   make fast     library only                     (skips the witnesses)
#   make check    both libraries                   (run before committing)
#   make axioms   print the axioms of every theorem; fails on a non-standard one

.PHONY: fast check axioms report help
.DEFAULT_GOAL := help

## fast: library only
fast:
	lake build LeanLinera

## check: both libraries
check:
	lake build

## axioms: every theorem uses only propext, Classical.choice, Quot.sound
axioms:
	lake env lean scripts/Axioms.lean

## report: every Lean statement displayed in docs/report.md is verbatim from the sources
report:
	python3 scripts/statements.py check

help:
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  make /'
