# Development loop for linera-lean.
#
#   make fast     library only                     (skips the witnesses)
#   make check    both libraries                   (run before committing)
#   make axioms   print the axioms of every theorem; fails on a non-standard one

.PHONY: fast check axioms report pdf help
.DEFAULT_GOAL := help

## fast: library only
fast:
	lake build Linera

## check: both libraries
check:
	lake build

## axioms: every theorem uses only propext, Classical.choice, Quot.sound
axioms:
	lake env lean scripts/Axioms.lean

## report: every Lean statement displayed in docs/report.md is verbatim from the sources
report:
	python3 scripts/statements.py check

## pdf: docs/pdf/report.pdf from docs/report.md (pandoc + xelatex)
pdf: report
	mkdir -p docs/pdf
	pandoc docs/report.md -o docs/pdf/report.pdf --pdf-engine=xelatex --toc \
	  -V mainfont="Times New Roman" -V monofont="Menlo" -V geometry:margin=2.5cm

help:
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  make /'
