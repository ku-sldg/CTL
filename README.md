## "I leave to various future times, but not to all, my garden of forking paths." \- Jorge Luis Borges

# Directories
## Ctl

This is a shallow embedding of Computation tree logic (CTL) in Coq.

## Glib

This is a general-purpose library used by Ctl. Most notably, it exports a number of axioms, including:
- law of the excluded middle
- functional extensionality
- propositional extensionality
- choice (on propositional truncations)

# Building

One should be able to build by running `make`. If not, you may try regenerating the makefile with the command: `coq_makefile -f _CoqProject -o Makefile`.
