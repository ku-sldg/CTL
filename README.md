## "I leave to various future times, but not to all, my garden of forking paths." \- Jorge Luis Borges

# Directories
## Ctl

This is a shallow embedding of Computation tree logic (CTL) in Coq. It is defined in `Ctl/Definition.v`, but `Ctl/Basic.v` presents the definitions as more legible theorems.

The CTL library depends on the general-purpose library "Glib".

## Glib

This is a general-purpose library used by Ctl. Most notably, it exports a number of axioms, including:
- law of the excluded middle
- functional extensionality
- propositional extensionality
- choice (on propositional truncations)

It also exports several notations. To disable the printing of a particular notation, find the declaration in question in `Glib/Notation.v`, and add the "only parsing" option.

# Building

One should be able to build by running `make`. If not, you may try regenerating the makefile with the command: `coq_makefile -f _CoqProject -o Makefile`.
