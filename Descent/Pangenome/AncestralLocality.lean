/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# `AncestralLocality` -- heredity-first closure of pangenomic observations

The layer head for the research note "Ancestral locality" of 11 September 2026, transcribed as
`ANCESTRAL_LOCALITY.md`. A module of the group is imported here once its proof check has passed
on the bytes on main.

1. `CompatibilityNeutrality` -- the checked-exchange model of §4: ordered children, exchange
   kernels and the compatibility kernel `K_G`; Theorem 3, that every single feature is exactly
   neutral; the finite-population law with its exact binomial count law (§4.1); and the
   eight-state witness of §5.2, two populations with one observed law and two next-generation
   observed laws.

This file contains no declarations.
-/
