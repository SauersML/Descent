/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Scaling
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Core: one island-model `F_ST`, and the lattice its specialisations form

**Depth 0-1. Imports `Core.Ratios` and Mathlib, and nothing else from this corpus.**

## What this file replaces

The corpus wrote the island-model equilibrium out five times, in three incompatible
parameterisations, in three modules that do not import each other:

    1 / (1 + 4Ne·m·(n/(n-1)) + 4Ne·μ)     PopGen.fstIslandEquilibriumFiniteDemes
    1 / (1 + 4Ne·m + 4Ne·μ)               PopGen.fstMigrationMutationEquilibriumManyDemes
    1 / (1 + 4Ne·m)                       Portability.fstMigrationDriftEquilibrium
    1 / (1 + θ)                           PopGen.DGP.fstMutationDriftEquilibrium
    1 / (1 + θ + 2M)                      PopGen.DGP.fstEquilibrium

These are ONE formula and four specialisations of it. Nothing in the corpus said so.
Three modules independently re-derived a member of this family -- one in raw `(Ne, m, μ)`,
one in raw `θ`, one in the structure fields `p.theta` and `p.bigM` -- and no theorem
placed any of them relative to any other, so a change to one diverged from the rest
silently.

The master is `fstIslandEquilibrium`. Each specialisation is a THEOREM below, not a
second definition, and the named bodies in the subsystem modules call this one.

## The convention this file fixes, and what it costs to get wrong

Every `F_ST` in this corpus written in `τ/(1 + τ)` coordinates is a **Hudson** `F_ST`.
That is not a stylistic choice. `neiFst`'s docstring records Nei's estimator FALSIFIED
at up to 18.59 sems against the split law on genotype matrices where Hudson's matches at
0.03, and records that the ratio between them is not constant across the design (0.62,
0.60, 0.68, 0.81) -- so no correction factor converts one to the other and a reader who
substitutes is simply wrong by a factor that moves with the data.

`NeiFst` and `HudsonFst` below are therefore distinct one-field types rather than two
reals. Substituting one for the other does not typecheck. A documented hazard that the
compiler enforces is a different object from one a docstring warns about.

## Empirical status

None. The bodies here are algebra: an equilibrium formula is a claim about a model, and
what carries an empirical status is a named quantity in a subsystem module asserting that
this algebra computes something measurable. Those names keep their own docstrings, their
own regimes, and their own ledger rows.
-/

namespace Descent.Core

open Filter Topology

/-! ### Scaling conventions

The four in `4·Ne·μ` is `2 · ploidy`: two lineages, each diploid. Writing it as a named
constant rather than a literal is what lets a ploidy change be a one-line edit instead of
a census.

`ploidy` and `scalingConstant` are defined in `Core/Scaling.lean`, imported above, along
with the one-field types `Theta`, `BigM`, `Tau` and `Rho` that carry these scalings where
a `ℝ` used to. They are in the same namespace, so every reference here and downstream
resolves unchanged. The two named rates below keep their bodies, their empirical status
and their ledger rows; `Theta.ofRate` and `BigM.ofRate` are the same arithmetic in the
wrapped types, and `scaledMutationRate_eq_theta` below is the identification. -/

/-- Scaled mutation rate, `θ = 4 Ne μ`.

    Empirical status: **VALIDATED** (`simcov/battery_bulk19.py`), and the verdict moved
    here from `PopGen.DGP`, which carried it on a wrapper that forwarded to this body.
    That placement was the sentence above taken too literally: a shape asserts nothing,
    but this shape's CONSTANT does, and the constant is here. There is no longer a second
    name for the measurement to be attached to.

    A scaling cannot be measured on its own, so it is read through the infinite-alleles
    equilibrium heterozygosity `θ/(1+θ)`, separately validated at
    `Portability.hetMutationFloor`. The body predicts 0.50000, 0.50000, 0.20000 and
    0.20000 against measured 0.53297 ± 0.01697, 0.46858 ± 0.01307, 0.20081 ± 0.00688 and
    0.21293 ± 0.00801 -- worst cell 2.40 sems.

    Power: `Nₑ` and `μ` are swept by a factor of four INDEPENDENTLY, so two cells reach
    `θ = 1` and two reach `θ = 4` by different routes. A wrong numeric factor and a wrong
    `Nₑ`-dependence each break one of those pairs, which a sweep holding `4·Nₑ·μ` fixed
    could not detect at all. -/
noncomputable def scaledMutationRate (Ne μ : ℝ) : ℝ := 2 * ploidy * Ne * μ

/-- Scaled migration rate, `M = 4 Ne m`, in the same units as `θ`. Being in the same
units is what makes `fstEquilibrium`'s `θ + 2M` comparable term by term.

    Empirical status: **VALIDATED** (`simcov/battery_bulk19.py`), moved here with the
    wrapper that used to carry it, for the reason given on `scaledMutationRate` above.

    Read through the two-deme island `F_ST` from coalescence times against `1/(1 + 2·M)`,
    where the factor two is `islandDemeCorrection` at `n = 2` -- the deme count matters and
    a deme-blind law would be off by it. The body predicts 0.33333, 0.33333, 0.11111 and
    0.11111 against measured 0.31967 ± 0.01809, 0.30661 ± 0.01138, 0.10482 ± 0.00611 and
    0.10891 ± 0.00467, worst cell 2.35 sems.

    Power: as for `scaledMutationRate`, `Nₑ` and `m` are swept by a factor of four
    INDEPENDENTLY, so `M = 1` and `M = 4` are each reached twice by different routes and
    the `Nₑ`-dependence is separately on trial. -/
noncomputable def scaledMigrationRate (Ne m : ℝ) : ℝ := 2 * ploidy * Ne * m

/-- **The scaling constant, stated as a value.** Both scaled rates carry the same four,
and a divergence between them fails this. -/
theorem scaledRates_share_constant (Ne x : ℝ) :
    scaledMutationRate Ne x = scaledMigrationRate Ne x := by
  unfold scaledMutationRate scaledMigrationRate; ring

/-- **The four, written once.** -/
theorem scaledMutationRate_eq (Ne μ : ℝ) : scaledMutationRate Ne μ = 4 * Ne * μ := by
  unfold scaledMutationRate ploidy; ring

/-- **The four, written once.** -/
theorem scaledMigrationRate_eq (Ne m : ℝ) : scaledMigrationRate Ne m = 4 * Ne * m := by
  unfold scaledMigrationRate ploidy; ring

/-- **The scaled mutation rate is `2 · ploidy · Nₑ · μ`, and that is its body.**

This states the definition against itself, so it is `rfl` and it cannot fail. Kept
rather than deleted because it names the shape at the point a reader meets the rate, but
it is NOT the theorem that protects the constant: `scaledMutationRate_eq` above is, since
that one relates the body to the literal `4` and so breaks if `ploidy` changes and the
rate does not follow. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    scaledMutationRate Ne mu = 2 * ploidy * Ne * mu := rfl

/-- **The scaled migration rate carries the same shape**, and likewise by `rfl`. The two
rates were written in different files, each spelling out its own `4`; what pins them
together now is `scaledRates_share_constant`, not this. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    scaledMigrationRate Ne m = 2 * ploidy * Ne * m := rfl

/-! ### The named rates and the wrapped types are the same arithmetic

`Core/Scaling.lean` carries `θ` and `M` as one-field types so that one cannot be passed
where the other is wanted. These two theorems say the wrapper costs nothing but the type:
the number inside is the one the named rate computes, and it is the number every ledger
row below was measured against. A divergence between the two sites -- a factor changed in
`scalingConstant` and not here, or the reverse -- fails these. -/

/-- **`Theta.ofRate` wraps `scaledMutationRate`.**

NOT `@[simp]`, and `simpNF` is why. `Theta.value_ofRate` is already simp and rewrites this
lemma's own left-hand side to `4 * Ne * μ`, so as a simp lemma this one could never fire --
it sat in the simp set contributing nothing except a non-confluence for the first person to
run the checker. It is the identification between the wrapped type and the named ledgered
rate, and it is used by name. -/
theorem scaledMutationRate_eq_theta (Ne μ : ℝ) :
    (Theta.ofRate Ne μ).value = scaledMutationRate Ne μ := by
  rw [Theta.value_ofRate, scaledMutationRate_eq]

/-- **`BigM.ofRate` wraps `scaledMigrationRate`.** Not `@[simp]`, for the reason on
`scaledMutationRate_eq_theta` directly above. -/
theorem scaledMigrationRate_eq_bigM (Ne m : ℝ) :
    (BigM.ofRate Ne m).value = scaledMigrationRate Ne m := by
  rw [BigM.value_ofRate, scaledMigrationRate_eq]

/-! ### The finite-deme correction -/

/-- The island-model deme-count correction, `d / (d - 1)`.

With `d` demes a migrant arrives from one of the OTHER `d - 1`, so the effective
migration rate between any two is inflated by this factor. It is `1` only in the limit
of infinitely many demes, and at `d = 2` it is `2` -- a factor of two, which is the size
of the error a many-deme formula makes on a two-population split.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def islandDemeCorrection (d : ℝ) : ℝ := ratio d (d - 1)

/-- **islandDemeCorrection at one deme, named.** With a single deme there is nowhere to
migrate from; the divisor vanishes and Lean returns `0`, reporting no inflation at all
for a case where the quantity is undefined. Consumers must require `d ≠ 1`. -/
theorem islandDemeCorrection_one_is_junk : islandDemeCorrection 1 = 0 := by
  unfold islandDemeCorrection ratio; norm_num

/-- **At two demes the correction is exactly two.** Pinned as a value because this is the
factor a many-deme formula drops on the two-population split that most of the corpus's
portability results are stated for. -/
@[simp] theorem islandDemeCorrection_two : islandDemeCorrection 2 = 2 := by
  unfold islandDemeCorrection ratio; norm_num

/-- **At twenty demes it is `20/19`.** Pinned as a value for the same reason as the
two-deme case, and because this is the other factor the ledger measured:
`simcov/battery_falsrepair_c2.py` separates the finite-deme form carrying this correction
from the many-deme limit that drops it, at `d = 20`, on a design whose error bars are
half those of the run that could not tell them apart. -/
@[simp] theorem islandDemeCorrection_twenty : islandDemeCorrection 20 = 20 / 19 := by
  unfold islandDemeCorrection ratio; norm_num

/-! ### The two factors the ledger measured, on the scaled rate that carries them

`BigM` is `4 Nₑ m` and never `8 Nₑ m`: the deme correction belongs to the deme count, not
to the migration scaling. These two theorems say what the correction does to a `BigM` at
the two deme counts the corpus has been measured at, so the factor a formula drops when
it omits the correction is a named quantity rather than a step in a derivation. -/

/-- **Two demes: the correction doubles the flow.** This is the factor
`simcov/battery_bulk38.py` measured. `1/(1 + θ + M)` was rejected at 3.30 sems and 57%
relative; `1/(1 + θ + 2M)` matches at 1.10. The `2` is this. -/
theorem twoDeme_vs_manyDeme_factor (Ne m : ℝ) :
    (BigM.ofRate Ne m).value * islandDemeCorrection 2 = 2 * (BigM.ofRate Ne m).value := by
  rw [islandDemeCorrection_two]; ring

/-- **Twenty demes: the correction is 5.3%, and it is resolvable.** This is the factor
`simcov/battery_falsrepair_c2.py` measured, where the limit form misses at 3.92 sems and
13% relative. Small enough to look like an approximation, large enough to falsify a body
at forty-eight replicates -- which is the case for carrying the deme count rather than
assuming it away. -/
theorem twentyDeme_vs_manyDeme_factor (Ne m : ℝ) :
    (BigM.ofRate Ne m).value * islandDemeCorrection 20
      = (20 / 19) * (BigM.ofRate Ne m).value := by
  rw [islandDemeCorrection_twenty]; ring

/-- **The exact distance from one**, which is more than the limit says: at `d` demes the
correction overshoots `1` by exactly `1/(d-1)`. A reader who needs to know whether the
many-deme formula is usable at `d = 20` gets `5%` from this and nothing from a limit. -/
theorem islandDemeCorrection_sub_one (d : ℝ) (hd : d ≠ 1) :
    islandDemeCorrection d - 1 = 1 / (d - 1) := by
  unfold islandDemeCorrection ratio
  have h : d - 1 ≠ 0 := sub_ne_zero_of_ne hd
  field_simp
  ring

/-- **The many-deme limit.** The correction tends to one as the deme count grows, which
is the sense in which the many-deme equilibrium below is a specialisation of the
finite-deme one. -/
theorem islandDemeCorrection_tendsto_one :
    Tendsto islandDemeCorrection atTop (𝓝 1) := by
  have hEq : islandDemeCorrection =ᶠ[atTop] fun d : ℝ ↦ 1 + 1 / (d - 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with d hd
    have h : d - 1 ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; exact absurd hc (by linarith)
    unfold islandDemeCorrection ratio
    field_simp
    ring
  rw [tendsto_congr' hEq]
  have hsub : Tendsto (fun d : ℝ ↦ d - 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).congr
      (fun x ↦ by show x + -1 = x - 1; ring)
  have h : Tendsto (fun d : ℝ ↦ 1 / (d - 1)) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp hsub).congr (fun x ↦ (one_div (x - 1)).symm)
  simpa using tendsto_const_nhds.add h

/-! ### The master equilibrium -/

/-- Total scaled flow into a deme, `M·(d/(d-1)) + θ`.

Naming it separates the two questions the equilibrium answers: what counts as flow, and
how flow becomes a differentiation. Every member of the lattice below differs only in
what it puts here.

**It takes `BigM` and `Theta`, not four reals.** The two failures `Core/Scaling.lean`
records were both a scaled quantity passed where a differently-scaled one was wanted, and
this is the argument position where that happened. A caller now supplies `BigM.ofRate Ne m`
and `Theta.ofRate Ne μ`, so the two cannot be exchanged and the effective size cannot be
given twice with different meanings. The raw `(Ne, m, μ, d)` spelling is gone rather than
kept beside this one: a second route that accepts the confusable arguments is exactly what
`deployedR2FromIsland` was, and it was deleted for the same reason.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def scaledFlow (bigM : BigM) (theta : Theta) (nDemes : ℝ) : ℝ :=
  bigM.value * islandDemeCorrection nDemes + theta.value

/-- **`1/(1 + x)` is the complement of a saturation**, away from the pole.

The hypothesis is not decoration. At `x = -1` the two sides are `0` and `1`: Lean's
`1/0 = 0` makes the left side report complete differentiation while the right reports
none. An earlier version of this theorem was stated without the hypothesis and was
false at exactly that point -- which is the junk-value discipline the rest of the corpus
applies to definitions, arriving here for a theorem. -/
theorem one_div_one_add_eq_complement_saturation (x : ℝ) (h : 1 + x ≠ 0) :
    1 / (1 + x) = complement (saturation x) := by
  unfold complement saturation
  field_simp
  ring

/-- **`F_ST` from a total scaled flow**, `1 / (1 + x)`.

Every equilibrium `F_ST` in this corpus is this map applied to a different flow. Naming
the map separates the two questions -- what counts as flow, and how flow becomes a
differentiation -- and it is what lets the five bodies the corpus had be five flows
rather than five formulas.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def fstFromFlow (x : ℝ) : ℝ := 1 / (1 + x)

/-- **No flow, no differentiation is lost.** At zero migration and zero mutation the
equilibrium is one: two demes with nothing connecting them are completely differentiated. -/
@[simp] theorem fstFromFlow_zero : fstFromFlow 0 = 1 := by
  unfold fstFromFlow; norm_num

/-- **Flow drives differentiation down.** Strictly decreasing on non-negative flows,
which is the qualitative content every named equilibrium below inherits. -/
theorem fstFromFlow_lt_of_lt (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) :
    fstFromFlow y < fstFromFlow x := by
  unfold fstFromFlow
  apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **Island-model `F_ST` at migration-mutation-drift equilibrium, with the deme count
carried.**

    F_ST = 1 / (1 + 4 Ne m (d/(d-1)) + 4 Ne μ)

This is the only place the formula is written. Every other `F_ST` equilibrium in the
corpus is a theorem below placing a named body inside this family.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def fstIslandEquilibrium (bigM : BigM) (theta : Theta) (nDemes : ℝ) : ℝ :=
  fstFromFlow (scaledFlow bigM theta nDemes)

/-- **The master, in the raw coordinates the subsystem modules wrote it in.** This is the
bridge that lets `fstIslandEquilibriumFiniteDemes` be a wrapper rather than a copy, and it
is now also the only way back to `(Ne, m, μ)`: the master itself no longer accepts them, so
a body written in raw rates reaches this family through `BigM.ofRate` and `Theta.ofRate`
here and nowhere else. -/
theorem fstIslandEquilibrium_eq (Ne m μ nDemes : ℝ) :
    fstIslandEquilibrium (BigM.ofRate Ne m) (Theta.ofRate Ne μ) nDemes
      = 1 / (1 + 4 * Ne * m * islandDemeCorrection nDemes + 4 * Ne * μ) := by
  unfold fstIslandEquilibrium fstFromFlow scaledFlow
  rw [BigM.value_ofRate, Theta.value_ofRate]
  ring_nf

/-- **The equilibrium is a saturation of the total scaled flow.** `F_ST = 1/(1 + x)` is
`1 - saturation x`, so the whole family lives on one curve and the only thing that
distinguishes its members is what they put into `x`. This is the statement that makes
the lattice below a lattice rather than a list. -/
theorem fstIslandEquilibrium_eq_complement_saturation (bigM : BigM) (theta : Theta)
    (nDemes : ℝ) (h : 1 + scaledFlow bigM theta nDemes ≠ 0) :
    fstIslandEquilibrium bigM theta nDemes
      = complement (saturation (scaledFlow bigM theta nDemes)) := by
  unfold fstIslandEquilibrium fstFromFlow
  exact one_div_one_add_eq_complement_saturation _ h

/-! ### The specialisation lattice

Four theorems, each dropping one term or changing coordinates. Together they say that
the five bodies the corpus had are one body. -/

/-- **Many demes: the correction is one.** `fstMigrationMutationEquilibriumManyDemes` is
the master at a deme correction of one, which `islandDemeCorrection_tendsto_one` shows is
the large-`d` limit. -/
theorem fstIslandEquilibrium_manyDemes (Ne m μ nDemes : ℝ)
    (hd : islandDemeCorrection nDemes = 1) :
    fstIslandEquilibrium (BigM.ofRate Ne m) (Theta.ofRate Ne μ) nDemes
      = 1 / (1 + 4 * Ne * m + 4 * Ne * μ) := by
  rw [fstIslandEquilibrium_eq, hd]; ring_nf

/-- **No mutation: `μ = 0`.** `fstMigrationDriftEquilibrium` is the many-deme master with the
mutation term dropped. Migration alone. -/
theorem fstIslandEquilibrium_no_mutation (Ne m nDemes : ℝ)
    (hd : islandDemeCorrection nDemes = 1) :
    fstIslandEquilibrium (BigM.ofRate Ne m) (Theta.ofRate Ne 0) nDemes
      = 1 / (1 + 4 * Ne * m) := by
  rw [fstIslandEquilibrium_manyDemes Ne m 0 nDemes hd]; ring_nf

/-- **No migration: `m = 0`.** `fstMutationDriftEquilibrium θ` is the master with the
migration term dropped and `θ = 4 Ne μ` substituted -- the pure mutation-drift balance a
single isolated population reaches. -/
theorem fstIslandEquilibrium_no_migration (Ne μ nDemes : ℝ) :
    fstIslandEquilibrium (BigM.ofRate Ne 0) (Theta.ofRate Ne μ) nDemes
      = 1 / (1 + scaledMutationRate Ne μ) := by
  unfold fstIslandEquilibrium fstFromFlow scaledFlow
  rw [BigM.value_ofRate, Theta.value_ofRate, scaledMutationRate_eq]
  ring_nf

/-- **The `θ` reparameterisation.** The scaled coordinates are not a different model:
`1/(1 + θ)` at `θ = 4 Ne μ` is the master with no migration. Written out because the
corpus had `fstMutationDriftEquilibrium` taking a bare `θ` in one module and
`fstIslandEquilibriumFiniteDemes` taking `(Ne, μ)` in another, with nothing relating the
two spellings. -/
theorem fstIslandEquilibrium_no_migration_scaled (Ne μ nDemes θ : ℝ)
    (hθ : θ = scaledMutationRate Ne μ) :
    fstIslandEquilibrium (BigM.ofRate Ne 0) (Theta.ofRate Ne μ) nDemes = 1 / (1 + θ) := by
  rw [fstIslandEquilibrium_no_migration, hθ]

/-- **The structure-field coordinates, `1/(1 + θ + 2M)`.** The bridge to the two
parameter records that write the equilibrium in scaled rates rather than in
`(Nₑ, m, μ)` -- `Core.PopGenParameters.fstEquilibrium` and `PopGen.DGP.fstEquilibrium`,
which are the same body in two records' fields.

**The `2` is the deme correction, and the deme count is `2`.** Both records define
`bigM` as `scaledMigrationRate`, which is `4 Nₑ m` -- `PopGenParameters.bigM` by
definition and `EvolutionaryParameters.bigM` by
`PopGen.EvolutionaryParameters_bigM_eq_ploidy_form` -- so `2M` is `8 Nₑ m`, while the
master carries `4 Nₑ m · d/(d-1)`. Those agree exactly at `d = 2`. So the free-looking
coefficient on `M` is not a coordinate artefact and not a many-deme reading: it is
`islandDemeCorrection` evaluated at the two-population split that most of this corpus's
portability results are stated for, and a reader who takes `1/(1 + θ + 2M)` for the
many-deme law is wrong by that factor.

This statement was previously written with hypotheses `bigM = 2 Nₑ m` and a deme
correction of one. Those are mutually consistent and describe no declaration in the
corpus: no `bigM` here is `2 Nₑ m`. The theorem was true and bridged nothing, and its
docstring asserted the inverted convention -- `bigM` is `2 Nₑ m`, NOT `4 Nₑ m` -- in a
file whose purpose is to hold the scaling constants. -/
theorem fstIslandEquilibrium_structure_coords (Ne m μ nDemes θ bigM : ℝ)
    (hd : islandDemeCorrection nDemes = 2)
    (hθ : θ = scaledMutationRate Ne μ) (hM : bigM = scaledMigrationRate Ne m) :
    fstIslandEquilibrium (BigM.ofRate Ne m) (Theta.ofRate Ne μ) nDemes
      = 1 / (1 + θ + 2 * bigM) := by
  have hflow : 1 + scaledFlow (BigM.ofRate Ne m) (Theta.ofRate Ne μ) nDemes
      = 1 + θ + 2 * bigM := by
    unfold scaledFlow
    rw [hd, hθ, hM, BigM.value_ofRate, Theta.value_ofRate,
      scaledMutationRate_eq, scaledMigrationRate_eq]
    ring
  unfold fstIslandEquilibrium fstFromFlow
  rw [hflow]

/-! ### `F_ST` from a scaled coalescence time

The other coordinate the corpus works in. `τ/(1 + τ)` is `saturation`, and every result
written in it is a Hudson `F_ST`. -/

/-- `F_ST` from a scaled coalescence time, `τ / (1 + τ)`.

**It takes `Tau`, not a real.** `Core/Scaling.lean` gives the reason as a theorem:
`fstFromTau` and `fstFromFlow` are `τ/(1+τ)` and `1/(1+x)`, which `fstFromFlow_add_fstFromTau`
proves are complements, so passing a scaled RATE here where a scaled TIME was wanted does
not make a small error -- it returns one minus the answer. As reals nothing separated the
two arguments; `Theta`, `BigM` and `Tau` are the same numbers in the same regimes.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def fstFromTau (t : Tau) : ℝ := saturation t.value

/-- **The split law and the equilibrium law are complementary readings of one curve.**
`F_ST = τ/(1+τ)` and `F_ST = 1/(1 + x)` are `saturation` and its complement, so a result
stated in one coordinate transfers to the other by reading `τ = 1/x`. Stated because the
corpus writes both and a reader meeting them in different files has no reason to expect
they are the same object. -/
theorem fstFromTau_add_equilibrium (t : Tau) (h : 1 + t.value ≠ 0) :
    fstFromTau t + 1 / (1 + t.value) = 1 := by
  unfold fstFromTau saturation
  field_simp
  ring

/-- **The equilibrium law and the split law are complements.** `fstFromFlow x` and
`fstFromTau x` sum to one away from the pole, so a result in either coordinate transfers
to the other. -/
theorem fstFromFlow_add_fstFromTau (t : Tau) (h : 1 + t.value ≠ 0) :
    fstFromFlow t.value + fstFromTau t = 1 := by
  unfold fstFromFlow
  rw [add_comm]
  exact fstFromTau_add_equilibrium t h

/-- **`F_ST` from a scaled time lands in the unit interval.** -/
theorem fstFromTau_mem_unit (t : Tau) (h : 0 ≤ t.value) :
    0 ≤ fstFromTau t ∧ fstFromTau t ≤ 1 :=
  saturation_mem_unit t.value h

/-- **A longer split differentiates more.** `τ/(1+τ)` is strictly increasing.

Stated here rather than reproved at each use: `Core.Moments` opened three separate
proofs with this same four-line `unfold`, `div_lt_div_iff₀`, `nlinarith` argument, and
the duplication guard reported the block three times over. A tactic script repeated
verbatim is a lemma that has not been named. -/
theorem fstFromTau_lt_fstFromTau (t₁ t₂ : Tau) (h0 : 0 ≤ t₁.value)
    (hlt : t₁.value < t₂.value) : fstFromTau t₁ < fstFromTau t₂ := by
  unfold fstFromTau saturation
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The split law never reaches complete differentiation.**

The STRICT companion to `fstFromTau_mem_unit`, which gives only `≤ 1`. The consumers
that need this need it strictly -- every monotonicity result below rests on the
deployed metric being computed at an `F_ST` short of one -- and were each proving it
inline. -/
theorem fstFromTau_lt_one (t : Tau) (h0 : 0 ≤ t.value) : fstFromTau t < 1 := by
  unfold fstFromTau saturation
  rw [div_lt_one (by linarith)]
  linarith

/-! ### Nei and Hudson are not interchangeable, and now cannot be

Two one-field types. The wrapper costs a `.value` at each use and buys the property that
a Nei estimate cannot be passed where a Hudson one is required. -/

/-- A Hudson `F_ST`: the ratio-of-averages estimator, and the convention every `τ/(1+τ)`
result in this corpus is stated in. -/
structure HudsonFst where
  /-- The estimate. -/
  value : ℝ

/-- A Nei `G_ST`: the average-of-ratios estimator. FALSIFIED at up to 18.59 sems against
the split law on the genotype matrices where Hudson's matches at 0.03. -/
structure NeiFst where
  /-- The estimate. -/
  value : ℝ

/-- A scaled coalescence time reads as a Hudson `F_ST`, and only as a Hudson one.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def hudsonFromTau (t : Tau) : HudsonFst := ⟨fstFromTau t⟩

/-- **The exact conversion, and the reason it is not a correction factor.**
`Hudson = 2G/(1 + G)`. It is a Möbius map and not a constant multiple, so there is no
number by which a Nei estimate can be scaled to give a Hudson one: the ratio between them
moves with the value. Measured ratios across one design were 0.62, 0.60, 0.68 and 0.81.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def hudsonOfNei (g : NeiFst) : HudsonFst :=
  ⟨2 * g.value / (1 + g.value)⟩

/-- **The two agree only at the endpoints.** `2G/(1+G) = G` forces `G = 0` or `G = 1`, so
anywhere a population is partially differentiated -- which is every case of interest --
the two estimators disagree. -/
theorem hudsonOfNei_eq_iff (g : NeiFst) (h : 1 + g.value ≠ 0) :
    (hudsonOfNei g).value = g.value ↔ g.value = 0 ∨ g.value = 1 := by
  show 2 * g.value / (1 + g.value) = g.value ↔ _
  rw [div_eq_iff h]
  constructor
  · intro hg
    have hz : g.value * (g.value - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  · rintro (h0 | h0) <;> rw [h0] <;> ring

/-- **A scaled coalescence time reads as a Hudson value, and the wrapper preserves it.**
The point of `hudsonFromTau` is that `τ/(1+τ)` cannot be handed to something expecting a
Nei estimate; this says the number inside is the one `fstFromTau` computes, so wrapping
costs nothing but the type. -/
@[simp] theorem hudsonFromTau_value (t : Tau) :
    (hudsonFromTau t).value = fstFromTau t := rfl

/-- **A witness that the gap is real and sizeable.** At a Nei `G_ST` of `1/2` the Hudson
value is `2/3`: a 33% difference, at a differentiation level ordinary human population
pairs sit near. Stated as a value because a monotonicity or an inequality would be
satisfied by an estimator that agreed to within a percent. -/
theorem hudsonOfNei_at_half : (hudsonOfNei ⟨1 / 2⟩).value = 2 / 3 := by
  unfold hudsonOfNei; norm_num

/-- Hardy--Weinberg heterozygosity, `2p(1-p)`.

Two names in the corpus carry this body -- `hweHeterozygosity` and
`genotypeVarianceHWE` -- and they are NOT one quantity: the first is the probability a
diploid is heterozygous, the second the variance of a `0/1/2` dosage. Under
Hardy--Weinberg those numbers coincide, and that coincidence is a fact about the
proportions rather than about the arithmetic. Both call this.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def hweHeterozygosity (p : ℝ) : ℝ := ploidy * p * (1 - p)

/-- **The maximum is at `p = 1/2`, where it is `1/2`.** The value that fixes the
coefficient: a body carrying any other multiple is still positive, still symmetric about
one half, and still vanishes at the boundaries. -/
theorem hweHeterozygosity_at_half : hweHeterozygosity (1 / 2) = 1 / 2 := by
  unfold hweHeterozygosity ploidy; norm_num

/-- **Symmetric under relabelling the allele.** Which allele is called the reference is a
convention, and a heterozygosity that changed when it flipped would be reporting the
convention. -/
theorem hweHeterozygosity_allele_swap (p : ℝ) :
    hweHeterozygosity (1 - p) = hweHeterozygosity p := by
  unfold hweHeterozygosity; ring

/-! ## The two estimators on allele frequencies

`hudsonFromTau` and `hudsonOfNei` above wrap the two estimators as one-field types and
relate them at that level.  What follows is the same pair written on the arguments the
data actually supplies -- a pair of subgroup allele frequencies -- together with the
witnesses that they are two functions and not two spellings of one.

These arrived here from `Program.Conventions`, which is where the corpus put statements it
could only make after importing everything.  None of them needed that.  `neiGst`,
`hudsonFst`, `meanAlleleFreq` and `betweenSubgroupVariance` are built from `ploidy`,
`midpoint` and `halfDiffSq` and from nothing else, so their home is here, below the
subsystems that consume them, and a module wanting Hudson's `F_ST` no longer has to import
the audit layer at the top of the graph to get it. -/

/-- Mean allele frequency across two subgroups of equal weight.

    Empirical status: NOT AN EMPIRICAL CLAIM. This file exists to fix conventions, and the
    equal-weight arithmetic mean is one: `(p₁ + p₂)/2` DEFINES what "the mean frequency"
    denotes downstream rather than predicting anything a sample could refute. The empirical
    consequence of choosing equal weights over sample-size weights shows up in the `F_ST`
    that consumes it, and the note below records that `effectiveSymmetricMigration` must
    share this convention or the two disagree. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ :=
  midpoint p₁ p₂

/-- **The mean allele frequency is unweighted, pinned.** The identity with the symmetric
migration map constrains the two definitions jointly. Taken alone: a fixed and an absent allele
average to one half, which fixes the two-population mean as the arithmetic midpoint. -/
theorem meanAlleleFreq_fixed_and_absent :
    meanAlleleFreq 0 1 = 1 / 2 := by
  unfold meanAlleleFreq midpoint
  norm_num

/-- **Nei's `G_ST`, explicitly distinguished from Hudson's `F_ST`.** One minus the ratio
of mean within-subgroup heterozygosity to TOTAL heterozygosity is the
definition of `G_ST`. Hudson's `F_ST`
divides by the BETWEEN-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`, not by
the total-pool `2·p̄·(1-p̄)`. The two denominators differ by exactly
`(p₁-p₂)²/2`, so THE DENOMINATORS agree iff `p₁ = p₂`, and the two ESTIMATORS
agree iff `G_ST = 0` or `G_ST = 1` -- that is, only where the differentiation
is degenerate.

**They agree when `p₁ = p₂`, and NOT when `p̄ = 1/2`**; the second is a tempting
disjunct and it is false in both readings.
The denominators differ by `(p₁-p₂)²/2`, which does not vanish at `p̄ = 1/2`;
and by the corpus's own `hudsonFst_eq_of_neiGst`, Hudson `= 2G/(1+G)`,
which equals `G` only at `G = 0` or `G = 1`. So there is no interior
`p̄ = 1/2` slice on which the two coincide. Witness, on `p̄ = 1/2` exactly:
at `p₁ = 0.9, p₂ = 0.1` the Nei denominator is `1`, `G_ST = 0.64`, and Hudson
is `0.64/0.82 = 0.7805` -- a ratio of `1.22`. Nearer the middle it is worse:
`1.995` at `(0.525, 0.475)`, `1.923` at `(0.6, 0.4)`, `1.724` at `(0.7, 0.3)`.

The error is worth naming because it is cheap to half-check and wrong: at
`p̄ = 1/2` the Nei denominator `4·p̄·(1-p̄)` is exactly `1`, which feels like it
should settle the comparison and does not -- it makes `G_ST = (p₁-p₂)²`, while
Hudson still divides by `1 - 2p₁p₂`. A DENOMINATOR COINCIDENCE IS NOT AN
ESTIMATOR COINCIDENCE, and here there was not even a denominator coincidence.
The claim had propagated into three `checks.py` can-fail clauses and out of the
corpus into status reporting before anyone tested the slice it names.

    Derivation, since this is decidable without any simulation. With
    `d = p₁ - p₂` and `p̄ = (p₁+p₂)/2`,
    `H_T - H_S = 2p̄(1-p̄) - (p₁(1-p₁) + p₂(1-p₂)) = d²/2`, so this body is
    `d² / (4·p̄·(1-p̄))`, which is Nei's `G_ST` and is also exactly the body of
    `PopulationGeneticsFoundations.neiGstFromFrequencies` --
    `neiGstFromFrequencies_eq_neiGst` below proves the two agree, and what
    it actually proves is that both are Nei.
    Hudson's is `d² / (p₁ + p₂ - 2p₁p₂)`; `hudsonFst` states it and
    `hudsonFst_eq_of_neiGst` gives the exact conversion. At `p₁ = 0.2`,
    `p₂ = 0.6` this body gives `0.1667` where Hudson gives `0.2857`, the
    +71.4% the differential tier measured against an independent
    implementation.

    The old `hudsonFst` name on the Nei body was removed rather than retained as
    a compatibility alias: that alias would preserve the biological category
    error. The genuine Hudson body now owns `hudsonFst`. Read every `neiGst` in the
    *contrast-normalization* chain --
    including `four_neiGst_eq_standardizedContrastVariance` -- as Nei's `G_ST`.
    The algebra is unaffected: `4·G_ST` is the standardized allele-frequency
    contrast variance for THIS body. It is not the empirically calibrated BBP
    spike. That law uses genuine Hudson `F_ST` and is named `hudsonBbpSpike`
    below. At weak differentiation the latter is almost twice
    `neiContrastSpike`; silently exchanging them is therefore a biologically
    material error, not a harmless change of notation.

    **There is no exception at `p̄ = 1/2`. Do not add one.** The factor does not
    vanish there: measured ratios along that exact slice are `1.995`, `1.923`,
    `1.724`, `1.220` -- monotone in `|p₁ - p₂|` and never reaching `1`. The
    identity in this file settles it without any measurement:
    `hudsonFst_eq_of_neiGst` gives `Hudson = 2G/(1+G)`, which equals `G` only at
    `G = 0` or `G = 1`. `neiGst_ne_hudsonFst_at_mean_half` certifies it at
    `(9/10, 1/10)` -- `p̄ = 1/2` exactly, ratio `50/41` -- and exists to stop an
    "except at `p̄ = 1/2`" caveat being reintroduced.

    Note which witness does the work: `neiGst_ne_hudsonFst` sits at `p̄ = 2/5`,
    OUTSIDE that slice, and cannot refute a claim about it. A witness outside an
    exception never refutes the exception.

    **Numerical warning -- this body must not be evaluated as written.** It is
    `1` minus a ratio that tends to `1` as the two populations become similar,
    so its floating-point relative error is the machine epsilon divided by the
    answer. Between human populations `G_ST` is `O(10⁻³)` genome-wide and much
    smaller at an individual variant, which is exactly the regime that has no
    digits left. Measured float64 against a 60-digit reference over
    `p₂ = p₁ + δ` for `p₁ ∈ {0.01, 0.1, 0.3, 0.5}` and `δ` from `10⁻²` down to
    `10⁻¹⁴`, arguments rounded to float64 FIRST so input representation cannot
    be charged to the formula: **36 of 52 cells exceed 1e-6 relative error,
    worst 9.3·10¹¹** -- the returned `G_ST` is wrong by eleven orders of
    magnitude, and at `δ ≲ 10⁻⁸` it is pure rounding noise of either sign.

    `PopulationGeneticsFoundations.neiGstFromFrequencies` is the SAME quantity
    written as `(p₁-p₂)² / (4 p̄ (1-p̄))`, with the cancellation done by hand;
    `neiGstFromFrequencies_eq_neiGst` proves they are equal over `ℝ`. On the
    same 52 cells that body gives **0 over tolerance, worst 1.9·10⁻¹⁶**. The
    equality theorem is what makes the substitution safe and it is also what
    made the difference invisible: two provably equal bodies are not two equally
    usable programs. Evaluate `neiGstFromFrequencies`; read `neiGst` as the
    definition of what is being computed.

    Metamorphic relations this body satisfies, all exactly:
    population relabelling `(p₁, p₂) ↦ (p₂, p₁)`, invariant;
    reference/alternate allele swap `(p₁, p₂) ↦ (1-p₁, 1-p₂)`, invariant
    (`neiGst_allele_swap`); and `p₁ = p₂`, zero.

    Empirical status: CONVENTION PINNED (Nei's `G_ST`; the name was corrected with it). -/
noncomputable def neiGst (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 /
    (ploidy ^ 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- **The textbook spelling, kept as a theorem rather than as the body.**

`G_ST = 1 - H_S/H_T` is how the quantity is defined in the literature and it is
what the name means; it is not how it should be computed. As `p₁ → p₂` the ratio
tends to `1` and `G_ST` is whatever survives the
subtraction, so its float64 relative error is machine epsilon divided by the
answer. Measured float64 against a 60-digit reference over `p₂ = p₁ + δ` for
`p₁ ∈ {0.01, 0.1, 0.3, 0.5}` and `δ` from `10⁻²` to `10⁻¹⁴`, arguments rounded to
float64 first: **36 of 52 cells over 1e-6 relative error, worst 9.3·10¹¹** for
this form, against **0 of 52, worst 1.9·10⁻¹⁶** for the body above. Human `G_ST`
is `O(10⁻³)` genome-wide and smaller per variant, so the failing region was the
use case.

The hypothesis is the one point at which the two spellings genuinely differ --
see `neiGst_at_zero_mean_heterozygosity`. -/
theorem neiGst_eq_oneMinusRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGst p₁ p₂ =
      1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
        (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold neiGst ploidy
  field_simp
  unfold meanAlleleFreq midpoint
  ring

/-- **Two identical monomorphic populations are not differentiated.**

Two populations fixed for the same allele could not be more alike, and the
statistic reports `0`. This is a real value, not a junk branch: the numerator
`(p₁ - p₂)²` vanishes with the denominator, so the cancellation-free body is
defined here by the same algebra that makes it stable elsewhere. Under the
`1 - H_S/H_T` spelling the ratio divides by zero, Mathlib returns `0`, and the
statistic reads `1` -- COMPLETE differentiation -- so that spelling requires
consumers to exclude the point. The stable spelling and the correct boundary are
the same spelling. -/
theorem neiGst_at_zero_mean_heterozygosity (p₁ p₂ : ℝ)
    (hzero : ploidy ^ 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) = 0) :
    neiGst p₁ p₂ = 0 := by
  unfold neiGst
  rw [hzero, div_zero]

/-- **Hudson's `F_ST` for two subgroups, parametric limit** (Bhatia, Patterson,
Sankararaman & Price 2013, eq. 10, at infinite sample size):

  `F_ST = (p₁ - p₂)² / (p₁(1-p₂) + p₂(1-p₁))`

The denominator is the probability that two genes drawn from DIFFERENT
subgroups differ -- the between-subgroup heterozygosity -- which is what makes
this a ratio of averages and what distinguishes it from Nei's `G_ST`. Added
alongside `neiGst` rather than replacing it, because the corpus's arithmetic
is Nei's throughout and changing the arithmetic would silently move every
downstream number; what was missing was a name for the quantity the corpus kept
saying it meant.

    Empirical status: VALIDATED -- matches `validation/differential/refs.fst_hudson`, which
    is checked against scikit-allel. -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 / (p₁ * (1 - p₂) + p₂ * (1 - p₁))

/-- **hudsonFst where its denominator vanishes, named.** The guard `p₁ * (1 - p₂) + p₂ * (1 - p₁)`
is zero at `p₁ = 0`, `p₂ = 0`. Two populations both fixed for the reference allele have no
polymorphism to partition. Lean returns `0` there rather than the value the modelled quantity
takes, and no type error marks the point. Consumers must require `p₁ * (1 - p₂) + p₂ * (1 - p₁)
≠ 0`. -/
theorem hudsonFst_at_p0p0_is_junk :
    hudsonFst 0 0 = 0 := by
  unfold hudsonFst
  norm_num

/-- **Hudson's `F_ST` does not care which population is called first.** Both the squared
frequency difference and the denominator `p₁ + p₂ - 2p₁p₂` are symmetric, so the statistic is
too. A body that broke this would be measuring a directed quantity under a symmetric name. -/
theorem hudsonFst_symm (p₁ p₂ : ℝ) : hudsonFst p₁ p₂ = hudsonFst p₂ p₁ := by
  unfold hudsonFst; ring_nf

/-- Two populations at the same frequency are not differentiated. -/
theorem hudsonFst_self (p : ℝ) : hudsonFst p p = 0 := by
  unfold hudsonFst; simp

/-- **Nei's `G_ST` is invariant under the reference/alternate allele swap.** Both the
within-population heterozygosity `p(1-p)` and the mean-frequency heterozygosity are
even about `p = 1/2`, so relabelling the alleles cannot move the statistic. -/
theorem neiGst_allele_swap (p₁ p₂ : ℝ) :
    neiGst (1 - p₁) (1 - p₂) = neiGst p₁ p₂ := by
  unfold neiGst meanAlleleFreq midpoint
  have hnum : ((1 - p₁) - (1 - p₂)) ^ 2 = (p₁ - p₂) ^ 2 := by ring
  have hden : ploidy ^ 2 * ((1 - p₁ + (1 - p₂)) / 2) * (1 - (1 - p₁ + (1 - p₂)) / 2)
      = ploidy ^ 2 * ((p₁ + p₂) / 2) * (1 - (p₁ + p₂) / 2) := by ring
  rw [hnum, hden]

/-- **Hudson's `F_ST` is invariant under the reference/alternate allele swap.** The
numerator is a squared difference and the between-population denominator
`p₁(1-p₂) + p₂(1-p₁)` is the probability that two genes drawn from different demes
differ, which is a statement about disagreement and so cannot depend on the labels. -/
theorem hudsonFst_allele_swap (p₁ p₂ : ℝ) :
    hudsonFst (1 - p₁) (1 - p₂) = hudsonFst p₁ p₂ := by
  unfold hudsonFst
  have hnum : ((1 - p₁) - (1 - p₂)) ^ 2 = (p₁ - p₂) ^ 2 := by ring
  have hden : (1 - p₁) * (1 - (1 - p₂)) + (1 - p₂) * (1 - (1 - p₁))
      = p₁ * (1 - p₂) + p₂ * (1 - p₁) := by ring
  rw [hnum, hden]

/-- **The exact conversion between the two conventions**, which is what turns
"they disagree by about 72% somewhere in this range" into a statement that
holds everywhere: `F_ST^Hudson = 2·G_ST / (1 + G_ST)`. Note it is not a
constant factor -- the discrepancy is 2× as `G_ST → 0` and vanishes as
`G_ST → 1` -- so no recalibration constant can absorb a convention mix-up.

WHAT IS AND IS NOT NEW HERE, stated so nobody reports the wrong half. THAT NEI
AND HUDSON DISAGREE IS TEXTBOOK: Bhatia, Patterson, Sankararaman & Price (2013)
is the standard reference, it is cited on `hudsonFst` above, and the
disagreement is not a finding of this corpus. What belongs to this development
is narrower and worth exactly what it is: the algebraic bridge between them
written down explicitly, MACHINE-CHECKED in Lean rather than asserted, and then
confirmed numerically against simulation to the last reported digit. A
well-known fact and a proved identity are different objects, and only the
second is ours.

    Empirical status: VALIDATED, and it is currently the cleanest
    theory-to-measurement match in this corpus. Inverting the identity to
    `G = H/(2 - H)` predicts the Nei estimate from the Hudson estimate on the
    same simulated data at **0.00% relative error across all eight cells**,
    while Hudson itself tracks the true `F_ST` (`0.0501` measured against
    `0.050` simulated). The identity is exact in practice as well as in Lean,
    which is the strongest form this kind of claim can take: a conversion that
    is proved and then found to hold to the last reported digit on data it was
    not fitted to.

    Power: across the eight frequency cells of
    `validation/empirical/differential/cluster/fam_fst_allel_crosscheck.py`
    (`(p₁, p₂)` from `(0.70, 0.75)` to `(0.10, 0.90)`) the predicted Nei
    estimate spans `0.0031` to `0.6400` and the Hudson estimate `0.0063` to
    `0.7805`, so the ratio between the conventions runs from `2.0` at the
    small-divergence end to `1.22` at the large one. A conversion off by any
    constant factor, and any conversion linear in `G`, separates on that
    design. -/
theorem hudsonFst_eq_of_neiGst (p₁ p₂ : ℝ)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonFst p₁ p₂ = 2 * neiGst p₁ p₂ / (1 + neiGst p₁ p₂) := by
  have hne : p₁ * (1 - p₂) + p₂ * (1 - p₁) ≠ 0 := ne_of_gt hpos
  have hmean : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul hbar
  have hcomp : 1 - meanAlleleFreq p₁ p₂ ≠ 0 := right_ne_zero_of_mul hbar
  have hD : 2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hmean) hcomp
  have hlink :
      (1 + neiGst p₁ p₂) *
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) =
        p₁ * (1 - p₂) + p₂ * (1 - p₁) := by
    unfold neiGst ploidy
    field_simp [hD]
    unfold meanAlleleFreq midpoint
    ring
  have htwo :
      2 * neiGst p₁ p₂ =
        (p₁ - p₂) ^ 2 /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
    unfold neiGst ploidy
    field_simp [hD]
  have hone :
      1 + neiGst p₁ p₂ =
        (p₁ * (1 - p₂) + p₂ * (1 - p₁)) /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) :=
    (eq_div_iff hD).2 hlink
  have hquot :
      (p₁ * (1 - p₂) + p₂ * (1 - p₁)) /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) ≠ 0 :=
    div_ne_zero hne hD
  unfold hudsonFst
  rw [htwo, hone]
  field_simp [hne, hD, hquot]

/-- **Witness that the two estimators are different functions**, not two
spellings of one. Without an exhibited point the conflation can be
reintroduced by anyone who reads the `neiGst` name and believes it. -/
theorem neiGst_ne_hudsonFst :
    neiGst (1/5) (3/5) ≠ hudsonFst (1/5) (3/5) := by
  unfold neiGst hudsonFst ploidy meanAlleleFreq midpoint
  norm_num

/-- **A witness ON the `p̄ = 1/2` slice**, where the estimators are sometimes
claimed to agree. They do not.

`p₁ = 9/10, p₂ = 1/10` has `p̄ = 1/2` exactly. `neiGst` (Nei's `G_ST`) is
`16/25` and `hudsonFst` is `(16/25)/(41/50)`, a ratio of `50/41 ≈ 1.22`.
The false claim is therefore refuted at a point, not merely argued against:
`p̄ = 1/2` makes the Nei denominator `1` and nothing more. Stated separately
from `neiGst_ne_hudsonFst` because that witness sits at `p̄ = 2/5` and
so cannot exclude the slice that was actually claimed. -/
theorem neiGst_ne_hudsonFst_at_mean_half :
    neiGst (9/10) (1/10) ≠ hudsonFst (9/10) (1/10) := by
  unfold neiGst hudsonFst ploidy meanAlleleFreq midpoint
  norm_num

/-- **NO FIXED FACTOR CONVERTS NEI'S `G_ST` INTO HUDSON'S `F_ST`.**

This closes the fork rather than documenting it. The two witnesses above exhibit
points where the estimators disagree, and `hudsonFst_eq_of_neiGst` gives the exact
map `Hudson = 2·G/(1 + G)`. Neither shuts the door this theorem shuts: a reader
who accepts that the two differ can still believe the difference is a calibration
constant to be divided out, and that belief is what a factor-of-two-to-four error
looks like from the inside.

There is no such constant, anywhere on the interior of the frequency range, and
the witnesses say why. The map `Hudson = 2G/(1 + G)` has slope `2` at `G = 0` and
slope `1` at `G = 1`, so the RATIO moves with the differentiation: at
`p₁ = 1/5, p₂ = 3/5` it is `12/7`, and at `p₁ = 9/10, p₂ = 1/10` it is `50/41`.

This is the machine-checked form of what `PopulationGeneticsFoundations.neiFst`
records in prose -- that the measured ratio runs `0.60, 0.60, 0.68, 0.82` across a
`τ` sweep, so no rescaling reconciles the two. A docstring paragraph can be read
past; a theorem cannot. After this, substituting one estimator for the other is
not a judgement call about tolerable error, it is a claim this file refutes.

    Empirical status: NOT AN EMPIRICAL CLAIM -- an arithmetic fact about two
    definitions, with both witnesses exhibited rather than sampled. -/
theorem no_constant_scales_neiGst_to_hudsonFst :
    ¬ ∃ c : ℝ, ∀ p₁ p₂ : ℝ, 0 < p₁ → p₁ < 1 → 0 < p₂ → p₂ < 1 →
      hudsonFst p₁ p₂ = c * neiGst p₁ p₂ := by
  rintro ⟨c, hc⟩
  have h₁ := hc (1/5) (3/5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hc (9/10) (1/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold neiGst hudsonFst ploidy meanAlleleFreq midpoint at h₁ h₂
  norm_num at h₁ h₂
  linarith

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ :=
  halfDiffSq p₁ p₂

/-- **The between-subgroup variance's normalisation, pinned.** The identity with the fair
two-point variance constrains the two definitions jointly and leaves a shared wrong factor free.
Two subgroups at the extremes of the frequency range have between-group variance one quarter --
the variance of a fair coin -- not one. -/
theorem betweenSubgroupVariance_extremes :
    betweenSubgroupVariance 1 0 = 1 / 4 := by
  unfold betweenSubgroupVariance halfDiffSq
  norm_num

/-- **Cross-check: the heterozygosity form and the variance form of `F_ST`
agree.** The corpus contained both shapes and never related them. -/
theorem neiGst_eq_varianceRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGst p₁ p₂ =
      betweenSubgroupVariance p₁ p₂ /
        (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold neiGst betweenSubgroupVariance ploidy halfDiffSq
  field_simp
  ring

/-- **The allele-frequency contrast constant is forced, not chosen.**

Four times `neiGst` -- which is Nei's `G_ST`, see its docstring; the `4` is
derived for THAT quantity and is not an empirical constant for Hudson's
estimator -- is exactly the variance of the standardized allele-frequency
contrast. The BBP inversion that recovered `3.9920 ± 0.0045` used genuine
Hudson `F_ST`; it validates `hudsonBbpSpike`, not this identity. Keeping those
two facts separate is the point of the named specializations below. -/
theorem four_neiGst_eq_standardizedContrastVariance (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    4 * neiGst p₁ p₂ =
      (p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  rw [neiGst_eq_varianceRatio p₁ p₂ h]
  unfold betweenSubgroupVariance halfDiffSq
  field_simp

/-- **Nei's `G_ST` between a frequency and its fold is the squared contrast.** At
`p₂ = 1 - p` the mean frequency is `1/2`, the total heterozygosity `ploidy · p̄ (1 - p̄)`
is `1/2`, and `G_ST` collapses to `(1 - ploidy · p)²`. This is the only place the
denominator's `ploidy` is visible as a number, and it is what makes the next theorem an
identity rather than a proportionality. -/
theorem neiGst_at_fold (p : ℝ) : neiGst p (1 - p) = (1 - ploidy * p) ^ 2 := by
  unfold neiGst meanAlleleFreq ploidy midpoint; ring

end Descent.Core
