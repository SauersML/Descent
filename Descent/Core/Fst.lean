/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Ratios
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

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
a census. -/

/-- Ploidy. Two, because every population in this corpus is diploid.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def ploidy : ℝ := 2

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
  have hEq : islandDemeCorrection =ᶠ[atTop] fun d : ℝ => 1 + 1 / (d - 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with d hd
    have h : d - 1 ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; exact absurd hc (by linarith)
    unfold islandDemeCorrection ratio
    field_simp
    ring
  rw [tendsto_congr' hEq]
  have hsub : Tendsto (fun d : ℝ => d - 1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id).congr
      (fun x => by show x + -1 = x - 1; ring)
  have h : Tendsto (fun d : ℝ => 1 / (d - 1)) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp hsub).congr (fun x => (one_div (x - 1)).symm)
  simpa using tendsto_const_nhds.add h

/-! ### The master equilibrium -/

/-- Total scaled flow into a deme, `4 Ne m (d/(d-1)) + 4 Ne μ`.

Naming it separates the two questions the equilibrium answers: what counts as flow, and
how flow becomes a differentiation. Every member of the lattice below differs only in
what it puts here.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def scaledFlow (Ne m μ nDemes : ℝ) : ℝ :=
  scaledMigrationRate Ne m * islandDemeCorrection nDemes + scaledMutationRate Ne μ

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
noncomputable def fstIslandEquilibrium (Ne m μ nDemes : ℝ) : ℝ :=
  fstFromFlow (scaledFlow Ne m μ nDemes)

/-- **The master, in the raw coordinates the subsystem modules wrote it in.** This is the
bridge that lets `fstIslandEquilibriumFiniteDemes` be a wrapper rather than a copy. -/
theorem fstIslandEquilibrium_eq (Ne m μ nDemes : ℝ) :
    fstIslandEquilibrium Ne m μ nDemes
      = 1 / (1 + 4 * Ne * m * islandDemeCorrection nDemes + 4 * Ne * μ) := by
  unfold fstIslandEquilibrium fstFromFlow scaledFlow
  rw [scaledMigrationRate_eq, scaledMutationRate_eq]
  ring_nf

/-- **The equilibrium is a saturation of the total scaled flow.** `F_ST = 1/(1 + x)` is
`1 - saturation x`, so the whole family lives on one curve and the only thing that
distinguishes its members is what they put into `x`. This is the statement that makes
the lattice below a lattice rather than a list. -/
theorem fstIslandEquilibrium_eq_complement_saturation (Ne m μ nDemes : ℝ)
    (h : 1 + scaledFlow Ne m μ nDemes ≠ 0) :
    fstIslandEquilibrium Ne m μ nDemes
      = complement (saturation (scaledFlow Ne m μ nDemes)) := by
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
    fstIslandEquilibrium Ne m μ nDemes = 1 / (1 + 4 * Ne * m + 4 * Ne * μ) := by
  rw [fstIslandEquilibrium_eq, hd]; ring_nf

/-- **No mutation: `μ = 0`.** `fstMigrationDriftEquilibrium` is the many-deme master with the mutation term dropped. Migration alone. -/
theorem fstIslandEquilibrium_no_mutation (Ne m nDemes : ℝ)
    (hd : islandDemeCorrection nDemes = 1) :
    fstIslandEquilibrium Ne m 0 nDemes = 1 / (1 + 4 * Ne * m) := by
  rw [fstIslandEquilibrium_manyDemes Ne m 0 nDemes hd]; ring_nf

/-- **No migration: `m = 0`.** `fstMutationDriftEquilibrium θ` is the master with the
migration term dropped and `θ = 4 Ne μ` substituted -- the pure mutation-drift balance a
single isolated population reaches. -/
theorem fstIslandEquilibrium_no_migration (Ne μ nDemes : ℝ) :
    fstIslandEquilibrium Ne 0 μ nDemes = 1 / (1 + scaledMutationRate Ne μ) := by
  unfold fstIslandEquilibrium fstFromFlow scaledFlow scaledMigrationRate
  ring_nf

/-- **The `θ` reparameterisation.** The scaled coordinates are not a different model:
`1/(1 + θ)` at `θ = 4 Ne μ` is the master with no migration. Written out because the
corpus had `fstMutationDriftEquilibrium` taking a bare `θ` in one module and
`fstIslandEquilibriumFiniteDemes` taking `(Ne, μ)` in another, with nothing relating the
two spellings. -/
theorem fstIslandEquilibrium_no_migration_scaled (Ne μ nDemes θ : ℝ)
    (hθ : θ = scaledMutationRate Ne μ) :
    fstIslandEquilibrium Ne 0 μ nDemes = 1 / (1 + θ) := by
  rw [fstIslandEquilibrium_no_migration, hθ]

/-- **The structure-field coordinates, `1/(1 + θ + 2M)`.** `DGP.fstEquilibrium` writes
the master with `θ = 4 Ne μ` and `M = 2 Ne m`, so `2M = 4 Ne m` is the migration term at
a deme correction of one. The factor of two is where the two parameterisations differ,
and it is the whole content of this theorem: `bigM` is `2 Ne m`, NOT `4 Ne m`, so reading
`M` for the scaled migration rate doubles the flow. -/
theorem fstIslandEquilibrium_structure_coords (Ne m μ nDemes θ bigM : ℝ)
    (hd : islandDemeCorrection nDemes = 1)
    (hθ : θ = 4 * Ne * μ) (hM : bigM = 2 * Ne * m) :
    fstIslandEquilibrium Ne m μ nDemes = 1 / (1 + θ + 2 * bigM) := by
  rw [fstIslandEquilibrium_manyDemes Ne m μ nDemes hd, hθ, hM]; ring_nf

/-! ### `F_ST` from a scaled coalescence time

The other coordinate the corpus works in. `τ/(1 + τ)` is `saturation`, and every result
written in it is a Hudson `F_ST`. -/

/-- `F_ST` from a scaled coalescence time, `τ / (1 + τ)`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def fstFromTau (tau : ℝ) : ℝ := saturation tau

/-- **The split law and the equilibrium law are complementary readings of one curve.**
`F_ST = τ/(1+τ)` and `F_ST = 1/(1 + x)` are `saturation` and its complement, so a result
stated in one coordinate transfers to the other by reading `τ = 1/x`. Stated because the
corpus writes both and a reader meeting them in different files has no reason to expect
they are the same object. -/
theorem fstFromTau_add_equilibrium (x : ℝ) (h : 1 + x ≠ 0) :
    fstFromTau x + 1 / (1 + x) = 1 := by
  unfold fstFromTau saturation
  field_simp
  ring

/-- **The equilibrium law and the split law are complements.** `fstFromFlow x` and
`fstFromTau x` sum to one away from the pole, so a result in either coordinate transfers
to the other. -/
theorem fstFromFlow_add_fstFromTau (x : ℝ) (h : 1 + x ≠ 0) :
    fstFromFlow x + fstFromTau x = 1 := by
  unfold fstFromFlow
  rw [add_comm]
  exact fstFromTau_add_equilibrium x h

/-- **`F_ST` from a scaled time lands in the unit interval.** -/
theorem fstFromTau_mem_unit (tau : ℝ) (h : 0 ≤ tau) :
    0 ≤ fstFromTau tau ∧ fstFromTau tau ≤ 1 :=
  saturation_mem_unit tau h

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
noncomputable def hudsonFromTau (tau : ℝ) : HudsonFst := ⟨fstFromTau tau⟩

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
@[simp] theorem hudsonFromTau_value (tau : ℝ) :
    (hudsonFromTau tau).value = fstFromTau tau := rfl

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

end Descent.Core
