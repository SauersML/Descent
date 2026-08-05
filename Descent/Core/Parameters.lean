/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Fst

/-!
# Core: one population-genetic parameter record

**Depth 1. Imports `Core.Fst` and `Core.Ratios`, and nothing else from this corpus.**

## What this replaces

The corpus carried two parameter records with the same fields, the same positivity
proofs, and different spellings, in two modules that do not import each other:

    EvolutionaryParameters          (PopGen.DGP)          Ne, mu,  mig, t_div, recomb, V_A
    GenerationalPopGenParameters    (Portability.Drift)   Ne, μ,   mig,        recomb, V_A

`mu` against `μ` is the whole difference apart from the divergence time, and a difference
of spelling is not a difference of quantity. Two records meant that a constraint added to
one -- a bound on the migration rate, a tightened positivity -- reached the other only if
someone noticed.

`t_div` is carried here rather than dropped. A model with no divergence time is this
record at `t_div = 0`, which is a value the field can take, and `PopGenParameters.atOrigin`
below names that reading so a caller supplying zero is saying something rather than
filling a slot.

## Why the proofs are fields

Each rate carries its admissibility as a field rather than as a hypothesis at each use
site. `recomb_le_half` is the one that earns it: a recombination fraction above `1/2` is
not a rare edge case but a sign that a caller has passed a rate where a fraction was
wanted, and putting it in the record means that mistake cannot be made once rather than
having to be excluded at each theorem.

## Empirical status

None. A parameter record asserts nothing; what carries a status is a law computed from
it.
-/

namespace Descent.Core

/-- **The population-genetic parameters of a two-population history.**

One record, one spelling. `t_div` is the divergence time in generations; a model that
does not carry one sets it to zero and `atOrigin` says so. -/
structure PopGenParameters where
  /-- Effective population size, the harmonic mean over the history. -/
  Ne : ℝ
  /-- Mutation rate per generation. Spelled `mu`, never `μ`. -/
  mu : ℝ
  /-- Symmetric migration rate per generation. -/
  mig : ℝ
  /-- Divergence time in generations; zero when the model carries none. -/
  t_div : ℝ
  /-- Recombination rate between the linked loci under consideration. -/
  recomb : ℝ
  /-- Additive genetic variance in the ancestral population. -/
  V_A : ℝ
  /-- A population has members. -/
  Ne_pos : 0 < Ne
  /-- Mutation does not run backwards. -/
  mu_nonneg : 0 ≤ mu
  /-- Migration does not run backwards. -/
  mig_nonneg : 0 ≤ mig
  /-- Time does not run backwards. -/
  t_div_nonneg : 0 ≤ t_div
  /-- Recombination does not run backwards. -/
  recomb_nonneg : 0 ≤ recomb
  /-- A recombination FRACTION, so at most one half: two loci cannot be less than
  independently assorted. -/
  recomb_le_half : recomb ≤ 1 / 2
  /-- There is additive variance for a score to capture. -/
  V_A_pos : 0 < V_A

namespace PopGenParameters

/-- **The record is inhabited**, at a standard human-scale setting: `Nₑ = 1000`,
`μ = 10⁻⁵` per generation, `m = 10⁻³`, `t = 2000` generations, `r = 10⁻²`, additive
variance `1`.

A theorem quantified over an uninhabited structure is true and empty. Every value here
is strictly inside its constraint -- no rate is zero and the recombination fraction is
well below the free-assortment boundary -- so nothing downstream reads a degenerate
point. -/
noncomputable def witness : PopGenParameters where
  Ne := 1000
  mu := 1 / 100000
  mig := 1 / 1000
  t_div := 2000
  recomb := 1 / 100
  V_A := 1
  Ne_pos := by norm_num
  mu_nonneg := by norm_num
  mig_nonneg := by norm_num
  t_div_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num

/-- **A history with no divergence.** The predicate a model without a split satisfies,
named so that `t_div = 0` reads as a claim rather than as an unfilled field. -/
def atOrigin (p : PopGenParameters) : Prop := p.t_div = 0

/-- Scaled mutation rate, `θ = 4 Nₑ μ`, in this record's coordinates. -/
noncomputable def theta (p : PopGenParameters) : ℝ := scaledMutationRate p.Ne p.mu

/-- Scaled migration rate in this record's coordinates, `M = 4 Nₑ m`.

Both modules that carried a parameter record defined `bigM` this way, so this is the
corpus's convention and not a choice made here. -/
noncomputable def bigM (p : PopGenParameters) : ℝ := scaledMigrationRate p.Ne p.mig

/-- **`M` is the scaled migration rate, not half of it.** -/
theorem bigM_eq_scaledMigrationRate (p : PopGenParameters) :
    p.bigM = scaledMigrationRate p.Ne p.mig := rfl

/-- Both scaled rates are non-negative, which every equilibrium below needs. -/
theorem theta_nonneg (p : PopGenParameters) : 0 ≤ p.theta := by
  unfold theta
  rw [scaledMutationRate_eq]
  have := p.Ne_pos
  have := p.mu_nonneg
  positivity

/-- Both scaled rates are non-negative, which every equilibrium below needs. -/
theorem bigM_nonneg (p : PopGenParameters) : 0 ≤ p.bigM := by
  unfold bigM
  rw [scaledMigrationRate_eq]
  have := p.Ne_pos
  have := p.mig_nonneg
  positivity

/-- **Equilibrium `F_ST` in this record's coordinates**, `1/(1 + θ + 2M)`.

This is `Core.fstFromFlow` applied to the total scaled flow, so it is the same law as
`fstIslandEquilibrium` at a many-deme correction and not a second formula. -/
noncomputable def fstEquilibrium (p : PopGenParameters) : ℝ :=
  fstFromFlow (p.theta + 2 * p.bigM)

/-- **The record's equilibrium IS the island master -- at exactly two demes.**

`fstEquilibrium` is `1/(1 + θ + 2M)` with `M = 4 Nₑ m`, so its migration flow is
`8 Nₑ m`, while `fstIslandEquilibrium` carries `4 Nₑ m · d/(d-1)`. Those agree precisely
when `d/(d-1) = 2`, which is `d = 2`.

This is worth stating rather than assuming, in both directions. The corpus wrote the two
laws in two modules that do not import each other, both called "equilibrium `F_ST`", with
nothing relating them -- and the free-looking `2` in `1/(1 + θ + 2M)` turns out not to be
free at all: it IS the finite-deme correction, evaluated at the two-population split that
most of this corpus's portability results are about. A reader who took `fstEquilibrium`
for the many-deme law was wrong by exactly that factor, and
`fstEquilibrium_ne_island_manyDemes` below is the witness. -/
theorem fstEquilibrium_eq_island_two_demes (p : PopGenParameters) :
    p.fstEquilibrium = fstIslandEquilibrium p.Ne p.mig p.mu 2 := by
  unfold fstEquilibrium theta bigM
  rw [fstIslandEquilibrium_eq, islandDemeCorrection_two,
    scaledMutationRate_eq, scaledMigrationRate_eq]
  unfold fstFromFlow
  ring_nf

/-- **And it is NOT the many-deme law.** At the record's own witness the two differ:
`1/9.04` against `1/5.04`, which is a factor of `1.79`. So `fstEquilibrium` may not be
substituted for `fstMigrationMutationEquilibriumManyDemes`, and the deme count is not a
detail either law can drop. -/
theorem fstEquilibrium_ne_island_manyDemes :
    PopGenParameters.witness.fstEquilibrium
      ≠ fstFromFlow (scaledMigrationRate PopGenParameters.witness.Ne
          PopGenParameters.witness.mig
        + scaledMutationRate PopGenParameters.witness.Ne PopGenParameters.witness.mu) := by
  unfold fstEquilibrium theta bigM witness
  norm_num [fstFromFlow, scaledMutationRate, scaledMigrationRate, ploidy]

/-- **Equilibrium differentiation lies in the unit interval.** Immediate from the flow
being non-negative, and stated because every consumer of `fstEquilibrium` needs it. -/
theorem fstEquilibrium_mem_unit (p : PopGenParameters) :
    0 ≤ p.fstEquilibrium ∧ p.fstEquilibrium ≤ 1 := by
  have hθ := p.theta_nonneg
  have hM := p.bigM_nonneg
  have hpos : (0 : ℝ) < 1 + (p.theta + 2 * p.bigM) := by linarith
  unfold fstEquilibrium fstFromFlow
  constructor
  · positivity
  · rw [div_le_one hpos]; linarith

/-- **Some flow means incomplete differentiation.** `F_ST = 1` exactly when nothing
connects the demes: no migration and no mutation. Stated with the hypothesis rather than
without, because the no-flow population is a real case and there the equilibrium IS one --
two populations with nothing passing between them are completely differentiated, which is
the right answer and not a junk value. -/
theorem fstEquilibrium_lt_one (p : PopGenParameters) (h : 0 < p.mu + p.mig) :
    p.fstEquilibrium < 1 := by
  have hNe := p.Ne_pos
  have hmu := p.mu_nonneg
  have hmig := p.mig_nonneg
  have hflow : 0 < p.theta + 2 * p.bigM := by
    unfold theta bigM
    rw [scaledMutationRate_eq, scaledMigrationRate_eq]
    nlinarith
  unfold fstEquilibrium fstFromFlow
  rw [div_lt_one (by linarith)]
  linarith

/-- **More migration means less differentiation.** The qualitative law the whole
demography-to-metric chain rests on, proved once on the record rather than once per
consumer. -/
theorem fstEquilibrium_lt_of_mig_lt (p q : PopGenParameters)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hlt : p.mig < q.mig) :
    q.fstEquilibrium < p.fstEquilibrium := by
  unfold fstEquilibrium theta bigM
  rw [hNe, hmu, scaledMutationRate_eq, scaledMigrationRate_eq, scaledMigrationRate_eq]
  have hNepos := q.Ne_pos
  have hmig := p.mig_nonneg
  have hmuq := q.mu_nonneg
  apply fstFromFlow_lt_of_lt
  · have h1 : 0 ≤ 4 * q.Ne * q.mu := by positivity
    have h2 : 0 ≤ 2 * (4 * q.Ne * p.mig) := by positivity
    linarith
  · nlinarith

end PopGenParameters

end Descent.Core
