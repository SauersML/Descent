/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Fst
import Descent.Layer

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

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

## The deme count is a field, and what carrying it fixed

This record carried no deme count, so `fstEquilibrium` could only ever be the TWO-deme
member of the island family: `1/(1 + θ + 2M)`, whose free-looking `2` is
`islandDemeCorrection 2` and nothing else. The `nDemes` degree of freedom that
`Core.fstIslandEquilibrium` was built to carry reached the deployed metric through a
SECOND function taking six raw reals -- `Core.Moments.deployedR2FromIsland` -- so there
were two routes from a demography to one metric, in the two files built to end that
pattern. `nDemes` is a field now, `fstEquilibrium` is the island master at this record's
own deme count, and the raw-real route is deleted.

`nDemes_ge_two` is the admissibility that field earns rather than a tidy-looking bound.
At one deme `Core.islandDemeCorrection_one_is_junk` shows the correction is Lean's `0` --
no inflation at all, reported for a quantity that is undefined -- so a record admitting
`d = 1` would compute `1/(1 + θ)` and call it the differentiation of a population that is
not divided.

## Fields this record does NOT carry, and why

A selection coefficient, a locus count and a sample size were each considered here and
each rejected. A field no theorem reads is a slot, not a parameter, and a record that
accumulates slots stops being the one place a constraint has to be added.

`Core.Moments.momentsUnderDrift` states its regime in its own docstring: no selection, no
gene-environment interaction, no effect turnover, the same causal variants in both
populations. There is no selection law at this depth for a `selCoef` to enter. Adding the
field would have meant writing a new equilibrium under selection to give it something to
do, which is a new empirical claim with no measurement behind it, arriving under cover of
a field addition.

A locus count and a sample size are excluded for a sharper reason, and it is a theorem
rather than a judgement: `fstEquilibrium_congr` below, and
`Core.Moments.deployedR2_congr`, prove that the equilibrium and the deployed metric are
functions of `Ne`, `mu`, `mig`, `nDemes` and `V_A` and of nothing else this record
carries. Genetic architecture reaches the drift chain only through `V_A`, which is
already here; a sample size belongs to an ESTIMATE of a metric rather than to the metric,
which is a population quantity and has no sampling error. Both want a sampling law to
attach to, and this layer has none.

## Empirical status

A parameter record asserts nothing, and the fields, the witness and `atOrigin` carry no
status for that reason. `fstEquilibrium` is the exception and states its own: it is a
LAW computed from the record, it has been measured at two demes, and it is what
`Core.Moments.deployedR2` reads. Nothing else in this file is on trial.
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
  /-- Number of demes in the island lattice this history is read as. Two for a
  two-population split, which is most of this corpus; larger for a structured
  metapopulation. Real rather than natural because `islandDemeCorrection` divides by
  `d - 1` and every consumer of it works in `ℝ`. -/
  nDemes : ℝ
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
  /-- A subdivided population has at least two parts. This is the field that keeps the
  deme correction meaningful: at `d = 1` there is nowhere to migrate from,
  `Core.islandDemeCorrection_one_is_junk` shows the correction is Lean's `0`, and a
  record admitting it would report `1/(1 + θ)` as the differentiation of an undivided
  population. It is also what makes `d/(d-1)` strictly above one, which every positivity
  bound below reads. -/
  nDemes_ge_two : 2 ≤ nDemes
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
`μ = 10⁻⁵` per generation, `m = 10⁻³`, `d = 2` demes, `t = 2000` generations,
`r = 10⁻²`, additive variance `1`.

A theorem quantified over an uninhabited structure is true and empty. Every value here
is strictly inside its constraint -- no rate is zero and the recombination fraction is
well below the free-assortment boundary -- so nothing downstream reads a degenerate
point. The deme count is the one exception and deliberately sits ON its boundary: two is
the two-population split most of this corpus's portability results are about, and it is
the value at which `fstEquilibrium` reduces to the body the batteries measured.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a parameter record and the
    laws computed from it. What carries a status is a claim that a population
    reaches these values, which is asked where the demography is. -/
noncomputable def witness : PopGenParameters where
  Ne := 1000
  mu := 1 / 100000
  mig := 1 / 1000
  nDemes := 2
  t_div := 2000
  recomb := 1 / 100
  V_A := 1
  Ne_pos := by norm_num
  mu_nonneg := by norm_num
  mig_nonneg := by norm_num
  nDemes_ge_two := by norm_num
  t_div_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num

/-- **A history with no divergence.** The predicate a model without a split satisfies,
named so that `t_div = 0` reads as a claim rather than as an unfilled field.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a parameter record and the
    laws computed from it. What carries a status is a claim that a population
    reaches these values, which is asked where the demography is. -/
def atOrigin (p : PopGenParameters) : Prop := p.t_div = 0

/-- **The witness is not at the origin.** `atOrigin` names the `t_div = 0` reading so a
model without a divergence time says so rather than leaving a field at its default; this
pins that the standard-scale witness is a diverged history and not that default. -/
theorem witness_not_atOrigin : ¬ witness.atOrigin := by
  unfold atOrigin witness
  norm_num

/-! ### The record's scaled coordinates, in the types that carry the scaling

These three accessors return `Theta`, `BigM` and `Tau` rather than three reals. They used
to return reals, and the record was therefore the place where the scaling convention was
lost: `p.theta` and `p.bigM` are the same number at equal rates -- `theta_bigM_share_constant`
says so -- so a body reading the wrong one off the record typechecked. Every consumer that
needs the number asks for `.value`, and no consumer can supply one where the other belongs. -/

/-- Scaled mutation rate, `θ = 4 Nₑ μ`, in this record's coordinates.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a parameter record and the
    laws computed from it. What carries a status is a claim that a population
    reaches these values, which is asked where the demography is. -/
noncomputable def theta (p : PopGenParameters) : Theta := Theta.ofRate p.Ne p.mu

/-- Scaled migration rate in this record's coordinates, `M = 4 Nₑ m`.

Both modules that carried a parameter record defined `bigM` this way, so this is the
corpus's convention and not a choice made here.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a parameter record and the
    laws computed from it. What carries a status is a claim that a population
    reaches these values, which is asked where the demography is. -/
noncomputable def bigM (p : PopGenParameters) : BigM := BigM.ofRate p.Ne p.mig

/-- The record's divergence time in coalescent units, `τ = t_div / (2 Nₑ)`.

The third scaled coordinate, and the one the record could not previously state: `t_div`
and `Ne` were both fields and every consumer that wanted a scaled time divided them by
hand, which is how `t/(2 Nₑ)` and `t/(4 Nₑ)` both appear in the corpus. `Tau.ofGenerations`
carries the `ploidy` and this names its value on this record.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a parameter record and the
    laws computed from it. What carries a status is a claim that a population
    reaches these values, which is asked where the demography is. -/
noncomputable def tau (p : PopGenParameters) : Tau := Tau.ofGenerations p.t_div p.Ne

/-- **`M` is the scaled migration rate, not half of it.** -/
theorem bigM_eq_scaledMigrationRate (p : PopGenParameters) :
    p.bigM.value = scaledMigrationRate p.Ne p.mig :=
  scaledMigrationRate_eq_bigM p.Ne p.mig

/-- **And `θ` is the scaled mutation rate.** The companion, stated so both readings of the
record's coordinates go through a named theorem rather than through `rfl` at a use site. -/
theorem theta_eq_scaledMutationRate (p : PopGenParameters) :
    p.theta.value = scaledMutationRate p.Ne p.mu :=
  scaledMutationRate_eq_theta p.Ne p.mu

/-- **The record's scaled time is `t_div / (2 Nₑ)`.** -/
@[simp] theorem tau_value (p : PopGenParameters) :
    p.tau.value = p.t_div / (2 * p.Ne) :=
  Tau.value_ofGenerations p.t_div p.Ne

/-- Both scaled rates are non-negative, which every equilibrium below needs. -/
theorem theta_nonneg (p : PopGenParameters) : 0 ≤ p.theta.value := by
  rw [p.theta_eq_scaledMutationRate, scaledMutationRate_eq]
  have := p.Ne_pos
  have := p.mu_nonneg
  positivity

/-- Both scaled rates are non-negative, which every equilibrium below needs. -/
theorem bigM_nonneg (p : PopGenParameters) : 0 ≤ p.bigM.value := by
  rw [p.bigM_eq_scaledMigrationRate, scaledMigrationRate_eq]
  have := p.Ne_pos
  have := p.mig_nonneg
  positivity

/-! ### The deme correction this record carries

`nDemes_ge_two` does its work here and nowhere else. Everything below reads the
correction through `demeCorrection_gt_one`, so a record that dropped the bound would fail
at this one lemma rather than silently producing a negative flow four theorems later. -/

/-- **The deme correction is a strict inflation.** `d/(d-1) > 1` at every `d ≥ 2`: the
migration term is always inflated, never deflated, and never the junk `0` that
`islandDemeCorrection_one_is_junk` records at a single deme. Proved through
`islandDemeCorrection_sub_one`, which gives the exact excess `1/(d-1)` rather than a
bound, so the strictness is read off a value. -/
theorem demeCorrection_gt_one (p : PopGenParameters) :
    1 < islandDemeCorrection p.nDemes := by
  have hd := p.nDemes_ge_two
  have hne : p.nDemes ≠ 1 := by
    intro h
    rw [h] at hd
    norm_num at hd
  have hsub := islandDemeCorrection_sub_one p.nDemes hne
  have hpos : 0 < 1 / (p.nDemes - 1) := div_pos one_pos (by linarith)
  linarith

/-- **The record's total scaled flow, in raw coordinates.** Written out once so that
every bound below reads the same expression rather than re-deriving it. -/
theorem scaledFlow_eq (p : PopGenParameters) :
    scaledFlow p.bigM p.theta p.nDemes
      = 4 * p.Ne * p.mig * islandDemeCorrection p.nDemes + 4 * p.Ne * p.mu := by
  unfold scaledFlow
  rw [p.bigM_eq_scaledMigrationRate, p.theta_eq_scaledMutationRate,
    scaledMigrationRate_eq, scaledMutationRate_eq]

/-- **The flow a record produces is non-negative.** Four fields at once: `Ne_pos`,
`mig_nonneg`, `mu_nonneg` and -- through `demeCorrection_gt_one` -- `nDemes_ge_two`. Drop
the deme bound and the correction can be zero or negative, and the flow with it. -/
theorem scaledFlow_nonneg (p : PopGenParameters) :
    0 ≤ scaledFlow p.bigM p.theta p.nDemes := by
  have hc := p.demeCorrection_gt_one
  have hNe := p.Ne_pos
  have h1 : 0 ≤ 4 * p.Ne * p.mig * islandDemeCorrection p.nDemes :=
    mul_nonneg (mul_nonneg (by linarith) p.mig_nonneg) (by linarith)
  have h2 : 0 ≤ 4 * p.Ne * p.mu := mul_nonneg (by linarith) p.mu_nonneg
  rw [p.scaledFlow_eq]
  linarith

/-- **Some rate means some flow.** Strict positivity as soon as mutation or migration is
running, which is exactly the hypothesis `fstEquilibrium_lt_one` carries. The deme
correction cannot rescue a dead history and cannot kill a live one: it multiplies the
migration term by something above one. -/
theorem scaledFlow_pos (p : PopGenParameters) (h : 0 < p.mu + p.mig) :
    0 < scaledFlow p.bigM p.theta p.nDemes := by
  have hc := p.demeCorrection_gt_one
  have hNe := p.Ne_pos
  have hmig : 0 ≤ 4 * p.Ne * p.mig := mul_nonneg (by linarith) p.mig_nonneg
  have h1 : 4 * p.Ne * p.mig * 1 ≤ 4 * p.Ne * p.mig * islandDemeCorrection p.nDemes :=
    mul_le_mul_of_nonneg_left (le_of_lt hc) hmig
  have h2 : 0 < 4 * p.Ne * (p.mu + p.mig) := mul_pos (by linarith) h
  rw [p.scaledFlow_eq]
  linarith

/-- **Equilibrium `F_ST` in this record's coordinates**: the island master, evaluated at
this record's own deme count.

    F_ST = 1 / (1 + 4 Nₑ m · d/(d-1) + 4 Nₑ μ)

There is one route from a demography to a differentiation and this is it. The body used
to read `1/(1 + θ + 2M)`, which is this law at `d = 2` and at no other deme count, and
the deme count reached the deployed metric only through a second function taking six raw
reals. `fstEquilibrium_eq_scaled_two_demes` below recovers the old body from this one as
the `nDemes = 2` member, and that theorem is what carries the measurement across.

    Empirical status: **MIXED**. The `nDemes = 2` member is VALIDATED; the deme
    dependence of the general body is UNTESTED. Every cell of every battery
    below was run at two demes, so what has been measured is the two-deme
    specialisation, and the `d/(d-1)` factor has never been swept against THIS
    body. That gap is not a formality: `simcov/battery_falsrepair_c2.py`
    FALSIFIES the many-deme limit `d/(d-1) = 1` at `d = 20` at 3.92 sems, on
    `PopGen.fstMigrationMutationEquilibriumManyDemes`, where the finite-deme
    form matches the same cells at 2.47. So the correction is measurable and
    moves the answer, and the design that would put this body's deme dependence
    on trial is owed rather than done.

    THE TWO-DEME MEMBER, MEASURED (`simcov/battery_falsrepair.py` `group_a`,
    and `simcov/battery_bulk38b.py`). Those batteries transcribe
    `1/(1 + theta + 2*bigM)`, which `fstEquilibrium_eq_scaled_two_demes` proves
    is this body at `p.nDemes = 2`, in these coordinates: the battery sets
    `m = bigM / (4 Nₑ)`, so its `bigM` is `4 Nₑ m`, which is this record's
    `bigM`, and its corpus candidate is that expression character for character.
    msprime infinite alleles at `Nₑ = 500`, `F_ST` built per replicate from
    identity by state as `(F_within - F_between)/(1 - F_between)` -- both terms
    measured, neither computed from the body -- 60 replicates over six `(θ, M)`
    cells: worst 1.10 sems. `bulk38b` re-runs `bulk38`'s own four cells and
    matches at 1.03. Three competitors are excluded on the same cells: the
    superseded body `1/(1 + θ + M)` at 7.58 sems, the multiplicative composition
    `1/((1 + θ)(1 + M))` at 5.37, and the squared correction `1/(1 + θ + 4M)`
    at 5.37. The cell table is on `PopGen.DGP.fstEquilibrium`, which is the
    two-deme body in the other parameter record's coordinates.

    THE LEDGER ALSO CARRIES A FALSIFICATION UNDER THIS NAME, AND IT IS NOT
    AGAINST THIS BODY. `simcov/battery_bulk38.py` rejects `1/(1 + θ + M)` at
    3.30 sems and 57% relative -- the body this one replaced, before the
    migration term carried the deme-count correction at all. That row is what
    moved the body. `simcov/adjudications.json` names `falsrepair` authoritative
    and records `bulk38` as superseded, and `bulk38b` re-runs bulk38's cells with
    the old body as a NAMED COMPETITOR, where it fails at the same 3.30 -- which
    is the check that the two rows are about two formulas and not two
    measurements. `simcov/battery_transfer.py`'s row is UNINFORMATIVE and also
    transcribes the old body.

    Why this declaration states its own evidence rather than inheriting the
    module's "a record asserts nothing": it is the input to
    `Core.Moments.deployedR2`, and so to every demography-to-metric theorem in
    the corpus. A silent status here is a silent status on the spine. -/
noncomputable def fstEquilibrium (p : PopGenParameters) : ℝ :=
  fstIslandEquilibrium p.bigM p.theta p.nDemes

/-- **One route, and this is it.** The record's equilibrium IS the island master at the
record's own deme count -- definitionally, not up to a lemma. Stated so that a reader who
knows `fstIslandEquilibrium` can see there is nothing else here, and so that the claim
survives as a theorem if the body is ever written a different way. -/
theorem fstEquilibrium_eq_island (p : PopGenParameters) :
    p.fstEquilibrium = fstIslandEquilibrium p.bigM p.theta p.nDemes := rfl

/-- **At two demes this is the two-deme island member.** The specialisation named, so a
result stated for the two-population split says which member it is about rather than
inheriting one by silence. -/
theorem fstEquilibrium_eq_island_two_demes (p : PopGenParameters) (hd : p.nDemes = 2) :
    p.fstEquilibrium = fstIslandEquilibrium p.bigM p.theta 2 := by
  unfold fstEquilibrium
  rw [hd]

/-- **And at two demes it is the measured body, `1/(1 + θ + 2M)`.**

This is the theorem the empirical record hangs on. The batteries on `fstEquilibrium`
transcribe `1/(1 + theta + 2*bigM)` character for character; that expression is this
body at `p.nDemes = 2` and at no other deme count, because `bigM` is `4 Nₑ m` so `2M` is
`8 Nₑ m` while the master carries `4 Nₑ m · d/(d-1)`, and those agree exactly when
`d/(d-1) = 2`.

So the free-looking `2` the old body carried was never free: it IS
`islandDemeCorrection 2`, and a reader who took `1/(1 + θ + 2M)` for the many-deme law
was wrong by that factor. What has changed is that the deme count is now a field, so the
specialisation is a hypothesis a caller states rather than an assumption the record made
for everyone. `fstEquilibrium_ne_island_manyDemes` below is the witness that the two
readings are far apart. -/
theorem fstEquilibrium_eq_scaled_two_demes (p : PopGenParameters) (hd : p.nDemes = 2) :
    p.fstEquilibrium = fstFromFlow (p.theta.value + 2 * p.bigM.value) := by
  unfold fstEquilibrium theta bigM
  rw [hd, fstIslandEquilibrium_eq, islandDemeCorrection_two,
    Theta.value_ofRate, BigM.value_ofRate]
  unfold fstFromFlow
  ring_nf

/-- **And it is NOT the many-deme law.** At the record's own witness -- which carries two
demes -- the two differ: `1/9.04` against `1/5.04`, a factor of `1.79`. So the equilibrium
may not be substituted for `fstMigrationMutationEquilibriumManyDemes`, and the deme count
is not a detail either law can drop. This is the witness that `nDemes` is a real degree of
freedom rather than a field the metric ignores. -/
theorem fstEquilibrium_ne_island_manyDemes :
    PopGenParameters.witness.fstEquilibrium
      ≠ fstFromFlow (scaledMigrationRate PopGenParameters.witness.Ne
          PopGenParameters.witness.mig
        + scaledMutationRate PopGenParameters.witness.Ne PopGenParameters.witness.mu) := by
  unfold fstEquilibrium witness
  norm_num [fstIslandEquilibrium, scaledFlow, fstFromFlow, theta, bigM,
    Theta.ofRate, BigM.ofRate, scalingConstant, scaledMutationRate,
    scaledMigrationRate, islandDemeCorrection, ratio, ploidy]

/-- **Equilibrium differentiation lies in the unit interval.** Immediate from the flow
being non-negative, and stated because every consumer of `fstEquilibrium` needs it. -/
theorem fstEquilibrium_mem_unit (p : PopGenParameters) :
    0 ≤ p.fstEquilibrium ∧ p.fstEquilibrium ≤ 1 := by
  have hf := p.scaledFlow_nonneg
  have hpos : (0 : ℝ) < 1 + scaledFlow p.bigM p.theta p.nDemes := by linarith
  unfold fstEquilibrium fstIslandEquilibrium fstFromFlow
  refine ⟨div_nonneg zero_le_one (le_of_lt hpos), ?_⟩
  rw [div_le_one hpos]
  linarith

/-- **Some flow means incomplete differentiation.** `F_ST = 1` exactly when nothing
connects the demes: no migration and no mutation. Stated with the hypothesis rather than
without, because the no-flow population is a real case and there the equilibrium IS one --
two populations with nothing passing between them are completely differentiated, which is
the right answer and not a junk value. -/
theorem fstEquilibrium_lt_one (p : PopGenParameters) (h : 0 < p.mu + p.mig) :
    p.fstEquilibrium < 1 := by
  have hf := p.scaledFlow_pos h
  unfold fstEquilibrium fstIslandEquilibrium fstFromFlow
  rw [div_lt_one (by linarith)]
  linarith

/-- **The equilibrium reads four of this record's fields and no others.**

`Ne`, `mu`, `mig`, `nDemes`. Not `t_div`, not `recomb`, and not anything a later hand
adds without a law to read it. The statement is worth having as a theorem rather than as
an observation about the body: it is the machine-checkable form of the rule that a field
must earn its place, and a field added with nothing to do fails to break it, which is
exactly what makes it a slot. -/
theorem fstEquilibrium_congr (p q : PopGenParameters)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) :
    p.fstEquilibrium = q.fstEquilibrium := by
  unfold fstEquilibrium theta bigM
  rw [hNe, hmu, hmig, hd]

/-- **More migration means less differentiation.** The qualitative law the whole
demography-to-metric chain rests on, proved once on the record rather than once per
consumer.

`hd` is not decoration. Two histories at different deme counts have different effective
migration between any given pair, so a comparison that let the lattice move too would be
about two changes at once. -/
theorem fstEquilibrium_lt_of_mig_lt (p q : PopGenParameters)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hlt : p.mig < q.mig) :
    q.fstEquilibrium < p.fstEquilibrium := by
  have hc := q.demeCorrection_gt_one
  have hNepos := q.Ne_pos
  unfold fstEquilibrium fstIslandEquilibrium
  refine fstFromFlow_lt_of_lt _ _ p.scaledFlow_nonneg ?_
  rw [p.scaledFlow_eq, q.scaledFlow_eq, hNe, hmu, hd]
  have h4 : (0 : ℝ) < 4 * q.Ne := by linarith
  have hmiglt : 4 * q.Ne * p.mig < 4 * q.Ne * q.mig := mul_lt_mul_of_pos_left hlt h4
  have key := mul_lt_mul_of_pos_right hmiglt
    (by linarith : (0 : ℝ) < islandDemeCorrection q.nDemes)
  linarith

/-- **More mutation, more transferable score.** Mutation regenerates variation the demes
would otherwise lose to drift, so it lowers the equilibrium differentiation exactly as
migration does -- and the chain carries that all the way to the deployed metric. -/
theorem fstEquilibrium_lt_of_mu_lt (p q : PopGenParameters)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hlt : p.mu < q.mu) :
    q.fstEquilibrium < p.fstEquilibrium := by
  have hNepos := q.Ne_pos
  unfold fstEquilibrium fstIslandEquilibrium
  refine fstFromFlow_lt_of_lt _ _ p.scaledFlow_nonneg ?_
  rw [p.scaledFlow_eq, q.scaledFlow_eq, hNe, hmig, hd]
  have h4 : (0 : ℝ) < 4 * q.Ne := by linarith
  have key : 4 * q.Ne * p.mu < 4 * q.Ne * q.mu := mul_lt_mul_of_pos_left hlt h4
  linarith

/-- **Larger effective size, more transferable score.** `Nₑ` multiplies both scaled
rates, so a bigger population reaches a lower equilibrium differentiation at the same
per-generation rates: drift is what differentiates, and drift is weaker when there are
more copies to sample from.

The flow hypothesis is now `0 < mu + mig` rather than `0 < mu + 2 mig`. The old form was
the two-deme migration coefficient written into a hypothesis; with the deme correction
carried as a field the coefficient is `d/(d-1)`, which is above one at every admissible
record, so the two hypotheses have the same content and only one of them says so. -/
theorem fstEquilibrium_lt_of_Ne_lt (p q : PopGenParameters)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hflow : 0 < p.mu + p.mig) (hlt : p.Ne < q.Ne) :
    q.fstEquilibrium < p.fstEquilibrium := by
  have hc := p.demeCorrection_gt_one
  have hNepos := p.Ne_pos
  unfold fstEquilibrium fstIslandEquilibrium
  refine fstFromFlow_lt_of_lt _ _ p.scaledFlow_nonneg ?_
  rw [p.scaledFlow_eq, q.scaledFlow_eq, ← hmu, ← hmig, ← hd]
  have hrate : 0 < 4 * p.mig * islandDemeCorrection p.nDemes + 4 * p.mu := by
    have h1 : 4 * p.mig * 1 ≤ 4 * p.mig * islandDemeCorrection p.nDemes :=
      mul_le_mul_of_nonneg_left (le_of_lt hc) (by linarith [p.mig_nonneg])
    linarith [p.mu_nonneg, p.mig_nonneg]
  have key := mul_pos (sub_pos.mpr hlt) hrate
  nlinarith [key]

/-- **More demes, more differentiation between any two of them.**

The deme correction `d/(d-1)` FALLS with `d`, so the effective migration between a given
pair falls, so the equilibrium differentiation rises. Counter-intuitive read as "more
populations means more mixing" and correct read as "a fixed per-pair migration rate
spreads a deme's immigration over more sources".

Migration must be strictly positive: at `m = 0` the deme count multiplies nothing and the
equilibrium is the pure mutation-drift balance at every lattice size, which is a real case
and not an edge to be excluded by fiat.

This is the law the empirical ledger asked for. `simcov/battery_falsrepair_c2.py`
FALSIFIES the many-deme limit at `d = 20` at 3.92 sems where the finite-deme form matches
at 2.47, which says the deme count moves the measured differentiation; this says which way
it moves and carries that all the way to the metric through
`Core.Moments.deployedR2_anti_in_demes`. -/
theorem fstEquilibrium_lt_of_nDemes_lt (p q : PopGenParameters)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    p.fstEquilibrium < q.fstEquilibrium := by
  have hp := p.nDemes_ge_two
  have hq := q.nDemes_ge_two
  have hNepos := q.Ne_pos
  have hcorr : islandDemeCorrection q.nDemes < islandDemeCorrection p.nDemes := by
    unfold islandDemeCorrection ratio
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  unfold fstEquilibrium fstIslandEquilibrium
  refine fstFromFlow_lt_of_lt _ _ q.scaledFlow_nonneg ?_
  rw [p.scaledFlow_eq, q.scaledFlow_eq, hNe, hmu, hmig]
  have hqmig : (0 : ℝ) < q.mig := by rw [← hmig]; exact hmigpos
  have h4 : (0 : ℝ) < 4 * q.Ne * q.mig := mul_pos (by linarith) hqmig
  have key := mul_lt_mul_of_pos_left hcorr h4
  linarith

end PopGenParameters

end Descent.Core
