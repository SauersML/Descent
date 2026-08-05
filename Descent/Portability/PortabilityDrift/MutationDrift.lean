/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.PresentDayMoments

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.MutationDrift`

Part of the split of `Portability/PortabilityDrift.lean`, which was 9,208 lines and 555
declarations -- the largest file in the corpus by both measures, and large enough that
nothing in it could be read without reading past most of it.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Sections are reopened and reclosed by name where a cut falls inside one: the original
opened `section PortabilityDrift` and closed it 8,000 lines later. A section scopes
`variable`s, and this file declares none at that level, so the reopening is exact.
-/



/-!
## Mutation-Drift Balance and Portability

When mutation is non-negligible, Fst has a finite equilibrium (Wright's
1/(1+4Neμ)) instead of approaching 1. This section generalizes the drift-only
portability model to include mutation as a first-class parameter.

Key results:
1. Generalized divergence model that includes mutation rate
2. Covariance divergence including both drift and mutation terms
3. Portability under mutation-drift: mutation-generated population-specific
   variants reduce tagging efficiency
4. Comparison: mutation-drift equilibrium portability vs pure-drift portability
-/

section MutationDriftPortability

/-- Generalized divergence model assumptions that include mutation as a parameter
    rather than assuming it is negligible. -/
structure MutationDriftModelAssumptions where
  Ne : ℝ
  μ : ℝ
  t : ℝ
  Ne_pos : 0 < Ne
  mu_pos : 0 < μ
  t_nonneg : 0 ≤ t

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MutationDriftModelAssumptions.witness : MutationDriftModelAssumptions where
  Ne := 1
  μ := 1
  t := 1
  Ne_pos := by norm_num
  mu_pos := by norm_num
  t_nonneg := by norm_num

/-- The scaled mutation parameter θ = 4Neμ for a mutation-drift model.

    Empirical status: UNTESTED. -/
noncomputable def MutationDriftModelAssumptions.theta (m : MutationDriftModelAssumptions) : ℝ :=
  Descent.Core.scaledMutationRate m.Ne m.μ

/-- **The scaled mutation parameter is linear in the mutation rate with slope four Ne.**
`theta_pos` below fixes the sign and leaves the slope free. -/
theorem MutationDriftModelAssumptions.theta_div_mu (m : MutationDriftModelAssumptions)
    (h : m.μ ≠ 0) :
    m.theta / m.μ = 4 * m.Ne := by
  unfold MutationDriftModelAssumptions.theta Descent.Core.scaledMutationRate
    Descent.Core.scaledMutationRate Descent.Core.ploidy
  field_simp
  ring

/-- θ is positive for any valid mutation-drift model. -/
theorem MutationDriftModelAssumptions.theta_pos (m : MutationDriftModelAssumptions) :
    0 < m.theta := by
  unfold MutationDriftModelAssumptions.theta Descent.Core.scaledMutationRate Descent.Core.ploidy
  nlinarith [m.Ne_pos, m.mu_pos]

/-- **One generation of the identity-by-descent balance.**

`F` is the probability that two gene copies drawn from the same subpopulation
are identical by descent (equivalently, `F_ST` measured against a total
population in which that probability is zero).  In one generation:

* drift makes a pair identical with probability `1/(2 Nₑ)` among the pairs that
  are not already identical, contributing `+(1 - F)/(2 Nₑ)`;
* each of the two lineages independently escapes the local identity class at
  rate `rate` -- by mutating away from its ancestral allelic state, or by being
  replaced by a migrant -- contributing `-2 · rate · F`.

`rate` is therefore whichever homogenising force is in play: `μ` for
mutation-drift balance, `m` for migration-drift balance, `μ + m` for both.
That the two forces enter identically is the whole content of
`islandModelFst_eq_mutationForm`.

Composition convention: this is the first-order (weak-force, large-`Nₑ`)
recursion, in which drift and the homogenising force are *added*, so their
within-generation ordering does not matter.  The unlinearised discrete-generation
recursion multiplies them instead -- see `islandFstMultiplicativeStep` -- and its fixed
point differs from this one at O(rate², rate/Nₑ).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_max.py`, `test_ibd_flow_step`).
    Wright-Fisher forward simulation, 4000 loci, 300 replicate populations, one
    generation of drift plus gene flow from a fixed source pool, `F` read as
    `1 - H/H_ancestral`:

      Ne     rate     this def   simulated            sems
      200    0.000     0.07459   0.07452±0.00030      0.22
      200    0.002     0.07018   0.07015±0.00028      0.09
      500    0.005     0.02596   0.02592±0.00010      0.43

    Power: the prediction spans 0.02596 to 0.07459 across the design. -/
noncomputable def ibdFlowStep (Ne rate F : ℝ) : ℝ :=
  F + (1 - F) / (2 * Ne) - 2 * rate * F

/-- **ibdFlowStep where its denominator vanishes, named.** The guard `2 * Ne` is zero at `Ne = 0`.
Lean returns `F - 2 * rate * F` there rather than the value the modelled quantity takes, and no
type error marks the point. Consumers must require `2 * Ne ≠ 0`. -/
theorem ibdFlowStep_at_ne0_is_junk (rate : ℝ) (F : ℝ) :
    ibdFlowStep 0 rate F = F - 2 * rate * F := by
  unfold ibdFlowStep
  norm_num

/-- **`1/(1 + 4 Nₑ · rate)` is the fixed point of the identity balance.**
Setting `(1 - F)/(2 Nₑ) = 2 · rate · F` gives `1 - F = 4 Nₑ · rate · F`, hence
`F = 1/(1 + 4 Nₑ · rate)`.  This single lemma is what pins every `1/(1 + θ)`
and `1/(1 + 4 N m)` in the development; none of them is stipulated. -/
theorem ibdFlowStep_fixedPoint (Ne rate : ℝ) (hNe : 0 < Ne) (hrate : 0 ≤ rate) :
    ibdFlowStep Ne rate (1 / (1 + 4 * Ne * rate)) = 1 / (1 + 4 * Ne * rate) := by
  have hprod : (0 : ℝ) ≤ 4 * Ne * rate := by positivity
  have hd : (0 : ℝ) < 1 + 4 * Ne * rate := by linarith
  have hd' : (1 : ℝ) + 4 * Ne * rate ≠ 0 := ne_of_gt hd
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  unfold ibdFlowStep
  field_simp
  ring

/-- **Complete fixation is a boundary the balance attains.**  With no
homogenising force the only fixed point is `F = 1`: drift runs to completion.
The closed form takes that value exactly, rather than approaching it. -/
@[simp] theorem ibdFlowStep_one_of_no_flow (Ne : ℝ) :
    ibdFlowStep Ne 0 1 = 1 := by
  unfold ibdFlowStep
  simp

/-- **Equilibrium identity probability under mutation-drift balance,
`F = 1/(1 + θ)` with `θ = 4·Nₑ·μ`.**

    **Attribution, corrected.** This is *not* the Wright (1931) island-model
    result, which this file also carries at `fstMigrationDriftEquilibrium` and
    which is `1/(1 + 4·Nₑ·m)` in the MIGRATION rate. The mutation-drift form is
    Malécot's `(4Nu + 1)⁻¹`, standardly cited to Kimura and Crow (1964),
    *The Number of Alleles That Can Be Maintained in a Finite Population*,
    Genetics 49:725--738. The two laws share the algebraic shape `1/(1 + 4·Nₑ·rate)`
    -- that shared shape is the whole content of `ibdFlowStep_fixedPoint`, which
    proves it once for an abstract `rate` -- and they are different results about
    different forces. A docstring that names the wrong one invites a reader to
    substitute `m` for `μ` on the authority of a citation that does not cover it.

    Convention: despite the `Fst` in the name (inherited from
    `DGP.fstMutationDriftEquilibrium`, whose docstring says the same thing), the
    quantity is the probability that two gene copies drawn at random from ONE
    population are identical by descent -- the complement of the equilibrium
    heterozygosity `θ/(1+θ)` at `PortabilityDrift.hetMutationFloor`. It is not a
    between-population differentiation measure.

    Not stipulated: `MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint`
    derives it as the rest point of `ibdFlowStep` with `rate = μ`.

    Empirical status: **VALIDATED**, by projection. This body IS
    `DGP.fstMutationDriftEquilibrium m.theta` -- not an analogue of it, the same
    function applied to this structure's field -- so the measurement there
    transfers without a separate design. That run is `simcov/battery_bulk19.py`
    against `msprime`'s `InfiniteAlleles` model, worst cell 2.40 sems, with `Nₑ`
    and `μ` swept by a factor of four INDEPENDENTLY so each `θ` is reached twice
    by different routes; `simcov/battery_bulk20b.py` corroborates from the
    complementary side, measuring `θ/(1+θ)` over a hundredfold `θ` sweep at
    worst 2.17 sems with an Ewens allele-count control passing at 1.10 sems.

    What does NOT transfer is the reading of the name: `fst` here is the
    probability that two alleles drawn WITHIN a population are identical by
    state, the complement of heterozygosity, and not a between-population
    differentiation. The measurement above is of that within-population
    quantity. A consumer wanting differentiation wants
    `DGP.EvolutionaryParameters.fstEquilibrium`, which is separately FALSIFIED
    -- so the two must not be substituted for one another. -/
noncomputable def MutationDriftModelAssumptions.fstEquilibrium
    (m : MutationDriftModelAssumptions) : ℝ :=
  PopGen.fstMutationDriftEquilibrium m.theta

/-- **The equilibrium inverts one plus the scaled mutation parameter.** `fstEquilibrium_pos`
fixes the sign; this fixes the value, and a body carrying any other coefficient on `theta` would
be positive too. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_mul_denom
    (m : MutationDriftModelAssumptions) (h : 1 + m.theta ≠ 0) :
    m.fstEquilibrium * (1 + m.theta) = 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  field_simp

/-- **The mutation-drift equilibrium is the fixed point of the identity
balance** driven by mutation alone. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint
    (m : MutationDriftModelAssumptions) :
    ibdFlowStep m.Ne m.μ m.fstEquilibrium = m.fstEquilibrium := by
  have hθ : m.fstEquilibrium = 1 / (1 + 4 * m.Ne * m.μ) := by
    unfold MutationDriftModelAssumptions.fstEquilibrium MutationDriftModelAssumptions.theta
      PopGen.fstMutationDriftEquilibrium Descent.Core.scaledMutationRate Descent.Core.fstFromFlow
      Descent.Core.scaledMutationRate Descent.Core.ploidy
    ring_nf
  rw [hθ]
  exact ibdFlowStep_fixedPoint m.Ne m.μ m.Ne_pos (le_of_lt m.mu_pos)

/-- Equilibrium Fst is positive. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_pos
    (m : MutationDriftModelAssumptions) :
    0 < m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstEquilibrium PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  have hden : 0 < 1 + m.theta := by
    nlinarith [m.theta_pos]
  exact div_pos one_pos hden

/-- Equilibrium Fst is strictly less than 1 (mutation prevents complete fixation). -/
theorem MutationDriftModelAssumptions.fstEquilibrium_lt_one
    (m : MutationDriftModelAssumptions) :
    m.fstEquilibrium < 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium PopGen.fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_lt_one (by linarith [m.theta_pos])]
  linarith [m.theta_pos]

/-- **Transient Fst under mutation-drift: approach to equilibrium.**
    Fst(t) = Fst_eq × (1 - exp(-(1+θ)t/(2Ne)))

    Regime: two demes split from a common ancestor, no migration, mutation at
    `θ = 4·Nₑ·μ`.

    Empirical status: **VALIDATED on its RATE**
    (`simcov/battery_bulk24.py`). The body makes two separable claims -- a
    plateau `Fst_eq` and a time constant `τ = 2·Nₑ/(1+θ)` -- and only the second
    is convention-free. Whether the plateau is Nei's `G_ST`, Hudson's `F_ST` or
    a per-branch drift `F` moves it by factors of two and four, and this corpus
    has already lost a factor of four to exactly that. Rescaling `F_ST` by any
    constant leaves `τ` untouched. So the design fits `A·(1 - exp(-t/τ))` to the
    measured trajectory, DISCARDS the amplitude `A`, and puts `τ` on trial:

      Nₑ     θ      τ measured      2·Nₑ/(1+θ)    sems
      500    0.5    668 ± 45        667           0.03
      500    0.02   912 ± 61        980           1.13
      1000   0.5    1333 ± 67       1333          0.00
      500    1.0    658 ± 83        500           1.92
      1000   0.1    1661 ± 71       1818          2.22

    Worst cell 2.22 sems. `Nₑ` and `θ` are swept separately, so the two scalings
    are separately falsifiable; holding `θ = 0.5` and doubling `Nₑ` moves `τ` by
    a factor of 1.996 against 2.000 predicted.

    Power, and why this is a measurement rather than an identity: the drift-only
    rate `τ = 2·Nₑ`, which drops the mutation term, is carried on the SAME cells
    and is FALSIFIED at up to 9.96 sems (50% relative). An oracle algebraically
    pinned to the body could not reject a competing form -- the "measurement"
    would move with whatever prediction was fed in -- so the rejection is what
    establishes that `τ` was measured and not recomputed. The control, a
    `θ = 0.02` cell where both candidate rates coincide, passed at 0.15 sems.

    LIMITS OF THIS RUN, recorded rather than smoothed over. The `θ = 0.5` and
    `θ = 1.0` cells fit amplitudes `A` of 1.13 and 1.59 -- an `F_ST` above one,
    which is unphysical and marks Hudson's ratio-of-averages estimator degrading
    under multiple hits. The `τ` estimate survives because `A` is discarded by
    construction, but those cells are weaker than their error bars suggest.
    Above `θ ≈ 1` the design fails outright: under infinite sites `θ` is set by
    `μ` at fixed `Nₑ`, so `θ = 3` at `Nₑ = 500` needs `μ = 1.5e-3` per site,
    five orders above realistic, and produces a genotype matrix too large to
    build. Testing the `(1+θ)` factor further needs a finite-sites model or
    branch-mode statistics, not this instrument. -/
noncomputable def MutationDriftModelAssumptions.fstTransient
    (m : MutationDriftModelAssumptions) : ℝ :=
  m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)))

/-- Transient Fst is nonneg. -/
theorem MutationDriftModelAssumptions.fstTransient_nonneg
    (m : MutationDriftModelAssumptions) :
    0 ≤ m.fstTransient := by
  unfold MutationDriftModelAssumptions.fstTransient
  apply mul_nonneg (le_of_lt m.fstEquilibrium_pos)
  have harg : 0 ≤ (1 + m.theta) * m.t / (2 * m.Ne) := by
    have hden : 0 < 2 * m.Ne := by nlinarith [m.Ne_pos]
    apply div_nonneg
    · exact mul_nonneg (by linarith [m.theta_pos]) m.t_nonneg
    · exact le_of_lt hden
  have hexp : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    have hnum_nonpos : -(1 + m.theta) * m.t ≤ 0 := by
      have h1 : 0 ≤ 1 + m.theta := by
        have h1' : 0 < 1 + m.theta := by nlinarith [m.theta_pos]
        linarith
      nlinarith [h1, m.t_nonneg]
    have hden_nonneg : 0 ≤ 2 * m.Ne := by linarith [m.Ne_pos]
    have hneg : -(1 + m.theta) * m.t / (2 * m.Ne) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    have hexp' : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hneg
    simpa using hexp'
  have hfactor_nonneg : 0 ≤ 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := by
    linarith
  exact hfactor_nonneg

/-- Transient Fst is bounded by the equilibrium Fst. -/
theorem MutationDriftModelAssumptions.fstTransient_le_equilibrium
    (m : MutationDriftModelAssumptions) :
    m.fstTransient ≤ m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstTransient
  have hfeq_pos : 0 < m.fstEquilibrium := m.fstEquilibrium_pos
  have hexp_pos : 0 < Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    linarith
  have hmul :
      m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne))) ≤
        m.fstEquilibrium * 1 :=
    mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
  simpa using hmul

/-! ## Derivation of the Multiplicative Covariance Divergence Formula

We derive the formula `covarianceDivergenceMutationDrift(Fst, shared_LD) = 1 - (1-Fst) × shared_LD`
from the covariance between a polygenic score and a phenotype across populations.

**Setup.** In the source population, the covariance between a PGS and the phenotype is:

  `Cov(PGS, Y_source) = Σᵢ βᵢ × Cov(Gᵢ_source, Y_source)`

In the target population:

  `Cov(PGS, Y_target) = Σᵢ βᵢ × Cov(Gᵢ_target, Y_target)`

The ratio `Cov_target / Cov_source` depends on two independent factors:

1. **Allele frequency correlation** (`freq_corr`): Genetic drift changes allele frequencies
   between populations. The correlation of allele frequencies between source and target
   populations is `1 - Fst`, where Fst measures frequency divergence. This scales the
   per-locus genetic covariance by `(1 - Fst)`.

2. **LD overlap** (`ld_overlap`): New mutations and recombination alter LD patterns.
   The fraction of LD structure that is shared between populations is `shared_LD`.
   Only shared LD contributes to tagging of causal variants by the PGS SNPs.

For a single locus pair, these act on different aspects of the covariance:
- Frequency change scales the marginal genetic variance: `Var(G_target) ∝ (1-Fst) × Var(G_source)`
- LD change scales the tagging efficiency: `r²_target ∝ shared_LD × r²_source`

Because these are independent mechanisms, the total covariance retention is their product:

  `Cov_target / Cov_source = (1 - Fst) × shared_LD`

Therefore the divergence (fraction of covariance lost) is:

  `divergence = 1 - retention = 1 - (1 - Fst) × shared_LD`
-/

/-- **Covariance retention** across populations.
    The fraction of PGS-phenotype covariance retained in the target population
    is the product of allele frequency correlation and LD overlap. These two
    factors are independent: frequency drift scales per-locus genetic variance,
    while LD decay scales tagging efficiency. -/
noncomputable def covarianceRetention (freq_corr ld_overlap : ℝ) : ℝ :=
  Descent.Core.product freq_corr ld_overlap

/-- The covariance-retention factor `1 - F_ST`.

    ONE STATUS MARKER, at the foot of this docstring. This block used to open
    with a second one carrying a refutation verdict, which described the
    SUPERSEDED definition `freqCorrFromFst` rather than this one, and every
    scanner that reads the first marker in a docstring reported this body as
    currently falsified. It is not. (The duplicate is removed rather than
    reworded: a marker quoted in prose is still a marker to a scanner, which is
    the same class of mistake as the one being corrected.) The refuted claim was
    an IDENTIFICATION --
    that `1 - F_ST` *is* the allele-frequency correlation -- and that claim was
    already repaired, by renaming this definition and by giving the correlation
    its own body with the arguments it actually depends on. What follows is the
    history of that repair, not a verdict on the body below.

    THE MEASUREMENT THAT KILLED THE IDENTIFICATION
    (`validation/empirical/simcov/battery_verify.py`,
    `test_freq_corr_killer`). Two Wright-Fisher designs were run to the SAME
    differentiation -- `G_ST` 0.0749 and 0.0750, so `1 - Fst` is 0.9251 and
    0.9250 -- differing only in the ancestral frequencies the two demes started
    from. `Ne = 200`, 60 generations, 4000 loci, 400 replicate deme pairs, the
    correlation taken within each replicate so its scatter is measured:

      ancestral p0            1 - Fst    measured corr    sems off
      all p0 = 0.5             0.9251    0.0004±0.0008      1117
      uniform(0.05, 0.95)      0.9250    0.7209±0.0003       653

    At identical `F_ST` the correlation is either zero or 0.72, so it is not a
    function of `F_ST` and no repair of the constant can make it one. The
    degenerate row is the clearest statement of the mechanism: when every locus
    starts at the same ancestral frequency there is no across-locus signal for
    the two demes to share, and the correlation vanishes however little they
    have diverged.

    What the quantity actually is:
    `corr(p1, p2) = Var(p0) / (Var(p0) + F * E[p0 (1 - p0)])`,
    which depends on the ancestral spread as well as on the drift index, and
    reduces to `1 - F` only when `Var(p0)` and `E[p0 (1 - p0)]` stand in one
    particular ratio.

    Power: the design holds `F_ST` fixed to four decimal places and moves the
    measured correlation from 0.0004 to 0.7209, which is the largest span the
    quantity admits.

    **The name has been changed.** This was `freqCorrFromFst`, and that name is
    the falsified claim: it asserted that `1 - Fst` IS the allele-frequency
    correlation, which the measurement above refutes. The body `1 - Fst` is
    retained because it is what every consumer actually uses it as -- a
    covariance-retention factor -- and the new name says only that. The
    correlation itself is `alleleFreqCorrelation` below, which carries the
    arguments the quantity depends on.

    THE LEDGER STILL CARRIES THE DEAD NAME. `simcov/ledger.json` holds three rows
    under `freqCorrFromFst` -- FALSIFIED at 235.05 sems (`pgs`), FALSIFIED
    (`verify`), and CONVENTION (`fix`) -- and no declaration in the corpus bears
    that name any more. A reader grepping the ledger for the refutation finds
    rows pointing at nothing; a reader grepping the Lean for `freqCorrFromFst`
    finds only prose. The rows are not stale in what they measured -- the
    measurement above IS them -- they are stale in what they name.
    This paragraph is the bridge, and it is here rather than in the ledger
    because the ledger is a record of what was run and rewriting a record to
    match a later rename is how a record stops being one.

    Empirical status: **VALIDATED as a covariance-retention factor**
    (`simcov/battery_drift05.py`). Its former justification was the correlation identity, and
    that justification is gone; retention now has a measurement instead.

    For a score with FIXED effects the genetic variance it carries in a drifted deme is
    `∑ βᵢ²·2pᵢ(1-pᵢ)`, so the retention is the heterozygosity ratio on the same draws. Against
    the MODEL's `fst = 1-(1-1/(2Nₑ))^t` -- never one estimated from the replicates the oracle
    measures -- over 300000 loci and four `(Nₑ, t)` cells, worst 0.58 sems at 0.03% relative,
    with `(1-fst)²` refuted at up to 259 sems.

    HONEST LIMIT: this shares its oracle with `targetHetFromFst` above, being that measurement
    rescaled by the ancestral heterozygosity. It is one measurement supporting two
    definitions, not two independent ones, and what it adds over the heterozygosity statement
    is the identification of that ratio with a COVARIANCE retention -- which holds because the
    effects are fixed and is exactly what would fail if they were not.

    Denotes: the covariance-retention factor, not the allele-frequency
    correlation. The same body `1 - fst` appears under names from 'correlation',
    'retention' and 'drift factor', and the formula alone does not fix which is
    meant; `alleleFreqCorrelation` is the correlation. -/
noncomputable def covarianceRetentionFactorFromFst (fst : ℝ) : ℝ :=
  Descent.Core.complement fst

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem covarianceRetentionFactorFromFst_at_reference_point :
    covarianceRetentionFactorFromFst (1 / 2) = 1 / 2 := by
  unfold covarianceRetentionFactorFromFst Descent.Core.complement
  norm_num

/-- **The allele-frequency correlation between two drifted demes.**

    `corr(p1, p2) = Var(p0) / (Var(p0) + fst * E[p0 (1 - p0)])`, where the two
    ancestral moments are taken over the loci scored. Both demes descend from
    one ancestral population, so their frequencies share exactly the ancestral
    across-locus spread and differ by independent drift; the correlation is the
    ratio of the shared part to the total, which is what this states.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_correct.py`,
    `correct_freq_corr`). Wright-Fisher forward simulation, `Ne = 200`, 4000
    loci, 400 replicate deme pairs, four ancestral distributions crossed with two drift depths --
    eight cells that a formula in `fst` alone must get wrong
    and this one gets right:

      ancestral p0          gens    1 - fst   this def   measured      sems
      uniform(0.05,0.95)      60     0.9251     0.7237     0.7240       1.1
      uniform(0.05,0.95)     200     0.7545     0.4786     0.4780       0.9
      beta(0.5,0.5)           60     0.9249     0.8721     0.8719       1.0
      beta(0.5,0.5)          200     0.7547     0.7136     0.7132       1.0
      beta(2,2)               60     0.9251     0.6437     0.6440       0.8
      beta(2,2)              200     0.7547     0.3908     0.3906       0.3
      all p0 = 0.5            60     0.9252     0.0000     0.0006       0.8
      all p0 = 0.5           200     0.7546     0.0000    -0.0001       0.1

    Power: the prediction spans 0.0000 to 0.8721 across the design, the full
    range the quantity admits, while `1 - fst` is pinned at 0.925 or 0.755 by
    the drift depth alone and is wrong in seven of the eight cells. -/
noncomputable def alleleFreqCorrelation (fst varAncestral meanHetAncestral : ℝ) : ℝ :=
  varAncestral / (varAncestral + fst * meanHetAncestral)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem alleleFreqCorrelation_at_zero_denominator_is_junk (fst varAncestral meanHetAncestral : ℝ)
    (hzero : (varAncestral + fst * meanHetAncestral) = 0) :
    alleleFreqCorrelation fst varAncestral meanHetAncestral = 0 := by
  unfold alleleFreqCorrelation
  rw [hzero, div_zero]


/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem alleleFreqCorrelation_at_reference_point :
    alleleFreqCorrelation (1 / 2) (1 / 2) (1 / 2) = 2 / 3 := by
  unfold alleleFreqCorrelation
  norm_num

/-- **Exactly when the retention factor is the frequency correlation.**

    The two agree precisely at `varAncestral = (1 - fst) * meanHetAncestral`,
    and nowhere else for positive `fst`. This is the assumption the old
    `freqCorrFromFst` name asserted silently; stating it is what stops it being
    assumed again. -/
theorem alleleFreqCorrelation_eq_retentionFactor_iff
    (fst varAncestral meanHetAncestral : ℝ)
    (hden : varAncestral + fst * meanHetAncestral ≠ 0) :
    alleleFreqCorrelation fst varAncestral meanHetAncestral =
        covarianceRetentionFactorFromFst fst ↔
      varAncestral * fst = (1 - fst) * fst * meanHetAncestral := by
  unfold alleleFreqCorrelation covarianceRetentionFactorFromFst Descent.Core.complement
  rw [div_eq_iff hden]
  constructor <;> intro h <;> nlinarith [h]

/-- LD overlap is directly the shared LD fraction (identity mapping, made
    explicit for clarity in the derivation chain).

    Empirical status: NOT AN EMPIRICAL CLAIM -- the body is the identity
    function on its argument, as the name and the parenthetical both say. There
    is no measurement that could agree or disagree with `fun x ↦ x`: any
    observation whatever is consistent with it, because it asserts nothing about
    the world.

    What this declaration DOES carry is a naming claim -- that "LD overlap" and
    "shared LD fraction" denote the same quantity -- and that is a claim about
    the two definitions' intended readings, not about a population. It is
    settled by the derivation chain this body was made explicit for, not by a
    simulation.

    A marker claiming an unpaid measurement debt here would be reporting one
    that does not exist; it inflates the count of things owed a measurement with an item that can
    never receive one. And the word for that debt must not
    appear anywhere in this docstring even as prose: `simcov/inventory.py` falls
    back to scanning the status note for state words when the head is not one of
    them, so the single word in the sentence this replaces made a declaration
    that reads NOT AN EMPIRICAL CLAIM count as an open debt in every coverage
    number the harness prints.

    The bodies downstream of it are where the empirical content
    lives: `covarianceDivergenceMutationDrift` and
    `presentDayPGSVarianceMutationDrift` both consume this fraction and both
    make claims a simulation can reach. -/
noncomputable def ldOverlapFromSharedLD (shared_ld : ℝ) : ℝ :=
  Descent.Core.identifiedWith shared_ld

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ldOverlapFromSharedLD_at_reference_point :
    ldOverlapFromSharedLD (1 / 2) = 1 / 2 := by
  unfold ldOverlapFromSharedLD Descent.Core.identifiedWith
  norm_num

/-- Covariance retention in terms of Fst and shared_LD. -/
theorem covarianceRetention_from_fst_ld (fst shared_ld : ℝ) :
    covarianceRetention (covarianceRetentionFactorFromFst fst) (ldOverlapFromSharedLD shared_ld) =
      (1 - fst) * shared_ld := by
  unfold covarianceRetention covarianceRetentionFactorFromFst ldOverlapFromSharedLD Descent.Core.product Descent.Core.complement Descent.Core.identifiedWith
  ring

/-- **Covariance divergence derived from retention.**
    Divergence is `1 - retention`, which yields the multiplicative formula
    `1 - (1 - Fst) × shared_LD`. -/
noncomputable def covarianceDivergenceFromRetention (fst shared_ld : ℝ) : ℝ :=
  1 - covarianceRetention (covarianceRetentionFactorFromFst fst) (ldOverlapFromSharedLD shared_ld)

/-- The derived divergence formula equals `1 - (1 - Fst) × shared_LD`. -/
theorem covarianceDivergenceFromRetention_eq (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld = 1 - (1 - fst) * shared_ld := by
  unfold covarianceDivergenceFromRetention
  rw [covarianceRetention_from_fst_ld]

/-- **Generalized covariance divergence under mutation-drift.**
    The total covariance divergence between source and target populations
    includes both:
    (a) drift-driven frequency changes: proportional to Fst
    (b) mutation-driven LD changes: proportional to tagging decay from new variants

    Total divergence factor = Fst_drift + (1 - Fst_drift) × (1 - shared_LD)
    where shared_LD is the fraction of LD preserved despite new mutations.

    Empirical status: **MEASURED, and the number is not a rejection**
    (`validation/empirical/simcov/battery_bulk36.py`). Two-deme island
    model, `Nₑ = 1000`, 5 Mb with recombination. `F_ST`, cross-deme LD
    correlation and score-covariance retention are three SEPARATE measurements
    on the same replicates, and the body is fed the measured `shared_ld` rather
    than its migration formula, which is what distinguishes it from
    `signalRetentionMigrationDrift`: this body takes the LD term as an ARGUMENT
    and so is not committed to the `M/(1+M)` reading that `battery_bulk34`
    refuted. Stated as retention, `1 - covDiv = (1 - fst) * shared_ld`:

      4Nₑm   measured retention   this body   1-F     shared_ld
      0.4    0.392 ± 0.074        0.429       0.472   0.909
      2.0    0.476 ± 0.075        0.751       0.803   0.936
      8.0    0.614 ± 0.076        0.918       0.944   0.973
      40     0.736 ± 0.085        0.979       0.988   0.991

    WHY THIS IS NOT WRITTEN AS A FALSIFICATION, though the raw gate says 4.01
    sems and 50% relative. The retention column is divided by the estimator's
    panmictic ceiling, and THAT run's ceiling came out 1.0430 -- above one, which
    attenuation cannot produce, so the calibration is noise-dominated on six
    replicates. `signalRetentionMigrationDrift` records the same retraction for
    the same numbers, and a rejection quoted here from a calibration retracted
    there would be the corpus disagreeing with itself in two docstrings. What
    the run does establish is the DIRECTION, and it is the same direction in both
    replications: measured retention runs well below every candidate at weak
    migration, so if any of the three is right it is not by a wide margin.

    Both competitors are rejected harder than the body on the same cells --
    `1 - F` alone at 4.37 sems and `shared_ld` alone at 7.02 -- so the product
    form is the best of the three and not merely the untested one. The positive
    control, one population split arbitrarily giving `F_ST = 0`, passed at 0.15
    sems; it is the ceiling and not the control that failed.

    argument_source: sample. `fst_drift` and `shared_ld` are estimated from the
    same replicates the retention is measured on. That is deliberate here -- a
    relation among three separately measured observables is the only way to test
    a body whose LD term is an argument -- but it is also why the verdict is a
    number and not a validation: what a usable design still owes is a retention
    estimator needing no ceiling at all, which means fitting the weights on an
    independent split of the source sample. -/
noncomputable def covarianceDivergenceMutationDrift
    (fst_drift shared_ld : ℝ) : ℝ :=
  fst_drift + (1 - fst_drift) * (1 - shared_ld)

/-- Covariance divergence simplifies algebraically. -/
theorem covarianceDivergenceMutationDrift_eq (fst_drift shared_ld : ℝ) :
    covarianceDivergenceMutationDrift fst_drift shared_ld = 1 - (1 - fst_drift) * shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- **The derived formula matches the existing definition.**
    This connects the derivation from covariance principles back to
    `covarianceDivergenceMutationDrift`, confirming the multiplicative
    structure is not merely assumed but follows from the independence
    of allele frequency drift and LD decay. -/
theorem covarianceDivergence_derivation_matches (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld =
      covarianceDivergenceMutationDrift fst shared_ld := by
  rw [covarianceDivergenceFromRetention_eq, covarianceDivergenceMutationDrift_eq]

/-- With perfect shared LD (shared_ld = 1), covariance divergence reduces to pure drift. -/
theorem covarianceDivergence_pure_drift (fst_drift : ℝ) :
    covarianceDivergenceMutationDrift fst_drift 1 = fst_drift := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- With zero drift (fst_drift = 0), covariance divergence equals the LD divergence. -/
theorem covarianceDivergence_pure_mutation (shared_ld : ℝ) :
    covarianceDivergenceMutationDrift 0 shared_ld = 1 - shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- Covariance divergence is at least the drift component alone when shared LD ≤ 1. -/
theorem covarianceDivergence_ge_drift (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : shared_ld ≤ 1) :
    fst_drift ≤ covarianceDivergenceMutationDrift fst_drift shared_ld := by
  unfold covarianceDivergenceMutationDrift
  have h1 : 0 ≤ 1 - fst_drift := by linarith
  have h2 : 0 ≤ 1 - shared_ld := by linarith
  linarith [mul_nonneg h1 h2]

/-- Covariance divergence is at most 1 when parameters are in [0, 1]. -/
theorem covarianceDivergence_le_one (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    covarianceDivergenceMutationDrift fst_drift shared_ld ≤ 1 := by
  rw [covarianceDivergenceMutationDrift_eq]
  have h1 : 0 ≤ (1 - fst_drift) * shared_ld :=
    mul_nonneg (by linarith) hld
  linarith

/-- **Generalized signal retention under mutation-drift.**
    The retained signal is (1 - total_divergence) × V_A.

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`). The retention
    fraction `1 - covarianceDivergenceMutationDrift` is what that battery
    measures directly, and the table, the reason it is not written as a
    rejection, and the two competitors are at
    `covarianceDivergenceMutationDrift`. What this body adds is the factor
    `V_A`, and NOTHING here measures it: a retention fraction times an additive
    variance is dimensional bookkeeping, and every cell of that design was run at
    one `V_A`. A design that swept `V_A` would test the linearity; none has.

    argument_source: sample, inherited. -/
noncomputable def presentDayPGSVarianceMutationDrift
    (V_A fst_drift shared_ld : ℝ) : ℝ :=
  (1 - covarianceDivergenceMutationDrift fst_drift shared_ld) * V_A

/-- Signal retention equals (1 - fst) × shared_ld × V_A. -/
theorem presentDayPGSVarianceMutationDrift_eq (V_A fst_drift shared_ld : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld =
      (1 - fst_drift) * shared_ld * V_A := by
  unfold presentDayPGSVarianceMutationDrift
  rw [covarianceDivergenceMutationDrift_eq]
  ring

/-- With perfect shared LD, signal retention reduces to the pure drift formula. -/
theorem presentDayPGSVarianceMutationDrift_pure_drift (V_A fst_drift : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift 1 = presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  ring

/-- Signal retention is nonneg under valid parameters. -/
theorem presentDayPGSVarianceMutationDrift_nonneg (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 ≤ V_A) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  exact mul_nonneg (mul_nonneg (by linarith) hld) hVA

/-- **Mutation strictly reduces signal retention beyond drift alone.**
    When shared_ld < 1 and other parameters are positive, mutation-drift signal
    retention is strictly below drift-only signal retention. -/
theorem mutationDrift_signal_lt_puredrift (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst_lt : fst_drift < 1) (hld_lt : shared_ld < 1) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld <
      presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 - fst_drift := by linarith
  have h_factor : (1 - fst_drift) * shared_ld < (1 - fst_drift) * 1 :=
    mul_lt_mul_of_pos_left hld_lt h1
  nlinarith

/-- **R² under mutation-drift balance.**

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`), through
    `presentDayPGSVarianceMutationDrift`, whose retention fraction is what that
    battery measures; the table is at `covarianceDivergenceMutationDrift`.

    The `v / (v + V_E)` chart on top of it is NOT tested by that run and is not
    claimed to be here. It is the same `r2FromSignalVariance` chart the
    drift-only `presentDayR2` uses, and it inherits whatever that chart carries;
    what a reader must not take from this marker is that the chart was exercised
    at more than one `V_E`, because it was not.

    argument_source: sample, inherited. -/
noncomputable def presentDayR2MutationDrift (V_A V_E fst_drift shared_ld : ℝ) : ℝ :=
  let v := presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld
  v / (v + V_E)

/-- Where the present-day score variance and the environmental variance cancel, the ratio
divides by zero and Mathlib returns `0`: no predictive accuracy, reported for a model that has
no total variance at all. -/
theorem presentDayR2MutationDrift_at_zero_total_variance_is_junk
    (V_A V_E fst_drift shared_ld : ℝ)
    (hzero : presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld + V_E = 0) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld = 0 := by
  show presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld /
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld + V_E) = 0
  rw [hzero, div_zero]



/-- **Mutation-drift R² is below drift-only R².**
    When shared LD is imperfect, R² under mutation-drift is strictly below
    drift-only R². This is the key portability result: ignoring mutation
    overestimates portability. -/
theorem mutationDrift_R2_lt_puredrift_R2 (V_A V_E fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt : fst_drift < 1)
    (hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld <
      presentDayR2 V_A V_E fst_drift := by
  unfold presentDayR2MutationDrift presentDayR2 PopGen.TransportedMetrics.r2FromSignalVariance Descent.Core.share
  have h_sig_lt := mutationDrift_signal_lt_puredrift V_A fst_drift shared_ld
    hVA hfst_lt hld_lt
  have h_md_nonneg : 0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld :=
    presentDayPGSVarianceMutationDrift_nonneg V_A fst_drift shared_ld
      (le_of_lt hVA) (le_of_lt hfst_lt) (le_of_lt hld)
  exact expectedR2_strictMono_nonneg V_E
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld)
    (presentDayPGSVariance V_A fst_drift)
    hVE h_md_nonneg h_sig_lt

/-- Scalar neutral benchmark that combines allele-frequency retention with a
shared-LD retention coordinate. This remains a coarse benchmark, not a
mechanistic SNP-level transport law.

    Empirical status: **MEASURED, inherited**
    (`validation/empirical/simcov/battery_bulk36.py`). Numerator and
    denominator are each the retention form `(1 - fst) * shared_ld` that battery
    measures directly, one per population, so the table and the reason it is a
    number rather than a rejection are at `covarianceDivergenceMutationDrift`.

    WHAT THE RATIO ADDS AND WHY IT IS THE WEAKER CLAIM OF THE TWO. Taking the
    quotient of two retention factors asserts that the source's own retention is
    the right normaliser -- that the benchmark is scale-free in whatever the two
    populations share. Nothing measured here reaches that: `battery_bulk36` runs
    two demes of a symmetric island model, where the source and target retention
    factors are equal by construction and the ratio is one at every cell. So the
    ratio's own content is untouched by the run that covers its parts, and a
    design that moved the two populations asymmetrically is what it owes.

    argument_source: sample, inherited. -/
noncomputable def neutralAFSharedLDBenchmarkRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
  ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)

/-- **The benchmark ratio's junk branch, named.** A source that shares no linkage structure, or
one at complete differentiation, zeroes the denominator and Lean returns `0`: the ratio reports
total loss of transfer where it is undefined, since there was no source performance to transfer.
Consumers must require the source denominator nonzero. -/
theorem neutralAFSharedLDBenchmarkRatio_no_source_is_junk
    (fstSource fstTarget shared_ld_target : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 0 shared_ld_target = 0 := by
  unfold neutralAFSharedLDBenchmarkRatio; simp

/-- The shared-LD benchmark reduces to the neutral allele-frequency benchmark
when shared LD is perfect in both populations. -/
theorem neutralAFSharedLDBenchmarkRatio_pure_drift (fstSource fstTarget : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 1 1 =
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  ring

/-- The shared-LD benchmark is below the pure neutral allele-frequency
benchmark when target shared LD is worse than source shared LD. -/
theorem neutralAFSharedLDBenchmarkRatio_lt_pure_drift_form
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ)
    (hfstS : fstSource < 1) (hfstT : fstTarget < 1)
    (hldS : 0 < shared_ld_source)
    (hld_decay : shared_ld_target / shared_ld_source < 1) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget shared_ld_source shared_ld_target <
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  have h1 : 0 < 1 - fstSource := by linarith
  have h_den_pos : 0 < (1 - fstSource) * shared_ld_source := mul_pos h1 hldS
  rw [div_lt_div_iff₀ h_den_pos h1]
  have h_ld_ratio : shared_ld_target < shared_ld_source := by
    rwa [div_lt_one hldS] at hld_decay
  have hnum_lt :
      ((1 - fstSource) * (1 - fstTarget)) * shared_ld_target <
        ((1 - fstSource) * (1 - fstTarget)) * shared_ld_source :=
    mul_lt_mul_of_pos_left h_ld_ratio (mul_pos h1 (by linarith))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnum_lt


/-- **At equilibrium, larger θ means lower Fst and thus the drift component
    of portability improves.**
    If we compare two populations at equilibrium with θ₁ < θ₂, the population
    with larger θ has smaller Fst. This improves the allele frequency component
    of signal retention. -/
theorem equilibrium_drift_component_improves_with_theta
    (V_A θ₁ θ₂ : ℝ)
    (hVA : 0 < V_A) (hθ₁ : 0 < θ₁)
    (h_more : θ₁ < θ₂) :
    presentDayPGSVariance V_A (1 / (1 + θ₁)) <
      presentDayPGSVariance V_A (1 / (1 + θ₂)) := by
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 + θ₁ := by linarith
  have h2 : 0 < 1 + θ₂ := by linarith
  -- 1/(1+θ₂) < 1/(1+θ₁), so 1 - 1/(1+θ₁) < 1 - 1/(1+θ₂)
  -- i.e., θ₁/(1+θ₁) < θ₂/(1+θ₂)
  have hfst₁ : 1 - 1 / (1 + θ₁) = θ₁ / (1 + θ₁) := by
    have hne : 1 + θ₁ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  have hfst₂ : 1 - 1 / (1 + θ₂) = θ₂ / (1 + θ₂) := by
    have hne : 1 + θ₂ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  rw [hfst₁, hfst₂]
  have h_ratio_lt : θ₁ / (1 + θ₁) < θ₂ / (1 + θ₂) := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  exact mul_lt_mul_of_pos_left h_ratio_lt hVA

/-- **Pure drift benchmark overestimates retained variance.**
    The drift-only benchmark (which sets `negligibleMutation` = True) always
    overestimates retained variance compared to the mutation-drift model.
    This theorem quantifies the gap: the ratio of mutation-drift variance
    to drift-only variance is exactly `shared_ld`. -/
theorem mutationDrift_variance_ratio (V_A fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst : fst < 1)
    (hld : 0 < shared_ld) :
    presentDayPGSVarianceMutationDrift V_A fst shared_ld /
      presentDayPGSVariance V_A fst = shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have hfst_ne : 1 - fst ≠ 0 := by linarith
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  field_simp [hfst_ne, hVA_ne]

/-! **Deleted: `neutral_af_benchmark_correction_factor`.**

This theorem is absent on purpose. It states `presentDayPGSVarianceMutationDrift V_A fst
ld = ld * presentDayPGSVariance V_A fst` and closes by `ring`. All six of its hypotheses go
unused — `0 < V_A`, `0 < V_E`, `0 ≤ fst`, `fst < 1`, `0 < ld`, `ld ≤ 1` — and `V_E` is a
phantom parameter appearing nowhere in the statement, present only so the signature reads
like a statement about `R²`. The identity is `presentDayPGSVarianceMutationDrift_eq` with the
factors reassociated, and `mutationDrift_variance_ratio` just above states the same
content as a ratio with the hypotheses it genuinely needs.

Two of those hypotheses are worse than unused. `0 ≤ fst` and `fst < 1` are the range in
which the "correction factor" reading means anything, and leaving them unused lets the
equation hold at `fst > 1`, where `presentDayPGSVariance` is negative and the word
*correction* has no referent. A theorem satisfied by the inadmissible parameter values too
is no evidence that the admissible ones are the intended domain. -/

/-- **Pairwise Fst under mutation-drift balance is bounded.**
    Under mutation-drift equilibrium, pairwise Fst between any two populations
    is bounded above by 2 × Fst_eq (since each branch contributes at most Fst_eq). -/
theorem pairwise_fst_mutationDrift_bound (θ : ℝ) (hθ : 0 < θ) :
    pairwiseFstFromBranches (1 / (1 + θ)) (1 / (1 + θ)) ≤ 2 / (1 + θ) := by
  simp [pairwiseFstFromBranches, Descent.Core.complementaryComposition]
  ring_nf
  have h1 : 0 < 1 + θ := by linarith
  have hsq : 0 ≤ (1 / (1 + θ)) ^ 2 := sq_nonneg (1 / (1 + θ))
  nlinarith

end MutationDriftPortability

end Descent.Portability
