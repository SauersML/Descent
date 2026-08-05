/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.OpenQuestions
import Descent.Core.Fst
import Descent.Core.Heterozygosity
import Descent.PopGen.PopulationGeneticsFoundations.FstDefinitions

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.CoalescentTheory`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Coalescent Theory and Heterozygosity

The coalescent provides the theoretical framework for understanding
genetic variation and differentiation.
-/

section CoalescentTheory

/-- **Expected heterozygosity from mutation-drift balance.**
    H = 4Neμ / (1 + 4Neμ) = θ / (1 + θ) where θ = 4Neμ. -/
noncomputable def expectedHeterozygosity (θ : ℝ) : ℝ :=
  θ / (1 + θ)

/-- **expectedHeterozygosity at `θ = -1`, named.** A negative scaled mutation rate is
inadmissible. The divisor vanishes at `θ = -1` and the expected heterozygosity is `0` -- a
monomorphic locus, which is a perfectly ordinary answer and therefore invisible. Consumers must
exclude it by hypothesis. -/
theorem expectedHeterozygosity_negative_unit_theta_is_junk :
    expectedHeterozygosity (-1) = 0 := by
  unfold expectedHeterozygosity
  norm_num

/-- **At unit scaled mutation rate the population is half heterozygous.** The membership in
`[0,1)` recorded below holds for every increasing map into that interval; the value at `θ = 1`
fixes which one, and it is the calibration point that distinguishes `θ/(1+θ)` from any other
saturating form. -/
theorem expectedHeterozygosity_at_one : expectedHeterozygosity 1 = 1 / 2 := by
  unfold expectedHeterozygosity
  norm_num

/-- Expected heterozygosity is in [0, 1). -/
theorem expected_het_in_unit (θ : ℝ) (h_θ : 0 ≤ θ) :
    0 ≤ expectedHeterozygosity θ ∧ expectedHeterozygosity θ < 1 := by
  unfold expectedHeterozygosity
  constructor
  · exact div_nonneg h_θ (by linarith)
  · rw [div_lt_one (by linarith : 0 < 1 + θ)]
    linarith

/-- **Heterozygosity increases with effective population size.**
    Larger Ne → more mutations retained → higher diversity. -/
theorem het_increases_with_ne
    (θ₁ θ₂ : ℝ) (h₁ : 0 < θ₁) (h_more : θ₁ < θ₂) :
    expectedHeterozygosity θ₁ < expectedHeterozygosity θ₂ := by
  unfold expectedHeterozygosity
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Coalescence time between populations.**
    For two populations separated t generations ago:
    E[T_between] = t + 2Ne, E[T_within] = 2Ne.
    Fst = 1 - T_within / T_between = t / (t + 2Ne).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_fix.py`,
    `test_fst_composition`). msprime coalescent simulation of a clean split with no migration, ancestral and both daughter sizes `Ne = 1000`, recombining at
    `1e-8` so a replicate carries many independent genealogies, Hudson `F_ST` as
    a ratio of averages, 25 replicates of 20 Mb, 50 diploids per deme:

      t        this def    simulated             sems
       500       0.20000   0.19923±0.00227     0.34
      1000       0.33333   0.33415±0.00319     0.25
      2000       0.50000   0.49974±0.00330     0.08

    Recombination is not optional in this design. At `recombination_rate = 0`
    every site in a replicate sits on ONE genealogy, so a 20 Mb sequence carries
    no more information about `F_ST` than a single site; two runs of this same
    demography then differed by 2.4 sems and neither error bar was usable.

    On these same runs the sibling composition that SUMS both branch taus errs
    by 51 to 59 sems. `pairwiseFstFromBranchTaus` was that body and has since
    been corrected to their MEAN, which counts the split time once; on a
    symmetric split it then reduces to this definition, which is why the two
    agree here rather than differing by half.

    Regime: symmetric split. This definition takes a single `Ne` and so says
    nothing about unequal daughter sizes; substituting a harmonic mean for an
    asymmetric split misses by 4.6 sems and is not a reading this definition
    offers.

    Power: the prediction spans 0.20000 to 0.50000 across the design, a factor
    of two and a half. -/
noncomputable def coalFst (t Ne : ℝ) : ℝ :=
  Descent.Core.oddsLike t Ne

/-- **coalFst where its denominator vanishes, named.** The guard `t + 2 * Ne` is zero at `t = 0`,
`Ne = 0`. At zero separation and zero effective size the coalescent chart is degenerate at both
ends at once. Lean returns `0` there rather than the value the modelled quantity takes, and no
type error marks the point. Consumers must require `t + 2 * Ne ≠ 0`. -/
theorem coalFst_at_t0ne0_is_junk :
    coalFst 0 0 = 0 := by
  unfold coalFst Descent.Core.oddsLike
  norm_num

/-- **One quantity, one definition.**  `coalFst` and `fstFromTau` are the same
function in generation and coalescent units.  Three formulas for this quantity
existed across three files and two were wrong; this theorem is the relation
whose absence let them disagree, and it fails to compile if either body moves. -/
theorem coalFst_eq_fstFromTau (t Ne : ℝ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    coalFst t Ne = Portability.fstFromTau (Portability.coalescentTau t Ne) := by
  have h2 : (2 : ℝ) * Ne ≠ 0 := by positivity
  have hsum : t + 2 * Ne ≠ 0 := by
    have hs : 0 < t + 2 * Ne := by linarith
    exact ne_of_gt hs
  unfold coalFst Portability.fstFromTau Portability.coalescentTau Descent.Core.fstFromTau Descent.Core.saturation Descent.Core.oddsLike
  field_simp
  ring

/-- Coalescent Fst is nonneg. -/
theorem coal_fst_nonneg (t Ne : ℝ) (h_t : 0 ≤ t) (h_Ne : 0 < Ne) :
    0 ≤ coalFst t Ne := by
  unfold coalFst Descent.Core.oddsLike
  exact div_nonneg h_t (by linarith)

/-- Coalescent Fst increases with separation time. -/
theorem coal_fst_increases_with_time
    (Ne : ℝ) (t₁ t₂ : ℝ) (h_Ne : 0 < Ne)
    (h_t₁ : 0 ≤ t₁) (h_more : t₁ < t₂) :
    coalFst t₁ Ne < coalFst t₂ Ne := by
  unfold coalFst Descent.Core.oddsLike
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Coalescent Fst approaches 1 as t → ∞ (relative to Ne). -/
theorem coal_fst_approaches_one
    (Ne t : ℝ) (h_Ne : 0 < Ne)
    (h_large : 100 * Ne < t) :
    49 / 50 < coalFst t Ne := by
  unfold coalFst Descent.Core.oddsLike
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 50) (by linarith)]
  nlinarith

end CoalescentTheory


/-!
## Effective Population Size

Ne determines the rate of genetic drift and the amount of genetic
variation. It is central to predicting portability.
-/

section EffectivePopulationSize


/-- **`V_A · t / (2 Nₑ)` decreases as `Nₑ` grows.**

    Read as drift variance of a polygenic score this says smaller effective size means faster
    drift and more variance. That the drift variance IS `V_A × F_ST` with `F_ST = t/(2Nₑ)` is
    the modelling step, supplied by writing the expression rather than derived below: no score,
    no allele frequency and no genealogy appears in the statement. -/
theorem ne_affects_pgs_variance
    (V_A t Ne₁ Ne₂ : ℝ)
    (h_VA : 0 < V_A) (h_t : 0 < t)
    (h_Ne₁ : 0 < Ne₁)
    (h_smaller : Ne₁ < Ne₂) :
    V_A * t / (2 * Ne₂) < V_A * t / (2 * Ne₁) := by
  exact div_lt_div_of_pos_left (mul_pos h_VA h_t) (by positivity) (by nlinarith)

end EffectivePopulationSize

end Descent.PopGen
