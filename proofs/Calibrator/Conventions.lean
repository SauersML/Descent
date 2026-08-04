/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PopulationGeneticsFoundations
import Calibrator.DriftRegime
import Calibrator.ImitationRigidity
import Calibrator.DemographicHistory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.PCCorrectability.Threshold
import Calibrator.AssortativeMatingPGS
import Calibrator.CovarianceStructure
import Calibrator.AncestrySpecificPower
import Calibrator.GeneticArchitectureDiscovery
import Calibrator.StatisticalGeneticsMethodology
import Calibrator.BlindnessRegistry
import Calibrator.SerialFounderChain
import Calibrator.BundleRigidity.TwoAtom
import Calibrator.LongitudinalPortability
import Calibrator.ImputationPortability
import Calibrator.SimulationValidation
import Calibrator.LDDecayTheory
import Calibrator.MetricSpecificPortability
import Calibrator.PhenomeWidePortability
import Calibrator.ScoreDistribution
import Calibrator.EpistasisAndNonAdditivity
import Calibrator.VarianceComponents
import Calibrator.PowerAnalysis
import Calibrator.SelectionArchitecture
import Calibrator.PolygenicAdaptation
import Calibrator.AncestryCalibration
import Calibrator.PortabilityBounds
import Calibrator.CovarianceStructure
import Calibrator.HaplotypeTheory
import Calibrator.LongitudinalPortability
import Calibrator.ImputationPortability
import Calibrator.SimulationValidation
import Calibrator.PortabilityDrift
import Calibrator.StratificationConfounding
import Calibrator.PolygenicArchitecture
import Calibrator.TransferLearningPGS

namespace Calibrator

/-!
# Identifications: making a named quantity carry its obligation

A Lean `def` cannot be wrong internally, so the entire risk of this
development sits in one place: a definition whose *name* claims a
population-genetic meaning that its *formula* does not have. Every theorem
downstream is then machine-checked and misleading. Two instances have now been
found by simulation rather than by proof.

`demographicSpike` carried the wrong constant, `2 F m_eff` where the data give
`3.9920 ± 0.0045`. A cross-check between two independently written formulas
would have caught it, and `four_neiGst_eq_standardizedContrastVariance`
below is that cross-check.

`singletonProportion N₀ N₁ = 1 - log N₀ / log N₁` was worse, and no
cross-check of that kind could have caught it. It returns `0` at the null
where the truth is `0.187`, and it takes no sample size at all although the
observable moves from `0.427` to `0.368` when `n` goes from 50 to 200. The
signature cannot express the quantity. That is a type error, not an arithmetic
one, and it is invisible to any argument that only compares formulas to other
formulas.

The two failures therefore need two different mechanisms.

* Against a wrong constant: over-determination. Derive the quantity from a
  primitive so the constant is forced, and relate independently written
  formulas so that drift between them fails to compile. That is this file.

* Against a wrong signature: an obligation attached to the name. A named
  empirical quantity must be introduced together with the observable it claims
  to be, and a proof that the two agree. Then a formula that cannot depend on
  `n` cannot identify an observable that does. Claims whose signatures omit
  required variables are not exported as theorems.
-/

section Ploidy

/-- Number of homologous copies per locus. Every non-exponent factor of two in
this development traces to this constant, and every factor of four to twice
it. Forty-eight definition bodies outside this file carry such a two and
fourteen carry such a four. The theorems in this file tie the independently
written ones back here, so that drift between them is a compile error rather
than a silent disagreement. -/
noncomputable def ploidy : ℝ := 2

/-- Genotype variance at a locus in Hardy-Weinberg proportions, for dosage
coded `0, 1, …, ploidy`.

    Empirical status: UNTESTED. -/
noncomputable def hweGenotypeVariance (p : ℝ) : ℝ := ploidy * p * (1 - p)

/-- **The genotype variance peaks at even allele frequency and is exactly one half there.** With
diploid ploidy the value at `p = 1/2` is `2 · (1/2) · (1/2) = 1/2`. The vanishing at the two
fixed points is shared by every multiple of `p(1-p)`; the value at the interior maximum fixes the
ploidy factor, which is the only free constant in the formula. -/
theorem hweGenotypeVariance_at_half : hweGenotypeVariance (1 / 2) = 1 / 2 := by
  unfold hweGenotypeVariance ploidy
  norm_num

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations.

    Empirical status: UNTESTED. -/
noncomputable def coalescentTimeScale (Ne : ℝ) : ℝ := ploidy * Ne

@[simp] theorem coalescentTimeScale_eq (Ne : ℝ) :
    coalescentTimeScale Ne = 2 * Ne := by
  unfold coalescentTimeScale ploidy; ring

/-- **Cross-check: the scaled mutation rate in `PopulationGeneticsFoundations`
is twice the coalescent time scale times the mutation rate**, rather than an
independently chosen `4`. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    scaledMutationRate Ne mu = 2 * ploidy * Ne * mu := by
  unfold scaledMutationRate ploidy; ring

/-- **Cross-check: the scaled migration rate in `PortabilityDrift` uses the
same convention.** These two were written in different files, each spelling
out its own `4`. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    scaledMigrationRate Ne m = 2 * ploidy * Ne * m := by
  unfold scaledMigrationRate ploidy; ring

/-- **Cross-check: `heterozygosityLossFromDrift` uses the coalescent time scale**, so the
`2 Nₑ` inside it is the same `ploidy · Nₑ` and not a separate choice.

The name of this theorem calls that body "the drift `F_ST`", and `DriftRegime` names
precisely that reading as the defect: a within-population heterozygosity loss and a
between-population variance ratio are different quantities, and the shared body is what
let one be substituted for the other. What is pinned here is the constant. The regime is
pinned separately, by
`heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` at the end of this file. -/
theorem fstFromDrift_uses_coalescentTimeScale (t : ℕ) (Ne : ℝ) :
    heterozygosityLossFromDrift t Ne = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold heterozygosityLossFromDrift; rw [coalescentTimeScale_eq]

/-- **Cross-check: the within-deme coalescence time carries the same two.**
`PortabilityDrift.twoDemeIMEquilibriumETss` is `2` in units of `Nₑ`
generations, and that two is the ploidy: `E[T_within] = ploidy · Nₑ`
generations is `coalescentTimeScale`, which is `2 Nₑ`. Writing the constant
without saying so left a bare numeral in an equilibrium; this theorem says
which two it is. -/
theorem twoDemeIMEquilibriumETss_eq_ploidy (M : ℝ) :
    twoDemeIMEquilibriumETss M = ploidy := by
  unfold twoDemeIMEquilibriumETss ploidy; ring

end Ploidy

section Differentiation

/-- Mean allele frequency across two subgroups of equal weight.

    Empirical status: UNTESTED. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ := (p₁ + p₂) / 2

/-! ### The arithmetic mean of two, shared with the migration rates

`meanAlleleFreq` averages two subgroup allele frequencies and
`effectiveSymmetricMigration` averages two directional migration rates: two different
quantities sharing one map, with an equal-weight convention that has to be the same
convention in both or the `F_ST` they feed disagrees with itself.

They are deliberately *not* collapsed into one definition. The bodies coincide, but an
allele frequency and a migration rate are not the same quantity, and a single name would
let a proof about one be applied to the other without anything failing. The theorem below
records the coincidence, which is what a shared convention deserves — as against the
island-model `F_ST`, where four names really did denote one quantity and are now one. -/

/-- **The mean allele frequency is unweighted, pinned.** The identity with the symmetric
migration map constrains the two definitions jointly. Taken alone: a fixed and an absent allele
average to one half, which fixes the two-population mean as the arithmetic midpoint. -/
theorem meanAlleleFreq_fixed_and_absent :
    meanAlleleFreq 0 1 = 1 / 2 := by
  unfold meanAlleleFreq
  norm_num

theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    effectiveSymmetricMigration m₁₂ m₂₁ = meanAlleleFreq m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration meanAlleleFreq; ring

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

    Empirical status: CONVENTION IDENTIFIED and NAME CORRECTED (Nei `G_ST`). -/
noncomputable def neiGst (p₁ p₂ : ℝ) : ℝ :=
  1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
    (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

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

    Empirical status: matches `validation/differential/refs.fst_hudson`, which
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
    unfold meanAlleleFreq
    ring
  have htwo :
      2 * neiGst p₁ p₂ =
        (p₁ - p₂) ^ 2 /
          (2 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
    unfold neiGst ploidy
    field_simp [hD]
    unfold meanAlleleFreq
    ring
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
  unfold neiGst hudsonFst ploidy meanAlleleFreq
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
  unfold neiGst hudsonFst ploidy meanAlleleFreq
  norm_num

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ := (p₁ - p₂) ^ 2 / 4

/-- **The between-subgroup variance's normalisation, pinned.** The identity with the fair
two-point variance constrains the two definitions jointly and leaves a shared wrong factor free.
Two subgroups at the extremes of the frequency range have between-group variance one quarter --
the variance of a fair coin -- not one. -/
theorem betweenSubgroupVariance_extremes :
    betweenSubgroupVariance 1 0 = 1 / 4 := by
  unfold betweenSubgroupVariance
  norm_num

/-- **Cross-check: the fair two-point variance in `ImitationRigidity` is the
between-subgroup variance.** Both are `(a - b)² / 4`: the variance of a
two-point law with equal weights. One is used as a nonconcentration witness for
a resolvent and the other as the numerator of `F_ST`, and neither file knew the
other existed. -/
theorem fairTwoPointVariance_eq_betweenSubgroupVariance (a b : ℝ) :
    fairTwoPointVariance a b = betweenSubgroupVariance a b := by
  unfold fairTwoPointVariance betweenSubgroupVariance; ring

/-- **Cross-check: the heterozygosity form and the variance form of `F_ST`
agree.** The corpus contained both shapes and never related them. -/
theorem neiGst_eq_varianceRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGst p₁ p₂ =
      betweenSubgroupVariance p₁ p₂ /
        (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  have h1 : meanAlleleFreq p₁ p₂ ≠ 0 := left_ne_zero_of_mul h
  have h2 : (1 - meanAlleleFreq p₁ p₂) ≠ 0 := right_ne_zero_of_mul h
  unfold neiGst betweenSubgroupVariance ploidy
  field_simp
  unfold meanAlleleFreq
  ring

/-- **Cross-check: the two spellings of Nei's `G_ST` in this corpus agree.**

What this proves is that two independently written spellings of NEI's `G_ST`
coincide. **Neither side is Hudson's estimator.** That one is `hudsonFst`, and
`neiGst_ne_hudsonFst` exhibits a point where it differs from both of these, so
do not read either name here as Hudson's. -/
theorem neiGstFromFrequencies_eq_neiGst (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiGstFromFrequencies p₁ p₂ = neiGst p₁ p₂ := by
  rw [neiGst_eq_varianceRatio p₁ p₂ h]
  change (p₁ - p₂) ^ 2 /
      (4 * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) =
    ((p₁ - p₂) ^ 2 / 4) /
      (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))
  field_simp [h]

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
  unfold betweenSubgroupVariance
  field_simp

/-- **The allele-frequency-contrast normalization.**

This is deliberately not called the BBP spike: its input is Nei's `G_ST`, and
its interpretation is the standardized allele-frequency contrast
variance times the subgroup load.

    Empirical status: UNTESTED. -/
noncomputable def neiContrastSpike (n m p₁ p₂ : ℝ) : ℝ :=
  demographicSpike n (neiGst p₁ p₂) m

/-- **The empirically calibrated PC/BBP normalization.**

The `F` supplied to the validation experiment was the ratio-of-averages Hudson
estimator. This named specialization prevents that empirical law from being
silently reinterpreted as the different Nei functional.

    Empirical status: UNTESTED. -/
noncomputable def hudsonBbpSpike (n m p₁ p₂ : ℝ) : ℝ :=
  demographicSpike n (hudsonFst p₁ p₂) m

/-- **The Nei-normalized contrast spike has an exact observable form.** -/
theorem neiContrastSpike_eq_contrastVariance_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    neiContrastSpike n m p₁ p₂ =
      ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
        effectiveSubgroupSize n m := by
  unfold neiContrastSpike demographicSpike
  rw [← four_neiGst_eq_standardizedContrastVariance p₁ p₂ h]

/-- **The Hudson-calibrated spike expressed on the Nei scale.**

The exact conversion is nonlinear:
`4·Hudson = 8·G_ST/(1+G_ST)`. Thus the two named spike laws cannot be
reconciled by changing a global constant. In the weak-differentiation regime
the Hudson-calibrated level approaches twice the Nei contrast level. -/
theorem hudsonBbpSpike_eq_eight_neiGst_div_one_add_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonBbpSpike n m p₁ p₂ =
      (8 * neiGst p₁ p₂ / (1 + neiGst p₁ p₂)) * effectiveSubgroupSize n m := by
  unfold hudsonBbpSpike demographicSpike
  rw [hudsonFst_eq_of_neiGst p₁ p₂ hpos hbar]
  ring

/-- **A regression witness preventing convention collapse.** At an interior,
mean-one-half frequency pair, the empirically Hudson-calibrated spike and the
exact Nei contrast spike are different. -/
theorem hudsonBbpSpike_ne_neiContrastSpike_at_mean_half :
    hudsonBbpSpike 4 2 (9/10) (1/10) ≠
      neiContrastSpike 4 2 (9/10) (1/10) := by
  unfold hudsonBbpSpike neiContrastSpike demographicSpike hudsonFst neiGst
    effectiveSubgroupSize ploidy meanAlleleFreq
  norm_num

end Differentiation

section EquilibriumAgreements

/-! **The island-model `F_ST` is one definition, `fstMigrationDriftEquilibrium`.**
Write new uses against it rather than spelling out `1 / (1 + 4 Nₑ m)` again; a second
spelling would carry its own factor of four with nothing to hold it in step.

`equilibriumFst` is worth recording as a hazard: it took its arguments in the opposite
order to the other two, so the same call spelled the same way meant different things
depending on which copy was in scope. -/

/-- **Cross-check: the two assortative-mating inflation claims agree only at
full heritability.**

`StratificationConfounding` carried `amInflationFactor r = 1/(1 - r)` and
`AssortativeMatingPGS` carries `amEquilibriumVariance V_A r h² = V_A/(1 - r h²)`
for the same quantity, and no theorem related them. Forward simulation with
the spousal correlation measured rather than assumed puts the second within
-5% to +1% and the first between +3% and +82% high, so the first is deleted.
This theorem records why the disagreement was invisible: the two coincide
exactly when `h² = 1`, which is the only case anyone would have checked by
inspection, and diverge with `h²` everywhere else. Assortative mating is a
forward-time phenomenon, so no coalescent simulation could have separated
them. -/
theorem amEquilibriumVariance_at_full_heritability (V_A r : ℝ) :
    amEquilibriumVariance V_A r 1 = V_A / (1 - r) := by
  unfold amEquilibriumVariance
  ring_nf

/-- **Cross-check spanning the mating and drift modules: assortative mating and
drift act multiplicatively on the additive variance.**

`amEquilibriumVariance` inflates by `1/(1 - r h²)` and `presentDayPGSVariance`
deflates by `(1 - F_ST)`, and composing them gives the product. Stated because
the two modules described the same variance and were never related, which is
the condition under which a falsified companion of `amEquilibriumVariance`
survived. -/
theorem amEquilibrium_then_drift (V_A r h2 fst : ℝ) :
    presentDayPGSVariance (amEquilibriumVariance V_A r h2) fst =
      (1 - fst) * (V_A / (1 - r * h2)) := by
  unfold presentDayPGSVariance pgsVarianceFromHet amEquilibriumVariance
  ring

/-! ### Tying the inlined genotype-variance restatements back to `ploidy`

**A definition that INLINES the literal `2` is tied to the ploidy convention by
nothing but the theorem that says so.** Those theorems are below, one per inlining
definition, and each is the only edge between a literal and the named convention:
change `ploidy` and they fail, which is their entire purpose. Do not delete one as a
trivial restatement -- the definitions on their left-hand sides do not reference
`ploidy`, so the equality holds only because `rfl` reduces `ploidy` to `2`.

Prefer calling `hweGenotypeVariance` in new code, so no new edge is needed.

The two inlinings are `genotypeVarianceHWE` and `hweHeterozygosity`, both in
`AncestrySpecificPower` and related to each other there by
`hweHeterozygosity_eq_genotypeVarianceHWE`. The two theorems below tie that pair back to
`ploidy`, so the convention has exactly one place to change. -/

theorem genotypeVarianceHWE_eq_hwe (p : ℝ) :
    genotypeVarianceHWE p = hweGenotypeVariance p := by
  unfold genotypeVarianceHWE hweGenotypeVariance ploidy; ring

theorem hweHeterozygosity_eq_hwe (p : ℝ) :
    hweHeterozygosity p = hweGenotypeVariance p := by
  unfold hweHeterozygosity hweGenotypeVariance ploidy; ring

/-! ### Tying the island-model equilibrium back to the scaled rate

One definition, one bridge: the island-model equilibrium is the migration-drift
equilibrium at the scaled migration rate. A second spelling of `1 / (1 + 4 Nₑ m)` would
need its own bridge theorem, which is a reason not to add one. -/

theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m =
      fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### Per-generation drift rate, written out in three modules

`1 / (2 Nₑ)` appears independently in `LongitudinalPortability`,
`DemographicHistory` and `LDDecayTheory` under three names. It is the
reciprocal of the coalescent time scale in each. -/

theorem driftLDCreationRate_eq_inv_timeScale (Ne : ℝ) :
    driftLDCreationRate Ne = 1 / coalescentTimeScale Ne := by
  unfold driftLDCreationRate; rw [coalescentTimeScale_eq]

theorem driftRatePerGen_eq_inv_timeScale (Ne : ℝ) :
    driftRatePerGen Ne = 1 / coalescentTimeScale Ne := by
  unfold driftRatePerGen; rw [coalescentTimeScale_eq]

/-- **Cross-check: the `2 Nₑ` inside `coalFst` is the coalescent time scale.**
`coalFst t Ne = t / (t + 2 Nₑ)` is `t / (t + E[T_within])`, and `E[T_within]`
is `ploidy · Nₑ` generations. Writing the two inline left the constant free;
this states which two it is. -/
theorem coalFst_uses_coalescentTimeScale (t Ne : ℝ) :
    coalFst t Ne = t / (t + coalescentTimeScale Ne) := by
  unfold coalFst; rw [coalescentTimeScale_eq]

/-! ### The coalescent `F_ST` map, written out once

`PopulationGeneticsFoundations.coalFst` is the one body for this map, and
`DemographicHistory` calls it directly. Simulation validates `coalFst` as split
`F_ST`, unbiased against branch-mode divergence where the drift formula runs up
to 28 percent high. The name `DemographicHistory.fstFromCoalescenceTime` is
absent on purpose: a second spelling of `coalFst` can drift from it silently. -/

/-! ### The harmonic mean, written out once

`OpenQuestions.f1Score` is the one body for this expression, and
`MetricSpecificPortability` calls it. The name
`MetricSpecificPortability.f1ScoreMetric` is absent on purpose: two spellings in
two modules, with no theorem relating them, can disagree without failing. -/

/-- Wright's compounding identity: one minus the product of retentions. It is
written once for the two branches of a split and once for the two levels of
the `F`-statistic hierarchy. -/
theorem pairwiseFstFromBranches_eq_wrightFIT (a b : ℝ) :
    pairwiseFstFromBranches a b = wrightFIT a b := by
  unfold pairwiseFstFromBranches wrightFIT; ring_nf

/-! ### The per-generation retention factor, written out in four modules

`1 - 1/(2 Nₑ)` is the probability that two lineages fail to coalesce in one
generation. It is spelled out independently in `PhenomeWidePortability`,
`LDDecayTheory`, `PopulationGeneticsFoundations` and `PortabilityDrift`.

**These theorems pin the constant, not the regime, and three of the four bodies below
are members of a falsified cluster.** `(1 - 1/(2 Nₑ))^t` is the closed-population,
no-mutation recurrence; at demographic equilibrium simulation measures a retention of
`1.02 ± 0.02` where it predicts `e^(-2) = 0.135`, because mutation replenishes diversity
(`DriftRegime`). Agreeing on `2 Nₑ` is exactly the kind of cross-check that cannot see
that, since every identity here holds *in* the shared premise whatever its value.

`heterozygosityLossDerived` and `wrightFisherDriftRetention` are attached to the named
regime at the end of this file. `neutralDriftFactor` is **not** attached and carries a
FALSIFIED status of its own in `PhenomeWidePortability`. Note that
`ldRetainedFraction_uses_timeScale` below is the one guard in this group that states
what its formula omits — copy that shape, not the bare ones. -/

theorem neutralDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) :
    neutralDriftFactor Ne t = (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold neutralDriftFactor; rw [coalescentTimeScale_eq]

/-- **The drift channel enters through `2·Nₑ`, and drift is not the whole retention.**
The recombination factor `(1 - r)` is part of the retained fraction, so
`(1 - 1/coalescentTimeScale Ne)^t` alone is NOT this quantity -- it is the `r = 0`
slice. This theorem pins the `2·Nₑ` convention inside the full expression. -/
theorem ldRetainedFraction_uses_timeScale (r Ne : ℝ) (t : ℕ) :
    ldRetainedFraction r Ne t
      = ((1 - r) * (1 - 1 / coalescentTimeScale Ne)) ^ t := by
  unfold ldRetainedFraction ldRetentionPerGen; rw [coalescentTimeScale_eq]

theorem heterozygosityLossDerived_uses_timeScale (Ne : ℝ) (t : ℕ) :
    heterozygosityLossDerived Ne t = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold heterozygosityLossDerived; rw [coalescentTimeScale_eq]

theorem wrightFisherDriftRetention_uses_timeScale (N : ℕ) (t : ℕ) :
    wrightFisherDriftRetention N t
      = (1 - 1 / coalescentTimeScale (N : ℝ)) ^ t := by
  unfold wrightFisherDriftRetention; rw [coalescentTimeScale_eq]

/-! ### The coalescent time coordinate, written out twice

`t / (2 Nₑ)` is time in coalescent units, in `PortabilityDrift` and in `DGP`. -/

theorem coalescentTau_uses_timeScale (t Ne : ℝ) :
    coalescentTau t Ne = t / coalescentTimeScale Ne := by
  unfold coalescentTau; rw [coalescentTimeScale_eq]

/-! ### The scaled rates, written out on three parameter records

`θ = 4 Nₑ μ` and `M = 4 Nₑ m` appear as fields of
`GenerationalPopGenParameters` in `PortabilityDrift` and of
`EvolutionaryParameters` in `DGP`, each spelling out its own four. -/

theorem GenerationalPopGenParameters_theta_eq_ploidy_form
    (g : GenerationalPopGenParameters) :
    GenerationalPopGenParameters.theta g = 2 * ploidy * g.Ne * g.μ := by
  unfold GenerationalPopGenParameters.theta ploidy scaledMutationRate; ring

theorem GenerationalPopGenParameters_bigM_eq_ploidy_form
    (g : GenerationalPopGenParameters) :
    GenerationalPopGenParameters.bigM g = 2 * ploidy * g.Ne * g.mig := by
  unfold GenerationalPopGenParameters.bigM ploidy scaledMigrationRate; ring

theorem EvolutionaryParameters_theta_eq_ploidy_form (p : EvolutionaryParameters) :
    EvolutionaryParameters.theta p = 2 * ploidy * p.Ne * p.mu := by
  unfold EvolutionaryParameters.theta ploidy scaledMutationRate; ring

theorem EvolutionaryParameters_bigM_eq_ploidy_form (p : EvolutionaryParameters) :
    EvolutionaryParameters.bigM p = 2 * ploidy * p.Ne * p.mig := by
  unfold EvolutionaryParameters.bigM ploidy scaledMigrationRate; ring

/-- **The between-population variance of the mean breeding value is
`ploidy · F_ST · V_A`.**

Two independently drifting populations each contribute `F_ST V_A`, so the
variance of their difference carries the ploidy factor. Writing `2` here is
the same convention as everywhere else and is now tied to it. -/
theorem Var_Delta_Mu_eq_ploidy_form (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = ploidy * fst * V_A := by
  unfold Var_Delta_Mu ploidy; ring

/-! ### Genotype variance inside sums and products

Eight further definitions carry `2 p (1 - p)` as a factor rather than as their
whole body: score means and variances, Fisher's average effect, dominance and
additive variance, two noncentrality parameters, and a pairwise epistatic
variance. Each is now written against `hweGenotypeVariance`. -/

theorem pgsVariance_uses_hwe {m : ℕ} (β p : Fin m → ℝ) :
    pgsVariance β p = ∑ i, β i ^ 2 * hweGenotypeVariance (p i) := by
  unfold pgsVariance hweGenotypeVariance ploidy; ring_nf

theorem dominanceVariance_uses_hwe {m : ℕ} (p d : Fin m → ℝ) :
    dominanceVariance p d = ∑ i, (hweGenotypeVariance (p i) * d i) ^ 2 := by
  unfold dominanceVariance hweGenotypeVariance ploidy; ring_nf

/-- **`additiveVariance` is a sum over loci and therefore assumes linkage equilibrium**;
this theorem pins its `2 p (1 - p)` to `ploidy` and says nothing about that assumption.

The qualifier is load-bearing. The per-locus sum drops the cross term
`Σ_{i≠j} 4 α_i α_j D_ij`, and the sign of the resulting error flips with the sign of the
effect product, so no constant repairs it: at `p = 1/2`, `D = 1/8`, `α = (1,1)` gives `1`
against a true `3/2`, while `α = (1,-1)` gives `1` against a true `1/2`. The
unconditional reading is FALSIFIED (`VarianceComponents.additiveVariance`). -/
theorem additiveVariance_uses_hwe {m : ℕ} (p α : Fin m → ℝ) :
    additiveVariance p α = ∑ i, hweGenotypeVariance (p i) * (α i) ^ 2 := by
  unfold additiveVariance hweGenotypeVariance ploidy; ring_nf

theorem noncentralityParam_uses_hwe (n : ℕ) (beta p : ℝ) :
    noncentralityParam n beta p = n * beta ^ 2 * hweGenotypeVariance p := by
  unfold noncentralityParam hweGenotypeVariance ploidy; ring_nf

theorem gwasNCP_uses_hwe (n : ℕ) (β p : ℝ) :
    gwasNCP n β p = n * β ^ 2 * hweGenotypeVariance p := by
  unfold gwasNCP hweGenotypeVariance ploidy; ring_nf

theorem effectiveFisherInformation_uses_hwe (n : ℕ) (p r2_ld : ℝ) :
    effectiveFisherInformation n p r2_ld = n * hweGenotypeVariance p * r2_ld := by
  unfold effectiveFisherInformation fisherInformation genotypeVarianceHWE
    hweGenotypeVariance ploidy
  ring_nf

theorem epistaticVariancePairwise_uses_hwe (γ p₁ p₂ : ℝ) :
    epistaticVariancePairwise γ p₁ p₂ =
      γ ^ 2 * hweGenotypeVariance p₁ * hweGenotypeVariance p₂ := by
  unfold epistaticVariancePairwise hweGenotypeVariance ploidy; ring_nf

/-- The between-population drift variance of the score, carrying the same
ploidy factor as `Var_Delta_Mu`. -/
theorem expectedPGSDiffVariance_eq_ploidy_form (V_A fst : ℝ) :
    expectedPGSDiffVariance V_A fst = ploidy * fst * V_A := by
  unfold expectedPGSDiffVariance ploidy; ring

/-! ### The remaining singletons

Each of these uses the ploidy convention once, with no sibling to disagree
with, so only a derivation from `ploidy` ties them down. -/

/-- **Do not simplify this to `coalescentTimeScale Ne * log 2`.** That is the `r → 0`
limit and is false at every `r > 0`. The `2·Nₑ` convention appears inside the retention
whose logarithm sets the half-life, which is what this states. -/
theorem ldHalfLife_uses_timeScale (r Ne : ℝ) :
    ldHalfLife r Ne
      = Real.log 2 / (-Real.log ((1 - r) * (1 - 1 / coalescentTimeScale Ne))) := by
  unfold ldHalfLife ldRetentionPerGen; rw [coalescentTimeScale_eq]

/-! `steppingStoneCharacteristicLength_uses_timeScale` has been DELETED, not
restated. It asserted
`steppingStoneCharacteristicLength Ne m = Real.sqrt (coalescentTimeScale Ne * m)`,
i.e. that the 1D decay length carries the `2·Nₑ` ploidy convention. The
corrected definition is `√(m/(2·μ))` and contains no effective size at all, so
there is no convention here to pin and no honest restatement to make: the
theorem existed only because the wrong body happened to contain `2·Nₑ`. Its
replacement, stating what that definition does claim, is
`PopulationGeneticsFoundations.steppingStoneCharacteristicLength_balances_mutation`. -/

theorem cumulativeDrift_uses_timeScale {T : ℕ} (Ne : Fin T → ℝ) :
    cumulativeDrift Ne = ∑ i, 1 / coalescentTimeScale (Ne i) := by
  unfold cumulativeDrift
  simp only [coalescentTimeScale_eq]

theorem ldRetentionPerGen_uses_timeScale (r Ne : ℝ) :
    ldRetentionPerGen r Ne = (1 - r) * (1 - 1 / coalescentTimeScale Ne) := by
  unfold ldRetentionPerGen; rw [coalescentTimeScale_eq]

theorem hetDecayFactor_uses_timeScale (Ne θ : ℝ) :
    hetDecayFactor Ne θ
      = (1 - 1 / coalescentTimeScale Ne) * (1 - θ / coalescentTimeScale Ne) := by
  unfold hetDecayFactor hetDecayFromScaled; rw [coalescentTimeScale_eq]

theorem asymmetricFst_eq_scaled (Ne m_into : ℝ) :
    asymmetricFst Ne m_into
      = fstMutationDriftEquilibrium (scaledMigrationRate Ne m_into) := by
  unfold asymmetricFst fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem fstMigDriftEquil_eq_scaled (Ne m : ℝ) :
    fstMigDriftEquil Ne m
      = fstMutationDriftEquilibrium (scaledMigrationRate Ne m) := by
  unfold fstMigDriftEquil fstMutationDriftEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

theorem fstMigrationMutationEquilibrium_eq_scaled (Ne m μ : ℝ) :
    fstMigrationMutationEquilibrium Ne m μ
      = 1 / (1 + scaledMigrationRate Ne m + scaledMutationRate Ne μ) := by
  unfold fstMigrationMutationEquilibrium
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold ploidy; ring_nf

/-- **The finite-deme island equilibrium carries the same two scaled rates.** Its
`4 Nₑ m` is `scaledMigrationRate` and its `4 Nₑ μ` is `scaledMutationRate`, exactly as in
the deme-blind limit form; the deme correction multiplies the migration rate and does not
touch either constant. Without this the `4` would be a third inlined ploidy convention. -/
theorem fstIslandEquilibriumFiniteDemes_eq_scaled (Ne m μ nDemes : ℝ) :
    fstIslandEquilibriumFiniteDemes Ne m μ nDemes
      = 1 / (1 + scaledMigrationRate Ne m * islandDemeCorrection nDemes
              + scaledMutationRate Ne μ) := by
  unfold fstIslandEquilibriumFiniteDemes
  rw [scaledMigrationRate_eq_ploidy_form, scaledMutationRate_eq_ploidy_form]
  unfold ploidy; ring_nf

theorem expectedFreqDiffSq_uses_hwe (fst p0 : ℝ) :
    expectedFreqDiffSq fst p0 = fst * hweGenotypeVariance p0 := by
  unfold expectedFreqDiffSq hweGenotypeVariance ploidy; ring

theorem pgsMean_uses_ploidy {m : ℕ} (β p : Fin m → ℝ) :
    pgsMean β p = ∑ i, β i * (ploidy * p i) := by
  unfold pgsMean ploidy; ring_nf

theorem fisherAverageEffect_uses_ploidy (a d p : ℝ) :
    fisherAverageEffect a d p = a + d * (1 - ploidy * p) := by
  unfold fisherAverageEffect ploidy; ring

theorem neutralPortability_uses_ploidy (r2_0 fst : ℝ) :
    neutralPortability r2_0 fst = r2_0 * max 0 (1 - ploidy * fst) := by
  rfl

/-! ### The last entangled uses

These carry the convention inside a larger expression. A relation still ties
them down; no definition needs rewriting. -/

theorem selectedDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) (s_correction : ℝ) :
    selectedDriftFactor Ne t s_correction
      = (1 - 1 / coalescentTimeScale Ne + s_correction) ^ t := by
  unfold selectedDriftFactor; rw [coalescentTimeScale_eq]

theorem SplitMigrationModel_scaledMigration_eq_ploidy_form
    (m : SplitMigrationModel) :
    scaledMigrationRate m.Ne m.mig = 2 * ploidy * m.Ne * m.mig := by
  unfold scaledMigrationRate ploidy; ring

theorem fstMigDriftNext_uses_timeScale (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst
      = (1 - 2 * m - 1 / coalescentTimeScale Ne) * Fst
        + 1 / coalescentTimeScale Ne := by
  unfold fstMigDriftNext; rw [coalescentTimeScale_eq]

theorem ibdFst_eq_ploidy_form (d N sigma_sq : ℝ) :
    ibdFst d N sigma_sq = d / (2 * ploidy * N * sigma_sq + d) := by
  unfold ibdFst ploidy; ring_nf

theorem EvolutionaryParameters_tau_uses_timeScale (p : EvolutionaryParameters) :
    EvolutionaryParameters.tau p = p.t_div / coalescentTimeScale p.Ne := by
  unfold EvolutionaryParameters.tau; rw [coalescentTimeScale_eq]

theorem sharedLDRetention_uses_ploidy (p : EvolutionaryParameters) :
    sharedLDRetention p = Real.exp (-ploidy * p.recomb * p.t_div) := by
  unfold sharedLDRetention ploidy; ring_nf

theorem demoSteppingStoneFst_eq_scaled (d Ne m σ_sq : ℝ) :
    demoSteppingStoneFst d Ne m σ_sq
      = d / (d + scaledMigrationRate Ne m * σ_sq) := by
  unfold demoSteppingStoneFst
  rw [scaledMigrationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### The last seven

Each carries the convention in its own shape: inside a `let`, in a recursion
step, or under two nested decay factors. A relation reaches all of them. -/

theorem tauAt_uses_timeScale (g : GenerationalPopGenParameters) (t : ℕ) :
    GenerationalPopGenParameters.tauAt g t
      = (t : ℝ) / coalescentTimeScale g.Ne := by
  unfold GenerationalPopGenParameters.tauAt; rw [coalescentTimeScale_eq]

theorem alleleFreqDivergenceRate_eq_scaled (Ne mu m_rate : ℝ) :
    alleleFreqDivergenceRate Ne mu m_rate
      = 1 / (coalescentTimeScale Ne *
          (1 + scaledMutationRate Ne mu + scaledMigrationRate Ne m_rate)) := by
  unfold alleleFreqDivergenceRate
  rw [coalescentTimeScale_eq, scaledMutationRate_eq_ploidy_form,
    scaledMigrationRate_eq_ploidy_form]
  unfold ploidy; ring_nf

theorem fstMutationDriftTransient_uses_timeScale (θ t Ne : ℝ) :
    fstMutationDriftTransient θ t Ne
      = fstMutationDriftEquilibrium θ *
          (1 - Real.exp (-(1 + θ) * t / coalescentTimeScale Ne)) := by
  unfold fstMutationDriftTransient; rw [coalescentTimeScale_eq]

theorem MutationDriftModelAssumptions_fstTransient_uses_timeScale
    (m : MutationDriftModelAssumptions) :
    MutationDriftModelAssumptions.fstTransient m
      = m.fstEquilibrium *
          (1 - Real.exp (-(1 + m.theta) * m.t / coalescentTimeScale m.Ne)) := by
  unfold MutationDriftModelAssumptions.fstTransient
  rw [coalescentTimeScale_eq]

theorem hetMutationDriftRecurrence_step_uses_timeScale
    (Ne mu H₀ : ℝ) (t : ℕ) :
    hetMutationDriftRecurrence Ne mu H₀ (t + 1)
      = (1 - 1 / coalescentTimeScale Ne) * hetMutationDriftRecurrence Ne mu H₀ t
        + ploidy * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t) := by
  change
    (1 - 1 / (2 * Ne)) * hetMutationDriftRecurrence Ne mu H₀ t +
        2 * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t) = _
  rw [coalescentTimeScale_eq]
  unfold ploidy
  rfl

/-- Equilibrium heterozygosity under mutation-drift balance, `θ/(1 + θ)`,
written out with its own four. This is the last inline restatement of the
ploidy convention in the development. -/
theorem hetMutationFloor_eq_scaled (Ne mu : ℝ) :
    hetMutationFloor Ne mu
      = scaledMutationRate Ne mu / (1 + scaledMutationRate Ne mu) := by
  unfold hetMutationFloor
  rw [scaledMutationRate_eq_ploidy_form]; unfold ploidy; ring_nf

/-! ### Shared primitives

Several groups of definitions across the development are the same map applied
to different quantities. Left unrelated, each is free to drift from the others;
naming the map once and relating them makes a divergence a failed proof. This
is the same device as `ploidy`, applied to structure rather than to a
constant. -/

/-- Convex combination, `α x + (1 - α) y`. -/
noncomputable def convexMix (α x y : ℝ) : ℝ := α * x + (1 - α) * y

theorem spikeAndSlabVariance_eq_convexMix (pi sl sm : ℝ) :
    spikeAndSlabVariance pi sl sm = convexMix pi sl sm := by
  unfold spikeAndSlabVariance convexMix; ring

theorem admixedAlleleFreq_eq_convexMix (α p_A p_B : ℝ) :
    admixedAlleleFreq α p_A p_B = convexMix α p_A p_B := by
  unfold admixedAlleleFreq convexMix; ring

theorem averagePhaseInteraction_eq_convexMix (freq_cis i_cis i_trans : ℝ) :
    averagePhaseInteraction freq_cis i_cis i_trans = convexMix freq_cis i_cis i_trans := by
  unfold averagePhaseInteraction convexMix; ring

theorem ancestrySpecificEffect_eq_convexMix (b1 b2 alpha : ℝ) :
    ancestrySpecificEffect b1 b2 alpha = convexMix alpha b1 b2 := by
  unfold ancestrySpecificEffect convexMix; ring

/-- Geometric decay, `(1 - r)^t`: LD across generations, recombination
survival along a genealogy, and admixture-LD decay are one map.

**THIS IS THE HUB. Route new spellings through it, and do not add pairwise theorems.**
`(1 - r)^t` is currently written out under FOUR names in four files — `geometricDecay`,
`LongitudinalPortability.ldDecayPerGeneration`, `DGP.discreteRecombinationSurvival` and
`PortabilityDrift.admixtureLDDecay` — and once carried SIX pairwise equalities between
them. Three are kept, immediately below: each ties one spelling to this primitive, and
together they make a divergence between any two spellings a failed proof. The other three
were pairwise restatements implied by these by transitivity, and are deleted.

**DO NOT FOLD THESE FOUR NAMES INTO ONE.** They are one FUNCTION under four
REFERENTS, and a name census sees only the arithmetic:

  * `geometricDecay` -- the bare primitive, and the hub.
  * `PortabilityDrift.admixtureLDDecay` -- admixture LD decay. VALIDATED as the
    `Nₑ → ∞` limit and MEASURED high by `+0.24%` to `+0.37%` against
    finite-population retention, with `admixtureLDDecay_ge_finitePopulation`
    proving the bias is one-sided. Folding it into a bare primitive would detach
    a measured regime and a proved error direction from the name they describe.
  * `DGP.discreteRecombinationSurvival` -- survival of two linked loci to the
    MRCA, a genealogical probability rather than an LD quantity.
  * `LongitudinalPortability.ldDecayPerGeneration` -- per-generation LD decay.

Identical arithmetic is not identical meaning. `hweHeterozygosity` and
`genotypeVarianceHWE` are both `2p(1-p)` and are heterozygosity and dosage
variance respectively; the same holds here at larger scale.

The three hub theorems below are the right amount of machinery: a divergence
between any two spellings fails one of them. -/
noncomputable def geometricDecay (r : ℝ) (t : ℕ) : ℝ := (1 - r) ^ t

theorem ldDecayPerGeneration_eq_geometricDecay (r : ℝ) (t : ℕ) :
    ldDecayPerGeneration r t = geometricDecay r t := by
  unfold ldDecayPerGeneration geometricDecay; ring_nf

theorem admixtureLDDecay_eq_geometricDecay (r : ℝ) (t : ℕ) :
    admixtureLDDecay r t = geometricDecay r t := by
  unfold admixtureLDDecay geometricDecay; ring_nf

theorem discreteRecombinationSurvival_eq_geometricDecay (r : ℝ) (t : ℕ) :
    discreteRecombinationSurvival r t = geometricDecay r t := by
  unfold discreteRecombinationSurvival geometricDecay; ring_nf

/-- One minus a ratio, `1 - a / b`: `F_ST` from a heterozygosity ratio, `F_ST`
from coalescence times, `R²` from a mean squared error, and residual efficacy
are one map. -/
noncomputable def oneMinusRatio (a b : ℝ) : ℝ := 1 - a / b

/-- **The complementary ratio at a zero denominator, named.** With `b = 0` the ratio is undefined
and so is its complement. Lean returns `1`, the value that means "`a` is entirely accounted for" --
the strongest possible claim, produced by the case where nothing is known at all. Consumers must
require `b ≠ 0`. -/
theorem oneMinusRatio_zero_denominator_is_junk (a : ℝ) :
    oneMinusRatio a 0 = 1 := by
  unfold oneMinusRatio
  simp

theorem fstFromHetRatio_eq_oneMinusRatio (H H₀ : ℝ) :
    fstFromHetRatio H H₀ = oneMinusRatio H H₀ := by
  unfold fstFromHetRatio oneMinusRatio; ring_nf

theorem hudsonFstFromCoalescenceTimes_eq_oneMinusRatio (ETss ETst : ℝ) :
    hudsonFstFromCoalescenceTimes ETss ETst = oneMinusRatio ETss ETst := by
  unfold hudsonFstFromCoalescenceTimes oneMinusRatio; ring_nf

/-- The PC-correction efficacy is the same `1 - a/b` map: what is corrected
away is one minus the fraction of the ancestry axis that survives correction,
exactly as `F_ST` is one minus the fraction of heterozygosity that survives
subdivision. The two are different quantities and must not drift into different
shapes. -/
theorem pcTargetAxisEfficacy_eq_oneMinusRatio (H Hres : ℝ) :
    pcTargetAxisEfficacy H Hres = oneMinusRatio Hres H := by
  unfold pcTargetAxisEfficacy oneMinusRatio; ring_nf

theorem r2FromMSE_eq_oneMinusRatio (mse varY : ℝ) :
    r2FromMSE mse varY = oneMinusRatio mse varY := by
  unfold r2FromMSE oneMinusRatio; ring_nf

/-! ### Retention and ratio maps

Three further groups are one map under several names. -/

/-- Retained fraction, `(1 - loss) · total`: the ascertainment-loss survivor,
the neutral portability ratio and the present-day PGS variance are one map. -/
noncomputable def retainedFraction (loss total : ℝ) : ℝ := (1 - loss) * total

/-- **retainedFraction pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 4`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem retainedFraction_at_reference_point :
    retainedFraction (1 / 2) (1 / 2) = 1 / 4 := by
  unfold retainedFraction
  norm_num

theorem ascertainment_loss_eq_retainedFraction (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal = retainedFraction coverage v_causal := by
  unfold ascertainment_loss retainedFraction; ring

theorem neutralPortabilityRatioLD_eq_retainedFraction (fst ld : ℝ) :
    neutralPortabilityRatioLD fst ld = retainedFraction fst ld := by
  unfold neutralPortabilityRatioLD retainedFraction; ring

theorem presentDayPGSVariance_eq_retainedFraction (V_A fst : ℝ) :
    presentDayPGSVariance V_A fst = retainedFraction fst V_A := by
  unfold presentDayPGSVariance pgsVarianceFromHet retainedFraction; ring

/-! `explainedR2FromTransportMoments` and `pgsR2` are the same term; the identity is
stated once, next to `pgsR2` in `TransferLearningPGS`. -/

/-! ### The regime obligation, stated once

A closed form whose docstring reads `Empirical status: FALSIFIED` or `CONDITIONALLY VALID`
is making two claims at once: an algebraic one, which Lean checks, and a claim about the
conditions under which the algebra describes a population, which until recently nothing
checked. `DriftRegime` established why that matters — a formula carrying its regime in a
docstring can be moved into a regime where it is false, and every internal cross-check will
still pass, because the identities are identities *in* the shared premise.

Every such closed form now carries its regime in a machine-checkable form, by one of four
mechanisms. Recorded here so that a new one added without any of them is visibly a
departure rather than an oversight:

* **In the signature.** The definition takes a structure whose fields include the
  regime definition: `ClosedPopulationNoMutation` has mutation fixed to zero,
  an explicitly stated approximation inequality.
* **Tied to a regime object.** A theorem identifies the bare formula with a quantity of a
  named regime: `closedPopulation_het_eq_neutralDriftFactor`,
  `heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` and its two siblings.
* **Never as an external theorem field.** If the development has no derivation connecting
  a numerical chart to a scientific observable, no identification theorem is exported.
  A citation or caller-supplied proposition cannot manufacture that theorem.
* **As a proved failure.** The departure is itself a theorem, so the limit is checkable
  rather than described: `benchmarkRatioForm_cannot_reach_measured`,
  `finiteIslandCorrection_two_excess`,
  `demoSteppingStoneFst_indistinguishable_from_quadratic`,
  `pairwiseFstFromBranches_eq_fstFromTau_add_mul`,
  `sampleLimitedScratchTargetR2_negative_of_small_sample`.

The fourth is the one worth noticing. Several of these regimes are not conditions under
which the formula holds but statements of how it fails — and a proved failure is stronger
than a hedged docstring, because it cannot be read past. -/

/-! ### Attaching the drift closed forms to the regime they came from

`DriftRegime` records the incident these two definitions are the residue of: a cluster of
five quantities, all functions of one closed-population retention, every cross-check
between them passing because every identity among them is an identity *in* that retention.
It fixed the diagnosis by making the regime an object — `closedPopulation` against
`mutationDriftBalance`, with `regimes_disagree` separating them — but the closed forms in
`PopulationGeneticsFoundations` were never attached to it, so they still carry their regime
only in prose.

These two theorems attach them. Neither is deep; that is the point. Each says the bare
formula is the measured loss of a *named* trajectory, so a reader who wants to know which
regime `heterozygosityLossFromDrift` assumes can follow a proof instead of trusting a
docstring — and anyone who moves it to a population at mutation-drift balance now
contradicts `regimes_disagree` rather than silently getting a wrong number. -/

theorem heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss
    (t : ℕ) (Ne H₀ : ℝ) (hH : 0 < H₀) :
    heterozygosityLossFromDrift t Ne = (closedPopulation Ne H₀ hH).measuredLoss t := by
  rw [measuredLoss_closedPopulation]
  unfold heterozygosityLossFromDrift
  rfl

/-- **The same body, read as a between-population `F_ST`.**

`heterozygosityLossDerived` and `heterozygosityLossFromDrift` share a body, and `DriftRegime` names
that
coincidence as the defect rather than a convenience: a within-population heterozygosity
loss and a between-population variance ratio are different quantities, and the shared body
is what let one be substituted for the other. They are deliberately *not* merged. This
theorem records that `heterozygosityLossDerived` inherits the closed-population regime through that
shared body — which is the fact a reader needs in order to see that its `F_ST` reading is
only available in the regime where the loss reading is.

Note the argument orders differ: `heterozygosityLossFromDrift` takes `(t, Ne)` and
`heterozygosityLossDerived` takes `(Ne, t)`, so the same call spelled the same way means different
things
depending on which is in scope. That is the hazard `equilibriumFst` carried before it was
collapsed, still live here because these two must *not* be collapsed. -/
theorem heterozygosityLossDerived_eq_closedPopulation_measuredLoss
    (t : ℕ) (Ne H₀ : ℝ) (hH : 0 < H₀) :
    heterozygosityLossDerived Ne t = (closedPopulation Ne H₀ hH).measuredLoss t := by
  rw [measuredLoss_closedPopulation]
  unfold heterozygosityLossDerived
  rfl

/-- **The Wright-Fisher loss is the same regime again**, at an integer effective size.

Third copy of the body, third reading of it. `DriftRegime` counted five members in the
cluster; this attaches the one that states the recurrence over `ℕ` generations, so that
all three now name the same trajectory rather than three formulas that happen to agree. -/
theorem wrightFisherHeterozygosityLoss_eq_closedPopulation_measuredLoss
    (N t : ℕ) (H₀ : ℝ) (hH : 0 < H₀) :
    wrightFisherHeterozygosityLoss N t
      = (closedPopulation (N : ℝ) H₀ hH).measuredLoss t := by
  rw [measuredLoss_closedPopulation]
  unfold wrightFisherHeterozygosityLoss wrightFisherDriftRetention
  rfl

/-- **The fourth proportional-reduction body, and the one that could not be reached from
its siblings.**

`PopulationGeneticsFoundations.fstFromHetRatio_eq_hudsonFst_eq_r2FromMSE` already relates
three spellings of `1 - residual/baseline`: a heterozygosity ratio, a coalescence-time
ratio, and an error-to-variance ratio.  `PCCorrectability.Diagnostic.pcTargetAxisEfficacy`
is the fourth — the fraction of a target ancestry axis captured by correction, written in
its own docstring as `V_K = 1 - H'/H`, deliberately echoing `F_ST` — and it could not join
them there, because `Diagnostic` imports nothing outside `PCCorrectability` and none of the
other three files imports `Diagnostic`.

This module reaches all four, through `StratificationConfounding → PCCorrectability`.  That
is the whole reason the statement is here and not beside any of the definitions: **the
tying theorem belongs wherever both sides are visible, not in one of the two files.**  A
guard demanding the latter reported this pair as unfixable when the only thing missing was
permission to speak from a third module.

As with its siblings these are four different quantities and no value of one may be
substituted for another; what is shared is the measure, and sharing it silently is what
this section exists to prevent. -/
theorem pcTargetAxisEfficacy_eq_proportionalReduction (residual baseline : ℝ) :
    pcTargetAxisEfficacy baseline residual = fstFromHetRatio residual baseline ∧
      pcTargetAxisEfficacy baseline residual =
        hudsonFstFromCoalescenceTimes residual baseline ∧
      pcTargetAxisEfficacy baseline residual = r2FromMSE residual baseline := by
  refine ⟨rfl, rfl, rfl⟩

end EquilibriumAgreements

section InlinedConstants

/-! ## The remaining inline restatements, tied back

Each definition below spells a `2` or a `4` out in its own body, in its own module. The
theorems here are the edges between those literals and `ploidy`: rewrite `ploidy` and each
one stops compiling, which is the whole of their purpose. They are not restatements of the
definitions — the left-hand sides do not mention `ploidy`, so the equality holds only
because `ploidy` reduces to `2`.

Where the constant is a coalescent scaling the tie goes through `coalescentTimeScale`,
which is `ploidy · Nₑ`; where it is the diploid genotype variance it goes through
`hweGenotypeVariance`; where it is a scaled rate it goes through `scaledMigrationRate`,
which `scaledMigrationRate_eq_ploidy_form` already forces. -/

/-- **The `2 p (1 - p)` in the effective sample size is the diploid genotype variance.**
`StatisticalGeneticsMethodology.effectiveSampleSizeFromSE` inverts `SE² · Var(dosage)`, and
`Var(dosage)` under Hardy-Weinberg proportions is `hweGenotypeVariance`. Written inline the
two was free; here it is the ploidy, and an SE reported on a haploid dosage scale would
have to change this file rather than that definition. -/
theorem effectiveSampleSizeFromSE_uses_hweGenotypeVariance (se p : ℝ) :
    effectiveSampleSizeFromSE se p = 1 / (se ^ 2 * hweGenotypeVariance p) := by
  unfold effectiveSampleSizeFromSE hweGenotypeVariance ploidy; ring

/-- **Both twos in the mutation-drift heterozygosity step are the ploidy.** The drift term
loses a fraction `1 / (ploidy · Nₑ)` per generation — the reciprocal coalescent time scale —
and the mutation term gains `ploidy · mu` because both copies at the locus are exposed. A
haploid recursion would carry neither. -/
theorem hetStepWithMutation_uses_coalescentTimeScale (Ne mu H : ℝ) :
    hetStepWithMutation Ne mu H
      = (1 - 1 / coalescentTimeScale Ne) * H + ploidy * mu * (1 - H) := by
  unfold hetStepWithMutation ploidy; rw [coalescentTimeScale_eq]

/-- **The closed-population retention is the coalescent retention over the horizon.** -/
theorem retention_uses_coalescentTimeScale (r : ClosedPopulationNoMutation) :
    r.retention = (1 - 1 / coalescentTimeScale r.Ne) ^ r.horizon := by
  unfold ClosedPopulationNoMutation.retention; rw [coalescentTimeScale_eq]

/-- **Both twos in the identity-flow step are the ploidy.** Identity is created at
`1 / (ploidy · Nₑ)` per generation, and destroyed at `ploidy · rate` because either of the
two lineages of a sampled pair can be hit by the homogenising force. That second two is
what makes the fixed point `1 / (1 + 4 Nₑ · rate)` rather than `1 / (1 + 2 Nₑ · rate)`, so
it is the one a reader most needs pinned. -/
theorem ibdFlowStep_uses_coalescentTimeScale (Ne rate F : ℝ) :
    ibdFlowStep Ne rate F
      = F + (1 - F) / coalescentTimeScale Ne - ploidy * rate * F := by
  unfold ibdFlowStep ploidy; rw [coalescentTimeScale_eq]

/-- **The multiplicative identity recurrence carries the same coalescent scale.** -/
theorem ibdRecurrenceStep_uses_coalescentTimeScale (Ne rate x : ℝ) :
    ibdRecurrenceStep Ne rate x
      = (1 - rate) ^ 2 * (1 / coalescentTimeScale Ne
          + (1 - 1 / coalescentTimeScale Ne) * x) := by
  unfold ibdRecurrenceStep; rw [coalescentTimeScale_eq]

/-- **The rest point of that recurrence carries it too**, in both of its constants: the
`2 Nₑ` is the coalescent time scale and the `2 - rate` is `ploidy - rate`, the two lineages
less the one disrupting event they share. -/
theorem ibdRecurrenceFixedPoint_uses_coalescentTimeScale (Ne rate : ℝ) :
    ibdRecurrenceFixedPoint Ne rate
      = (1 - rate) ^ 2
          / ((1 - rate) ^ 2 + coalescentTimeScale Ne * rate * (ploidy - rate)) := by
  unfold ibdRecurrenceFixedPoint ploidy; rw [coalescentTimeScale_eq]

/-- **Both denominators in the scaled heterozygosity decay are the coalescent time
scale**, so `θ / (2 Nₑ)` is `θ` measured in coalescent units and not a second convention. -/
theorem hetDecayFromScaled_uses_coalescentTimeScale (Ne θ : ℝ) :
    hetDecayFromScaled Ne θ
      = (1 - 1 / coalescentTimeScale Ne) * (1 - θ / coalescentTimeScale Ne) := by
  unfold hetDecayFromScaled; rw [coalescentTimeScale_eq]

/-- **The `F_ST` flow step is `ibdFlowStep` at the summed rate, with the same two twos.**
Migration and mutation enter through their sum, and the `ploidy` in front of that sum is
the same "either lineage" factor as in `ibdFlowStep`. -/
theorem fstDriftFlowStep_uses_coalescentTimeScale (p : EvolutionaryParameters) (F : ℝ) :
    fstDriftFlowStep p F
      = F + (1 - F) / coalescentTimeScale p.Ne - ploidy * (p.mig + p.mu) * F := by
  unfold fstDriftFlowStep ploidy; rw [coalescentTimeScale_eq]

/-- **The `2 p` in Fisher's average effect is the expected diploid dosage.** The dominance
deviation is weighted by `1 - ploidy · p`, which is `q - p`, and `ploidy · p` is `E[X]` for
a dosage `X` on `0, 1, …, ploidy` in Hardy-Weinberg proportions. On a haploid scale the
weight is not this expression, so the constant is forced by the coding and belongs here. -/
theorem averageEffect_uses_ploidy (m : OneLocusArchitecture) :
    m.averageEffect = m.a + m.d * (1 - ploidy * m.p) := by
  unfold OneLocusArchitecture.averageEffect ploidy; ring

/-- **The two in the polygenic-adaptation shift is the ploidy.** The mean score is
`Σᵢ βᵢ · ploidy · pᵢ`, so its shift carries the same factor; the body writes the `2` as a
literal only because importing `Conventions` into `SelectionArchitecture` closes an import
cycle. This theorem is what stops that literal from drifting away from `ploidy`. -/
theorem polygenicAdaptationShift_uses_ploidy {m : ℕ} (β Δp : Fin m → ℝ) :
    polygenicAdaptationShift β Δp = ∑ i, β i * ploidy * Δp i := by
  unfold polygenicAdaptationShift ploidy
  simp

/-- **The four in the quadratic stepping-stone form is twice the ploidy**, the same
`4 Nₑ` scaling as every other migration-drift denominator in the corpus. Only the powers of
`m` and `σ²` distinguish this form from `demoSteppingStoneFst`; the constant does not. -/
theorem steppingStoneFstQuadratic_uses_ploidy (d Ne m σ_sq : ℝ) :
    steppingStoneFstQuadratic d Ne m σ_sq
      = d / (d + 2 * ploidy * Ne * σ_sq ^ 2 * m ^ 2) := by
  unfold steppingStoneFstQuadratic ploidy; ring

/-- **The two-locus drift step carries the coalescent time scale.** `driftLDStep` creates
identity at `1 / (ploidy · Nₑ)`, the same rate `driftLDCreationRate` names. -/
theorem driftLDStep_uses_coalescentTimeScale (Ne c Q : ℝ) :
    driftLDStep Ne c Q
      = (1 - c) ^ 2 * (1 / coalescentTimeScale Ne
          + (1 - 1 / coalescentTimeScale Ne) * Q) := by
  unfold driftLDStep; rw [coalescentTimeScale_eq]

/-- **Its slope in `Q` carries it too.** -/
theorem driftLDRetention_uses_coalescentTimeScale (Ne c : ℝ) :
    driftLDRetention Ne c = (1 - c) ^ 2 * (1 - 1 / coalescentTimeScale Ne) := by
  unfold driftLDRetention; rw [coalescentTimeScale_eq]

/-- **And so does its equilibrium**, which is a ratio of two expressions in that one
scale rather than an independently chosen constant. -/
theorem driftLDEquilibrium_uses_coalescentTimeScale (Ne c : ℝ) :
    driftLDEquilibrium Ne c
      = (1 - c) ^ 2 * (1 / coalescentTimeScale Ne) / (1 - driftLDRetention Ne c) := by
  unfold driftLDEquilibrium; rw [coalescentTimeScale_eq]

/-- **The `ρ` of the Ohta-Kimura approximation is the coalescent-scaled recombination
rate**, `2 · ploidy · Nₑ · c`, the same scaling `scaledMutationRate` applies to `μ` and
`scaledMigrationRate` to `m`. The remaining `2`, `10` and `11` are coefficients of the
moment recursion and are deliberately left as literals: they are not conventions, and
tying them to `ploidy` would assert a derivation this corpus does not have. -/
theorem ohtaKimuraSigmaDSq_uses_ploidy (Ne c : ℝ) :
    ohtaKimuraSigmaDSq Ne c
      = (10 + 2 * ploidy * Ne * c)
          / ((2 + 2 * ploidy * Ne * c) * (11 + 2 * ploidy * Ne * c)) := by
  simp only [ohtaKimuraSigmaDSq, ploidy]
  ring

/-- **The finite-deme island `F_ST` is the identity fraction at the deme-corrected scaled
migration rate.** Its `4 Nₑ m` is `scaledMigrationRate`, which
`scaledMigrationRate_eq_ploidy_form` already forces to `2 · ploidy · Nₑ · m`; the deme
correction multiplies that rate and does not touch the constant. This is the second
consumer of the one bridge, so the finite-`d` form and its `d → ∞` limit cannot acquire
different conventions. -/
theorem islandFstFiniteDemes_eq_scaled (Ne m d : ℝ) :
    islandFstFiniteDemes Ne m d
      = fstMutationDriftEquilibrium (scaledMigrationRate Ne m * islandDemeCorrection d) := by
  unfold islandFstFiniteDemes fstMutationDriftEquilibrium scaledMigrationRate; ring

/-- **The `2 μ` in the stepping-stone characteristic length counts the two lineages of a
sampled pair.** Mutation destroys the identity of a pair at rate `ploidy · μ`, so
`1 / (ploidy · μ)` is the time available to the diffusion and `L² = m σ² / (ploidy · μ)`
is the balance. Written inline the two read as arbitrary; it is the same two that
`coalescentTimeScale` puts in front of `Nₑ`. -/
theorem steppingStoneCharacteristicLength_uses_ploidy (m σ_sq μ : ℝ) :
    steppingStoneCharacteristicLength m σ_sq μ = Real.sqrt (m * σ_sq / (ploidy * μ)) := by
  unfold steppingStoneCharacteristicLength ploidy; ring

/-- **All three twos in the serial-founder within-deme time are coalescent time scales.**
A pair either coalesces inside the chain, on the scale `coalescentTimeScale N`, or survives
into the ancestral population and waits a further `coalescentTimeScale Nanc`. Three literal
twos in one body is exactly the shape in which one of them gets changed alone. -/
theorem serialFounderWithinTime_uses_coalescentTimeScale (N Nanc tAnc : ℝ) :
    serialFounderWithinTime N Nanc tAnc
      = coalescentTimeScale N * (1 - Real.exp (-tAnc / coalescentTimeScale N))
          + Real.exp (-tAnc / coalescentTimeScale N) * (tAnc + coalescentTimeScale Nanc) := by
  unfold serialFounderWithinTime coalescentTimeScale ploidy; ring

/-- **Nei's `G_ST` between a frequency and its fold is the squared contrast.** At
`p₂ = 1 - p` the mean frequency is `1/2`, the total heterozygosity `ploidy · p̄ (1 - p̄)`
is `1/2`, and `G_ST` collapses to `(1 - ploidy · p)²`. This is the only place the
denominator's `ploidy` is visible as a number, and it is what makes the next theorem an
identity rather than a proportionality. -/
theorem neiGst_at_fold (p : ℝ) : neiGst p (1 - p) = (1 - ploidy * p) ^ 2 := by
  unfold neiGst meanAlleleFreq ploidy; ring

/-- **The two-atom modulus curves are Nei's `G_ST` at the fold, divided by the product of
the two masses.**

`BundleRigidity.mOne` and `BundleRigidity.mTwo` share the numerator `|1 - 2p|`, and their
product is `(1 - 2p)² / (p (1 - p))`. The numerator is `neiGst p (1 - p)` by `neiGst_at_fold`
and the denominator is the product of the family's two masses, so the constant inside the
modulus curves is forced by the `ploidy` in `neiGst`'s normalisation rather than chosen.

This is the folded-spectrum reading of that module stated as an equation: `τ p = 1 - p` is
the ancestral/derived swap, `neiGst p (1 - p)` is symmetric under it, and the two modulus
curves are exchanged by it. `TwoAtom` imports only Mathlib and that is deliberate; the
statement therefore lives here, where both sides are visible. -/
theorem mOne_mul_mTwo_eq_neiGst_at_fold (p : ℝ) :
    BundleRigidity.mOne p * BundleRigidity.mTwo p = neiGst p (1 - p) / (p * (1 - p)) := by
  rw [neiGst_at_fold]
  unfold BundleRigidity.mOne BundleRigidity.mTwo ploidy
  rw [div_mul_div_comm, ← sq_abs (1 - 2 * p), pow_two]

end InlinedConstants

section SharedMaps

/-! ## Quantities written twice in two modules, tied here

Three more pairs share a body across modules that cannot see each other. As everywhere in
this file, the tying theorem lives where both sides are visible, and the names stay
separate because they denote different things; what is forbidden is one spelling drifting
while the other stays put. -/

/-- **The importance-weighting effective sample size is a response-to-noise
permeability.** `(Σ w)² / Σ w²` is `Γ² / V` at `Γ = Σ w` and `V = Σ w²`: the reciprocal
variance with which averaging independent copies of a summary estimates its tangent.
`TransferLearningPGS` reads it as a sample count and `Permeability` reads it as
information; the arithmetic is one map, so a change of convention in either is a change in
both. -/
theorem importanceWeightESS_eq_momentPermeability (sum_w sum_w_sq : ℝ) :
    importanceWeightESS sum_w sum_w_sq = momentPermeability sum_w sum_w_sq := rfl

/-- **The `p (1 - p)` in the drift variance is half the diploid genotype variance.**
`AncestrySpecificArchitecture.driftVariance` is `p₀ (1 - p₀) · F_ST`, the ancestral
heterozygosity that has become between-population variance. Its heterozygosity factor is
`hweGenotypeVariance` on the allele scale rather than the dosage scale, which is exactly
one `ploidy` apart, and writing it inline left that scale choice free. -/
theorem driftVariance_uses_hweGenotypeVariance (p0 fst : ℝ) :
    driftVariance p0 fst = hweGenotypeVariance p0 * fst / ploidy := by
  unfold driftVariance hweGenotypeVariance ploidy; ring

/-- **The realised target PGS variance is a retained fraction, scaled by transport.**
`PortabilityDrift.realWorldPGSVariance` erodes the additive variance by `1 - F_ST` and then
by the transported correlation. The first factor is `retainedFraction`, the same
`(1 - loss) · total` map as the ascertainment survivor and the neutral portability ratio,
so drift between the drift erosion and its siblings fails here. -/
theorem realWorldPGSVariance_eq_retainedFraction (V_A fst rhoSq : ℝ) :
    realWorldPGSVariance V_A fst rhoSq = rhoSq * retainedFraction fst V_A := by
  unfold realWorldPGSVariance retainedFraction; ring

end SharedMaps

end Calibrator
