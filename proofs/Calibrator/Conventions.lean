import Calibrator.PopulationGeneticsFoundations
import Calibrator.DriftRegime
import Calibrator.ImitationRigidity
import Calibrator.DemographicHistory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.PCCorrectability.Threshold
import Calibrator.Identification
import Calibrator.AssortativeMatingPGS
import Calibrator.CovarianceStructure
import Calibrator.AncestrySpecificPower
import Calibrator.GeneticArchitectureDiscovery
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
  `n` cannot be offered as an observable that does. That is `Identification`
  in `Calibrator.Identification`.
-/

section Ploidy

/-- Number of homologous copies per locus. Every non-exponent factor of two in
this development traces to this constant, and every factor of four to twice
it. The corpus currently restates the convention inline at ninety-nine
definition sites: seventy-eight carrying a two and twenty-one a four. The
theorems in this section tie the independently written ones back here, so that
drift between them is a compile error rather than a silent disagreement. -/
noncomputable def ploidy : ℝ := 2

/-- Genotype variance at a locus in Hardy-Weinberg proportions, for dosage
coded `0, 1, …, ploidy`.

    Empirical status: UNTESTED. -/
noncomputable def hweGenotypeVariance (p : ℝ) : ℝ := ploidy * p * (1 - p)

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations. -/
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

/-- **Cross-check: the drift `F_ST` uses the coalescent time scale**, so the
`2 Nₑ` inside it is the same `ploidy · Nₑ` and not a separate choice. -/
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
island-model `F_ST`, where four names really did denote one quantity and are now one.

There used to be two copies of this theorem, one per copy of the migration average. -/

theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    effectiveSymmetricMigration m₁₂ m₂₁ = meanAlleleFreq m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration meanAlleleFreq; ring

/-- **Nei's `G_ST`, explicitly distinguished from Hudson's `F_ST`.** One minus the ratio
of mean within-subgroup heterozygosity to TOTAL heterozygosity is the
definition of `G_ST`; the docstring said exactly that and nobody noticed it
described a different estimator from the one in the name. Hudson's `F_ST`
divides by the BETWEEN-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`, not by
the total-pool `2·p̄·(1-p̄)`. The two denominators differ by exactly
`(p₁-p₂)²/2`, so THE DENOMINATORS agree iff `p₁ = p₂`, and the two ESTIMATORS
agree iff `G_ST = 0` or `G_ST = 1` -- that is, only where the differentiation
is degenerate.

**A previous version of this docstring said they agree when `p₁ = p₂` OR
`p̄ = 1/2`. THE SECOND DISJUNCT IS FALSE**, and it is false in both readings.
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
    error. The genuine Hudson body now owns `hudsonFst`. Read every `neiGst` in the *contrast-normalization* chain --
    including `four_neiGst_eq_standardizedContrastVariance` -- as Nei's `G_ST`.
    The algebra is unaffected: `4·G_ST` is the standardized allele-frequency
    contrast variance for THIS body. It is not the empirically calibrated BBP
    spike. That law uses genuine Hudson `F_ST` and is named `hudsonBbpSpike`
    below. At weak differentiation the latter is almost twice
    `neiContrastSpike`; silently exchanging them is therefore a biologically
    material error, not a harmless change of notation.

    **This sentence used to end "at `p̄ ≠ 1/2`", which is the third instance of
    one false claim in this file** and the last to be found. It implies the
    factor VANISHES at `p̄ = 1/2`. It does not: measured ratios along that
    exact slice are `1.995`, `1.923`, `1.724`, `1.220` -- monotone in
    `|p₁ - p₂|` and never reaching `1`. The identity already in this file
    settles it without any measurement: `hudsonFst_eq_of_neiGst` gives
    `Hudson = 2G/(1+G)`, which equals `G` only at `G = 0` or `G = 1`, so the
    exception named here is empty apart from the endpoints.
    `neiGst_ne_hudsonFst_at_mean_half` certifies it at
    `(9/10, 1/10)` -- `p̄ = 1/2` exactly, ratio `50/41`.

    Why it took three passes to remove: the pre-existing witness
    `neiGst_ne_hudsonFst` sits at `p̄ = 2/5`, OUTSIDE the slice the claim
    names, so the claim looked checked while nothing tested it. A witness
    outside the exception cannot refute the exception. If you are ever tempted
    to reintroduce an "except at `p̄ = 1/2`" caveat,
    `neiGst_ne_hudsonFst_at_mean_half` below is what will stop you, and
    it is placed there for that purpose.

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
    not fitted to. -/
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

/-- **A witness ON the `p̄ = 1/2` slice**, which two docstrings and three
`checks.py` clauses used to name as a place where the estimators agree.

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

RENAMED from `neiGstFromFrequencies_eq_hudsonFst`. That name asserted that
`PopulationGeneticsFoundations.simpleFst` is Hudson's `F_ST`. The theorem is
true and the name was the defect: what it proves is that two independently
written spellings of NEI's `G_ST` coincide. Neither side is Hudson's estimator; that one is
`hudsonFst`, and `neiGst_ne_hudsonFst` exhibits a point where it
differs from both of these. -/
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

/-- **The exact allele-frequency-contrast normalization.**

This is deliberately not called the BBP spike: its input is Nei's `G_ST`, and
its exact interpretation is the standardized allele-frequency contrast
variance times the subgroup load. -/
noncomputable def neiContrastSpike (n m p₁ p₂ : ℝ) : ℝ :=
  demographicSpike n (neiGst p₁ p₂) m

/-- **The empirically calibrated PC/BBP normalization.**

The `F` supplied to the validation experiment was the ratio-of-averages Hudson
estimator. This named specialization prevents that empirical law from being
silently reinterpreted as the different Nei functional. -/
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

/-- **The Nei contrast spike, as an identification rather than a definition.**

This is the mechanism of `Calibrator.Identification` applied to the quantity
that motivated it. It identifies the per-frequency contrast normalization; it
does not claim that the BBP experiment used Nei's estimator.

    Empirical status: UNTESTED. -/
noncomputable def neiContrastSpikeIdentification (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    Identification ℝ where
  formula := neiContrastSpike n m p₁ p₂
  observable :=
    ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
      effectiveSubgroupSize n m
  derivation := neiContrastSpike_eq_contrastVariance_mul_effectiveSize n m p₁ p₂ h
  evidence := Evidence.derived

end Differentiation

section EquilibriumAgreements

/-! **The island-model `F_ST` is now one definition.** It used to be written out
independently in several modules — `DemographicHistory.demoIslandModelFst`,
`PopulationGeneticsFoundations.islandModelFst`, `AncestrySpecificArchitecture.equilibriumFst`
and `PortabilityDrift.fstMigrationDriftEquilibrium` — each spelling out its own factor of
four, and this file carried a cross-check theorem per pair to keep them in step. The copies
are gone in favour of the single `fstMigrationDriftEquilibrium`, so the cross-checks have
nothing left to relate.

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

Five definitions across five modules used to spell out `2 p (1 - p)`
independently, and none was related to any other, so a change to the ploidy
convention in one would have left the others silently disagreeing. Four of the
five are gone: `CovarianceStructure.genotypeVarianceAtLocus`,
`GeneticArchitectureDiscovery.tagGenotypeVariance` and
`StratificationConfounding.heterozygosity` were deleted and their references
repointed, and `AncestrySpecificPower.ancestryHeterozygosity` was renamed
`hweHeterozygosity`. What survives is one genotype variance and one
heterozygote frequency, both in `AncestrySpecificPower`, related there by
`hweHeterozygosity_eq_genotypeVarianceHWE`. These two theorems tie that pair
back to `ploidy`, so the convention still has exactly one place to change. -/

theorem genotypeVarianceHWE_eq_hwe (p : ℝ) :
    genotypeVarianceHWE p = hweGenotypeVariance p := by
  unfold genotypeVarianceHWE hweGenotypeVariance ploidy; ring

theorem hweHeterozygosity_eq_hwe (p : ℝ) :
    hweHeterozygosity p = hweGenotypeVariance p := by
  unfold hweHeterozygosity hweGenotypeVariance ploidy; ring

/-! ### Tying the island-model equilibrium back to the scaled rate

`1 / (1 + 4 Nₑ m)` used to be spelled out by several definitions across several modules,
and this section carried one bridge theorem per copy — three of them with identical
statements and identical proofs. There is now a single definition, so there is a single
bridge: it is the migration-drift equilibrium at the scaled migration rate. -/

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

theorem ldDecayRatePerGen_eq_inv_timeScale (Ne : ℝ) :
    ldDecayRatePerGen Ne = 1 / coalescentTimeScale Ne := by
  unfold ldDecayRatePerGen; rw [coalescentTimeScale_eq]

/-- **Cross-check: the `2 Nₑ` inside `coalFst` is the coalescent time scale.**
`coalFst t Ne = t / (t + 2 Nₑ)` is `t / (t + E[T_within])`, and `E[T_within]`
is `ploidy · Nₑ` generations. Writing the two inline left the constant free;
this states which two it is. -/
theorem coalFst_uses_coalescentTimeScale (t Ne : ℝ) :
    coalFst t Ne = t / (t + coalescentTimeScale Ne) := by
  unfold coalFst; rw [coalescentTimeScale_eq]

/-! ### The coalescent `F_ST` map, no longer written out twice

`DemographicHistory.fstFromCoalescenceTime` and
`PopulationGeneticsFoundations.coalFst` were the same function under two names.
`coalFst` is the one simulation validated as split `F_ST`, being unbiased
against branch-mode divergence where the drift formula was biased upward by up
to 28 percent, so it is the survivor; `fstFromCoalescenceTime` has been deleted
and its uses in `DemographicHistory` now call `coalFst` directly. -/

/-! ### The harmonic mean, no longer written out twice

`MetricSpecificPortability.f1ScoreMetric` and `OpenQuestions.f1Score` were the
same expression under two names in two modules, with no theorem relating them.
`f1ScoreMetric` has been deleted and `MetricSpecificPortability` now calls
`f1Score`. -/

/-- Wright's compounding identity: one minus the product of retentions. It is
written once for the two branches of a split and once for the two levels of
the `F`-statistic hierarchy. -/
theorem pairwiseFstFromBranches_eq_wrightFIT (a b : ℝ) :
    pairwiseFstFromBranches a b = wrightFIT a b := by
  unfold pairwiseFstFromBranches wrightFIT; ring_nf

/-! ### The per-generation retention factor, written out in four modules

`1 - 1/(2 Nₑ)` is the probability that two lineages fail to coalesce in one
generation. It is spelled out independently in `PhenomeWidePortability`,
`LDDecayTheory`, `PopulationGeneticsFoundations` and `PortabilityDrift`. -/

theorem neutralDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) :
    neutralDriftFactor Ne t = (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold neutralDriftFactor; rw [coalescentTimeScale_eq]

/-- RESTATED. This used to read
`ldRetainedFraction Ne t = (1 - 1/coalescentTimeScale Ne)^t`, which was true of
a body that had dropped the recombination factor and false of the corrected
one. It is restated rather than deleted because the convention it was pinning
-- that the drift channel enters through `2·Nₑ` -- is still present and still
worth pinning; what changed is that drift is no longer the whole retention. -/
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

/-- RESTATED. This used to read `ldHalfLife Ne = coalescentTimeScale Ne * log 2`,
which is the `r → 0` limit and is false of the corrected body at every `r > 0`.
The `2·Nₑ` convention still appears, now inside the retention whose logarithm
sets the half-life, and that is what this states. -/
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

theorem stabilizingPortability_uses_ploidy (r2_0 fst strength : ℝ) :
    stabilizingPortability r2_0 fst strength
      = r2_0 * max 0 (1 - ploidy * fst) * Real.exp (-strength * fst) := by
  rfl

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

theorem diversifyingPortability_uses_ploidy (r2_0 fst lam_turn : ℝ) :
    diversifyingPortability r2_0 fst lam_turn
      = r2_0 * max 0 (1 - ploidy * fst) * (Real.exp (-lam_turn * fst)) ^ 2 := by
  rfl

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
survival along a genealogy, and admixture-LD decay are one map. -/
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

theorem ascertainment_loss_eq_retainedFraction (coverage v_causal : ℝ) :
    ascertainment_loss coverage v_causal = retainedFraction coverage v_causal := by
  unfold ascertainment_loss retainedFraction; ring

theorem neutralPortabilityRatioLD_eq_retainedFraction (fst ld : ℝ) :
    neutralPortabilityRatioLD fst ld = retainedFraction fst ld := by
  unfold neutralPortabilityRatioLD retainedFraction; ring

theorem presentDayPGSVariance_eq_retainedFraction (V_A fst : ℝ) :
    presentDayPGSVariance V_A fst = retainedFraction fst V_A := by
  unfold presentDayPGSVariance pgsVarianceFromHet retainedFraction; ring

/-! `explainedR2FromTransportMoments_eq_pgsR2` used to sit here. It was the `Eq.symm` of
`TransferLearningPGS.pgsR2_eq_explainedR2FromTransportMoments`, which states the same
identity and proves it by `rfl` — the two bodies are the same term, not merely `ring`-equal.
Two names for one restatement is one restatement too many, and nothing referenced either,
so the copy in this file is deleted and the identity is stated once, next to `pgsR2`. -/

/-! The two portability ratios were the same quotient of transported metrics,
written once in `SimulationValidation` and once in
`GeneticArchitectureDiscovery`. `sourceTargetPortabilityRatio` has been deleted
and `GeneticArchitectureDiscovery` now calls `mechanisticPortabilityRatio`. -/

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
  assumption: `ClosedPopulationNoMutation.mutation_negligible`,
  `InfiniteIslandLimit.limit_adequate`.
* **Tied to a regime object.** A theorem identifies the bare formula with a quantity of a
  named regime: `closedPopulation_het_eq_neutralDriftFactor`,
  `heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss` and its two siblings.
* **As an external obligation.** The quantity the closed form claims to be is a field
  supplied by the caller, and the regime is the hypothesis that they agree:
  `PowerAgreement`, `GaussianLiabilityRegime`, `FittedSelectionLaw`. Used where the
  development has no derivation available, so that asserting one would be the
  `singletonProportion` failure.
* **As a proved failure.** The departure is itself a theorem, so the limit is checkable
  rather than described: `neutralAFBenchmarkRatio_cannot_reach_measured`,
  `InfiniteIslandLimit.two_demes_excess`,
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

`heterozygosityLossDerived` and `heterozygosityLossFromDrift` share a body, and `DriftRegime` names that
coincidence as the defect rather than a convenience: a within-population heterozygosity
loss and a between-population variance ratio are different quantities, and the shared body
is what let one be substituted for the other. They are deliberately *not* merged. This
theorem records that `heterozygosityLossDerived` inherits the closed-population regime through that
shared body — which is the fact a reader needs in order to see that its `F_ST` reading is
only available in the regime where the loss reading is.

Note the argument orders differ: `heterozygosityLossFromDrift` takes `(t, Ne)` and
`heterozygosityLossDerived` takes `(Ne, t)`, so the same call spelled the same way means different things
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

end EquilibriumAgreements

end Calibrator
