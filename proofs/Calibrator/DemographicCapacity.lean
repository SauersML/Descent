import Calibrator.Conventions

namespace Calibrator

noncomputable section

/-!
# The demographic spike as a certificate value, with `F` pinned

`Calibrator.PCCorrectability.ImitationCapacity` proves that the corpus's
`demographicSpike` is the trace-window certificate increment: a spike level
times the spike load of the centered subgroup contrast, the load being
`effectiveSubgroupSize`.  That statement carries `F` as a free argument, which
is exactly the defect `Calibrator.Conventions` was written to remove — `F` free
is how the spike constant was able to be wrong by a factor of two.

This module composes the two.  `Conventions` pins the level: four times Hudson
`F_ST` is the variance of the standardized subgroup contrast, which is
`four_hudsonFst_eq_standardizedContrastVariance`.  `ImitationCapacity` pins the
load: it is the squared length of the contrast direction.  Their product is the
certificate increment, and the composition below has no free constant and no
free `F` anywhere in it.

The module exists as a separate file for an import reason and not a conceptual
one: `Conventions` imports `StratificationConfounding`, which imports
`PCCorrectability`, so `ImitationCapacity` cannot import `Conventions` without
a cycle.  The composition therefore lives downstream of both.
-/

section DemographicCapacity

/-- **The spike level of a subgroup contrast**: the variance of the
standardized allele-frequency contrast between the two subgroups.

This is the level, in the linear program's sense, that a demographic spike
enters at — the multiplier on the spike load.  It is written as a quantity
rather than as a numeral times `F_ST` for the reason that the numeral is what
was wrong before: `contrastSpikeLevel_eq_four_hudsonFst` derives it from
`Conventions.four_hudsonFst_eq_standardizedContrastVariance` instead of
stipulating it, so a spike level built on `2 F_ST` is unprovable here rather
than merely differently calibrated.

    Empirical status: UNTESTED as an estimator. The constant relating it to
    Hudson `F_ST` is DERIVED, and simulation recovers `3.9920 ± 0.0045` against
    the derived `4` (see `Conventions.spikeIdentification`). -/
noncomputable def contrastSpikeLevel (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- **The level is four times Hudson `F_ST`, derived rather than stipulated.** -/
theorem contrastSpikeLevel_eq_four_hudsonFst (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    contrastSpikeLevel p₁ p₂ = 4 * hudsonFst p₁ p₂ := by
  unfold contrastSpikeLevel
  exact (four_hudsonFst_eq_standardizedContrastVariance p₁ p₂ h).symm

/-- **The linear program's two factors, for a stratified genotype panel.**

The demographic spike is the level times the load: `contrastSpikeLevel` is the
level, pinned to Hudson `F_ST`; the trace-window spike load of the
subgroup-contrast direction is the load, pinned to `effectiveSubgroupSize` by
`dot_demographicSpikeDirection`.  Neither factor is a free parameter and no
numeral appears. -/
theorem demographicSpike_eq_contrastSpikeLevel_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    demographicSpike (N : ℝ) (hudsonFst p₁ p₂) (m : ℝ) =
      contrastSpikeLevel p₁ p₂ *
        (traceWindowBudgetClass base budget).spikeLoad a
          (demographicSpikeDirection N m) := by
  rw [contrastSpikeLevel_eq_four_hudsonFst p₁ p₂ h,
    traceWindow_spikeLoad_demographic m hmn hN base budget a]
  unfold demographicSpike
  ring

/-- **The demographic spike is the certificate increment, with `F` pinned to
Hudson `F_ST` and no numeral anywhere on the right.**

The spike level is the standardized contrast variance — pinned by
`four_hudsonFst_eq_standardizedContrastVariance`, so the old constant `2`
cannot be substituted — and the load is the trace-window spike load of the
subgroup-contrast direction, pinned by `dot_demographicSpikeDirection`.  Both
factors are now quantities rather than names, which is the whole point of the
`Identification` mechanism applied to the object that motivated it. -/
theorem demographicSpike_eq_contrastVariance_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    demographicSpike (N : ℝ) (hudsonFst p₁ p₂) (m : ℝ) =
      ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
        (traceWindowBudgetClass base budget).spikeLoad a
          (demographicSpikeDirection N m) := by
  rw [demographicSpike_eq_contrastVariance_mul_effectiveSize (N : ℝ) (m : ℝ) p₁ p₂ h,
    traceWindow_spikeLoad_demographic m hmn hN base budget a]

/-- **The imitation criterion for a stratified panel, with `F` pinned.**

A demographic spike between two subgroups with allele frequencies `p₁` and `p₂`
is a legal member of the trace-window background class — undetectable at any
sample size, by any procedure — exactly when the certificate increment fits
inside the budget.  Nothing here is a spectral quantity: `bbpProxyThreshold`
does not appear, because the imitation question does not involve it. -/
theorem stratification_imitable_iff_within_budget
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (hfst : 0 ≤ hudsonFst p₁ p₂)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ)
    (hbase : VarianceNonneg (S₀ - base))
    (markerCount : ℝ)
    (hmargin : 0 < pcCorrectabilityMargin (N : ℝ) markerCount
      (hudsonFst p₁ p₂) (m : ℝ))
    (hbudget : traceForm S₀ +
      demographicSpike (N : ℝ) (hudsonFst p₁ p₂) (m : ℝ) ≤ budget) :
    (traceWindowBudgetClass base budget).IsNull
      ((traceWindowBudgetClass base budget).spiked S₀ (4 * hudsonFst p₁ p₂)
        (demographicSpikeDirection N m)) :=
  imitable_despite_positive_pcCorrectabilityMargin m (hudsonFst p₁ p₂) markerCount
    hfst hmn hN base S₀ budget hbase hbudget hmargin

/-- **The correction to `pcCorrectabilityMargin`, stated on genotypes.**

With `F` pinned to Hudson `F_ST`, the sign of the existing margin is the
detectability criterion exactly when the trace window is active at the
baseline.  Away from that case the criterion is
`stratificationCertificateMargin`, which carries the headroom the existing
quantity omits. -/
theorem rigid_pcCorrectabilityMargin_is_the_criterion
    {N : ℕ} (m : ℕ) (p₁ p₂ markerCount : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (a : Unit) :
    0 < pcCorrectabilityMargin (N : ℝ) markerCount (hudsonFst p₁ p₂) (m : ℝ) ↔
      (traceWindowBudgetClass base (traceForm S₀)).bound a +
          bbpProxyThreshold (N : ℝ) markerCount <
        (traceWindowBudgetClass base (traceForm S₀)).form a
          ((traceWindowBudgetClass base (traceForm S₀)).spiked S₀
            (4 * hudsonFst p₁ p₂) (demographicSpikeDirection N m)) :=
  rigid_certificate_exceeds_ceiling_iff_pcCorrectabilityMargin_pos m
    (hudsonFst p₁ p₂) markerCount hmn hN base S₀ a

end DemographicCapacity

end

end Calibrator
