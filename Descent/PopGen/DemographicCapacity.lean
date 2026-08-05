/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PCCorrectability.ImitationCapacity

namespace Descent.PopGen

noncomputable section

/-!
# Two demographic spike laws, separated by convention

`Descent.PCCorrectability.ImitationCapacity` proves that the corpus's
`demographicSpike` is the trace-window certificate increment: a spike level
times the spike load of the centered subgroup contrast, the load being
`effectiveSubgroupSize`. That algebraic statement deliberately carries an
abstract real coordinate `F`; it cannot decide which population-genetic
differentiation functional a biological analysis supplied.

There are two legitimate specializations, and conflating them causes an almost
twofold error at weak differentiation:

* `neiContrastSpike` is an exact per-frequency identity. Four times Nei's
  `G_ST` is the standardized allele-frequency contrast variance.
* `hudsonBbpSpike` is the empirical PC/BBP law. The validation experiment used
  genuine ratio-of-averages Hudson `F_ST` and recovered coefficient
  `3.9920 ± 0.0045` against the theoretical `4`.

The exact conversion is `Hudson = 2G/(1+G)`, so the Hudson-calibrated spike is
`8G/(1+G)` times the subgroup load, not `4G` times that load. This module wires
both laws to the same certificate geometry while keeping their biological
meanings separate.

The module exists as a separate file for an import reason and not a conceptual
one: `Conventions` imports `StratificationConfounding`, which imports
`PCCorrectability`, so `ImitationCapacity` cannot import `Conventions` without
a cycle.  The composition therefore lives downstream of both.
-/

section DemographicCapacity

/-- **The spike level of a subgroup contrast**: the variance of the
standardized allele-frequency contrast between the two subgroups.

This is the level of the exact Nei-normalized allele-frequency contrast. It is
written as a quantity rather than as an ambiguously named `F_ST` multiple:
`contrastSpikeLevel_eq_four_neiGst` derives it from
`Core.four_neiGst_eq_standardizedContrastVariance` instead of
stipulating it.

    Empirical status: DERIVED as an identity for Nei's `G_ST`; distinct from
    the empirically validated Hudson BBP level. -/
noncomputable def contrastSpikeLevel (p₁ p₂ : ℝ) : ℝ :=
  (p₁ - p₂) ^ 2 / (Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂))

/-- **contrastSpikeLevel at its junk point, named.** The divisor is `p̄ (1 - p̄)` inside
`meanAlleleFreq`, which vanishes when both populations are fixed. Numerator and denominator
vanish together and Lean returns `0`: no contrast spike, which a locus with identical
intermediate frequencies also gives. The guard is not visible in this definition's own body, so
reading this line does not reveal that a branch exists. Consumers must exclude the argument that
makes the guard vanish. -/
theorem contrastSpikeLevel_monomorphic_is_junk :
    contrastSpikeLevel 0 0 = 0 := by
  unfold contrastSpikeLevel Descent.Core.meanAlleleFreq Descent.Core.midpoint
  norm_num

/-- **No contrast, no spike.** Two populations at the same allele frequency produce a level of
exactly zero, whatever the frequency is. The proportionality to Nei's `G_ST` fixes the scale;
this fixes the origin, and a body with an additive offset would satisfy the first and not this. -/
theorem contrastSpikeLevel_self (p : ℝ) :
    contrastSpikeLevel p p = 0 := by
  unfold contrastSpikeLevel
  norm_num

/-- **The level is four times Nei's `G_ST`, derived rather than stipulated.** -/
theorem contrastSpikeLevel_eq_four_neiGst (p₁ p₂ : ℝ)
    (h : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0) :
    contrastSpikeLevel p₁ p₂ = 4 * Descent.Core.neiGst p₁ p₂ := by
  unfold contrastSpikeLevel
  exact (Descent.Core.four_neiGst_eq_standardizedContrastVariance p₁ p₂ h).symm

/-- **The exact Nei contrast law composed with the certificate load.**

`contrastSpikeLevel` is the exact allele-frequency contrast level; the
trace-window spike load of the
subgroup-contrast direction is the load, pinned to `effectiveSubgroupSize` by
`dot_demographicSpikeDirection`.  Neither factor is a free parameter and no
numeral appears. -/
theorem neiContrastSpike_eq_contrastSpikeLevel_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (h : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    Portability.neiContrastSpike (N : ℝ) (m : ℝ) p₁ p₂ =
      contrastSpikeLevel p₁ p₂ *
        (Portability.traceWindowBudgetClass base budget).spikeLoad a
          (Portability.demographicSpikeDirection N m) := by
  rw [contrastSpikeLevel_eq_four_neiGst p₁ p₂ h,
    Portability.traceWindow_spikeLoad_demographic m hmn hN base budget a]
  unfold Portability.neiContrastSpike Portability.demographicSpike
  ring

/-- **The exact Nei contrast spike written without a free coefficient.**

The spike level is the standardized contrast variance, pinned by
`four_neiGst_eq_standardizedContrastVariance`, so a bare constant such as `2`
cannot stand in for it. The load is the trace-window spike load of the
subgroup-contrast direction, pinned by `dot_demographicSpikeDirection`.  Both
factors are quantities rather than names, and their equality is proved directly. -/
theorem neiContrastSpike_eq_contrastVariance_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (h : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    Portability.neiContrastSpike (N : ℝ) (m : ℝ) p₁ p₂ =
      ((p₁ - p₂) ^ 2 / (Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂))) *
        (Portability.traceWindowBudgetClass base budget).spikeLoad a
          (Portability.demographicSpikeDirection N m) := by
  rw [Portability.neiContrastSpike_eq_contrastVariance_mul_effectiveSize (N : ℝ) (m : ℝ) p₁ p₂ h,
    Portability.traceWindow_spikeLoad_demographic m hmn hN base budget a]

/-- **The empirically calibrated Hudson BBP spike is level times load.** -/
theorem hudsonBbpSpike_eq_level_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    Portability.hudsonBbpSpike (N : ℝ) (m : ℝ) p₁ p₂ =
      (4 * Descent.Core.hudsonFst p₁ p₂) *
        (Portability.traceWindowBudgetClass base budget).spikeLoad a
          (Portability.demographicSpikeDirection N m) := by
  rw [Portability.traceWindow_spikeLoad_demographic m hmn hN base budget a]
  unfold Portability.hudsonBbpSpike Portability.demographicSpike
  ring

/-- **The Hudson BBP spike on the Nei scale.** This is the exact formula that
prevents the empirically validated coefficient `4` from being attached to the
wrong differentiation estimator. -/
theorem hudsonBbpSpike_eq_nei_conversion_mul_spikeLoad
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    Portability.hudsonBbpSpike (N : ℝ) (m : ℝ) p₁ p₂ =
      (8 * Descent.Core.neiGst p₁ p₂ / (1 + Descent.Core.neiGst p₁ p₂)) *
        (Portability.traceWindowBudgetClass base budget).spikeLoad a
          (Portability.demographicSpikeDirection N m) := by
  rw [Portability.hudsonBbpSpike_eq_eight_neiGst_div_one_add_mul_effectiveSize
      (N : ℝ) (m : ℝ) p₁ p₂ hpos hbar,
    Portability.traceWindow_spikeLoad_demographic m hmn hN base budget a]

/-- **Exact multiplicative convention gap at certificate level.** The Hudson-calibrated
stratification spike is `2/(1+G_ST)` times the Nei-calibrated spike. Thus the estimator choice
rescales the complete PC-correction certificate, not merely a descriptive scalar. -/
theorem hudsonBbpSpike_eq_nei_multiplier_mul_neiContrastSpike
    (N m p₁ p₂ : ℝ)
    (hpos : 0 < p₁ * (1 - p₂) + p₂ * (1 - p₁))
    (hbar : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0) :
    Portability.hudsonBbpSpike N m p₁ p₂ =
      (2 / (1 + Descent.Core.neiGst p₁ p₂)) * Portability.neiContrastSpike N m p₁ p₂ := by
  rw [Portability.hudsonBbpSpike_eq_eight_neiGst_div_one_add_mul_effectiveSize
    N m p₁ p₂ hpos hbar]
  unfold Portability.neiContrastSpike Portability.demographicSpike
  ring

/-- On the biological range `0 ≤ G_ST ≤ 1`, the Hudson-to-Nei spike multiplier lies between one
and two. Weak differentiation approaches the factor-two boundary; complete differentiation makes
the two conventions agree. -/
theorem neiSpikeMultiplier_mem_unit_two (G : ℝ) (hG0 : 0 ≤ G) (hG1 : G ≤ 1) :
    1 ≤ 2 / (1 + G) ∧ 2 / (1 + G) ≤ 2 := by
  have hden : 0 < 1 + G := by linarith
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    nlinarith

/-- **The imitation criterion for the empirically calibrated stratification
spike.**

A demographic spike between two subgroups with allele frequencies `p₁` and `p₂`
is a legal member of the trace-window background class — undetectable at any
sample size, by any procedure — exactly when the certificate increment fits
inside the budget.  Nothing here is a spectral quantity: `bbpProxyThreshold`
does not appear, because the imitation question does not involve it. -/
theorem hudsonCalibrated_stratification_imitable_if_within_budget
    {N : ℕ} (m : ℕ) (p₁ p₂ : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (hfst : 0 ≤ Descent.Core.hudsonFst p₁ p₂)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ)
    (hbase : Blindness.VarianceNonneg (S₀ - base))
    (hbudget : Portability.traceForm S₀ +
      Portability.hudsonBbpSpike (N : ℝ) (m : ℝ) p₁ p₂ ≤ budget) :
    (Portability.traceWindowBudgetClass base budget).IsNull
      ((Portability.traceWindowBudgetClass base budget).spiked S₀ (4 * Descent.Core.hudsonFst p₁ p₂)
        (Portability.demographicSpikeDirection N m)) :=
  Portability.imitable_within_traceWindowBudget m (Descent.Core.hudsonFst p₁ p₂)
    hfst hmn hN base S₀ budget hbase hbudget

/-- **The correction to the empirically Hudson-calibrated
`pcCorrectabilityMargin`, stated on genotypes.**

With `F` pinned to genuine Hudson `F_ST`, the sign of the existing margin is the
detectability criterion exactly when the trace window is active at the
baseline.  Away from that case the criterion is
`stratificationCertificateMargin`, which carries the headroom the existing
quantity omits. -/
theorem hudsonCalibrated_rigid_pcCorrectabilityMargin_is_the_criterion
    {N : ℕ} (m : ℕ) (p₁ p₂ markerCount : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (a : Unit) :
    0 < Portability.pcCorrectabilityMargin (N : ℝ) markerCount (Descent.Core.hudsonFst p₁ p₂) (m : ℝ) ↔
      (Portability.traceWindowBudgetClass base (Portability.traceForm S₀)).bound a +
          Portability.bbpProxyThreshold (N : ℝ) markerCount <
        (Portability.traceWindowBudgetClass base (Portability.traceForm S₀)).form a
          ((Portability.traceWindowBudgetClass base (Portability.traceForm S₀)).spiked S₀
            (4 * Descent.Core.hudsonFst p₁ p₂) (Portability.demographicSpikeDirection N m)) :=
  Portability.rigid_certificate_exceeds_ceiling_iff_pcCorrectabilityMargin_pos m
    (Descent.Core.hudsonFst p₁ p₂) markerCount hmn hN base S₀ a

end DemographicCapacity

end

end Descent.PopGen
