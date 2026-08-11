/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Fst

assert_below Descent.Conditionals Descent.Decision Descent.Portability

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

end DemographicCapacity

end

end Descent.PopGen
