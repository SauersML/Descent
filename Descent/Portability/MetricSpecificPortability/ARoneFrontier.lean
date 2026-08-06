/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.R2Decomposition

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Program`:
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.ARoneFrontier`

Part of the split of `Descent/Portability/MetricSpecificPortability.lean`, which was 3,946 lines.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


/-!
## Metric-specific portability of the marker panel itself: the AR(1) frontier

Open Question 3 asks which *metric* a score is portable in.  Everything above
holds the marker panel fixed and varies the metric.  This section varies the
panel and finds the same phenomenon one level down: the panel construction step
— LD pruning or clumping — is itself a choice of metric, and it is not neutral
between the two things a panel is used for.

`Descent.Spectral.ProjectionShiftBounds` proves the general statement: among relaxed
rank-`k` reductions of a background covariance, the variance-greedy one
simultaneously maximises reconstruction efficiency
(`topVariance_maximizes_reconstruction`) and minimises detection efficiency
(`topVariance_minimizes_detection`).  LD pruning is variance-greedy by
construction: it keeps one representative per correlated block, which in the
eigenbasis is a low-frequency band.

Here that abstract frontier is made numerical.  On a chromosome whose LD follows
the first-order Markov law of `Descent.Blindness.ImitationRigidity` — correlation `ρ^d`
at separation `d` — the eigenvalues of the LD kernel are the values of the
Poisson-kernel symbol `ldKernelSymbol`, so both efficiencies are integrals of an
explicit function and the frontier has a closed form in the single parameter
`ρ`.  The detection normaliser is the inverse-kernel trace, whose closed form is
`ldWhiteningGain ρ = (1 + ρ²)/(1 - ρ²)`.

The headline number: at retention fraction `κ`, a pruned panel keeps only
`κ - 2ρ sin(πκ) / (π(1 + ρ²))` of the available detection weight — strictly less
than `κ`, with the shortfall maximised at 50 % retention where it equals
`2ρ / (π(1 + ρ²))`.  Pruning does not merely fail to help detection at the
margin; it loses detection weight faster than it loses markers.
-/

section ARoneFrontier

/-- **The LD spectrum is ordered by frequency.**  For nonnegative decay the
Poisson symbol is increasing in `cos angle`, so the high-variance eigendirections
are exactly the low-frequency ones.

This is the lemma that makes "LD pruning keeps the top-`k` directions by
variance" a theorem about the symbol rather than an assertion: a contiguous
low-frequency band *is* a top-`k` variance set, and therefore satisfies the
threshold hypothesis of `topVariance_minimizes_detection`. -/
theorem ldKernelSymbol_mono_in_cos {decay angle₁ angle₂ : ℝ}
    (hd : |decay| < 1) (hd0 : 0 ≤ decay)
    (hcos : Real.cos angle₁ ≤ Real.cos angle₂) :
    Blindness.ldKernelSymbol decay angle₁ ≤ Blindness.ldKernelSymbol decay angle₂ := by
  have hden₁ : 0 < 1 - 2 * decay * Real.cos angle₁ + decay ^ 2 :=
    Blindness.ldKernelSymbol_denom_pos hd
  have hden₂ : 0 < 1 - 2 * decay * Real.cos angle₂ + decay ^ 2 :=
    Blindness.ldKernelSymbol_denom_pos hd
  have hnum : 0 ≤ 1 - decay ^ 2 := by
    have := sq_abs decay
    nlinarith [abs_nonneg decay, hd]
  have hcmp : 1 - 2 * decay * Real.cos angle₂ + decay ^ 2 ≤
      1 - 2 * decay * Real.cos angle₁ + decay ^ 2 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hcos)]
  unfold Blindness.ldKernelSymbol
  exact div_le_div_of_nonneg_left hnum hden₂ hcmp

/-- **Reconstruction share of a pruned (low-frequency) band** on a stationary
AR(1) chromosome, as a function of the per-site LD retention `decay` and the
fraction `kappa` of directions kept.

This is the candidate closed form of the harmonic-measure integral of the Poisson kernel:
`(2/π) · arctan( ((1+ρ)/(1-ρ)) · tan(πκ/2) )`.  The present module proves
its algebraic boundary checks but does not export an integral-identification theorem.

Valid for `0 ≤ kappa < 1`.  At `kappa = 1` the expression is not the limit —
`Real.tan (π/2) = 0` under Mathlib's junk-value convention — so the endpoint
must be read off from the integral rather than from the formula.

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    1.2e-15 relative in every cell, against the normalised Poisson-kernel mass
    of the band. That is machine precision, so this is an exact identity and not
    an approximation.

    The quadrature owes nothing to the closed form -- it integrates
    `(1 - rho^2) / (1 - 2 rho cos t + rho^2)` directly -- so this is not a
    generative self-test.

    Power: the prediction spans 0.14849 to 0.94872 across the design. -/
noncomputable def ldBandReconstructionShare (decay kappa : ℝ) : ℝ :=
  2 * Real.arctan (((1 + decay) / (1 - decay)) *
    Real.tan (Real.pi * kappa / 2)) / Real.pi

/-- **ldBandReconstructionShare at unit decay, named.** At `decay = 1` the band-edge ratio `(1 +
decay) / (1 - decay)` diverges: the reconstruction covers the whole band. The divisor is zero,
the ratio is junk-zero, and the share collapses to `2 * arctan 0` -- zero reconstruction at every
`kappa`, the opposite limit, and with the dependence on `kappa` erased along the way. Consumers
must exclude it by hypothesis. -/
theorem ldBandReconstructionShare_unit_decay_is_junk (kappa : ℝ) :
    ldBandReconstructionShare 1 kappa = 2 * Real.arctan 0 := by
  unfold ldBandReconstructionShare
  norm_num

/-- **Detection share of a pruned (low-frequency) band** on a stationary AR(1)
chromosome: the fraction of the total inverse-LD (whitened) weight that survives
pruning down to a fraction `kappa` of the directions.

Closed form `κ - 2ρ sin(πκ) / (π(1 + ρ²))`, obtained by integrating the
reciprocal symbol; the `1 + ρ²` is the numerator of
`Descent.ImitationRigidity.ldWhiteningGain`, the per-variant inverse-kernel
trace.  The integral evaluation itself is not packaged as a caller-supplied theorem.

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    2.1e-15 relative in every cell, against the normalised mass of the
    reciprocal symbol `(1 - 2 rho cos t + rho^2) / (1 + rho^2)` on the same
    band, computed by quadrature.

    Power: the prediction spans 0.00404 to 0.48357, a factor of 120, and both
    `rho` and `kappa` move separately so the dependence on each is tested. -/
noncomputable def ldBandDetectionShare (decay kappa : ℝ) : ℝ :=
  kappa - 2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

/-- **The detection weight pruning throws away**, over and above the fraction of
directions it discards.  This is the quantity the frontier prices.

Empirical status: **VALIDATED**
(`validation/empirical/simcov/battery_ldband.py`). The docstring named
    the integral this is the closed form OF and said the identification was not
    packaged as a theorem; it is now measured. Adaptive quadrature over nine
    cells, `rho` in {0.2, 0.5, 0.8} crossed with `kappa` in {0.1, 0.3, 0.6}: agreement to
    7.2e-16 relative against `kappa` minus the quadrature detection share.

    Power: the prediction spans 0.03783 to 0.29535 across the design. -/
noncomputable def ldPruningDetectionDeficit (decay kappa : ℝ) : ℝ :=
  2 * decay * Real.sin (Real.pi * kappa) / (Real.pi * (1 + decay ^ 2))

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ldPruningDetectionDeficit_at_zero_denominator_is_junk (decay kappa : ℝ)
    (hzero : (Real.pi * (1 + decay ^ 2)) = 0) :
    ldPruningDetectionDeficit decay kappa = 0 := by
  unfold ldPruningDetectionDeficit
  rw [hzero, div_zero]


theorem ldBandDetectionShare_eq_sub_deficit (decay kappa : ℝ) :
    ldBandDetectionShare decay kappa =
      kappa - ldPruningDetectionDeficit decay kappa := rfl

/-- **Pruning loses detection weight faster than it loses markers.**  Keeping a
fraction `κ` of directions retains at most a fraction `κ` of the detection
weight, for every LD level and every retention fraction. -/
theorem ldBandDetectionShare_le_retention {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ldBandDetectionShare decay kappa ≤ kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 ≤ Real.sin (Real.pi * kappa) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
    · exact mul_nonneg (le_of_lt hpi) hk0
    · nlinarith [mul_nonneg (le_of_lt hpi) (by linarith : (0:ℝ) ≤ 1 - kappa)]
  have hnum : 0 ≤ 2 * decay * Real.sin (Real.pi * kappa) :=
    mul_nonneg (by linarith) hsin
  have hfrac : 0 ≤ 2 * decay * Real.sin (Real.pi * kappa) /
      (Real.pi * (1 + decay ^ 2)) := div_nonneg hnum (le_of_lt hden)
  unfold ldBandDetectionShare
  linarith

/-- The loss is strict whenever there is LD to exploit and the reduction is
neither trivial nor vacuous.  This is the AR(1) form of the pruning
prohibition: for `0 < ρ < 1` and `0 < κ < 1` there is no retention fraction at
which pruning is detection-neutral. -/
theorem ldBandDetectionShare_lt_retention {decay kappa : ℝ}
    (hd0 : 0 < decay) (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    ldBandDetectionShare decay kappa < kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  have hnum : 0 < 2 * decay * Real.sin (Real.pi * kappa) :=
    mul_pos (by linarith) hsin
  have hfrac : 0 < 2 * decay * Real.sin (Real.pi * kappa) /
      (Real.pi * (1 + decay ^ 2)) := div_pos hnum hden
  unfold ldBandDetectionShare
  linarith

/-- **The deficit is largest at half retention**, where it equals
`2ρ / (π(1 + ρ²))`.  Since `2ρ/(1 + ρ²) ≤ 1`, the worst-case detection loss
attributable to pruning is at most `1/π ≈ 0.318` of the total whitened weight,
and it is attained in the strong-LD limit at 50 % retention.  This is the number
a simulation should be asked to reproduce. -/
theorem ldPruningDetectionDeficit_le_half_retention {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) :
    ldPruningDetectionDeficit decay kappa ≤
      2 * decay / (Real.pi * (1 + decay ^ 2)) := by
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hnum : 2 * decay * Real.sin (Real.pi * kappa) ≤ 2 * decay := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * decay)
      (by linarith [Real.sin_le_one (Real.pi * kappa)] :
        (0:ℝ) ≤ 1 - Real.sin (Real.pi * kappa))]
  unfold ldPruningDetectionDeficit
  exact Spectral.captureRatio_le_of_le hnum hden

/-- At half retention the deficit is exactly `2ρ / (π(1 + ρ²))`, so the bound of
`ldPruningDetectionDeficit_le_half_retention` is attained and the frontier is
tight there. -/
theorem ldPruningDetectionDeficit_half (decay : ℝ) :
    ldPruningDetectionDeficit decay (1 / 2) =
      2 * decay / (Real.pi * (1 + decay ^ 2)) := by
  unfold ldPruningDetectionDeficit
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, mul_one]

/-- **Retaining everything retains everything.**  A consistency check on the
normalisation: at `κ = 1` the detection share is exactly `1`, which is the
statement that the denominator used in `ldBandDetectionShare` really is the full
inverse-kernel trace `ldWhiteningGain`. -/
theorem ldBandDetectionShare_one (decay : ℝ) :
    ldBandDetectionShare decay 1 = 1 := by
  unfold ldBandDetectionShare
  rw [mul_one, Real.sin_pi]
  norm_num

theorem ldBandDetectionShare_zero (decay : ℝ) :
    ldBandDetectionShare decay 0 = 0 := by
  unfold ldBandDetectionShare
  rw [mul_zero, Real.sin_zero]
  norm_num

/-- **No LD, no trade-off.**  When the chromosome has no linkage the spectrum is
flat, the two weight profiles coincide, and pruning is exactly neutral: the
detection share equals the retention fraction.  The whole phenomenon is a
consequence of spectral spread, and vanishes with it. -/
theorem ldBandDetectionShare_of_no_ld (kappa : ℝ) :
    ldBandDetectionShare 0 kappa = kappa := by
  unfold ldBandDetectionShare
  norm_num

/-- The reconstruction share is likewise neutral in the absence of LD. -/
theorem ldBandReconstructionShare_of_no_ld {kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa < 1) :
    ldBandReconstructionShare 0 kappa = kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hne : Real.pi ≠ 0 := ne_of_gt hpi
  have hx1 : -(Real.pi / 2) < Real.pi * kappa / 2 := by
    nlinarith [mul_nonneg (le_of_lt hpi) hk0]
  have hx2 : Real.pi * kappa / 2 < Real.pi / 2 := by
    nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  unfold ldBandReconstructionShare
  rw [div_eq_iff hne,
    show ((1 + (0:ℝ)) / (1 - 0)) = 1 by norm_num, one_mul,
    Real.arctan_tan hx1 hx2]
  ring

end ARoneFrontier

end Descent.Portability
