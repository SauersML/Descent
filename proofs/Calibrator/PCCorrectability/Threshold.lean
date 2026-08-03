/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Sqrt

namespace Calibrator

/-!
# Rank-one spectral threshold model

The threshold is an explicit spiked-covariance model input. Applying it to a
dependent matrix still requires an external theorem or certificate justifying
the effective independent-marker count; no such bridge is silently assumed.
-/

/-- Effective size of a subgroup contrast with subgroup size `m` in a panel of
size `n`.

    Empirical status: VALIDATED (recovered spike/F over m(n-m)/n is 3.95-4.06 for m in 100..900).

    Power: the unbalanced arm of
    `validation/empirical/pc_correctability/bn_independent.py` sweeps `m` over
    `50, 100, 200, 350, 500, 650, 800, 900, 950` at `n = 1000`, so this
    definition predicts effective sizes from `47.5` at the extreme arms through
    `90.0`, `160.0` and `227.5` up to `250.0` at the balanced split — a
    fivefold span, and a hump rather than a monotone trend, so a linear or
    transposed body cannot ride along. -/
noncomputable def effectiveSubgroupSize (n m : ℝ) : ℝ := m * (n - m) / n

/-- **The effective size is the harmonic combination of the two arms**: its reciprocal is
the sum of the reciprocals of the subgroup and its complement. This pins the body — a
scaled, shifted, negated or `n`/`m`-transposed version of `m(n-m)/n` fails it — which is
why it is stated. Every other theorem mentioning `effectiveSubgroupSize` has it on both
sides of an equation, where it cancels. The direct contrast-variance theorem in
`Conventions.lean` constrains the factor `4` and the scale of `F`, but does not constrain
this definition. The reciprocal identity below is the independent repair. -/
theorem inv_effectiveSubgroupSize (n m : ℝ)
    (hm : m ≠ 0) (hnm : n - m ≠ 0) :
    (effectiveSubgroupSize n m)⁻¹ = m⁻¹ + (n - m)⁻¹ := by
  unfold effectiveSubgroupSize
  field_simp
  ring

/-- Rank-one signal contributed by a subgroup contrast with differentiation
coordinate `F`.

The constant is `4`, not `2`.  Inverting the BBP eigenvalue law on simulated
genotypes recovers `3.9920 ± 0.0045` when `F` is measured as genuine Hudson
`F_ST` on the same simulated data. The generic algebra below leaves the real
coordinate abstract; biologically safe specializations are named separately:
`hudsonBbpSpike` is the empirically calibrated PC law, whereas
`neiContrastSpike` is the exact per-frequency allele-contrast normalization.
The conversion `Hudson = 2G/(1+G)` is nonlinear, so the two must not be
substituted for one another.

    Empirical status: VALIDATED (BBP inversion recovers 3.9920 ± 0.0045 against the derived 4).

    Power: `validation/empirical/pc_correctability/which_fst_inversion.py`
    inverts at `F_ST = 0.01, 0.02, 0.05` with `n = 800` and `m = 400`, where
    this definition predicts spikes of `8.00`, `16.00` and `40.00`. The
    fivefold span is what separates the constant `4` from `2`: a wrong constant
    is a fixed factor on every one of those points and cannot be absorbed by
    the fitted `F_ST`, which is measured on the same data. -/
noncomputable def demographicSpike (n F m : ℝ) : ℝ :=
  4 * F * effectiveSubgroupSize n m

/-- BBP-style proxy threshold for `n` samples and `M` effectively independent
markers.

`M` is the effectively independent marker count, not a raw variant count.
Simulation measures the cost of confusing the two: supplying a raw count in
place of `M` overstates correctability by about twentyfold in `M`, predicting
eigenvector overlap `0.87` at `F_ST = 0.001` where the observed value is
`0.014`. That error is optimistic, whereas the spike-constant error corrected
alongside it was conservative, so the two partially masked each other. -/
noncomputable def bbpProxyThreshold (n M : ℝ) : ℝ :=
  Real.sqrt (n / M)

/-- Signed distance from the spike to the spectral proxy threshold.  A positive
value is the detectable side of the phase diagram. -/
noncomputable def pcCorrectabilityMargin (n M F m : ℝ) : ℝ :=
  demographicSpike n F m - bbpProxyThreshold n M

end Calibrator
