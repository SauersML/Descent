import Mathlib.Data.Real.Sqrt

namespace Calibrator

/-!
# Rank-one spectral threshold model

The threshold is an explicit spiked-covariance model input. Applying it to a
dependent matrix still requires an external theorem or certificate justifying
the effective independent-marker count; no such bridge is silently assumed.
-/

/-- Effective size of a subgroup contrast with subgroup size `m` in a panel of
size `n`. -/
noncomputable def effectiveSubgroupSize (n m : ℝ) : ℝ := m * (n - m) / n

/-- Rank-one signal contributed by a subgroup contrast with differentiation
`F`. -/
noncomputable def demographicSpike (n F m : ℝ) : ℝ :=
  2 * F * effectiveSubgroupSize n m

/-- BBP-style proxy threshold for `n` samples and `M` effectively independent
markers. -/
noncomputable def bbpProxyThreshold (n M : ℝ) : ℝ :=
  Real.sqrt (n / M)

/-- Signed distance from the spike to the spectral proxy threshold.  A positive
value is the detectable side of the phase diagram. -/
noncomputable def pcCorrectabilityMargin (n M F m : ℝ) : ℝ :=
  demographicSpike n F m - bbpProxyThreshold n M

end Calibrator
