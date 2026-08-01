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
`F`, where `F` is Hudson `F_ST` between the two subgroups.

The constant is `4`, not `2`.  Inverting the BBP eigenvalue law on simulated
genotypes recovers `3.9920 ± 0.0045` with `F` measured as Hudson `F_ST` on the
same simulated data, and the resulting sharp criterion `1 < M F² n` is the
Patterson-Price-Reich boundary.  A constant of `2` corresponds instead to
reading `F` as `Var(p₁ - p₂) / (p̄ (1 - p̄)) = 2 F_ST`; that is self-consistent
but is not a standard quantity, so the scale of `F` is pinned to Hudson `F_ST`
here rather than left to the caller. -/
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
