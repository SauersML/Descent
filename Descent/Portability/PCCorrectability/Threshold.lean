/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.ReferenceEvaluation
import Mathlib.Data.Real.Sqrt

namespace Descent

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

/-- **effectiveSubgroupSize at zero n, named.** An empty cohort has no effective subgroup size and
the quantity is undefined. Lean returns `0`, which is also what a genuinely balanced split of an
empty design would give, so the degenerate case is not distinguishable. Consumers must require
`n ≠ 0`. -/
theorem effectiveSubgroupSize_zero_n_is_junk (m : ℝ) :
    effectiveSubgroupSize 0 m = 0 := by
  unfold effectiveSubgroupSize
  simp

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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem demographicSpike_at_reference_point :
    demographicSpike 4 1 1 = 3 := by
  norm_num [demographicSpike, effectiveSubgroupSize]

/-- **The reference point above, carrying the competitor it rejects.**

Moving the evaluation off `m = n` repairs one theorem.  This term is the
obligation that stops the defect recurring: `ReferenceEvaluation.ofScale`
cannot be applied unless the body is nonzero at the point, and
`scale_competitor_ne_iff` proves that nonzeroness is exactly what it takes to
separate `demographicSpike` from a wrong constant factor.  The competitor
carried here is the halved constant -- the error that was actually live.

    Empirical status: NOT AN EMPIRICAL CLAIM.  This bundles an evaluation point,
    a value and a rejected competitor for `demographicSpike`; the empirical
    content is `demographicSpike`'s own, which is VALIDATED against a BBP
    inversion recovering `3.9920 ± 0.0045`.  Nothing here is measurable
    separately from that. -/
noncomputable def demographicSpike_referenceEvaluation :
    ReferenceEvaluation (ℝ × ℝ × ℝ) :=
  ReferenceEvaluation.ofScale
    (fun p ↦ demographicSpike p.1 p.2.1 p.2.2) (4, 1, 1) 2 (by norm_num)
    (by norm_num [demographicSpike, effectiveSubgroupSize])

theorem demographicSpike_referenceEvaluation_value :
    demographicSpike_referenceEvaluation.value = 3 := by
  show demographicSpike 4 1 1 = 3
  exact demographicSpike_at_reference_point

/-- **A discriminating reference evaluation exists for `demographicSpike`.**

This is the statement that relates `ReferenceEvaluation` to the quantity it
constrains.  Without it the obligation would live in a module no other module's
theorem ever mentions, and a false definition there would be consistent with the
whole corpus -- the same shelter that let two falsified identifications survive
review.  A machine that forbids vacuous reference points is not much use sitting
somewhere nothing can contradict. -/
theorem exists_discriminating_referenceEvaluation_for_demographicSpike :
    ∃ r : ReferenceEvaluation (ℝ × ℝ × ℝ),
      r.body = (fun p ↦ demographicSpike p.1 p.2.1 p.2.2) ∧ r.value = 3 :=
  ⟨demographicSpike_referenceEvaluation, rfl, demographicSpike_referenceEvaluation_value⟩

/-- **The old reference point pinned nothing, stated as a theorem rather than as
a warning in a docstring.**  At `n = m = 1` the spike vanishes, so the
halved-constant competitor agrees with the body exactly and the value `0` that
the corpus used to state there separates them not at all. -/
theorem demographicSpike_old_reference_point_discriminates_nothing :
    2 * demographicSpike 1 1 1 = demographicSpike 1 1 1 :=
  scale_competitor_eq_of_body_eq_zero
    (fun p : ℝ × ℝ × ℝ ↦ demographicSpike p.1 p.2.1 p.2.2) (1, 1, 1)
    (by norm_num [demographicSpike, effectiveSubgroupSize]) 2



/-- BBP-style proxy threshold for `n` individuals and `M` effectively
independent markers.

**Which count is the dimension, stated.** The threshold is `√(n/M)`, not
`√(M/n)`, and the difference is not a typo to be normalized away. The
Baik--Ben Arous--Péché transition puts a spike above the bulk edge exactly when
it exceeds `√γ` with `γ = dimension/observations`. This corpus's PCA is the
Patterson--Price--Reich one, run on the `n × n` cross-individual matrix built
from `M` markers: the INDIVIDUALS are the dimension and the MARKERS are the
observations, so `γ = n/M`. Reading it the other way -- `M` as dimension --
inverts the aspect ratio and, in the usual `M ≫ n` genotype panel, turns an
easy detection problem into an impossible one.

`M` is the effectively independent marker count, not a raw variant count.
Simulation measures the cost of confusing the two: supplying a raw count in
place of `M` overstates correctability by about twentyfold in `M`, predicting
eigenvector overlap `0.87` at `F_ST = 0.001` where the observed value is
`0.014`. That error is optimistic, whereas the spike-constant error corrected
alongside it was conservative, so the two partially masked each other. -/
noncomputable def bbpProxyThreshold (n M : ℝ) : ℝ :=
  Real.sqrt (n / M)

/-- **bbpProxyThreshold at its junk point, named.** With no markers there are no observations
and the BBP aspect ratio is undefined -- and the true threshold DIVERGES as `M → 0`, since
`n/M → ∞`. The ratio is junk-zero and the threshold is `0` instead: every spike is above it, so
the detection criterion admits everything at exactly the parameter where it should admit
nothing. Consumers must guard the argument that makes the divisor vanish. -/
theorem bbpProxyThreshold_zero_dimension_is_junk (n : ℝ) :
    bbpProxyThreshold n 0 = 0 := by
  unfold bbpProxyThreshold
  simp

/-- **The threshold depends only on the aspect ratio.** Growing the sample and the panel together
leaves it unchanged: what matters is `n/M`, not either count alone, which is the whole content of
a proportional-regime threshold. Squaring recovers that ratio exactly. -/
theorem bbpProxyThreshold_aspect_invariant (n M t : ℝ) (ht : t ≠ 0) :
    bbpProxyThreshold (t * n) (t * M) = bbpProxyThreshold n M := by
  unfold bbpProxyThreshold
  rw [mul_div_mul_left _ _ ht]

theorem bbpProxyThreshold_sq (n M : ℝ) (h : 0 ≤ n / M) :
    bbpProxyThreshold n M ^ 2 = n / M := by
  unfold bbpProxyThreshold
  exact Real.sq_sqrt h

/-- Signed distance from the spike to the spectral proxy threshold.  A positive
value is the detectable side of the phase diagram. -/
noncomputable def pcCorrectabilityMargin (n M F m : ℝ) : ℝ :=
  demographicSpike n F m - bbpProxyThreshold n M

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem pcCorrectabilityMargin_at_reference_point :
    pcCorrectabilityMargin 4 1 1 1 = 1 := by
  have hsqrt : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  unfold pcCorrectabilityMargin bbpProxyThreshold demographicSpike effectiveSubgroupSize
  norm_num [hsqrt]

/-- `√4 = 2`, used by both the margin reference point and its competitor. -/
private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The margin reference point, carrying the competitor it rejects.**

The competitor here is deliberately not a rescaling of the whole margin.  A
rescaled margin would be rejected by any nonzero value and would therefore say
nothing about which half of the difference is right.  What is carried instead is
the margin computed with the *halved spike constant* -- the error class that was
actually live -- which at this point gives `2 * 3 - 2 = 4` against the body's
`3 - 2 = 1`.  At the old point `n = M = F = m = 1` the same competitor gives
`0 - 1 = -1`, exactly the value the corpus stated, so it was rejected by
nothing. -/
noncomputable def pcCorrectabilityMargin_referenceEvaluation :
    ReferenceEvaluation (ℝ × ℝ × ℝ × ℝ) where
  point := (4, 1, 1, 1)
  body := fun p ↦ pcCorrectabilityMargin p.1 p.2.1 p.2.2.1 p.2.2.2
  value := 1
  competitor := fun p ↦
    2 * demographicSpike p.1 p.2.2.1 p.2.2.2 - bbpProxyThreshold p.1 p.2.1
  evaluates := pcCorrectabilityMargin_at_reference_point
  discriminates := by
    show 2 * demographicSpike 4 1 1 - bbpProxyThreshold 4 1 ≠ 1
    unfold bbpProxyThreshold demographicSpike effectiveSubgroupSize
    norm_num [sqrt_four]

/-- **The old margin reference point pinned nothing about the spike.**  At
`n = M = F = m = 1` the halved-constant competitor reproduces the stated value
`-1` exactly, because the spike term it differs in has collapsed to zero. -/
theorem pcCorrectabilityMargin_old_reference_point_discriminates_nothing :
    2 * demographicSpike 1 1 1 - bbpProxyThreshold 1 1 =
      pcCorrectabilityMargin 1 1 1 1 := by
  unfold pcCorrectabilityMargin bbpProxyThreshold demographicSpike effectiveSubgroupSize
  norm_num

end Descent
