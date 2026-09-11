/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimplexResamplingKernel

assert_below Descent.Decision Descent.Program

/-!
# Second-order expansion of the corpus diffusion jets along one resampling step

NOTE 1 section 2.3 needs, for Theorem 1's hypothesis (3), a genuine probability kernel whose
one-step effect on the observable family is the generator plus a uniformly small remainder.
This file supplies the drift (coalescence) half of that estimate for the corpus jets, using
the single-draw step of `SimplexResamplingKernel`.

`ResamplingExpansion jet` is the witness structure.  It carries DATA, not an existential: an
explicit second-order coefficient `second`, an explicit uniform bound `bound` on value,
gradient and second-order coefficient, and an explicit remainder constant `remainder`.  Its
Prop fields say that the one-step residual `expansionResidual` is at most `remainder / N ^ 3`
uniformly in the state, the deme, the drawn haplotype and `N`, and that the second-order
coefficient averages to the corpus `driftAt`.  The first-order coefficient is not free: it is
forced to be `centeredGradient`, the gradient at the drawn haplotype minus its multinomial
mean, because the single-draw direction is `e a - x`.

The instances are built compositionally.  `resamplingExpansionConst`,
`resamplingExpansionLeftFrequencyJet`, `resamplingExpansionRightFrequencyJet` and
`resamplingExpansionLinkageJet` are exact: their remainder is literally zero, since a marginal
frequency is linear and a determinant is quadratic in the haplotype coordinates.
`ResamplingExpansion.add`, `.smul` and `.mul` close the class under the corpus jet algebra;
the product rule's second-order coefficient is `mulSecondOrder`, whose mean is the corpus
`TwoLocusDiffusionJet.mul` drift precisely because of the multinomial covariance identity
`twoLocusHaplotypeMean_centered_mul`.  Hence every `twoLocusCoordinateJet` (the `H`, `DD`,
`Dz` and `pi2` coordinates of `LowOrderLDCoordinate`) and every `twoLocusRightHJet` has an
expansion, named `resamplingExpansionCoordinateJet` and `resamplingExpansionRightHJet`.

`resampleExpectation_jet_expansion` is the consequence NOTE 1 uses: the expectation after one
step equals the value plus `driftAt / N ^ 2` up to `remainder / N ^ 3`.  The first-order term
drops out because the direction averages to zero, and the second-order term becomes `driftAt`
by `second_mean`.

Scope.  The constants here are explicit but not sharp; `bound` and `remainder` are whatever
the closure rules produce, and no attempt is made to optimize them.  Nothing about a step size
`h`, a coalescence rate, a mixture over stages or a semigroup appears here: that is
`RandomStageKernel`.  Multinomial resampling, NOTE 1 (10), is not formalized; the single-draw
alternative NOTE 1 licenses is used throughout.

## Empirical status

None.  The bodies here are algebra: a jet expansion is a polynomial identity about a named
affine map of the simplex together with bounds read off the simplex constraints, so no
measurement can bear on them.  Whether a population resamples this way is asked wherever a
composed prediction meets data, not here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ResamplingJetExpansion

open Coalescent SimplexResamplingKernel

noncomputable section

/-- The centred gradient of a jet in one deme: the gradient at the drawn haplotype minus its
multinomial mean.  Because the single-draw direction is `e a - x`, this is exactly the
gradient contracted with the step direction. -/
def centeredGradient {D : ℕ} (jet : TwoLocusDiffusionJet D) (deme : Fin D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (drawn : TwoLocusHaplotype) : ℝ :=
  jet.gradientAt deme state drawn -
    twoLocusHaplotypeMean (state deme) (jet.gradientAt deme state)

/-- The residual left by the two-term expansion of a jet along one single-draw step: the
actual change minus the first-order term `(1 / N)` times the centred gradient minus the
second-order term `(1 / N) ^ 2` times the proposed second-order coefficient. -/
def expansionResidual {D : ℕ} (jet : TwoLocusDiffusionJet D)
    (secondOrder : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → TwoLocusHaplotype → ℝ)
    (N : ℕ) (state : Fin D → TwoLocusHaplotypeFrequencies) (deme : Fin D)
    (drawn : TwoLocusHaplotype) : ℝ :=
  jet.value (resampleStepAt state deme N drawn) - jet.value state -
    1 / (N : ℝ) * centeredGradient jet deme state drawn -
    (1 / (N : ℝ)) ^ 2 * secondOrder deme state drawn

/-- A constructive second-order expansion of one corpus diffusion jet along the single-draw
resampling step.  The second-order coefficient and both constants are data the caller holds,
not existentially quantified: `second` is the explicit coefficient, `bound` a uniform bound on
value, gradient and coefficient, and `remainder` the uniform third-order constant.

`Assumes:` the four Prop fields.  Concrete inhabitants are constructed below for the constant
jet, the marginal-frequency jets, the linkage jet and, through `add`, `smul` and `mul`, for
every `twoLocusCoordinateJet`. -/
structure ResamplingExpansion {D : ℕ} (jet : TwoLocusDiffusionJet D) where
  /-- The explicit second-order coefficient of the expansion. -/
  second : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → TwoLocusHaplotype → ℝ
  /-- A uniform bound on value, gradient and second-order coefficient. -/
  bound : ℝ
  /-- The uniform third-order remainder constant. -/
  remainder : ℝ
  /-- The jet's value is uniformly bounded. -/
  value_le : ∀ state, |jet.value state| ≤ bound
  /-- The jet's gradient is uniformly bounded. -/
  gradient_le : ∀ deme state drawn, |jet.gradientAt deme state drawn| ≤ bound
  /-- The second-order coefficient is uniformly bounded. -/
  second_le : ∀ deme state drawn, |second deme state drawn| ≤ bound
  /-- The two-term expansion has a uniform third-order remainder. -/
  expansion : ∀ N : ℕ, 1 ≤ N → ∀ state deme drawn,
    |expansionResidual jet second N state deme drawn| ≤ remainder / (N : ℝ) ^ 3
  /-- The second-order coefficient averages to the corpus drift. -/
  second_mean : ∀ deme state,
    twoLocusHaplotypeMean (state deme) (second deme state) = jet.driftAt deme state

namespace ResamplingExpansion

/-- The uniform bound of an expansion is nonnegative, because it dominates an absolute
value at the constant maximal-coupling state. -/
theorem bound_nonneg {D : ℕ} {jet : TwoLocusDiffusionJet D}
    (resampling : ResamplingExpansion jet) : 0 ≤ resampling.bound :=
  le_trans (abs_nonneg _)
    (resampling.value_le (fun _ ↦ TwoLocusHaplotypeFrequencies.maximalCoupling))

/-- The remainder constant of an expansion is nonnegative, read off the expansion bound at
one chromosome. -/
theorem remainder_nonneg {D : ℕ} {jet : TwoLocusDiffusionJet D}
    (resampling : ResamplingExpansion jet)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (deme : Fin D)
    (drawn : TwoLocusHaplotype) : 0 ≤ resampling.remainder := by
  have hstep := le_trans (abs_nonneg _) (resampling.expansion 1 le_rfl state deme drawn)
  simpa using hstep

end ResamplingExpansion

/-- Bounding two factors bounds their product. -/
theorem abs_mul_le_of_abs_le_of_abs_le {first second firstBound secondBound : ℝ}
    (hfirst : |first| ≤ firstBound) (hsecond : |second| ≤ secondBound) :
    |first * second| ≤ firstBound * secondBound := by
  rw [abs_mul]
  exact mul_le_mul hfirst hsecond (abs_nonneg second)
    (le_trans (abs_nonneg first) hfirst)

/-- Triangle inequality for a four-term sum. -/
theorem abs_add_four_le (first second third fourth : ℝ) :
    |first + second + third + fourth| ≤
      |first| + |second| + |third| + |fourth| := by
  have houter := abs_add_le (first + second + third) fourth
  have hmiddle := abs_add_le (first + second) third
  have hinner := abs_add_le first second
  linarith

/-- A pointwise gradient bound gives a centred-gradient bound with a factor two, because the
multinomial mean of a bounded score is bounded by the same constant. -/
theorem abs_centeredGradient_le {D : ℕ} (jet : TwoLocusDiffusionJet D) (deme : Fin D)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (drawn : TwoLocusHaplotype) (level : ℝ)
    (gradient_le : ∀ observed, |jet.gradientAt deme state observed| ≤ level) :
    |centeredGradient jet deme state drawn| ≤ 2 * level := by
  obtain ⟨hmeanlow, hmeanhigh⟩ := abs_le.mp (twoLocusHaplotypeMean_abs_le (state deme)
    (jet.gradientAt deme state) level gradient_le)
  obtain ⟨hdrawnlow, hdrawnhigh⟩ := abs_le.mp (gradient_le drawn)
  simp only [centeredGradient]
  rw [abs_le]
  constructor <;> linarith

/-- A vanishing residual gives the expansion bound with remainder zero. -/
theorem abs_expansionResidual_le_of_eq_zero {D : ℕ} {jet : TwoLocusDiffusionJet D}
    {secondOrder : Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → TwoLocusHaplotype → ℝ}
    {N : ℕ} {state : Fin D → TwoLocusHaplotypeFrequencies} {deme : Fin D}
    {drawn : TwoLocusHaplotype}
    (hzero : expansionResidual jet secondOrder N state deme drawn = 0) :
    |expansionResidual jet secondOrder N state deme drawn| ≤ 0 / (N : ℝ) ^ 3 := by
  rw [hzero, abs_zero, zero_div]

/-- A constant observable expands exactly: no first-order term, no second-order term and no
remainder at all. -/
def resamplingExpansionConst {D : ℕ} (level : ℝ) :
    ResamplingExpansion (TwoLocusDiffusionJet.const level : TwoLocusDiffusionJet D) where
  second _ _ _ := 0
  bound := |level|
  remainder := 0
  value_le _ := by simp [TwoLocusDiffusionJet.const]
  gradient_le _ _ _ := by simp [TwoLocusDiffusionJet.const]
  second_le _ _ _ := by simp
  expansion _ _ _ _ _ := abs_expansionResidual_le_of_eq_zero (by
    simp only [expansionResidual, centeredGradient, TwoLocusDiffusionJet.const,
      twoLocusHaplotypeMean]
    ring)
  second_mean _ _ := by
    simp only [TwoLocusDiffusionJet.const, twoLocusHaplotypeMean]
    ring

end

end Descent.Portability.ResamplingJetExpansion
