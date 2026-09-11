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

namespace ResamplingExpansion

/-- Expansions add: the second-order coefficients, the bounds and the remainders add. -/
def add {D : ℕ} {firstJet secondJet : TwoLocusDiffusionJet D}
    (firstExpansion : ResamplingExpansion firstJet)
    (secondExpansion : ResamplingExpansion secondJet) :
    ResamplingExpansion (firstJet.add secondJet) where
  second deme state drawn :=
    firstExpansion.second deme state drawn + secondExpansion.second deme state drawn
  bound := firstExpansion.bound + secondExpansion.bound
  remainder := firstExpansion.remainder + secondExpansion.remainder
  value_le state := by
    have hfirst := firstExpansion.value_le state
    have hsecond := secondExpansion.value_le state
    have htriangle := abs_add_le (firstJet.value state) (secondJet.value state)
    simp only [TwoLocusDiffusionJet.add]
    linarith
  gradient_le deme state drawn := by
    have hfirst := firstExpansion.gradient_le deme state drawn
    have hsecond := secondExpansion.gradient_le deme state drawn
    have htriangle := abs_add_le (firstJet.gradientAt deme state drawn)
      (secondJet.gradientAt deme state drawn)
    simp only [TwoLocusDiffusionJet.add]
    linarith
  second_le deme state drawn := by
    have hfirst := firstExpansion.second_le deme state drawn
    have hsecond := secondExpansion.second_le deme state drawn
    have htriangle := abs_add_le (firstExpansion.second deme state drawn)
      (secondExpansion.second deme state drawn)
    show |firstExpansion.second deme state drawn +
      secondExpansion.second deme state drawn| ≤ _
    linarith
  expansion N hN state deme drawn := by
    have hfirst := firstExpansion.expansion N hN state deme drawn
    have hsecond := secondExpansion.expansion N hN state deme drawn
    have hresidual : expansionResidual (firstJet.add secondJet)
        (fun innerDeme innerState innerDrawn ↦
          firstExpansion.second innerDeme innerState innerDrawn +
            secondExpansion.second innerDeme innerState innerDrawn)
        N state deme drawn =
        expansionResidual firstJet firstExpansion.second N state deme drawn +
          expansionResidual secondJet secondExpansion.second N state deme drawn := by
      simp only [expansionResidual, centeredGradient, TwoLocusDiffusionJet.add,
        twoLocusHaplotypeMean]
      ring
    rw [hresidual]
    have htriangle := abs_add_le
      (expansionResidual firstJet firstExpansion.second N state deme drawn)
      (expansionResidual secondJet secondExpansion.second N state deme drawn)
    have hcollect : firstExpansion.remainder / (N : ℝ) ^ 3 +
        secondExpansion.remainder / (N : ℝ) ^ 3 =
        (firstExpansion.remainder + secondExpansion.remainder) / (N : ℝ) ^ 3 := by
      ring
    linarith
  second_mean deme state := by
    have hfirst := firstExpansion.second_mean deme state
    have hsecond := secondExpansion.second_mean deme state
    simp only [TwoLocusDiffusionJet.add, twoLocusHaplotypeMean] at hfirst hsecond ⊢
    linear_combination hfirst + hsecond

/-- Expansions rescale: the second-order coefficient, the bound and the remainder all pick up
the factor. -/
def smul {D : ℕ} {jet : TwoLocusDiffusionJet D} (scalar : ℝ)
    (resampling : ResamplingExpansion jet) :
    ResamplingExpansion (TwoLocusDiffusionJet.smul scalar jet) where
  second deme state drawn := scalar * resampling.second deme state drawn
  bound := |scalar| * resampling.bound
  remainder := |scalar| * resampling.remainder
  value_le state := by
    simp only [TwoLocusDiffusionJet.smul]
    exact abs_mul_le_of_abs_le_of_abs_le (le_refl |scalar|) (resampling.value_le state)
  gradient_le deme state drawn := by
    simp only [TwoLocusDiffusionJet.smul]
    exact abs_mul_le_of_abs_le_of_abs_le (le_refl |scalar|)
      (resampling.gradient_le deme state drawn)
  second_le deme state drawn :=
    abs_mul_le_of_abs_le_of_abs_le (le_refl |scalar|)
      (resampling.second_le deme state drawn)
  expansion N hN state deme drawn := by
    have hresidual : expansionResidual (TwoLocusDiffusionJet.smul scalar jet)
        (fun innerDeme innerState innerDrawn ↦
          scalar * resampling.second innerDeme innerState innerDrawn)
        N state deme drawn =
        scalar * expansionResidual jet resampling.second N state deme drawn := by
      simp only [expansionResidual, centeredGradient, TwoLocusDiffusionJet.smul,
        twoLocusHaplotypeMean]
      ring
    rw [hresidual, abs_mul]
    have hbase := mul_le_mul_of_nonneg_left (resampling.expansion N hN state deme drawn)
      (abs_nonneg scalar)
    have hcollect : |scalar| * (resampling.remainder / (N : ℝ) ^ 3) =
        |scalar| * resampling.remainder / (N : ℝ) ^ 3 := by
      ring
    linarith
  second_mean deme state := by
    have hbase := resampling.second_mean deme state
    simp only [TwoLocusDiffusionJet.smul, twoLocusHaplotypeMean] at hbase ⊢
    linear_combination scalar * hbase

end ResamplingExpansion

/-- Second-order coefficient of a product jet: the two Leibniz terms plus the product of the
two centred gradients.  That last term is the multinomial covariance contribution which makes
the Wright--Fisher product rule exact. -/
def mulSecondOrder {D : ℕ} (firstJet secondJet : TwoLocusDiffusionJet D)
    (firstSecond secondSecond :
      Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → TwoLocusHaplotype → ℝ)
    (deme : Fin D) (state : Fin D → TwoLocusHaplotypeFrequencies)
    (drawn : TwoLocusHaplotype) : ℝ :=
  firstJet.value state * secondSecond deme state drawn +
    secondJet.value state * firstSecond deme state drawn +
    centeredGradient firstJet deme state drawn * centeredGradient secondJet deme state drawn

/-- Exact algebraic decomposition of a product jet's residual: everything of total order at
least three in `1 / N`, plus the two factors' own residuals carried by bounded companions. -/
theorem expansionResidual_mul {D : ℕ} (firstJet secondJet : TwoLocusDiffusionJet D)
    (firstSecond secondSecond :
      Fin D → (Fin D → TwoLocusHaplotypeFrequencies) → TwoLocusHaplotype → ℝ)
    (N : ℕ) (state : Fin D → TwoLocusHaplotypeFrequencies) (deme : Fin D)
    (drawn : TwoLocusHaplotype) :
    expansionResidual (firstJet.mul secondJet)
        (mulSecondOrder firstJet secondJet firstSecond secondSecond) N state deme drawn =
      (1 / (N : ℝ)) ^ 3 * (centeredGradient firstJet deme state drawn *
          secondSecond deme state drawn +
        firstSecond deme state drawn * centeredGradient secondJet deme state drawn) +
      (1 / (N : ℝ)) ^ 4 * (firstSecond deme state drawn * secondSecond deme state drawn) +
      expansionResidual firstJet firstSecond N state deme drawn *
        secondJet.value (resampleStepAt state deme N drawn) +
      expansionResidual secondJet secondSecond N state deme drawn *
        (firstJet.value state + 1 / (N : ℝ) * centeredGradient firstJet deme state drawn +
          (1 / (N : ℝ)) ^ 2 * firstSecond deme state drawn) := by
  simp only [expansionResidual, mulSecondOrder, centeredGradient,
    TwoLocusDiffusionJet.mul, twoLocusHaplotypeMean]
  ring

namespace ResamplingExpansion

/-- Expansions multiply.  The second-order coefficient is `mulSecondOrder`, whose mean is the
corpus product-rule drift, and the remainder collects every term of total order at least three
in `1 / N`. -/
def mul {D : ℕ} {firstJet secondJet : TwoLocusDiffusionJet D}
    (firstExpansion : ResamplingExpansion firstJet)
    (secondExpansion : ResamplingExpansion secondJet) :
    ResamplingExpansion (firstJet.mul secondJet) where
  second := mulSecondOrder firstJet secondJet firstExpansion.second secondExpansion.second
  bound := 6 * firstExpansion.bound * secondExpansion.bound
  remainder := 5 * firstExpansion.bound * secondExpansion.bound +
    firstExpansion.remainder * secondExpansion.bound +
    4 * secondExpansion.remainder * firstExpansion.bound
  value_le state := by
    have hproduct := abs_mul_le_of_abs_le_of_abs_le (firstExpansion.value_le state)
      (secondExpansion.value_le state)
    have hnonneg := mul_nonneg firstExpansion.bound_nonneg secondExpansion.bound_nonneg
    simp only [TwoLocusDiffusionJet.mul]
    linarith
  gradient_le deme state drawn := by
    have hleft := abs_mul_le_of_abs_le_of_abs_le (firstExpansion.value_le state)
      (secondExpansion.gradient_le deme state drawn)
    have hright := abs_mul_le_of_abs_le_of_abs_le (secondExpansion.value_le state)
      (firstExpansion.gradient_le deme state drawn)
    have htriangle := abs_add_le (firstJet.value state * secondJet.gradientAt deme state drawn)
      (secondJet.value state * firstJet.gradientAt deme state drawn)
    have hnonneg := mul_nonneg firstExpansion.bound_nonneg secondExpansion.bound_nonneg
    simp only [TwoLocusDiffusionJet.mul]
    linarith
  second_le deme state drawn := by
    have hleft := abs_mul_le_of_abs_le_of_abs_le (firstExpansion.value_le state)
      (secondExpansion.second_le deme state drawn)
    have hright := abs_mul_le_of_abs_le_of_abs_le (secondExpansion.value_le state)
      (firstExpansion.second_le deme state drawn)
    have hcross := abs_mul_le_of_abs_le_of_abs_le
      (abs_centeredGradient_le firstJet deme state drawn firstExpansion.bound
        (firstExpansion.gradient_le deme state))
      (abs_centeredGradient_le secondJet deme state drawn secondExpansion.bound
        (secondExpansion.gradient_le deme state))
    have houter := abs_add_le (firstJet.value state *
        secondExpansion.second deme state drawn +
      secondJet.value state * firstExpansion.second deme state drawn)
      (centeredGradient firstJet deme state drawn *
        centeredGradient secondJet deme state drawn)
    have hinner := abs_add_le (firstJet.value state * secondExpansion.second deme state drawn)
      (secondJet.value state * firstExpansion.second deme state drawn)
    simp only [mulSecondOrder]
    linarith
  expansion N hN state deme drawn := by
    have hpositive : 0 < N := hN
    have hcast : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpositive
    have hone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hstep : (1 : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hcast]
      exact hone
    have hstepnn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have hMfirst := firstExpansion.bound_nonneg
    have hMsecond := secondExpansion.bound_nonneg
    have hcollect : ∀ level : ℝ, level / (N : ℝ) ^ 3 = (1 / (N : ℝ)) ^ 3 * level := by
      intro level
      ring
    have hRfirst := firstExpansion.expansion N hN state deme drawn
    have hRsecond := secondExpansion.expansion N hN state deme drawn
    rw [expansionResidual_mul]
    rw [hcollect] at hRfirst hRsecond ⊢
    have hGfirst := abs_centeredGradient_le firstJet deme state drawn firstExpansion.bound
      (firstExpansion.gradient_le deme state)
    have hGsecond := abs_centeredGradient_le secondJet deme state drawn secondExpansion.bound
      (secondExpansion.gradient_le deme state)
    have hSfirst := firstExpansion.second_le deme state drawn
    have hSsecond := secondExpansion.second_le deme state drawn
    have habsthird : |(1 / (N : ℝ)) ^ 3| = (1 / (N : ℝ)) ^ 3 :=
      abs_of_nonneg (by positivity)
    have habsfourth : |(1 / (N : ℝ)) ^ 4| = (1 / (N : ℝ)) ^ 4 :=
      abs_of_nonneg (by positivity)
    have hcrossinner : |centeredGradient firstJet deme state drawn *
        secondExpansion.second deme state drawn +
        firstExpansion.second deme state drawn *
          centeredGradient secondJet deme state drawn| ≤
        4 * firstExpansion.bound * secondExpansion.bound := by
      have hleft := abs_mul_le_of_abs_le_of_abs_le hGfirst hSsecond
      have hright := abs_mul_le_of_abs_le_of_abs_le hSfirst hGsecond
      have htriangle := abs_add_le (centeredGradient firstJet deme state drawn *
          secondExpansion.second deme state drawn)
        (firstExpansion.second deme state drawn *
          centeredGradient secondJet deme state drawn)
      linarith
    have hthird := abs_mul_le_of_abs_le_of_abs_le (le_of_eq habsthird) hcrossinner
    have hfourth := abs_mul_le_of_abs_le_of_abs_le (le_of_eq habsfourth)
      (abs_mul_le_of_abs_le_of_abs_le hSfirst hSsecond)
    have hcarry := abs_mul_le_of_abs_le_of_abs_le hRfirst
      (secondExpansion.value_le (resampleStepAt state deme N drawn))
    have hcompanion : |firstJet.value state +
        1 / (N : ℝ) * centeredGradient firstJet deme state drawn +
        (1 / (N : ℝ)) ^ 2 * firstExpansion.second deme state drawn| ≤
        4 * firstExpansion.bound := by
      have hsquare : |(1 / (N : ℝ)) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)]
        nlinarith
      have hlinear : |1 / (N : ℝ) * centeredGradient firstJet deme state drawn| ≤
          1 * (2 * firstExpansion.bound) :=
        abs_mul_le_of_abs_le_of_abs_le (by rwa [abs_of_nonneg hstepnn]) hGfirst
      have hquadratic : |(1 / (N : ℝ)) ^ 2 *
          firstExpansion.second deme state drawn| ≤ 1 * firstExpansion.bound :=
        abs_mul_le_of_abs_le_of_abs_le hsquare hSfirst
      have houter := abs_add_le (firstJet.value state +
        1 / (N : ℝ) * centeredGradient firstJet deme state drawn)
        ((1 / (N : ℝ)) ^ 2 * firstExpansion.second deme state drawn)
      have hinner := abs_add_le (firstJet.value state)
        (1 / (N : ℝ) * centeredGradient firstJet deme state drawn)
      have hvalue := firstExpansion.value_le state
      linarith
    have hcompanionbound := abs_mul_le_of_abs_le_of_abs_le hRsecond hcompanion
    have hslack : (1 / (N : ℝ)) ^ 4 * (firstExpansion.bound * secondExpansion.bound) ≤
        (1 / (N : ℝ)) ^ 3 * (firstExpansion.bound * secondExpansion.bound) := by
      have hcube : (0 : ℝ) < (1 / (N : ℝ)) ^ 3 := by positivity
      nlinarith [mul_nonneg (le_of_lt hcube) (mul_nonneg hMfirst hMsecond), hstep]
    refine le_trans (abs_add_four_le _ _ _ _) ?_
    linarith
  second_mean deme state := by
    have hfirst := firstExpansion.second_mean deme state
    have hsecond := secondExpansion.second_mean deme state
    have hcovariance := twoLocusHaplotypeMean_centered_mul (state deme)
      (firstJet.gradientAt deme state) (secondJet.gradientAt deme state)
    simp only [TwoLocusDiffusionJet.mul, mulSecondOrder, centeredGradient,
      twoLocusHaplotypeCovariance, twoLocusHaplotypeMean] at hfirst hsecond hcovariance ⊢
    linear_combination firstJet.value state * hsecond +
      secondJet.value state * hfirst + hcovariance

end ResamplingExpansion

end

end Descent.Portability.ResamplingJetExpansion
