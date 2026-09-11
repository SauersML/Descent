/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TwoLocusHistory

assert_below Descent.Decision Descent.Program

/-!
# A single-draw resampling kernel on the two-locus haplotype simplex

NOTE 1 section 2.3 constructs the positive microscopic kernels whose existence Theorem 1
needs.  Its FORMALIZATION ALTERNATIVE paragraph replaces multinomial resampling by a
single-draw (Moran-type) step: draw one haplotype `a` with probability `x a` and move the
frequency vector to `x + (e a - x) / N`.  This file builds that step as a genuine map of the
haplotype simplex into itself and records the exact algebra of one step.

`resampleStep` is the map.  Its four coordinates are nonnegative and sum to one for every
`N`, so no positivity side condition travels downstream; with `N = 0` the division convention
makes the step the identity, which is why no `0 < N` hypothesis appears.  `stepDirection` is
`e a - x`, and `stepDirection_eq_centered_indicator` identifies it with the centred indicator
of the observed haplotype, which is what makes the first-order term average to zero
(`twoLocusHaplotypeMean_stepDirection`).  `resampleStepAt` applies the step inside one named
deme of a multi-deme state, and `resampleExpectation` averages an observable over the drawn
haplotype with that deme's own frequencies as weights, which is exactly the corpus
`twoLocusHaplotypeMean`.

The exact facts proved here are the ones a second-order expansion needs.  For each linear
coordinate one step moves the value by exactly `1 / N` times the centred gradient and there
is no remainder: `resampleStep_leftFrequency` and `resampleStep_rightFrequency`.  For
`linkage`, which is quadratic, `resampleStep_linkage` moves the value by exactly `1 / N`
times the centred gradient plus `(1 / N) ^ 2` times `linkageStepForm`, the quadratic form of
the direction, again with no remainder, because a determinant has no third derivative.  This
is the whole of the expansion NOTE 1 (10) asks for in the single-draw case.
`twoLocusHaplotypeMean_centered_mul` is the multinomial covariance identity that turns an
average of centred products into the corpus `twoLocusHaplotypeCovariance`, and
`twoLocusHaplotypeMean_linkageStepForm` identifies the average of the quadratic form with the
corpus drift `twoLocusLinkageDrift`, hence with `-D` through
`twoLocusLinkageDrift_eq_neg_linkage`.

Not proved here: nothing about a step size `h`, about rates, or about semigroups.  The choice
`N = N h` and the resulting `h * epsilon h` bound belong to `RandomStageKernel`; the jet-level
expansion with its uniform third-order remainder belongs to `ResamplingJetExpansion`.
Multinomial resampling with `N` chromosomes, NOTE 1 (10) with its Stirling-number remainder,
is not formalized at all: the single-draw step is used in its place, which NOTE 1 explicitly
licenses as equally physical.

## Empirical status

None.  The bodies here are algebra: `resampleStep` is a named affine map of the simplex and
every theorem about it is a polynomial identity or a bound read off the simplex constraints,
so no measurement can bear on them.  Whether a population resamples this way is a question
asked wherever a composed prediction meets data, not here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimplexResamplingKernel

open Coalescent

noncomputable section

/-- Coordinate readout of one haplotype-frequency simplex point. -/
def haplotypeCoordinate (frequency : TwoLocusHaplotypeFrequencies) :
    TwoLocusHaplotype → ℝ
  | .AB => frequency.AB
  | .Ab => frequency.Ab
  | .aB => frequency.aB
  | .ab => frequency.ab

/-- Every haplotype coordinate of a simplex point is nonnegative. -/
theorem haplotypeCoordinate_nonneg (frequency : TwoLocusHaplotypeFrequencies)
    (observed : TwoLocusHaplotype) : 0 ≤ haplotypeCoordinate frequency observed := by
  cases observed <;> simp only [haplotypeCoordinate]
  exacts [frequency.AB_nonneg, frequency.Ab_nonneg, frequency.aB_nonneg,
    frequency.ab_nonneg]

/-- Every haplotype coordinate of a simplex point is at most one. -/
theorem haplotypeCoordinate_le_one (frequency : TwoLocusHaplotypeFrequencies)
    (observed : TwoLocusHaplotype) : haplotypeCoordinate frequency observed ≤ 1 := by
  have htotal := frequency.total_eq_one
  cases observed <;> simp only [haplotypeCoordinate] <;>
    linarith [frequency.AB_nonneg, frequency.Ab_nonneg, frequency.aB_nonneg,
      frequency.ab_nonneg]

/-- The one-haplotype indicator is symmetric in its two arguments. -/
theorem twoLocusHaplotypeIndicator_comm (first second : TwoLocusHaplotype) :
    twoLocusHaplotypeIndicator first second = twoLocusHaplotypeIndicator second first := by
  cases first <;> cases second <;> simp [twoLocusHaplotypeIndicator]

/-- The multinomial mean of a one-haplotype indicator is that haplotype's frequency. -/
theorem twoLocusHaplotypeMean_indicator (frequency : TwoLocusHaplotypeFrequencies)
    (target : TwoLocusHaplotype) :
    twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator target) =
      haplotypeCoordinate frequency target := by
  cases target <;>
    simp [twoLocusHaplotypeMean, twoLocusHaplotypeIndicator, haplotypeCoordinate]

/-- The multinomial mean is additive on differences of scores. -/
theorem twoLocusHaplotypeMean_sub (frequency : TwoLocusHaplotypeFrequencies)
    (firstScore secondScore : TwoLocusHaplotype → ℝ) :
    twoLocusHaplotypeMean frequency (fun observed ↦ firstScore observed -
        secondScore observed) =
      twoLocusHaplotypeMean frequency firstScore -
        twoLocusHaplotypeMean frequency secondScore := by
  simp only [twoLocusHaplotypeMean]
  ring

/-- Subtracting a constant from a score subtracts it from the multinomial mean, because the
four weights sum to one. -/
theorem twoLocusHaplotypeMean_sub_const (frequency : TwoLocusHaplotypeFrequencies)
    (score : TwoLocusHaplotype → ℝ) (level : ℝ) :
    twoLocusHaplotypeMean frequency (fun observed ↦ score observed - level) =
      twoLocusHaplotypeMean frequency score - level := by
  simp only [twoLocusHaplotypeMean]
  linear_combination (-level) * frequency.total_eq_one

/-- A pointwise bound on a score bounds its multinomial mean, because the weights are
nonnegative and sum to one. -/
theorem twoLocusHaplotypeMean_abs_le (frequency : TwoLocusHaplotypeFrequencies)
    (score : TwoLocusHaplotype → ℝ) (level : ℝ)
    (score_le : ∀ observed, |score observed| ≤ level) :
    |twoLocusHaplotypeMean frequency score| ≤ level := by
  have hAB := abs_le.mp (score_le .AB)
  have hAb := abs_le.mp (score_le .Ab)
  have haB := abs_le.mp (score_le .aB)
  have hab := abs_le.mp (score_le .ab)
  have htotal := frequency.total_eq_one
  have hupper : frequency.AB * level + frequency.Ab * level + frequency.aB * level +
      frequency.ab * level = level := by
    linear_combination level * htotal
  have hlower : frequency.AB * (-level) + frequency.Ab * (-level) +
      frequency.aB * (-level) + frequency.ab * (-level) = -level := by
    linear_combination (-level) * htotal
  have pAB := mul_le_mul_of_nonneg_left hAB.2 frequency.AB_nonneg
  have pAb := mul_le_mul_of_nonneg_left hAb.2 frequency.Ab_nonneg
  have paB := mul_le_mul_of_nonneg_left haB.2 frequency.aB_nonneg
  have pab := mul_le_mul_of_nonneg_left hab.2 frequency.ab_nonneg
  have qAB := mul_le_mul_of_nonneg_left hAB.1 frequency.AB_nonneg
  have qAb := mul_le_mul_of_nonneg_left hAb.1 frequency.Ab_nonneg
  have qaB := mul_le_mul_of_nonneg_left haB.1 frequency.aB_nonneg
  have qab := mul_le_mul_of_nonneg_left hab.1 frequency.ab_nonneg
  simp only [twoLocusHaplotypeMean]
  rw [abs_le]
  constructor <;> linarith

/-- **Multinomial covariance identity.**  Averaging the product of two centred scores over
the drawn haplotype returns exactly the corpus covariance. -/
theorem twoLocusHaplotypeMean_centered_mul (frequency : TwoLocusHaplotypeFrequencies)
    (firstScore secondScore : TwoLocusHaplotype → ℝ) :
    twoLocusHaplotypeMean frequency (fun observed ↦
        (firstScore observed - twoLocusHaplotypeMean frequency firstScore) *
          (secondScore observed - twoLocusHaplotypeMean frequency secondScore)) =
      twoLocusHaplotypeCovariance frequency firstScore secondScore := by
  simp only [twoLocusHaplotypeCovariance, twoLocusHaplotypeMean]
  linear_combination
    ((frequency.AB * firstScore .AB + frequency.Ab * firstScore .Ab +
        frequency.aB * firstScore .aB + frequency.ab * firstScore .ab) *
      (frequency.AB * secondScore .AB + frequency.Ab * secondScore .Ab +
        frequency.aB * secondScore .aB + frequency.ab * secondScore .ab)) *
      frequency.total_eq_one

/-- The direction of one single-draw resampling move: the drawn haplotype's unit vector
minus the current frequency vector. -/
def stepDirection (frequency : TwoLocusHaplotypeFrequencies)
    (drawn : TwoLocusHaplotype) : TwoLocusHaplotype → ℝ :=
  fun observed ↦ twoLocusHaplotypeIndicator drawn observed -
    haplotypeCoordinate frequency observed

/-- The resampling direction in one coordinate, read as a function of the drawn haplotype,
is the centred indicator of that coordinate. -/
theorem stepDirection_eq_centered_indicator (frequency : TwoLocusHaplotypeFrequencies)
    (drawn observed : TwoLocusHaplotype) :
    stepDirection frequency drawn observed =
      twoLocusHaplotypeIndicator observed drawn -
        twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator observed) := by
  simp only [stepDirection]
  rw [twoLocusHaplotypeIndicator_comm drawn observed, twoLocusHaplotypeMean_indicator]

/-- Every coordinate of the resampling direction lies in `[-1, 1]`. -/
theorem abs_stepDirection_le_one (frequency : TwoLocusHaplotypeFrequencies)
    (drawn observed : TwoLocusHaplotype) :
    |stepDirection frequency drawn observed| ≤ 1 := by
  have hzero := haplotypeCoordinate_nonneg frequency observed
  have hone := haplotypeCoordinate_le_one frequency observed
  simp only [stepDirection, twoLocusHaplotypeIndicator]
  rw [abs_le]
  constructor <;> (split <;> linarith)

/-- **The first-order term averages to zero.**  Averaging the resampling direction over the
drawn haplotype, with the frequencies themselves as weights, gives zero in every
coordinate. -/
theorem twoLocusHaplotypeMean_stepDirection (frequency : TwoLocusHaplotypeFrequencies)
    (observed : TwoLocusHaplotype) :
    twoLocusHaplotypeMean frequency
        (fun drawn ↦ stepDirection frequency drawn observed) = 0 := by
  have hfun : (fun drawn ↦ stepDirection frequency drawn observed) =
      fun drawn ↦ twoLocusHaplotypeIndicator observed drawn -
        twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator observed) := by
    funext drawn
    exact stepDirection_eq_centered_indicator frequency drawn observed
  rw [hfun, twoLocusHaplotypeMean_sub_const]
  ring

/-- One single-draw step keeps every coordinate nonnegative whenever its step fraction lies
in `[0, 1]`: the coordinate is then the convex combination
`(1 - fraction) * x b + fraction * e b`.  A population of `N` chromosomes steps by the
fraction `1 / N`, which lies in `[0, 1]` for every `N`; at `N = 0` it is zero and the step is
the identity. -/
theorem resampleStep_coordinate_nonneg (frequency : TwoLocusHaplotypeFrequencies) {fraction : ℝ}
    (hlow : 0 ≤ fraction) (hhigh : fraction ≤ 1) (drawn observed : TwoLocusHaplotype) :
    0 ≤ haplotypeCoordinate frequency observed +
      fraction * stepDirection frequency drawn observed := by
  have hcoord := haplotypeCoordinate_nonneg frequency observed
  have hind : 0 ≤ twoLocusHaplotypeIndicator drawn observed := by
    simp only [twoLocusHaplotypeIndicator]
    split <;> norm_num
  have hconvex : haplotypeCoordinate frequency observed +
      fraction * stepDirection frequency drawn observed =
      haplotypeCoordinate frequency observed * (1 - fraction) +
        twoLocusHaplotypeIndicator drawn observed * fraction := by
    simp only [stepDirection]
    ring
  rw [hconvex]
  exact add_nonneg (mul_nonneg hcoord (by linarith)) (mul_nonneg hind hlow)

/-- One single-draw (Moran-type) resampling step in a population of `N` chromosomes: a
haplotype is drawn and the frequency vector moves a fraction `1 / N` of the way toward that
haplotype's unit vector.  With `N = 0` the step is the identity. -/
def resampleStep (frequency : TwoLocusHaplotypeFrequencies) (N : ℕ)
    (drawn : TwoLocusHaplotype) : TwoLocusHaplotypeFrequencies where
  AB := frequency.AB + stepDirection frequency drawn .AB / N
  Ab := frequency.Ab + stepDirection frequency drawn .Ab / N
  aB := frequency.aB + stepDirection frequency drawn .aB / N
  ab := frequency.ab + stepDirection frequency drawn .ab / N
  AB_nonneg := by
    rw [div_eq_inv_mul]
    exact resampleStep_coordinate_nonneg frequency (by positivity) N.cast_inv_le_one drawn .AB
  Ab_nonneg := by
    rw [div_eq_inv_mul]
    exact resampleStep_coordinate_nonneg frequency (by positivity) N.cast_inv_le_one drawn .Ab
  aB_nonneg := by
    rw [div_eq_inv_mul]
    exact resampleStep_coordinate_nonneg frequency (by positivity) N.cast_inv_le_one drawn .aB
  ab_nonneg := by
    rw [div_eq_inv_mul]
    exact resampleStep_coordinate_nonneg frequency (by positivity) N.cast_inv_le_one drawn .ab
  total_eq_one := by
    have htotal := frequency.total_eq_one
    have hsum : stepDirection frequency drawn .AB + stepDirection frequency drawn .Ab +
        stepDirection frequency drawn .aB + stepDirection frequency drawn .ab = 0 := by
      cases drawn <;>
        simp [stepDirection, haplotypeCoordinate, twoLocusHaplotypeIndicator] <;>
        linarith
    linear_combination htotal + 1 / (N : ℝ) * hsum

/-- Reading one coordinate of the stepped simplex point. -/
@[simp] theorem resampleStep_coordinate (frequency : TwoLocusHaplotypeFrequencies) (N : ℕ)
    (drawn observed : TwoLocusHaplotype) :
    haplotypeCoordinate (resampleStep frequency N drawn) observed =
      haplotypeCoordinate frequency observed +
        stepDirection frequency drawn observed / N := by
  cases observed <;> rfl

/-- With no chromosome drawn the step leaves every coordinate alone. -/
theorem resampleStep_zero_coordinate (frequency : TwoLocusHaplotypeFrequencies)
    (drawn observed : TwoLocusHaplotype) :
    haplotypeCoordinate (resampleStep frequency 0 drawn) observed =
      haplotypeCoordinate frequency observed := by
  simp

/-- **Exact linear response at the left locus.**  One step moves the left marginal frequency
by exactly `1 / N` times the centred left-allele indicator, with no remainder. -/
theorem resampleStep_leftFrequency (frequency : TwoLocusHaplotypeFrequencies) (N : ℕ)
    (drawn : TwoLocusHaplotype) :
    (resampleStep frequency N drawn).leftFrequency =
      frequency.leftFrequency +
        1 / (N : ℝ) * (twoLocusLeftAlleleIndicator drawn -
          twoLocusHaplotypeMean frequency twoLocusLeftAlleleIndicator) := by
  cases drawn <;>
    simp [resampleStep, stepDirection, haplotypeCoordinate, twoLocusHaplotypeIndicator,
      twoLocusHaplotypeMean, twoLocusLeftAlleleIndicator,
      TwoLocusHaplotypeFrequencies.leftFrequency] <;>
    ring

/-- **Exact linear response at the right locus.**  One step moves the right marginal
frequency by exactly `1 / N` times the centred right-allele indicator. -/
theorem resampleStep_rightFrequency (frequency : TwoLocusHaplotypeFrequencies) (N : ℕ)
    (drawn : TwoLocusHaplotype) :
    (resampleStep frequency N drawn).rightFrequency =
      frequency.rightFrequency +
        1 / (N : ℝ) * (twoLocusRightAlleleIndicator drawn -
          twoLocusHaplotypeMean frequency twoLocusRightAlleleIndicator) := by
  cases drawn <;>
    simp [resampleStep, stepDirection, haplotypeCoordinate, twoLocusHaplotypeIndicator,
      twoLocusHaplotypeMean, twoLocusRightAlleleIndicator,
      TwoLocusHaplotypeFrequencies.rightFrequency] <;>
    ring

/-- The quadratic form of the resampling direction that carries the whole second-order
response of the linkage determinant. -/
def linkageStepForm (frequency : TwoLocusHaplotypeFrequencies)
    (drawn : TwoLocusHaplotype) : ℝ :=
  stepDirection frequency drawn .AB * stepDirection frequency drawn .ab -
    stepDirection frequency drawn .Ab * stepDirection frequency drawn .aB

/-- The linkage quadratic form of a direction is bounded by two. -/
theorem abs_linkageStepForm_le_two (frequency : TwoLocusHaplotypeFrequencies)
    (drawn : TwoLocusHaplotype) : |linkageStepForm frequency drawn| ≤ 2 := by
  have hproduct : ∀ first second : TwoLocusHaplotype,
      |stepDirection frequency drawn first * stepDirection frequency drawn second| ≤ 1 := by
    intro first second
    rw [abs_mul]
    have hfirst := abs_stepDirection_le_one frequency drawn first
    have hsecond := abs_stepDirection_le_one frequency drawn second
    nlinarith [abs_nonneg (stepDirection frequency drawn first),
      abs_nonneg (stepDirection frequency drawn second)]
  have hAB := abs_le.mp (hproduct .AB .ab)
  have hAb := abs_le.mp (hproduct .Ab .aB)
  simp only [linkageStepForm]
  rw [abs_le]
  constructor <;> linarith

/-- **Exact second-order response of the linkage determinant.**  A determinant is quadratic,
so one single-draw step moves it by exactly `1 / N` times the centred linkage gradient plus
`(1 / N) ^ 2` times the quadratic form of the direction.  There is no remainder at all; this
is the single-draw form of the expansion NOTE 1 (10) states for multinomial resampling. -/
theorem resampleStep_linkage (frequency : TwoLocusHaplotypeFrequencies) (N : ℕ)
    (drawn : TwoLocusHaplotype) :
    (resampleStep frequency N drawn).linkage =
      frequency.linkage +
        1 / (N : ℝ) * (twoLocusLinkageGradient frequency drawn -
          twoLocusHaplotypeMean frequency (twoLocusLinkageGradient frequency)) +
        (1 / (N : ℝ)) ^ 2 * linkageStepForm frequency drawn := by
  cases drawn <;>
    simp [resampleStep, stepDirection, haplotypeCoordinate, twoLocusHaplotypeIndicator,
      twoLocusHaplotypeMean, twoLocusLinkageGradient, linkageStepForm,
      TwoLocusHaplotypeFrequencies.linkage] <;>
    ring

/-- **The second-order term averages to the corpus drift.**  Averaging the linkage quadratic
form over the drawn haplotype returns exactly `twoLocusLinkageDrift`, the Wright--Fisher
linkage velocity the corpus builds from the four-category multinomial covariance. -/
theorem twoLocusHaplotypeMean_linkageStepForm (frequency : TwoLocusHaplotypeFrequencies) :
    twoLocusHaplotypeMean frequency (linkageStepForm frequency) =
      twoLocusLinkageDrift frequency := by
  have hfirst := twoLocusHaplotypeMean_centered_mul frequency
    (twoLocusHaplotypeIndicator .AB) (twoLocusHaplotypeIndicator .ab)
  have hsecond := twoLocusHaplotypeMean_centered_mul frequency
    (twoLocusHaplotypeIndicator .Ab) (twoLocusHaplotypeIndicator .aB)
  have hsplit : twoLocusHaplotypeMean frequency (linkageStepForm frequency) =
      twoLocusHaplotypeMean frequency (fun drawn ↦
          (twoLocusHaplotypeIndicator .AB drawn -
              twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator .AB)) *
            (twoLocusHaplotypeIndicator .ab drawn -
              twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator .ab))) -
        twoLocusHaplotypeMean frequency (fun drawn ↦
          (twoLocusHaplotypeIndicator .Ab drawn -
              twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator .Ab)) *
            (twoLocusHaplotypeIndicator .aB drawn -
              twoLocusHaplotypeMean frequency (twoLocusHaplotypeIndicator .aB))) := by
    simp only [twoLocusHaplotypeMean, linkageStepForm, stepDirection_eq_centered_indicator]
    ring
  rw [hsplit, hfirst, hsecond]
  rfl

/-- The linkage gradient has every coordinate in `[-1, 1]`. -/
theorem abs_twoLocusLinkageGradient_le_one (frequency : TwoLocusHaplotypeFrequencies)
    (observed : TwoLocusHaplotype) :
    |twoLocusLinkageGradient frequency observed| ≤ 1 := by
  have htotal := frequency.total_eq_one
  have hAB := frequency.AB_nonneg
  have hAb := frequency.Ab_nonneg
  have haB := frequency.aB_nonneg
  have hab := frequency.ab_nonneg
  cases observed <;> simp only [twoLocusLinkageGradient] <;> rw [abs_le] <;>
    constructor <;> linarith

/-- The left-allele indicator has absolute value at most one. -/
theorem abs_twoLocusLeftAlleleIndicator_le_one (observed : TwoLocusHaplotype) :
    |twoLocusLeftAlleleIndicator observed| ≤ 1 := by
  cases observed <;> simp [twoLocusLeftAlleleIndicator]

/-- The right-allele indicator has absolute value at most one. -/
theorem abs_twoLocusRightAlleleIndicator_le_one (observed : TwoLocusHaplotype) :
    |twoLocusRightAlleleIndicator observed| ≤ 1 := by
  cases observed <;> simp [twoLocusRightAlleleIndicator]

/-- One single-draw resampling step applied inside a single named deme of a multi-deme
haplotype state.  Every other deme is left exactly as it was. -/
def resampleStepAt {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies) (deme : Fin D)
    (N : ℕ) (drawn : TwoLocusHaplotype) : Fin D → TwoLocusHaplotypeFrequencies :=
  Function.update state deme (resampleStep (state deme) N drawn)

/-- The stepped deme carries the stepped simplex point. -/
@[simp] theorem resampleStepAt_self {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme : Fin D) (N : ℕ) (drawn : TwoLocusHaplotype) :
    resampleStepAt state deme N drawn deme = resampleStep (state deme) N drawn := by
  simp [resampleStepAt]

/-- Every deme other than the stepped one is unchanged. -/
theorem resampleStepAt_of_ne {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme other : Fin D) (N : ℕ) (drawn : TwoLocusHaplotype) (hne : other ≠ deme) :
    resampleStepAt state deme N drawn other = state other := by
  simp [resampleStepAt, Function.update_of_ne hne]

/-- Expectation of an observable of the whole multi-deme state after one single-draw
resampling step in the named deme, with the deme's own haplotype frequencies as the drawing
weights.  This is the `apply` of the resampling kernel. -/
def resampleExpectation {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme : Fin D) (N : ℕ)
    (observable : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ) : ℝ :=
  twoLocusHaplotypeMean (state deme)
    (fun drawn ↦ observable (resampleStepAt state deme N drawn))

/-- The resampling expectation of a constant observable is that constant. -/
theorem resampleExpectation_const {D : ℕ} (state : Fin D → TwoLocusHaplotypeFrequencies)
    (deme : Fin D) (N : ℕ) (level : ℝ) :
    resampleExpectation state deme N (fun _ ↦ level) = level := by
  simp only [resampleExpectation, twoLocusHaplotypeMean]
  linear_combination level * (state deme).total_eq_one

end

end Descent.Portability.SimplexResamplingKernel
