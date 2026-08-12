/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Structured
import Descent.Core.Moments
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

namespace Coalescent

open MeasureTheory

/-!
# The structured present-day law

This file supplies the object that the one-population block-counting result in
`SampleMonomorphism` explicitly leaves open.  The route is the structured coalescent of
Notohara (1990), followed by the exact two-population sample-frequency construction of
Wakeley and Hey (1997).  Numerical uniformization is not part of any definition here.

For source frequency `X` and target frequency `Y`, the finite table

`m a b = E[X^a Y^b]`

determines every joint sample-count probability.  If `I | X ~ Bin(ns,X)` and
`J | Y ~ Bin(nt,Y)`, independently conditional on `(X,Y)`, then

`P(I=i,J=j) = C(ns,i) C(nt,j)
  sum_{a=0}^{ns-i} sum_{b=0}^{nt-j}
    C(ns-i,a) C(nt-j,b) (-1)^(a+b) m(i+a,j+b)`.

That is the two-dimensional Bernstein transform below.  It is the joint present-day law;
fixation, loss of polymorphism and conditional spectra are events in this law, not
independently named attenuation factors.

For a piecewise-constant structured diffusion, every finite moment table is the solution of
a finite linear system.  `cramerCoordinate` records its symbolic solution.  When the entries
of the system are polynomial in demographic rates, each moment is therefore a rational
function of those rates.  This is also the representation used for the two-locus system:
Ragsdale and Gravel's `DD`, `Dz` and `pi2` recursions are a finite affine system, so Cramer's
rule is a closed form even when expanding its determinants would obscure the result.
-/

section SymbolicLinearSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Replace column `k` of a square matrix by a forcing vector. -/
noncomputable def replaceColumn (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (k : ι) : Matrix ι ι ℝ :=
  fun i j ↦ if j = k then b i else A i j

/-- One coordinate of the exact symbolic solution of `A x = b`, by Cramer's rule. -/
noncomputable def cramerCoordinate (A : Matrix ι ι ℝ)
    (b : ι → ℝ) (k : ι) : ℝ :=
  (replaceColumn A b k).det / A.det

/-- The symbolic coordinate is explicitly a determinant quotient.  If the matrix and forcing
entries are polynomial in model parameters, this is a rational function of those parameters;
no numerical inverse or fitted rate enters. -/
theorem cramerCoordinate_eq_det_ratio (A : Matrix ι ι ℝ)
    (b : ι → ℝ) (k : ι) :
    cramerCoordinate A b k = (replaceColumn A b k).det / A.det := rfl

/-- A ratio of two coordinates from the same nonsingular Cramer system cancels the common
operator determinant.  Keeping this proof abstract avoids expanding a concrete large matrix. -/
theorem cramerCoordinate_ratio_eq_replaceColumn_ratio
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (numerator denominator : ι)
    (hoperator : A.det ≠ 0)
    (hdenominator : (replaceColumn A b denominator).det ≠ 0) :
    cramerCoordinate A b numerator / cramerCoordinate A b denominator =
      (replaceColumn A b numerator).det / (replaceColumn A b denominator).det := by
  unfold cramerCoordinate
  field_simp [hoperator, hdenominator]

/-- A singular symbolic system is named rather than silently interpreted as a zero law. -/
theorem cramerCoordinate_at_singular_is_junk (A : Matrix ι ι ℝ)
    (b : ι → ℝ) (k : ι) (h : A.det = 0) :
    cramerCoordinate A b k = 0 := by
  unfold cramerCoordinate
  rw [h, div_zero]

end SymbolicLinearSystem

/-! ## A1. The two-deme joint present-day law -/

/-- Typed rates of the two-deme Wright--Fisher diffusion, in one declared time scale.
The positivity/nonnegativity constraints are fields, so a theorem cannot acquire a valid
demography from prose. -/
structure TwoDemeRates where
  sourceCoal : ℝ
  targetCoal : ℝ
  sourceToTarget : ℝ
  targetToSource : ℝ
  sourceForwardMutation : ℝ
  sourceBackwardMutation : ℝ
  targetForwardMutation : ℝ
  targetBackwardMutation : ℝ
  sourceCoal_pos : 0 < sourceCoal
  targetCoal_pos : 0 < targetCoal
  sourceToTarget_nonneg : 0 ≤ sourceToTarget
  targetToSource_nonneg : 0 ≤ targetToSource
  sourceForwardMutation_nonneg : 0 ≤ sourceForwardMutation
  sourceBackwardMutation_nonneg : 0 ≤ sourceBackwardMutation
  targetForwardMutation_nonneg : 0 ≤ targetForwardMutation
  targetBackwardMutation_nonneg : 0 ≤ targetBackwardMutation

/-- The structured diffusion generator applied to the mixed monomial `x^i y^j`, written as
a linear functional of a candidate moment table `m`.  Coalescence lowers an exponent,
migration moves one ancestral lineage between demes without changing total degree, and
parent-independent mutation lowers degree.  Thus moments through total degree `K` form a
closed finite system. -/
noncomputable def twoDemeMomentGenerator
    (r : TwoDemeRates) (m : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  r.sourceCoal * ((i * (i - 1) : ℕ) : ℝ) / 2 * (m (i - 1) j - m i j) +
  r.targetCoal * ((j * (j - 1) : ℕ) : ℝ) / 2 * (m i (j - 1) - m i j) +
  r.sourceToTarget * i * (m (i - 1) (j + 1) - m i j) +
  r.targetToSource * j * (m (i + 1) (j - 1) - m i j) +
  r.sourceForwardMutation * i * (m (i - 1) j - m i j) -
  r.sourceBackwardMutation * i * m i j +
  r.targetForwardMutation * j * (m i (j - 1) - m i j) -
  r.targetBackwardMutation * j * m i j

/-- Rectangular coordinate carrier for all moments required through total degree `K`.
Coordinates above total degree `K` are pinned by identity rows and do not enter valid rows. -/
abbrev MomentCoordinate (K : ℕ) := Fin (K + 1) × Fin (K + 1)

/-- Read a coordinate vector as a moment table, returning zero outside the finite rectangle. -/
noncomputable def momentVectorTable (K : ℕ)
    (v : MomentCoordinate K → ℝ) (i j : ℕ) : ℝ :=
  if hi : i < K + 1 then
    if hj : j < K + 1 then v (⟨i, hi⟩, ⟨j, hj⟩) else 0
  else 0

/-- Basis table for one unknown nonconstant moment. -/
noncomputable def momentBasisTable (K : ℕ) (column : MomentCoordinate K) : ℕ → ℕ → ℝ :=
  momentVectorTable K (fun coordinate ↦ if coordinate = column then 1 else 0)

/-- The fixed affine part `m₀₀=1`; every other coordinate is zero. -/
noncomputable def momentConstantTable : ℕ → ℕ → ℝ :=
  fun i j ↦ if i = 0 ∧ j = 0 then 1 else 0

/-- Exact finite coefficient matrix of the stationary structured moment system.  Valid
nonconstant moments receive generator rows.  The unused rectangle receives identity rows,
which makes the enclosing square representation harmless rather than singular by padding. -/
noncomputable def twoDemeMomentMatrix (r : TwoDemeRates) (K : ℕ) :
    Matrix (MomentCoordinate K) (MomentCoordinate K) ℝ :=
  fun row column ↦
    let i := row.1.val
    let j := row.2.val
    if 0 < i + j ∧ i + j ≤ K then
      twoDemeMomentGenerator r (momentBasisTable K column) i j
    else if row = column then 1 else 0

/-- Affine forcing created solely by the normalized constant moment `m₀₀=1`. -/
noncomputable def twoDemeMomentForcing (r : TwoDemeRates) (K : ℕ) :
    MomentCoordinate K → ℝ :=
  fun row ↦
    let i := row.1.val
    let j := row.2.val
    if 0 < i + j ∧ i + j ≤ K then
      -twoDemeMomentGenerator r momentConstantTable i j
    else 0

/-- The symbolic mixed moment obtained by solving the finite structured system with Cramer's
rule.  Moments beyond degree `K` are deliberately unavailable, not extrapolated. -/
noncomputable def solvedTwoDemeMixedMoment
    (r : TwoDemeRates) (K i j : ℕ) : ℝ :=
  if hzero : i = 0 ∧ j = 0 then 1
  else if hi : i < K + 1 then
    if hj : j < K + 1 then
      if hdegree : i + j ≤ K then
        cramerCoordinate (twoDemeMomentMatrix r K) (twoDemeMomentForcing r K)
          (⟨i, hi⟩, ⟨j, hj⟩)
      else 0
    else 0
  else 0

/-- The solved moment is literally a rational determinant expression in the demographic
rates. -/
theorem solvedTwoDemeMixedMoment_eq_cramer (r : TwoDemeRates) (K i j : ℕ)
    (hnotzero : ¬ (i = 0 ∧ j = 0)) (hi : i < K + 1) (hj : j < K + 1)
    (hdegree : i + j ≤ K) :
    solvedTwoDemeMixedMoment r K i j =
      cramerCoordinate (twoDemeMomentMatrix r K) (twoDemeMomentForcing r K)
        (⟨i, hi⟩, ⟨j, hj⟩) := by
  simp [solvedTwoDemeMixedMoment, hnotzero, hi, hj, hdegree]

/-- Bernstein core evaluated directly from a specified demography's symbolic moment solve. -/
noncomputable def solvedJointBernsteinCore (r : TwoDemeRates) (K : ℕ)
    (i j remainingSource remainingTarget : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (remainingSource + 1),
    ∑ b ∈ Finset.range (remainingTarget + 1),
      (Nat.choose remainingSource a : ℝ) * (Nat.choose remainingTarget b : ℝ) *
        (-1 : ℝ) ^ (a + b) * solvedTwoDemeMixedMoment r K (i + a) (j + b)

/-- A finite structured moment system on its genuine domain.  Nonsingularity is carried by
the value consumed downstream rather than left as a prose side condition. -/
structure NonsingularTwoDemeMomentSystem (K : ℕ) where
  rates : TwoDemeRates
  nonsingular : (twoDemeMomentMatrix rates K).det ≠ 0

/-- A1 without a hand-supplied moment table: the exact joint sample-count probability is the
Bernstein transform of the Cramer solution at total degree `ns+nt`. -/
noncomputable def solvedTwoDemeJointSampleCount
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt))
    (i j : ℕ) : ℝ :=
  if i ≤ ns ∧ j ≤ nt then
    (Nat.choose ns i : ℝ) * (Nat.choose nt j : ℝ) *
      solvedJointBernsteinCore system.rates (ns + nt) i j (ns - i) (nt - j)
  else 0

/-- The directly solved law is zero outside its sample rectangle. -/
theorem solvedTwoDemeJointSampleCount_outside
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt))
    (i j : ℕ) (h : ¬ (i ≤ ns ∧ j ≤ nt)) :
    solvedTwoDemeJointSampleCount ns nt system i j = 0 := by
  simp [solvedTwoDemeJointSampleCount, h]

/-! ### Sample-size-specific ascertainment events -/

/-- Mass of the event that the source sample is polymorphic.  The cohort sizes occur in the
event itself: source counts range from `1` through `ns - 1`, and every target count through
`nt` is marginalized.  This is not a time parameter. -/
noncomputable def sourcePolymorphicEventMass
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (ns - 1),
    ∑ j ∈ Finset.range (nt + 1), jointCount i j

/-- Mass of source polymorphism together with target monomorphism.  Increasing `nt` moves
the upper monomorphic boundary from the count `nt` to the new cohort size, so a cohort-size
change alters the conditioning event even if the underlying frequency law is held fixed. -/
noncomputable def sourcePolymorphicTargetMonomorphicEventMass
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (ns - 1), (jointCount i 0 + jointCount i nt)

/-- Exact cohort-evaluation functional: target monomorphism conditional on observed source
polymorphism, evaluated from one joint count law.  A time-shift approximation is not an
argument of this definition; sample-size dependence enters both the supplied Bernstein law
and the event boundaries above. -/
noncomputable def targetErosionEvent
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) : Option ℝ :=
  let denominator := sourcePolymorphicEventMass jointCount ns nt
  if 0 < denominator then
    some (sourcePolymorphicTargetMonomorphicEventMass jointCount ns nt / denominator)
  else none

/-! ### Transient piecewise demographies -/

/-- Homogeneous generator for the nonconstant moment coordinates.  Unlike the stationary
square solve, unused padding coordinates have zero rows: they do not evolve. -/
noncomputable def twoDemeMomentDynamicsMatrix (r : TwoDemeRates) (K : ℕ) :
    Matrix (MomentCoordinate K) (MomentCoordinate K) ℝ :=
  fun row column ↦
    let i := row.1.val
    let j := row.2.val
    if 0 < i + j ∧ i + j ≤ K then
      twoDemeMomentGenerator r (momentBasisTable K column) i j
    else 0

/-- The exact matrix exponential, defined by its absolutely convergent power series. -/
noncomputable def matrixExponential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) : Matrix ι ι ℝ :=
  ∑' power : ℕ, ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)

/-- The series used by `matrixExponential` is summable for every finite real matrix and
every real time.  The operator norm is introduced only inside the proof; the exponential's
definition and all downstream demographic objects remain independent of a chosen matrix
norm. -/
private theorem matrixExponentialSeries_summable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) :
    Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) := by
  open scoped Matrix.Norms.Operator in
    exact NormedSpace.expSeries_summable' (𝕂 := ℝ) (time • A)

/-- Generator intertwining propagates through every finite power.  The following theorem
passes this identity through the absolutely convergent exponential series. -/
theorem matrix_pow_intertwines
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (projection : Matrix κ ι ℝ) (source : Matrix ι ι ℝ) (target : Matrix κ κ ℝ)
    (hgenerator : projection * source = target * projection) (power : ℕ) :
    projection * source ^ power = target ^ power * projection := by
  induction power with
  | zero => simp
  | succ power ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hgenerator,
        ← Matrix.mul_assoc, ← pow_succ]

/-- A generator projection intertwines the exact epoch semigroups.  This is the analytic
completion of `matrix_pow_intertwines`: absolute convergence permits left and right matrix
multiplication to pass through the power series, and every corresponding power agrees. -/
theorem matrixExponential_intertwines
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (projection : Matrix κ ι ℝ) (source : Matrix ι ι ℝ) (target : Matrix κ κ ℝ)
    (hgenerator : projection * source = target * projection) (time : ℝ) :
    projection * matrixExponential source time =
      matrixExponential target time * projection := by
  let left : Matrix ι ι ℝ →+ Matrix κ ι ℝ :=
    { toFun := fun matrix ↦ projection * matrix
      map_zero' := by simp
      map_add' := by intro first second; rw [Matrix.mul_add] }
  let right : Matrix κ κ ℝ →+ Matrix κ ι ℝ :=
    { toFun := fun matrix ↦ matrix * projection
      map_zero' := by simp
      map_add' := by intro first second; rw [Matrix.add_mul] }
  have hleftContinuous : Continuous left := by
    exact continuous_const.matrix_mul continuous_id
  have hrightContinuous : Continuous right := by
    exact continuous_id.matrix_mul continuous_const
  have hleft :=
    (matrixExponentialSeries_summable source time).hasSum.map left hleftContinuous
  have hright :=
    (matrixExponentialSeries_summable target time).hasSum.map right hrightContinuous
  have hscaled : projection * (time • source) = (time • target) * projection := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hgenerator]
  unfold matrixExponential
  change left (∑' power : ℕ,
      ((power.factorial : ℝ)⁻¹) • ((time • source) ^ power)) =
    right (∑' power : ℕ,
      ((power.factorial : ℝ)⁻¹) • ((time • target) ^ power))
  rw [← hleft.tsum_eq, ← hright.tsum_eq]
  apply tsum_congr
  intro power
  change projection *
      (((power.factorial : ℝ)⁻¹) • ((time • source) ^ power)) =
    (((power.factorial : ℝ)⁻¹) • ((time • target) ^ power)) * projection
  rw [Matrix.mul_smul, Matrix.smul_mul,
    matrix_pow_intertwines projection (time • source) (time • target) hscaled power]

/-- Add one constant coordinate to turn `x' = A x + b` into a homogeneous system. -/
abbrev AffineMomentCoordinate (K : ℕ) := Option (MomentCoordinate K)

/-- Augmented affine generator `[A, -b; 0, 0]`.  The stationary system is `A m = b`,
whereas forward dynamics is `m' = A m - b`; `none` is the constant coordinate. -/
noncomputable def augmentedTwoDemeMomentGenerator (r : TwoDemeRates) (K : ℕ) :
    Matrix (AffineMomentCoordinate K) (AffineMomentCoordinate K) ℝ
  | some row, some column => twoDemeMomentDynamicsMatrix r K row column
  | some row, none => -twoDemeMomentForcing r K row
  | none, _ => 0

/-- One piecewise-constant epoch.  Rates may change arbitrarily between epochs. -/
structure TwoDemeMomentEpoch (K : ℕ) where
  rates : TwoDemeRates
  duration : ℝ
  duration_nonneg : 0 ≤ duration

/-- Exact propagator of one epoch. -/
noncomputable def TwoDemeMomentEpoch.propagator {K : ℕ}
    (epoch : TwoDemeMomentEpoch K) :
    Matrix (AffineMomentCoordinate K) (AffineMomentCoordinate K) ℝ :=
  matrixExponential (augmentedTwoDemeMomentGenerator epoch.rates K) epoch.duration

/-- At an instantaneous split the two daughter frequencies equal the ancestral frequency,
so the mixed moment `(i,j)` is the ancestral moment of total degree `i+j`. -/
noncomputable def splitMomentState (K : ℕ) (ancestralMoment : ℕ → ℝ) :
    AffineMomentCoordinate K → ℝ
  | none => 1
  | some coordinate =>
      let i := coordinate.1.val
      let j := coordinate.2.val
      if 0 < i + j ∧ i + j ≤ K then ancestralMoment (i + j) else 0

/-- Apply a list of epochs in forward-time order. -/
noncomputable def propagateTwoDemeMomentEpochs {K : ℕ}
    (epochs : List (TwoDemeMomentEpoch K))
    (initial : AffineMomentCoordinate K → ℝ) : AffineMomentCoordinate K → ℝ :=
  epochs.foldl (fun state epoch ↦ epoch.propagator.mulVec state) initial

/-- Arbitrary piecewise-constant two-deme history from an ancestral frequency law. -/
structure PiecewiseTwoDemeMomentDemography (K : ℕ) where
  ancestralMoment : ℕ → ℝ
  ancestralMeasure : Measure ℝ
  ancestralProbability : IsProbabilityMeasure ancestralMeasure
  ancestralSupported : ∀ᵐ frequency ∂ancestralMeasure, frequency ∈ Set.Icc (0 : ℝ) 1
  ancestralMoment_spec : ∀ degree,
    ancestralMoment degree = ∫ frequency, frequency ^ degree ∂ancestralMeasure
  ancestralNormalized : ancestralMoment 0 = 1
  epochs : List (TwoDemeMomentEpoch K)

/-- Present-day mixed moment under the full epoch cascade. -/
noncomputable def PiecewiseTwoDemeMomentDemography.presentMoment {K : ℕ}
    (demography : PiecewiseTwoDemeMomentDemography K) (i j : ℕ) : ℝ :=
  if hzero : i = 0 ∧ j = 0 then 1
  else if hi : i < K + 1 then
    if hj : j < K + 1 then
      if hdegree : i + j ≤ K then
        propagateTwoDemeMomentEpochs demography.epochs
          (splitMomentState K demography.ancestralMoment) (some (⟨i, hi⟩, ⟨j, hj⟩))
      else 0
    else 0
  else 0

/-- Present-day Bernstein core after an arbitrary epoch cascade. -/
noncomputable def PiecewiseTwoDemeMomentDemography.jointBernsteinCore {K : ℕ}
    (demography : PiecewiseTwoDemeMomentDemography K)
    (i j remainingSource remainingTarget : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (remainingSource + 1),
    ∑ b ∈ Finset.range (remainingTarget + 1),
      (Nat.choose remainingSource a : ℝ) * (Nat.choose remainingTarget b : ℝ) *
        (-1 : ℝ) ^ (a + b) * demography.presentMoment (i + a) (j + b)

/-- A1 for an arbitrary finite epoch cascade.  The type index pins the moment degree to the
two requested sample sizes. -/
noncomputable def PiecewiseTwoDemeMomentDemography.jointSampleCount
    (ns nt : ℕ) (demography : PiecewiseTwoDemeMomentDemography (ns + nt))
    (i j : ℕ) : ℝ :=
  if i ≤ ns ∧ j ≤ nt then
    (Nat.choose ns i : ℝ) * (Nat.choose nt j : ℝ) *
      demography.jointBernsteinCore i j (ns - i) (nt - j)
  else 0

/-- Fixed differences are events of the transient joint law. -/
noncomputable def PiecewiseTwoDemeMomentDemography.fixedDifference
    (ns nt : ℕ) (demography : PiecewiseTwoDemeMomentDemography (ns + nt)) : ℝ :=
  demography.jointSampleCount ns nt ns 0 + demography.jointSampleCount ns nt 0 nt

/-- Target monomorphism conditional on source polymorphism under the same transient law. -/
noncomputable def PiecewiseTwoDemeMomentDemography.targetErosionGivenSourcePolymorphic
    (ns nt : ℕ) (demography : PiecewiseTwoDemeMomentDemography (ns + nt)) : Option ℝ :=
  targetErosionEvent (demography.jointSampleCount ns nt) ns nt

/-- Conditional target spectrum under the full transient demography. -/
noncomputable def PiecewiseTwoDemeMomentDemography.conditionalTargetSpectrum
    (ns nt : ℕ) (demography : PiecewiseTwoDemeMomentDemography (ns + nt))
    (sourceCount targetCount : ℕ) : Option ℝ :=
  let denominator := ∑ j ∈ Finset.range (nt + 1),
    demography.jointSampleCount ns nt sourceCount j
  if 0 < denominator then
    some (demography.jointSampleCount ns nt sourceCount targetCount / denominator)
  else none

/-- Zero-duration epochs are identity propagators: an exact analytic limit. -/
theorem matrixExponential_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : matrixExponential A 0 = 1 := by
  unfold matrixExponential
  rw [tsum_eq_single 0 (by intro n hn; simp [zero_pow hn])]
  simp

/-- The exponential of the zero generator is the identity at every elapsed time. -/
theorem matrixExponential_zero_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (time : ℝ) : matrixExponential (0 : Matrix ι ι ℝ) time = 1 := by
  unfold matrixExponential
  rw [tsum_eq_single 0 (by intro n hn; simp [zero_pow hn])]
  simp

/-- A zero generator row is an exactly conserved coordinate of every matrix-exponential
trajectory.  This is the finite-dimensional conservation law used below for augmented affine
constants and for rectangular padding coordinates; it follows from a one-row intertwining,
not from a numerical ODE approximation. -/
theorem matrixExponential_mulVec_apply_of_row_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (state : ι → ℝ) (coordinate : ι)
    (hrow : ∀ column, A coordinate column = 0) :
    (matrixExponential A time).mulVec state coordinate = state coordinate := by
  let select : Matrix Unit ι ℝ := fun _ column ↦ if column = coordinate then 1 else 0
  have hgenerator : select * A = (0 : Matrix Unit Unit ℝ) * select := by
    apply Matrix.ext
    intro row column
    simp [Matrix.mul_apply, select, hrow]
  have hsemigroup := matrixExponential_intertwines select A
    (0 : Matrix Unit Unit ℝ) hgenerator time
  rw [matrixExponential_zero_matrix] at hsemigroup
  have happ := congrArg (fun matrix ↦ matrix.mulVec state) hsemigroup
  change (select * matrixExponential A time).mulVec state =
    ((1 : Matrix Unit Unit ℝ) * select).mulVec state at happ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at happ
  have hcoordinate := congrFun happ ()
  simpa [Matrix.mulVec, dotProduct, select] using hcoordinate

/-- Fixed difference under the directly solved joint law. -/
noncomputable def solvedTwoDemeFixedDifference
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt)) : ℝ :=
  solvedTwoDemeJointSampleCount ns nt system ns 0 +
    solvedTwoDemeJointSampleCount ns nt system 0 nt

/-- Target erosion conditional on source polymorphism, with both masses evaluated from the
same directly solved joint law. -/
noncomputable def solvedTwoDemeTargetErosionGivenSourcePolymorphic
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt)) : Option ℝ :=
  targetErosionEvent (solvedTwoDemeJointSampleCount ns nt system) ns nt

/-- Conditional target spectrum at a given source count, directly from the symbolic joint
law. -/
noncomputable def solvedTwoDemeConditionalTargetSpectrum
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt))
    (sourceCount targetCount : ℕ) : Option ℝ :=
  let denominator := ∑ j ∈ Finset.range (nt + 1),
    solvedTwoDemeJointSampleCount ns nt system sourceCount j
  if 0 < denominator then
    some (solvedTwoDemeJointSampleCount ns nt system sourceCount targetCount / denominator)
  else none

/-- A present-day two-deme frequency law backed by an actual probability measure on the unit
square.  Stationary Cramer solves and transient epoch propagators are constructors of this
interface only after their moment tables have been certified against such a measure. -/
structure TwoDemePresentDayLaw where
  mixedMoment : ℕ → ℕ → ℝ
  representingMeasure : Measure (ℝ × ℝ)
  probability : IsProbabilityMeasure representingMeasure
  supported_on_unit_square : ∀ᵐ frequency ∂representingMeasure,
    frequency.1 ∈ Set.Icc (0 : ℝ) 1 ∧ frequency.2 ∈ Set.Icc (0 : ℝ) 1
  mixedMoment_spec : ∀ i j,
    mixedMoment i j =
      ∫ frequency, frequency.1 ^ i * frequency.2 ^ j ∂representingMeasure
  normalized : mixedMoment 0 0 = 1
  moment_nonneg : ∀ i j, 0 ≤ mixedMoment i j
  moment_le_one : ∀ i j, mixedMoment i j ≤ 1

/-- Falling on the complement side of a binomial sample expands by the binomial theorem.
This is `E[X^i(1-X)^remaining Y^j(1-Y)^remaining]` in mixed moments. -/
noncomputable def jointBernsteinCore (law : TwoDemePresentDayLaw)
    (i j remainingSource remainingTarget : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (remainingSource + 1),
    ∑ b ∈ Finset.range (remainingTarget + 1),
      (Nat.choose remainingSource a : ℝ) * (Nat.choose remainingTarget b : ℝ) *
        (-1 : ℝ) ^ (a + b) * law.mixedMoment (i + a) (j + b)

/-- **The exact two-deme joint present-day sample law.**  The arguments `i,j` are allele
counts in source and target samples.  Out-of-range counts are zero. -/
noncomputable def twoDemeJointSampleCount (law : TwoDemePresentDayLaw)
    (ns nt i j : ℕ) : ℝ :=
  if i ≤ ns ∧ j ≤ nt then
    (Nat.choose ns i : ℝ) * (Nat.choose nt j : ℝ) *
      jointBernsteinCore law i j (ns - i) (nt - j)
  else 0

/-- The ancestral allele and its complement give the same monomorphism event.  Written as
an event in the joint law, not as a separately postulated survival factor. -/
noncomputable def twoDemeBothSamplesMonomorphic (law : TwoDemePresentDayLaw)
    (ns nt : ℕ) : ℝ :=
  twoDemeJointSampleCount law ns nt 0 0 +
  twoDemeJointSampleCount law ns nt ns nt +
  twoDemeJointSampleCount law ns nt ns 0 +
  twoDemeJointSampleCount law ns nt 0 nt

/-- Probability of a fixed difference between the two samples. -/
noncomputable def twoDemeFixedDifference (law : TwoDemePresentDayLaw)
    (ns nt : ℕ) : ℝ :=
  twoDemeJointSampleCount law ns nt ns 0 +
    twoDemeJointSampleCount law ns nt 0 nt

/-- Probability that a source-polymorphic sampled variant is absent or fixed in the target
sample.  Conditioning happens once, by division by the source-polymorphic mass; there is no
sign-changing correction term. -/
noncomputable def twoDemeTargetErosionGivenSourcePolymorphic
    (law : TwoDemePresentDayLaw) (ns nt : ℕ) : Option ℝ :=
  targetErosionEvent (twoDemeJointSampleCount law ns nt) ns nt

/-- Conditional target spectrum given a source count.  This is the object required by
ascertainment: the numerator and denominator are entries of one joint law, so conditioning
cannot introduce an independently chosen sign or multiplier. -/
noncomputable def twoDemeConditionalTargetSpectrum
    (law : TwoDemePresentDayLaw) (ns nt sourceCount targetCount : ℕ) : Option ℝ :=
  let denominator := ∑ j ∈ Finset.range (nt + 1),
    twoDemeJointSampleCount law ns nt sourceCount j
  if 0 < denominator then
    some (twoDemeJointSampleCount law ns nt sourceCount targetCount / denominator)
  else none

/-- The joint count law has literal zero outside its sample rectangle. -/
theorem twoDemeJointSampleCount_outside (law : TwoDemePresentDayLaw)
    (ns nt i j : ℕ) (h : ¬ (i ≤ ns ∧ j ≤ nt)) :
    twoDemeJointSampleCount law ns nt i j = 0 := by
  simp [twoDemeJointSampleCount, h]

/-! ## A2. The two-deme two-locus stationary law -/

/-- A finite Ragsdale--Gravel two-locus moment system.  Its coordinates are the canonical
`DD`, `Dz`, and `pi2` moments.  The operator is `drift + recombination + migration`; the
forcing is mutation applied to the already-solved heterozygosity vector. -/
structure TwoDemeLDSystem (n : ℕ) where
  operator : ℝ → ℝ → Matrix (Fin n) (Fin n) ℝ
  forcing : ℝ → Fin n → ℝ
  withinSource : Fin n
  crossSourceTarget : Fin n
  withinTarget : Fin n
  symmetricWithin : ∀ (rho M : ℝ),
    cramerCoordinate (operator rho M) (fun i ↦ -forcing M i) withinSource =
      cramerCoordinate (operator rho M) (fun i ↦ -forcing M i) withinTarget

/-- An affine stationary two-locus system.  Published drift, recombination and migration
matrices plug into separate fields, making every entry polynomial of degree at most one in
`rho` and `M`; determinant coordinates are therefore rational functions of those parameters. -/
structure AffineTwoDemeLDSystem (n : ℕ) where
  drift : Matrix (Fin n) (Fin n) ℝ
  recombination : Matrix (Fin n) (Fin n) ℝ
  migration : Matrix (Fin n) (Fin n) ℝ
  forcingBase : Fin n → ℝ
  forcingMigration : Fin n → ℝ
  withinSource : Fin n
  crossSourceTarget : Fin n
  withinTarget : Fin n
  symmetricWithin : ∀ (rho M : ℝ),
    cramerCoordinate (drift + rho • recombination + M • migration)
        (fun i ↦ -(forcingBase i + M * forcingMigration i)) withinSource =
      cramerCoordinate (drift + rho • recombination + M • migration)
        (fun i ↦ -(forcingBase i + M * forcingMigration i)) withinTarget

/-- Forget only the affine decomposition, preserving the exact operator and moment indices. -/
noncomputable def AffineTwoDemeLDSystem.toSystem {n : ℕ}
    (sys : AffineTwoDemeLDSystem n) : TwoDemeLDSystem n where
  operator := fun rho M ↦ sys.drift + rho • sys.recombination + M • sys.migration
  forcing := fun M i ↦ sys.forcingBase i + M * sys.forcingMigration i
  withinSource := sys.withinSource
  crossSourceTarget := sys.crossSourceTarget
  withinTarget := sys.withinTarget
  symmetricWithin := sys.symmetricWithin

/-- A stationary two-locus coordinate, exactly `-(D+R+M)^{-1}Uh` in the published moment
system, expressed by Cramer's rule. -/
noncomputable def TwoDemeLDSystem.stationaryCoordinate {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ) (k : Fin n) : ℝ :=
  cramerCoordinate (sys.operator rho M) (fun i ↦ -sys.forcing M i) k

/-- The `E[D_source D_target]` member of the stationary family. -/
noncomputable def TwoDemeLDSystem.crossD {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ) : ℝ :=
  sys.stationaryCoordinate rho M sys.crossSourceTarget

/-- The source `E[D^2]` member of the same solve. -/
noncomputable def TwoDemeLDSystem.withinD {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ) : ℝ :=
  sys.stationaryCoordinate rho M sys.withinSource

/-- Cross-deme correlation of `D`.  Equal sizes and symmetric migration make the two
within-deme second moments equal, so the square-root denominator reduces to `E[D^2]`.
This name is introduced only after both numerator and denominator exist in the solved law. -/
noncomputable def TwoDemeLDSystem.crossDCorrelation {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ) : ℝ :=
  sys.crossD rho M / sys.withinD rho M

/-- A2's closed form for an arbitrary published affine moment system. -/
noncomputable def AffineTwoDemeLDSystem.crossDCorrelation {n : ℕ}
    (sys : AffineTwoDemeLDSystem n) (rho M : ℝ) : ℝ :=
  sys.toSystem.crossDCorrelation rho M

/-- A parameter point on which the affine stationary solution and its correlation denominator
exist.  Both counterexample-producing poles are excluded by the value's type. -/
structure NonsingularAffineLDPoint {n : ℕ} (sys : AffineTwoDemeLDSystem n) where
  rho : ℝ
  migration : ℝ
  rho_nonnegative : 0 ≤ rho
  migration_nonnegative : 0 ≤ migration
  operator_nonsingular :
    (sys.drift + rho • sys.recombination + migration • sys.migration).det ≠ 0
  within_numerator_nonzero :
    (replaceColumn
      (sys.drift + rho • sys.recombination + migration • sys.migration)
      (fun i ↦ -(sys.forcingBase i + migration * sys.forcingMigration i))
      sys.withinSource).det ≠ 0

/-- Correlation evaluated only at a typed nonsingular parameter point. -/
noncomputable def NonsingularAffineLDPoint.crossDCorrelation {n : ℕ}
    {sys : AffineTwoDemeLDSystem n} (point : NonsingularAffineLDPoint sys) : ℝ :=
  sys.crossDCorrelation point.rho point.migration

/-- The affine system's cross moment is visibly the Cramer quotient of a matrix affine in
recombination and migration. -/
theorem AffineTwoDemeLDSystem.crossD_eq_det_ratio {n : ℕ}
    (sys : AffineTwoDemeLDSystem n) (rho M : ℝ) :
    sys.toSystem.crossD rho M =
      (replaceColumn
        (sys.drift + rho • sys.recombination + M • sys.migration)
        (fun i ↦ -(sys.forcingBase i + M * sys.forcingMigration i))
        sys.crossSourceTarget).det /
      (sys.drift + rho • sys.recombination + M • sys.migration).det := rfl


/-- **The migration--LD law is rational in `(rho,M)`.**  Expanded determinants are not a
different result: this quotient is exactly the quotient of two Cramer numerators, because
the common system determinant cancels. -/
theorem TwoDemeLDSystem.crossDCorrelation_eq_cramer_numerator_ratio {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ)
    (hdet : (sys.operator rho M).det ≠ 0)
    (hwithin : (replaceColumn (sys.operator rho M) (fun i ↦ -sys.forcing M i)
      sys.withinSource).det ≠ 0) :
    sys.crossDCorrelation rho M =
      (replaceColumn (sys.operator rho M) (fun i ↦ -sys.forcing M i)
        sys.crossSourceTarget).det /
      (replaceColumn (sys.operator rho M) (fun i ↦ -sys.forcing M i)
        sys.withinSource).det := by
  unfold TwoDemeLDSystem.crossDCorrelation TwoDemeLDSystem.crossD
    TwoDemeLDSystem.withinD TwoDemeLDSystem.stationaryCoordinate cramerCoordinate
  field_simp [hdet, hwithin]

/-- The panmictic check: once migration makes the cross and within Cramer numerators equal,
the correlation is exactly one.  This is an analytic limit check, not a numerical validator. -/
theorem TwoDemeLDSystem.crossDCorrelation_panmixia {n : ℕ}
    (sys : TwoDemeLDSystem n) (rho M : ℝ)
    (hwithin : sys.withinD rho M ≠ 0)
    (hpan : sys.crossD rho M = sys.withinD rho M) :
    sys.crossDCorrelation rho M = 1 := by
  unfold TwoDemeLDSystem.crossDCorrelation
  rw [hpan, div_self hwithin]

/-! ## A3--A4. Typed demographic functionals and the many-deme representation -/

/-- Typed rates for an arbitrary finite structured diffusion. -/
structure ManyDemeRates (D : ℕ) where
  coalescence : Fin D → ℝ
  migration : Fin D → Fin D → ℝ
  forwardMutation : Fin D → ℝ
  backwardMutation : Fin D → ℝ
  coalescence_pos : ∀ d, 0 < coalescence d
  migration_nonneg : ∀ i j, 0 ≤ migration i j
  migration_self : ∀ i, migration i i = 0
  forwardMutation_nonneg : ∀ d, 0 ≤ forwardMutation d
  backwardMutation_nonneg : ∀ d, 0 ≤ backwardMutation d

/-- The homogeneous augmentation of the expected allelic-divergence evolution law.

The final argument is the degree-zero moment carried as an explicit affine coordinate.  A
probability moment table supplies `constant = 1`; matrix columns supply either zero or one.
Making that coordinate explicit is what permits the generator identity below to lift through
matrix multiplication without pretending that individual basis columns are probability
laws. -/
noncomputable def symmetricPairDivergenceAffineDerivative {D : ℕ}
    (coalescence : Fin D → ℝ) (migration : Fin D → Fin D → ℝ)
    (mutation : Fin D → ℝ) (divergence : Fin D → Fin D → ℝ)
    (constant : ℝ) (first second : Fin D) : ℝ :=
  (if first = second then
      -coalescence first * divergence first second
    else 0) +
    (∑ target, migration first target *
      (divergence target second - divergence first second)) +
    (∑ target, migration second target *
      (divergence first target - divergence first second)) -
    (mutation first + mutation second) * divergence first second +
    (mutation first + mutation second) / 2 * constant

/-- The closed affine evolution law for expected allelic divergence
`H(i,j) = E[X_i] + E[X_j] - 2 E[X_i X_j]` under symmetric recurrent mutation.

`mutation` is the total forward-plus-backward rate (`2u` when both directions have rate
`u`).  This operator is deliberately shared by the marginal and joint systems: a projection
proof has one target law rather than two algebraically similar formulas. -/
noncomputable def symmetricPairDivergenceDerivative {D : ℕ}
    (coalescence : Fin D → ℝ) (migration : Fin D → Fin D → ℝ)
    (mutation : Fin D → ℝ) (divergence : Fin D → Fin D → ℝ)
    (first second : Fin D) : ℝ :=
  symmetricPairDivergenceAffineDerivative coalescence migration mutation divergence 1 first second

/-- Lower one exponent, using truncated subtraction only at the coordinate whose coefficient
already guarantees a positive exponent. -/
def decrementExponent {D : ℕ} (exponent : Fin D → ℕ) (deme : Fin D) : Fin D → ℕ :=
  fun d ↦ if d = deme then exponent d - 1 else exponent d

/-- Move one ancestral lineage from one deme label to another.

Empirical status: NOT AN EMPIRICAL CLAIM -- index bookkeeping for the moment generator.
Relabelling a lineage asserts nothing about a population; the generator assembled from it is
where a migration mechanism is chosen, and the composed output is where a measurement could
bear. -/
def migrateExponent {D : ℕ} (exponent : Fin D → ℕ)
    (src dst : Fin D) : Fin D → ℕ :=
  fun d ↦ if d = src then exponent d - 1 else if d = dst then exponent d + 1 else exponent d

/-- The arbitrary-deme structured moment generator.  This is the direct many-deme extension
of `twoDemeMomentGenerator`; a serial chain, grid, island model, or typed external demography
differs only in the supplied rate matrix and epoch schedule. -/
noncomputable def manyDemeMomentGenerator {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ) (exponent : Fin D → ℕ) : ℝ :=
  (∑ d, rates.coalescence d * ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
      (moment (decrementExponent exponent d) - moment exponent)) +
  (∑ src, ∑ dst, rates.migration src dst * exponent src *
      (moment (migrateExponent exponent src dst) - moment exponent)) +
  (∑ d, (rates.forwardMutation d * exponent d *
      (moment (decrementExponent exponent d) - moment exponent) -
    rates.backwardMutation d * exponent d * moment exponent))

/-! ### Exact finite propagation for arbitrary deme count -/

/-- Finite rectangular carrier for every exponent through coordinatewise degree `K`.
Rows whose total degree exceeds `K` are padding and never enter a valid generator row. -/
abbrev ManyDemeMomentCoordinate (D K : ℕ) := Fin D → Fin (K + 1)

/-- Total degree of a finite many-deme moment coordinate. -/
def ManyDemeMomentCoordinate.degree {D K : ℕ}
    (coordinate : ManyDemeMomentCoordinate D K) : ℕ :=
  ∑ d, (coordinate d).val

/-- Read a finite vector as a moment table, returning zero outside its rectangle. -/
noncomputable def manyDemeMomentVectorTable {D : ℕ} (K : ℕ)
    (vector : ManyDemeMomentCoordinate D K → ℝ)
    (exponent : Fin D → ℕ) : ℝ :=
  if h : ∀ d, exponent d < K + 1 then
    vector (fun d ↦ ⟨exponent d, h d⟩)
  else 0

/-- Basis table for one many-deme moment coordinate. -/
noncomputable def manyDemeMomentBasisTable {D : ℕ} (K : ℕ)
    (column : ManyDemeMomentCoordinate D K) : (Fin D → ℕ) → ℝ :=
  manyDemeMomentVectorTable K (fun coordinate ↦ if coordinate = column then 1 else 0)

/-- Normalized constant moment table. -/
noncomputable def manyDemeMomentConstantTable {D : ℕ} : (Fin D → ℕ) → ℝ :=
  fun exponent ↦ if ∀ d, exponent d = 0 then 1 else 0

/-- Homogeneous generator matrix for all nonconstant moments of total degree at most `K`. -/
noncomputable def manyDemeMomentDynamicsMatrix {D : ℕ}
    (rates : ManyDemeRates D) (K : ℕ) :
    Matrix (ManyDemeMomentCoordinate D K) (ManyDemeMomentCoordinate D K) ℝ :=
  fun row column ↦
    if 0 < row.degree ∧ row.degree ≤ K then
      manyDemeMomentGenerator rates (manyDemeMomentBasisTable K column)
        (fun d ↦ (row d).val)
    else 0

/-- Affine forcing contributed by the normalized constant moment. -/
noncomputable def manyDemeMomentForcing {D : ℕ}
    (rates : ManyDemeRates D) (K : ℕ) : ManyDemeMomentCoordinate D K → ℝ :=
  fun row ↦
    if 0 < row.degree ∧ row.degree ≤ K then
      -manyDemeMomentGenerator rates manyDemeMomentConstantTable
        (fun d ↦ (row d).val)
    else 0

/-- Constant-augmented coordinate for affine many-deme moment propagation. -/
abbrev AffineManyDemeMomentCoordinate (D K : ℕ) :=
  Option (ManyDemeMomentCoordinate D K)

/-- Exact affine generator `[A,-b;0,0]` for arbitrary finite deme count. -/
noncomputable def augmentedManyDemeMomentGenerator {D : ℕ}
    (rates : ManyDemeRates D) (K : ℕ) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ
  | some row, some column => manyDemeMomentDynamicsMatrix rates K row column
  | some row, none => -manyDemeMomentForcing rates K row
  | none, _ => 0

/-- One arbitrary-deme piecewise-constant diffusion epoch in raw time units. -/
structure ManyDemeMomentEpoch (D K : ℕ) where
  rates : ManyDemeRates D
  duration : ℝ
  duration_nonneg : 0 ≤ duration

/-- Exact matrix-exponential propagator for an arbitrary-deme epoch. -/
noncomputable def ManyDemeMomentEpoch.propagator {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  matrixExponential (augmentedManyDemeMomentGenerator epoch.rates K) epoch.duration

/-- The explicit affine constant is conserved by every arbitrary-deme moment epoch. -/
theorem ManyDemeMomentEpoch.propagator_none {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    epoch.propagator.mulVec state none = state none := by
  apply matrixExponential_mulVec_apply_of_row_zero
  intro column
  rfl

/-- The duplicated degree-zero coordinate in the rectangular carrier is padding and remains
exactly fixed under every epoch.  Reachable states initialize it at zero, so it can never
contaminate the affine constant or a biological moment. -/
theorem ManyDemeMomentEpoch.propagator_zeroCoordinate {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    epoch.propagator.mulVec state (some (fun _ ↦ 0)) = state (some (fun _ ↦ 0)) := by
  apply matrixExponential_mulVec_apply_of_row_zero
  intro column
  cases column <;>
    simp [augmentedManyDemeMomentGenerator, manyDemeMomentDynamicsMatrix,
      manyDemeMomentForcing, ManyDemeMomentCoordinate.degree]

/-- Merge a newly split child's exponent back into its parent.  This is the pullback of the
instantaneous constraint `X_child = X_parent`. -/
def mergeSplitExponent {D : ℕ} (parent child : Fin D)
    (exponent : Fin D → ℕ) : Fin D → ℕ :=
  fun d ↦ if d = parent then exponent parent + exponent child
    else if d = child then 0 else exponent d

/-- Exact instantaneous split transform on a finite moment state. -/
noncomputable def splitManyDemeMomentState {D K : ℕ}
    (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ
  | none => 1
  | some coordinate =>
      manyDemeMomentVectorTable K (fun oldCoordinate ↦ state (some oldCoordinate))
        (mergeSplitExponent parent child (fun d ↦ (coordinate d).val))

/-- A split resets the affine constant to its normalized value. -/
theorem splitManyDemeMomentState_none {D K : ℕ} (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    splitManyDemeMomentState parent child state none = 1 :=
  rfl

/-- A split preserves the rectangular degree-zero padding coordinate. -/
theorem splitManyDemeMomentState_zeroCoordinate {D K : ℕ} (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    splitManyDemeMomentState parent child state (some (fun _ ↦ 0)) =
      state (some (fun _ ↦ 0)) := by
  simp [splitManyDemeMomentState, manyDemeMomentVectorTable, mergeSplitExponent]

/-- An exact instruction is either continuous propagation or an instantaneous split. -/
inductive ManyDemeMomentInstruction (D K : ℕ) where
  | evolve (epoch : ManyDemeMomentEpoch D K)
  | split (parent child : Fin D)

/-- Execute an arbitrary finite sequence of exact demographic moment instructions. -/
noncomputable def propagateManyDemeMomentInstructions {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K))
    (initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ :=
  instructions.foldl (fun state instruction ↦ match instruction with
    | .evolve epoch => epoch.propagator.mulVec state
    | .split parent child => splitManyDemeMomentState parent child state) initial

/-- At a common ancestor all deme frequencies coincide, so a mixed moment depends only on
the total exponent. -/
noncomputable def commonAncestorManyDemeMomentState {D K : ℕ}
    (ancestralMoment : ℕ → ℝ) : AffineManyDemeMomentCoordinate D K → ℝ
  | none => 1
  | some coordinate =>
      if 0 < coordinate.degree ∧ coordinate.degree ≤ K then
        ancestralMoment coordinate.degree
      else 0

/-- Embed a bivariate train-target exponent into the full deme index without enumerating a
full sample-count cell. -/
def pairExponent {D : ℕ} (train target : Fin D) (i j : ℕ) : Fin D → ℕ :=
  if train = target then fun d ↦ if d = train then i + j else 0
  else fun d ↦ if d = train then i else if d = target then j else 0

/-- Exponent selecting one marginal moment in one deme.  It lives beside `pairExponent` so
all consumers use the same coordinate embedding. -/
def oneDemeExponent {D : ℕ} (deme : Fin D) (degree : ℕ) : Fin D → ℕ :=
  fun other ↦ if other = deme then degree else 0

private theorem sum_oneDemeExponent {D : ℕ} (deme : Fin D) (degree : ℕ) :
    ∑ d, oneDemeExponent deme degree d = degree := by
  classical
  simp [oneDemeExponent]

private theorem sum_pairExponent {D : ℕ} (first second : Fin D) (i j : ℕ) :
    ∑ d, pairExponent first second i j d = i + j := by
  classical
  by_cases hsame : first = second
  · subst second
    simp [pairExponent]
  · simp only [pairExponent, if_neg hsame]
    calc
      (∑ d, if d = first then i else if d = second then j else 0) =
          (∑ d, if d = first then i else 0) +
            ∑ d, if d = second then j else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hfirst : d = first
        · subst d
          simp [hsame]
        · simp [hfirst]
      _ = i + j := by simp

private theorem oneDemeExponent_lt_three {D : ℕ} (deme : Fin D) (degree : ℕ)
    (hdegree : degree < 3) : ∀ d, oneDemeExponent deme degree d < 3 := by
  intro d
  simp only [oneDemeExponent]
  split <;> omega

private theorem pairExponent_one_one_lt_three {D : ℕ} (first second : Fin D) :
    ∀ d, pairExponent first second 1 1 d < 3 := by
  intro d
  by_cases hsame : first = second
  · subst second
    by_cases hd : d = first <;> simp [pairExponent, hd]
  · by_cases hfirst : d = first
    · simp [pairExponent, hsame, hfirst]
    · by_cases hsecond : d = second
      · simp [pairExponent, hsame, hfirst, hsecond]
      · simp [pairExponent, hsame, hfirst, hsecond]

private theorem commonAncestorManyDemeMomentState_vectorTable
    {D : ℕ} (ancestralMoment : ℕ → ℝ) (exponent : Fin D → ℕ)
    (hrect : ∀ d, exponent d < 3) (hdegree_pos : 0 < ∑ d, exponent d)
    (hdegree_le : ∑ d, exponent d ≤ 2) :
    manyDemeMomentVectorTable 2
        (fun coordinate ↦ commonAncestorManyDemeMomentState ancestralMoment (some coordinate))
        exponent = ancestralMoment (∑ d, exponent d) := by
  simp [manyDemeMomentVectorTable, hrect, commonAncestorManyDemeMomentState,
    ManyDemeMomentCoordinate.degree, hdegree_pos, hdegree_le]

/-- Pairwise allelic divergence read directly from a full mixed-moment table.

This is the linear projection used by both the finite ascertainment system and the `H`
coordinate of the two-locus system.  Naming it at the generator layer avoids duplicating the
same three-term expression in the epoch and history intertwining proofs. -/
noncomputable def momentPairDivergence {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (first second : Fin D) : ℝ :=
  moment (oneDemeExponent first 1) + moment (oneDemeExponent second 1) -
    2 * moment (pairExponent first second 1 1)

private theorem decrement_oneDemeExponent_one {D : ℕ} (deme : Fin D) :
    decrementExponent (oneDemeExponent deme 1) deme = fun _ ↦ 0 := by
  funext other
  simp only [decrementExponent, oneDemeExponent]
  split_ifs <;> simp_all

private theorem decrement_oneDemeExponent_two {D : ℕ} (deme : Fin D) :
    decrementExponent (oneDemeExponent deme 2) deme = oneDemeExponent deme 1 := by
  funext other
  simp only [decrementExponent, oneDemeExponent]
  split_ifs <;> simp_all

private theorem decrement_pairExponent_left {D : ℕ} (first second : Fin D)
    (hne : first ≠ second) :
    decrementExponent (pairExponent first second 1 1) first =
      oneDemeExponent second 1 := by
  funext other
  simp only [decrementExponent, pairExponent, oneDemeExponent]
  split_ifs <;> simp_all

private theorem decrement_pairExponent_right {D : ℕ} (first second : Fin D)
    (hne : first ≠ second) :
    decrementExponent (pairExponent first second 1 1) second =
      oneDemeExponent first 1 := by
  funext other
  simp only [decrementExponent, pairExponent, oneDemeExponent]
  split_ifs <;> simp_all

private theorem migrate_oneDemeExponent_weighted {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ) (source target : Fin D) :
    rates.migration source target *
        (moment (migrateExponent (oneDemeExponent source 1) source target) -
          moment (oneDemeExponent source 1)) =
      rates.migration source target *
        (moment (oneDemeExponent target 1) - moment (oneDemeExponent source 1)) := by
  by_cases hsame : source = target
  · subst target
    simp [rates.migration_self]
  · congr 2
    apply congrArg moment
    funext deme
    simp only [migrateExponent, oneDemeExponent]
    split_ifs <;> simp_all

private theorem migrate_pairExponent_left_weighted {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ) (first second target : Fin D)
    (hne : first ≠ second) :
    rates.migration first target *
        (moment (migrateExponent (pairExponent first second 1 1) first target) -
          moment (pairExponent first second 1 1)) =
      rates.migration first target *
        (moment (pairExponent target second 1 1) -
          moment (pairExponent first second 1 1)) := by
  by_cases hself : first = target
  · subst target
    simp [rates.migration_self]
  · congr 2
    apply congrArg moment
    funext deme
    simp only [migrateExponent, pairExponent]
    split_ifs <;> simp_all

private theorem migrate_pairExponent_right_weighted {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ) (first second target : Fin D)
    (hne : first ≠ second) :
    rates.migration second target *
        (moment (migrateExponent (pairExponent first second 1 1) second target) -
          moment (pairExponent first second 1 1)) =
      rates.migration second target *
        (moment (pairExponent first target 1 1) -
          moment (pairExponent first second 1 1)) := by
  by_cases hself : second = target
  · subst target
    simp [rates.migration_self]
  · by_cases htargetFirst : target = first
    · subst target
      congr 2
      apply congrArg moment
      funext deme
      simp only [migrateExponent, pairExponent]
      split_ifs <;> simp_all
    · congr 2
      apply congrArg moment
      funext deme
      have hreverse : second ≠ first := fun h ↦ hne h.symm
      simp only [migrateExponent, pairExponent]
      (split_ifs <;> simp_all)

private theorem migrate_oneDemeExponent_two_weighted {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ) (source target : Fin D) :
    rates.migration source target * 2 *
        (moment (migrateExponent (oneDemeExponent source 2) source target) -
          moment (oneDemeExponent source 2)) =
      rates.migration source target * 2 *
        (moment (pairExponent source target 1 1) -
          moment (oneDemeExponent source 2)) := by
  by_cases hself : source = target
  · subst target
    simp [rates.migration_self]
  · congr 2
    apply congrArg moment
    funext deme
    simp only [migrateExponent, pairExponent, oneDemeExponent]
    split_ifs <;> simp_all

/-- The arbitrary-deme one-locus generator projects exactly to the homogeneous affine
pair-divergence generator when forward and backward mutation rates agree.

The diagonal branch contains coalescence and two copies of lineage migration; the
off-diagonal branch contains one migration sum for each lineage.  In both branches the total
mutation coordinate is `forward + backward`, exactly the convention consumed by the
two-locus `H` row.  The degree-zero moment is retained explicitly, so this identity applies
both to normalized probability moments and to every column of the augmented generator
matrix.  It is not a closure or equilibrium calculation. -/
theorem manyDemeMomentGenerator_pairDivergence_affine {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ)
    (hsymmetric : ∀ deme, rates.backwardMutation deme = rates.forwardMutation deme)
    (first second : Fin D) :
    manyDemeMomentGenerator rates moment (oneDemeExponent first 1) +
        manyDemeMomentGenerator rates moment (oneDemeExponent second 1) -
        2 * manyDemeMomentGenerator rates moment (pairExponent first second 1 1) =
      symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration
        (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme)
        (momentPairDivergence moment) (moment (fun _ ↦ 0)) first second := by
  classical
  have hsingle (deme : Fin D) :
      manyDemeMomentGenerator rates moment (oneDemeExponent deme 1) =
        (∑ target, rates.migration deme target *
          (moment (oneDemeExponent target 1) - moment (oneDemeExponent deme 1))) +
        rates.forwardMutation deme *
            (moment (fun _ ↦ 0) - moment (oneDemeExponent deme 1)) -
          rates.backwardMutation deme * moment (oneDemeExponent deme 1) := by
    unfold manyDemeMomentGenerator
    have hcoal :
        (∑ d, rates.coalescence d *
          (((oneDemeExponent deme 1 d) * (oneDemeExponent deme 1 d - 1) : ℕ) : ℝ) / 2 *
          (moment (decrementExponent (oneDemeExponent deme 1) d) -
            moment (oneDemeExponent deme 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      by_cases hd : d = deme <;> simp [oneDemeExponent, hd]
    have hmigration :
        (∑ src, ∑ target, rates.migration src target * oneDemeExponent deme 1 src *
          (moment (migrateExponent (oneDemeExponent deme 1) src target) -
            moment (oneDemeExponent deme 1))) =
          ∑ target, rates.migration deme target *
            (moment (oneDemeExponent target 1) - moment (oneDemeExponent deme 1)) := by
      rw [Finset.sum_eq_single deme]
      · apply Finset.sum_congr rfl
        intro target _
        simpa [oneDemeExponent] using
          migrate_oneDemeExponent_weighted rates moment deme target
      · intro source _ hsource
        simp [oneDemeExponent, hsource]
      · simp
    have hmutation :
        (∑ d, (rates.forwardMutation d * oneDemeExponent deme 1 d *
              (moment (decrementExponent (oneDemeExponent deme 1) d) -
                moment (oneDemeExponent deme 1)) -
            rates.backwardMutation d * oneDemeExponent deme 1 d *
              moment (oneDemeExponent deme 1))) =
          rates.forwardMutation deme *
              (moment (fun _ ↦ 0) - moment (oneDemeExponent deme 1)) -
            rates.backwardMutation deme * moment (oneDemeExponent deme 1) := by
      rw [Finset.sum_eq_single deme]
      · rw [decrement_oneDemeExponent_one]
        simp [oneDemeExponent]
      · intro d _ hd
        simp [oneDemeExponent, hd]
      · simp
    rw [hcoal, hmigration, hmutation]
    ring
  by_cases hsame : first = second
  · subst second
    have hpairSelf : pairExponent first first 1 1 = oneDemeExponent first 2 := by
      funext d
      simp [pairExponent, oneDemeExponent]
    have hpairComm (target : Fin D) :
        pairExponent target first 1 1 = pairExponent first target 1 1 := by
      funext d
      by_cases htarget : target = first
      · simp [pairExponent, htarget]
      · by_cases hdTarget : d = target <;> by_cases hdFirst : d = first <;>
          simp [pairExponent, htarget, hdTarget, hdFirst] <;> aesop
    have hdouble :
        manyDemeMomentGenerator rates moment (oneDemeExponent first 2) =
          rates.coalescence first *
              (moment (oneDemeExponent first 1) - moment (oneDemeExponent first 2)) +
            (∑ target, rates.migration first target * 2 *
              (moment (pairExponent first target 1 1) -
                moment (oneDemeExponent first 2))) +
            rates.forwardMutation first * 2 *
              (moment (oneDemeExponent first 1) - moment (oneDemeExponent first 2)) -
            rates.backwardMutation first * 2 * moment (oneDemeExponent first 2) := by
      unfold manyDemeMomentGenerator
      have hcoal :
          (∑ d, rates.coalescence d *
            (((oneDemeExponent first 2 d) * (oneDemeExponent first 2 d - 1) : ℕ) : ℝ) /
              2 *
            (moment (decrementExponent (oneDemeExponent first 2) d) -
              moment (oneDemeExponent first 2))) =
            rates.coalescence first *
              (moment (oneDemeExponent first 1) - moment (oneDemeExponent first 2)) := by
        rw [Finset.sum_eq_single first]
        · rw [decrement_oneDemeExponent_two]
          norm_num [oneDemeExponent]
        · intro d _ hd
          simp [oneDemeExponent, hd]
        · simp
      have hmigration :
          (∑ src, ∑ target, rates.migration src target * oneDemeExponent first 2 src *
            (moment (migrateExponent (oneDemeExponent first 2) src target) -
              moment (oneDemeExponent first 2))) =
            ∑ target, rates.migration first target * 2 *
              (moment (pairExponent first target 1 1) -
                moment (oneDemeExponent first 2)) := by
        rw [Finset.sum_eq_single first]
        · apply Finset.sum_congr rfl
          intro target _
          simpa [oneDemeExponent] using
            migrate_oneDemeExponent_two_weighted rates moment first target
        · intro source _ hsource
          simp [oneDemeExponent, hsource]
        · simp
      have hmutation :
          (∑ d, (rates.forwardMutation d * oneDemeExponent first 2 d *
                (moment (decrementExponent (oneDemeExponent first 2) d) -
                  moment (oneDemeExponent first 2)) -
              rates.backwardMutation d * oneDemeExponent first 2 d *
                moment (oneDemeExponent first 2))) =
            rates.forwardMutation first * 2 *
                (moment (oneDemeExponent first 1) - moment (oneDemeExponent first 2)) -
              rates.backwardMutation first * 2 * moment (oneDemeExponent first 2) := by
        rw [Finset.sum_eq_single first]
        · rw [decrement_oneDemeExponent_two]
          norm_num [oneDemeExponent]
        · intro d _ hd
          simp [oneDemeExponent, hd]
        · simp
      rw [hcoal, hmigration, hmutation]
      abel
    have hmigrationIdentity :
        (∑ target, rates.migration first target *
            (moment (oneDemeExponent target 1) - moment (oneDemeExponent first 1))) +
          (∑ target, rates.migration first target *
            (moment (oneDemeExponent target 1) - moment (oneDemeExponent first 1))) -
          2 * (∑ target, rates.migration first target * 2 *
            (moment (pairExponent first target 1 1) -
              moment (oneDemeExponent first 2))) =
        (∑ target, rates.migration first target *
            ((moment (oneDemeExponent target 1) + moment (oneDemeExponent first 1) -
                2 * moment (pairExponent first target 1 1)) -
              (2 * moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) +
          (∑ target, rates.migration first target *
            ((moment (oneDemeExponent first 1) + moment (oneDemeExponent target 1) -
                2 * moment (pairExponent first target 1 1)) -
              (2 * moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro target _
      ring
    have hdivergenceSums :
        (∑ target, rates.migration first target *
            ((moment (oneDemeExponent target 1) + moment (oneDemeExponent first 1) -
                2 * moment (pairExponent first target 1 1)) -
              (2 * moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) +
          (∑ target, rates.migration first target *
            ((moment (oneDemeExponent first 1) + moment (oneDemeExponent target 1) -
                2 * moment (pairExponent first target 1 1)) -
              (2 * moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) =
        (∑ target, rates.migration first target *
            ((moment (oneDemeExponent target 1) + moment (oneDemeExponent first 1) -
                2 * moment (pairExponent first target 1 1)) -
              (moment (oneDemeExponent first 1) + moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) +
          (∑ target, rates.migration first target *
            ((moment (oneDemeExponent first 1) + moment (oneDemeExponent target 1) -
                2 * moment (pairExponent first target 1 1)) -
              (moment (oneDemeExponent first 1) + moment (oneDemeExponent first 1) -
                2 * moment (oneDemeExponent first 2)))) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro target _ <;> ring
    rw [hdivergenceSums] at hmigrationIdentity
    rw [hpairSelf, hsingle first, hdouble]
    simp only [symmetricPairDivergenceAffineDerivative, if_pos, momentPairDivergence]
    rw [hsymmetric first]
    simp [hpairSelf]
    simp_rw [hpairComm]
    linear_combination hmigrationIdentity
  · have hreverse : second ≠ first := fun h ↦ hsame h.symm
    have hpair :
        manyDemeMomentGenerator rates moment (pairExponent first second 1 1) =
          (∑ target, rates.migration first target *
              (moment (pairExponent target second 1 1) -
                moment (pairExponent first second 1 1))) +
            (∑ target, rates.migration second target *
              (moment (pairExponent first target 1 1) -
                moment (pairExponent first second 1 1))) +
            rates.forwardMutation first *
              (moment (oneDemeExponent second 1) -
                moment (pairExponent first second 1 1)) -
            rates.backwardMutation first * moment (pairExponent first second 1 1) +
            (rates.forwardMutation second *
              (moment (oneDemeExponent first 1) -
                moment (pairExponent first second 1 1)) -
            rates.backwardMutation second * moment (pairExponent first second 1 1)) := by
      unfold manyDemeMomentGenerator
      have hcoal :
          (∑ d, rates.coalescence d *
            (((pairExponent first second 1 1 d) *
              (pairExponent first second 1 1 d - 1) : ℕ) : ℝ) / 2 *
            (moment (decrementExponent (pairExponent first second 1 1) d) -
              moment (pairExponent first second 1 1))) = 0 := by
        apply Finset.sum_eq_zero
        intro d _
        by_cases hdFirst : d = first
        · subst d
          simp [pairExponent, hsame]
        · by_cases hdSecond : d = second
          · subst d
            simp [pairExponent, hsame, hreverse]
          · simp [pairExponent, hsame, hdFirst, hdSecond]
      let firstRow := ∑ target, rates.migration first target *
        (moment (pairExponent target second 1 1) -
          moment (pairExponent first second 1 1))
      let secondRow := ∑ target, rates.migration second target *
        (moment (pairExponent first target 1 1) -
          moment (pairExponent first second 1 1))
      have hmigrationRow (source : Fin D) :
          (∑ target, rates.migration source target *
            pairExponent first second 1 1 source *
            (moment (migrateExponent (pairExponent first second 1 1) source target) -
              moment (pairExponent first second 1 1))) =
            if source = first then firstRow else if source = second then secondRow else 0 := by
        by_cases hsourceFirst : source = first
        · subst source
          simp only [if_pos]
          apply Finset.sum_congr rfl
          intro target _
          simpa [firstRow, pairExponent, hsame] using
            migrate_pairExponent_left_weighted rates moment first second target hsame
        · by_cases hsourceSecond : source = second
          · subst source
            simp only [hreverse, if_false, if_pos]
            apply Finset.sum_congr rfl
            intro target _
            simpa [secondRow, pairExponent, hsame, hreverse] using
              migrate_pairExponent_right_weighted rates moment first second target hsame
          · simp [pairExponent, hsame, hsourceFirst, hsourceSecond]
      have hmigration :
          (∑ source, ∑ target, rates.migration source target *
            pairExponent first second 1 1 source *
            (moment (migrateExponent (pairExponent first second 1 1) source target) -
              moment (pairExponent first second 1 1))) = firstRow + secondRow := by
        simp_rw [hmigrationRow]
        have hsplit (source : Fin D) :
            (if source = first then firstRow else if source = second then secondRow else 0) =
              (if source = first then firstRow else 0) +
                (if source = second then secondRow else 0) := by
          by_cases hsourceFirst : source = first
          · have hsourceSecond : source ≠ second := fun h ↦ hsame (hsourceFirst.symm.trans h)
            rw [if_pos hsourceFirst, if_pos hsourceFirst, if_neg hsourceSecond]
            ring
          · by_cases hsourceSecond : source = second
            · have hsecondFirst : second ≠ first := hreverse
              rw [if_neg hsourceFirst, if_pos hsourceSecond]
              have hnot : ¬source = first := hsourceFirst
              rw [if_neg hnot]
              ring
            · rw [if_neg hsourceFirst, if_neg hsourceSecond, if_neg hsourceFirst]
              ring
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      let firstMutation := rates.forwardMutation first *
          (moment (oneDemeExponent second 1) -
            moment (pairExponent first second 1 1)) -
        rates.backwardMutation first * moment (pairExponent first second 1 1)
      let secondMutation := rates.forwardMutation second *
          (moment (oneDemeExponent first 1) -
            moment (pairExponent first second 1 1)) -
        rates.backwardMutation second * moment (pairExponent first second 1 1)
      have hmutationRow (d : Fin D) :
          rates.forwardMutation d * pairExponent first second 1 1 d *
              (moment (decrementExponent (pairExponent first second 1 1) d) -
                moment (pairExponent first second 1 1)) -
            rates.backwardMutation d * pairExponent first second 1 1 d *
              moment (pairExponent first second 1 1) =
            if d = first then firstMutation else if d = second then secondMutation else 0 := by
        by_cases hdFirst : d = first
        · subst d
          rw [decrement_pairExponent_left first second hsame]
          simp [pairExponent, hsame, firstMutation]
        · by_cases hdSecond : d = second
          · subst d
            rw [decrement_pairExponent_right first second hsame]
            simp [pairExponent, hsame, hreverse, secondMutation]
          · simp [pairExponent, hsame, hdFirst, hdSecond]
      have hmutation :
          (∑ d, (rates.forwardMutation d * pairExponent first second 1 1 d *
                (moment (decrementExponent (pairExponent first second 1 1) d) -
                  moment (pairExponent first second 1 1)) -
              rates.backwardMutation d * pairExponent first second 1 1 d *
                moment (pairExponent first second 1 1))) =
            firstMutation + secondMutation := by
        simp_rw [hmutationRow]
        have hsplit (d : Fin D) :
            (if d = first then firstMutation else if d = second then secondMutation else 0) =
              (if d = first then firstMutation else 0) +
                (if d = second then secondMutation else 0) := by
          by_cases hdFirst : d = first
          · have hdSecond : d ≠ second := fun h ↦ hsame (hdFirst.symm.trans h)
            rw [if_pos hdFirst, if_pos hdFirst, if_neg hdSecond]
            ring
          · by_cases hdSecond : d = second
            · have hsecondFirst : second ≠ first := hreverse
              rw [if_neg hdFirst, if_pos hdSecond]
              have hnot : ¬d = first := hdFirst
              rw [if_neg hnot]
              ring
            · rw [if_neg hdFirst, if_neg hdSecond, if_neg hdFirst]
              ring
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      rw [hcoal, hmigration, hmutation]
      simp only [firstRow, secondRow, firstMutation, secondMutation]
      abel
    have hmigrationFirst :
        (∑ target, rates.migration first target *
            (moment (oneDemeExponent target 1) - moment (oneDemeExponent first 1))) -
          2 * (∑ target, rates.migration first target *
            (moment (pairExponent target second 1 1) -
              moment (pairExponent first second 1 1))) =
        ∑ target, rates.migration first target *
          ((moment (oneDemeExponent target 1) + moment (oneDemeExponent second 1) -
              2 * moment (pairExponent target second 1 1)) -
            (moment (oneDemeExponent first 1) + moment (oneDemeExponent second 1) -
              2 * moment (pairExponent first second 1 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro target _
      ring
    have hmigrationSecond :
        (∑ target, rates.migration second target *
            (moment (oneDemeExponent target 1) - moment (oneDemeExponent second 1))) -
          2 * (∑ target, rates.migration second target *
            (moment (pairExponent first target 1 1) -
              moment (pairExponent first second 1 1))) =
        ∑ target, rates.migration second target *
          ((moment (oneDemeExponent first 1) + moment (oneDemeExponent target 1) -
              2 * moment (pairExponent first target 1 1)) -
            (moment (oneDemeExponent first 1) + moment (oneDemeExponent second 1) -
              2 * moment (pairExponent first second 1 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro target _
      ring
    rw [hsingle first, hsingle second, hpair]
    simp only [symmetricPairDivergenceAffineDerivative, if_neg hsame, zero_add,
      momentPairDivergence]
    rw [hsymmetric first, hsymmetric second]
    linear_combination hmigrationFirst + hmigrationSecond

/-- The probability-law specialization of
`manyDemeMomentGenerator_pairDivergence_affine`: normalized moment tables have affine
coordinate one and therefore obey the shared closed divergence law. -/
theorem manyDemeMomentGenerator_pairDivergence {D : ℕ} (rates : ManyDemeRates D)
    (moment : (Fin D → ℕ) → ℝ)
    (hnormalized : moment (fun _ ↦ 0) = 1)
    (hsymmetric : ∀ deme, rates.backwardMutation deme = rates.forwardMutation deme)
    (first second : Fin D) :
    manyDemeMomentGenerator rates moment (oneDemeExponent first 1) +
        manyDemeMomentGenerator rates moment (oneDemeExponent second 1) -
        2 * manyDemeMomentGenerator rates moment (pairExponent first second 1 1) =
      symmetricPairDivergenceDerivative rates.coalescence rates.migration
        (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme)
        (momentPairDivergence moment) first second := by
  rw [manyDemeMomentGenerator_pairDivergence_affine rates moment hsymmetric first second,
    symmetricPairDivergenceDerivative, hnormalized]

/-! ### Finite affine projection onto pairwise divergence -/

/-- Ordered deme pairs carrying the closed allelic-divergence subsystem. -/
abbrev PairDivergenceCoordinate (D : ℕ) := Fin D × Fin D

/-- Constant-augmented carrier for the closed pair-divergence subsystem. -/
abbrev AffinePairDivergenceCoordinate (D : ℕ) := Option (PairDivergenceCoordinate D)

/-- Read an affine pair-divergence vector as its pair-indexed table. -/
def pairDivergenceVectorTable {D : ℕ}
    (state : AffinePairDivergenceCoordinate D → ℝ) (first second : Fin D) : ℝ :=
  state (some (first, second))

/-- Linear operator of the constant-augmented closed pair-divergence system. -/
noncomputable def pairDivergenceGeneratorLinearMap {D : ℕ}
    (coalescence : Fin D → ℝ) (migration : Fin D → Fin D → ℝ)
    (mutation : Fin D → ℝ) :
    (AffinePairDivergenceCoordinate D → ℝ) →ₗ[ℝ]
      (AffinePairDivergenceCoordinate D → ℝ) where
  toFun state coordinate := match coordinate with
    | none => 0
    | some (first, second) =>
        symmetricPairDivergenceAffineDerivative coalescence migration mutation
          (pairDivergenceVectorTable state) (state none) first second
  map_add' := by
    intro left right
    funext coordinate
    cases coordinate with
    | none => simp
    | some pair =>
        rcases pair with ⟨first, second⟩
        have hfirst :
            (∑ target, migration first target *
              (pairDivergenceVectorTable (left + right) target second -
                pairDivergenceVectorTable (left + right) first second)) =
              (∑ target, migration first target *
                (pairDivergenceVectorTable left target second -
                  pairDivergenceVectorTable left first second)) +
              (∑ target, migration first target *
                (pairDivergenceVectorTable right target second -
                  pairDivergenceVectorTable right first second)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro target _
          simp [pairDivergenceVectorTable]
          ring
        have hsecond :
            (∑ target, migration second target *
              (pairDivergenceVectorTable (left + right) first target -
                pairDivergenceVectorTable (left + right) first second)) =
              (∑ target, migration second target *
                (pairDivergenceVectorTable left first target -
                  pairDivergenceVectorTable left first second)) +
              (∑ target, migration second target *
                (pairDivergenceVectorTable right first target -
                  pairDivergenceVectorTable right first second)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro target _
          simp [pairDivergenceVectorTable]
          ring
        simp only [symmetricPairDivergenceAffineDerivative]
        rw [hfirst, hsecond]
        simp only [pairDivergenceVectorTable, Pi.add_apply]
        by_cases hsame : first = second <;> simp [hsame] <;> ring
  map_smul' := by
    intro scalar state
    funext coordinate
    cases coordinate with
    | none => simp
    | some pair =>
        rcases pair with ⟨first, second⟩
        have hfirst :
            (∑ target, migration first target *
              (pairDivergenceVectorTable (scalar • state) target second -
                pairDivergenceVectorTable (scalar • state) first second)) =
              scalar * ∑ target, migration first target *
                (pairDivergenceVectorTable state target second -
                  pairDivergenceVectorTable state first second) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro target _
          simp [pairDivergenceVectorTable]
          ring
        have hsecond :
            (∑ target, migration second target *
              (pairDivergenceVectorTable (scalar • state) first target -
                pairDivergenceVectorTable (scalar • state) first second)) =
              scalar * ∑ target, migration second target *
                (pairDivergenceVectorTable state first target -
                  pairDivergenceVectorTable state first second) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro target _
          simp [pairDivergenceVectorTable]
          ring
        simp only [symmetricPairDivergenceAffineDerivative]
        rw [hfirst, hsecond]
        simp only [pairDivergenceVectorTable, Pi.smul_apply, smul_eq_mul]
        by_cases hsame : first = second <;> simp [hsame] <;> ring

/-- Constant-augmented matrix of the closed pair-divergence generator. -/
noncomputable def augmentedPairDivergenceGenerator {D : ℕ}
    (coalescence : Fin D → ℝ) (migration : Fin D → Fin D → ℝ)
    (mutation : Fin D → ℝ) :
    Matrix (AffinePairDivergenceCoordinate D) (AffinePairDivergenceCoordinate D) ℝ :=
  LinearMap.toMatrix' (pairDivergenceGeneratorLinearMap coalescence migration mutation)

/-- Matrix application is definitionally the closed affine divergence derivative. -/
theorem augmentedPairDivergenceGenerator_mulVec {D : ℕ}
    (coalescence : Fin D → ℝ) (migration : Fin D → Fin D → ℝ)
    (mutation : Fin D → ℝ) (state : AffinePairDivergenceCoordinate D → ℝ) :
    (augmentedPairDivergenceGenerator coalescence migration mutation).mulVec state =
      pairDivergenceGeneratorLinearMap coalescence migration mutation state := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Rectangular linear projection from degree-two mixed moments to the affine pairwise
divergence subsystem.  Its coefficient on a moment basis column is exactly the defining
three-term divergence functional; the affine constant passes through unchanged. -/
noncomputable def manyDemePairDivergenceProjection (D : ℕ) :
    Matrix (AffinePairDivergenceCoordinate D) (AffineManyDemeMomentCoordinate D 2) ℝ
  | none, none => 1
  | none, some column => manyDemeMomentBasisTable 2 column (fun _ ↦ 0)
  | some _, none => 0
  | some (first, second), some column =>
      momentPairDivergence (manyDemeMomentBasisTable 2 column) first second

/-- The rectangular matrix above evaluates to the advertised three-term divergence of the
finite moment vector. -/
theorem manyDemePairDivergenceProjection_mulVec {D : ℕ}
    (state : AffineManyDemeMomentCoordinate D 2 → ℝ) :
    (manyDemePairDivergenceProjection D).mulVec state =
      fun coordinate ↦ match coordinate with
        | none => state none +
            manyDemeMomentVectorTable 2 (fun column ↦ state (some column)) (fun _ ↦ 0)
        | some (first, second) =>
            momentPairDivergence
              (manyDemeMomentVectorTable 2 (fun column ↦ state (some column))) first second := by
  funext coordinate
  cases coordinate with
  | none =>
      simp only [Matrix.mulVec, dotProduct, manyDemePairDivergenceProjection]
      rw [Fintype.sum_option]
      simp [manyDemeMomentBasisTable, manyDemeMomentVectorTable]
  | some pair =>
      rcases pair with ⟨first, second⟩
      simp only [Matrix.mulVec, dotProduct, manyDemePairDivergenceProjection,
        momentPairDivergence]
      rw [Fintype.sum_option]
      simp only [zero_mul, zero_add]
      have hvector (exponent : Fin D → ℕ) (hbound : ∀ d, exponent d < 3) :
          (∑ column, manyDemeMomentBasisTable 2 column exponent * state (some column)) =
            manyDemeMomentVectorTable 2 (fun column ↦ state (some column)) exponent := by
        simp [manyDemeMomentBasisTable, manyDemeMomentVectorTable, hbound]
      have hfirst : ∀ d, oneDemeExponent first 1 d < 3 := by
        intro d
        by_cases hd : d = first <;> simp [oneDemeExponent, hd]
      have hsecond : ∀ d, oneDemeExponent second 1 d < 3 := by
        intro d
        by_cases hd : d = second <;> simp [oneDemeExponent, hd]
      have hpair : ∀ d, pairExponent first second 1 1 d < 3 := by
        intro d
        by_cases hsame : first = second
        · subst second
          by_cases hd : d = first <;> simp [pairExponent, hd]
        · by_cases hfirstD : d = first <;> by_cases hsecondD : d = second <;>
            simp [pairExponent, hsame, hfirstD, hsecondD]
      calc
        _ = (∑ column, manyDemeMomentBasisTable 2 column
              (oneDemeExponent first 1) * state (some column)) +
            (∑ column, manyDemeMomentBasisTable 2 column
              (oneDemeExponent second 1) * state (some column)) -
            2 * (∑ column, manyDemeMomentBasisTable 2 column
              (pairExponent first second 1 1) * state (some column)) := by
          calc
            _ = ∑ column,
                (manyDemeMomentBasisTable 2 column (oneDemeExponent first 1) *
                    state (some column) +
                  manyDemeMomentBasisTable 2 column (oneDemeExponent second 1) *
                    state (some column) -
                  2 * (manyDemeMomentBasisTable 2 column
                    (pairExponent first second 1 1) * state (some column))) := by
                apply Finset.sum_congr rfl
                intro column _
                ring
            _ = _ := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by rw [hvector _ hfirst, hvector _ hsecond, hvector _ hpair]

/-- At the common ancestral boundary every ordered pair has the same divergence, namely the
within-population heterozygosity `2(E[p] - E[p²])`; the affine coordinate is normalized to
one. -/
theorem manyDemePairDivergenceProjection_commonAncestor {D : ℕ}
    (ancestralMoment : ℕ → ℝ) :
    (manyDemePairDivergenceProjection D).mulVec
        (commonAncestorManyDemeMomentState (K := 2) ancestralMoment) =
      fun coordinate ↦ match coordinate with
        | none => 1
        | some _ => 2 * (ancestralMoment 1 - ancestralMoment 2) := by
  rw [manyDemePairDivergenceProjection_mulVec]
  funext coordinate
  cases coordinate with
  | none =>
      simp [commonAncestorManyDemeMomentState, manyDemeMomentVectorTable,
        ManyDemeMomentCoordinate.degree]
  | some pair =>
      rcases pair with ⟨first, second⟩
      have hfirst := commonAncestorManyDemeMomentState_vectorTable ancestralMoment
        (oneDemeExponent first 1) (oneDemeExponent_lt_three first 1 (by omega))
        (by simp [sum_oneDemeExponent]) (by simp [sum_oneDemeExponent])
      have hsecond := commonAncestorManyDemeMomentState_vectorTable ancestralMoment
        (oneDemeExponent second 1) (oneDemeExponent_lt_three second 1 (by omega))
        (by simp [sum_oneDemeExponent]) (by simp [sum_oneDemeExponent])
      have hpair := commonAncestorManyDemeMomentState_vectorTable ancestralMoment
        (pairExponent first second 1 1) (pairExponent_one_one_lt_three first second)
        (by simp [sum_pairExponent]) (by simp [sum_pairExponent])
      simp only
      unfold momentPairDivergence
      rw [hfirst, hsecond, hpair]
      simp only [sum_oneDemeExponent, sum_pairExponent]
      ring

/-- Moment table represented by one column of the constant-augmented degree-`K` system. -/
noncomputable def manyDemeMomentAffineColumnTable {D K : ℕ}
    (column : AffineManyDemeMomentCoordinate D K) : (Fin D → ℕ) → ℝ :=
  match column with
  | none => manyDemeMomentConstantTable
  | some coordinate => manyDemeMomentBasisTable K coordinate

/-- Degree-zero coefficient represented by one affine moment column. -/
noncomputable def manyDemeMomentAffineColumnConstant {D K : ℕ}
    (column : AffineManyDemeMomentCoordinate D K) : ℝ :=
  manyDemeMomentAffineColumnTable column (fun _ ↦ 0)

private theorem manyDemeMomentGenerator_column_read {D K : ℕ}
    (rates : ManyDemeRates D) (column : AffineManyDemeMomentCoordinate D K)
    (exponent : Fin D → ℕ) (hbound : ∀ d, exponent d < K + 1)
    (hdegree : 0 < ∑ d, exponent d ∧ ∑ d, exponent d ≤ K) :
    manyDemeMomentVectorTable K
        (fun row ↦ augmentedManyDemeMomentGenerator rates K (some row) column) exponent =
      manyDemeMomentGenerator rates (manyDemeMomentAffineColumnTable column) exponent := by
  unfold manyDemeMomentVectorTable
  rw [dif_pos hbound]
  cases column with
  | none =>
      simp [augmentedManyDemeMomentGenerator, manyDemeMomentForcing,
        manyDemeMomentAffineColumnTable, ManyDemeMomentCoordinate.degree, hdegree]
  | some column =>
      simp [augmentedManyDemeMomentGenerator, manyDemeMomentDynamicsMatrix,
        manyDemeMomentAffineColumnTable, ManyDemeMomentCoordinate.degree, hdegree]

/-- Each column of the rectangular projection is the divergence of the corresponding affine
moment basis table. -/
theorem manyDemePairDivergenceProjection_apply {D : ℕ}
    (first second : Fin D) (column : AffineManyDemeMomentCoordinate D 2) :
    manyDemePairDivergenceProjection D (some (first, second)) column =
      momentPairDivergence (manyDemeMomentAffineColumnTable column) first second := by
  cases column with
  | none =>
      have hfirst : ¬∀ d, oneDemeExponent first 1 d = 0 := by
        intro h
        simpa [oneDemeExponent] using h first
      have hsecond : ¬∀ d, oneDemeExponent second 1 d = 0 := by
        intro h
        simpa [oneDemeExponent] using h second
      have hpair : ¬∀ d, pairExponent first second 1 1 d = 0 := by
        intro h
        have hvalue := h first
        by_cases hsame : first = second <;> simp [pairExponent, hsame] at hvalue
      simp [manyDemePairDivergenceProjection, manyDemeMomentAffineColumnTable,
        momentPairDivergence, manyDemeMomentConstantTable, hfirst, hsecond, hpair]
  | some column =>
      rfl

/-- The projection passes exactly the affine degree-zero column. -/
theorem manyDemePairDivergenceProjection_none {D : ℕ}
    (column : AffineManyDemeMomentCoordinate D 2) :
    manyDemePairDivergenceProjection D none column =
      manyDemeMomentAffineColumnConstant column := by
  cases column <;>
    simp [manyDemePairDivergenceProjection, manyDemeMomentAffineColumnConstant,
      manyDemeMomentAffineColumnTable, manyDemeMomentConstantTable]

/-- The degree-two one-locus affine generator intertwines with the closed pair-divergence
generator for every symmetric-biallelic arbitrary-deme rate matrix. -/
theorem manyDemePairDivergenceProjection_generator_intertwines {D : ℕ}
    (rates : ManyDemeRates D)
    (hsymmetric : ∀ deme, rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemePairDivergenceProjection D * augmentedManyDemeMomentGenerator rates 2 =
      augmentedPairDivergenceGenerator rates.coalescence rates.migration
        (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme) *
          manyDemePairDivergenceProjection D := by
  apply Matrix.ext
  intro row column
  change (manyDemePairDivergenceProjection D).mulVec
      (fun source ↦ augmentedManyDemeMomentGenerator rates 2 source column) row =
    (augmentedPairDivergenceGenerator rates.coalescence rates.migration
      (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme)).mulVec
        (fun target ↦ manyDemePairDivergenceProjection D target column) row
  rw [manyDemePairDivergenceProjection_mulVec,
    augmentedPairDivergenceGenerator_mulVec]
  cases row with
  | none =>
      cases column <;>
        simp [pairDivergenceGeneratorLinearMap, augmentedManyDemeMomentGenerator,
          manyDemeMomentVectorTable, manyDemeMomentDynamicsMatrix,
          manyDemeMomentForcing, ManyDemeMomentCoordinate.degree]
  | some pair =>
      rcases pair with ⟨first, second⟩
      have hfirstBound : ∀ d, oneDemeExponent first 1 d < 3 := by
        intro d
        by_cases hd : d = first <;> simp [oneDemeExponent, hd]
      have hsecondBound : ∀ d, oneDemeExponent second 1 d < 3 := by
        intro d
        by_cases hd : d = second <;> simp [oneDemeExponent, hd]
      have hpairBound : ∀ d, pairExponent first second 1 1 d < 3 := by
        intro d
        by_cases hsame : first = second
        · subst second
          by_cases hd : d = first <;> simp [pairExponent, hd]
        · by_cases hdFirst : d = first <;> by_cases hdSecond : d = second <;>
            simp [pairExponent, hsame, hdFirst, hdSecond]
      have hfirstDegree :
          0 < ∑ d, oneDemeExponent first 1 d ∧
            ∑ d, oneDemeExponent first 1 d ≤ 2 := by
        simp [oneDemeExponent]
      have hsecondDegree :
          0 < ∑ d, oneDemeExponent second 1 d ∧
            ∑ d, oneDemeExponent second 1 d ≤ 2 := by
        simp [oneDemeExponent]
      have hpairDegree :
          0 < ∑ d, pairExponent first second 1 1 d ∧
            ∑ d, pairExponent first second 1 1 d ≤ 2 := by
        by_cases hsame : first = second
        · subst second
          simp [pairExponent]
        · have hsum :
              (∑ d, if d = first then 1 else if d = second then 1 else 0) = 2 := by
            calc
              _ = (∑ d, if d = first then 1 else 0) +
                  ∑ d, if d = second then 1 else 0 := by
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro d _
                    by_cases hdFirst : d = first
                    · subst d
                      simp [hsame]
                    · by_cases hdSecond : d = second
                      · subst d
                        simp [hdFirst]
                      · simp [hdFirst, hdSecond]
              _ = 2 := by simp
          simp [pairExponent, hsame, hsum]
      simp only [momentPairDivergence, pairDivergenceGeneratorLinearMap]
      rw [manyDemeMomentGenerator_column_read rates column _ hfirstBound hfirstDegree,
        manyDemeMomentGenerator_column_read rates column _ hsecondBound hsecondDegree,
        manyDemeMomentGenerator_column_read rates column _ hpairBound hpairDegree]
      change _ = symmetricPairDivergenceAffineDerivative rates.coalescence rates.migration
        (fun deme ↦ rates.forwardMutation deme + rates.backwardMutation deme)
        (fun source target ↦ manyDemePairDivergenceProjection D
          (some (source, target)) column)
        (manyDemePairDivergenceProjection D none column) first second
      rw [manyDemePairDivergenceProjection_none]
      simp_rw [manyDemePairDivergenceProjection_apply]
      exact manyDemeMomentGenerator_pairDivergence_affine rates
        (manyDemeMomentAffineColumnTable column) hsymmetric first second

/-- Generator intertwining lifts to every exact one-locus epoch matrix exponential. -/
theorem manyDemePairDivergenceProjection_propagator_intertwines {D : ℕ}
    (epoch : ManyDemeMomentEpoch D 2)
    (hsymmetric : ∀ deme,
      epoch.rates.backwardMutation deme = epoch.rates.forwardMutation deme) :
    manyDemePairDivergenceProjection D * epoch.propagator =
      matrixExponential
          (augmentedPairDivergenceGenerator epoch.rates.coalescence epoch.rates.migration
            (fun deme ↦ epoch.rates.forwardMutation deme +
              epoch.rates.backwardMutation deme)) epoch.duration *
        manyDemePairDivergenceProjection D := by
  exact matrixExponential_intertwines _ _ _
    (manyDemePairDivergenceProjection_generator_intertwines epoch.rates hsymmetric)
    epoch.duration

/-- Pull one deme label back across a split. -/
def mergeSplitDemeLabel {D : ℕ} (parent child label : Fin D) : Fin D :=
  if label = child then parent else label

/-- The induced split action on the affine ordered-pair divergence subsystem. -/
def splitPairDivergenceState {D : ℕ} (parent child : Fin D)
    (state : AffinePairDivergenceCoordinate D → ℝ) :
    AffinePairDivergenceCoordinate D → ℝ
  | none => 1
  | some (first, second) =>
      state (some (mergeSplitDemeLabel parent child first,
        mergeSplitDemeLabel parent child second))

private theorem mergeSplitExponent_zero {D : ℕ} (parent child : Fin D) :
    mergeSplitExponent parent child (fun _ ↦ 0) = fun _ ↦ 0 := by
  funext d
  simp [mergeSplitExponent]

private theorem mergeSplitExponent_oneDeme {D : ℕ} (parent child deme : Fin D)
    (hne : parent ≠ child) :
    mergeSplitExponent parent child (oneDemeExponent deme 1) =
      oneDemeExponent (mergeSplitDemeLabel parent child deme) 1 := by
  funext d
  have hreverse : child ≠ parent := fun h ↦ hne h.symm
  by_cases hdParent : d = parent
  · subst d
    by_cases hdemeParent : deme = parent
    · subst deme
      simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hne, hreverse]
    · by_cases hdemeChild : deme = child
      · subst deme
        simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hne]
      · have hparentDeme : parent ≠ deme := fun h ↦ hdemeParent h.symm
        have hchildDeme : child ≠ deme := fun h ↦ hdemeChild h.symm
        simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hne, hreverse,
          hdemeChild, hparentDeme, hchildDeme]
  · by_cases hdChild : d = child
    · subst d
      by_cases hdemeChild : deme = child
      · subst deme
        simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hne]
      · have hchildDeme : child ≠ deme := fun h ↦ hdemeChild h.symm
        simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hreverse,
          hdemeChild, hchildDeme]
    · by_cases hdemeChild : deme = child
      · subst deme
        simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hne,
          hdParent, hdChild]
      · simp [mergeSplitExponent, oneDemeExponent, mergeSplitDemeLabel, hdParent,
          hdChild, hdemeChild]

private theorem pairExponent_eq_oneDeme_add {D : ℕ} (first second : Fin D) :
    pairExponent first second 1 1 =
      oneDemeExponent first 1 + oneDemeExponent second 1 := by
  funext d
  by_cases hsame : first = second
  · subst second
    by_cases hd : d = first <;> simp [pairExponent, oneDemeExponent, hd]
  · have hreverse : second ≠ first := fun h ↦ hsame h.symm
    by_cases hdFirst : d = first
    · subst d
      simp [pairExponent, oneDemeExponent, hsame, hreverse]
    · by_cases hdSecond : d = second
      · subst d
        simp [pairExponent, oneDemeExponent, hsame, hreverse]
      · simp [pairExponent, oneDemeExponent, hsame, hdFirst, hdSecond]

private theorem mergeSplitExponent_add {D : ℕ} (parent child : Fin D)
    (hne : parent ≠ child) (left right : Fin D → ℕ) :
    mergeSplitExponent parent child (left + right) =
      mergeSplitExponent parent child left + mergeSplitExponent parent child right := by
  funext d
  have hreverse : child ≠ parent := fun h ↦ hne h.symm
  by_cases hdParent : d = parent
  · subst d
    simp [mergeSplitExponent, hne] <;> omega
  · by_cases hdChild : d = child
    · subst d
      simp [mergeSplitExponent, hreverse]
    · simp [mergeSplitExponent, hdParent, hdChild]

private theorem mergeSplitExponent_pair {D : ℕ} (parent child first second : Fin D)
    (hne : parent ≠ child) :
    mergeSplitExponent parent child (pairExponent first second 1 1) =
      pairExponent (mergeSplitDemeLabel parent child first)
        (mergeSplitDemeLabel parent child second) 1 1 := by
  rw [pairExponent_eq_oneDeme_add, mergeSplitExponent_add parent child hne,
    mergeSplitExponent_oneDeme parent child first hne,
    mergeSplitExponent_oneDeme parent child second hne,
    pairExponent_eq_oneDeme_add]

/-- The exact marginal split transform commutes with the pair-divergence projection on the
reachable affine subspace: the explicit constant is one and the padded degree-zero
coordinate is zero. -/
theorem manyDemePairDivergenceProjection_split {D : ℕ} (parent child : Fin D)
    (hne : parent ≠ child)
    (state : AffineManyDemeMomentCoordinate D 2 → ℝ)
    (hzero : manyDemeMomentVectorTable 2 (fun coordinate ↦ state (some coordinate))
      (fun _ ↦ 0) = 0) :
    (manyDemePairDivergenceProjection D).mulVec
        (splitManyDemeMomentState parent child state) =
      splitPairDivergenceState parent child
        ((manyDemePairDivergenceProjection D).mulVec state) := by
  rw [manyDemePairDivergenceProjection_mulVec,
    manyDemePairDivergenceProjection_mulVec]
  funext coordinate
  cases coordinate with
  | none =>
      simp only [splitPairDivergenceState, splitManyDemeMomentState]
      rw [manyDemeMomentVectorTable]
      simp only [Nat.reduceAdd, Nat.reduceLT, forall_const, ↓reduceDIte]
      rw [mergeSplitExponent_zero parent child]
      rw [dif_pos (by intro; trivial), hzero]
      norm_num
  | some pair =>
      rcases pair with ⟨first, second⟩
      simp only [splitPairDivergenceState, momentPairDivergence]
      have hfirst : ∀ d, oneDemeExponent first 1 d < 3 := by
        intro d
        by_cases hd : d = first <;> simp [oneDemeExponent, hd]
      have hsecond : ∀ d, oneDemeExponent second 1 d < 3 := by
        intro d
        by_cases hd : d = second <;> simp [oneDemeExponent, hd]
      have hpair : ∀ d, pairExponent first second 1 1 d < 3 := by
        intro d
        by_cases hsame : first = second
        · subst second
          by_cases hd : d = first <;> simp [pairExponent, hd]
        · by_cases hdFirst : d = first <;> by_cases hdSecond : d = second <;>
            simp [pairExponent, hsame, hdFirst, hdSecond]
      simp only [splitManyDemeMomentState, manyDemeMomentVectorTable]
      rw [dif_pos hfirst, dif_pos hsecond, dif_pos hpair]
      rw [mergeSplitExponent_oneDeme parent child first hne,
        mergeSplitExponent_oneDeme parent child second hne,
        mergeSplitExponent_pair parent child first second hne]

/-- A many-deme mixed-moment oracle.  Implementations may be a sparse moment solver, the
published JSFS dynamic program, or an exact external demography constructor; consumers see
one typed mathematical object. -/
structure ManyDemeMomentLaw (D : ℕ) where
  mixedMoment : (Fin D → ℕ) → ℝ
  representingMeasure : Measure (Fin D → ℝ)
  probability : IsProbabilityMeasure representingMeasure
  supported_on_unit_cube : ∀ᵐ frequency ∂representingMeasure,
    ∀ d, frequency d ∈ Set.Icc (0 : ℝ) 1
  mixedMoment_spec : ∀ exponent,
    mixedMoment exponent =
      ∫ frequency, (∏ d, frequency d ^ exponent d) ∂representingMeasure
  normalized : mixedMoment (fun _ ↦ 0) = 1
  moment_nonneg : ∀ exponent, 0 ≤ mixedMoment exponent
  moment_le_one : ∀ exponent, mixedMoment exponent ≤ 1

/-- Exact pairwise projection of a full many-deme moment law. -/
noncomputable def ManyDemeMomentLaw.pairMoment {D : ℕ} (law : ManyDemeMomentLaw D)
    (train target : Fin D) (i j : ℕ) : ℝ :=
  law.mixedMoment (pairExponent train target i j)

/-- A linear-size train-versus-all representation: only bivariate projections needed by the
report are materialized.  Exactness is certified against a full moment oracle, but downstream
state is `O(D K²)` rather than the Cartesian product of all deme sample configurations. -/
structure TrainVsAllMomentProjection (D : ℕ) where
  fullLaw : ManyDemeMomentLaw D
  train : Fin D
  trainSampleSize : ℕ
  targetSampleSize : Fin D → ℕ

/-- Exact joint train-target sample-count law for one target projection. -/
noncomputable def TrainVsAllMomentProjection.jointSampleCount {D : ℕ}
    (projection : TrainVsAllMomentProjection D) (target : Fin D)
    (sourceCount targetCount : ℕ) : ℝ :=
  let ns := projection.trainSampleSize
  let nt := projection.targetSampleSize target
  if sourceCount ≤ ns ∧ targetCount ≤ nt then
    (Nat.choose ns sourceCount : ℝ) * (Nat.choose nt targetCount : ℝ) *
      (∑ a ∈ Finset.range (ns - sourceCount + 1),
        ∑ b ∈ Finset.range (nt - targetCount + 1),
          (Nat.choose (ns - sourceCount) a : ℝ) *
          (Nat.choose (nt - targetCount) b : ℝ) * (-1 : ℝ) ^ (a + b) *
          projection.fullLaw.pairMoment projection.train target
            (sourceCount + a) (targetCount + b))
  else 0

/-- Exact target spectrum conditional on a source count, in `O(D)` pairwise projections. -/
noncomputable def TrainVsAllMomentProjection.conditionalTargetSpectrum {D : ℕ}
    (projection : TrainVsAllMomentProjection D) (target : Fin D)
    (sourceCount targetCount : ℕ) : Option ℝ :=
  let denominator := ∑ j ∈ Finset.range (projection.targetSampleSize target + 1),
    projection.jointSampleCount target sourceCount j
  if 0 < denominator then
    some (projection.jointSampleCount target sourceCount targetCount / denominator)
  else none

/-- Exact erosion probability for every train-target pair. -/
noncomputable def TrainVsAllMomentProjection.targetErosion {D : ℕ}
    (projection : TrainVsAllMomentProjection D) (target : Fin D) : Option ℝ :=
  let ns := projection.trainSampleSize
  let nt := projection.targetSampleSize target
  targetErosionEvent (projection.jointSampleCount target) ns nt

/-- Pairwise coalescence times in raw generations. -/
structure PairwiseCoalescenceTimes (D : ℕ) where
  within : Fin D → ℝ
  between : Fin D → Fin D → ℝ
  within_pos : ∀ d, 0 < within d
  between_pos : ∀ i j, 0 < between i j
  between_symmetric : ∀ i j, between i j = between j i
  between_self : ∀ i, between i i = within i

/-- A typed joint spectrum rather than an unlabelled array of reals. -/
structure JointSampleSpectrum (D : ℕ) where
  sampleSize : Fin D → ℕ
  mass : (∀ d, Fin (sampleSize d + 1)) → ℝ
  mass_nonneg : ∀ cell, 0 ≤ mass cell
  mass_sum_one : ∑ cell, mass cell = 1

/-- A nonnegative physical separation between two marker positions, in base pairs. -/
structure MarkerSeparationBp where
  value : ℝ
  value_nonneg : 0 ≤ value

/-- **The separation type has a named off-boundary inhabitant: the 250 kb clump window.**
Strictly positive rather than the zero its nonnegativity field permits, so any body dividing
by or thresholding on a separation is exercised away from the boundary.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness at a protocol constant. -/
noncomputable def clumpWindowSeparation : MarkerSeparationBp := ⟨250000, by norm_num⟩

/-- The two-locus moments a demographic history supplies at a recombination coordinate. -/
structure DemographicTwoLocusMoments (D : ℕ) where
  H : MarkerSeparationBp → Fin D → Fin D → ℝ
  DD : MarkerSeparationBp → Fin D → Fin D → ℝ
  Dz : MarkerSeparationBp → Fin D → Fin D → Fin D → ℝ
  pi2 : MarkerSeparationBp → Fin D → Fin D → Fin D → Fin D → ℝ

/-- Minimal domain on which the normalized cross-deme `DD` quotient is evaluable. -/
structure DemographicTwoLocusMoments.LDNormalizationDomain {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D) : Prop where
  firstWithin_pos : 0 < moments.DD rho first first
  secondWithin_pos : 0 < moments.DD rho second second

/-- Certificate that an evaluable `DD` pair is also a realizable covariance pair.  This
extra field is needed to prove `lambda ≤ 1`; it is not needed to evaluate `lambda`. -/
structure DemographicTwoLocusMoments.LDPairDomain {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D) : Prop extends
      moments.LDNormalizationDomain rho first second where
  cross_sq_le : (moments.DD rho first second) ^ 2 ≤
    moments.DD rho first first * moments.DD rho second second

/-- Exact normalized cross-deme linkage correlation
`E[D_i D_j] / sqrt(E[D_i²] E[D_j²])` for an arbitrary demographic two-locus law.

Empirical status: DERIVED from whatever `DemographicTwoLocusMoments` a history supplies --
this is the normalized ratio of the supplied joint moments and asserts nothing beyond them.
The empirical claim lives in the history that fills the interface (the composed generator of
`TwoLocusHistory`, or the two-deme stationary solve), and no battery has recorded a verdict
on any composed cross-deme correlation yet. -/
noncomputable def DemographicTwoLocusMoments.crossDemeLDCorrelation {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (_ : moments.LDNormalizationDomain rho first second) : ℝ :=
  moments.DD rho first second /
    Real.sqrt (moments.DD rho first first * moments.DD rho second second)

/-- The joint-channel factor on the `R²` scale.  Score accuracy is quadratic in the
tag--causal correlation, so this is the exact quotient `DD(i,j)²/(DD(i,i)DD(j,j))`, not an
independently fitted retention coefficient.  The next theorem identifies the quotient with
the squared normalized correlation.

Empirical status: DERIVED -- the quotient of the composed `DD` coordinates, whose status it
inherits; `accuracyLinkageFactor_nonneg` is its arithmetic consequence.  That score accuracy
is quadratic in the tag--causal correlation is the standard result assumed by the consumer
in `PhenomeWidePortability`; whether a composed history's factor matches simulation is the
untested composite claim named in `TwoLocusHistory`'s module status. -/
noncomputable def DemographicTwoLocusMoments.accuracyLinkageFactor {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (_ : moments.LDNormalizationDomain rho first second) : ℝ :=
  (moments.DD rho first second) ^ 2 /
    (moments.DD rho first first * moments.DD rho second second)

/-- On the nondegenerate normalization domain, the determinant quotient is exactly the
square of the normalized `DD` correlation.  The quotient form evaluates without first
assuming Cauchy--Schwarz; the correlation form explains its statistical meaning. -/
theorem DemographicTwoLocusMoments.accuracyLinkageFactor_eq_correlation_sq {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDNormalizationDomain rho first second) :
    moments.accuracyLinkageFactor rho first second domain =
      (moments.crossDemeLDCorrelation rho first second domain) ^ 2 := by
  unfold DemographicTwoLocusMoments.accuracyLinkageFactor
    DemographicTwoLocusMoments.crossDemeLDCorrelation
  rw [div_pow, Real.sq_sqrt
    (mul_nonneg domain.firstWithin_pos.le domain.secondWithin_pos.le)]

/-- The exact joint-channel factor is nonnegative on its typed domain. -/
theorem DemographicTwoLocusMoments.accuracyLinkageFactor_nonneg {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDNormalizationDomain rho first second) :
    0 ≤ moments.accuracyLinkageFactor rho first second domain :=
  div_nonneg (sq_nonneg _) (mul_nonneg domain.firstWithin_pos.le domain.secondWithin_pos.le)

/-- A genuine normalized `DD` correlation cannot contribute more than one unit of
accuracy.  The Cauchy--Schwarz fact is part of `LDPairDomain`, rather than silently assumed
from arbitrary real-valued moment fields. -/
theorem DemographicTwoLocusMoments.accuracyLinkageFactor_le_one {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDPairDomain rho first second) :
    moments.accuracyLinkageFactor rho first second domain.toLDNormalizationDomain ≤ 1 := by
  unfold DemographicTwoLocusMoments.accuracyLinkageFactor
  exact (div_le_one (mul_pos domain.firstWithin_pos domain.secondWithin_pos)).2
    domain.cross_sq_le

/-- Evaluability-and-meaning domain for the panel transport ratio: the panel's within-source
linkage mass and both heterozygosity readouts are positive.  Positivity of the within-source
`DD` sum is what makes the learned-weight normalization meaningful; the two heterozygosity
readouts are the per-deme score and liability variance scales. -/
structure DemographicTwoLocusMoments.PanelTransportDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : Prop where
  panelWithin_pos : 0 < ∑ k, moments.DD (panel k) source source
  sourceHet_pos : 0 < moments.H hetRho source source
  targetHet_pos : 0 < moments.H hetRho target target

/-- **The transport ratio `r²(target)/r²(source)` of a linear score trained in `source`,
from the propagated moments alone, with no marginal divergence factor.**

Derivation, and the reason there is no `(1 - F)` anywhere in the body.  Write the score as
tag dosages weighted by effects learned in the source deme.  Per tag--causal channel the
learned weight scales with the source-deme linkage moment `DD(source, source)`, and the
covariance the same weight delivers in the target deme scales with the cross-deme moment
`DD(source, target)`; channels at every panel separation sum coherently before squaring.
The score and liability variances in the target deme each scale with that deme's
heterozygosity.  Assembling the correlation ratio therefore gives

  `((Σ DD_st) / (Σ DD_ss))² · (H_ss / H_tt)²`

and the frequency-divergence loss is already inside `DD(source, target)`, which decays with
divergence; a composition that additionally multiplies a marginal `(1 - F)` factor charges
the same loss twice.  Under equal deme sizes and a single separation the ratio reduces to
`accuracyLinkageFactor` exactly (`panelTransportRatio_eq_linkageFactor`), which is why the
product composition looked correct on symmetric demographies and failed on asymmetric ones.

Empirical status: DERIVED, with the composition SHAPE measured on hostile demographies and
a committed battery still owed.  On the frozen eight-deme unequal-size asymmetric-migration
stress cube and the six-deme three-epoch split history (specs, predictions and grades in
`theory-out/stress_spec.json`, `stress_predict.json`, `stress_l3_grade2.json`, real plink
P+T pipeline, eight seeds each): this ratio grades at mean residual `+0.075 ± 0.038` and
`+0.0001 ± 0.058` respectively against measured per-deme transported `r²`, while the
superseded product form `marginal × linkage` graded `+0.144 ± 0.042`, pair-structured, on
the same cells.  The `hetRho` argument names the separation at which the one-locus
heterozygosity coordinate is read; histories propagate `H` identically across separations,
and no claim here depends on which is supplied.

Downstream metric charts are exact GIVEN the per-deme index variance and are not exact from
raw `H`: on the same stress cells the Gaussian liability AUC chart reproduces measured AUC
at `0.006 ± 0.006` when fed the measured per-deme latent-index variance, but the raw-`H`
prediction of that variance sits `0.60` below measurement because the causal panel is
COMMON-VARIANT ASCERTAINED and ascertainment flattens per-deme heterozygosity -- worth
about `0.05` of AUC if ignored.  The ascertained-spectrum heterozygosity is therefore the
one named factor separating this transport law from full metric-level prediction; it is the
finite-cohort ascertainment law's object, not a free parameter.  The classical
common-variant decomposition `v_j = (1 - F*_j)/(1 + F̄)` -- both divergences read from this
interface's `H` as coalescence times, deme-versus-pool and pooled -- is the current best
closed-form candidate: at honest seed-level clustering it grades `+0.028 ± 0.030` on the
six-deme stress history and `+0.113 ± 0.056` (2.0 sems, within the house 3-sem bar) on the
eight-deme cube, where per-seed residuals swing `-0.07` to `+0.45` because each seed draws
its own 150-locus causal panel.  The tension on the cube is real but unresolved at this
power; whatever residual survives more seeds is the pooled-sample MAF conditioning beyond
the time-ratio reading, which only the sample-count spectrum machinery expresses. -/
noncomputable def DemographicTwoLocusMoments.panelTransportRatio {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (_ : moments.PanelTransportDomain panel hetRho source target) : ℝ :=
  (((∑ k, moments.DD (panel k) source target) /
      (∑ k, moments.DD (panel k) source source)) ^ 2) *
    ((moments.H hetRho source source / moments.H hetRho target target) ^ 2)

/-- **A score transported to its own training deme keeps its accuracy exactly.**  Both
quotients collapse to one on the domain, with no hypotheses beyond evaluability.  A body
that returned anything else would charge a transport penalty for not transporting. -/
theorem DemographicTwoLocusMoments.panelTransportRatio_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.PanelTransportDomain panel hetRho source source) :
    moments.panelTransportRatio panel hetRho source source domain = 1 := by
  unfold DemographicTwoLocusMoments.panelTransportRatio
  rw [div_self domain.panelWithin_pos.ne', div_self domain.sourceHet_pos.ne']
  norm_num

/-- The transport ratio is a product of squares, hence nonnegative with no hypotheses. -/
theorem DemographicTwoLocusMoments.panelTransportRatio_nonneg {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (domain : moments.PanelTransportDomain panel hetRho source target) :
    0 ≤ moments.panelTransportRatio panel hetRho source target domain := by
  unfold DemographicTwoLocusMoments.panelTransportRatio
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Realizability domain for a panel-wide portability bound.  In addition to evaluability of
the transport ratio, every marker separation carries its exact two-deme covariance
certificate. -/
structure DemographicTwoLocusMoments.PanelTransportCauchyDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : Prop extends
      moments.PanelTransportDomain panel hetRho source target where
  pairDomain : ∀ k, moments.LDPairDomain (panel k) source target

/-- The panel-wide Cauchy upper envelope.  The linkage contribution is the ratio of total
target to total source within-deme `DD`; the heterozygosity scale is the same exact factor as
in `panelTransportRatio`. -/
noncomputable def DemographicTwoLocusMoments.panelTransportCauchyBound {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : ℝ :=
  ((∑ k, moments.DD (panel k) target target) /
      (∑ k, moments.DD (panel k) source source)) *
    (moments.H hetRho source source / moments.H hetRho target target) ^ 2

/-- The Cauchy envelope is normalized exactly at the training deme. -/
theorem DemographicTwoLocusMoments.panelTransportCauchyBound_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.PanelTransportDomain panel hetRho source source) :
    moments.panelTransportCauchyBound panel hetRho source source = 1 := by
  unfold DemographicTwoLocusMoments.panelTransportCauchyBound
  rw [div_self domain.panelWithin_pos.ne', div_self domain.sourceHet_pos.ne']
  norm_num

/-- The coherent cross-deme panel linkage is bounded by the product of the two within-deme
panel linkage masses.  This is derived from each propagated `DD` covariance certificate and
finite Cauchy--Schwarz; no panel-level fitted constant or bound is assumed. -/
theorem DemographicTwoLocusMoments.panelCrossSum_sq_le {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (source target : Fin D)
    (pairDomain : ∀ k, moments.LDPairDomain (panel k) source target) :
    (∑ k, moments.DD (panel k) source target) ^ 2 ≤
      (∑ k, moments.DD (panel k) source source) *
        (∑ k, moments.DD (panel k) target target) := by
  let sourceWithin : Fin n → ℝ := fun k ↦ moments.DD (panel k) source source
  let targetWithin : Fin n → ℝ := fun k ↦ moments.DD (panel k) target target
  let cross : Fin n → ℝ := fun k ↦ moments.DD (panel k) source target
  have hsource (k : Fin n) : 0 ≤ sourceWithin k :=
    (pairDomain k).firstWithin_pos.le
  have htarget (k : Fin n) : 0 ≤ targetWithin k :=
    (pairDomain k).secondWithin_pos.le
  have hterm (k : Fin n) :
      |cross k| ≤ Real.sqrt (sourceWithin k) * Real.sqrt (targetWithin k) := by
    calc
      |cross k| ≤ Real.sqrt (sourceWithin k * targetWithin k) :=
        Real.abs_le_sqrt (pairDomain k).cross_sq_le
      _ = Real.sqrt (sourceWithin k) * Real.sqrt (targetWithin k) := by
        rw [Real.sqrt_mul (hsource k)]
  have habs :
      |∑ k, cross k| ≤
        Real.sqrt (∑ k, sourceWithin k) * Real.sqrt (∑ k, targetWithin k) := by
    calc
      |∑ k, cross k| ≤ ∑ k, |cross k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, Real.sqrt (sourceWithin k) * Real.sqrt (targetWithin k) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
      _ ≤ Real.sqrt (∑ k, sourceWithin k) * Real.sqrt (∑ k, targetWithin k) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ hsource htarget
  have hsourceSum : 0 ≤ ∑ k, sourceWithin k :=
    Finset.sum_nonneg fun k _ ↦ hsource k
  have htargetSum : 0 ≤ ∑ k, targetWithin k :=
    Finset.sum_nonneg fun k _ ↦ htarget k
  calc
    (∑ k, moments.DD (panel k) source target) ^ 2 = |∑ k, cross k| ^ 2 := by
      simp only [cross, sq_abs]
    _ ≤ (Real.sqrt (∑ k, sourceWithin k) *
        Real.sqrt (∑ k, targetWithin k)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 habs
    _ = (∑ k, moments.DD (panel k) source source) *
        (∑ k, moments.DD (panel k) target target) := by
      rw [mul_pow, Real.sq_sqrt hsourceSum, Real.sq_sqrt htargetSum]

/-- **Certified portability bound for every finite panel and every finite demography.**

The exact transported accuracy ratio cannot exceed the panel-wide Cauchy envelope.  Because
the demographic history is already inside every `H` and `DD` entry, this theorem applies
unchanged to chains, two-dimensional grids, three-dimensional grids, arbitrary migration
graphs, and arbitrary split/rate-change histories. -/
theorem DemographicTwoLocusMoments.panelTransportRatio_le_cauchyBound {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (domain : moments.PanelTransportCauchyDomain panel hetRho source target) :
    moments.panelTransportRatio panel hetRho source target
        domain.toPanelTransportDomain ≤
      moments.panelTransportCauchyBound panel hetRho source target := by
  let sourceSum := ∑ k, moments.DD (panel k) source source
  let targetSum := ∑ k, moments.DD (panel k) target target
  let crossSum := ∑ k, moments.DD (panel k) source target
  let heterozygosityFactor :=
    (moments.H hetRho source source / moments.H hetRho target target) ^ 2
  have hsource : 0 < sourceSum := domain.panelWithin_pos
  have hcross : crossSum ^ 2 ≤ sourceSum * targetSum :=
    moments.panelCrossSum_sq_le panel source target domain.pairDomain
  have hlinkage : (crossSum / sourceSum) ^ 2 ≤ targetSum / sourceSum := by
    rw [div_pow]
    calc
      crossSum ^ 2 / sourceSum ^ 2 ≤ (sourceSum * targetSum) / sourceSum ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hsource)).2 hcross
      _ = targetSum / sourceSum := by
        field_simp [hsource.ne']
  unfold DemographicTwoLocusMoments.panelTransportRatio
    DemographicTwoLocusMoments.panelTransportCauchyBound
  dsimp only [sourceSum, targetSum, crossSum, heterozygosityFactor] at hlinkage ⊢
  exact mul_le_mul_of_nonneg_right hlinkage (sq_nonneg _)

/-- The panel portability bound is attained at the source population, so it is not a purely
formal loose envelope. -/
theorem DemographicTwoLocusMoments.panelTransportRatio_eq_cauchyBound_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.PanelTransportCauchyDomain panel hetRho source source) :
    moments.panelTransportRatio panel hetRho source source
        domain.toPanelTransportDomain =
      moments.panelTransportCauchyBound panel hetRho source source := by
  rw [moments.panelTransportRatio_self panel hetRho source domain.toPanelTransportDomain,
    moments.panelTransportCauchyBound_self panel hetRho source domain.toPanelTransportDomain]

/-- **On a symmetric pair the transport ratio IS the joint-channel linkage factor.**  With a
single panel separation, equal within-deme linkage and equal heterozygosity, the ratio
reduces to `accuracyLinkageFactor` -- the equal-size specialization that made the superseded
product composition look correct on tame demographies. -/
theorem DemographicTwoLocusMoments.panelTransportRatio_eq_linkageFactor {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho hetRho : MarkerSeparationBp)
    (source target : Fin D)
    (domain : moments.PanelTransportDomain (fun _ : Fin 1 ↦ rho) hetRho source target)
    (ndom : moments.LDNormalizationDomain rho source target)
    (hDD : moments.DD rho source source = moments.DD rho target target)
    (hH : moments.H hetRho source source = moments.H hetRho target target) :
    moments.panelTransportRatio (fun _ : Fin 1 ↦ rho) hetRho source target domain =
      moments.accuracyLinkageFactor rho source target ndom := by
  unfold DemographicTwoLocusMoments.panelTransportRatio
    DemographicTwoLocusMoments.accuracyLinkageFactor
  rw [Fin.sum_univ_one, Fin.sum_univ_one, hH, div_self domain.targetHet_pos.ne',
    one_pow, mul_one, div_pow]
  congr 1
  linear_combination moments.DD rho source source * hDD

/-- Domain for the selection-weighted transport ratio: positive within-source linkage at
every panel separation, and a nonzero reference regression at the tightest separation. -/
structure DemographicTwoLocusMoments.SelectionPanelDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (source target : Fin D) : Prop where
  within_pos : ∀ k, 0 < moments.DD (panel k) source source
  ref_ne : moments.DD (panel 0) source target ≠ 0

/-- **The selection-weighted transport ratio: the winner-location integral law.**

The clump index of a GWAS region is a random location on the linkage profile, and the
transported accuracy channel it carries is the selection-conditioned REGRESSION retention
`DD_tj/DD_tt` at that location, scaled to the self channel at the tightest separation.
Given winner-location weights `w` (a probability vector over the panel, supplied by the
correlated-significance-field computation) and the self-channel amplitude `selfAmp`
(the square root of the ascertained drift-heterogeneity ratio), the law is

  `ratio = (Σ_k w k · selfAmp · reg k / reg 0)²,  reg k = DD_tj(panel k)/DD_tt(panel k)`.

Its limits recover the corpus's earlier transport bodies: a point mass at the tightest
separation gives the pure self-channel law, and degenerate flat weights with unit self
amplitude give the unconditioned `panelTransportRatio` family.

Empirical status: MEASURED, blind, three times, on the grid2d demography with the real
plink P+T pipeline and hash-pinned predictors (validation/empirical/gate/): the
unconditioned family misses +0.261 ± 0.101 (gate 1, seeds 101-108) and the pure
self-channel endpoint misses -0.272 ± 0.047 (gate 2, seeds 109-116), while THIS law
passes every pre-filed bar at gate 3 (seeds 117-124): transport ratio +0.032 ± 0.052 and
chart AUC -0.002 ± 0.009, zero fitted constants in the chain.  The governing complete
derivation, with the frozen list of terms measured to lie below gate power at this
design (multi-causal regions, panel winner's curse, the LD-field closure bound), is
validation/empirical/gate/EXACT_TRANSPORT_DERIVATION.md. -/
noncomputable def DemographicTwoLocusMoments.selectionWeightedTransportRatio {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (winner : Fin (n + 1) → ℝ) (selfAmp : ℝ) (source target : Fin D)
    (_ : moments.SelectionPanelDomain panel source target) : ℝ :=
  ((∑ k, winner k * (selfAmp *
      ((moments.DD (panel k) source target / moments.DD (panel k) source source) /
        (moments.DD (panel 0) source target / moments.DD (panel 0) source source)))) ^ 2)

/-- **A point mass at the tightest separation recovers the self-channel law exactly.** -/
theorem DemographicTwoLocusMoments.selectionWeightedTransportRatio_pointMass {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (selfAmp : ℝ) (source target : Fin D)
    (domain : moments.SelectionPanelDomain panel source target) :
    moments.selectionWeightedTransportRatio panel
      (fun k ↦ if k = 0 then 1 else 0) selfAmp source target domain = selfAmp ^ 2 := by
  classical
  unfold DemographicTwoLocusMoments.selectionWeightedTransportRatio
  have hden : (moments.DD (panel 0) source target / moments.DD (panel 0) source source) ≠ 0 :=
    div_ne_zero domain.ref_ne (domain.within_pos 0).ne'
  have hsum : (∑ k, (if k = 0 then (1 : ℝ) else 0) *
      (selfAmp * ((moments.DD (panel k) source target / moments.DD (panel k) source source) /
        (moments.DD (panel 0) source target / moments.DD (panel 0) source source)))) =
      selfAmp * ((moments.DD (panel 0) source target / moments.DD (panel 0) source source) /
        (moments.DD (panel 0) source target / moments.DD (panel 0) source source)) := by
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, div_self hden]
  ring

/-- The selection-weighted ratio is a square, hence nonnegative with no hypotheses. -/
theorem DemographicTwoLocusMoments.selectionWeightedTransportRatio_nonneg {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (winner : Fin (n + 1) → ℝ) (selfAmp : ℝ) (source target : Fin D)
    (domain : moments.SelectionPanelDomain panel source target) :
    0 ≤ moments.selectionWeightedTransportRatio panel winner selfAmp source target domain :=
  sq_nonneg _

/-- Concrete three-deme moment table for the transport-domain witness.  Three demes rather
than two so that two-deme degeneracies cannot hide; every within-deme heterozygosity and
linkage value is distinct so the size-correction factor and the normalization are both
exercised rather than silently equal to one.

Empirical status: NOT AN EMPIRICAL CLAIM -- a concrete table inhabiting the interface. -/
noncomputable def panelTransportWitnessMoments : DemographicTwoLocusMoments 3 where
  H := fun _ i j ↦ (i.val + j.val + 2 : ℝ)
  DD := fun _ i j ↦ if i = j then (i.val + 2 : ℝ) else 1
  Dz := fun _ _ _ _ ↦ 0
  pi2 := fun _ _ _ _ _ ↦ 0

/-- **The Cauchy--Schwarz-certified pair domain has a named off-boundary inhabitant.**  The
cross moment is 1 against within-deme moments 2 and 3, so the certificate inequality
`1 < 6` holds STRICTLY -- a witness at equality would certify a perfectly correlated pair
and hide a body that only works on the degenerate boundary.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
noncomputable def panelTransportPairDomainWitness :
    panelTransportWitnessMoments.LDPairDomain clumpWindowSeparation 0 1 where
  firstWithin_pos := by
    simp [panelTransportWitnessMoments]
  secondWithin_pos := by
    simp [panelTransportWitnessMoments]
    norm_num
  cross_sq_le := by
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    simp [panelTransportWitnessMoments, h01]
    norm_num

/-- The transport domain has an off-boundary inhabitant: a one-window panel at the 250 kb
clump separation between demes of UNEQUAL heterozygosity (2 versus 4), so the witness would
detect a body that dropped the size-correction factor rather than only certifying that the
quotients evaluate.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
noncomputable def panelTransportDomainWitness :
    panelTransportWitnessMoments.PanelTransportDomain
      (fun _ : Fin 1 ↦ clumpWindowSeparation) clumpWindowSeparation 0 1 where
  panelWithin_pos := by
    simp [panelTransportWitnessMoments]
  sourceHet_pos := by simp [panelTransportWitnessMoments]
  targetHet_pos := by
    simp [panelTransportWitnessMoments]
    norm_num

/-- The selection-panel domain has a named off-boundary inhabitant on the witness table:
within-deme linkage 2 and 3 (positive, distinct) and cross linkage 1 (nonzero), so the
reference regression is exercised away from every degenerate value.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
noncomputable def selectionPanelDomainWitness :
    panelTransportWitnessMoments.SelectionPanelDomain
      (fun _ : Fin 2 ↦ clumpWindowSeparation) 0 1 where
  within_pos := by
    intro k
    simp [panelTransportWitnessMoments]
  ref_ne := by
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    simp [panelTransportWitnessMoments, h01]

/-- The bare normalization domain inherits the pair witness's inhabitant by projection.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness by projection. -/
noncomputable def panelTransportNormalizationDomainWitness :
    panelTransportWitnessMoments.LDNormalizationDomain clumpWindowSeparation 0 1 :=
  panelTransportPairDomainWitness.toLDNormalizationDomain

/-- The complete typed output of a demography.  Serial-founder, grid and `stdpopsim` histories
are constructors of this interface, not new metric derivations. -/
structure DemographyFunctionals (D : ℕ) where
  coalescence : PairwiseCoalescenceTimes D
  spectrum : JointSampleSpectrum D
  twoLocus : DemographicTwoLocusMoments D

/-- Slatkin--Hudson `F_ST` on the typed coalescence constructor.

Empirical status: DERIVED -- the ratio-of-times reading of Hudson's `F_ST`,
`1 - t̄_within / t_between`, applied to the typed coalescence functionals; Slatkin's identity
(`slatkin_identity`, proved beside it) is what licenses reading it as a heterozygosity ratio
with the mutation rate cancelled.  It is Hudson's convention and not Nei's `G_ST`; the
conversion and their inequality live in `Core.Fst`.  Which population supplies the times is
the empirical question, asked wherever a demography constructor fills
`PairwiseCoalescenceTimes`. -/
noncomputable def PairwiseCoalescenceTimes.hudsonFst {D : ℕ}
    (T : PairwiseCoalescenceTimes D) (i j : Fin D) : ℝ :=
  1 - ((T.within i + T.within j) / 2) / T.between i j

/-- **Slatkin's identity**, with mutation cancelling from the ratio: if within and between
heterozygosities are a common mutation rate times their typed coalescence times, Hudson's
heterozygosity ratio equals the time ratio. -/
theorem PairwiseCoalescenceTimes.slatkin_identity {D : ℕ}
    (T : PairwiseCoalescenceTimes D) (i j : Fin D) (mu : ℝ)
    (hmu : mu ≠ 0) :
    1 - (mu * ((T.within i + T.within j) / 2)) / (mu * T.between i j) =
      T.hudsonFst i j := by
  unfold PairwiseCoalescenceTimes.hudsonFst
  field_simp [hmu, (T.between_pos i j).ne']

/-- Exact train-versus-all projection of the many-population JSFS/moment representation.
Following the marginal-projection principle used by Kamm--Terhorst--Song, only the
train-to-deme pairwise functionals needed by the requested report are materialized.  Its state
therefore grows linearly in the number of demes rather than as the Cartesian product of all
sample configurations. -/
structure TrainVsAllRepresentation (D : ℕ) where
  train : Fin D
  weight : Fin D → ℝ
  weight_nonneg : ∀ d, 0 ≤ weight d
  weight_sum_one : ∑ d, weight d = 1
  scoreMean : Fin D → ℝ
  scoreVariance : Fin D → ℝ
  scoreOutcomeCovariance : Fin D → ℝ
  prevalence : Fin D → ℝ
  pairwiseSpectrum : Fin D → ℕ → ℕ → ℝ
  pairwiseLD : ℝ → Fin D → ℝ

/-- Any exact demewise quantity aggregates without enumerating a `D`-dimensional JSFS. -/
noncomputable def TrainVsAllRepresentation.aggregate {D : ℕ}
    (r : TrainVsAllRepresentation D) (quantity : Fin D → ℝ) : ℝ :=
  ∑ d, r.weight d * quantity d

/-- The aggregate of a constant is the constant, pinning the weight convention. -/
theorem TrainVsAllRepresentation.aggregate_const {D : ℕ}
    (r : TrainVsAllRepresentation D) (c : ℝ) :
    r.aggregate (fun _ ↦ c) = c := by
  unfold TrainVsAllRepresentation.aggregate
  rw [← Finset.sum_mul, r.weight_sum_one, one_mul]

/-! ## Inhabitation

A theorem quantified over an uninhabited structure is true and empty -- kernel-checked, clean
axiom report, no content -- so the rate and moment classes carry exhibited inhabitants.

THE VALUES ARE OFF THE BOUNDARIES THEIR OWN HYPOTHESES ADMIT.  Migration and mutation are
allowed to be zero by the type, and are nonzero here: zero migration disconnects the two demes
and collapses every structured statement to a pair of independent panmictic ones, and zero
mutation removes the only forcing term, so a witness at either would inhabit the class while
making the structure it exists to describe unreachable.  The between-deme coalescence time
likewise exceeds the within-deme one, which is what "structured" means. -/

/-- Inhabitation for the two-deme rate set, at nonzero migration and nonzero mutation. -/
noncomputable def TwoDemeRates.witness : TwoDemeRates where
  sourceCoal := 1
  targetCoal := 1
  sourceToTarget := 1 / 10
  targetToSource := 1 / 10
  sourceForwardMutation := 1 / 1000
  sourceBackwardMutation := 1 / 1000
  targetForwardMutation := 1 / 1000
  targetBackwardMutation := 1 / 1000
  sourceCoal_pos := by norm_num
  targetCoal_pos := by norm_num
  sourceToTarget_nonneg := by norm_num
  targetToSource_nonneg := by norm_num
  sourceForwardMutation_nonneg := by norm_num
  sourceBackwardMutation_nonneg := by norm_num
  targetForwardMutation_nonneg := by norm_num
  targetBackwardMutation_nonneg := by norm_num

/-- Inhabitation for one epoch, at a positive duration.  A zero-duration epoch has the
identity propagator, so it would satisfy the class without propagating anything. -/
noncomputable def TwoDemeMomentEpoch.witness (K : ℕ) : TwoDemeMomentEpoch K where
  rates := TwoDemeRates.witness
  duration := 1
  duration_nonneg := by norm_num

/-- Inhabitation for the pairwise coalescence times, on two demes and with the between-deme
time strictly exceeding the within-deme one -- the ordering that makes `hudsonFst` positive
rather than zero. -/
noncomputable def PairwiseCoalescenceTimes.witness : PairwiseCoalescenceTimes 2 where
  within := fun _ ↦ 1
  between := fun i j ↦ if i = j then 1 else 2
  within_pos := by intro d; norm_num
  between_pos := by intro i j; split <;> norm_num
  between_symmetric := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  between_self := by intro i; simp

/-- Inhabitation for the two-locus moment interface.  The moments are constant in the
recombination coordinate here, which is all the class asks: its two hypotheses are the index
symmetries, and a constant family satisfies them without pretending to a decay law the
interface deliberately does not fix. -/
noncomputable def DemographicTwoLocusMoments.witness : DemographicTwoLocusMoments 2 where
  H := fun _ _ _ ↦ 1
  DD := fun _ _ _ ↦ 1
  Dz := fun _ _ _ _ ↦ 0
  pi2 := fun _ _ _ _ _ ↦ 1

end Coalescent

end Descent
