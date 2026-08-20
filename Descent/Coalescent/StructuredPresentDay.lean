/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Structured
import Descent.Core.Moments
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

set_option autoImplicit false

namespace Descent

namespace Coalescent

open MeasureTheory Filter Topology
open scoped Matrix.Norms.Operator

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

/-- The normalized descending-factorial statistic carried by a count `j` from a sample of
size `n`: `(j)_order / (n)_order`.  Its domain proof forbids requesting a frequency moment
whose order exceeds the sample size. -/
noncomputable def normalizedCountFactorialMoment
    (sampleSize order count : ℕ) (_ : order ≤ sampleSize) : ℝ :=
  (count.descFactorial order : ℝ) / (sampleSize.descFactorial order : ℝ)

/-- Exact finite-sample heterozygosity statistic.  For at least two haplotypes this is
`2 ((J)_1/(n)_1 - (J)_2/(n)_2)`, the unbiased pairwise-difference readout of the target
frequency.  A sample with fewer than two haplotypes contains no pair and therefore has no
inhabitant of this statistic's domain. -/
noncomputable def targetCountHeterozygosity
    (sampleSize count : ℕ) (domain : 2 ≤ sampleSize) : ℝ :=
  2 * (normalizedCountFactorialMoment sampleSize 1 count (by omega) -
    normalizedCountFactorialMoment sampleSize 2 count domain)

/-- Joint mass of source-sample ascertainment weighted by an arbitrary statistic of the
target count.  This is the finite conditional-expectation numerator; both cohort sizes occur
in the event and the target statistic, so changing a cohort size changes the law itself. -/
noncomputable def sourcePolymorphicTargetStatisticMass
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) (statistic : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (ns - 1),
    ∑ j ∈ Finset.range (nt + 1), statistic j * jointCount i j

/-- Exact conditional expectation of a target-count statistic given observed source
polymorphism.  `none` is the genuine zero-mass conditioning case, never a numerical fallback. -/
noncomputable def targetStatisticGivenSourcePolymorphic
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) (statistic : ℕ → ℝ) : Option ℝ :=
  let denominator := sourcePolymorphicEventMass jointCount ns nt
  if 0 < denominator then
    some (sourcePolymorphicTargetStatisticMass jointCount ns nt statistic / denominator)
  else none

/-- Every target frequency moment identifiable from `nt` haplotypes, conditional on the
actual source ascertainment event.  The descending-factorial statistic makes this a direct
Bernstein readout rather than a plug-in frequency approximation. -/
noncomputable def targetFactorialMomentGivenSourcePolymorphic
    (jointCount : ℕ → ℕ → ℝ) (ns nt order : ℕ) : Option ℝ :=
  if domain : order ≤ nt then
    targetStatisticGivenSourcePolymorphic jointCount ns nt
      (fun count ↦ normalizedCountFactorialMoment nt order count domain)
  else none

/-- Exact expected target heterozygosity after source-sample ascertainment, evaluated at both
actual cohort sizes.  This is the missing common-variant spectrum coordinate needed by score
variance; fixation probability alone does not determine it. -/
noncomputable def targetHeterozygosityGivenSourcePolymorphic
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) : Option ℝ :=
  if domain : 2 ≤ nt then
    targetStatisticGivenSourcePolymorphic jointCount ns nt
      (fun count ↦ targetCountHeterozygosity nt count domain)
  else none

/-- Monomorphic target counts contribute exactly zero to the finite-sample heterozygosity
readout. -/
theorem targetCountHeterozygosity_zero (sampleSize : ℕ) (domain : 2 ≤ sampleSize) :
    targetCountHeterozygosity sampleSize 0 domain = 0 := by
  simp [targetCountHeterozygosity, normalizedCountFactorialMoment]

/-- The all-derived target count also contributes exactly zero. -/
theorem targetCountHeterozygosity_self (sampleSize : ℕ) (domain : 2 ≤ sampleSize) :
    targetCountHeterozygosity sampleSize sampleSize domain = 0 := by
  unfold targetCountHeterozygosity normalizedCountFactorialMoment
  rw [Nat.descFactorial_one]
  have hn : (sampleSize : ℝ) ≠ 0 := by positivity
  have hdf : (sampleSize.descFactorial 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr domain).ne'
  rw [div_self hn, div_self hdf]
  ring

/-- Weighting and summing over the finite ascertainment event is linear.  This elementary
identity is the algebraic step that turns the first two exact factorial moments into exact
heterozygosity after conditioning. -/
theorem sourcePolymorphicTargetStatisticMass_scaledSub
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) (scale : ℝ)
    (first second : ℕ → ℝ) :
    sourcePolymorphicTargetStatisticMass jointCount ns nt
        (fun count ↦ scale * (first count - second count)) =
      scale * (sourcePolymorphicTargetStatisticMass jointCount ns nt first -
        sourcePolymorphicTargetStatisticMass jointCount ns nt second) := by
  classical
  unfold sourcePolymorphicTargetStatisticMass
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- The conditional heterozygosity law is exactly twice the difference between the first and
second conditional descending-factorial moments.  This theorem rules out treating fixation
retention as a substitute for the interior spectrum: both moments are required. -/
theorem targetHeterozygosityGivenSourcePolymorphic_eq_factorialMoments
    (jointCount : ℕ → ℕ → ℝ) (ns nt : ℕ) (hnt : 2 ≤ nt) :
    targetHeterozygosityGivenSourcePolymorphic jointCount ns nt =
      (targetFactorialMomentGivenSourcePolymorphic jointCount ns nt 1).bind fun first ↦
        (targetFactorialMomentGivenSourcePolymorphic jointCount ns nt 2).map fun second ↦
          2 * (first - second) := by
  let denominator := sourcePolymorphicEventMass jointCount ns nt
  have hntOne : 1 ≤ nt := by omega
  by_cases hdenominator : 0 < denominator
  · simp only [targetHeterozygosityGivenSourcePolymorphic, dif_pos hnt,
      targetFactorialMomentGivenSourcePolymorphic,
      dif_pos hntOne, dif_pos hnt,
      targetStatisticGivenSourcePolymorphic, denominator, hdenominator, if_pos,
      Option.bind_some, Option.map_some]
    have hstatistic : (fun count ↦ targetCountHeterozygosity nt count hnt) = fun count ↦
        2 * (normalizedCountFactorialMoment nt 1 count hntOne -
          normalizedCountFactorialMoment nt 2 count hnt) := by
      funext count
      rfl
    rw [hstatistic]
    rw [sourcePolymorphicTargetStatisticMass_scaledSub]
    ring
  · simp [targetHeterozygosityGivenSourcePolymorphic, hnt,
      targetFactorialMomentGivenSourcePolymorphic,
      hntOne, targetStatisticGivenSourcePolymorphic, denominator, hdenominator]

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

/-- A finite real generator is Metzler when every off-diagonal entry is nonnegative.  This
is the exact infinitesimal condition for a positive finite-dimensional semigroup; diagonal
entries may be negative because they contain total exit and killing rates. -/
def Matrix.IsMetzler {ι : Type*} (A : Matrix ι ι ℝ) : Prop :=
  ∀ row column, row ≠ column → 0 ≤ A row column

/-- Finite diagonal shift used to turn a Metzler matrix into an entrywise-nonnegative
matrix.  The sum of absolute diagonal entries is deliberately nonminimal but exact and
requires no choice of a maximizing coordinate. -/
noncomputable def matrixMetzlerShift {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  ∑ coordinate, |A coordinate coordinate|

/-- Adding the exact finite diagonal shift makes every entry of a Metzler matrix
nonnegative. -/
theorem matrix_add_metzlerShift_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : Matrix.IsMetzler A) (row column : ι) :
    0 ≤ (A + matrixMetzlerShift A • (1 : Matrix ι ι ℝ)) row column := by
  by_cases equal : row = column
  · subst column
    have diagonal_le : |A row row| ≤ matrixMetzlerShift A := by
      unfold matrixMetzlerShift
      exact Finset.single_le_sum (fun coordinate _ ↦ abs_nonneg (A coordinate coordinate))
        (Finset.mem_univ row)
    have neg_diagonal_le : -A row row ≤ |A row row| := neg_le_abs (A row row)
    have shiftedDiagonal : 0 ≤ A row row + matrixMetzlerShift A := by linarith
    simpa [Matrix.one_apply] using shiftedDiagonal
  · simp [Matrix.add_apply, equal, hA row column equal]

/-- Every power of an entrywise-nonnegative finite matrix is entrywise nonnegative. -/
theorem matrix_pow_apply_nonneg_of_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : ∀ row column, 0 ≤ A row column) :
    ∀ power row column, 0 ≤ (A ^ power) row column := by
  intro power
  induction power with
  | zero =>
      intro row column
      by_cases equal : row = column <;> simp [equal]
  | succ power induction =>
      intro row column
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun middle _ ↦
        mul_nonneg (induction row middle) (hA middle column)

/-- The exact exponential series of an entrywise-nonnegative matrix at nonnegative time is
entrywise nonnegative. -/
theorem matrixExponential_apply_nonneg_of_nonneg {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : ∀ row column, 0 ≤ A row column) (time : ℝ) (time_nonneg : 0 ≤ time)
    (row column : ι) :
    0 ≤ matrixExponential A time row column := by
  unfold matrixExponential
  have summableMatrix : Summable (fun power : ℕ ↦
      ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) :=
    NormedSpace.expSeries_summable' (time • A)
  have summableRow : Summable (fun power : ℕ ↦
      (((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)) row) :=
    Pi.summable.mp summableMatrix row
  rw [tsum_apply summableMatrix, tsum_apply summableRow]
  apply tsum_nonneg
  intro power
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg power.factorial)
  · apply matrix_pow_apply_nonneg_of_nonneg
    intro source target
    change 0 ≤ time * A source target
    exact mul_nonneg time_nonneg (hA source target)

/-- The corpus matrix exponential is definitionally the Banach-algebra exponential of the
time-scaled matrix.  This bridge permits exact commuting-shift identities while retaining
the explicit series definition used by certified evaluators. -/
theorem matrixExponential_eq_normedSpace_exp {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (time : ℝ) :
    matrixExponential A time = NormedSpace.exp ℝ (time • A) := by
  rw [NormedSpace.exp_eq_tsum]
  rfl

/-- **A finite Metzler generator has an entrywise-nonnegative exact semigroup.**

The proof adds the finite scalar diagonal shift `c = Σᵢ |Aᵢᵢ|`, making
`B = A + cI` entrywise nonnegative.  Since the scalar matrix commutes with `B`,
`exp(tA) = exp(-tc I) exp(tB)`.  The second factor is nonnegative term-by-term in its
convergent series and the first is a positive scalar diagonal.  No Euler discretization,
closure, or limiting Markov-chain assertion is assumed. -/
theorem matrixExponential_apply_nonneg_of_metzler {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : Matrix.IsMetzler A)
    (time : ℝ) (time_nonneg : 0 ≤ time) (row column : ι) :
    0 ≤ matrixExponential A time row column := by
  let shift := matrixMetzlerShift A
  let shifted := A + shift • (1 : Matrix ι ι ℝ)
  have shifted_nonneg : ∀ source target, 0 ≤ shifted source target := by
    intro source target
    exact matrix_add_metzlerShift_nonneg A hA source target
  have decomposition : time • A =
      (-time * shift) • (1 : Matrix ι ι ℝ) + time • shifted := by
    ext source target
    by_cases equal : source = target
    · subst target
      simp [shifted]
    · simp [shifted, equal]
  have commute : Commute ((-time * shift) • (1 : Matrix ι ι ℝ)) (time • shifted) :=
    (Commute.one_left (time • shifted)).smul_left (-time * shift)
  have exponentialDecomposition :
      NormedSpace.exp ℝ
          ((-time * shift) • (1 : Matrix ι ι ℝ) + time • shifted) =
        NormedSpace.exp ℝ ((-time * shift) • (1 : Matrix ι ι ℝ)) *
          NormedSpace.exp ℝ (time • shifted) :=
    Matrix.exp_add_of_commute ℝ _ _ commute
  rw [matrixExponential_eq_normedSpace_exp, decomposition, exponentialDecomposition]
  rw [show (-time * shift) • (1 : Matrix ι ι ℝ) =
      Matrix.diagonal (fun _ : ι ↦ -time * shift) by
        ext source target
        by_cases equal : source = target <;> simp [equal]]
  rw [Matrix.exp_diagonal]
  rw [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro middle _
  apply mul_nonneg
  · by_cases equal : row = middle
    · subst middle
      have exponential_nonneg : 0 ≤ Real.exp (-(time * shift)) := (Real.exp_pos _).le
      rw [Real.exp_eq_exp_ℝ] at exponential_nonneg
      simpa using exponential_nonneg
    · simp [equal]
  · rw [← matrixExponential_eq_normedSpace_exp]
    exact matrixExponential_apply_nonneg_of_nonneg shifted shifted_nonneg time time_nonneg
      middle column

/-- Finite Taylor evaluation of the exact matrix exponential, through powers
`0, ..., terms - 1`. -/
noncomputable def matrixExponentialPartialSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) : Matrix ι ι ℝ :=
  ∑ power ∈ Finset.range terms,
    ((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)

/-- Exact operator-norm tail certificate for a finite Taylor evaluation.  It is a convergent
nonnegative scalar series and can itself be enclosed to any desired precision. -/
noncomputable def matrixExponentialTailBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) : ℝ :=
  ∑' offset : ℕ,
    ‖(((offset + terms).factorial : ℝ)⁻¹) •
      ((time • A) ^ (offset + terms))‖

/-- Transposition commutes exactly with the custom matrix exponential.  This is the
algebraic step that turns forward moment propagation into the backward sampling dual; it
uses the complete convergent series, not a time discretization or a truncated ladder. -/
theorem matrixExponential_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) :
    matrixExponential A.transpose time = (matrixExponential A time).transpose := by
  unfold matrixExponential
  rw [Matrix.transpose_tsum]
  apply tsum_congr
  intro power
  rw [Matrix.transpose_smul, Matrix.transpose_pow, Matrix.transpose_smul]

/-- Exact forward/backward pairing for a finite moment generator.  A requested terminal
functional `probe` may be propagated through the transposed generator and paired with the
initial state instead of constructing the full forward moment vector.  This identity is the
finite-dimensional sampling-dual law used by sparse uniformization and Krylov evaluators. -/
theorem matrixExponential_samplingDual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (probe state : ι → ℝ) :
    probe ⬝ᵥ (matrixExponential A time).mulVec state =
      (matrixExponential A.transpose time).mulVec probe ⬝ᵥ state := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← matrixExponential_transpose]

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

/-- Absolute summability of the norm series used by the certified Taylor tail. -/
private theorem matrixExponentialSeries_norm_summable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) :
    Summable (fun power : ℕ ↦
      ‖((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)‖) := by
  exact NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (time • A)

/-- Exact decomposition into the finite Taylor approximation plus its matrix-valued tail. -/
theorem matrixExponential_eq_partialSum_add_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) :
    matrixExponential A time = matrixExponentialPartialSum A time terms +
      ∑' offset : ℕ,
        (((offset + terms).factorial : ℝ)⁻¹) •
          ((time • A) ^ (offset + terms)) := by
  exact (matrixExponentialSeries_summable A time).sum_add_tsum_nat_add terms |>.symm

/-- The certified scalar tail is nonnegative. -/
theorem matrixExponentialTailBound_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) :
    0 ≤ matrixExponentialTailBound A time terms := by
  exact tsum_nonneg fun _ ↦ norm_nonneg _

/-- The certified tail bound vanishes as the number of retained terms tends to infinity. -/
theorem matrixExponentialTailBound_tendsto_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) :
    Tendsto (fun terms ↦ matrixExponentialTailBound A time terms)
      atTop (𝓝 0) := by
  exact tendsto_sum_nat_add (fun power : ℕ ↦
    ‖((power.factorial : ℝ)⁻¹) • ((time • A) ^ power)‖)

/-- Finite Taylor matrices converge to the exact operator. -/
theorem matrixExponentialPartialSum_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) :
    Tendsto (fun terms ↦ matrixExponentialPartialSum A time terms)
      atTop (𝓝 (matrixExponential A time)) := by
  exact (matrixExponentialSeries_summable A time).hasSum.tendsto_sum_nat

/-- Rigorous operator-norm error certificate for every finite Taylor evaluation.  Increasing
`terms` changes only an explicit finite sum and the tail index; no unproved numerical
tolerance or fitted stopping rule enters. -/
theorem matrixExponential_partialSum_error_le_tailBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) :
    ‖matrixExponential A time - matrixExponentialPartialSum A time terms‖ ≤
      matrixExponentialTailBound A time terms := by
  calc
    _ = ‖∑' offset : ℕ,
          (((offset + terms).factorial : ℝ)⁻¹) •
            ((time • A) ^ (offset + terms))‖ := by
      rw [matrixExponential_eq_partialSum_add_tail A time terms,
        add_sub_cancel_left]
    _ ≤ matrixExponentialTailBound A time terms := by
      unfold matrixExponentialTailBound
      apply norm_tsum_le_tsum_norm
      exact (summable_nat_add_iff terms).2
        (matrixExponentialSeries_norm_summable A time)

/-- Certified error after applying the finite Taylor matrix to a probe or state vector.  This
is the directly usable stopping bound for backward sparse propagation. -/
theorem matrixExponential_partialSum_mulVec_error_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (time : ℝ) (terms : ℕ) (vector : ι → ℝ) :
    ‖(matrixExponential A time).mulVec vector -
        (matrixExponentialPartialSum A time terms).mulVec vector‖ ≤
      matrixExponentialTailBound A time terms * ‖vector‖ := by
  rw [← Matrix.sub_mulVec]
  calc
    _ ≤ ‖matrixExponential A time - matrixExponentialPartialSum A time terms‖ *
        ‖vector‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ matrixExponentialTailBound A time terms * ‖vector‖ :=
      mul_le_mul_of_nonneg_right
        (matrixExponential_partialSum_error_le_tailBound A time terms) (norm_nonneg _)

/-- Hölder's finite `L∞ × L1` bound in the exact norms used by the matrix evaluator. -/
theorem abs_dotProduct_le_norm_mul_sum_abs
    {ι : Type*} [Fintype ι] (left right : ι → ℝ) :
    |left ⬝ᵥ right| ≤ ‖left‖ * ∑ coordinate, |right coordinate| := by
  rw [dotProduct]
  calc
    |∑ coordinate, left coordinate * right coordinate| ≤
        ∑ coordinate, |left coordinate * right coordinate| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ coordinate, |left coordinate| * |right coordinate| := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [abs_mul]
    _ ≤ ∑ coordinate, ‖left‖ * |right coordinate| := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact mul_le_mul_of_nonneg_right
        (norm_le_pi_norm left coordinate) (abs_nonneg _)
    _ = ‖left‖ * ∑ coordinate, |right coordinate| := by
      rw [Finset.mul_sum]

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

/-- Raise one lineage-count coordinate. -/
def incrementExponent {D : ℕ} (exponent : Fin D → ℕ) (deme : Fin D) : Fin D → ℕ :=
  fun d ↦ if d = deme then exponent d + 1 else exponent d

/-- Raising the coordinate just lowered recovers the original exponent whenever that
coordinate was positive. -/
theorem incrementExponent_decrementExponent {D : ℕ} (exponent : Fin D → ℕ)
    (deme : Fin D) (positive : 0 < exponent deme) :
    incrementExponent (decrementExponent exponent deme) deme = exponent := by
  funext d
  by_cases equal : d = deme
  · subst d
    simp [incrementExponent, decrementExponent]
    omega
  · simp [incrementExponent, decrementExponent, equal]

/-- Raising one exponent raises its total degree by exactly one. -/
theorem sum_incrementExponent {D : ℕ} (exponent : Fin D → ℕ) (deme : Fin D) :
    ∑ d, incrementExponent exponent deme d = (∑ d, exponent d) + 1 := by
  classical
  calc
    _ = incrementExponent exponent deme deme +
        ∑ d ∈ Finset.univ \ {deme}, incrementExponent exponent deme d :=
      Finset.sum_eq_add_sum_diff_singleton (f := incrementExponent exponent deme)
        (Finset.mem_univ deme)
    _ = (exponent deme + 1) +
        ∑ d ∈ Finset.univ \ {deme}, exponent d := by
      congr 1
      · simp [incrementExponent]
      · apply Finset.sum_congr rfl
        intro d member
        have distinct : d ≠ deme :=
          Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
        simp [incrementExponent, distinct]
    _ = (∑ d, exponent d) + 1 := by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ deme)]
      omega

/-- Removing a positive exponent lowers its total degree by exactly one. -/
theorem sum_decrementExponent {D : ℕ} (exponent : Fin D → ℕ) (deme : Fin D)
    (positive : 0 < exponent deme) :
    ∑ d, decrementExponent exponent deme d = (∑ d, exponent d) - 1 := by
  classical
  calc
    _ = decrementExponent exponent deme deme +
        ∑ d ∈ Finset.univ \ {deme}, decrementExponent exponent deme d :=
      Finset.sum_eq_add_sum_diff_singleton (f := decrementExponent exponent deme)
        (Finset.mem_univ deme)
    _ = (exponent deme - 1) +
        ∑ d ∈ Finset.univ \ {deme}, exponent d := by
      congr 1
      · simp [decrementExponent]
      · apply Finset.sum_congr rfl
        intro d member
        have distinct : d ≠ deme :=
          Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
        simp [decrementExponent, distinct]
    _ = (∑ d, exponent d) - 1 := by
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ deme)]
      omega

/-- Truncated decrement never increases total degree, including at a zero exponent. -/
theorem sum_decrementExponent_le {D : ℕ} (exponent : Fin D → ℕ) (deme : Fin D) :
    (∑ d, decrementExponent exponent deme d) ≤ ∑ d, exponent d := by
  apply Finset.sum_le_sum
  intro d _
  by_cases equal : d = deme
  · subst d
    simp [decrementExponent]
  · simp [decrementExponent, equal]

/-- Move one ancestral lineage from one deme label to another.

Empirical status: NOT AN EMPIRICAL CLAIM -- index bookkeeping for the moment generator.
Relabelling a lineage asserts nothing about a population; the generator assembled from it is
where a migration mechanism is chosen, and the composed output is where a measurement could
bear. -/
def migrateExponent {D : ℕ} (exponent : Fin D → ℕ)
    (src dst : Fin D) : Fin D → ℕ :=
  fun d ↦ if d = src then exponent d - 1 else if d = dst then exponent d + 1 else exponent d

/-- Product Bernstein basis weight for derived and ancestral lineage counts.  This is the
positive basis used by the killed structured-coalescent dual: no alternating monomial
expansion appears in the state value itself. -/
noncomputable def manyDemeBernsteinWeight {D : ℕ} (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  ∏ deme, frequency deme ^ derived deme * (1 - frequency deme) ^ ancestral deme

/-- One deme's factor in a product Bernstein polynomial. -/
noncomputable def manyDemeBernsteinPolynomialFactor {D : ℕ} (deme : Fin D)
    (derived ancestral : ℕ) : MvPolynomial (Fin D) ℝ :=
  MvPolynomial.X deme ^ derived * (1 - MvPolynomial.X deme) ^ ancestral

/-- The same product Bernstein basis element as a multivariate real polynomial.  This lift
lets a pointwise generator identity become a coefficient-level identity by polynomial
extensionality, which is the bridge needed for finite moment-matrix intertwining. -/
noncomputable def manyDemeBernsteinPolynomial {D : ℕ}
    (derived ancestral : Fin D → ℕ) : MvPolynomial (Fin D) ℝ :=
  ∏ deme, manyDemeBernsteinPolynomialFactor deme (derived deme) (ancestral deme)

/-- Evaluating the polynomial lift recovers exactly the numerical Bernstein weight. -/
theorem eval_manyDemeBernsteinPolynomial {D : ℕ} (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) :
    MvPolynomial.eval frequency (manyDemeBernsteinPolynomial derived ancestral) =
      manyDemeBernsteinWeight frequency derived ancestral := by
  classical
  unfold manyDemeBernsteinPolynomial manyDemeBernsteinWeight
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro deme _
  simp [manyDemeBernsteinPolynomialFactor]

/-- A partial derivative in one deme annihilates every different deme's Bernstein factor. -/
theorem pderiv_manyDemeBernsteinPolynomialFactor_of_ne {D : ℕ}
    (different deme : Fin D) (derived ancestral : ℕ) (distinct : different ≠ deme) :
    MvPolynomial.pderiv deme
        (manyDemeBernsteinPolynomialFactor different derived ancestral) = 0 := by
  simp [manyDemeBernsteinPolynomialFactor, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_of_ne distinct]

/-- A Bernstein polynomial with no ancestral labels is exactly the corresponding monomial. -/
theorem manyDemeBernsteinPolynomial_zeroAncestral_eq_monomial {D : ℕ}
    (exponent : Fin D → ℕ) :
    manyDemeBernsteinPolynomial exponent (fun _ ↦ 0) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm exponent) 1 := by
  classical
  simp [manyDemeBernsteinPolynomial, manyDemeBernsteinPolynomialFactor,
    MvPolynomial.monomial_eq, Finsupp.prod]
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro deme _ absent
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at absent
  simp [absent]

/-- One Bernstein factor has total degree at most the number of its two lineage labels. -/
theorem manyDemeBernsteinPolynomialFactor_totalDegree_le {D : ℕ} (deme : Fin D)
    (derived ancestral : ℕ) :
    (manyDemeBernsteinPolynomialFactor deme derived ancestral).totalDegree ≤
      derived + ancestral := by
  unfold manyDemeBernsteinPolynomialFactor
  calc
    _ ≤ (MvPolynomial.X deme ^ derived : MvPolynomial (Fin D) ℝ).totalDegree +
        ((1 - MvPolynomial.X deme) ^ ancestral : MvPolynomial (Fin D) ℝ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ derived + ancestral := by
      apply Nat.add_le_add
      · simp
      · exact (MvPolynomial.totalDegree_pow _ _).trans (by
          have hbase : (1 - MvPolynomial.X deme : MvPolynomial (Fin D) ℝ).totalDegree ≤ 1 :=
            (MvPolynomial.totalDegree_sub _ _).trans (by simp)
          nlinarith)

/-- A product Bernstein polynomial never exceeds its total lineage degree. -/
theorem manyDemeBernsteinPolynomial_totalDegree_le {D : ℕ}
    (derived ancestral : Fin D → ℕ) :
    (manyDemeBernsteinPolynomial derived ancestral).totalDegree ≤
      (∑ deme, derived deme) + ∑ deme, ancestral deme := by
  unfold manyDemeBernsteinPolynomial
  calc
    _ ≤ ∑ deme, (manyDemeBernsteinPolynomialFactor deme
        (derived deme) (ancestral deme)).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ deme, (derived deme + ancestral deme) := by
      apply Finset.sum_le_sum
      intro deme _
      exact manyDemeBernsteinPolynomialFactor_totalDegree_le deme _ _
    _ = _ := by rw [Finset.sum_add_distrib]

/-- A partial derivative annihilates a product of factors whose indices exclude its deme. -/
theorem pderiv_manyDemeBernsteinPolynomial_prod_of_not_mem {D : ℕ}
    (deme : Fin D) (derived ancestral : Fin D → ℕ) (demes : Finset (Fin D))
    (absent : deme ∉ demes) :
    MvPolynomial.pderiv deme
        (∏ different ∈ demes,
          manyDemeBernsteinPolynomialFactor different
            (derived different) (ancestral different)) = 0 := by
  classical
  induction demes using Finset.induction_on with
  | empty => simp [MvPolynomial.pderiv_one]
  | @insert different demes fresh ih =>
      have different_ne : different ≠ deme := by
        intro equal
        subst different
        exact absent (Finset.mem_insert_self deme demes)
      have deme_absent : deme ∉ demes := by
        exact fun member ↦ absent (Finset.mem_insert_of_mem member)
      rw [Finset.prod_insert fresh, MvPolynomial.pderiv_mul,
        pderiv_manyDemeBernsteinPolynomialFactor_of_ne different deme
          (derived different) (ancestral different) different_ne,
        ih deme_absent]
      simp

/-- Exact derivative of the one-deme Bernstein factor, including zero boundary exponents. -/
theorem pderiv_manyDemeBernsteinPolynomialFactor_self {D : ℕ}
    (deme : Fin D) (derived ancestral : ℕ) :
    MvPolynomial.pderiv deme
        (manyDemeBernsteinPolynomialFactor deme derived ancestral) =
      MvPolynomial.C (derived : ℝ) *
          manyDemeBernsteinPolynomialFactor deme (derived - 1) ancestral -
        MvPolynomial.C (ancestral : ℝ) *
          manyDemeBernsteinPolynomialFactor deme derived (ancestral - 1) := by
  simp [manyDemeBernsteinPolynomialFactor, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_pow]
  ring

/-- Multiplying after removing one positive derived exponent restores the original
Bernstein weight. -/
theorem frequency_mul_manyDemeBernsteinWeight_decrementDerived {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D)
    (positive : 0 < derived deme) :
    frequency deme * manyDemeBernsteinWeight frequency
        (decrementExponent derived deme) ancestral =
      manyDemeBernsteinWeight frequency derived ancestral := by
  unfold manyDemeBernsteinWeight
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
  have hrest :
      (∏ x ∈ Finset.univ \ {deme},
        frequency x ^ decrementExponent derived deme x *
          (1 - frequency x) ^ ancestral x) =
      ∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x * (1 - frequency x) ^ ancestral x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ deme := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hx).2
    simp [decrementExponent, hne]
  rw [hrest]
  simp only [decrementExponent, if_pos]
  have hpow : frequency deme ^ derived deme =
      frequency deme ^ (derived deme - 1) * frequency deme := by
    conv_lhs => rw [show derived deme = derived deme - 1 + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  ring

/-- Multiplying by the complement after removing one positive ancestral exponent restores
the original Bernstein weight. -/
theorem complement_mul_manyDemeBernsteinWeight_decrementAncestral {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D)
    (positive : 0 < ancestral deme) :
    (1 - frequency deme) * manyDemeBernsteinWeight frequency derived
        (decrementExponent ancestral deme) =
      manyDemeBernsteinWeight frequency derived ancestral := by
  unfold manyDemeBernsteinWeight
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
  have hrest :
      (∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x *
          (1 - frequency x) ^ decrementExponent ancestral deme x) =
      ∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x * (1 - frequency x) ^ ancestral x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ deme := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hx).2
    simp [decrementExponent, hne]
  rw [hrest]
  simp only [decrementExponent, if_pos]
  have hpow : (1 - frequency deme) ^ ancestral deme =
      (1 - frequency deme) ^ (ancestral deme - 1) * (1 - frequency deme) := by
    conv_lhs => rw [show ancestral deme = ancestral deme - 1 + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  ring

/-- Multiplication by one deme frequency raises its derived-lineage exponent. -/
theorem frequency_mul_manyDemeBernsteinWeight_eq_incrementDerived {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    frequency deme * manyDemeBernsteinWeight frequency derived ancestral =
      manyDemeBernsteinWeight frequency (incrementExponent derived deme) ancestral := by
  unfold manyDemeBernsteinWeight
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
  have hrest :
      (∏ x ∈ Finset.univ \ {deme},
        frequency x ^ incrementExponent derived deme x *
          (1 - frequency x) ^ ancestral x) =
      ∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x * (1 - frequency x) ^ ancestral x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ deme := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hx).2
    simp [incrementExponent, hne]
  rw [hrest]
  simp only [incrementExponent, if_pos, pow_succ]
  ring

/-- Multiplication by one deme complement raises its ancestral-lineage exponent. -/
theorem complement_mul_manyDemeBernsteinWeight_eq_incrementAncestral {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    (1 - frequency deme) * manyDemeBernsteinWeight frequency derived ancestral =
      manyDemeBernsteinWeight frequency derived (incrementExponent ancestral deme) := by
  unfold manyDemeBernsteinWeight
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
  have hrest :
      (∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x *
          (1 - frequency x) ^ incrementExponent ancestral deme x) =
      ∏ x ∈ Finset.univ \ {deme},
        frequency x ^ derived x * (1 - frequency x) ^ ancestral x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ deme := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hx).2
    simp [incrementExponent, hne]
  rw [hrest]
  simp only [incrementExponent, if_pos, pow_succ]
  ring

/-- Adding one ancestral label is exactly subtraction of the same basis element with one
additional derived label.  This is the multivariate polynomial identity
`B(d,a+eᵢ) = B(d,a) - B(d+eᵢ,a)` and does not require a frequency-domain assumption. -/
theorem manyDemeBernsteinPolynomial_incrementAncestral {D : ℕ}
    (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    manyDemeBernsteinPolynomial derived (incrementExponent ancestral deme) =
      manyDemeBernsteinPolynomial derived ancestral -
        manyDemeBernsteinPolynomial (incrementExponent derived deme) ancestral := by
  apply MvPolynomial.funext
  intro frequency
  simp only [map_sub, eval_manyDemeBernsteinPolynomial]
  rw [← complement_mul_manyDemeBernsteinWeight_eq_incrementAncestral frequency
    derived ancestral deme,
    ← frequency_mul_manyDemeBernsteinWeight_eq_incrementDerived frequency
      derived ancestral deme]
  ring

/-- Moving one positive count between distinct demes is decrement followed by increment. -/
theorem migrateExponent_eq_increment_decrement {D : ℕ}
    (exponent : Fin D → ℕ) (src dst : Fin D) (distinct : src ≠ dst) :
    migrateExponent exponent src dst =
      incrementExponent (decrementExponent exponent src) dst := by
  funext deme
  by_cases hsrc : deme = src
  · subst deme
    simp [migrateExponent, decrementExponent, incrementExponent, distinct]
  · by_cases hdst : deme = dst
    · subst deme
      have hreverse : dst ≠ src := fun h ↦ distinct h.symm
      simp [migrateExponent, decrementExponent, incrementExponent, distinct, hreverse]
    · simp [migrateExponent, decrementExponent, incrementExponent, hsrc, hdst]

/-- Moving one positive lineage along a genuine edge preserves total lineage degree. -/
theorem sum_migrateExponent {D : ℕ} (exponent : Fin D → ℕ) (src dst : Fin D)
    (distinct : src ≠ dst) (positive : 0 < exponent src) :
    ∑ d, migrateExponent exponent src dst d = ∑ d, exponent d := by
  rw [migrateExponent_eq_increment_decrement exponent src dst distinct,
    sum_incrementExponent, sum_decrementExponent _ src positive]
  have totalPositive : 0 < ∑ d, exponent d := by
    exact lt_of_lt_of_le positive
      (Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d)) (Finset.mem_univ src))
  omega

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

/-- Positive derived-lineage migration has an exact Bernstein weight identity. -/
theorem frequency_mul_manyDemeBernsteinWeight_decrementDerived_eq_migrate {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (src dst : Fin D)
    (distinct : src ≠ dst) :
    frequency dst * manyDemeBernsteinWeight frequency
        (decrementExponent derived src) ancestral =
      manyDemeBernsteinWeight frequency (migrateExponent derived src dst) ancestral := by
  rw [migrateExponent_eq_increment_decrement derived src dst distinct,
    frequency_mul_manyDemeBernsteinWeight_eq_incrementDerived]

/-- Positive ancestral-lineage migration has the complementary weight identity. -/
theorem complement_mul_manyDemeBernsteinWeight_decrementAncestral_eq_migrate {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (src dst : Fin D)
    (distinct : src ≠ dst) :
    (1 - frequency dst) * manyDemeBernsteinWeight frequency derived
        (decrementExponent ancestral src) =
      manyDemeBernsteinWeight frequency derived (migrateExponent ancestral src dst) := by
  rw [migrateExponent_eq_increment_decrement ancestral src dst distinct,
    complement_mul_manyDemeBernsteinWeight_eq_incrementAncestral]

/-- First partial derivative of a Bernstein weight, written without division or negative
exponents. -/
noncomputable def manyDemeBernsteinFirstDerivative {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) : ℝ :=
  derived deme * manyDemeBernsteinWeight frequency
      (decrementExponent derived deme) ancestral -
    ancestral deme * manyDemeBernsteinWeight frequency derived
      (decrementExponent ancestral deme)

/-- Second partial derivative of a Bernstein weight. -/
noncomputable def manyDemeBernsteinSecondDerivative {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) : ℝ :=
  ((derived deme * (derived deme - 1) : ℕ) : ℝ) *
      manyDemeBernsteinWeight frequency
        (decrementExponent (decrementExponent derived deme) deme) ancestral -
    2 * derived deme * ancestral deme *
      manyDemeBernsteinWeight frequency (decrementExponent derived deme)
        (decrementExponent ancestral deme) +
    ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) *
      manyDemeBernsteinWeight frequency derived
        (decrementExponent (decrementExponent ancestral deme) deme)

/-- Division-free first derivative formula lifted into the multivariate polynomial ring. -/
noncomputable def manyDemeBernsteinFirstDerivativePolynomial {D : ℕ}
    (derived ancestral : Fin D → ℕ) (deme : Fin D) : MvPolynomial (Fin D) ℝ :=
  MvPolynomial.C (derived deme : ℝ) *
      manyDemeBernsteinPolynomial (decrementExponent derived deme) ancestral -
    MvPolynomial.C (ancestral deme : ℝ) *
      manyDemeBernsteinPolynomial derived (decrementExponent ancestral deme)

/-- Division-free second derivative formula lifted into the polynomial ring. -/
noncomputable def manyDemeBernsteinSecondDerivativePolynomial {D : ℕ}
    (derived ancestral : Fin D → ℕ) (deme : Fin D) : MvPolynomial (Fin D) ℝ :=
  MvPolynomial.C (((derived deme * (derived deme - 1) : ℕ) : ℝ)) *
      manyDemeBernsteinPolynomial
        (decrementExponent (decrementExponent derived deme) deme) ancestral -
    MvPolynomial.C (2 * derived deme * ancestral deme : ℝ) *
      manyDemeBernsteinPolynomial (decrementExponent derived deme)
        (decrementExponent ancestral deme) +
    MvPolynomial.C (((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ)) *
      manyDemeBernsteinPolynomial derived
        (decrementExponent (decrementExponent ancestral deme) deme)

/-- The explicit first-derivative polynomial is the genuine partial derivative of the product
Bernstein polynomial. -/
theorem pderiv_manyDemeBernsteinPolynomial {D : ℕ}
    (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    MvPolynomial.pderiv deme (manyDemeBernsteinPolynomial derived ancestral) =
      manyDemeBernsteinFirstDerivativePolynomial derived ancestral deme := by
  classical
  let rest := ∏ different ∈ Finset.univ \ {deme},
    manyDemeBernsteinPolynomialFactor different
      (derived different) (ancestral different)
  have original_split : manyDemeBernsteinPolynomial derived ancestral =
      manyDemeBernsteinPolynomialFactor deme (derived deme) (ancestral deme) * rest := by
    unfold manyDemeBernsteinPolynomial rest
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
  have rest_derivative : MvPolynomial.pderiv deme rest = 0 := by
    apply pderiv_manyDemeBernsteinPolynomial_prod_of_not_mem
    simp
  have derived_split :
      manyDemeBernsteinPolynomial (decrementExponent derived deme) ancestral =
        manyDemeBernsteinPolynomialFactor deme (derived deme - 1) (ancestral deme) * rest := by
    unfold manyDemeBernsteinPolynomial rest
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
    simp only [decrementExponent, if_pos]
    congr 1
    apply Finset.prod_congr rfl
    intro different member
    have distinct : different ≠ deme :=
      Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
    simp [decrementExponent, distinct]
  have ancestral_split :
      manyDemeBernsteinPolynomial derived (decrementExponent ancestral deme) =
        manyDemeBernsteinPolynomialFactor deme (derived deme) (ancestral deme - 1) * rest := by
    unfold manyDemeBernsteinPolynomial rest
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ deme)]
    simp only [decrementExponent, if_pos]
    congr 1
    apply Finset.prod_congr rfl
    intro different member
    have distinct : different ≠ deme :=
      Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
    simp [decrementExponent, distinct]
  rw [original_split, MvPolynomial.pderiv_mul,
    pderiv_manyDemeBernsteinPolynomialFactor_self, rest_derivative]
  unfold manyDemeBernsteinFirstDerivativePolynomial
  rw [derived_split, ancestral_split]
  ring

/-- The explicit second-derivative polynomial is the iterated genuine partial derivative. -/
theorem pderiv_pderiv_manyDemeBernsteinPolynomial {D : ℕ}
    (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    MvPolynomial.pderiv deme
        (MvPolynomial.pderiv deme (manyDemeBernsteinPolynomial derived ancestral)) =
      manyDemeBernsteinSecondDerivativePolynomial derived ancestral deme := by
  rw [pderiv_manyDemeBernsteinPolynomial]
  unfold manyDemeBernsteinFirstDerivativePolynomial
  rw [map_sub, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C_mul,
    pderiv_manyDemeBernsteinPolynomial, pderiv_manyDemeBernsteinPolynomial]
  unfold manyDemeBernsteinFirstDerivativePolynomial
    manyDemeBernsteinSecondDerivativePolynomial
  simp only [decrementExponent, if_pos, Nat.cast_mul, map_mul, map_ofNat]
  ring

/-- Polynomial evaluation commutes with the explicit first-derivative lift. -/
theorem eval_manyDemeBernsteinFirstDerivativePolynomial {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    MvPolynomial.eval frequency
        (manyDemeBernsteinFirstDerivativePolynomial derived ancestral deme) =
      manyDemeBernsteinFirstDerivative frequency derived ancestral deme := by
  simp [manyDemeBernsteinFirstDerivativePolynomial, manyDemeBernsteinFirstDerivative,
    eval_manyDemeBernsteinPolynomial]

/-- Polynomial evaluation commutes with the explicit second-derivative lift. -/
theorem eval_manyDemeBernsteinSecondDerivativePolynomial {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    MvPolynomial.eval frequency
        (manyDemeBernsteinSecondDerivativePolynomial derived ancestral deme) =
      manyDemeBernsteinSecondDerivative frequency derived ancestral deme := by
  simp [manyDemeBernsteinSecondDerivativePolynomial, manyDemeBernsteinSecondDerivative,
    eval_manyDemeBernsteinPolynomial]

/-- Two like-type derived lineages coalesce, while the complementary factor supplies the
diagonal subtraction. -/
theorem bernsteinWeight_derivedCoalescence_identity {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    ((derived deme * (derived deme - 1) : ℕ) : ℝ) * frequency deme *
        (1 - frequency deme) *
        manyDemeBernsteinWeight frequency
          (decrementExponent (decrementExponent derived deme) deme) ancestral =
      ((derived deme * (derived deme - 1) : ℕ) : ℝ) *
        (manyDemeBernsteinWeight frequency (decrementExponent derived deme) ancestral -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases htwo : 2 ≤ derived deme
  · have hone : 0 < derived deme := by omega
    have hdecrement : 0 < decrementExponent derived deme deme := by
      simp [decrementExponent]
      omega
    have hfirst := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
      (decrementExponent derived deme) ancestral deme hdecrement
    have hsecond := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
      derived ancestral deme hone
    calc
      _ = ((derived deme * (derived deme - 1) : ℕ) : ℝ) *
          (1 - frequency deme) *
          (frequency deme * manyDemeBernsteinWeight frequency
            (decrementExponent (decrementExponent derived deme) deme) ancestral) := by ring
      _ = ((derived deme * (derived deme - 1) : ℕ) : ℝ) *
          (1 - frequency deme) *
          manyDemeBernsteinWeight frequency (decrementExponent derived deme) ancestral := by
            rw [hfirst]
      _ = ((derived deme * (derived deme - 1) : ℕ) : ℝ) *
          (manyDemeBernsteinWeight frequency (decrementExponent derived deme) ancestral -
            frequency deme * manyDemeBernsteinWeight frequency
              (decrementExponent derived deme) ancestral) := by ring
      _ = _ := by rw [hsecond]
  · have hsmall : derived deme = 0 ∨ derived deme = 1 := by omega
    rcases hsmall with hzero | hone
    · simp [hzero]
    · simp [hone]

/-- The analogous coalescence identity for ancestral lineages. -/
theorem bernsteinWeight_ancestralCoalescence_identity {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) * frequency deme *
        (1 - frequency deme) *
        manyDemeBernsteinWeight frequency derived
          (decrementExponent (decrementExponent ancestral deme) deme) =
      ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) *
        (manyDemeBernsteinWeight frequency derived (decrementExponent ancestral deme) -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases htwo : 2 ≤ ancestral deme
  · have hone : 0 < ancestral deme := by omega
    have hdecrement : 0 < decrementExponent ancestral deme deme := by
      simp [decrementExponent]
      omega
    have hfirst := complement_mul_manyDemeBernsteinWeight_decrementAncestral frequency
      derived (decrementExponent ancestral deme) deme hdecrement
    have hsecond := complement_mul_manyDemeBernsteinWeight_decrementAncestral frequency
      derived ancestral deme hone
    calc
      _ = ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) * frequency deme *
          ((1 - frequency deme) * manyDemeBernsteinWeight frequency derived
            (decrementExponent (decrementExponent ancestral deme) deme)) := by ring
      _ = ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) * frequency deme *
          manyDemeBernsteinWeight frequency derived
            (decrementExponent ancestral deme) := by rw [hfirst]
      _ = ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) *
          (manyDemeBernsteinWeight frequency derived (decrementExponent ancestral deme) -
            (1 - frequency deme) * manyDemeBernsteinWeight frequency derived
              (decrementExponent ancestral deme)) := by ring
      _ = _ := by rw [hsecond]
  · have hsmall : ancestral deme = 0 ∨ ancestral deme = 1 := by omega
    rcases hsmall with hzero | hone
    · simp [hzero]
    · simp [hone]

/-- A derived/ancestral pair in the same deme is incompatible after coalescence; its rate is
therefore killing rather than a transition to another Bernstein state. -/
theorem bernsteinWeight_oppositeCoalescence_identity {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    (derived deme * ancestral deme : ℕ) * frequency deme * (1 - frequency deme) *
        manyDemeBernsteinWeight frequency (decrementExponent derived deme)
          (decrementExponent ancestral deme) =
      (derived deme * ancestral deme : ℕ) *
        manyDemeBernsteinWeight frequency derived ancestral := by
  by_cases hderived : 0 < derived deme
  · by_cases hancestral : 0 < ancestral deme
    · have hfirst := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
        derived (decrementExponent ancestral deme) deme hderived
      have hsecond := complement_mul_manyDemeBernsteinWeight_decrementAncestral frequency
        derived ancestral deme hancestral
      calc
        _ = (derived deme * ancestral deme : ℕ) * (1 - frequency deme) *
            (frequency deme * manyDemeBernsteinWeight frequency
              (decrementExponent derived deme) (decrementExponent ancestral deme)) := by ring
        _ = (derived deme * ancestral deme : ℕ) * (1 - frequency deme) *
            manyDemeBernsteinWeight frequency derived
              (decrementExponent ancestral deme) := by rw [hfirst]
        _ = (derived deme * ancestral deme : ℕ) *
            ((1 - frequency deme) * manyDemeBernsteinWeight frequency derived
              (decrementExponent ancestral deme)) := by ring
        _ = _ := by rw [hsecond]
    · have : ancestral deme = 0 := Nat.eq_zero_of_not_pos hancestral
      simp [this]
  · have : derived deme = 0 := Nat.eq_zero_of_not_pos hderived
    simp [this]

/-- The analytic migration drift of derived lineages is exactly the positive lineage-label
transition in the Bernstein basis. -/
theorem bernsteinWeight_derivedMigration_identity {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) (src dst : Fin D) :
    rates.migration src dst * derived src * (frequency dst - frequency src) *
        manyDemeBernsteinWeight frequency (decrementExponent derived src) ancestral =
      rates.migration src dst * derived src *
        (manyDemeBernsteinWeight frequency (migrateExponent derived src dst) ancestral -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases distinct : src ≠ dst
  · by_cases positive : 0 < derived src
    · have hmoved :=
        frequency_mul_manyDemeBernsteinWeight_decrementDerived_eq_migrate frequency
          derived ancestral src dst distinct
      have horiginal := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
        derived ancestral src positive
      calc
        _ = rates.migration src dst * derived src *
            (frequency dst * manyDemeBernsteinWeight frequency
                (decrementExponent derived src) ancestral -
              frequency src * manyDemeBernsteinWeight frequency
                (decrementExponent derived src) ancestral) := by ring
        _ = _ := by rw [hmoved, horiginal]
    · have hzero : derived src = 0 := Nat.eq_zero_of_not_pos positive
      simp [hzero]
  · have heq : src = dst := not_ne_iff.mp distinct
    subst dst
    simp [rates.migration_self]

/-- The analytic migration drift of ancestral lineages is the same positive label transition,
with allele complements reversing the frequency difference. -/
theorem bernsteinWeight_ancestralMigration_identity {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) (src dst : Fin D) :
    -(rates.migration src dst * ancestral src * (frequency dst - frequency src) *
        manyDemeBernsteinWeight frequency derived (decrementExponent ancestral src)) =
      rates.migration src dst * ancestral src *
        (manyDemeBernsteinWeight frequency derived (migrateExponent ancestral src dst) -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases distinct : src ≠ dst
  · by_cases positive : 0 < ancestral src
    · have hmoved :=
        complement_mul_manyDemeBernsteinWeight_decrementAncestral_eq_migrate frequency
          derived ancestral src dst distinct
      have horiginal := complement_mul_manyDemeBernsteinWeight_decrementAncestral frequency
        derived ancestral src positive
      calc
        _ = rates.migration src dst * ancestral src *
            ((1 - frequency dst) * manyDemeBernsteinWeight frequency derived
                (decrementExponent ancestral src) -
              (1 - frequency src) * manyDemeBernsteinWeight frequency derived
                (decrementExponent ancestral src)) := by ring
        _ = _ := by rw [hmoved, horiginal]
    · have hzero : ancestral src = 0 := Nat.eq_zero_of_not_pos positive
      simp [hzero]
  · have heq : src = dst := not_ne_iff.mp distinct
    subst dst
    simp [rates.migration_self]

/-- Under symmetric recurrent mutation, a derived dual lineage flips to ancestral with a
positive rate. -/
theorem bernsteinWeight_derivedMutation_identity {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    derived deme * (1 - 2 * frequency deme) *
        manyDemeBernsteinWeight frequency (decrementExponent derived deme) ancestral =
      derived deme *
        (manyDemeBernsteinWeight frequency (decrementExponent derived deme)
            (incrementExponent ancestral deme) -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases positive : 0 < derived deme
  · have hflip := complement_mul_manyDemeBernsteinWeight_eq_incrementAncestral frequency
      (decrementExponent derived deme) ancestral deme
    have horiginal := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
      derived ancestral deme positive
    calc
      _ = derived deme *
          ((1 - frequency deme) * manyDemeBernsteinWeight frequency
              (decrementExponent derived deme) ancestral -
            frequency deme * manyDemeBernsteinWeight frequency
              (decrementExponent derived deme) ancestral) := by ring
      _ = _ := by rw [hflip, horiginal]
  · have hzero : derived deme = 0 := Nat.eq_zero_of_not_pos positive
    simp [hzero]

/-- Under symmetric recurrent mutation, an ancestral dual lineage flips to derived with a
positive rate. -/
theorem bernsteinWeight_ancestralMutation_identity {D : ℕ}
    (frequency : Fin D → ℝ) (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    -(ancestral deme * (1 - 2 * frequency deme) *
        manyDemeBernsteinWeight frequency derived (decrementExponent ancestral deme)) =
      ancestral deme *
        (manyDemeBernsteinWeight frequency (incrementExponent derived deme)
            (decrementExponent ancestral deme) -
          manyDemeBernsteinWeight frequency derived ancestral) := by
  by_cases positive : 0 < ancestral deme
  · have hflip := frequency_mul_manyDemeBernsteinWeight_eq_incrementDerived frequency
      derived (decrementExponent ancestral deme) deme
    have horiginal := complement_mul_manyDemeBernsteinWeight_decrementAncestral frequency
      derived ancestral deme positive
    calc
      _ = ancestral deme *
          (frequency deme * manyDemeBernsteinWeight frequency derived
              (decrementExponent ancestral deme) -
            (1 - frequency deme) * manyDemeBernsteinWeight frequency derived
              (decrementExponent ancestral deme)) := by ring
      _ = _ := by rw [hflip, horiginal]
  · have hzero : ancestral deme = 0 := Nat.eq_zero_of_not_pos positive
    simp [hzero]

/-- The diffusion channel at one deme is exactly two positive like-type coalescence
transitions plus killing at the opposite-type collision rate. -/
theorem bernsteinWeight_coalescenceChannel_identity {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) (deme : Fin D) :
    rates.coalescence deme / 2 * frequency deme * (1 - frequency deme) *
        manyDemeBernsteinSecondDerivative frequency derived ancestral deme =
      rates.coalescence deme *
          ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
          (manyDemeBernsteinWeight frequency (decrementExponent derived deme) ancestral -
            manyDemeBernsteinWeight frequency derived ancestral) +
        rates.coalescence deme *
          ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
          (manyDemeBernsteinWeight frequency derived (decrementExponent ancestral deme) -
            manyDemeBernsteinWeight frequency derived ancestral) -
        rates.coalescence deme * derived deme * ancestral deme *
          manyDemeBernsteinWeight frequency derived ancestral := by
  have hderived := bernsteinWeight_derivedCoalescence_identity frequency
    derived ancestral deme
  have hancestral := bernsteinWeight_ancestralCoalescence_identity frequency
    derived ancestral deme
  have hopposite := bernsteinWeight_oppositeCoalescence_identity frequency
    derived ancestral deme
  unfold manyDemeBernsteinSecondDerivative
  simp only [Nat.cast_mul] at hderived hancestral hopposite ⊢
  linear_combination
    (rates.coalescence deme / 2) * hderived +
    (rates.coalescence deme / 2) * hancestral -
    rates.coalescence deme * hopposite

/-- The diffusion migration channel at one ordered edge is exactly independent positive
migration of derived and ancestral dual lineages. -/
theorem bernsteinWeight_migrationChannel_identity {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) (src dst : Fin D) :
    rates.migration src dst * (frequency dst - frequency src) *
        manyDemeBernsteinFirstDerivative frequency derived ancestral src =
      rates.migration src dst * derived src *
          (manyDemeBernsteinWeight frequency (migrateExponent derived src dst) ancestral -
            manyDemeBernsteinWeight frequency derived ancestral) +
        rates.migration src dst * ancestral src *
          (manyDemeBernsteinWeight frequency derived (migrateExponent ancestral src dst) -
            manyDemeBernsteinWeight frequency derived ancestral) := by
  have hderived := bernsteinWeight_derivedMigration_identity rates frequency
    derived ancestral src dst
  have hancestral := bernsteinWeight_ancestralMigration_identity rates frequency
    derived ancestral src dst
  unfold manyDemeBernsteinFirstDerivative
  rw [← hderived, ← hancestral]
  ring

/-- With equal forward and backward mutation rates, the analytic mutation drift is exactly
positive label flipping in both directions. -/
theorem bernsteinWeight_symmetricMutationChannel_identity {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) (deme : Fin D)
    (symmetric : rates.backwardMutation deme = rates.forwardMutation deme) :
    (rates.forwardMutation deme * (1 - frequency deme) -
        rates.backwardMutation deme * frequency deme) *
        manyDemeBernsteinFirstDerivative frequency derived ancestral deme =
      rates.forwardMutation deme * derived deme *
          (manyDemeBernsteinWeight frequency (decrementExponent derived deme)
              (incrementExponent ancestral deme) -
            manyDemeBernsteinWeight frequency derived ancestral) +
        rates.forwardMutation deme * ancestral deme *
          (manyDemeBernsteinWeight frequency (incrementExponent derived deme)
              (decrementExponent ancestral deme) -
            manyDemeBernsteinWeight frequency derived ancestral) := by
  have hderived := bernsteinWeight_derivedMutation_identity frequency
    derived ancestral deme
  have hancestral := bernsteinWeight_ancestralMutation_identity frequency
    derived ancestral deme
  unfold manyDemeBernsteinFirstDerivative
  rw [symmetric]
  linear_combination
    rates.forwardMutation deme * hderived +
    rates.forwardMutation deme * hancestral

/-- The structured Wright--Fisher diffusion generator applied analytically to one Bernstein
basis weight.  The displayed first and second derivatives contain no division and remain
valid at boundary exponents. -/
noncomputable def manyDemeBernsteinAnalyticGenerator {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  (∑ deme, rates.coalescence deme / 2 * frequency deme * (1 - frequency deme) *
      manyDemeBernsteinSecondDerivative frequency derived ancestral deme) +
  (∑ src, ∑ dst, rates.migration src dst * (frequency dst - frequency src) *
      manyDemeBernsteinFirstDerivative frequency derived ancestral src) +
  ∑ deme, (rates.forwardMutation deme * (1 - frequency deme) -
      rates.backwardMutation deme * frequency deme) *
      manyDemeBernsteinFirstDerivative frequency derived ancestral deme

/-- Positive killed structured-coalescent generator on derived/ancestral lineage counts.

Like-type pairs coalesce; individual labels migrate; symmetric recurrent mutation flips a
lineage's allele label; and an opposite-type pair in one deme is killed at rate
`coalescence * derived * ancestral`.  Every off-diagonal coefficient is nonnegative under the
typed rate assumptions. -/
noncomputable def manyDemeKilledDualGenerator {D : ℕ}
    (rates : ManyDemeRates D)
    (value : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  (∑ deme, (
      rates.coalescence deme *
          ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
          (value (decrementExponent derived deme) ancestral - value derived ancestral) +
      rates.coalescence deme *
          ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
          (value derived (decrementExponent ancestral deme) - value derived ancestral) -
      rates.coalescence deme * derived deme * ancestral deme * value derived ancestral)) +
  (∑ src, ∑ dst, (
      rates.migration src dst * derived src *
          (value (migrateExponent derived src dst) ancestral - value derived ancestral) +
      rates.migration src dst * ancestral src *
          (value derived (migrateExponent ancestral src dst) - value derived ancestral))) +
  ∑ deme, (
      rates.forwardMutation deme * derived deme *
          (value (decrementExponent derived deme) (incrementExponent ancestral deme) -
            value derived ancestral) +
      rates.forwardMutation deme * ancestral deme *
          (value (incrementExponent derived deme) (decrementExponent ancestral deme) -
            value derived ancestral))

/-- **Arbitrary-deme positive killed-dual identity.**  For every frequency vector and every
derived/ancestral lineage configuration, the existing structured diffusion generator on the
Bernstein basis is exactly the killed coalescent generator.  This proves—not stipulates—the
sparse positive law used by the MSI two-deme evaluator, and extends it to every finite deme
count and migration matrix. -/
theorem manyDemeBernsteinAnalyticGenerator_eq_killedDual {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemeBernsteinAnalyticGenerator rates frequency derived ancestral =
      manyDemeKilledDualGenerator rates
        (manyDemeBernsteinWeight frequency) derived ancestral := by
  unfold manyDemeBernsteinAnalyticGenerator manyDemeKilledDualGenerator
  simp_rw [bernsteinWeight_coalescenceChannel_identity rates frequency derived ancestral]
  simp_rw [bernsteinWeight_migrationChannel_identity rates frequency derived ancestral]
  simp_rw [bernsteinWeight_symmetricMutationChannel_identity rates frequency derived ancestral
    _ (symmetric _)]

/-- Polynomial lift of the analytic diffusion generator applied to one Bernstein basis
element.  All derivatives are the already-derived division-free polynomials above. -/
noncomputable def manyDemeBernsteinAnalyticGeneratorPolynomial {D : ℕ}
    (rates : ManyDemeRates D) (derived ancestral : Fin D → ℕ) :
    MvPolynomial (Fin D) ℝ :=
  (∑ deme, MvPolynomial.C (rates.coalescence deme / 2) *
      MvPolynomial.X deme * (1 - MvPolynomial.X deme) *
      manyDemeBernsteinSecondDerivativePolynomial derived ancestral deme) +
  (∑ src, ∑ dst, MvPolynomial.C (rates.migration src dst) *
      (MvPolynomial.X dst - MvPolynomial.X src) *
      manyDemeBernsteinFirstDerivativePolynomial derived ancestral src) +
  ∑ deme, (MvPolynomial.C (rates.forwardMutation deme) *
        (1 - MvPolynomial.X deme) -
      MvPolynomial.C (rates.backwardMutation deme) * MvPolynomial.X deme) *
      manyDemeBernsteinFirstDerivativePolynomial derived ancestral deme

/-- The structured Wright--Fisher diffusion generator as a linear operator on arbitrary
multivariate polynomials. -/
noncomputable def manyDemeDiffusionPolynomialGenerator {D : ℕ}
    (rates : ManyDemeRates D) :
    MvPolynomial (Fin D) ℝ →ₗ[ℝ] MvPolynomial (Fin D) ℝ :=
  (∑ deme, (LinearMap.mulLeft ℝ
      (MvPolynomial.C (rates.coalescence deme / 2) *
        MvPolynomial.X deme * (1 - MvPolynomial.X deme))).comp
      ((MvPolynomial.pderiv deme).toLinearMap.comp
        (MvPolynomial.pderiv deme).toLinearMap)) +
  (∑ src, ∑ dst, (LinearMap.mulLeft ℝ
      (MvPolynomial.C (rates.migration src dst) *
        (MvPolynomial.X dst - MvPolynomial.X src))).comp
      (MvPolynomial.pderiv src).toLinearMap) +
  ∑ deme, (LinearMap.mulLeft ℝ
      (MvPolynomial.C (rates.forwardMutation deme) *
          (1 - MvPolynomial.X deme) -
        MvPolynomial.C (rates.backwardMutation deme) * MvPolynomial.X deme)).comp
      (MvPolynomial.pderiv deme).toLinearMap

/-- On a Bernstein basis element, the general polynomial diffusion operator is exactly the
explicit analytic generator polynomial. -/
theorem manyDemeDiffusionPolynomialGenerator_bernstein {D : ℕ}
    (rates : ManyDemeRates D) (derived ancestral : Fin D → ℕ) :
    manyDemeDiffusionPolynomialGenerator rates
        (manyDemeBernsteinPolynomial derived ancestral) =
      manyDemeBernsteinAnalyticGeneratorPolynomial rates derived ancestral := by
  have secondDerivative (deme : Fin D) :
      MvPolynomial.pderiv deme
          (manyDemeBernsteinFirstDerivativePolynomial derived ancestral deme) =
        manyDemeBernsteinSecondDerivativePolynomial derived ancestral deme := by
    rw [← pderiv_manyDemeBernsteinPolynomial,
      pderiv_pderiv_manyDemeBernsteinPolynomial]
  simp [manyDemeDiffusionPolynomialGenerator,
    manyDemeBernsteinAnalyticGeneratorPolynomial,
    pderiv_manyDemeBernsteinPolynomial, secondDerivative]
  ring

/-- Polynomial lift of the positive killed-coalescent generator applied to the Bernstein
basis family. -/
noncomputable def manyDemeKilledDualGeneratorPolynomial {D : ℕ}
    (rates : ManyDemeRates D) (derived ancestral : Fin D → ℕ) :
    MvPolynomial (Fin D) ℝ :=
  (∑ deme, (
      MvPolynomial.C (rates.coalescence deme *
          ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2) *
          (manyDemeBernsteinPolynomial (decrementExponent derived deme) ancestral -
            manyDemeBernsteinPolynomial derived ancestral) +
      MvPolynomial.C (rates.coalescence deme *
          ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2) *
          (manyDemeBernsteinPolynomial derived (decrementExponent ancestral deme) -
            manyDemeBernsteinPolynomial derived ancestral) -
      MvPolynomial.C (rates.coalescence deme * derived deme * ancestral deme) *
        manyDemeBernsteinPolynomial derived ancestral)) +
  (∑ src, ∑ dst, (
      MvPolynomial.C (rates.migration src dst * derived src) *
          (manyDemeBernsteinPolynomial (migrateExponent derived src dst) ancestral -
            manyDemeBernsteinPolynomial derived ancestral) +
      MvPolynomial.C (rates.migration src dst * ancestral src) *
          (manyDemeBernsteinPolynomial derived (migrateExponent ancestral src dst) -
            manyDemeBernsteinPolynomial derived ancestral))) +
  ∑ deme, (
      MvPolynomial.C (rates.forwardMutation deme * derived deme) *
          (manyDemeBernsteinPolynomial (decrementExponent derived deme)
              (incrementExponent ancestral deme) -
            manyDemeBernsteinPolynomial derived ancestral) +
      MvPolynomial.C (rates.forwardMutation deme * ancestral deme) *
          (manyDemeBernsteinPolynomial (incrementExponent derived deme)
              (decrementExponent ancestral deme) -
            manyDemeBernsteinPolynomial derived ancestral))

/-- Evaluation of the analytic generator polynomial is the numerical analytic generator. -/
theorem eval_manyDemeBernsteinAnalyticGeneratorPolynomial {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) :
    MvPolynomial.eval frequency
        (manyDemeBernsteinAnalyticGeneratorPolynomial rates derived ancestral) =
      manyDemeBernsteinAnalyticGenerator rates frequency derived ancestral := by
  simp [manyDemeBernsteinAnalyticGeneratorPolynomial,
    manyDemeBernsteinAnalyticGenerator,
    eval_manyDemeBernsteinFirstDerivativePolynomial,
    eval_manyDemeBernsteinSecondDerivativePolynomial]

/-- Evaluation of the killed-dual polynomial is the numerical killed generator. -/
theorem eval_manyDemeKilledDualGeneratorPolynomial {D : ℕ}
    (rates : ManyDemeRates D) (frequency : Fin D → ℝ)
    (derived ancestral : Fin D → ℕ) :
    MvPolynomial.eval frequency
        (manyDemeKilledDualGeneratorPolynomial rates derived ancestral) =
      manyDemeKilledDualGenerator rates (manyDemeBernsteinWeight frequency)
        derived ancestral := by
  simp [manyDemeKilledDualGeneratorPolynomial, manyDemeKilledDualGenerator,
    eval_manyDemeBernsteinPolynomial]

/-- **Coefficient-level arbitrary-deme duality.**  The analytic diffusion generator and the
positive killed-coalescent generator are the same multivariate polynomial, not merely equal at
chosen frequencies.  Consequently every linear moment functional sees the same generator. -/
theorem manyDemeBernsteinAnalyticGeneratorPolynomial_eq_killedDual {D : ℕ}
    (rates : ManyDemeRates D) (derived ancestral : Fin D → ℕ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemeBernsteinAnalyticGeneratorPolynomial rates derived ancestral =
      manyDemeKilledDualGeneratorPolynomial rates derived ancestral := by
  apply MvPolynomial.funext
  intro frequency
  rw [eval_manyDemeBernsteinAnalyticGeneratorPolynomial,
    eval_manyDemeKilledDualGeneratorPolynomial]
  exact manyDemeBernsteinAnalyticGenerator_eq_killedDual rates frequency
    derived ancestral symmetric

/-- Linear mixed-moment functional on multivariate polynomials. -/
noncomputable def manyDemePolynomialMomentLinearMap {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun exponent ↦
    LinearMap.mulRight ℝ (moment (fun deme ↦ exponent deme))

/-- Apply a multivariate polynomial to an arbitrary mixed-moment table by replacing each
monomial coefficient with the corresponding table entry. -/
noncomputable def manyDemePolynomialMomentFunctional {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (polynomial : MvPolynomial (Fin D) ℝ) : ℝ :=
  manyDemePolynomialMomentLinearMap moment polynomial

/-- The bundled functional is the expected finite coefficient sum. -/
theorem manyDemePolynomialMomentFunctional_eq_sum {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (polynomial : MvPolynomial (Fin D) ℝ) :
    manyDemePolynomialMomentFunctional moment polynomial =
      polynomial.sum fun exponent coefficient ↦
        coefficient * moment (fun deme ↦ exponent deme) := by
  unfold manyDemePolynomialMomentFunctional manyDemePolynomialMomentLinearMap
  rfl

/-- A degree-`K` polynomial moment depends only on mixed moments of total degree at most `K`. -/
theorem manyDemePolynomialMomentFunctional_congr_of_totalDegree_le {D K : ℕ}
    (left right : (Fin D → ℕ) → ℝ) (polynomial : MvPolynomial (Fin D) ℝ)
    (degree_le : polynomial.totalDegree ≤ K)
    (agree : ∀ exponent, (∑ deme, exponent deme) ≤ K → left exponent = right exponent) :
    manyDemePolynomialMomentFunctional left polynomial =
      manyDemePolynomialMomentFunctional right polynomial := by
  rw [manyDemePolynomialMomentFunctional_eq_sum,
    manyDemePolynomialMomentFunctional_eq_sum]
  apply Finset.sum_congr rfl
  intro exponent member
  change polynomial.coeff exponent * left (fun deme ↦ exponent deme) =
    polynomial.coeff exponent * right (fun deme ↦ exponent deme)
  rw [agree (fun deme ↦ exponent deme) (by
    have support_degree := (MvPolynomial.le_totalDegree member).trans degree_le
    simpa [Finsupp.sum_fintype] using support_degree)]

/-- The coefficient-level duality survives every mixed-moment functional.  This is the exact
scalar generator equality needed by each row of the forthcoming Bernstein projection matrix. -/
theorem manyDemeBernsteinGenerator_momentFunctional_eq_killedDual {D : ℕ}
    (rates : ManyDemeRates D) (moment : (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemePolynomialMomentFunctional moment
        (manyDemeBernsteinAnalyticGeneratorPolynomial rates derived ancestral) =
      manyDemePolynomialMomentFunctional moment
        (manyDemeKilledDualGeneratorPolynomial rates derived ancestral) := by
  rw [manyDemeBernsteinAnalyticGeneratorPolynomial_eq_killedDual rates derived ancestral
    symmetric]

/-- Applying any moment functional to the killed polynomial is definitionally the killed
generator applied to the family of Bernstein moment functionals. -/
theorem manyDemePolynomialMomentFunctional_killedGenerator {D : ℕ}
    (rates : ManyDemeRates D) (moment : (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemePolynomialMomentFunctional moment
        (manyDemeKilledDualGeneratorPolynomial rates derived ancestral) =
      manyDemeKilledDualGenerator rates
        (fun a b ↦ manyDemePolynomialMomentFunctional moment
          (manyDemeBernsteinPolynomial a b)) derived ancestral := by
  have scalar_apply (scalar : ℝ) (polynomial : MvPolynomial (Fin D) ℝ) :
      manyDemePolynomialMomentLinearMap moment (MvPolynomial.C scalar * polynomial) =
        scalar * manyDemePolynomialMomentLinearMap moment polynomial := by
    rw [← MvPolynomial.smul_eq_C_mul]
    rw [map_smul]
    rfl
  change (manyDemePolynomialMomentLinearMap moment)
      (manyDemeKilledDualGeneratorPolynomial rates derived ancestral) =
    manyDemeKilledDualGenerator rates
      (fun a b ↦ manyDemePolynomialMomentLinearMap moment
        (manyDemeBernsteinPolynomial a b)) derived ancestral
  simp only [manyDemeKilledDualGeneratorPolynomial, manyDemeKilledDualGenerator,
    map_add, map_sub, map_sum, scalar_apply]

/-- The mixed-moment functional reads a unit monomial as the corresponding table entry. -/
theorem manyDemePolynomialMomentFunctional_monomial_one {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (exponent : Fin D → ℕ) :
    manyDemePolynomialMomentFunctional moment
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm exponent) 1) =
      moment exponent := by
  rw [manyDemePolynomialMomentFunctional_eq_sum, MvPolynomial.sum_monomial_eq] <;> simp

/-- The moment functional of a zero-ancestral Bernstein polynomial is the ordinary mixed
moment at its derived exponent. -/
theorem manyDemePolynomialMomentFunctional_zeroAncestral {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (exponent : Fin D → ℕ) :
    manyDemePolynomialMomentFunctional moment
        (manyDemeBernsteinPolynomial exponent (fun _ ↦ 0)) = moment exponent := by
  rw [manyDemeBernsteinPolynomial_zeroAncestral_eq_monomial,
    manyDemePolynomialMomentFunctional_monomial_one]

/-- The moment functional sends the conventional finite product of variable powers to the
corresponding mixed moment. -/
theorem manyDemePolynomialMomentFunctional_prod_X_pow {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (exponent : Fin D → ℕ) :
    manyDemePolynomialMomentFunctional moment
        (∏ deme, MvPolynomial.X deme ^ exponent deme) = moment exponent := by
  rw [← manyDemePolynomialMomentFunctional_zeroAncestral moment exponent]
  congr 1
  simp [manyDemeBernsteinPolynomial, manyDemeBernsteinPolynomialFactor]

/-- A derived-to-ancestral flip at one positive exponent is exactly the adjacent-moment
difference under an arbitrary mixed-moment functional. -/
theorem manyDemePolynomialMomentFunctional_singleAncestralFlip {D : ℕ}
    (moment : (Fin D → ℕ) → ℝ) (exponent : Fin D → ℕ) (deme : Fin D)
    (positive : 0 < exponent deme) :
    manyDemePolynomialMomentFunctional moment
        (manyDemeBernsteinPolynomial (decrementExponent exponent deme)
          (incrementExponent (fun _ ↦ 0) deme)) =
      moment (decrementExponent exponent deme) - moment exponent := by
  have polynomialIdentity :
      manyDemeBernsteinPolynomial (decrementExponent exponent deme)
          (incrementExponent (fun _ ↦ 0) deme) =
        manyDemeBernsteinPolynomial (decrementExponent exponent deme) (fun _ ↦ 0) -
          manyDemeBernsteinPolynomial exponent (fun _ ↦ 0) := by
    apply MvPolynomial.funext
    intro frequency
    simp only [map_sub, eval_manyDemeBernsteinPolynomial]
    rw [← complement_mul_manyDemeBernsteinWeight_eq_incrementAncestral frequency
      (decrementExponent exponent deme) (fun _ ↦ 0) deme]
    have restore := frequency_mul_manyDemeBernsteinWeight_decrementDerived frequency
      exponent (fun _ ↦ 0) deme positive
    calc
      _ = manyDemeBernsteinWeight frequency (decrementExponent exponent deme) (fun _ ↦ 0) -
          frequency deme * manyDemeBernsteinWeight frequency
            (decrementExponent exponent deme) (fun _ ↦ 0) := by ring
      _ = _ := by rw [restore]
  rw [polynomialIdentity]
  change (manyDemePolynomialMomentLinearMap moment) (_ - _) = _
  rw [map_sub]
  change manyDemePolynomialMomentFunctional moment _ -
      manyDemePolynomialMomentFunctional moment _ = _
  rw [
    manyDemePolynomialMomentFunctional_zeroAncestral,
    manyDemePolynomialMomentFunctional_zeroAncestral]

/-- **Polynomial/moment generator adjoint on monomials.**  Applying the diffusion polynomial
operator to a monomial and then the mixed-moment functional is exactly the existing
arbitrary-deme moment generator.  This is derived through the already-proved Bernstein dual,
including mutation forcing and every migration edge. -/
theorem manyDemePolynomialMomentFunctional_diffusion_monomial {D : ℕ}
    (rates : ManyDemeRates D) (moment : (Fin D → ℕ) → ℝ)
    (exponent : Fin D → ℕ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemePolynomialMomentFunctional moment
        (manyDemeDiffusionPolynomialGenerator rates
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm exponent) 1)) =
      manyDemeMomentGenerator rates moment exponent := by
  rw [← manyDemeBernsteinPolynomial_zeroAncestral_eq_monomial exponent,
    manyDemeDiffusionPolynomialGenerator_bernstein,
    manyDemeBernsteinGenerator_momentFunctional_eq_killedDual rates moment exponent
      (fun _ ↦ 0) symmetric,
    manyDemePolynomialMomentFunctional_killedGenerator]
  unfold manyDemeKilledDualGenerator manyDemeMomentGenerator
  simp_rw [manyDemePolynomialMomentFunctional_zeroAncestral]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_div]
  have flipSum :
      (∑ deme, rates.forwardMutation deme * exponent deme *
          (manyDemePolynomialMomentFunctional moment
              (manyDemeBernsteinPolynomial (decrementExponent exponent deme)
                (incrementExponent (fun _ ↦ 0) deme)) - moment exponent)) =
        ∑ deme, rates.forwardMutation deme * exponent deme *
          ((moment (decrementExponent exponent deme) - moment exponent) -
            moment exponent) := by
    apply Finset.sum_congr rfl
    intro deme _
    by_cases positive : 0 < exponent deme
    · rw [manyDemePolynomialMomentFunctional_singleAncestralFlip moment exponent deme positive]
    · have zero : exponent deme = 0 := by omega
      simp [zero]
  rw [flipSum]
  have mutationSum :
      (∑ deme, rates.forwardMutation deme * exponent deme *
          ((moment (decrementExponent exponent deme) - moment exponent) -
            moment exponent)) =
        ∑ deme, (rates.forwardMutation deme * exponent deme *
            (moment (decrementExponent exponent deme) - moment exponent) -
          rates.backwardMutation deme * exponent deme * moment exponent) := by
    apply Finset.sum_congr rfl
    intro deme _
    rw [symmetric deme]
    ring
  rw [mutationSum]

/-- **Full polynomial/moment adjoint identity.**  The existing moment generator is the exact
linear adjoint of the structured diffusion operator on every multivariate polynomial. -/
theorem manyDemePolynomialMomentFunctional_diffusion {D : ℕ}
    (rates : ManyDemeRates D) (moment : (Fin D → ℕ) → ℝ)
    (polynomial : MvPolynomial (Fin D) ℝ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemePolynomialMomentFunctional
        (manyDemeMomentGenerator rates moment) polynomial =
      manyDemePolynomialMomentFunctional moment
        (manyDemeDiffusionPolynomialGenerator rates polynomial) := by
  let left := manyDemePolynomialMomentLinearMap
    (manyDemeMomentGenerator rates moment)
  let right := (manyDemePolynomialMomentLinearMap moment).comp
    (manyDemeDiffusionPolynomialGenerator rates)
  have maps_equal : left = right := by
    apply MvPolynomial.linearMap_ext
    intro exponent
    apply LinearMap.ext
    intro coefficient
    change left (MvPolynomial.monomial exponent coefficient) =
      right (MvPolynomial.monomial exponent coefficient)
    rw [← show coefficient • MvPolynomial.monomial exponent (1 : ℝ) =
        MvPolynomial.monomial exponent coefficient by
          simp [MvPolynomial.smul_monomial]]
    rw [left.map_smul, right.map_smul]
    have base := (manyDemePolynomialMomentFunctional_diffusion_monomial rates moment
      (fun deme ↦ exponent deme) symmetric).symm
    have baseLR : left (MvPolynomial.monomial exponent 1) =
        right (MvPolynomial.monomial exponent 1) := by
      change manyDemePolynomialMomentFunctional (manyDemeMomentGenerator rates moment)
          (MvPolynomial.monomial exponent 1) =
        manyDemePolynomialMomentFunctional moment
          (manyDemeDiffusionPolynomialGenerator rates
            (MvPolynomial.monomial exponent 1))
      have roundtrip : Finsupp.equivFunOnFinite.symm (fun deme ↦ exponent deme) = exponent :=
        Finsupp.equivFunOnFinite.symm_apply_apply exponent
      rw [← roundtrip, manyDemePolynomialMomentFunctional_monomial_one]
      exact base
    exact congrArg (fun value : ℝ ↦ coefficient • value) baseLR
  exact LinearMap.congr_fun maps_equal polynomial

/-- **Exact unrestricted moment/killed-dual generator intertwining.**  Projecting an arbitrary
mixed-moment table onto any product Bernstein coordinate after one infinitesimal diffusion
step is exactly the positive killed generator applied to all its Bernstein projections. -/
theorem manyDemeMomentGenerator_bernstein_intertwines {D : ℕ}
    (rates : ManyDemeRates D) (moment : (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    manyDemePolynomialMomentFunctional (manyDemeMomentGenerator rates moment)
        (manyDemeBernsteinPolynomial derived ancestral) =
      manyDemeKilledDualGenerator rates
        (fun a b ↦ manyDemePolynomialMomentFunctional moment
          (manyDemeBernsteinPolynomial a b)) derived ancestral := by
  rw [manyDemePolynomialMomentFunctional_diffusion rates moment _ symmetric,
    manyDemeDiffusionPolynomialGenerator_bernstein,
    manyDemeBernsteinGenerator_momentFunctional_eq_killedDual rates moment
      derived ancestral symmetric,
    manyDemePolynomialMomentFunctional_killedGenerator]

/-- Total absorption rate of the positive Bernstein dual.  Absorption occurs exactly when a
derived and an ancestral lineage choose the same coalescing parental lineage in one deme. -/
noncomputable def manyDemeKilledDualKillingRate {D : ℕ} (rates : ManyDemeRates D)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  ∑ deme, rates.coalescence deme * derived deme * ancestral deme

/-- The absorption rate is nonnegative for every lineage configuration. -/
theorem manyDemeKilledDualKillingRate_nonneg {D : ℕ} (rates : ManyDemeRates D)
    (derived ancestral : Fin D → ℕ) :
    0 ≤ manyDemeKilledDualKillingRate rates derived ancestral := by
  unfold manyDemeKilledDualKillingRate
  apply Finset.sum_nonneg
  intro deme _
  exact mul_nonneg
    (mul_nonneg (le_of_lt (rates.coalescence_pos deme)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- Conservative jump part of the positive Bernstein dual.  The killed generator is this
Markov jump generator minus the explicit absorption rate. -/
noncomputable def manyDemeKilledDualJumpGenerator {D : ℕ}
    (rates : ManyDemeRates D)
    (value : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  (∑ deme, (
      rates.coalescence deme *
          ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
          (value (decrementExponent derived deme) ancestral - value derived ancestral) +
      rates.coalescence deme *
          ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
          (value derived (decrementExponent ancestral deme) - value derived ancestral))) +
  (∑ src, ∑ dst, (
      rates.migration src dst * derived src *
          (value (migrateExponent derived src dst) ancestral - value derived ancestral) +
      rates.migration src dst * ancestral src *
          (value derived (migrateExponent ancestral src dst) - value derived ancestral))) +
  ∑ deme, (
      rates.forwardMutation deme * derived deme *
          (value (decrementExponent derived deme) (incrementExponent ancestral deme) -
            value derived ancestral) +
      rates.forwardMutation deme * ancestral deme *
          (value (incrementExponent derived deme) (decrementExponent ancestral deme) -
            value derived ancestral))

/-- Exact conservative-plus-killing decomposition of the arbitrary-deme dual generator. -/
theorem manyDemeKilledDualGenerator_eq_jump_sub_killing {D : ℕ}
    (rates : ManyDemeRates D)
    (value : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemeKilledDualGenerator rates value derived ancestral =
      manyDemeKilledDualJumpGenerator rates value derived ancestral -
        manyDemeKilledDualKillingRate rates derived ancestral * value derived ancestral := by
  unfold manyDemeKilledDualGenerator manyDemeKilledDualJumpGenerator
    manyDemeKilledDualKillingRate
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
  ring

/-- A nonnegative value table that vanishes at the current configuration has a
nonnegative killed-generator derivative there.  This is the coefficient-level positivity
statement behind the Metzler property: killing and all diagonal exit charges disappear at
the zero current value, while every possible destination is charged at a typed
nonnegative rate. -/
theorem manyDemeKilledDualGenerator_nonneg_of_nonneg_of_current_eq_zero {D : ℕ}
    (rates : ManyDemeRates D)
    (value : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ)
    (value_nonneg : ∀ a b, 0 ≤ value a b)
    (current_zero : value derived ancestral = 0) :
    0 ≤ manyDemeKilledDualGenerator rates value derived ancestral := by
  rw [manyDemeKilledDualGenerator_eq_jump_sub_killing, current_zero]
  simp only [mul_zero, sub_zero]
  unfold manyDemeKilledDualJumpGenerator
  rw [current_zero]
  simp only [sub_zero]
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro deme _
      apply add_nonneg
      · exact mul_nonneg
          (div_nonneg
            (mul_nonneg (rates.coalescence_pos deme).le (Nat.cast_nonneg _)) (by norm_num))
          (value_nonneg _ _)
      · exact mul_nonneg
          (div_nonneg
            (mul_nonneg (rates.coalescence_pos deme).le (Nat.cast_nonneg _)) (by norm_num))
          (value_nonneg _ _)
    · apply Finset.sum_nonneg
      intro source _
      apply Finset.sum_nonneg
      intro target _
      apply add_nonneg
      · exact mul_nonneg
          (mul_nonneg (rates.migration_nonneg source target) (Nat.cast_nonneg _))
          (value_nonneg _ _)
      · exact mul_nonneg
          (mul_nonneg (rates.migration_nonneg source target) (Nat.cast_nonneg _))
          (value_nonneg _ _)
  · apply Finset.sum_nonneg
    intro deme _
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (rates.forwardMutation_nonneg deme) (Nat.cast_nonneg _))
        (value_nonneg _ _)
    · exact mul_nonneg
        (mul_nonneg (rates.forwardMutation_nonneg deme) (Nat.cast_nonneg _))
        (value_nonneg _ _)

/-- Finite rectangular carrier for derived/ancestral lineage configurations.  Rows of total
lineage count above `K` are padding; every transition from a biological row of degree at most
`K` remains in the rectangle or is absorbed. -/
abbrev ManyDemeKilledDualCoordinate (D K : ℕ) :=
  (Fin D → Fin (K + 1)) × (Fin D → Fin (K + 1))

/-- Total number of labelled dual lineages in a finite coordinate. -/
def ManyDemeKilledDualCoordinate.degree {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) : ℕ :=
  (∑ deme, (coordinate.1 deme).val) + ∑ deme, (coordinate.2 deme).val

/-- Removing one lineage never leaves the finite coordinate rectangle. -/
theorem decrementExponent_lt_of_fin {D K : ℕ} (exponent : Fin D → Fin (K + 1))
    (deme : Fin D) :
    ∀ other, decrementExponent (fun d ↦ (exponent d).val) deme other < K + 1 := by
  intro other
  by_cases equal : other = deme
  · subst other
    simp [decrementExponent]
    omega
  · simp [decrementExponent, equal, (exponent other).isLt]

/-- Moving a positive lineage preserves the degree bound and hence stays inside the finite
rectangle.  This is the key closure fact for every migration edge. -/
theorem migrateExponent_lt_of_sum_le {D K : ℕ}
    (exponent other : Fin D → Fin (K + 1)) (src dst : Fin D)
    (degree_le : (∑ deme, (exponent deme).val) +
      ∑ deme, (other deme).val ≤ K)
    (positive : 0 < (exponent src).val) :
    ∀ deme, migrateExponent (fun d ↦ (exponent d).val) src dst deme < K + 1 := by
  intro deme
  by_cases at_source : deme = src
  · subst deme
    simp [migrateExponent]
    omega
  · by_cases at_target : deme = dst
    · subst deme
      have distinct : src ≠ dst := by exact fun equal ↦ at_source equal.symm
      have pair_le : (exponent src).val + (exponent dst).val ≤
          ∑ d, (exponent d).val :=
        Finset.add_le_sum (fun d _ ↦ Nat.zero_le (exponent d).val)
          (Finset.mem_univ src) (Finset.mem_univ dst) distinct
      simp [migrateExponent, at_source]
      omega
    · simp [migrateExponent, at_source, at_target, (exponent deme).isLt]

/-- Flipping one positive lineage into the opposite label preserves total degree, so the
incremented label also remains in the finite rectangle. -/
theorem incrementExponent_lt_of_other_positive_sum_le {D K : ℕ}
    (incremented other : Fin D → Fin (K + 1)) (deme : Fin D)
    (degree_le : (∑ d, (other d).val) + ∑ d, (incremented d).val ≤ K)
    (positive : 0 < (other deme).val) :
    ∀ target, incrementExponent (fun d ↦ (incremented d).val) deme target < K + 1 := by
  intro target
  by_cases equal : target = deme
  · subst target
    have other_le : (other deme).val ≤ ∑ d, (other d).val :=
      Finset.single_le_sum (fun d _ ↦ Nat.zero_le (other d).val)
        (Finset.mem_univ deme)
    have incremented_le : (incremented deme).val ≤ ∑ d, (incremented d).val :=
      Finset.single_le_sum (fun d _ ↦ Nat.zero_le (incremented d).val)
        (Finset.mem_univ deme)
    simp [incrementExponent]
    omega
  · simp [incrementExponent, equal, (incremented target).isLt]

/-- Every active derived-lineage migration target lies in the degree-`K` carrier. -/
theorem ManyDemeKilledDualCoordinate.derivedMigration_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (src dst : Fin D)
    (degree_le : coordinate.degree ≤ K) (positive : 0 < (coordinate.1 src).val) :
    ∀ deme, migrateExponent (fun d ↦ (coordinate.1 d).val) src dst deme < K + 1 := by
  exact migrateExponent_lt_of_sum_le coordinate.1 coordinate.2 src dst degree_le positive

/-- Every active ancestral-lineage migration target lies in the degree-`K` carrier. -/
theorem ManyDemeKilledDualCoordinate.ancestralMigration_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (src dst : Fin D)
    (degree_le : coordinate.degree ≤ K) (positive : 0 < (coordinate.2 src).val) :
    ∀ deme, migrateExponent (fun d ↦ (coordinate.2 d).val) src dst deme < K + 1 := by
  apply migrateExponent_lt_of_sum_le coordinate.2 coordinate.1 src dst
  · unfold ManyDemeKilledDualCoordinate.degree at degree_le
    omega
  · exact positive

/-- Every active derived-to-ancestral mutation flip lies in the degree-`K` carrier. -/
theorem ManyDemeKilledDualCoordinate.derivedFlip_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (deme : Fin D)
    (degree_le : coordinate.degree ≤ K) (positive : 0 < (coordinate.1 deme).val) :
    ∀ target,
      incrementExponent (fun d ↦ (coordinate.2 d).val) deme target < K + 1 := by
  exact incrementExponent_lt_of_other_positive_sum_le coordinate.2 coordinate.1 deme
    degree_le positive

/-- Every active ancestral-to-derived mutation flip lies in the degree-`K` carrier. -/
theorem ManyDemeKilledDualCoordinate.ancestralFlip_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (deme : Fin D)
    (degree_le : coordinate.degree ≤ K) (positive : 0 < (coordinate.2 deme).val) :
    ∀ target,
      incrementExponent (fun d ↦ (coordinate.1 d).val) deme target < K + 1 := by
  apply incrementExponent_lt_of_other_positive_sum_le coordinate.1 coordinate.2 deme
  · unfold ManyDemeKilledDualCoordinate.degree at degree_le
    omega
  · exact positive

/-- **Finite-carrier closure.**  Every configuration consulted by a nonzero-rate transition
from a degree-`K` biological row remains coordinatewise below `K + 1`.  Coalescence only
decrements; migration conserves lineage count; and mutation transfers one lineage between
labels.  Opposite-type collision is absorption and therefore needs no destination coordinate. -/
theorem ManyDemeKilledDualCoordinate.allTransitions_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (degree_le : coordinate.degree ≤ K) :
    (∀ deme,
      (∀ target, decrementExponent (fun d ↦ (coordinate.1 d).val) deme target < K + 1) ∧
      (∀ target, decrementExponent (fun d ↦ (coordinate.2 d).val) deme target < K + 1)) ∧
    (∀ src dst, 0 < (coordinate.1 src).val →
      ∀ deme, migrateExponent (fun d ↦ (coordinate.1 d).val) src dst deme < K + 1) ∧
    (∀ src dst, 0 < (coordinate.2 src).val →
      ∀ deme, migrateExponent (fun d ↦ (coordinate.2 d).val) src dst deme < K + 1) ∧
    (∀ deme, 0 < (coordinate.1 deme).val →
      ∀ target, incrementExponent (fun d ↦ (coordinate.2 d).val) deme target < K + 1) ∧
    (∀ deme, 0 < (coordinate.2 deme).val →
      ∀ target, incrementExponent (fun d ↦ (coordinate.1 d).val) deme target < K + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro deme
    exact ⟨decrementExponent_lt_of_fin coordinate.1 deme,
      decrementExponent_lt_of_fin coordinate.2 deme⟩
  · intro src dst positive
    exact coordinate.derivedMigration_closed src dst degree_le positive
  · intro src dst positive
    exact coordinate.ancestralMigration_closed src dst degree_le positive
  · intro deme positive
    exact coordinate.derivedFlip_closed deme degree_le positive
  · intro deme positive
    exact coordinate.ancestralFlip_closed deme degree_le positive

/-- Read a finite vector as a lineage-configuration table, returning zero outside its
coordinate rectangle. -/
noncomputable def manyDemeKilledDualVectorTable {D : ℕ} (K : ℕ)
    (vector : ManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  if hderived : ∀ deme, derived deme < K + 1 then
    if hancestral : ∀ deme, ancestral deme < K + 1 then
      vector (fun deme ↦ ⟨derived deme, hderived deme⟩,
        fun deme ↦ ⟨ancestral deme, hancestral deme⟩)
    else 0
  else 0

/-- Finite table construction commutes with vector addition. -/
theorem manyDemeKilledDualVectorTable_add {D K : ℕ}
    (left right : ManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemeKilledDualVectorTable K (left + right) derived ancestral =
      manyDemeKilledDualVectorTable K left derived ancestral +
        manyDemeKilledDualVectorTable K right derived ancestral := by
  unfold manyDemeKilledDualVectorTable
  split_ifs <;> simp

/-- Finite table construction commutes with scalar multiplication. -/
theorem manyDemeKilledDualVectorTable_smul {D K : ℕ} (scalar : ℝ)
    (vector : ManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemeKilledDualVectorTable K (scalar • vector) derived ancestral =
      scalar * manyDemeKilledDualVectorTable K vector derived ancestral := by
  unfold manyDemeKilledDualVectorTable
  split_ifs <;> simp

/-- The killed generator is linear in the configuration value table. -/
theorem manyDemeKilledDualGenerator_add {D : ℕ} (rates : ManyDemeRates D)
    (left right : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemeKilledDualGenerator rates (fun a b ↦ left a b + right a b)
        derived ancestral =
      manyDemeKilledDualGenerator rates left derived ancestral +
        manyDemeKilledDualGenerator rates right derived ancestral := by
  have coalescence :
      (∑ deme, (
        rates.coalescence deme *
            ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
            ((left (decrementExponent derived deme) ancestral +
                right (decrementExponent derived deme) ancestral) -
              (left derived ancestral + right derived ancestral)) +
        rates.coalescence deme *
            ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
            ((left derived (decrementExponent ancestral deme) +
                right derived (decrementExponent ancestral deme)) -
              (left derived ancestral + right derived ancestral)) -
        rates.coalescence deme * derived deme * ancestral deme *
          (left derived ancestral + right derived ancestral))) =
        (∑ deme, (
          rates.coalescence deme *
              ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
              (left (decrementExponent derived deme) ancestral - left derived ancestral) +
          rates.coalescence deme *
              ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
              (left derived (decrementExponent ancestral deme) - left derived ancestral) -
          rates.coalescence deme * derived deme * ancestral deme * left derived ancestral)) +
        ∑ deme, (
          rates.coalescence deme *
              ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
              (right (decrementExponent derived deme) ancestral - right derived ancestral) +
          rates.coalescence deme *
              ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
              (right derived (decrementExponent ancestral deme) - right derived ancestral) -
          rates.coalescence deme * derived deme * ancestral deme * right derived ancestral) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro deme _
    ring
  have migration :
      (∑ src, ∑ dst, (
        rates.migration src dst * derived src *
            ((left (migrateExponent derived src dst) ancestral +
                right (migrateExponent derived src dst) ancestral) -
              (left derived ancestral + right derived ancestral)) +
        rates.migration src dst * ancestral src *
            ((left derived (migrateExponent ancestral src dst) +
                right derived (migrateExponent ancestral src dst)) -
              (left derived ancestral + right derived ancestral)))) =
        (∑ src, ∑ dst, (
          rates.migration src dst * derived src *
              (left (migrateExponent derived src dst) ancestral - left derived ancestral) +
          rates.migration src dst * ancestral src *
              (left derived (migrateExponent ancestral src dst) - left derived ancestral))) +
        ∑ src, ∑ dst, (
          rates.migration src dst * derived src *
              (right (migrateExponent derived src dst) ancestral - right derived ancestral) +
          rates.migration src dst * ancestral src *
              (right derived (migrateExponent ancestral src dst) - right derived ancestral)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro src _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro dst _
    ring
  have mutation :
      (∑ deme, (
        rates.forwardMutation deme * derived deme *
            ((left (decrementExponent derived deme) (incrementExponent ancestral deme) +
                right (decrementExponent derived deme) (incrementExponent ancestral deme)) -
              (left derived ancestral + right derived ancestral)) +
        rates.forwardMutation deme * ancestral deme *
            ((left (incrementExponent derived deme) (decrementExponent ancestral deme) +
                right (incrementExponent derived deme) (decrementExponent ancestral deme)) -
              (left derived ancestral + right derived ancestral)))) =
        (∑ deme, (
          rates.forwardMutation deme * derived deme *
              (left (decrementExponent derived deme) (incrementExponent ancestral deme) -
                left derived ancestral) +
          rates.forwardMutation deme * ancestral deme *
              (left (incrementExponent derived deme) (decrementExponent ancestral deme) -
                left derived ancestral))) +
        ∑ deme, (
          rates.forwardMutation deme * derived deme *
              (right (decrementExponent derived deme) (incrementExponent ancestral deme) -
                right derived ancestral) +
          rates.forwardMutation deme * ancestral deme *
              (right (incrementExponent derived deme) (decrementExponent ancestral deme) -
                right derived ancestral)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro deme _
    ring
  unfold manyDemeKilledDualGenerator
  rw [coalescence, migration, mutation]
  ring

/-- The killed generator commutes with scalar multiplication of its value table. -/
theorem manyDemeKilledDualGenerator_smul {D : ℕ} (rates : ManyDemeRates D)
    (scalar : ℝ) (value : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ) :
    manyDemeKilledDualGenerator rates (fun a b ↦ scalar * value a b)
        derived ancestral =
      scalar * manyDemeKilledDualGenerator rates value derived ancestral := by
  have coalescence :
      (∑ deme, (
        rates.coalescence deme *
            ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
            (scalar * value (decrementExponent derived deme) ancestral -
              scalar * value derived ancestral) +
        rates.coalescence deme *
            ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
            (scalar * value derived (decrementExponent ancestral deme) -
              scalar * value derived ancestral) -
        rates.coalescence deme * derived deme * ancestral deme *
          (scalar * value derived ancestral))) =
        scalar * ∑ deme, (
          rates.coalescence deme *
              ((derived deme * (derived deme - 1) : ℕ) : ℝ) / 2 *
              (value (decrementExponent derived deme) ancestral - value derived ancestral) +
          rates.coalescence deme *
              ((ancestral deme * (ancestral deme - 1) : ℕ) : ℝ) / 2 *
              (value derived (decrementExponent ancestral deme) - value derived ancestral) -
          rates.coalescence deme * derived deme * ancestral deme * value derived ancestral) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro deme _
    ring
  have migration :
      (∑ src, ∑ dst, (
        rates.migration src dst * derived src *
            (scalar * value (migrateExponent derived src dst) ancestral -
              scalar * value derived ancestral) +
        rates.migration src dst * ancestral src *
            (scalar * value derived (migrateExponent ancestral src dst) -
              scalar * value derived ancestral))) =
        scalar * ∑ src, ∑ dst, (
          rates.migration src dst * derived src *
              (value (migrateExponent derived src dst) ancestral - value derived ancestral) +
          rates.migration src dst * ancestral src *
              (value derived (migrateExponent ancestral src dst) - value derived ancestral)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro src _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro dst _
    ring
  have mutation :
      (∑ deme, (
        rates.forwardMutation deme * derived deme *
            (scalar * value (decrementExponent derived deme) (incrementExponent ancestral deme) -
              scalar * value derived ancestral) +
        rates.forwardMutation deme * ancestral deme *
            (scalar * value (incrementExponent derived deme) (decrementExponent ancestral deme) -
              scalar * value derived ancestral))) =
        scalar * ∑ deme, (
          rates.forwardMutation deme * derived deme *
              (value (decrementExponent derived deme) (incrementExponent ancestral deme) -
                value derived ancestral) +
          rates.forwardMutation deme * ancestral deme *
              (value (incrementExponent derived deme) (decrementExponent ancestral deme) -
                value derived ancestral)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro deme _
    ring
  unfold manyDemeKilledDualGenerator
  rw [coalescence, migration, mutation]
  ring

/-- Two value tables agreeing through the current lineage degree give the same killed
generator at that configuration.  All active transitions either lower or preserve degree. -/
theorem manyDemeKilledDualGenerator_congr_of_degree_le {D : ℕ}
    (rates : ManyDemeRates D)
    (left right : (Fin D → ℕ) → (Fin D → ℕ) → ℝ)
    (derived ancestral : Fin D → ℕ)
    (agree : ∀ a b,
      (∑ deme, a deme) + ∑ deme, b deme ≤
        (∑ deme, derived deme) + ∑ deme, ancestral deme → left a b = right a b) :
    manyDemeKilledDualGenerator rates left derived ancestral =
      manyDemeKilledDualGenerator rates right derived ancestral := by
  have original := agree derived ancestral (by omega)
  have derivedCoal (deme : Fin D) :
      left (decrementExponent derived deme) ancestral =
        right (decrementExponent derived deme) ancestral :=
    agree _ _ (by
      have := sum_decrementExponent_le derived deme
      omega)
  have ancestralCoal (deme : Fin D) :
      left derived (decrementExponent ancestral deme) =
        right derived (decrementExponent ancestral deme) :=
    agree _ _ (by
      have := sum_decrementExponent_le ancestral deme
      omega)
  have derivedMigration (src dst : Fin D) (positive : 0 < derived src)
      (distinct : src ≠ dst) :
      left (migrateExponent derived src dst) ancestral =
        right (migrateExponent derived src dst) ancestral :=
    agree _ _ (by rw [sum_migrateExponent derived src dst distinct positive])
  have ancestralMigration (src dst : Fin D) (positive : 0 < ancestral src)
      (distinct : src ≠ dst) :
      left derived (migrateExponent ancestral src dst) =
        right derived (migrateExponent ancestral src dst) :=
    agree _ _ (by rw [sum_migrateExponent ancestral src dst distinct positive])
  have derivedFlip (deme : Fin D) (positive : 0 < derived deme) :
      left (decrementExponent derived deme) (incrementExponent ancestral deme) =
        right (decrementExponent derived deme) (incrementExponent ancestral deme) :=
    agree _ _ (by
      rw [sum_decrementExponent derived deme positive, sum_incrementExponent]
      have totalPositive : 0 < ∑ d, derived d :=
        lt_of_lt_of_le positive
          (Finset.single_le_sum (fun d _ ↦ Nat.zero_le (derived d))
            (Finset.mem_univ deme))
      omega)
  have ancestralFlip (deme : Fin D) (positive : 0 < ancestral deme) :
      left (incrementExponent derived deme) (decrementExponent ancestral deme) =
        right (incrementExponent derived deme) (decrementExponent ancestral deme) :=
    agree _ _ (by
      rw [sum_incrementExponent, sum_decrementExponent ancestral deme positive]
      have totalPositive : 0 < ∑ d, ancestral d :=
        lt_of_lt_of_le positive
          (Finset.single_le_sum (fun d _ ↦ Nat.zero_le (ancestral d))
            (Finset.mem_univ deme))
      omega)
  unfold manyDemeKilledDualGenerator
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro deme _
      rw [derivedCoal, ancestralCoal, original]
    · apply Finset.sum_congr rfl
      intro src _
      apply Finset.sum_congr rfl
      intro dst _
      by_cases same : src = dst
      · subst dst
        simp [rates.migration_self]
      · by_cases derivedPositive : 0 < derived src
        · rw [derivedMigration src dst derivedPositive same, original]
          by_cases ancestralPositive : 0 < ancestral src
          · rw [ancestralMigration src dst ancestralPositive same]
          · have ancestralZero : ancestral src = 0 := by omega
            simp [ancestralZero]
        · have derivedZero : derived src = 0 := by omega
          simp only [derivedZero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
          rw [original]
          by_cases ancestralPositive : 0 < ancestral src
          · rw [ancestralMigration src dst ancestralPositive same]
          · have ancestralZero : ancestral src = 0 := by omega
            simp [ancestralZero]
  · apply Finset.sum_congr rfl
    intro deme _
    by_cases derivedPositive : 0 < derived deme
    · rw [derivedFlip deme derivedPositive, original]
      by_cases ancestralPositive : 0 < ancestral deme
      · rw [ancestralFlip deme ancestralPositive]
      · have ancestralZero : ancestral deme = 0 := by omega
        simp [ancestralZero]
    · have derivedZero : derived deme = 0 := by omega
      simp only [derivedZero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
      rw [original]
      by_cases ancestralPositive : 0 < ancestral deme
      · rw [ancestralFlip deme ancestralPositive]
      · have ancestralZero : ancestral deme = 0 := by omega
        simp [ancestralZero]

/-- Finite linear operator obtained directly from the proved positive killed-dual law. -/
noncomputable def manyDemeKilledDualGeneratorLinearMap {D K : ℕ}
    (rates : ManyDemeRates D) :
    (ManyDemeKilledDualCoordinate D K → ℝ) →ₗ[ℝ]
      (ManyDemeKilledDualCoordinate D K → ℝ) where
  toFun vector coordinate :=
    if coordinate.degree ≤ K then
      manyDemeKilledDualGenerator rates (manyDemeKilledDualVectorTable K vector)
        (fun deme ↦ (coordinate.1 deme).val)
        (fun deme ↦ (coordinate.2 deme).val)
    else 0
  map_add' := by
    intro left right
    funext coordinate
    by_cases hdegree : coordinate.degree ≤ K
    · simp only [hdegree, if_true, Pi.add_apply]
      have tableAdd : manyDemeKilledDualVectorTable K (left + right) =
          manyDemeKilledDualVectorTable K left + manyDemeKilledDualVectorTable K right := by
        funext derived ancestral
        exact manyDemeKilledDualVectorTable_add left right derived ancestral
      rw [tableAdd]
      exact manyDemeKilledDualGenerator_add rates _ _ _ _
    · simp [hdegree]
  map_smul' := by
    intro scalar vector
    funext coordinate
    by_cases hdegree : coordinate.degree ≤ K
    · simp only [hdegree, if_true, Pi.smul_apply, smul_eq_mul]
      have tableSmul : manyDemeKilledDualVectorTable K (scalar • vector) =
          fun derived ancestral ↦ scalar *
            manyDemeKilledDualVectorTable K vector derived ancestral := by
        funext derived ancestral
        exact manyDemeKilledDualVectorTable_smul scalar vector derived ancestral
      rw [tableSmul]
      simp only [RingHom.id_apply]
      exact manyDemeKilledDualGenerator_smul rates scalar _ _ _
    · simp [hdegree]

/-- Finite zero-extended matrix encoding the arbitrary-deme positive killed dual.  A separate
closure theorem is required before identifying its exponential with the unrestricted process. -/
noncomputable def manyDemeKilledDualDynamicsMatrix {D K : ℕ}
    (rates : ManyDemeRates D) :
    Matrix (ManyDemeKilledDualCoordinate D K) (ManyDemeKilledDualCoordinate D K) ℝ :=
  LinearMap.toMatrix' (manyDemeKilledDualGeneratorLinearMap (K := K) rates)

/-- Matrix application evaluates exactly the finite zero-extended killed-dual generator. -/
theorem manyDemeKilledDualDynamicsMatrix_mulVec {D K : ℕ}
    (rates : ManyDemeRates D) (vector : ManyDemeKilledDualCoordinate D K → ℝ) :
    (manyDemeKilledDualDynamicsMatrix (K := K) rates).mulVec vector =
      manyDemeKilledDualGeneratorLinearMap rates vector := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- Biological killed-dual coordinates are exactly the lineage configurations whose total
degree is at most `K`; rectangular padding is excluded by construction. -/
structure BiologicalManyDemeKilledDualCoordinate (D K : ℕ) where
  coordinate : ManyDemeKilledDualCoordinate D K
  degree_le : coordinate.degree ≤ K
  deriving DecidableEq

instance biologicalManyDemeKilledDualCoordinateFinite (D K : ℕ) :
    Finite (BiologicalManyDemeKilledDualCoordinate D K) := by
  apply Finite.of_injective
    (fun coordinate : BiologicalManyDemeKilledDualCoordinate D K ↦ coordinate.coordinate)
  intro left right equal
  cases left
  cases right
  cases equal
  rfl

noncomputable instance biologicalManyDemeKilledDualCoordinateFintype (D K : ℕ) :
    Fintype (BiologicalManyDemeKilledDualCoordinate D K) :=
  Fintype.ofFinite _

/-- Read a compact killed-dual vector as an unrestricted lineage-configuration table. -/
noncomputable def biologicalManyDemeKilledDualVectorTable {D K : ℕ}
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) : ℝ :=
  if hderived : ∀ deme, derived deme < K + 1 then
    if hancestral : ∀ deme, ancestral deme < K + 1 then
      let coordinate : ManyDemeKilledDualCoordinate D K :=
        (fun deme ↦ ⟨derived deme, hderived deme⟩,
          fun deme ↦ ⟨ancestral deme, hancestral deme⟩)
      if hdegree : coordinate.degree ≤ K then
        state ⟨coordinate, hdegree⟩
      else 0
    else 0
  else 0

/-- Zero extension from the compact biological carrier preserves pointwise
nonnegativity. -/
theorem biologicalManyDemeKilledDualVectorTable_nonneg {D K : ℕ}
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (state_nonneg : ∀ coordinate, 0 ≤ state coordinate)
    (derived ancestral : Fin D → ℕ) :
    0 ≤ biologicalManyDemeKilledDualVectorTable state derived ancestral := by
  unfold biologicalManyDemeKilledDualVectorTable
  by_cases hderived : ∀ deme, derived deme < K + 1
  · rw [dif_pos hderived]
    by_cases hancestral : ∀ deme, ancestral deme < K + 1
    · rw [dif_pos hancestral]
      dsimp only
      split_ifs
      · exact state_nonneg _
      · exact le_rfl
    · rw [dif_neg hancestral]
  · rw [dif_neg hderived]

/-- Compact killed-dual table construction commutes with addition. -/
theorem biologicalManyDemeKilledDualVectorTable_add {D K : ℕ}
    (left right : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) :
    biologicalManyDemeKilledDualVectorTable (left + right) derived ancestral =
      biologicalManyDemeKilledDualVectorTable left derived ancestral +
        biologicalManyDemeKilledDualVectorTable right derived ancestral := by
  unfold biologicalManyDemeKilledDualVectorTable
  by_cases hderived : ∀ deme, derived deme < K + 1
  · simp only [dif_pos hderived]
    by_cases hancestral : ∀ deme, ancestral deme < K + 1
    · simp only [dif_pos hancestral]
      let coordinate : ManyDemeKilledDualCoordinate D K :=
        (fun deme ↦ ⟨derived deme, hderived deme⟩,
          fun deme ↦ ⟨ancestral deme, hancestral deme⟩)
      change (if hdegree : coordinate.degree ≤ K then
          (left + right) ⟨coordinate, hdegree⟩ else 0) =
        (if hdegree : coordinate.degree ≤ K then left ⟨coordinate, hdegree⟩ else 0) +
          if hdegree : coordinate.degree ≤ K then right ⟨coordinate, hdegree⟩ else 0
      by_cases hdegree : coordinate.degree ≤ K
      · simp [hdegree, Pi.add_apply]
      · simp [hdegree]
    · simp only [dif_neg hancestral, zero_add]
  · simp only [dif_neg hderived, zero_add]

/-- Compact killed-dual table construction commutes with scalar multiplication. -/
theorem biologicalManyDemeKilledDualVectorTable_smul {D K : ℕ} (scalar : ℝ)
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ) :
    biologicalManyDemeKilledDualVectorTable (scalar • state) derived ancestral =
      scalar * biologicalManyDemeKilledDualVectorTable state derived ancestral := by
  unfold biologicalManyDemeKilledDualVectorTable
  split_ifs <;> simp

/-- Compact table lookup succeeds for every unrestricted configuration of total degree at
most `K`. -/
theorem biologicalManyDemeKilledDualVectorTable_of_degree_le {D K : ℕ}
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ)
    (degree_le : (∑ deme, derived deme) + ∑ deme, ancestral deme ≤ K) :
    biologicalManyDemeKilledDualVectorTable state derived ancestral =
      state {
        coordinate :=
          (fun deme ↦ ⟨derived deme, by
              have coordinate_le : derived deme ≤ ∑ d, derived d :=
                Finset.single_le_sum (fun d _ ↦ Nat.zero_le (derived d))
                  (Finset.mem_univ deme)
              omega⟩,
            fun deme ↦ ⟨ancestral deme, by
              have coordinate_le : ancestral deme ≤ ∑ d, ancestral d :=
                Finset.single_le_sum (fun d _ ↦ Nat.zero_le (ancestral d))
                  (Finset.mem_univ deme)
              omega⟩)
        degree_le := by
          simpa [ManyDemeKilledDualCoordinate.degree] } := by
  have derivedBound : ∀ deme, derived deme < K + 1 := by
    intro deme
    have coordinate_le : derived deme ≤ ∑ d, derived d :=
      Finset.single_le_sum (fun d _ ↦ Nat.zero_le (derived d)) (Finset.mem_univ deme)
    omega
  have ancestralBound : ∀ deme, ancestral deme < K + 1 := by
    intro deme
    have coordinate_le : ancestral deme ≤ ∑ d, ancestral d :=
      Finset.single_le_sum (fun d _ ↦ Nat.zero_le (ancestral d)) (Finset.mem_univ deme)
    omega
  unfold biologicalManyDemeKilledDualVectorTable
  rw [dif_pos derivedBound, dif_pos ancestralBound]
  simp only [ManyDemeKilledDualCoordinate.degree]
  rw [dif_pos (by simpa using degree_le)]

/-- Reading the unrestricted table at the configuration represented by a compact
coordinate returns that coordinate's entry exactly. -/
theorem biologicalManyDemeKilledDualVectorTable_at_coordinate {D K : ℕ}
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (coordinate : BiologicalManyDemeKilledDualCoordinate D K) :
    biologicalManyDemeKilledDualVectorTable state
        (fun deme ↦ (coordinate.coordinate.1 deme).val)
        (fun deme ↦ (coordinate.coordinate.2 deme).val) =
      state coordinate := by
  rw [biologicalManyDemeKilledDualVectorTable_of_degree_le _ _ _ (by
    simpa [ManyDemeKilledDualCoordinate.degree] using coordinate.degree_le)]

/-- Exact killed-dual linear operator on its closed biological carrier. -/
noncomputable def biologicalManyDemeKilledDualGeneratorLinearMap {D K : ℕ}
    (rates : ManyDemeRates D) :
    (BiologicalManyDemeKilledDualCoordinate D K → ℝ) →ₗ[ℝ]
      (BiologicalManyDemeKilledDualCoordinate D K → ℝ) where
  toFun state coordinate :=
    manyDemeKilledDualGenerator rates
      (biologicalManyDemeKilledDualVectorTable state)
      (fun deme ↦ (coordinate.coordinate.1 deme).val)
      (fun deme ↦ (coordinate.coordinate.2 deme).val)
  map_add' := by
    intro left right
    funext coordinate
    simp only [Pi.add_apply]
    have tableAdd : biologicalManyDemeKilledDualVectorTable (left + right) =
        biologicalManyDemeKilledDualVectorTable left +
          biologicalManyDemeKilledDualVectorTable right := by
      funext derived ancestral
      exact biologicalManyDemeKilledDualVectorTable_add left right derived ancestral
    rw [tableAdd]
    exact manyDemeKilledDualGenerator_add rates _ _ _ _
  map_smul' := by
    intro scalar state
    funext coordinate
    simp only [Pi.smul_apply, smul_eq_mul]
    have tableSmul : biologicalManyDemeKilledDualVectorTable (scalar • state) =
        fun derived ancestral ↦ scalar *
          biologicalManyDemeKilledDualVectorTable state derived ancestral := by
      funext derived ancestral
      exact biologicalManyDemeKilledDualVectorTable_smul scalar state derived ancestral
    rw [tableSmul]
    simp only [RingHom.id_apply]
    exact manyDemeKilledDualGenerator_smul rates scalar _ _ _

/-- Exact finite killed-dual generator matrix with no padding rows or columns. -/
noncomputable def biologicalManyDemeKilledDualGenerator {D K : ℕ}
    (rates : ManyDemeRates D) :
    Matrix (BiologicalManyDemeKilledDualCoordinate D K)
      (BiologicalManyDemeKilledDualCoordinate D K) ℝ :=
  LinearMap.toMatrix' (biologicalManyDemeKilledDualGeneratorLinearMap rates)

/-- Applying the compact matrix evaluates the unrestricted killed generator through the
compact configuration table. -/
theorem biologicalManyDemeKilledDualGenerator_mulVec {D K : ℕ}
    (rates : ManyDemeRates D)
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ) :
    (biologicalManyDemeKilledDualGenerator rates).mulVec state =
      biologicalManyDemeKilledDualGeneratorLinearMap rates state := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- **The exact compact biological killed-dual generator is Metzler.**  Every
off-diagonal matrix entry is a sum of coalescence, migration, and mutation jump rates into
the indicated destination.  The proof works for every finite deme count and every typed
migration matrix; the absorption channel changes only the diagonal. -/
theorem biologicalManyDemeKilledDualGenerator_isMetzler {D K : ℕ}
    (rates : ManyDemeRates D) :
    Matrix.IsMetzler (biologicalManyDemeKilledDualGenerator (K := K) rates) := by
  intro row column distinct
  unfold biologicalManyDemeKilledDualGenerator
  rw [LinearMap.toMatrix'_apply]
  change 0 ≤ manyDemeKilledDualGenerator rates
      (biologicalManyDemeKilledDualVectorTable
        (fun candidate ↦ if candidate = column then 1 else 0))
      (fun deme ↦ (row.coordinate.1 deme).val)
      (fun deme ↦ (row.coordinate.2 deme).val)
  apply manyDemeKilledDualGenerator_nonneg_of_nonneg_of_current_eq_zero
  · intro derived ancestral
    apply biologicalManyDemeKilledDualVectorTable_nonneg
    intro candidate
    split_ifs <;> norm_num
  · rw [biologicalManyDemeKilledDualVectorTable_at_coordinate]
    simp [distinct]

/-- Every transition consulted by a biological killed-generator row stays inside its finite
carrier. -/
theorem BiologicalManyDemeKilledDualCoordinate.transitions_closed {D K : ℕ}
    (coordinate : BiologicalManyDemeKilledDualCoordinate D K) :
    (∀ deme,
      (∀ target, decrementExponent
          (fun d ↦ (coordinate.coordinate.1 d).val) deme target < K + 1) ∧
      (∀ target, decrementExponent
          (fun d ↦ (coordinate.coordinate.2 d).val) deme target < K + 1)) ∧
    (∀ src dst, 0 < (coordinate.coordinate.1 src).val →
      ∀ deme, migrateExponent
        (fun d ↦ (coordinate.coordinate.1 d).val) src dst deme < K + 1) ∧
    (∀ src dst, 0 < (coordinate.coordinate.2 src).val →
      ∀ deme, migrateExponent
        (fun d ↦ (coordinate.coordinate.2 d).val) src dst deme < K + 1) ∧
    (∀ deme, 0 < (coordinate.coordinate.1 deme).val →
      ∀ target, incrementExponent
        (fun d ↦ (coordinate.coordinate.2 d).val) deme target < K + 1) ∧
    (∀ deme, 0 < (coordinate.coordinate.2 deme).val →
      ∀ target, incrementExponent
        (fun d ↦ (coordinate.coordinate.1 d).val) deme target < K + 1) :=
  coordinate.coordinate.allTransitions_closed coordinate.degree_le

/-- One piecewise-constant epoch for direct positive killed-dual propagation. -/
structure ManyDemeKilledDualEpoch (D K : ℕ) where
  rates : ManyDemeRates D
  duration : ℝ
  duration_nonneg : 0 ≤ duration

/-- Exactly evaluable finite positive-basis candidate epoch operator.  It is the exponential
of the zero-extended matrix whose unrestricted generator law was derived above; no equivalence
to the unrestricted semigroup is claimed before the carrier-closure proof. -/
noncomputable def ManyDemeKilledDualEpoch.propagator {D K : ℕ}
    (epoch : ManyDemeKilledDualEpoch D K) :
    Matrix (ManyDemeKilledDualCoordinate D K) (ManyDemeKilledDualCoordinate D K) ℝ :=
  matrixExponential (manyDemeKilledDualDynamicsMatrix epoch.rates) epoch.duration

/-- A zero-duration killed-dual epoch is exactly the identity operator. -/
theorem ManyDemeKilledDualEpoch.propagator_zero {D K : ℕ}
    (rates : ManyDemeRates D) (nonnegative : 0 ≤ (0 : ℝ)) :
    (ManyDemeKilledDualEpoch.mk rates 0 nonnegative :
      ManyDemeKilledDualEpoch D K).propagator = 1 := by
  exact matrixExponential_zero _

/-- Merge a newly split child's exponent back into its parent.  This is the pullback of the
instantaneous constraint `X_child = X_parent`. -/
def mergeSplitExponent {D : ℕ} (parent child : Fin D)
    (exponent : Fin D → ℕ) : Fin D → ℕ :=
  fun d ↦ if d = parent then exponent parent + exponent child
    else if d = child then 0 else exponent d

/-- Pulling a coordinate back across a genuine parent/child split preserves total degree. -/
theorem sum_mergeSplitExponent {D : ℕ} (parent child : Fin D)
    (distinct : parent ≠ child) (exponent : Fin D → ℕ) :
    ∑ deme, mergeSplitExponent parent child exponent deme = ∑ deme, exponent deme := by
  classical
  have child_mem : child ∈ Finset.univ \ {parent} := by simp [distinct.symm]
  calc
    _ = mergeSplitExponent parent child exponent parent +
        ∑ deme ∈ Finset.univ \ {parent}, mergeSplitExponent parent child exponent deme :=
      Finset.sum_eq_add_sum_diff_singleton (f := mergeSplitExponent parent child exponent)
        (Finset.mem_univ parent)
    _ = mergeSplitExponent parent child exponent parent +
        (mergeSplitExponent parent child exponent child +
          ∑ deme ∈ (Finset.univ \ {parent}) \ {child},
            mergeSplitExponent parent child exponent deme) := by
      rw [Finset.sum_eq_add_sum_diff_singleton (f := mergeSplitExponent parent child exponent)
        child_mem]
    _ = exponent parent + exponent child +
        ∑ deme ∈ (Finset.univ \ {parent}) \ {child}, exponent deme := by
      simp only [mergeSplitExponent, if_pos, distinct.symm, if_false, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro deme member
      have parent_ne : deme ≠ parent :=
        Finset.notMem_singleton.mp (Finset.mem_sdiff.mp
          (Finset.mem_sdiff.mp member).1).2
      have child_ne : deme ≠ child :=
        Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
      simp [mergeSplitExponent, parent_ne, child_ne]
    _ = ∑ deme, exponent deme := by
      rw [Finset.sum_eq_add_sum_diff_singleton (f := exponent) (Finset.mem_univ parent),
        Finset.sum_eq_add_sum_diff_singleton (f := exponent) child_mem]
      omega

/-- Polynomial substitution induced by the instantaneous split constraint
`X_child = X_parent`. -/
noncomputable def splitManyDemePolynomial {D : ℕ} (parent child : Fin D) :
    MvPolynomial (Fin D) ℝ →ₐ[ℝ] MvPolynomial (Fin D) ℝ :=
  MvPolynomial.aeval fun deme ↦ if deme = child then MvPolynomial.X parent
    else MvPolynomial.X deme

/-- Split substitution sends each product Bernstein polynomial to the merged lineage
configuration. -/
theorem splitManyDemePolynomial_bernstein {D : ℕ} (parent child : Fin D)
    (distinct : parent ≠ child) (derived ancestral : Fin D → ℕ) :
    splitManyDemePolynomial parent child
        (manyDemeBernsteinPolynomial derived ancestral) =
      manyDemeBernsteinPolynomial
        (mergeSplitExponent parent child derived)
        (mergeSplitExponent parent child ancestral) := by
  simp only [splitManyDemePolynomial, map_prod, manyDemeBernsteinPolynomial,
    manyDemeBernsteinPolynomialFactor, map_mul, map_pow, map_sub, map_one,
    MvPolynomial.aeval_X]
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ parent),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ parent)]
  have child_mem : child ∈ Finset.univ \ {parent} := by simp [distinct.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton child_mem,
    Finset.prod_eq_mul_prod_diff_singleton child_mem]
  simp only [mergeSplitExponent, if_pos, distinct.symm, if_false, pow_zero, mul_one]
  have rest_equal :
      (∏ x ∈ (Finset.univ \ {parent}) \ {child},
        (if x = child then MvPolynomial.X parent else MvPolynomial.X x) ^ derived x *
          ((1 : MvPolynomial (Fin D) ℝ) -
            if x = child then MvPolynomial.X parent else MvPolynomial.X x) ^ ancestral x) =
        ∏ x ∈ (Finset.univ \ {parent}) \ {child},
          MvPolynomial.X x ^ mergeSplitExponent parent child derived x *
            ((1 : MvPolynomial (Fin D) ℝ) - MvPolynomial.X x) ^
              mergeSplitExponent parent child ancestral x := by
    apply Finset.prod_congr rfl
    intro x member
    have parent_ne : x ≠ parent :=
      Finset.notMem_singleton.mp (Finset.mem_sdiff.mp
        (Finset.mem_sdiff.mp member).1).2
    have child_ne : x ≠ child :=
      Finset.notMem_singleton.mp (Finset.mem_sdiff.mp member).2
    simp [mergeSplitExponent, parent_ne, child_ne]
  rw [rest_equal]
  simp only [mergeSplitExponent, if_pos, if_neg distinct, pow_add]
  ring

/-- Merging distinct child and parent lineage counts across a split preserves a global degree
bound and therefore remains inside the coordinate rectangle. -/
theorem mergeSplitExponent_lt_of_sum_le {D K : ℕ} (exponent : Fin D → Fin (K + 1))
    (parent child : Fin D) (distinct : parent ≠ child)
    (degree_le : ∑ deme, (exponent deme).val ≤ K) :
    ∀ deme,
      mergeSplitExponent parent child (fun d ↦ (exponent d).val) deme < K + 1 := by
  intro deme
  by_cases at_parent : deme = parent
  · subst deme
    have pair_le : (exponent parent).val + (exponent child).val ≤
        ∑ d, (exponent d).val :=
      Finset.add_le_sum (fun d _ ↦ Nat.zero_le (exponent d).val)
        (Finset.mem_univ parent) (Finset.mem_univ child) distinct
    simp [mergeSplitExponent]
    omega
  · by_cases at_child : deme = child
    · subst deme
      simp [mergeSplitExponent, distinct.symm]
    · simp [mergeSplitExponent, at_parent, at_child, (exponent deme).isLt]

/-- Both allele-label coordinates remain finite when a genuine split is pulled back. -/
theorem ManyDemeKilledDualCoordinate.mergeSplit_closed {D K : ℕ}
    (coordinate : ManyDemeKilledDualCoordinate D K) (parent child : Fin D)
    (distinct : parent ≠ child) (degree_le : coordinate.degree ≤ K) :
    (∀ deme, mergeSplitExponent parent child
        (fun d ↦ (coordinate.1 d).val) deme < K + 1) ∧
      ∀ deme, mergeSplitExponent parent child
        (fun d ↦ (coordinate.2 d).val) deme < K + 1 := by
  constructor
  · apply mergeSplitExponent_lt_of_sum_le coordinate.1 parent child distinct
    unfold ManyDemeKilledDualCoordinate.degree at degree_le
    omega
  · apply mergeSplitExponent_lt_of_sum_le coordinate.2 parent child distinct
    unfold ManyDemeKilledDualCoordinate.degree at degree_le
    omega

/-- Merge both label-count vectors of a biological killed-dual coordinate across a genuine
split. -/
def BiologicalManyDemeKilledDualCoordinate.mergeSplit {D K : ℕ}
    (coordinate : BiologicalManyDemeKilledDualCoordinate D K)
    (parent child : Fin D) (distinct : parent ≠ child) :
    BiologicalManyDemeKilledDualCoordinate D K := by
  have closed := coordinate.coordinate.mergeSplit_closed parent child distinct
    coordinate.degree_le
  exact {
    coordinate :=
      (fun deme ↦ ⟨mergeSplitExponent parent child
          (fun d ↦ (coordinate.coordinate.1 d).val) deme, closed.1 deme⟩,
        fun deme ↦ ⟨mergeSplitExponent parent child
          (fun d ↦ (coordinate.coordinate.2 d).val) deme, closed.2 deme⟩)
    degree_le := by
      unfold ManyDemeKilledDualCoordinate.degree
      rw [show (∑ deme, (⟨mergeSplitExponent parent child
            (fun d ↦ (coordinate.coordinate.1 d).val) deme, closed.1 deme⟩ : Fin (K + 1)).val) =
          ∑ deme, mergeSplitExponent parent child
            (fun d ↦ (coordinate.coordinate.1 d).val) deme by rfl,
        show (∑ deme, (⟨mergeSplitExponent parent child
            (fun d ↦ (coordinate.coordinate.2 d).val) deme, closed.2 deme⟩ : Fin (K + 1)).val) =
          ∑ deme, mergeSplitExponent parent child
            (fun d ↦ (coordinate.coordinate.2 d).val) deme by rfl,
        sum_mergeSplitExponent parent child distinct,
        sum_mergeSplitExponent parent child distinct]
      exact coordinate.degree_le }

/-- Sparse compact killed-dual split matrix. -/
noncomputable def biologicalManyDemeKilledDualSplitPropagator {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child) :
    Matrix (BiologicalManyDemeKilledDualCoordinate D K)
      (BiologicalManyDemeKilledDualCoordinate D K) ℝ :=
  fun row column ↦ if column = row.mergeSplit parent child distinct then 1 else 0

/-- The compact killed-dual split matrix performs exactly deterministic lineage merging. -/
theorem biologicalManyDemeKilledDualSplitPropagator_mulVec {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child)
    (state : BiologicalManyDemeKilledDualCoordinate D K → ℝ) :
    (biologicalManyDemeKilledDualSplitPropagator parent child distinct).mulVec state =
      fun row ↦ state (row.mergeSplit parent child distinct) := by
  funext row
  simp [biologicalManyDemeKilledDualSplitPropagator, Matrix.mulVec, dotProduct]

/-- Split-merging a killed coordinate simply merges both exponents in its Bernstein
polynomial. -/
theorem biologicalKilledDual_mergeSplit_bernsteinPolynomial {D K : ℕ}
    (row : BiologicalManyDemeKilledDualCoordinate D K)
    (parent child : Fin D) (distinct : parent ≠ child) :
    manyDemeBernsteinPolynomial
        (fun deme ↦ ((row.mergeSplit parent child distinct).coordinate.1 deme).val)
        (fun deme ↦ ((row.mergeSplit parent child distinct).coordinate.2 deme).val) =
      manyDemeBernsteinPolynomial
        (mergeSplitExponent parent child
          (fun deme ↦ (row.coordinate.1 deme).val))
        (mergeSplitExponent parent child
          (fun deme ↦ (row.coordinate.2 deme).val)) := by
  rfl

/-- Sparse deterministic pullback of a positive dual configuration across a population split.
Each row has at most one nonzero entry, at the configuration formed by merging child counts
into the parent. -/
noncomputable def splitManyDemeKilledDualPropagator {D K : ℕ}
    (parent child : Fin D) :
    Matrix (ManyDemeKilledDualCoordinate D K) (ManyDemeKilledDualCoordinate D K) ℝ :=
  fun row column ↦
    if hderived : ∀ deme, mergeSplitExponent parent child
        (fun d ↦ (row.1 d).val) deme < K + 1 then
      if hancestral : ∀ deme, mergeSplitExponent parent child
          (fun d ↦ (row.2 d).val) deme < K + 1 then
        let merged : ManyDemeKilledDualCoordinate D K :=
          (fun deme ↦ ⟨mergeSplitExponent parent child
              (fun d ↦ (row.1 d).val) deme, hderived deme⟩,
            fun deme ↦ ⟨mergeSplitExponent parent child
              (fun d ↦ (row.2 d).val) deme, hancestral deme⟩)
        if column = merged then 1 else 0
      else 0
    else 0

/-- Direct deterministic split action on a finite killed-dual value vector. -/
noncomputable def splitManyDemeKilledDualState {D K : ℕ}
    (parent child : Fin D) (state : ManyDemeKilledDualCoordinate D K → ℝ)
    (row : ManyDemeKilledDualCoordinate D K) : ℝ :=
  manyDemeKilledDualVectorTable K state
    (mergeSplitExponent parent child (fun d ↦ (row.1 d).val))
    (mergeSplitExponent parent child (fun d ↦ (row.2 d).val))

/-- The sparse split matrix is exactly its deterministic merge action. -/
theorem splitManyDemeKilledDualPropagator_mulVec {D K : ℕ}
    (parent child : Fin D) (state : ManyDemeKilledDualCoordinate D K → ℝ) :
    (splitManyDemeKilledDualPropagator parent child).mulVec state =
      splitManyDemeKilledDualState parent child state := by
  funext row
  by_cases hderived : ∀ deme, mergeSplitExponent parent child
      (fun d ↦ (row.1 d).val) deme < K + 1
  · by_cases hancestral : ∀ deme, mergeSplitExponent parent child
        (fun d ↦ (row.2 d).val) deme < K + 1
    · let merged : ManyDemeKilledDualCoordinate D K :=
        (fun deme ↦ ⟨mergeSplitExponent parent child
            (fun d ↦ (row.1 d).val) deme, hderived deme⟩,
          fun deme ↦ ⟨mergeSplitExponent parent child
            (fun d ↦ (row.2 d).val) deme, hancestral deme⟩)
      simp [Matrix.mulVec, dotProduct, splitManyDemeKilledDualPropagator,
        splitManyDemeKilledDualState, manyDemeKilledDualVectorTable,
        hderived, hancestral, merged]
    · simp [Matrix.mulVec, dotProduct, splitManyDemeKilledDualPropagator,
        splitManyDemeKilledDualState, manyDemeKilledDualVectorTable,
        hderived, hancestral]
  · simp [Matrix.mulVec, dotProduct, splitManyDemeKilledDualPropagator,
      splitManyDemeKilledDualState, manyDemeKilledDualVectorTable, hderived]

/-- One finite positive-dual demographic instruction: continuous killed propagation or a
deterministic pullback across a split. -/
inductive ManyDemeKilledDualInstruction (D K : ℕ) where
  | evolve (epoch : ManyDemeKilledDualEpoch D K)
  | split (parent child : Fin D)

/-- Matrix for one finite positive-dual instruction. -/
noncomputable def ManyDemeKilledDualInstruction.propagator {D K : ℕ}
    (instruction : ManyDemeKilledDualInstruction D K) :
    Matrix (ManyDemeKilledDualCoordinate D K) (ManyDemeKilledDualCoordinate D K) ℝ :=
  match instruction with
  | .evolve epoch => epoch.propagator
  | .split parent child => splitManyDemeKilledDualPropagator parent child

/-- Ordered product for an arbitrary finite positive-dual epoch/split history. -/
noncomputable def manyDemeKilledDualHistoryPropagator {D K : ℕ} :
    List (ManyDemeKilledDualInstruction D K) →
      Matrix (ManyDemeKilledDualCoordinate D K) (ManyDemeKilledDualCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      instruction.propagator * manyDemeKilledDualHistoryPropagator remaining

/-- The structured moment generator at one exponent, bundled as a linear functional of the
moment table. -/
noncomputable def manyDemeMomentGeneratorLinearMapAt {D : ℕ}
    (rates : ManyDemeRates D) (exponent : Fin D → ℕ) :
    ((Fin D → ℕ) → ℝ) →ₗ[ℝ] ℝ where
  toFun moment := manyDemeMomentGenerator rates moment exponent
  map_add' := by
    intro left right
    have coalescence :
        (∑ d, rates.coalescence d * ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
            ((left (decrementExponent exponent d) + right (decrementExponent exponent d)) -
              (left exponent + right exponent))) =
          (∑ d, rates.coalescence d * ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
            (left (decrementExponent exponent d) - left exponent)) +
          ∑ d, rates.coalescence d * ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
            (right (decrementExponent exponent d) - right exponent) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    have migration :
        (∑ src, ∑ dst, rates.migration src dst * exponent src *
            ((left (migrateExponent exponent src dst) +
                right (migrateExponent exponent src dst)) -
              (left exponent + right exponent))) =
          (∑ src, ∑ dst, rates.migration src dst * exponent src *
            (left (migrateExponent exponent src dst) - left exponent)) +
          ∑ src, ∑ dst, rates.migration src dst * exponent src *
            (right (migrateExponent exponent src dst) - right exponent) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro src _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro dst _
      ring
    have mutation :
        (∑ d, (rates.forwardMutation d * exponent d *
            ((left (decrementExponent exponent d) + right (decrementExponent exponent d)) -
              (left exponent + right exponent)) -
          rates.backwardMutation d * exponent d * (left exponent + right exponent))) =
          (∑ d, (rates.forwardMutation d * exponent d *
              (left (decrementExponent exponent d) - left exponent) -
            rates.backwardMutation d * exponent d * left exponent)) +
          ∑ d, (rates.forwardMutation d * exponent d *
              (right (decrementExponent exponent d) - right exponent) -
            rates.backwardMutation d * exponent d * right exponent) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d _
      ring
    unfold manyDemeMomentGenerator
    simp only [Pi.add_apply]
    rw [coalescence, migration, mutation]
    ring
  map_smul' := by
    intro scalar moment
    have coalescence :
        (∑ d, rates.coalescence d * ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
            (scalar * moment (decrementExponent exponent d) - scalar * moment exponent)) =
          scalar * ∑ d, rates.coalescence d *
            ((exponent d * (exponent d - 1) : ℕ) : ℝ) / 2 *
            (moment (decrementExponent exponent d) - moment exponent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    have migration :
        (∑ src, ∑ dst, rates.migration src dst * exponent src *
            (scalar * moment (migrateExponent exponent src dst) - scalar * moment exponent)) =
          scalar * ∑ src, ∑ dst, rates.migration src dst * exponent src *
            (moment (migrateExponent exponent src dst) - moment exponent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro src _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro dst _
      ring
    have mutation :
        (∑ d, (rates.forwardMutation d * exponent d *
            (scalar * moment (decrementExponent exponent d) - scalar * moment exponent) -
          rates.backwardMutation d * exponent d * (scalar * moment exponent))) =
          scalar * ∑ d, (rates.forwardMutation d * exponent d *
              (moment (decrementExponent exponent d) - moment exponent) -
            rates.backwardMutation d * exponent d * moment exponent) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    unfold manyDemeMomentGenerator
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [coalescence, migration, mutation]
    simp only [RingHom.id_apply, mul_add]

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

/-- Read one monomial from a constant-augmented moment state.  The all-zero exponent uses the
unique affine constant rather than the rectangular degree-zero padding coordinate. -/
noncomputable def manyDemeMomentStateReadout {D : ℕ} (K : ℕ)
    (state : Option (ManyDemeMomentCoordinate D K) → ℝ)
    (exponent : Fin D → ℕ) : ℝ :=
  if ∀ d, exponent d = 0 then state none
  else manyDemeMomentVectorTable K (fun coordinate ↦ state (some coordinate)) exponent

/-- One-hot terminal probe representing a requested mixed monomial on the augmented moment
carrier.  Out-of-rectangle exponents produce the zero probe, matching the state readout. -/
noncomputable def manyDemeMomentReadoutProbe {D : ℕ} (K : ℕ)
    (exponent : Fin D → ℕ) : Option (ManyDemeMomentCoordinate D K) → ℝ := by
  classical
  exact if hzero : ∀ d, exponent d = 0 then
      fun coordinate ↦ if coordinate = none then 1 else 0
    else if hbound : ∀ d, exponent d < K + 1 then
      let coordinate : ManyDemeMomentCoordinate D K :=
        fun d ↦ ⟨exponent d, hbound d⟩
      fun candidate ↦ if candidate = some coordinate then 1 else 0
    else 0

/-- Pairing the monomial probe with any augmented state gives exactly the corresponding
mixed-moment readout. -/
theorem manyDemeMomentReadoutProbe_dotProduct {D : ℕ} (K : ℕ)
    (exponent : Fin D → ℕ)
    (state : Option (ManyDemeMomentCoordinate D K) → ℝ) :
    manyDemeMomentReadoutProbe K exponent ⬝ᵥ state =
      manyDemeMomentStateReadout K state exponent := by
  classical
  by_cases hzero : ∀ d, exponent d = 0
  · simp [manyDemeMomentReadoutProbe, manyDemeMomentStateReadout, hzero, dotProduct]
  · by_cases hbound : ∀ d, exponent d < K + 1
    · simp [manyDemeMomentReadoutProbe, manyDemeMomentStateReadout,
        manyDemeMomentVectorTable, hzero, hbound, dotProduct]
    · simp [manyDemeMomentReadoutProbe, manyDemeMomentStateReadout,
        manyDemeMomentVectorTable, hzero, hbound]

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

/-- A genuinely biological nonconstant moment coordinate.  Unlike the rectangular carrier,
this type cannot represent the duplicated all-zero coordinate or any total degree above `K`. -/
structure PositiveManyDemeMomentCoordinate (D K : ℕ) where
  coordinate : ManyDemeMomentCoordinate D K
  degree_pos : 0 < coordinate.degree
  degree_le : coordinate.degree ≤ K
  deriving DecidableEq

instance positiveManyDemeMomentCoordinateFinite (D K : ℕ) :
    Finite (PositiveManyDemeMomentCoordinate D K) := by
  apply Finite.of_injective
    (fun coordinate : PositiveManyDemeMomentCoordinate D K ↦ coordinate.coordinate)
  intro left right equal
  cases left
  cases right
  cases equal
  rfl

noncomputable instance positiveManyDemeMomentCoordinateFintype (D K : ℕ) :
    Fintype (PositiveManyDemeMomentCoordinate D K) :=
  Fintype.ofFinite _

/-- Merge a positive moment coordinate across a genuine split. -/
def PositiveManyDemeMomentCoordinate.mergeSplit {D K : ℕ}
    (coordinate : PositiveManyDemeMomentCoordinate D K)
    (parent child : Fin D) (distinct : parent ≠ child) :
    PositiveManyDemeMomentCoordinate D K :=
  { coordinate := fun deme ↦
      ⟨mergeSplitExponent parent child
          (fun d ↦ (coordinate.coordinate d).val) deme,
        mergeSplitExponent_lt_of_sum_le coordinate.coordinate parent child distinct
          coordinate.degree_le deme⟩
    degree_pos := by
      unfold ManyDemeMomentCoordinate.degree
      simpa [sum_mergeSplitExponent parent child distinct]
        using coordinate.degree_pos
    degree_le := by
      unfold ManyDemeMomentCoordinate.degree
      simpa [sum_mergeSplitExponent parent child distinct]
        using coordinate.degree_le }

/-- Minimal normalized moment carrier: one constant plus exactly the positive mixed moments
of total degree at most `K`. -/
abbrev BiologicalManyDemeMomentCoordinate (D K : ℕ) :=
  Option (PositiveManyDemeMomentCoordinate D K)

/-- Merge a normalized moment coordinate across a split; the unique constant stays constant. -/
def BiologicalManyDemeMomentCoordinate.mergeSplit {D K : ℕ}
    (coordinate : BiologicalManyDemeMomentCoordinate D K)
    (parent child : Fin D) (distinct : parent ≠ child) :
    BiologicalManyDemeMomentCoordinate D K :=
  coordinate.map fun positive ↦ positive.mergeSplit parent child distinct

/-- Sparse compact moment split matrix.  A post-split moment reads the unique pre-split
moment obtained by merging child exponents into the parent. -/
noncomputable def biologicalManyDemeMomentSplitPropagator {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child) :
    Matrix (BiologicalManyDemeMomentCoordinate D K)
      (BiologicalManyDemeMomentCoordinate D K) ℝ :=
  fun row column ↦ if column = row.mergeSplit parent child distinct then 1 else 0

/-- The compact moment split matrix performs exactly its deterministic merge lookup. -/
theorem biologicalManyDemeMomentSplitPropagator_mulVec {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child)
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (biologicalManyDemeMomentSplitPropagator parent child distinct).mulVec state =
      fun row ↦ state (row.mergeSplit parent child distinct) := by
  funext row
  simp [biologicalManyDemeMomentSplitPropagator, Matrix.mulVec, dotProduct]

/-- Forget the biological proof and embed the minimal carrier in the old rectangular affine
carrier. -/
def BiologicalManyDemeMomentCoordinate.toAffine {D K : ℕ} :
    BiologicalManyDemeMomentCoordinate D K → AffineManyDemeMomentCoordinate D K
  | none => none
  | some coordinate => some coordinate.coordinate

/-- Restrict a rectangular affine state to its unique biological coordinates. -/
def restrictAffineManyDemeMomentState {D K : ℕ}
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    BiologicalManyDemeMomentCoordinate D K → ℝ :=
  fun coordinate ↦ state coordinate.toAffine

/-- Embed a compact biological state into the old rectangular affine carrier, assigning zero
to the duplicated degree-zero coordinate and every above-`K` padding coordinate. -/
noncomputable def extendBiologicalManyDemeMomentState {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ
  | none => state none
  | some coordinate =>
      if h : 0 < coordinate.degree ∧ coordinate.degree ≤ K then
        state (some ⟨coordinate, h.1, h.2⟩)
      else 0

/-- Restricting after zero-padding extension is exactly the original compact state. -/
theorem restrictAffine_extendBiologicalManyDemeMomentState {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    restrictAffineManyDemeMomentState (extendBiologicalManyDemeMomentState state) = state := by
  funext coordinate
  cases coordinate with
  | none => rfl
  | some coordinate =>
      simp [restrictAffineManyDemeMomentState,
        BiologicalManyDemeMomentCoordinate.toAffine,
        extendBiologicalManyDemeMomentState, coordinate.degree_pos, coordinate.degree_le]

/-- The compact extension always zeros the duplicated rectangular constant coordinate. -/
theorem extendBiologicalManyDemeMomentState_zeroPadding {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    extendBiologicalManyDemeMomentState state (some (fun _ ↦ 0)) = 0 := by
  simp [extendBiologicalManyDemeMomentState, ManyDemeMomentCoordinate.degree]

/-- The compact extension vanishes at every nonbiological rectangular coordinate. -/
theorem extendBiologicalManyDemeMomentState_padding {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (coordinate : ManyDemeMomentCoordinate D K)
    (padding : ¬(0 < coordinate.degree ∧ coordinate.degree ≤ K)) :
    extendBiologicalManyDemeMomentState state (some coordinate) = 0 := by
  simp [extendBiologicalManyDemeMomentState, padding]

/-- Linear zero-padding embedding of the compact moment carrier. -/
noncomputable def extendBiologicalManyDemeMomentLinearMap {D K : ℕ} :
    (BiologicalManyDemeMomentCoordinate D K → ℝ) →ₗ[ℝ]
      (AffineManyDemeMomentCoordinate D K → ℝ) where
  toFun := extendBiologicalManyDemeMomentState
  map_add' := by
    intro left right
    funext coordinate
    cases coordinate with
    | none => rfl
    | some coordinate =>
        by_cases biological : 0 < coordinate.degree ∧ coordinate.degree ≤ K
        · simp [extendBiologicalManyDemeMomentState, biological, Pi.add_apply]
        · simp [extendBiologicalManyDemeMomentState, biological]
  map_smul' := by
    intro scalar state
    funext coordinate
    cases coordinate with
    | none => rfl
    | some coordinate =>
        by_cases biological : 0 < coordinate.degree ∧ coordinate.degree ≤ K
        · simp [extendBiologicalManyDemeMomentState, biological, Pi.smul_apply]
        · simp [extendBiologicalManyDemeMomentState, biological]

/-- Matrix of the compact-to-rectangular zero-padding embedding. -/
noncomputable def extendBiologicalManyDemeMomentMatrix (D K : ℕ) :
    Matrix (AffineManyDemeMomentCoordinate D K)
      (BiologicalManyDemeMomentCoordinate D K) ℝ :=
  LinearMap.toMatrix' (extendBiologicalManyDemeMomentLinearMap (D := D) (K := K))

/-- Applying the embedding matrix is exactly zero-padding extension. -/
theorem extendBiologicalManyDemeMomentMatrix_mulVec {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (extendBiologicalManyDemeMomentMatrix D K).mulVec state =
      extendBiologicalManyDemeMomentState state := by
  exact LinearMap.toMatrix'_mulVec _ _

/-- The biological embedding is injective, so no two normalized coordinates are identified. -/
theorem BiologicalManyDemeMomentCoordinate.toAffine_injective {D K : ℕ} :
    Function.Injective
      (BiologicalManyDemeMomentCoordinate.toAffine :
        BiologicalManyDemeMomentCoordinate D K → AffineManyDemeMomentCoordinate D K) := by
  intro left right equal
  cases left with
  | none => cases right <;> simp_all [BiologicalManyDemeMomentCoordinate.toAffine]
  | some left =>
      cases right with
      | none => simp_all [BiologicalManyDemeMomentCoordinate.toAffine]
      | some right =>
          simp only [BiologicalManyDemeMomentCoordinate.toAffine, Option.some.injEq] at equal
          apply congrArg some
          cases left
          cases right
          cases equal
          rfl

/-- Exponent represented by a minimal biological moment coordinate. -/
def BiologicalManyDemeMomentCoordinate.exponent {D K : ℕ}
    (coordinate : BiologicalManyDemeMomentCoordinate D K) : Fin D → ℕ :=
  match coordinate with
  | none => fun _ ↦ 0
  | some positive => fun deme ↦ (positive.coordinate deme).val

/-- The exponent encoding of the compact biological moment carrier is injective. -/
theorem BiologicalManyDemeMomentCoordinate.exponent_injective {D K : ℕ} :
    Function.Injective
      (BiologicalManyDemeMomentCoordinate.exponent :
        BiologicalManyDemeMomentCoordinate D K → Fin D → ℕ) := by
  intro left right equal
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          have degreeZero : right.coordinate.degree = 0 := by
            unfold ManyDemeMomentCoordinate.degree
            apply Finset.sum_eq_zero
            intro deme _
            have component := congrFun equal deme
            simpa [BiologicalManyDemeMomentCoordinate.exponent] using component.symm
          exact False.elim ((Nat.ne_of_gt right.degree_pos) degreeZero)
  | some left =>
      cases right with
      | none =>
          have degreeZero : left.coordinate.degree = 0 := by
            unfold ManyDemeMomentCoordinate.degree
            apply Finset.sum_eq_zero
            intro deme _
            have component := congrFun equal deme
            simpa [BiologicalManyDemeMomentCoordinate.exponent] using component
          exact False.elim ((Nat.ne_of_gt left.degree_pos) degreeZero)
      | some right =>
          apply congrArg some
          cases left with
          | mk leftCoordinate leftPositive leftBound =>
              cases right with
              | mk rightCoordinate rightPositive rightBound =>
                  have coordinateEqual : leftCoordinate = rightCoordinate := by
                    funext deme
                    apply Fin.ext
                    have component := congrFun equal deme
                    simpa [BiologicalManyDemeMomentCoordinate.exponent] using component
                  cases coordinateEqual
                  rfl

/-- Moment table represented by one minimal biological basis column.  It is the exact
Kronecker table at the column's unrestricted monomial exponent. -/
noncomputable def biologicalManyDemeMomentColumnTable {D K : ℕ}
    (column : BiologicalManyDemeMomentCoordinate D K) : (Fin D → ℕ) → ℝ :=
  fun exponent ↦ if Finsupp.equivFunOnFinite.symm exponent =
      Finsupp.equivFunOnFinite.symm column.exponent then 1 else 0

/-- The compact constant column is exactly the established normalized constant table. -/
theorem biologicalManyDemeMomentColumnTable_none {D K : ℕ} :
    biologicalManyDemeMomentColumnTable
        (none : BiologicalManyDemeMomentCoordinate D K) =
      manyDemeMomentConstantTable := by
  funext exponent
  by_cases zero : exponent = fun _ ↦ 0
  · subst exponent
    simp [biologicalManyDemeMomentColumnTable, manyDemeMomentConstantTable,
      BiologicalManyDemeMomentCoordinate.exponent]
  · have not_all_zero : ¬∀ deme, exponent deme = 0 := by
      intro all_zero
      apply zero
      funext deme
      exact all_zero deme
    simp [biologicalManyDemeMomentColumnTable, manyDemeMomentConstantTable,
      BiologicalManyDemeMomentCoordinate.exponent, zero, not_all_zero]

/-- Every compact positive column is exactly its established rectangular basis table. -/
theorem biologicalManyDemeMomentColumnTable_some {D K : ℕ}
    (column : PositiveManyDemeMomentCoordinate D K) :
    biologicalManyDemeMomentColumnTable
        (some column : BiologicalManyDemeMomentCoordinate D K) =
      manyDemeMomentBasisTable K column.coordinate := by
  funext exponent
  by_cases bound : ∀ deme, exponent deme < K + 1
  · have equality_iff :
        Finsupp.equivFunOnFinite.symm exponent =
            Finsupp.equivFunOnFinite.symm
              (BiologicalManyDemeMomentCoordinate.exponent
                (some column : BiologicalManyDemeMomentCoordinate D K)) ↔
          (fun deme ↦ ⟨exponent deme, bound deme⟩ : ManyDemeMomentCoordinate D K) =
            column.coordinate := by
      constructor
      · intro equal
        funext deme
        apply Fin.ext
        exact congrArg (fun value : Fin D →₀ ℕ ↦ value deme) equal
      · intro equal
        apply Finsupp.ext
        intro deme
        have component := congrFun equal deme
        exact congrArg Fin.val component
    simp [biologicalManyDemeMomentColumnTable, manyDemeMomentBasisTable,
      manyDemeMomentVectorTable, bound, equality_iff]
  · have exponent_ne :
        Finsupp.equivFunOnFinite.symm exponent ≠
          Finsupp.equivFunOnFinite.symm
            (BiologicalManyDemeMomentCoordinate.exponent
              (some column : BiologicalManyDemeMomentCoordinate D K)) := by
      intro equal
      apply bound
      intro deme
      have component := congrArg (fun value : Fin D →₀ ℕ ↦ value deme) equal
      have value_equal : exponent deme = (column.coordinate deme).val := by
        simpa [BiologicalManyDemeMomentCoordinate.exponent] using component
      rw [value_equal]
      exact (column.coordinate deme).isLt
    simp [biologicalManyDemeMomentColumnTable, manyDemeMomentBasisTable,
      manyDemeMomentVectorTable, bound, exponent_ne]

/-- Monomial represented by a minimal biological moment coordinate. -/
noncomputable def biologicalManyDemeMomentColumnPolynomial {D K : ℕ}
    (coordinate : BiologicalManyDemeMomentCoordinate D K) :
    MvPolynomial (Fin D) ℝ :=
  MvPolynomial.monomial
    (Finsupp.equivFunOnFinite.symm coordinate.exponent) 1

/-- The biological moment tables and monomial polynomials are exactly biorthogonal. -/
theorem biologicalManyDemeMomentColumn_biorthogonal {D K : ℕ}
    (row column : BiologicalManyDemeMomentCoordinate D K) :
    manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable column)
        (biologicalManyDemeMomentColumnPolynomial row) =
      if column = row then 1 else 0 := by
  rw [biologicalManyDemeMomentColumnPolynomial,
    manyDemePolynomialMomentFunctional_monomial_one]
  unfold biologicalManyDemeMomentColumnTable
  rw [if_congr (by
    constructor
    · intro exponentEqual
      apply BiologicalManyDemeMomentCoordinate.exponent_injective
      exact Finsupp.equivFunOnFinite.symm.injective exponentEqual.symm
    · intro coordinateEqual
      subst column
      rfl) rfl rfl]

/-- A biological column functional is exactly coefficient extraction at its monomial. -/
theorem biologicalManyDemeMomentColumnFunctional_eq_coeff {D K : ℕ}
    (column : BiologicalManyDemeMomentCoordinate D K)
    (polynomial : MvPolynomial (Fin D) ℝ) :
    manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable column)
        polynomial =
      polynomial.coeff (Finsupp.equivFunOnFinite.symm column.exponent) := by
  classical
  rw [manyDemePolynomialMomentFunctional_eq_sum]
  simp [biologicalManyDemeMomentColumnTable, MvPolynomial.mem_support_iff]
  change (if polynomial.coeff (Finsupp.equivFunOnFinite.symm column.exponent) = 0 then 0
      else polynomial.coeff (Finsupp.equivFunOnFinite.symm column.exponent)) =
    polynomial.coeff (Finsupp.equivFunOnFinite.symm column.exponent)
  split_ifs <;> simp_all

/-- Reconstruct a polynomial from its coefficients on the compact biological monomial basis. -/
noncomputable def biologicalManyDemePolynomialSynthesis {D K : ℕ}
    (coefficient : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    MvPolynomial (Fin D) ℝ :=
  ∑ coordinate, coefficient coordinate •
    biologicalManyDemeMomentColumnPolynomial coordinate

/-- The compact biological basis reconstructs every polynomial of total degree at most `K`
exactly. -/
theorem biologicalManyDemePolynomialSynthesis_coefficients {D K : ℕ}
    (polynomial : MvPolynomial (Fin D) ℝ) (degree_le : polynomial.totalDegree ≤ K) :
    biologicalManyDemePolynomialSynthesis (D := D) (K := K)
        (fun coordinate ↦ manyDemePolynomialMomentFunctional
          (biologicalManyDemeMomentColumnTable coordinate) polynomial) = polynomial := by
  classical
  apply MvPolynomial.ext
  intro exponent
  simp only [biologicalManyDemePolynomialSynthesis, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul,
    biologicalManyDemeMomentColumnFunctional_eq_coeff,
    biologicalManyDemeMomentColumnPolynomial, MvPolynomial.coeff_monomial,
    smul_eq_mul]
  let exponentFunction : Fin D → ℕ := fun deme ↦ exponent deme
  have exponentSum : (∑ deme, exponentFunction deme) = exponent.sum fun _ power ↦ power := by
    simp [exponentFunction, Finsupp.sum_fintype]
  by_cases exponentDegree : (∑ deme, exponentFunction deme) ≤ K
  · by_cases exponentPositive : 0 < ∑ deme, exponentFunction deme
    · let coordinate : ManyDemeMomentCoordinate D K := fun deme ↦
        ⟨exponentFunction deme, by
          have coordinate_le : exponentFunction deme ≤ ∑ d, exponentFunction d :=
            Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponentFunction d))
              (Finset.mem_univ deme)
          omega⟩
      let positive : PositiveManyDemeMomentCoordinate D K := {
        coordinate := coordinate
        degree_pos := by simpa [coordinate, ManyDemeMomentCoordinate.degree]
        degree_le := by simpa [coordinate, ManyDemeMomentCoordinate.degree] }
      have selectedPositive : Finsupp.equivFunOnFinite.symm
          (BiologicalManyDemeMomentCoordinate.exponent
            (some positive : BiologicalManyDemeMomentCoordinate D K)) = exponent := by
        apply Finsupp.ext
        intro deme
        simp [BiologicalManyDemeMomentCoordinate.exponent, positive, coordinate,
          exponentFunction]
      rw [Finset.sum_eq_single (some positive)]
      · simp [selectedPositive]
      · intro other _ distinct
        have exponent_ne :
            Finsupp.equivFunOnFinite.symm
              (BiologicalManyDemeMomentCoordinate.exponent other) ≠ exponent := by
          intro equal
          apply distinct
          cases other with
          | none =>
              have zero : ∀ deme, exponentFunction deme = 0 := by
                intro deme
                have := congrArg (fun e : Fin D →₀ ℕ ↦ e deme) equal
                simpa [BiologicalManyDemeMomentCoordinate.exponent, exponentFunction] using this.symm
              have : (∑ deme, exponentFunction deme) = 0 := by simp [zero]
              omega
          | some other =>
              exact BiologicalManyDemeMomentCoordinate.exponent_injective
                (Finsupp.equivFunOnFinite.symm.injective
                  (equal.trans selectedPositive.symm))
        simp [exponent_ne]
      · simp
    · have exponentZero : exponent = 0 := by
        apply Finsupp.ext
        intro deme
        have coordinate_le : exponentFunction deme ≤ ∑ d, exponentFunction d :=
          Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponentFunction d))
            (Finset.mem_univ deme)
        have : exponentFunction deme = 0 := by omega
        simpa [exponentFunction] using this
      subst exponent
      have selectedNone : Finsupp.equivFunOnFinite.symm
          (BiologicalManyDemeMomentCoordinate.exponent
            (none : BiologicalManyDemeMomentCoordinate D K)) = 0 := by
        apply Finsupp.ext
        intro deme
        simp [BiologicalManyDemeMomentCoordinate.exponent]
      rw [Finset.sum_eq_single none]
      · simp [selectedNone]
      · intro other _ distinct
        cases other with
        | none => exact (distinct rfl).elim
        | some other =>
            have nonzero : Finsupp.equivFunOnFinite.symm
                (BiologicalManyDemeMomentCoordinate.exponent
                  (some other : BiologicalManyDemeMomentCoordinate D K)) ≠ 0 := by
              intro equal
              have degree_zero : other.coordinate.degree = 0 := by
                unfold ManyDemeMomentCoordinate.degree
                apply Finset.sum_eq_zero
                intro deme _
                have := congrArg (fun e : Fin D →₀ ℕ ↦ e deme) equal
                simpa [BiologicalManyDemeMomentCoordinate.exponent] using this
              exact (Nat.ne_of_gt other.degree_pos) degree_zero
            simp [nonzero]
      · simp
  · have coefficientZero : polynomial.coeff exponent = 0 := by
      by_contra nonzero
      have member : exponent ∈ polynomial.support := by
        exact MvPolynomial.mem_support_iff.mpr nonzero
      have supportDegree := (MvPolynomial.le_totalDegree member).trans degree_le
      rw [← exponentSum] at supportDegree
      omega
    rw [coefficientZero]
    apply Finset.sum_eq_zero
    intro coordinate _
    have exponent_ne : Finsupp.equivFunOnFinite.symm
        (BiologicalManyDemeMomentCoordinate.exponent coordinate) ≠ exponent := by
      intro equal
      have coordinateDegree : (∑ deme, coordinate.exponent deme) ≤ K := by
        cases coordinate with
        | none => simp [BiologicalManyDemeMomentCoordinate.exponent]
        | some coordinate =>
            simpa [BiologicalManyDemeMomentCoordinate.exponent,
              ManyDemeMomentCoordinate.degree] using coordinate.degree_le
      have functionEqual : coordinate.exponent = exponentFunction := by
        funext deme
        have := congrArg (fun e : Fin D →₀ ℕ ↦ e deme) equal
        simpa [exponentFunction] using this
      rw [functionEqual] at coordinateDegree
      exact exponentDegree coordinateDegree
    simp [exponent_ne]

/-- Substituting the split constraint into a compact moment column monomial gives the monomial
of its merged biological coordinate. -/
theorem splitManyDemePolynomial_biologicalColumn {D K : ℕ}
    (row : BiologicalManyDemeMomentCoordinate D K)
    (parent child : Fin D) (distinct : parent ≠ child) :
    splitManyDemePolynomial parent child
        (biologicalManyDemeMomentColumnPolynomial row) =
      biologicalManyDemeMomentColumnPolynomial
        (row.mergeSplit parent child distinct) := by
  rw [biologicalManyDemeMomentColumnPolynomial,
    ← manyDemeBernsteinPolynomial_zeroAncestral_eq_monomial row.exponent,
    splitManyDemePolynomial_bernstein parent child distinct,
    biologicalManyDemeMomentColumnPolynomial,
    ← manyDemeBernsteinPolynomial_zeroAncestral_eq_monomial]
  congr 1 <;>
    funext deme <;>
    cases row <;>
    simp [BiologicalManyDemeMomentCoordinate.mergeSplit,
      PositiveManyDemeMomentCoordinate.mergeSplit,
      BiologicalManyDemeMomentCoordinate.exponent, mergeSplitExponent]

/-- Splitting a degree-bounded polynomial is the sum of the split images of its compact
monomial coefficients. -/
theorem splitManyDemePolynomial_eq_compactSum {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child)
    (polynomial : MvPolynomial (Fin D) ℝ) (degree_le : polynomial.totalDegree ≤ K) :
    splitManyDemePolynomial parent child polynomial =
      ∑ row : BiologicalManyDemeMomentCoordinate D K,
        manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable row)
            polynomial •
          biologicalManyDemeMomentColumnPolynomial
            (row.mergeSplit parent child distinct) := by
  conv_lhs => rw [← biologicalManyDemePolynomialSynthesis_coefficients polynomial degree_le]
  unfold biologicalManyDemePolynomialSynthesis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [map_smul, splitManyDemePolynomial_biologicalColumn row parent child distinct]

/-- Coefficient extraction after split substitution is exactly multiplication by the transpose
of the compact moment split matrix.  The transpose is essential: substitution can merge several
pre-split monomials into one post-split monomial, so coefficients are pushed forward by summing
all preimages while moment states themselves are pulled back by the untransposed matrix. -/
theorem biologicalMomentSplit_coefficients {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child)
    (polynomial : MvPolynomial (Fin D) ℝ) (degree_le : polynomial.totalDegree ≤ K)
    (column : BiologicalManyDemeMomentCoordinate D K) :
    manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable column)
        (splitManyDemePolynomial parent child polynomial) =
      (biologicalManyDemeMomentSplitPropagator parent child distinct).transpose.mulVec
        (fun row ↦ manyDemePolynomialMomentFunctional
          (biologicalManyDemeMomentColumnTable row) polynomial) column := by
  rw [splitManyDemePolynomial_eq_compactSum parent child distinct polynomial degree_le,
    biologicalManyDemeMomentColumnFunctional_eq_coeff]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    biologicalManyDemeMomentColumnFunctional_eq_coeff,
    biologicalManyDemeMomentColumnPolynomial, MvPolynomial.coeff_monomial,
    smul_eq_mul]
  unfold Matrix.mulVec dotProduct Matrix.transpose biologicalManyDemeMomentSplitPropagator
  apply Finset.sum_congr rfl
  intro row _
  by_cases equal : column = row.mergeSplit parent child distinct
  · subst column
    simp
  · have exponent_ne :
        Finsupp.equivFunOnFinite.symm
            (row.mergeSplit parent child distinct).exponent ≠
          Finsupp.equivFunOnFinite.symm column.exponent := by
      intro exponentEqual
      apply equal
      apply BiologicalManyDemeMomentCoordinate.exponent_injective
      exact Finsupp.equivFunOnFinite.symm.injective exponentEqual.symm
    simp [equal, exponent_ne]

/-- Synthesize the unrestricted mixed-moment table represented by a vector on the minimal
biological carrier. -/
noncomputable def biologicalManyDemeMomentSynthesis {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) : (Fin D → ℕ) → ℝ :=
  fun exponent ↦ ∑ column,
    state column * biologicalManyDemeMomentColumnTable column exponent

/-- Synthesis reads the explicit constant coordinate at the zero exponent. -/
theorem biologicalManyDemeMomentSynthesis_zero {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    biologicalManyDemeMomentSynthesis state (fun _ ↦ 0) = state none := by
  classical
  unfold biologicalManyDemeMomentSynthesis
  rw [Finset.sum_eq_single none]
  · simp [biologicalManyDemeMomentColumnTable,
      BiologicalManyDemeMomentCoordinate.exponent]
  · intro other _ distinct
    have exponent_ne : Finsupp.equivFunOnFinite.symm (fun _ : Fin D ↦ 0) ≠
        Finsupp.equivFunOnFinite.symm
          (BiologicalManyDemeMomentCoordinate.exponent other) := by
      intro equal
      apply distinct
      apply BiologicalManyDemeMomentCoordinate.exponent_injective
      exact Finsupp.equivFunOnFinite.symm.injective equal.symm
    change state other *
      (if Finsupp.equivFunOnFinite.symm (fun _ : Fin D ↦ 0) =
          Finsupp.equivFunOnFinite.symm
            (BiologicalManyDemeMomentCoordinate.exponent other) then 1 else 0) = 0
    rw [if_neg exponent_ne]
    ring
  · simp

/-- Synthesis reads the unique positive biological coordinate at every in-range exponent. -/
theorem biologicalManyDemeMomentSynthesis_positive {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (exponent : Fin D → ℕ) (degree_pos : 0 < ∑ deme, exponent deme)
    (degree_le : (∑ deme, exponent deme) ≤ K) :
    biologicalManyDemeMomentSynthesis state exponent =
      state (some {
        coordinate := fun deme ↦ ⟨exponent deme, by
          have coordinate_le : exponent deme ≤ ∑ d, exponent d :=
            Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d))
              (Finset.mem_univ deme)
          omega⟩
        degree_pos := by simpa [ManyDemeMomentCoordinate.degree]
        degree_le := by simpa [ManyDemeMomentCoordinate.degree] }) := by
  classical
  let coordinate : ManyDemeMomentCoordinate D K := fun deme ↦
    ⟨exponent deme, by
      have coordinate_le : exponent deme ≤ ∑ d, exponent d :=
        Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d))
          (Finset.mem_univ deme)
      omega⟩
  let positive : PositiveManyDemeMomentCoordinate D K := {
    coordinate := coordinate
    degree_pos := by simpa [coordinate, ManyDemeMomentCoordinate.degree]
    degree_le := by simpa [coordinate, ManyDemeMomentCoordinate.degree] }
  change biologicalManyDemeMomentSynthesis state exponent = state (some positive)
  have selected : BiologicalManyDemeMomentCoordinate.exponent
      (some positive : BiologicalManyDemeMomentCoordinate D K) = exponent := by
    funext deme
    rfl
  unfold biologicalManyDemeMomentSynthesis
  rw [Finset.sum_eq_single (some positive)]
  · change state (some positive) *
        (if Finsupp.equivFunOnFinite.symm exponent =
            Finsupp.equivFunOnFinite.symm
              (BiologicalManyDemeMomentCoordinate.exponent
                (some positive : BiologicalManyDemeMomentCoordinate D K)) then 1 else 0) =
          state (some positive)
    rw [if_pos (congrArg Finsupp.equivFunOnFinite.symm selected.symm)]
    ring
  · intro other _ distinct
    have exponent_ne : Finsupp.equivFunOnFinite.symm exponent ≠
        Finsupp.equivFunOnFinite.symm
          (BiologicalManyDemeMomentCoordinate.exponent other) := by
      intro equal
      apply distinct
      apply BiologicalManyDemeMomentCoordinate.exponent_injective
      exact (Finsupp.equivFunOnFinite.symm.injective equal).symm.trans selected.symm
    change state other *
      (if Finsupp.equivFunOnFinite.symm exponent =
          Finsupp.equivFunOnFinite.symm
            (BiologicalManyDemeMomentCoordinate.exponent other) then 1 else 0) = 0
    rw [if_neg exponent_ne]
    ring
  · simp

/-- Compact synthesis and rectangular state readout are exactly the same representation on
every monomial through total degree `K`.  This is the scalar form of the zero-padding embedding
and includes the normalized degree-zero monomial. -/
theorem biologicalManyDemeMomentSynthesis_eq_stateReadout {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (exponent : Fin D → ℕ) (degree_le : (∑ deme, exponent deme) ≤ K) :
    biologicalManyDemeMomentSynthesis state exponent =
      manyDemeMomentStateReadout K (extendBiologicalManyDemeMomentState state) exponent := by
  classical
  by_cases degree_zero : (∑ deme, exponent deme) = 0
  · have exponent_zero : exponent = fun _ ↦ 0 := by
      funext deme
      have component_le : exponent deme ≤ ∑ d, exponent d :=
        Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d))
          (Finset.mem_univ deme)
      omega
    subst exponent
    rw [biologicalManyDemeMomentSynthesis_zero]
    simp [manyDemeMomentStateReadout, extendBiologicalManyDemeMomentState]
  · have degree_pos : 0 < ∑ deme, exponent deme := Nat.pos_of_ne_zero degree_zero
    have nonzero : ¬∀ deme, exponent deme = 0 := by
      intro all_zero
      apply degree_zero
      simp [all_zero]
    have bound : ∀ deme, exponent deme < K + 1 := by
      intro deme
      have component_le : exponent deme ≤ ∑ d, exponent d :=
        Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d))
          (Finset.mem_univ deme)
      omega
    rw [biologicalManyDemeMomentSynthesis_positive state exponent degree_pos degree_le]
    simp [manyDemeMomentStateReadout, manyDemeMomentVectorTable,
      extendBiologicalManyDemeMomentState, nonzero, bound,
      ManyDemeMomentCoordinate.degree, degree_pos, degree_le]

/-- A polynomial moment of a synthesized state is the same finite linear combination of its
basis-column polynomial moments. -/
theorem manyDemePolynomialMomentFunctional_biologicalSynthesis {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (polynomial : MvPolynomial (Fin D) ℝ) :
    manyDemePolynomialMomentFunctional
        (biologicalManyDemeMomentSynthesis state) polynomial =
      ∑ column, state column *
        manyDemePolynomialMomentFunctional
          (biologicalManyDemeMomentColumnTable column) polynomial := by
  rw [manyDemePolynomialMomentFunctional_eq_sum]
  unfold biologicalManyDemeMomentSynthesis
  change (∑ exponent ∈ polynomial.support,
      polynomial.coeff exponent *
        ∑ column, state column * biologicalManyDemeMomentColumnTable column
          (fun deme ↦ exponent deme)) =
    ∑ column, state column *
      ∑ exponent ∈ polynomial.support,
        polynomial.coeff exponent *
          biologicalManyDemeMomentColumnTable column (fun deme ↦ exponent deme)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro column _
  apply Finset.sum_congr rfl
  intro exponent _
  ring

/-- The moment generator commutes with finite synthesis on the biological carrier. -/
theorem manyDemeMomentGenerator_biologicalSynthesis {D K : ℕ}
    (rates : ManyDemeRates D)
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (exponent : Fin D → ℕ) :
    manyDemeMomentGenerator rates (biologicalManyDemeMomentSynthesis state) exponent =
      ∑ column, state column *
        manyDemeMomentGenerator rates
          (biologicalManyDemeMomentColumnTable column) exponent := by
  let generator := manyDemeMomentGeneratorLinearMapAt rates exponent
  have synthesis_eq : biologicalManyDemeMomentSynthesis state =
      ∑ column, state column • biologicalManyDemeMomentColumnTable column := by
    funext requested
    simp [biologicalManyDemeMomentSynthesis]
  change generator (biologicalManyDemeMomentSynthesis state) = _
  rw [synthesis_eq, map_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [generator, manyDemeMomentGeneratorLinearMapAt]

/-- Exact normalized generator without rectangular padding or an affine forcing convention. -/
noncomputable def biologicalManyDemeMomentGenerator {D K : ℕ}
    (rates : ManyDemeRates D) :
    Matrix (BiologicalManyDemeMomentCoordinate D K)
      (BiologicalManyDemeMomentCoordinate D K) ℝ
  | none, _ => 0
  | some row, column =>
      manyDemeMomentGenerator rates (biologicalManyDemeMomentColumnTable column)
        (fun deme ↦ (row.coordinate deme).val)

/-- Matrix application of the compact moment generator is the unrestricted generator of the
synthesized table at every biological coordinate. -/
theorem biologicalManyDemeMomentGenerator_mulVec {D K : ℕ}
    (rates : ManyDemeRates D)
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (biologicalManyDemeMomentGenerator rates).mulVec state =
      fun coordinate ↦ match coordinate with
        | none => 0
        | some row => manyDemeMomentGenerator rates
            (biologicalManyDemeMomentSynthesis state)
            (fun deme ↦ (row.coordinate deme).val) := by
  funext coordinate
  cases coordinate with
  | none => simp [Matrix.mulVec, biologicalManyDemeMomentGenerator]
  | some row =>
      change (biologicalManyDemeMomentGenerator rates).mulVec state (some row) =
        manyDemeMomentGenerator rates (biologicalManyDemeMomentSynthesis state)
          (fun deme ↦ (row.coordinate deme).val)
      rw [manyDemeMomentGenerator_biologicalSynthesis]
      unfold Matrix.mulVec dotProduct biologicalManyDemeMomentGenerator
      apply Finset.sum_congr rfl
      intro column _
      ring

/-- Synthesizing one generator column recovers the unrestricted moment-generator column at
every exponent through degree `K`. -/
theorem biologicalManyDemeMomentSynthesis_generatorColumn {D K : ℕ}
    (rates : ManyDemeRates D) (column : BiologicalManyDemeMomentCoordinate D K)
    (exponent : Fin D → ℕ) (degree_le : (∑ deme, exponent deme) ≤ K) :
    biologicalManyDemeMomentSynthesis
        (fun row ↦ biologicalManyDemeMomentGenerator rates row column) exponent =
      manyDemeMomentGenerator rates
        (biologicalManyDemeMomentColumnTable column) exponent := by
  by_cases degree_pos : 0 < ∑ deme, exponent deme
  · rw [biologicalManyDemeMomentSynthesis_positive _ exponent degree_pos degree_le]
    rfl
  · have degree_zero : (∑ deme, exponent deme) = 0 := by omega
    have exponent_zero : exponent = fun _ ↦ 0 := by
      funext deme
      have coordinate_le : exponent deme ≤ ∑ d, exponent d :=
        Finset.single_le_sum (fun d _ ↦ Nat.zero_le (exponent d))
          (Finset.mem_univ deme)
      omega
    subst exponent
    rw [biologicalManyDemeMomentSynthesis_zero]
    simp [biologicalManyDemeMomentGenerator, manyDemeMomentGenerator]

/-- Compact positive-dual Bernstein coefficient projection from the normalized moment
carrier.  Neither side contains a padding coordinate. -/
noncomputable def biologicalManyDemeBernsteinMomentProjection (D K : ℕ) :
    Matrix (BiologicalManyDemeKilledDualCoordinate D K)
      (BiologicalManyDemeMomentCoordinate D K) ℝ :=
  fun row column ↦
    manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable column)
      (manyDemeBernsteinPolynomial
        (fun deme ↦ (row.coordinate.1 deme).val)
        (fun deme ↦ (row.coordinate.2 deme).val))

/-- Matrix multiplication by the compact projection is exactly Bernstein evaluation of the
synthesized moment table. -/
theorem biologicalManyDemeBernsteinMomentProjection_mulVec {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (biologicalManyDemeBernsteinMomentProjection D K).mulVec state =
      fun row ↦ manyDemePolynomialMomentFunctional
        (biologicalManyDemeMomentSynthesis state)
        (manyDemeBernsteinPolynomial
          (fun deme ↦ (row.coordinate.1 deme).val)
          (fun deme ↦ (row.coordinate.2 deme).val)) := by
  funext row
  rw [manyDemePolynomialMomentFunctional_biologicalSynthesis]
  unfold biologicalManyDemeBernsteinMomentProjection Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro column _
  ring

/-- Looking up a projected compact vector is exactly applying the synthesized moment
functional to that Bernstein polynomial. -/
theorem biologicalManyDemeKilledDualVectorTable_projection_mulVec {D K : ℕ}
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ)
    (derived ancestral : Fin D → ℕ)
    (degree_le : (∑ deme, derived deme) + ∑ deme, ancestral deme ≤ K) :
    biologicalManyDemeKilledDualVectorTable
        ((biologicalManyDemeBernsteinMomentProjection D K).mulVec state)
        derived ancestral =
      manyDemePolynomialMomentFunctional (biologicalManyDemeMomentSynthesis state)
        (manyDemeBernsteinPolynomial derived ancestral) := by
  rw [biologicalManyDemeKilledDualVectorTable_of_degree_le _ derived ancestral degree_le,
    biologicalManyDemeBernsteinMomentProjection_mulVec]

/-- Looking up one compact projection column gives its Bernstein moment functional. -/
theorem biologicalManyDemeKilledDualVectorTable_projectionColumn {D K : ℕ}
    (column : BiologicalManyDemeMomentCoordinate D K)
    (derived ancestral : Fin D → ℕ)
    (degree_le : (∑ deme, derived deme) + ∑ deme, ancestral deme ≤ K) :
    biologicalManyDemeKilledDualVectorTable
        (fun row ↦ biologicalManyDemeBernsteinMomentProjection D K row column)
        derived ancestral =
      manyDemePolynomialMomentFunctional
        (biologicalManyDemeMomentColumnTable column)
        (manyDemeBernsteinPolynomial derived ancestral) := by
  rw [biologicalManyDemeKilledDualVectorTable_of_degree_le _ derived ancestral degree_le]
  rfl

/-- One compact moment-generator column projected into Bernstein coordinates is exactly the
unrestricted killed generator applied to that column's Bernstein coefficients.  This theorem
contains the finite degree restriction explicitly and has no padding hypothesis. -/
theorem biologicalManyDemeBernsteinMomentProjection_momentGeneratorColumn {D K : ℕ}
    (rates : ManyDemeRates D)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme)
    (row : BiologicalManyDemeKilledDualCoordinate D K)
    (column : BiologicalManyDemeMomentCoordinate D K) :
    (biologicalManyDemeBernsteinMomentProjection D K).mulVec
        (fun source ↦ biologicalManyDemeMomentGenerator rates source column) row =
      manyDemeKilledDualGenerator rates
        (fun derived ancestral ↦
          manyDemePolynomialMomentFunctional
            (biologicalManyDemeMomentColumnTable column)
            (manyDemeBernsteinPolynomial derived ancestral))
        (fun deme ↦ (row.coordinate.1 deme).val)
        (fun deme ↦ (row.coordinate.2 deme).val) := by
  rw [biologicalManyDemeBernsteinMomentProjection_mulVec]
  let derived : Fin D → ℕ := fun deme ↦ (row.coordinate.1 deme).val
  let ancestral : Fin D → ℕ := fun deme ↦ (row.coordinate.2 deme).val
  have polynomialDegree :
      (manyDemeBernsteinPolynomial derived ancestral).totalDegree ≤ K :=
    (manyDemeBernsteinPolynomial_totalDegree_le derived ancestral).trans (by
      simpa [derived, ancestral, ManyDemeKilledDualCoordinate.degree] using row.degree_le)
  change manyDemePolynomialMomentFunctional
      (biologicalManyDemeMomentSynthesis
        (fun source ↦ biologicalManyDemeMomentGenerator rates source column))
      (manyDemeBernsteinPolynomial derived ancestral) = _
  rw [manyDemePolynomialMomentFunctional_congr_of_totalDegree_le
    (biologicalManyDemeMomentSynthesis
      (fun source ↦ biologicalManyDemeMomentGenerator rates source column))
    (manyDemeMomentGenerator rates (biologicalManyDemeMomentColumnTable column))
    (manyDemeBernsteinPolynomial derived ancestral) polynomialDegree]
  · exact manyDemeMomentGenerator_bernstein_intertwines rates
      (biologicalManyDemeMomentColumnTable column) derived ancestral symmetric
  · intro exponent degree_le
    exact biologicalManyDemeMomentSynthesis_generatorColumn rates column exponent degree_le

/-- One compact killed-generator column action on Bernstein coefficients is exactly the same
unrestricted killed generator appearing on the moment side. -/
theorem biologicalManyDemeKilledDualGenerator_projectionColumn {D K : ℕ}
    (rates : ManyDemeRates D)
    (row : BiologicalManyDemeKilledDualCoordinate D K)
    (column : BiologicalManyDemeMomentCoordinate D K) :
    (biologicalManyDemeKilledDualGenerator rates).mulVec
        (fun target ↦ biologicalManyDemeBernsteinMomentProjection D K target column) row =
      manyDemeKilledDualGenerator rates
        (fun derived ancestral ↦
          manyDemePolynomialMomentFunctional
            (biologicalManyDemeMomentColumnTable column)
            (manyDemeBernsteinPolynomial derived ancestral))
        (fun deme ↦ (row.coordinate.1 deme).val)
        (fun deme ↦ (row.coordinate.2 deme).val) := by
  rw [biologicalManyDemeKilledDualGenerator_mulVec]
  apply manyDemeKilledDualGenerator_congr_of_degree_le
  intro derived ancestral degree_le
  exact biologicalManyDemeKilledDualVectorTable_projectionColumn
    column derived ancestral (degree_le.trans row.degree_le)

/-- **Exact compact finite generator intertwining.**  On carriers containing exactly the
normalized degree-`K` moments and exactly the degree-`K` killed configurations, the Bernstein
coefficient matrix intertwines the two generators with no padding qualification. -/
theorem biologicalManyDemeBernsteinMomentProjection_generator_intertwines {D K : ℕ}
    (rates : ManyDemeRates D)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme) :
    biologicalManyDemeBernsteinMomentProjection D K *
        biologicalManyDemeMomentGenerator rates =
      biologicalManyDemeKilledDualGenerator rates *
        biologicalManyDemeBernsteinMomentProjection D K := by
  apply Matrix.ext
  intro row column
  change (biologicalManyDemeBernsteinMomentProjection D K).mulVec
      (fun source ↦ biologicalManyDemeMomentGenerator rates source column) row =
    (biologicalManyDemeKilledDualGenerator rates).mulVec
      (fun target ↦ biologicalManyDemeBernsteinMomentProjection D K target column) row
  rw [biologicalManyDemeBernsteinMomentProjection_momentGeneratorColumn rates symmetric,
    biologicalManyDemeKilledDualGenerator_projectionColumn]

/-- **Exact finite-time compact epoch intertwining.**  Generator duality lifts through the
absolutely convergent matrix exponential at every real duration.  Thus positive killed-dual
propagation and normalized moment propagation give identical Bernstein coordinates for a
whole epoch, not only to first order. -/
theorem biologicalManyDemeBernsteinMomentProjection_exponential_intertwines {D K : ℕ}
    (rates : ManyDemeRates D)
    (symmetric : ∀ deme,
      rates.backwardMutation deme = rates.forwardMutation deme)
    (duration : ℝ) :
    biologicalManyDemeBernsteinMomentProjection D K *
        matrixExponential (biologicalManyDemeMomentGenerator rates) duration =
      matrixExponential (biologicalManyDemeKilledDualGenerator rates) duration *
        biologicalManyDemeBernsteinMomentProjection D K := by
  exact matrixExponential_intertwines _ _ _
    (biologicalManyDemeBernsteinMomentProjection_generator_intertwines rates symmetric)
    duration

/-- **Exact compact split intertwining.**  Bernstein projection commutes with an
instantaneous population split: either push monomial coefficients through the transpose of
the moment pullback or merge the positive-dual lineages. -/
theorem biologicalManyDemeBernsteinMomentProjection_split_intertwines {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child) :
    biologicalManyDemeBernsteinMomentProjection D K *
        biologicalManyDemeMomentSplitPropagator parent child distinct =
      biologicalManyDemeKilledDualSplitPropagator parent child distinct *
        biologicalManyDemeBernsteinMomentProjection D K := by
  apply Matrix.ext
  intro row column
  change (biologicalManyDemeBernsteinMomentProjection D K).mulVec
      (fun source ↦ biologicalManyDemeMomentSplitPropagator parent child distinct source column)
        row =
    (biologicalManyDemeKilledDualSplitPropagator parent child distinct).mulVec
      (fun target ↦ biologicalManyDemeBernsteinMomentProjection D K target column) row
  rw [biologicalManyDemeKilledDualSplitPropagator_mulVec]
  let polynomial := manyDemeBernsteinPolynomial
    (fun deme ↦ (row.coordinate.1 deme).val)
    (fun deme ↦ (row.coordinate.2 deme).val)
  have degree_le : polynomial.totalDegree ≤ K :=
    (manyDemeBernsteinPolynomial_totalDegree_le _ _).trans (by
      simpa [polynomial, ManyDemeKilledDualCoordinate.degree] using row.degree_le)
  calc
    _ = (biologicalManyDemeMomentSplitPropagator parent child distinct).transpose.mulVec
          (fun source ↦ manyDemePolynomialMomentFunctional
            (biologicalManyDemeMomentColumnTable source) polynomial) column := by
        unfold biologicalManyDemeBernsteinMomentProjection Matrix.mulVec dotProduct
          Matrix.transpose
        apply Finset.sum_congr rfl
        intro source _
        simp [polynomial]
        ring
    _ = manyDemePolynomialMomentFunctional (biologicalManyDemeMomentColumnTable column)
          (splitManyDemePolynomial parent child polynomial) :=
        (biologicalMomentSplit_coefficients parent child distinct polynomial degree_le column).symm
    _ = biologicalManyDemeBernsteinMomentProjection D K
          (row.mergeSplit parent child distinct) column := by
        unfold biologicalManyDemeBernsteinMomentProjection polynomial
        rw [splitManyDemePolynomial_bernstein parent child distinct,
          ← biologicalKilledDual_mergeSplit_bernsteinPolynomial]

/-- One compact demographic instruction, with symmetric biallelic mutation made explicit in
the epoch constructor and genuine parent/child distinction made explicit in the split. -/
inductive BiologicalManyDemeInstruction (D K : ℕ) where
  | evolve (rates : ManyDemeRates D) (duration : ℝ) (duration_nonneg : 0 ≤ duration)
      (symmetric : ∀ deme, rates.backwardMutation deme = rates.forwardMutation deme)
  | split (parent child : Fin D) (distinct : parent ≠ child)

/-- Exact compact forward moment matrix for one demographic instruction. -/
noncomputable def BiologicalManyDemeInstruction.momentPropagator {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K) :
    Matrix (BiologicalManyDemeMomentCoordinate D K)
      (BiologicalManyDemeMomentCoordinate D K) ℝ :=
  match instruction with
  | .evolve rates duration _ _ =>
      matrixExponential (biologicalManyDemeMomentGenerator rates) duration
  | .split parent child distinct =>
      biologicalManyDemeMomentSplitPropagator parent child distinct

/-- Exact compact positive killed-dual matrix for the same instruction. -/
noncomputable def BiologicalManyDemeInstruction.killedPropagator {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K) :
    Matrix (BiologicalManyDemeKilledDualCoordinate D K)
      (BiologicalManyDemeKilledDualCoordinate D K) ℝ :=
  match instruction with
  | .evolve rates duration _ _ =>
      matrixExponential (biologicalManyDemeKilledDualGenerator rates) duration
  | .split parent child distinct =>
      biologicalManyDemeKilledDualSplitPropagator parent child distinct

/-- Every exact compact killed-dual demographic instruction is entrywise nonnegative.
Epoch positivity follows from the derived Metzler semigroup theorem; split positivity is
the deterministic zero-one merge kernel. -/
theorem BiologicalManyDemeInstruction.killedPropagator_nonneg {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K)
    (row column : BiologicalManyDemeKilledDualCoordinate D K) :
    0 ≤ instruction.killedPropagator row column := by
  cases instruction with
  | evolve rates duration duration_nonneg symmetric =>
      exact matrixExponential_apply_nonneg_of_metzler
        (biologicalManyDemeKilledDualGenerator rates)
        (biologicalManyDemeKilledDualGenerator_isMetzler rates)
        duration duration_nonneg row column
  | split parent child distinct =>
      simp only [BiologicalManyDemeInstruction.killedPropagator,
        biologicalManyDemeKilledDualSplitPropagator]
      split_ifs <;> norm_num

/-- Every compact demographic instruction intertwines through the same Bernstein projection. -/
theorem BiologicalManyDemeInstruction.intertwines {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K) :
    biologicalManyDemeBernsteinMomentProjection D K * instruction.momentPropagator =
      instruction.killedPropagator * biologicalManyDemeBernsteinMomentProjection D K := by
  cases instruction with
  | evolve rates duration duration_nonneg symmetric =>
      exact biologicalManyDemeBernsteinMomentProjection_exponential_intertwines
        rates symmetric duration
  | split parent child distinct =>
      exact biologicalManyDemeBernsteinMomentProjection_split_intertwines
        parent child distinct

/-- Ordered compact forward moment product for an arbitrary demographic history. -/
noncomputable def biologicalManyDemeMomentHistoryPropagator {D K : ℕ} :
    List (BiologicalManyDemeInstruction D K) →
      Matrix (BiologicalManyDemeMomentCoordinate D K)
        (BiologicalManyDemeMomentCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      biologicalManyDemeMomentHistoryPropagator remaining * instruction.momentPropagator

/-- Execute a compact moment history directly in forward order. -/
noncomputable def propagateBiologicalManyDemeMomentInstructions {D K : ℕ} :
    List (BiologicalManyDemeInstruction D K) →
      (BiologicalManyDemeMomentCoordinate D K → ℝ) →
        BiologicalManyDemeMomentCoordinate D K → ℝ
  | [], initial => initial
  | instruction :: remaining, initial =>
      propagateBiologicalManyDemeMomentInstructions remaining
        (instruction.momentPropagator.mulVec initial)

/-- Direct compact forward execution equals the ordered compact moment matrix product. -/
theorem biologicalManyDemeMomentHistoryPropagator_mulVec {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K))
    (initial : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial =
      propagateBiologicalManyDemeMomentInstructions instructions initial := by
  induction instructions generalizing initial with
  | nil => simp [biologicalManyDemeMomentHistoryPropagator,
      propagateBiologicalManyDemeMomentInstructions]
  | cons instruction remaining induction =>
      rw [biologicalManyDemeMomentHistoryPropagator, ← Matrix.mulVec_mulVec,
        induction]
      rfl

/-- Ordered compact killed-dual product corresponding to the same forward history. -/
noncomputable def biologicalManyDemeKilledDualHistoryPropagator {D K : ℕ} :
    List (BiologicalManyDemeInstruction D K) →
      Matrix (BiologicalManyDemeKilledDualCoordinate D K)
        (BiologicalManyDemeKilledDualCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      biologicalManyDemeKilledDualHistoryPropagator remaining * instruction.killedPropagator

/-- **Every arbitrary finite demographic history has a positive exact killed-dual
operator.**  This covers any finite deme count, every typed migration graph, every sequence
of rate epochs, and every genuine split. -/
theorem biologicalManyDemeKilledDualHistoryPropagator_nonneg {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K))
    (row column : BiologicalManyDemeKilledDualCoordinate D K) :
    0 ≤ biologicalManyDemeKilledDualHistoryPropagator instructions row column := by
  induction instructions generalizing row column with
  | nil =>
      rw [biologicalManyDemeKilledDualHistoryPropagator]
      change 0 ≤ if row = column then 1 else 0
      split_ifs <;> norm_num
  | cons instruction remaining induction =>
      rw [biologicalManyDemeKilledDualHistoryPropagator, Matrix.mul_apply]
      exact Finset.sum_nonneg fun middle _ ↦
        mul_nonneg (induction row middle) (instruction.killedPropagator_nonneg middle column)

/-- A nonnegative compact killed-dual boundary remains nonnegative after any arbitrary
finite demographic history. -/
theorem biologicalManyDemeKilledDualHistoryPropagator_mulVec_nonneg {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K))
    (initial : BiologicalManyDemeKilledDualCoordinate D K → ℝ)
    (initial_nonneg : ∀ coordinate, 0 ≤ initial coordinate)
    (row : BiologicalManyDemeKilledDualCoordinate D K) :
    0 ≤ (biologicalManyDemeKilledDualHistoryPropagator instructions).mulVec initial row := by
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun column _ ↦
    mul_nonneg (biologicalManyDemeKilledDualHistoryPropagator_nonneg
      instructions row column) (initial_nonneg column)

/-- **Exact history-wide positive duality.**  The single compact Bernstein projection
intertwines every finite ordered sequence of arbitrary migration epochs and population splits. -/
theorem biologicalManyDemeBernsteinMomentProjection_history_intertwines {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K)) :
    biologicalManyDemeBernsteinMomentProjection D K *
        biologicalManyDemeMomentHistoryPropagator instructions =
      biologicalManyDemeKilledDualHistoryPropagator instructions *
        biologicalManyDemeBernsteinMomentProjection D K := by
  induction instructions with
  | nil => simp [biologicalManyDemeMomentHistoryPropagator,
      biologicalManyDemeKilledDualHistoryPropagator]
  | cons instruction remaining induction =>
      simp only [biologicalManyDemeMomentHistoryPropagator,
        biologicalManyDemeKilledDualHistoryPropagator]
      calc
        _ = (biologicalManyDemeBernsteinMomentProjection D K *
              biologicalManyDemeMomentHistoryPropagator remaining) *
            instruction.momentPropagator := by rw [Matrix.mul_assoc]
        _ = (biologicalManyDemeKilledDualHistoryPropagator remaining *
              biologicalManyDemeBernsteinMomentProjection D K) *
            instruction.momentPropagator := by rw [induction]
        _ = biologicalManyDemeKilledDualHistoryPropagator remaining *
            (biologicalManyDemeBernsteinMomentProjection D K *
              instruction.momentPropagator) := by rw [Matrix.mul_assoc]
        _ = biologicalManyDemeKilledDualHistoryPropagator remaining *
            (instruction.killedPropagator *
              biologicalManyDemeBernsteinMomentProjection D K) := by
              rw [instruction.intertwines]
        _ = _ := by rw [← Matrix.mul_assoc]

/-- Complete compact positive-dual history applied to a projected ancestral moment state is
identical to projecting the exact forward compact moment history. -/
theorem biologicalManyDemeHistory_projectedState {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K))
    (initial : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (biologicalManyDemeBernsteinMomentProjection D K).mulVec
        ((biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial) =
      (biologicalManyDemeKilledDualHistoryPropagator instructions).mulVec
        ((biologicalManyDemeBernsteinMomentProjection D K).mulVec initial) := by
  calc
    _ = (biologicalManyDemeBernsteinMomentProjection D K *
          biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial := by
        rw [Matrix.mulVec_mulVec]
    _ = (biologicalManyDemeKilledDualHistoryPropagator instructions *
          biologicalManyDemeBernsteinMomentProjection D K).mulVec initial := by
        rw [biologicalManyDemeBernsteinMomentProjection_history_intertwines]
    _ = _ := by rw [Matrix.mulVec_mulVec]

/-- Moment-basis table represented by one biological affine column.  The explicit `none`
column carries the constant monomial; degree-zero and above-`K` rectangular coordinates are
padding and therefore represent the zero polynomial here. -/
noncomputable def manyDemeBiologicalAffineColumnTable {D K : ℕ}
    (column : AffineManyDemeMomentCoordinate D K) : (Fin D → ℕ) → ℝ :=
  match column with
  | none => manyDemeMomentConstantTable
  | some coordinate =>
      if 0 < coordinate.degree ∧ coordinate.degree ≤ K then
        manyDemeMomentBasisTable K coordinate
      else 0

/-- Bernstein coefficient projection from the affine monomial carrier to the positive
killed-dual carrier.  Each entry applies the corresponding monomial-basis column functional
to the exact Bernstein polynomial.  Padding killed rows are set to zero. -/
noncomputable def manyDemeBernsteinMomentProjection (D K : ℕ) :
    Matrix (ManyDemeKilledDualCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  fun row column ↦
    if row.degree ≤ K then
      manyDemePolynomialMomentFunctional (manyDemeBiologicalAffineColumnTable column)
        (manyDemeBernsteinPolynomial
          (fun deme ↦ (row.1 deme).val) (fun deme ↦ (row.2 deme).val))
    else 0

/-- Padding killed-dual rows have a zero Bernstein projection row. -/
theorem manyDemeBernsteinMomentProjection_of_degree_gt {D K : ℕ}
    (row : ManyDemeKilledDualCoordinate D K) (degree_gt : K < row.degree)
    (column : AffineManyDemeMomentCoordinate D K) :
    manyDemeBernsteinMomentProjection D K row column = 0 := by
  simp [manyDemeBernsteinMomentProjection, Nat.not_le.mpr degree_gt]

/-- Padding monomial coordinates have a zero Bernstein projection column. -/
theorem manyDemeBernsteinMomentProjection_of_padding_column {D K : ℕ}
    (row : ManyDemeKilledDualCoordinate D K) (coordinate : ManyDemeMomentCoordinate D K)
    (padding : ¬(0 < coordinate.degree ∧ coordinate.degree ≤ K)) :
    manyDemeBernsteinMomentProjection D K row (some coordinate) = 0 := by
  unfold manyDemeBernsteinMomentProjection
  by_cases row_degree : row.degree ≤ K
  · rw [if_pos row_degree]
    rw [manyDemePolynomialMomentFunctional_eq_sum]
    simp [manyDemeBiologicalAffineColumnTable, padding]
  · simp [row_degree]

/-- The compact Bernstein projection is precisely the biological submatrix of the earlier
rectangular projection. -/
theorem biologicalManyDemeBernsteinMomentProjection_eq_submatrix (D K : ℕ) :
    biologicalManyDemeBernsteinMomentProjection D K =
      (manyDemeBernsteinMomentProjection D K).submatrix
        BiologicalManyDemeKilledDualCoordinate.coordinate
        BiologicalManyDemeMomentCoordinate.toAffine := by
  apply Matrix.ext
  intro row column
  cases column with
  | none =>
      simp [biologicalManyDemeBernsteinMomentProjection,
        manyDemeBernsteinMomentProjection, biologicalManyDemeMomentColumnTable_none,
        manyDemeBiologicalAffineColumnTable,
        BiologicalManyDemeMomentCoordinate.toAffine, row.degree_le]
  | some column =>
      simp [biologicalManyDemeBernsteinMomentProjection,
        manyDemeBernsteinMomentProjection, biologicalManyDemeMomentColumnTable_some,
        manyDemeBiologicalAffineColumnTable,
        BiologicalManyDemeMomentCoordinate.toAffine, row.degree_le,
        column.degree_pos, column.degree_le]

/-- Exact affine generator `[A,-b;0,0]` for arbitrary finite deme count. -/
noncomputable def augmentedManyDemeMomentGenerator {D : ℕ}
    (rates : ManyDemeRates D) (K : ℕ) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ
  | some row, some column => manyDemeMomentDynamicsMatrix rates K row column
  | some row, none => -manyDemeMomentForcing rates K row
  | none, _ => 0

/-- The compact generator is exactly the biological submatrix of the existing augmented
rectangular generator. -/
theorem biologicalManyDemeMomentGenerator_eq_submatrix {D K : ℕ}
    (rates : ManyDemeRates D) :
    biologicalManyDemeMomentGenerator rates =
      (augmentedManyDemeMomentGenerator rates K).submatrix
        BiologicalManyDemeMomentCoordinate.toAffine
        BiologicalManyDemeMomentCoordinate.toAffine := by
  apply Matrix.ext
  intro row column
  cases row with
  | none => simp [biologicalManyDemeMomentGenerator,
      augmentedManyDemeMomentGenerator,
      BiologicalManyDemeMomentCoordinate.toAffine]
  | some row =>
      have rowBiological :
          0 < (∑ deme, (row.coordinate deme).val) ∧
            (∑ deme, (row.coordinate deme).val) ≤ K := by
        simpa [ManyDemeMomentCoordinate.degree] using
          And.intro row.degree_pos row.degree_le
      cases column with
      | none =>
          simp [biologicalManyDemeMomentGenerator, biologicalManyDemeMomentColumnTable_none,
            augmentedManyDemeMomentGenerator, manyDemeMomentForcing,
            BiologicalManyDemeMomentCoordinate.toAffine, ManyDemeMomentCoordinate.degree,
            rowBiological]
      | some column =>
          simp [biologicalManyDemeMomentGenerator, biologicalManyDemeMomentColumnTable_some,
            augmentedManyDemeMomentGenerator, manyDemeMomentDynamicsMatrix,
            BiologicalManyDemeMomentCoordinate.toAffine, ManyDemeMomentCoordinate.degree,
            rowBiological]

/-- The old rectangular affine generator restricted after application equals the compact
biological generator applied after restriction, provided every nonbiological rectangular
padding coordinate is zero. -/
theorem restrictAffineManyDemeMomentState_generator_mulVec {D K : ℕ}
    (rates : ManyDemeRates D) (state : AffineManyDemeMomentCoordinate D K → ℝ)
    (paddingZero : ∀ coordinate,
      ¬(0 < coordinate.degree ∧ coordinate.degree ≤ K) → state (some coordinate) = 0) :
    restrictAffineManyDemeMomentState
        ((augmentedManyDemeMomentGenerator rates K).mulVec state) =
      (biologicalManyDemeMomentGenerator rates).mulVec
        (restrictAffineManyDemeMomentState state) := by
  funext row
  cases row with
  | none => simp [restrictAffineManyDemeMomentState,
      BiologicalManyDemeMomentCoordinate.toAffine,
      augmentedManyDemeMomentGenerator, Matrix.mulVec,
      biologicalManyDemeMomentGenerator]
  | some row =>
      change (augmentedManyDemeMomentGenerator rates K).mulVec state
          (some row.coordinate) = _
      rw [biologicalManyDemeMomentGenerator_eq_submatrix]
      unfold Matrix.mulVec dotProduct
      simp_rw [Fintype.sum_option]
      simp only [restrictAffineManyDemeMomentState,
        BiologicalManyDemeMomentCoordinate.toAffine]
      let biologicalSet : Finset (ManyDemeMomentCoordinate D K) :=
        Finset.univ.filter fun coordinate ↦ 0 < coordinate.degree ∧ coordinate.degree ≤ K
      have sourceSum :
          (∑ coordinate : ManyDemeMomentCoordinate D K,
            augmentedManyDemeMomentGenerator rates K (some row.coordinate) (some coordinate) *
              state (some coordinate)) =
            ∑ coordinate ∈ biologicalSet,
            augmentedManyDemeMomentGenerator rates K (some row.coordinate) (some coordinate) *
                state (some coordinate) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ biologicalSet)
        intro coordinate _ absent
        have padding : ¬(0 < coordinate.degree ∧ coordinate.degree ≤ K) := by
          simpa [biologicalSet] using absent
        simp [paddingZero coordinate padding]
      rw [sourceSum]
      congr 1
      let embedding : PositiveManyDemeMomentCoordinate D K ↪
          ManyDemeMomentCoordinate D K :=
        ⟨fun coordinate ↦ coordinate.coordinate, by
          intro left right equal
          cases left with
          | mk leftCoordinate leftPositive leftBound =>
              cases right with
              | mk rightCoordinate rightPositive rightBound =>
                  cases equal
                  rfl⟩
      have biologicalSet_eq : biologicalSet = Finset.univ.map embedding := by
        ext coordinate
        simp only [biologicalSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_map]
        constructor
        · intro biological
          exact ⟨⟨coordinate, biological.1, biological.2⟩, rfl⟩
        · rintro ⟨positive, equal⟩
          rw [← equal]
          exact ⟨positive.degree_pos, positive.degree_le⟩
      rw [biologicalSet_eq]
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro coordinate _
      rfl

/-- The rectangular generator applied to a zero-padded compact state is exactly the
zero-padded compact generator state.  This includes every padding output row, not only the
biological restriction. -/
theorem augmentedManyDemeMomentGenerator_extend_mulVec {D K : ℕ}
    (rates : ManyDemeRates D)
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    (augmentedManyDemeMomentGenerator rates K).mulVec
        (extendBiologicalManyDemeMomentState state) =
      extendBiologicalManyDemeMomentState
        ((biologicalManyDemeMomentGenerator rates).mulVec state) := by
  funext coordinate
  cases coordinate with
  | none => simp [Matrix.mulVec, augmentedManyDemeMomentGenerator,
      dotProduct, biologicalManyDemeMomentGenerator,
      extendBiologicalManyDemeMomentState]
  | some coordinate =>
      by_cases biological : 0 < coordinate.degree ∧ coordinate.degree ≤ K
      · let positive : PositiveManyDemeMomentCoordinate D K :=
          ⟨coordinate, biological.1, biological.2⟩
        have restriction := congrFun
          (restrictAffineManyDemeMomentState_generator_mulVec rates
            (extendBiologicalManyDemeMomentState state)
            (fun coordinate padding ↦
              extendBiologicalManyDemeMomentState_padding state coordinate padding))
          (some positive)
        rw [restrictAffine_extendBiologicalManyDemeMomentState] at restriction
        simpa [restrictAffineManyDemeMomentState,
          BiologicalManyDemeMomentCoordinate.toAffine,
          extendBiologicalManyDemeMomentState, biological, positive] using restriction
      · have rowZero : ∀ column,
            augmentedManyDemeMomentGenerator rates K (some coordinate) column = 0 := by
          intro column
          cases column <;>
            simp [augmentedManyDemeMomentGenerator, manyDemeMomentDynamicsMatrix,
              manyDemeMomentForcing, biological]
        simp [Matrix.mulVec, rowZero, extendBiologicalManyDemeMomentState, biological]

/-- **Compact/rectangular generator embedding.**  The old padded affine matrix and the new
minimal biological matrix agree exactly through the zero-padding embedding. -/
theorem extendBiologicalManyDemeMomentMatrix_generator_intertwines {D K : ℕ}
    (rates : ManyDemeRates D) :
    extendBiologicalManyDemeMomentMatrix D K *
        biologicalManyDemeMomentGenerator rates =
      augmentedManyDemeMomentGenerator rates K *
        extendBiologicalManyDemeMomentMatrix D K := by
  apply Matrix.ext
  intro row column
  change (extendBiologicalManyDemeMomentMatrix D K).mulVec
      (fun source ↦ biologicalManyDemeMomentGenerator rates source column) row =
    (augmentedManyDemeMomentGenerator rates K).mulVec
      (fun source ↦ extendBiologicalManyDemeMomentMatrix D K source column) row
  have equality := augmentedManyDemeMomentGenerator_extend_mulVec rates
    (fun source ↦ if source = column then 1 else 0)
  rw [← extendBiologicalManyDemeMomentMatrix_mulVec,
    ← extendBiologicalManyDemeMomentMatrix_mulVec] at equality
  simpa [Matrix.mulVec, dotProduct] using (congrFun equality row).symm

/-- The compact-to-rectangular embedding intertwines every exact epoch exponential. -/
theorem extendBiologicalManyDemeMomentMatrix_exponential_intertwines {D K : ℕ}
    (rates : ManyDemeRates D) (duration : ℝ) :
    extendBiologicalManyDemeMomentMatrix D K *
        matrixExponential (biologicalManyDemeMomentGenerator rates) duration =
      matrixExponential (augmentedManyDemeMomentGenerator rates K) duration *
        extendBiologicalManyDemeMomentMatrix D K := by
  exact matrixExponential_intertwines _ _ _
    (extendBiologicalManyDemeMomentMatrix_generator_intertwines rates) duration

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

/-- Backward sampling-dual propagator for one arbitrary-deme epoch.  Its carrier is the same
finite degree-`K` coordinate space as the forward law, but it evolves only the requested
terminal functional. -/
noncomputable def ManyDemeMomentEpoch.dualPropagator {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  matrixExponential (augmentedManyDemeMomentGenerator epoch.rates K).transpose epoch.duration

/-- The epoch dual is exactly the transpose of the forward propagator. -/
theorem ManyDemeMomentEpoch.dualPropagator_eq_transpose {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K) :
    epoch.dualPropagator = epoch.propagator.transpose := by
  exact matrixExponential_transpose _ _

/-- One-epoch sampling duality for every arbitrary migration matrix, mutation vector,
coalescence vector, truncation degree, terminal probe, and initial moment state. -/
theorem ManyDemeMomentEpoch.samplingDual {D K : ℕ}
    (epoch : ManyDemeMomentEpoch D K)
    (probe state : AffineManyDemeMomentCoordinate D K → ℝ) :
    probe ⬝ᵥ epoch.propagator.mulVec state =
      epoch.dualPropagator.mulVec probe ⬝ᵥ state := by
  exact matrixExponential_samplingDual _ _ _ _

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

/-- Sparse linear split operator on the constant-augmented moment carrier.  Every biological
row has at most one nonzero entry: the pre-split coordinate obtained by merging the child's
exponent into its parent.  Coordinates whose merged exponent leaves the degree rectangle
have a zero row, exactly as in `manyDemeMomentVectorTable`. -/
noncomputable def splitManyDemeMomentPropagator {D K : ℕ}
    (parent child : Fin D) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some row, some column =>
      if hbound : ∀ d,
          mergeSplitExponent parent child (fun d ↦ (row d).val) d < K + 1 then
        if column = fun d ↦
            ⟨mergeSplitExponent parent child (fun d ↦ (row d).val) d, hbound d⟩
          then 1 else 0
      else 0

/-- Exact instantaneous split transform on a finite moment state. -/
noncomputable def splitManyDemeMomentState {D K : ℕ}
    (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ
  | none => state none
  | some coordinate =>
      manyDemeMomentVectorTable K (fun oldCoordinate ↦ state (some oldCoordinate))
        (mergeSplitExponent parent child (fun d ↦ (coordinate d).val))

/-- The split function is exactly multiplication by its sparse matrix on every augmented
state.  In particular, normalization is a proved invariant of reachable states rather than a
literal silently injected by the instantaneous operator. -/
theorem splitManyDemeMomentPropagator_mulVec {D K : ℕ}
    (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    (splitManyDemeMomentPropagator parent child).mulVec state =
      splitManyDemeMomentState parent child state := by
  funext row
  cases row with
  | none =>
      simp [Matrix.mulVec, dotProduct, splitManyDemeMomentPropagator,
        splitManyDemeMomentState]
  | some row =>
      let merged := mergeSplitExponent parent child (fun d ↦ (row d).val)
      by_cases hbound : ∀ d, merged d < K + 1
      · let column : ManyDemeMomentCoordinate D K := fun d ↦ ⟨merged d, hbound d⟩
        simp [Matrix.mulVec, dotProduct, splitManyDemeMomentPropagator,
          splitManyDemeMomentState, manyDemeMomentVectorTable, merged, hbound]
      · simp [Matrix.mulVec, dotProduct, splitManyDemeMomentPropagator,
          splitManyDemeMomentState, manyDemeMomentVectorTable, merged, hbound]

/-- The old rectangular split applied to a zero-padded compact state is exactly the extension
of the compact split result. -/
theorem splitManyDemeMomentState_extendBiological {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child)
    (state : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    splitManyDemeMomentState parent child
        (extendBiologicalManyDemeMomentState state) =
      extendBiologicalManyDemeMomentState
        ((biologicalManyDemeMomentSplitPropagator parent child distinct).mulVec state) := by
  funext row
  cases row with
  | none =>
      rw [biologicalManyDemeMomentSplitPropagator_mulVec]
      rfl
  | some row =>
      by_cases biological : 0 < row.degree ∧ row.degree ≤ K
      · let positive : PositiveManyDemeMomentCoordinate D K :=
          ⟨row, biological.1, biological.2⟩
        have mergedDegree :
            (positive.mergeSplit parent child distinct).coordinate.degree = row.degree := by
          unfold PositiveManyDemeMomentCoordinate.mergeSplit
            ManyDemeMomentCoordinate.degree
          simpa using sum_mergeSplitExponent parent child distinct
            (fun deme ↦ (row deme).val)
        have mergedBound : ∀ deme,
            mergeSplitExponent parent child (fun d ↦ (row d).val) deme < K + 1 :=
          mergeSplitExponent_lt_of_sum_le row parent child distinct biological.2
        have mergedCoordinate :
            (fun deme ↦ ⟨mergeSplitExponent parent child (fun d ↦ (row d).val) deme,
              mergedBound deme⟩ : ManyDemeMomentCoordinate D K) =
              (positive.mergeSplit parent child distinct).coordinate := by
          funext deme
          apply Fin.ext
          rfl
        simp [splitManyDemeMomentState, manyDemeMomentVectorTable,
          extendBiologicalManyDemeMomentState,
          biologicalManyDemeMomentSplitPropagator_mulVec, positive, biological,
          mergedBound, mergedDegree, mergedCoordinate] <;> congr
      · by_cases degreeZero : row.degree = 0
        · have rowZero : row = fun _ ↦ 0 := by
            funext deme
            have coordinate_le : (row deme).val ≤ row.degree := by
              unfold ManyDemeMomentCoordinate.degree
              exact Finset.single_le_sum (fun d _ ↦ Nat.zero_le (row d).val)
                (Finset.mem_univ deme)
            apply Fin.ext
            exact Nat.eq_zero_of_le_zero (degreeZero ▸ coordinate_le)
          subst row
          simp [splitManyDemeMomentState, manyDemeMomentVectorTable,
            extendBiologicalManyDemeMomentState,
            biologicalManyDemeMomentSplitPropagator_mulVec,
            ManyDemeMomentCoordinate.degree, mergeSplitExponent]
        · have degreePositive : 0 < row.degree := Nat.pos_of_ne_zero degreeZero
          have degreeHigh : K < row.degree := by omega
          by_cases mergedBound : ∀ deme,
              mergeSplitExponent parent child (fun d ↦ (row d).val) deme < K + 1
          · let merged : ManyDemeMomentCoordinate D K := fun deme ↦
              ⟨mergeSplitExponent parent child (fun d ↦ (row d).val) deme,
                mergedBound deme⟩
            have mergedDegree : merged.degree = row.degree := by
              unfold merged ManyDemeMomentCoordinate.degree
              simpa using sum_mergeSplitExponent parent child distinct
                (fun deme ↦ (row deme).val)
            have mergedPadding : ¬(0 < merged.degree ∧ merged.degree ≤ K) := by
              omega
            simp [splitManyDemeMomentState, manyDemeMomentVectorTable,
              extendBiologicalManyDemeMomentState,
              biologicalManyDemeMomentSplitPropagator_mulVec,
              biological, mergedBound, merged, mergedPadding]
          · simp [splitManyDemeMomentState, manyDemeMomentVectorTable,
              extendBiologicalManyDemeMomentState,
              biologicalManyDemeMomentSplitPropagator_mulVec,
              biological, mergedBound]

/-- The compact moment split matrix embeds exactly into the old rectangular split matrix. -/
theorem extendBiologicalManyDemeMomentMatrix_split_intertwines {D K : ℕ}
    (parent child : Fin D) (distinct : parent ≠ child) :
    extendBiologicalManyDemeMomentMatrix D K *
        biologicalManyDemeMomentSplitPropagator parent child distinct =
      splitManyDemeMomentPropagator parent child *
        extendBiologicalManyDemeMomentMatrix D K := by
  apply Matrix.ext
  intro row column
  have equality := splitManyDemeMomentState_extendBiological parent child distinct
    (Pi.single column 1)
  rw [← splitManyDemeMomentPropagator_mulVec,
    ← extendBiologicalManyDemeMomentMatrix_mulVec,
    ← extendBiologicalManyDemeMomentMatrix_mulVec] at equality
  simp only [Matrix.mulVec_single_one] at equality
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using (congrFun equality row).symm

/-- A split preserves the explicit affine constant coordinate. -/
theorem splitManyDemeMomentState_none {D K : ℕ} (parent child : Fin D)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    splitManyDemeMomentState parent child state none = state none :=
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

/-- Exact forward matrix associated with either kind of demographic instruction. -/
noncomputable def ManyDemeMomentInstruction.propagator {D K : ℕ}
    (instruction : ManyDemeMomentInstruction D K) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  match instruction with
  | .evolve epoch => epoch.propagator
  | .split parent child => splitManyDemeMomentPropagator parent child

/-- Apply one instruction in the original state-space presentation. -/
noncomputable def ManyDemeMomentInstruction.apply {D K : ℕ}
    (instruction : ManyDemeMomentInstruction D K)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ :=
  match instruction with
  | .evolve epoch => epoch.propagator.mulVec state
  | .split parent child => splitManyDemeMomentState parent child state

/-- Matrix multiplication and direct application of one instruction coincide on every
augmented state. -/
theorem ManyDemeMomentInstruction.propagator_mulVec {D K : ℕ}
    (instruction : ManyDemeMomentInstruction D K)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    instruction.propagator.mulVec state = instruction.apply state := by
  cases instruction with
  | evolve => rfl
  | split parent child =>
      exact splitManyDemeMomentPropagator_mulVec parent child state

/-- Every exact demographic instruction preserves the explicit affine constant. -/
theorem ManyDemeMomentInstruction.apply_none {D K : ℕ}
    (instruction : ManyDemeMomentInstruction D K)
    (state : AffineManyDemeMomentCoordinate D K → ℝ) :
    instruction.apply state none = state none := by
  cases instruction with
  | evolve epoch => exact epoch.propagator_none state
  | split => rfl

/-- Execute an arbitrary finite sequence of exact demographic moment instructions. -/
noncomputable def propagateManyDemeMomentInstructions {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K))
    (initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    AffineManyDemeMomentCoordinate D K → ℝ :=
  instructions.foldl (fun state instruction ↦ instruction.apply state) initial

/-- A complete instruction sequence preserves the affine constant exactly. -/
theorem propagateManyDemeMomentInstructions_none {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K))
    (initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    propagateManyDemeMomentInstructions instructions initial none = initial none := by
  induction instructions generalizing initial with
  | nil => rfl
  | cons instruction remaining ih =>
      change propagateManyDemeMomentInstructions remaining
        (instruction.apply initial) none = initial none
      rw [ih, instruction.apply_none]

/-- Ordered forward product for a complete arbitrary-deme instruction history.  For
`[M₁, M₂, ...]`, this is `... * M₂ * M₁`, the matrix acting on a column initial state. -/
noncomputable def manyDemeMomentHistoryPropagator {D K : ℕ} :
    List (ManyDemeMomentInstruction D K) →
      Matrix (AffineManyDemeMomentCoordinate D K)
        (AffineManyDemeMomentCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      manyDemeMomentHistoryPropagator remaining * instruction.propagator

/-- Direct instruction execution equals multiplication by the ordered history product. -/
theorem manyDemeMomentHistoryPropagator_mulVec {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K))
    (initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    (manyDemeMomentHistoryPropagator instructions).mulVec initial =
      propagateManyDemeMomentInstructions instructions initial := by
  induction instructions generalizing initial with
  | nil => simp [manyDemeMomentHistoryPropagator,
      propagateManyDemeMomentInstructions]
  | cons instruction remaining ih =>
      rw [manyDemeMomentHistoryPropagator, ← Matrix.mulVec_mulVec,
        instruction.propagator_mulVec, ih]
      rfl

/-- Forget only the proof refinements of a compact biological instruction and recover the
corresponding instruction on the older rectangular affine carrier.  Rates, durations, and
split labels are unchanged. -/
def BiologicalManyDemeInstruction.toAffine {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K) :
    ManyDemeMomentInstruction D K :=
  match instruction with
  | .evolve rates duration duration_nonneg _ =>
      .evolve { rates := rates, duration := duration, duration_nonneg := duration_nonneg }
  | .split parent child _ => .split parent child

/-- The compact-to-rectangular embedding commutes with every biological instruction. -/
theorem BiologicalManyDemeInstruction.toAffine_propagator_intertwines {D K : ℕ}
    (instruction : BiologicalManyDemeInstruction D K) :
    extendBiologicalManyDemeMomentMatrix D K * instruction.momentPropagator =
      instruction.toAffine.propagator * extendBiologicalManyDemeMomentMatrix D K := by
  cases instruction with
  | evolve rates duration duration_nonneg symmetric =>
      exact extendBiologicalManyDemeMomentMatrix_exponential_intertwines rates duration
  | split parent child distinct =>
      exact extendBiologicalManyDemeMomentMatrix_split_intertwines parent child distinct

/-- The zero-padding embedding intertwines an arbitrary compact history with the same history
on the rectangular carrier.  This proves representation equivalence for every finite sequence,
not only for individual epochs or splits. -/
theorem extendBiologicalManyDemeMomentMatrix_history_intertwines {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K)) :
    extendBiologicalManyDemeMomentMatrix D K *
        biologicalManyDemeMomentHistoryPropagator instructions =
      manyDemeMomentHistoryPropagator
          (instructions.map BiologicalManyDemeInstruction.toAffine) *
        extendBiologicalManyDemeMomentMatrix D K := by
  induction instructions with
  | nil => simp [biologicalManyDemeMomentHistoryPropagator,
      manyDemeMomentHistoryPropagator]
  | cons instruction remaining induction =>
      simp only [biologicalManyDemeMomentHistoryPropagator, List.map_cons,
        manyDemeMomentHistoryPropagator]
      calc
        _ = (extendBiologicalManyDemeMomentMatrix D K *
              biologicalManyDemeMomentHistoryPropagator remaining) *
            instruction.momentPropagator := by rw [Matrix.mul_assoc]
        _ = (manyDemeMomentHistoryPropagator
              (remaining.map BiologicalManyDemeInstruction.toAffine) *
                extendBiologicalManyDemeMomentMatrix D K) *
            instruction.momentPropagator := by rw [induction]
        _ = manyDemeMomentHistoryPropagator
              (remaining.map BiologicalManyDemeInstruction.toAffine) *
            (extendBiologicalManyDemeMomentMatrix D K *
              instruction.momentPropagator) := by rw [Matrix.mul_assoc]
        _ = manyDemeMomentHistoryPropagator
              (remaining.map BiologicalManyDemeInstruction.toAffine) *
            (instruction.toAffine.propagator *
              extendBiologicalManyDemeMomentMatrix D K) := by
                rw [instruction.toAffine_propagator_intertwines]
        _ = _ := by rw [← Matrix.mul_assoc]

/-- Executing a compact history and then zero-padding gives exactly the rectangular execution
of the erased history from the zero-padded initial state. -/
theorem extendBiologicalManyDemeMomentState_history_mulVec {D K : ℕ}
    (instructions : List (BiologicalManyDemeInstruction D K))
    (initial : BiologicalManyDemeMomentCoordinate D K → ℝ) :
    extendBiologicalManyDemeMomentState
        ((biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial) =
      (manyDemeMomentHistoryPropagator
        (instructions.map BiologicalManyDemeInstruction.toAffine)).mulVec
          (extendBiologicalManyDemeMomentState initial) := by
  calc
    _ = (extendBiologicalManyDemeMomentMatrix D K).mulVec
          ((biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial) := by
        rw [extendBiologicalManyDemeMomentMatrix_mulVec]
    _ = (extendBiologicalManyDemeMomentMatrix D K *
          biologicalManyDemeMomentHistoryPropagator instructions).mulVec initial := by
        rw [Matrix.mulVec_mulVec]
    _ = (manyDemeMomentHistoryPropagator
          (instructions.map BiologicalManyDemeInstruction.toAffine) *
            extendBiologicalManyDemeMomentMatrix D K).mulVec initial := by
        rw [extendBiologicalManyDemeMomentMatrix_history_intertwines]
    _ = (manyDemeMomentHistoryPropagator
          (instructions.map BiologicalManyDemeInstruction.toAffine)).mulVec
            ((extendBiologicalManyDemeMomentMatrix D K).mulVec initial) := by
        rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [extendBiologicalManyDemeMomentMatrix_mulVec]

/-- Transposed matrix for one backward sampling-dual instruction. -/
noncomputable def ManyDemeMomentInstruction.dualPropagator {D K : ℕ}
    (instruction : ManyDemeMomentInstruction D K) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  instruction.propagator.transpose

/-- An instruction annotated with exactly the finite work used to evaluate its backward
operator.  Splits are exact sparse maps and therefore carry no meaningless Taylor order. -/
inductive CertifiedDualMomentInstruction (D K : ℕ) where
  | evolve (epoch : ManyDemeMomentEpoch D K) (terms : ℕ)
  | split (parent child : Fin D)

/-- Drop the evaluation certificate and recover the exact demographic instruction. -/
def CertifiedDualMomentInstruction.exactInstruction {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    ManyDemeMomentInstruction D K :=
  match instruction with
  | .evolve epoch _ => .evolve epoch
  | .split parent child => .split parent child

/-- Attach an epoch-specific finite Taylor schedule to one exact instruction. -/
def ManyDemeMomentInstruction.certify {D K : ℕ}
    (termOrder : ManyDemeMomentEpoch D K → ℕ)
    (instruction : ManyDemeMomentInstruction D K) :
    CertifiedDualMomentInstruction D K :=
  match instruction with
  | .evolve epoch => .evolve epoch (termOrder epoch)
  | .split parent child => .split parent child

/-- Attach a finite Taylor schedule to every epoch of an exact history; splits remain exact. -/
def certifyManyDemeMomentHistory {D K : ℕ}
    (termOrder : ManyDemeMomentEpoch D K → ℕ)
    (instructions : List (ManyDemeMomentInstruction D K)) :
    List (CertifiedDualMomentInstruction D K) :=
  instructions.map (ManyDemeMomentInstruction.certify termOrder)

/-- Attaching and then erasing an epoch schedule preserves the exact instruction history. -/
theorem certifyManyDemeMomentHistory_exactInstructions {D K : ℕ}
    (termOrder : ManyDemeMomentEpoch D K → ℕ)
    (instructions : List (ManyDemeMomentInstruction D K)) :
    (certifyManyDemeMomentHistory termOrder instructions).map
        CertifiedDualMomentInstruction.exactInstruction = instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction remaining ih =>
      unfold certifyManyDemeMomentHistory at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      cases instruction <;>
        simp [ManyDemeMomentInstruction.certify,
          CertifiedDualMomentInstruction.exactInstruction, ih]

/-- Finite backward matrix used by a certified instruction evaluation. -/
noncomputable def CertifiedDualMomentInstruction.approximatePropagator {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    Matrix (AffineManyDemeMomentCoordinate D K) (AffineManyDemeMomentCoordinate D K) ℝ :=
  match instruction with
  | .evolve epoch terms =>
      matrixExponentialPartialSum
        (augmentedManyDemeMomentGenerator epoch.rates K).transpose epoch.duration terms
  | .split parent child =>
      (splitManyDemeMomentPropagator parent child).transpose

/-- Certified one-instruction operator error. -/
noncomputable def CertifiedDualMomentInstruction.errorBound {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) : ℝ :=
  match instruction with
  | .evolve epoch terms =>
      matrixExponentialTailBound
        (augmentedManyDemeMomentGenerator epoch.rates K).transpose epoch.duration terms
  | .split _ _ => 0

/-- Certified norm bound for the exact one-instruction dual. -/
noncomputable def CertifiedDualMomentInstruction.normBound {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) : ℝ :=
  instruction.errorBound + ‖instruction.approximatePropagator‖

/-- Each annotated instruction's exact dual lies within its stated finite-evaluation error. -/
theorem CertifiedDualMomentInstruction.error_le {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    ‖instruction.exactInstruction.dualPropagator - instruction.approximatePropagator‖ ≤
      instruction.errorBound := by
  cases instruction with
  | evolve epoch terms =>
      simp only [CertifiedDualMomentInstruction.exactInstruction,
        ManyDemeMomentInstruction.dualPropagator,
        ManyDemeMomentInstruction.propagator, ManyDemeMomentEpoch.propagator,
        CertifiedDualMomentInstruction.approximatePropagator,
        CertifiedDualMomentInstruction.errorBound]
      rw [← matrixExponential_transpose]
      exact matrixExponential_partialSum_error_le_tailBound _ _ _
  | split parent child =>
      simp only [CertifiedDualMomentInstruction.exactInstruction,
        ManyDemeMomentInstruction.dualPropagator,
        ManyDemeMomentInstruction.propagator,
        CertifiedDualMomentInstruction.approximatePropagator,
        CertifiedDualMomentInstruction.errorBound]
      simp

/-- The exact dual norm is bounded by approximation norm plus certified error. -/
theorem CertifiedDualMomentInstruction.exact_norm_le {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    ‖instruction.exactInstruction.dualPropagator‖ ≤ instruction.normBound := by
  calc
    _ ≤ ‖instruction.exactInstruction.dualPropagator -
          instruction.approximatePropagator‖ +
        ‖instruction.approximatePropagator‖ := by
      have := norm_add_le
        (instruction.exactInstruction.dualPropagator -
          instruction.approximatePropagator)
        instruction.approximatePropagator
      simpa using this
    _ ≤ instruction.errorBound + ‖instruction.approximatePropagator‖ :=
      add_le_add_right instruction.error_le _
    _ = instruction.normBound := rfl

/-- Each instruction error bound is nonnegative. -/
theorem CertifiedDualMomentInstruction.errorBound_nonneg {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    0 ≤ instruction.errorBound := by
  cases instruction with
  | evolve epoch terms => exact matrixExponentialTailBound_nonneg _ _ _
  | split => rfl

/-- Each instruction norm bound is nonnegative. -/
theorem CertifiedDualMomentInstruction.normBound_nonneg {D K : ℕ}
    (instruction : CertifiedDualMomentInstruction D K) :
    0 ≤ instruction.normBound :=
  add_nonneg instruction.errorBound_nonneg (norm_nonneg _)

/-- Finite backward product for a completely annotated history. -/
noncomputable def certifiedManyDemeMomentHistoryApproximation {D K : ℕ} :
    List (CertifiedDualMomentInstruction D K) →
      Matrix (AffineManyDemeMomentCoordinate D K)
        (AffineManyDemeMomentCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      instruction.approximatePropagator *
        certifiedManyDemeMomentHistoryApproximation remaining

/-- Multiplicative norm certificate for the exact annotated history product. -/
noncomputable def certifiedManyDemeMomentHistoryNormBound {D K : ℕ} :
    List (CertifiedDualMomentInstruction D K) → ℝ
  | [] => 1
  | instruction :: remaining =>
      instruction.normBound * certifiedManyDemeMomentHistoryNormBound remaining

/-- Recursive total error certificate for the annotated history product. -/
noncomputable def certifiedManyDemeMomentHistoryErrorBound {D K : ℕ} :
    List (CertifiedDualMomentInstruction D K) → ℝ
  | [] => 0
  | instruction :: remaining =>
      instruction.errorBound * certifiedManyDemeMomentHistoryNormBound remaining +
        ‖instruction.approximatePropagator‖ *
          certifiedManyDemeMomentHistoryErrorBound remaining

/-- Exact backward product represented by an annotated instruction history. -/
noncomputable def certifiedManyDemeMomentHistoryExact {D K : ℕ} :
    List (CertifiedDualMomentInstruction D K) →
      Matrix (AffineManyDemeMomentCoordinate D K)
        (AffineManyDemeMomentCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      instruction.exactInstruction.dualPropagator *
        certifiedManyDemeMomentHistoryExact remaining

/-- The exact annotated history norm obeys its multiplicative certificate. -/
theorem certifiedManyDemeMomentHistoryExact_norm_le {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K)) :
    ‖certifiedManyDemeMomentHistoryExact instructions‖ ≤
      certifiedManyDemeMomentHistoryNormBound instructions := by
  induction instructions with
  | nil => simp [certifiedManyDemeMomentHistoryExact,
      certifiedManyDemeMomentHistoryNormBound]
  | cons instruction remaining ih =>
      simp only [certifiedManyDemeMomentHistoryExact,
        certifiedManyDemeMomentHistoryNormBound]
      exact (norm_mul_le _ _).trans
        (mul_le_mul instruction.exact_norm_le ih (norm_nonneg _)
          instruction.normBound_nonneg)

/-- The multiplicative exact-history norm certificate is nonnegative. -/
theorem certifiedManyDemeMomentHistoryNormBound_nonneg {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K)) :
    0 ≤ certifiedManyDemeMomentHistoryNormBound instructions := by
  induction instructions with
  | nil => norm_num [certifiedManyDemeMomentHistoryNormBound]
  | cons instruction remaining ih =>
      exact mul_nonneg instruction.normBound_nonneg ih

/-- The recursively accumulated history error is nonnegative. -/
theorem certifiedManyDemeMomentHistoryErrorBound_nonneg {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K)) :
    0 ≤ certifiedManyDemeMomentHistoryErrorBound instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction remaining ih =>
      exact add_nonneg
        (mul_nonneg instruction.errorBound_nonneg
          (certifiedManyDemeMomentHistoryNormBound_nonneg remaining))
        (mul_nonneg (norm_nonneg _) ih)

/-- The finite annotated history product is within the recursive error certificate of the
exact history dual.  This is the rigorous stopping law for arbitrary sequences of epochs and
splits. -/
theorem certifiedManyDemeMomentHistory_error_le {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K)) :
    ‖certifiedManyDemeMomentHistoryExact instructions -
        certifiedManyDemeMomentHistoryApproximation instructions‖ ≤
      certifiedManyDemeMomentHistoryErrorBound instructions := by
  induction instructions with
  | nil => simp [certifiedManyDemeMomentHistoryExact,
      certifiedManyDemeMomentHistoryApproximation,
      certifiedManyDemeMomentHistoryErrorBound]
  | cons instruction remaining ih =>
      let exactHead := instruction.exactInstruction.dualPropagator
      let approximateHead := instruction.approximatePropagator
      let exactTail := certifiedManyDemeMomentHistoryExact remaining
      let approximateTail := certifiedManyDemeMomentHistoryApproximation remaining
      have hdecompose :
          exactHead * exactTail - approximateHead * approximateTail =
            (exactHead - approximateHead) * exactTail +
              approximateHead * (exactTail - approximateTail) := by
        noncomm_ring
      change ‖exactHead * exactTail - approximateHead * approximateTail‖ ≤ _
      rw [hdecompose]
      calc
        _ ≤ ‖(exactHead - approximateHead) * exactTail‖ +
            ‖approximateHead * (exactTail - approximateTail)‖ := norm_add_le _ _
        _ ≤ ‖exactHead - approximateHead‖ * ‖exactTail‖ +
            ‖approximateHead‖ * ‖exactTail - approximateTail‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ instruction.errorBound * certifiedManyDemeMomentHistoryNormBound remaining +
            ‖instruction.approximatePropagator‖ *
              certifiedManyDemeMomentHistoryErrorBound remaining := by
          exact add_le_add
            (mul_le_mul instruction.error_le
              (certifiedManyDemeMomentHistoryExact_norm_le remaining)
              (norm_nonneg _) instruction.errorBound_nonneg)
            (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
        _ = certifiedManyDemeMomentHistoryErrorBound (instruction :: remaining) := rfl

/-- Applying the finite annotated history to a probe inherits the total operator certificate. -/
theorem certifiedManyDemeMomentHistory_mulVec_error_le {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K))
    (probe : AffineManyDemeMomentCoordinate D K → ℝ) :
    ‖(certifiedManyDemeMomentHistoryExact instructions).mulVec probe -
        (certifiedManyDemeMomentHistoryApproximation instructions).mulVec probe‖ ≤
      certifiedManyDemeMomentHistoryErrorBound instructions * ‖probe‖ := by
  rw [← Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right
      (certifiedManyDemeMomentHistory_error_le instructions) (norm_nonneg _))

/-- Scalar pairing error after the certified backward history evaluation. -/
theorem certifiedManyDemeMomentHistory_pairing_error_le {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K))
    (probe initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    |(certifiedManyDemeMomentHistoryExact instructions).mulVec probe ⬝ᵥ initial -
        (certifiedManyDemeMomentHistoryApproximation instructions).mulVec probe ⬝ᵥ initial| ≤
      certifiedManyDemeMomentHistoryErrorBound instructions * ‖probe‖ *
        ∑ coordinate, |initial coordinate| := by
  rw [← sub_dotProduct]
  exact (abs_dotProduct_le_norm_mul_sum_abs _ _).trans
    (mul_le_mul_of_nonneg_right
      (certifiedManyDemeMomentHistory_mulVec_error_le instructions probe)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))

/-- Exact backward product for an instruction history.  It traverses the list structurally
in reverse operator order without ever constructing the dense forward state. -/
noncomputable def manyDemeMomentHistoryDualPropagator {D K : ℕ} :
    List (ManyDemeMomentInstruction D K) →
      Matrix (AffineManyDemeMomentCoordinate D K)
        (AffineManyDemeMomentCoordinate D K) ℝ
  | [] => 1
  | instruction :: remaining =>
      instruction.dualPropagator * manyDemeMomentHistoryDualPropagator remaining

/-- Erasing Taylor orders from an annotated history recovers exactly the ordinary history
dual; the annotations affect only its finite approximation and certificate. -/
theorem certifiedManyDemeMomentHistoryExact_eq_dualPropagator {D K : ℕ}
    (instructions : List (CertifiedDualMomentInstruction D K)) :
    certifiedManyDemeMomentHistoryExact instructions =
      manyDemeMomentHistoryDualPropagator
        (instructions.map CertifiedDualMomentInstruction.exactInstruction) := by
  induction instructions with
  | nil => rfl
  | cons instruction remaining ih =>
      simp only [certifiedManyDemeMomentHistoryExact, List.map_cons,
        manyDemeMomentHistoryDualPropagator]
      rw [ih]

/-- Any epoch-specific finite schedule certifies an approximation to the exact unannotated
history dual, with no change to the demographic semantics. -/
theorem certifiedScheduledHistoryExact_eq_dualPropagator {D K : ℕ}
    (termOrder : ManyDemeMomentEpoch D K → ℕ)
    (instructions : List (ManyDemeMomentInstruction D K)) :
    certifiedManyDemeMomentHistoryExact
        (certifyManyDemeMomentHistory termOrder instructions) =
      manyDemeMomentHistoryDualPropagator instructions := by
  rw [certifiedManyDemeMomentHistoryExact_eq_dualPropagator,
    certifyManyDemeMomentHistory_exactInstructions]

/-- The structural backward product is exactly the transpose of the complete forward
history product, including every epoch and instantaneous split. -/
theorem manyDemeMomentHistoryDualPropagator_eq_transpose {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K)) :
    manyDemeMomentHistoryDualPropagator instructions =
      (manyDemeMomentHistoryPropagator instructions).transpose := by
  induction instructions with
  | nil => simp [manyDemeMomentHistoryDualPropagator,
      manyDemeMomentHistoryPropagator]
  | cons instruction remaining ih =>
      simp [manyDemeMomentHistoryDualPropagator, manyDemeMomentHistoryPropagator,
        ManyDemeMomentInstruction.dualPropagator, Matrix.transpose_mul, ih]

/-- History-wide sampling-dual law for arbitrary finite deme count, migration matrix, rate
changes, sizes, mutation rates, and split sequence.  A terminal statistic is evaluated by
propagating its probe backward and taking one initial-state dot product. -/
theorem propagateManyDemeMomentInstructions_samplingDual {D K : ℕ}
    (instructions : List (ManyDemeMomentInstruction D K))
    (probe initial : AffineManyDemeMomentCoordinate D K → ℝ) :
    probe ⬝ᵥ propagateManyDemeMomentInstructions instructions initial =
      (manyDemeMomentHistoryDualPropagator instructions).mulVec probe ⬝ᵥ initial := by
  rw [← manyDemeMomentHistoryPropagator_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← manyDemeMomentHistoryDualPropagator_eq_transpose]

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
  | none => state none
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

/-- The squared normalized cross-deme `DD` correlation.

This is an exact property of the **unascertained two-locus moment field**.  It is not an
accuracy factor for a GWAS score: ascertainment, noisy association estimates, thresholding,
and clumping condition which marker--causal pairs receive nonzero score weights.  The exact
selected-score `R²` instead uses the full selected weight vector and genotype covariance
matrix in `RealizedPTGWASDraw.winningR2True_eq_full_selected_moments`.

Empirical status: DERIVED -- the quotient of the composed `DD` coordinates, whose status it
inherits.  No equality between this quotient and an ascertained score-portability factor is
asserted. -/
noncomputable def DemographicTwoLocusMoments.unascertainedLDCorrelationSq {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (_ : moments.LDNormalizationDomain rho first second) : ℝ :=
  (moments.DD rho first second) ^ 2 /
    (moments.DD rho first first * moments.DD rho second second)

/-- On the nondegenerate normalization domain, the determinant quotient is exactly the
square of the normalized `DD` correlation.  The quotient form evaluates without first
assuming Cauchy--Schwarz; the correlation form explains its statistical meaning. -/
theorem DemographicTwoLocusMoments.unascertainedLDCorrelationSq_eq {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDNormalizationDomain rho first second) :
    moments.unascertainedLDCorrelationSq rho first second domain =
      (moments.crossDemeLDCorrelation rho first second domain) ^ 2 := by
  unfold DemographicTwoLocusMoments.unascertainedLDCorrelationSq
    DemographicTwoLocusMoments.crossDemeLDCorrelation
  rw [div_pow, Real.sq_sqrt
    (mul_nonneg domain.firstWithin_pos.le domain.secondWithin_pos.le)]

/-- The squared unascertained `DD` correlation is nonnegative on its typed domain. -/
theorem DemographicTwoLocusMoments.unascertainedLDCorrelationSq_nonneg {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDNormalizationDomain rho first second) :
    0 ≤ moments.unascertainedLDCorrelationSq rho first second domain :=
  div_nonneg (sq_nonneg _) (mul_nonneg domain.firstWithin_pos.le domain.secondWithin_pos.le)

/-- A genuine squared normalized `DD` correlation cannot exceed one.  The Cauchy--Schwarz
fact is part of `LDPairDomain`, rather than silently assumed
from arbitrary real-valued moment fields. -/
theorem DemographicTwoLocusMoments.unascertainedLDCorrelationSq_le_one {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho : MarkerSeparationBp)
    (first second : Fin D)
    (domain : moments.LDPairDomain rho first second) :
    moments.unascertainedLDCorrelationSq rho first second domain.toLDNormalizationDomain ≤ 1 := by
  unfold DemographicTwoLocusMoments.unascertainedLDCorrelationSq
  exact (div_le_one (mul_pos domain.firstWithin_pos domain.secondWithin_pos)).2
    domain.cross_sq_le

/-- Evaluability domain for an unascertained panel-moment quotient: the panel's within-source
linkage mass and both heterozygosity readouts are positive. -/
structure DemographicTwoLocusMoments.UnascertainedPanelMomentDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : Prop where
  panelWithin_pos : 0 < ∑ k, moments.DD (panel k) source source
  sourceHet_pos : 0 < moments.H hetRho source source
  targetHet_pos : 0 < moments.H hetRho target target

/-- **An unascertained low-order panel-moment quotient.**

The expression is

  `((Σ DD_st) / (Σ DD_ss))² · (H_ss / H_tt)²`

Under equal deme sizes and a single separation the quotient reduces to
`unascertainedLDCorrelationSq` exactly
(`unascertainedPanelMomentRatio_eq_unascertainedLDCorrelationSq`).

It is not a selected-score transport law.  It discards marker-specific ascertainment,
estimated weights, clumping, cross-marker covariance, and the causal architecture.  Earlier
empirical agreement of this quotient with some stress cells does not establish the missing
identity; the unascertained scalar projection fails the gnomon linkage gate and must not be
used as an end-to-end predictor. -/
noncomputable def DemographicTwoLocusMoments.unascertainedPanelMomentRatio {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (_ : moments.UnascertainedPanelMomentDomain panel hetRho source target) : ℝ :=
  (((∑ k, moments.DD (panel k) source target) /
      (∑ k, moments.DD (panel k) source source)) ^ 2) *
    ((moments.H hetRho source source / moments.H hetRho target target) ^ 2)

/-- The unascertained panel-moment quotient is normalized to one at its source. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentRatio_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.UnascertainedPanelMomentDomain panel hetRho source source) :
    moments.unascertainedPanelMomentRatio panel hetRho source source domain = 1 := by
  unfold DemographicTwoLocusMoments.unascertainedPanelMomentRatio
  rw [div_self domain.panelWithin_pos.ne', div_self domain.sourceHet_pos.ne']
  norm_num

/-- The unascertained panel-moment quotient is a product of squares, hence nonnegative. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentRatio_nonneg {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (domain : moments.UnascertainedPanelMomentDomain panel hetRho source target) :
    0 ≤ moments.unascertainedPanelMomentRatio panel hetRho source target domain := by
  unfold DemographicTwoLocusMoments.unascertainedPanelMomentRatio
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Realizability domain for a Cauchy bound on the unascertained panel-moment quotient. -/
structure DemographicTwoLocusMoments.UnascertainedPanelMomentCauchyDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : Prop extends
      moments.UnascertainedPanelMomentDomain panel hetRho source target where
  pairDomain : ∀ k, moments.LDPairDomain (panel k) source target

/-- The panel-wide Cauchy upper envelope.  The linkage contribution is the ratio of total
target to total source within-deme `DD`; the heterozygosity scale is the same exact factor as
in `unascertainedPanelMomentRatio`. -/
noncomputable def DemographicTwoLocusMoments.unascertainedPanelMomentCauchyBound {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D) : ℝ :=
  ((∑ k, moments.DD (panel k) target target) /
      (∑ k, moments.DD (panel k) source source)) *
    (moments.H hetRho source source / moments.H hetRho target target) ^ 2

/-- The Cauchy envelope is normalized exactly at the training deme. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentCauchyBound_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.UnascertainedPanelMomentDomain panel hetRho source source) :
    moments.unascertainedPanelMomentCauchyBound panel hetRho source source = 1 := by
  unfold DemographicTwoLocusMoments.unascertainedPanelMomentCauchyBound
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

/-- Cauchy--Schwarz bounds the unascertained panel-moment quotient for every finite moment
field satisfying the pairwise covariance certificates.  This is not a bound on the
ascertained score's `R²`. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentRatio_le_cauchyBound {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source target : Fin D)
    (domain : moments.UnascertainedPanelMomentCauchyDomain panel hetRho source target) :
    moments.unascertainedPanelMomentRatio panel hetRho source target
        domain.toUnascertainedPanelMomentDomain ≤
      moments.unascertainedPanelMomentCauchyBound panel hetRho source target := by
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
  unfold DemographicTwoLocusMoments.unascertainedPanelMomentRatio
    DemographicTwoLocusMoments.unascertainedPanelMomentCauchyBound
  dsimp only [sourceSum, targetSum, crossSum, heterozygosityFactor] at hlinkage ⊢
  exact mul_le_mul_of_nonneg_right hlinkage (sq_nonneg _)

/-- The moment-quotient Cauchy envelope is attained at the source population. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentRatio_eq_cauchyBound_self {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin n → MarkerSeparationBp)
    (hetRho : MarkerSeparationBp) (source : Fin D)
    (domain : moments.UnascertainedPanelMomentCauchyDomain panel hetRho source source) :
    moments.unascertainedPanelMomentRatio panel hetRho source source
        domain.toUnascertainedPanelMomentDomain =
      moments.unascertainedPanelMomentCauchyBound panel hetRho source source := by
  rw [moments.unascertainedPanelMomentRatio_self panel hetRho source domain.toUnascertainedPanelMomentDomain,
    moments.unascertainedPanelMomentCauchyBound_self panel hetRho source domain.toUnascertainedPanelMomentDomain]

/-- On a symmetric pair the panel quotient is the squared unascertained `DD` correlation.  With a
single panel separation, equal within-deme linkage and equal heterozygosity, this moment
quotient reduces to `unascertainedLDCorrelationSq`.  This is an identity between
unascertained moment summaries, not an identification with selected-score portability. -/
theorem DemographicTwoLocusMoments.unascertainedPanelMomentRatio_eq_unascertainedLDCorrelationSq {D : ℕ}
    (moments : DemographicTwoLocusMoments D) (rho hetRho : MarkerSeparationBp)
    (source target : Fin D)
    (domain : moments.UnascertainedPanelMomentDomain (fun _ : Fin 1 ↦ rho) hetRho source target)
    (ndom : moments.LDNormalizationDomain rho source target)
    (hDD : moments.DD rho source source = moments.DD rho target target)
    (hH : moments.H hetRho source source = moments.H hetRho target target) :
    moments.unascertainedPanelMomentRatio (fun _ : Fin 1 ↦ rho) hetRho source target domain =
      moments.unascertainedLDCorrelationSq rho source target ndom := by
  unfold DemographicTwoLocusMoments.unascertainedPanelMomentRatio
    DemographicTwoLocusMoments.unascertainedLDCorrelationSq
  rw [Fin.sum_univ_one, Fin.sum_univ_one, hH, div_self domain.targetHet_pos.ne',
    one_pow, mul_one, div_pow]
  congr 1
  linear_combination moments.DD rho source source * hDD

/-- Domain for the selection-weighted `DD` proxy: positive within-source linkage at
every panel separation, and a nonzero reference regression at the tightest separation. -/
structure DemographicTwoLocusMoments.SelectionWeightedDDProxyDomain {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (source target : Fin D) : Prop where
  within_pos : ∀ k, 0 < moments.DD (panel k) source source
  ref_ne : moments.DD (panel 0) source target ≠ 0

/-- **A selection-weighted `DD` proxy, not a selected-score law.**

The clump index of a GWAS region is a random location on the linkage profile, and the
transported accuracy channel it carries is the selection-conditioned REGRESSION retention
`DD_tj/DD_tt` at that location, scaled to the self channel at the tightest separation.
Given winner-location weights `w` and a self-channel amplitude `selfAmp`, the proxy is

  `ratio = (Σ_k w k · selfAmp · reg k / reg 0)²,  reg k = DD_tj(panel k)/DD_tt(panel k)`.

Its limits recover earlier proxy bodies: a point mass at the tightest
separation gives the pure self-channel law, and degenerate flat weights with unit self
amplitude give the unconditioned `unascertainedPanelMomentRatio` family.

Empirical status: MEASURED, blind, three times, on the grid2d demography with the real
plink P+T pipeline and hash-pinned predictors (validation/empirical/gate/): the
unconditioned family misses +0.261 ± 0.101 (gate 1, seeds 101-108) and the pure
self-channel endpoint misses -0.272 ± 0.047 (gate 2, seeds 109-116), while this proxy
passes every pre-filed bar at gate 3 (seeds 117-124): transport ratio +0.032 ± 0.052 and
chart AUC -0.002 ± 0.009, zero fitted constants in the chain.  The governing complete
derivation, with the frozen list of terms measured to lie below gate power at this
design (multi-causal regions, panel winner's curse, the LD-field closure bound), is
validation/empirical/gate/EXACT_TRANSPORT_DERIVATION.md.  Passing those cells does not
upgrade the proxy to an exact law. -/
noncomputable def DemographicTwoLocusMoments.selectionWeightedDDProxy {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (winner : Fin (n + 1) → ℝ) (selfAmp : ℝ) (source target : Fin D)
    (_ : moments.SelectionWeightedDDProxyDomain panel source target) : ℝ :=
  ((∑ k, winner k * (selfAmp *
      ((moments.DD (panel k) source target / moments.DD (panel k) source source) /
        (moments.DD (panel 0) source target / moments.DD (panel 0) source source)))) ^ 2)

/-- **A point mass at the tightest separation recovers the self-channel law exactly.** -/
theorem DemographicTwoLocusMoments.selectionWeightedDDProxy_pointMass {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (selfAmp : ℝ) (source target : Fin D)
    (domain : moments.SelectionWeightedDDProxyDomain panel source target) :
    moments.selectionWeightedDDProxy panel
      (fun k ↦ if k = 0 then 1 else 0) selfAmp source target domain = selfAmp ^ 2 := by
  classical
  unfold DemographicTwoLocusMoments.selectionWeightedDDProxy
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

/-- The selection-weighted proxy is a square, hence nonnegative. -/
theorem DemographicTwoLocusMoments.selectionWeightedDDProxy_nonneg {D n : ℕ}
    (moments : DemographicTwoLocusMoments D) (panel : Fin (n + 1) → MarkerSeparationBp)
    (winner : Fin (n + 1) → ℝ) (selfAmp : ℝ) (source target : Fin D)
    (domain : moments.SelectionWeightedDDProxyDomain panel source target) :
    0 ≤ moments.selectionWeightedDDProxy panel winner selfAmp source target domain :=
  sq_nonneg _

/-- Concrete three-deme moment table for the transport-domain witness.  Three demes rather
than two so that two-deme degeneracies cannot hide; every within-deme heterozygosity and
linkage value is distinct so the size-correction factor and the normalization are both
exercised rather than silently equal to one.

Empirical status: NOT AN EMPIRICAL CLAIM -- a concrete table inhabiting the interface. -/
noncomputable def panelMomentWitnessMoments : DemographicTwoLocusMoments 3 where
  H := fun _ i j ↦ (i.val + j.val + 2 : ℝ)
  DD := fun _ i j ↦ if i = j then (i.val + 2 : ℝ) else 1
  Dz := fun _ _ _ _ ↦ 0
  pi2 := fun _ _ _ _ _ ↦ 0

/-- **The Cauchy--Schwarz-certified pair domain has a named off-boundary inhabitant.**  The
cross moment is 1 against within-deme moments 2 and 3, so the certificate inequality
`1 < 6` holds STRICTLY -- a witness at equality would certify a perfectly correlated pair
and hide a body that only works on the degenerate boundary.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
theorem panelMomentPairDomainWitness :
    panelMomentWitnessMoments.LDPairDomain clumpWindowSeparation 0 1 where
  firstWithin_pos := by
    simp [panelMomentWitnessMoments]
  secondWithin_pos := by
    simp [panelMomentWitnessMoments]
    norm_num
  cross_sq_le := by
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    simp [panelMomentWitnessMoments, h01]
    norm_num

/-- The transport domain has an off-boundary inhabitant: a one-window panel at the 250 kb
clump separation between demes of UNEQUAL heterozygosity (2 versus 4), so the witness would
detect a body that dropped the size-correction factor rather than only certifying that the
quotients evaluate.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
theorem panelMomentDomainWitness :
    panelMomentWitnessMoments.UnascertainedPanelMomentDomain
      (fun _ : Fin 1 ↦ clumpWindowSeparation) clumpWindowSeparation 0 1 where
  panelWithin_pos := by
    simp [panelMomentWitnessMoments]
  sourceHet_pos := by simp [panelMomentWitnessMoments]
  targetHet_pos := by
    simp [panelMomentWitnessMoments]
    norm_num

/-- The selection-panel domain has a named off-boundary inhabitant on the witness table:
within-deme linkage 2 and 3 (positive, distinct) and cross linkage 1 (nonzero), so the
reference regression is exercised away from every degenerate value.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness. -/
theorem selectionPanelDomainWitness :
    panelMomentWitnessMoments.SelectionWeightedDDProxyDomain
      (fun _ : Fin 2 ↦ clumpWindowSeparation) 0 1 where
  within_pos := by
    intro k
    simp [panelMomentWitnessMoments]
  ref_ne := by
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    simp [panelMomentWitnessMoments, h01]

/-- The bare normalization domain inherits the pair witness's inhabitant by projection.

Empirical status: NOT AN EMPIRICAL CLAIM -- an inhabitation witness by projection. -/
theorem panelMomentNormalizationDomainWitness :
    panelMomentWitnessMoments.LDNormalizationDomain clumpWindowSeparation 0 1 :=
  panelMomentPairDomainWitness.toLDNormalizationDomain

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
