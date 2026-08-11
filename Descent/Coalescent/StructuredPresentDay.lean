/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Structured
import Descent.Core.Moments
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

namespace Coalescent

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

/-- Fixed difference under the directly solved joint law. -/
noncomputable def solvedTwoDemeFixedDifference
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt)) : ℝ :=
  solvedTwoDemeJointSampleCount ns nt system ns 0 +
    solvedTwoDemeJointSampleCount ns nt system 0 nt

/-- Target erosion conditional on source polymorphism, with both masses evaluated from the
same directly solved joint law. -/
noncomputable def solvedTwoDemeTargetErosionGivenSourcePolymorphic
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt)) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (ns - 1),
      solvedTwoDemeJointSampleCount ns nt system i 0 +
        solvedTwoDemeJointSampleCount ns nt system i nt) /
    (∑ i ∈ Finset.Icc 1 (ns - 1),
      ∑ j ∈ Finset.range (nt + 1), solvedTwoDemeJointSampleCount ns nt system i j)

/-- Conditional target spectrum at a given source count, directly from the symbolic joint
law. -/
noncomputable def solvedTwoDemeConditionalTargetSpectrum
    (ns nt : ℕ) (system : NonsingularTwoDemeMomentSystem (ns + nt))
    (sourceCount targetCount : ℕ) : ℝ :=
  solvedTwoDemeJointSampleCount ns nt system sourceCount targetCount /
    (∑ j ∈ Finset.range (nt + 1),
      solvedTwoDemeJointSampleCount ns nt system sourceCount j)

/-- A solved present-day mixed-moment law for a specified two-deme demography.

`stationary` is the Notohara structured moment system.  For a transient epoch the same
interface is filled by the epoch propagator and the field is the corresponding forward
equation; downstream sample laws do not change.  The normalization and Hausdorff bounds are
part of the object, preventing an arbitrary table from masquerading as a population law. -/
structure TwoDemePresentDayLaw where
  rates : TwoDemeRates
  mixedMoment : ℕ → ℕ → ℝ
  normalized : mixedMoment 0 0 = 1
  stationary : ∀ i j, i + j > 0 →
    twoDemeMomentGenerator rates mixedMoment i j = 0
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
    (law : TwoDemePresentDayLaw) (ns nt : ℕ) : ℝ :=
  let sourcePolyTargetMono :=
    ∑ i ∈ Finset.Icc 1 (ns - 1),
      twoDemeJointSampleCount law ns nt i 0 +
        twoDemeJointSampleCount law ns nt i nt
  let sourcePoly :=
    ∑ i ∈ Finset.Icc 1 (ns - 1),
      ∑ j ∈ Finset.range (nt + 1), twoDemeJointSampleCount law ns nt i j
  sourcePolyTargetMono / sourcePoly

/-- Conditional target spectrum given a source count.  This is the object required by
ascertainment: the numerator and denominator are entries of one joint law, so conditioning
cannot introduce an independently chosen sign or multiplier. -/
noncomputable def twoDemeConditionalTargetSpectrum
    (law : TwoDemePresentDayLaw) (ns nt sourceCount targetCount : ℕ) : ℝ :=
  twoDemeJointSampleCount law ns nt sourceCount targetCount /
    (∑ j ∈ Finset.range (nt + 1),
      twoDemeJointSampleCount law ns nt sourceCount j)

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
  symmetricWithin : ∀ rho M,
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
  symmetricWithin : ∀ rho M,
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

/-- A2's closed form for an arbitrary published affine moment system. -/
noncomputable def AffineTwoDemeLDSystem.crossDCorrelation {n : ℕ}
    (sys : AffineTwoDemeLDSystem n) (rho M : ℝ) : ℝ :=
  sys.toSystem.crossDCorrelation rho M

/-- A parameter point on which the affine stationary solution and its correlation denominator
exist.  Both counterexample-producing poles are excluded by the value's type. -/
structure NonsingularAffineLDPoint {n : ℕ} (sys : AffineTwoDemeLDSystem n) where
  rho : ℝ
  migration : ℝ
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

/-- Pairwise coalescence times in raw generations. -/
structure PairwiseCoalescenceTimes (D : ℕ) where
  within : Fin D → ℝ
  between : Fin D → Fin D → ℝ
  within_pos : ∀ d, 0 < within d
  between_pos : ∀ i j, 0 < between i j

/-- A typed joint spectrum rather than an unlabelled array of reals. -/
structure JointSampleSpectrum (D : ℕ) where
  sampleSize : Fin D → ℕ
  mass : (∀ d, Fin (sampleSize d + 1)) → ℝ
  mass_nonneg : ∀ cell, 0 ≤ mass cell

/-- The two-locus moments a demographic history supplies at a recombination coordinate. -/
structure DemographicTwoLocusMoments (D : ℕ) where
  DD : ℝ → Fin D → Fin D → ℝ
  Dz : ℝ → Fin D → Fin D → Fin D → ℝ
  pi2 : ℝ → Fin D → Fin D → Fin D → Fin D → ℝ

/-- The complete typed output of a demography.  Serial-founder, grid and `stdpopsim` histories
are constructors of this interface, not new metric derivations. -/
structure DemographyFunctionals (D : ℕ) where
  coalescence : PairwiseCoalescenceTimes D
  spectrum : JointSampleSpectrum D
  twoLocus : DemographicTwoLocusMoments D

/-- Slatkin--Hudson `F_ST` on the typed coalescence constructor. -/
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

end Coalescent

end Descent
