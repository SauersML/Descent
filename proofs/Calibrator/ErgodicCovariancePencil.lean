/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.NNReal.Basic
import Calibrator.PencilEnvironment

/-!
# Ergodic covariance pencils: the law-preserving formulation

This module repairs the probabilistic foundation of a proposed source/target covariance
pencil.  A coordinatewise Markov update that preserves the marginal law at each locus does
not, in general, preserve the joint law across loci.  The correct primitive is a stationary
space--time field: source and target are two time slices of one process, and stationarity is
asserted for the law of the *whole slice*.

## Biological reading

The spatial coordinate may index ordered variants, haplotype blocks, or genomic windows.
A slice is then a population-specific local-dependence field from which an LD/covariance
operator is built.  The coupling time is a separation between two populations or sampling
epochs in a calibrated evolutionary/environmental dynamics; it is not itself a divergence
and is identifiable only relative to that dynamics' relaxation scale.

This file deliberately separates proved finite algebra from spectral-program claims.

* Proved here: joint stationarity implies every coordinate marginal is preserved; the
  converse fails; the two-site generalized Rayleigh quotient is a ratio of local covariance
  gaps; and an eigenmode conditional mean produces the exact affine-exponential local trace
  law.
* Not asserted here: existence of an infinite-volume density of states, a Thouless formula,
  Kotani/Minami theory for random `R_II` pencils, Poisson edge limits, or a sampled
  extremal-to-Bessel crossover.  Those require analytic input absent from Mathlib.

The categorical correction is equally important.  Two independent bounded-range operators
in the same genomic basis are not made asymptotically free merely by independence of their
environments.  Free multiplicative convolution belongs to an additional rotationally
invariant sampling layer (for example Wishart noise), not to the population coupling itself.
The positive four-step path expression is formalized once, in
`tridiagonalABAB_pathExpression_pos`.
-/

namespace Calibrator

open MeasureTheory

/-! ## Joint-law stationarity -/

/-- Two source/target slices coupled on one probability space, with equality of their full
process laws.  This is the minimum law-preserving object needed by a covariance pencil.

`source` and `target` take values in the entire process space `K → E`; the equality is not
merely a collection of one-coordinate marginal equalities. -/
structure StationaryTwoSliceField (Ω K E : Type*)
    [MeasurableSpace Ω] [MeasurableSpace E] where
  /-- Probability law of the underlying space--time realization. -/
  probability : Measure Ω
  /-- The underlying law is normalized. -/
  isProbability : IsProbabilityMeasure probability
  /-- Source time slice. -/
  source : Ω → K → E
  /-- Target time slice. -/
  target : Ω → K → E
  /-- Measurability of the full source slice. -/
  measurable_source : Measurable source
  /-- Measurability of the full target slice. -/
  measurable_target : Measurable target
  /-- Stationarity at the level of the full process law. -/
  jointLaw_preserved : Measure.map source probability = Measure.map target probability

/-- A jointly stationary space--time field.  This structure records the law-preserving
content needed downstream.  Markov, reversibility, ergodicity, and spatial-shift covariance
are additional analytic hypotheses for limit theorems; they are intentionally not replaced
by opaque Boolean fields here. -/
structure StationarySpaceTimeField (Ω K E : Type*)
    [MeasurableSpace Ω] [MeasurableSpace E] where
  /-- Probability law of the full realization. -/
  probability : Measure Ω
  /-- Normalization of the realization law. -/
  isProbability : IsProbabilityMeasure probability
  /-- Process slice at nonnegative coupling time. -/
  slice : NNReal → Ω → K → E
  /-- Every full slice is measurable. -/
  measurable_slice : ∀ t, Measurable (slice t)
  /-- Time stationarity at the level of the full spatial process law. -/
  stationary : ∀ t, Measure.map (slice t) probability = Measure.map (slice 0) probability

/-- **The class is inhabited**, by the constant field on a one-point realization
space.

    Stationarity is the field with content, and a slice that does not depend on
    `t` satisfies it by reflexivity. This establishes only that the theorems
    below are about something; a field with genuine time dependence is what they
    are for. -/
noncomputable def StationarySpaceTimeField.witness (K : Type*) :
    StationarySpaceTimeField Unit K Unit where
  probability := Measure.dirac ()
  isProbability := by infer_instance
  slice := fun _ _ _ ↦ ()
  measurable_slice := fun _ ↦ measurable_const
  stationary := fun _ ↦ rfl

namespace StationarySpaceTimeField

/-- Extract the source/target coupling at time separation `tau`.  Both slices live on the
same realization, so `tau` is literally a time separation rather than a label for two
unrelated ensembles. -/
def twoSlice {Ω K E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : StationarySpaceTimeField Ω K E) (tau : NNReal) :
    StationaryTwoSliceField Ω K E where
  probability := P.probability
  isProbability := P.isProbability
  source := P.slice 0
  target := P.slice tau
  measurable_source := P.measurable_slice 0
  measurable_target := P.measurable_slice tau
  jointLaw_preserved := (P.stationary tau).symm

end StationarySpaceTimeField

/-- **The two-slice class is inhabited**, by the zero-separation coupling of the
constant field above.

    `twoSlice` alone does not establish this: it builds a two-slice field *from* a
    stationary space--time field, so it moves the obligation rather than
    discharging it.  Supplying the space--time witness discharges it. -/
noncomputable def StationaryTwoSliceField.witness (K : Type*) :
    StationaryTwoSliceField Unit K Unit :=
  (StationarySpaceTimeField.witness K).twoSlice 0

namespace StationaryTwoSliceField

/-- Full slice-law preservation implies preservation of every one-locus marginal.  The
converse is false; `coordinateMarginalsDoNotDetermineJointLaw` below is a finite witness. -/
theorem coordinateLaw_preserved {Ω K E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (P : StationaryTwoSliceField Ω K E) (k : K) :
    Measure.map (fun ω ↦ P.source ω k) P.probability =
      Measure.map (fun ω ↦ P.target ω k) P.probability := by
  have h := congrArg (Measure.map (fun x : K → E ↦ x k)) P.jointLaw_preserved
  simpa [Measure.map_map (measurable_pi_apply k) P.measurable_source,
    Measure.map_map (measurable_pi_apply k) P.measurable_target] using h

end StationaryTwoSliceField

/-! ### A finite witness: marginals survive while dependence is destroyed -/

/-- A perfectly dependent two-locus binary process. -/
def coupledBinarySource (ω : Bool) (_ : Fin 2) : Bool := ω

/-- A second slice obtained by flipping only locus `1`.  Both loci remain fair under a fair
input bit, but the two-locus dependence changes from equality to anti-equality. -/
def coordinatewiseMarginalPreserver (ω : Bool) (k : Fin 2) : Bool :=
  if k = 0 then ω else !ω

/-- The source and transformed processes have the same counting law at each individual
coordinate.  This is the finite analogue of preserving all one-dimensional marginals. -/
theorem binary_coordinate_marginals_match (k : Fin 2) (b : Bool) :
    ((Finset.univ.filter fun ω : Bool ↦ coupledBinarySource ω k = b).card) =
      ((Finset.univ.filter fun ω : Bool ↦ coordinatewiseMarginalPreserver ω k = b).card) := by
  fin_cases k <;> cases b <;> decide

/-- The full joint laws nevertheless differ: the source loci agree for every realization,
whereas the transformed loci never agree.  Coordinatewise invariance is therefore
insufficient for a law-preserving matrix pencil. -/
theorem coordinateMarginalsDoNotDetermineJointLaw :
    (∀ ω : Bool, coupledBinarySource ω 0 = coupledBinarySource ω 1) ∧
      (∀ ω : Bool, coordinatewiseMarginalPreserver ω 0 ≠
        coordinatewiseMarginalPreserver ω 1) := by
  constructor <;> intro ω <;> cases ω <;> decide

/-! ## Covariance-to-precision reduction -/

/-- **The pencil factorization.**  For invertible covariance matrices,
`A⁻¹ (B - λA) B⁻¹ = A⁻¹ - λB⁻¹`.  Thus the dense covariance pencil reduces to
the reversed pair of precision matrices.  When the underlying population model is
finite-range Markov, those precisions are banded and the generalized eigenvector equation
is a finite-order transfer recurrence. -/
theorem covariancePencil_precision_factorization {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (lambda : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ * (B - lambda • A) * B⁻¹ = A⁻¹ - lambda • B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_nonsing_inv_cancel_right B A⁻¹ hB]
  congr 1
  calc
    A⁻¹ * (lambda • A) * B⁻¹ = (lambda • (A⁻¹ * A)) * B⁻¹ := by
      rw [Matrix.mul_smul]
    _ = (lambda • (1 : Matrix n n ℝ)) * B⁻¹ := by rw [A.nonsing_inv_mul hA]
    _ = lambda • B⁻¹ := by simp

/-- Determinant form of `covariancePencil_precision_factorization`.  The two inverse
determinants are nonzero under the hypotheses, so the determinant vanishes at exactly the
same `lambda` for the covariance and precision pencils. -/
theorem precisionPencil_det_factorization {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (lambda : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (A⁻¹ - lambda • B⁻¹).det =
      A⁻¹.det * (B - lambda • A).det * B⁻¹.det := by
  rw [← covariancePencil_precision_factorization A B lambda hA hB,
    Matrix.det_mul, Matrix.det_mul]

/-- The covariance pencil and reversed precision pencil have exactly the same generalized
eigenvalue equation. -/
theorem covariancePencil_det_zero_iff_precisionPencil_det_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (lambda : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (B - lambda • A).det = 0 ↔ (A⁻¹ - lambda • B⁻¹).det = 0 := by
  have hAinv : A⁻¹.det ≠ 0 := (A.isUnit_nonsing_inv_det hA).ne_zero
  have hBinv : B⁻¹.det ≠ 0 := (B.isUnit_nonsing_inv_det hB).ne_zero
  constructor
  · intro h
    rw [precisionPencil_det_factorization A B lambda hA hB, h]
    ring
  · intro h
    rw [precisionPencil_det_factorization A B lambda hA hB] at h
    rcases mul_eq_zero.mp h with hleft | hright
    · rcases mul_eq_zero.mp hleft with hbad | hpencil
      · exact absurd hbad hAinv
      · exact hpencil
    · exact absurd hright hBinv

/-! ## The two-site pencil identity -/

/-- Quadratic energy of the two-site unit-diagonal covariance block
`[[1, ρ], [ρ, 1]]` at vector `(x,y)`. -/
def twoSiteCovarianceEnergy (ρ x y : ℝ) : ℝ := x ^ 2 + y ^ 2 + 2 * ρ * x * y

/-- The local contrast `(1,-1)` sees exactly twice the covariance gap `1-ρ`. -/
theorem twoSiteCovarianceEnergy_contrast (ρ : ℝ) :
    twoSiteCovarianceEnergy ρ 1 (-1) = 2 * (1 - ρ) := by
  unfold twoSiteCovarianceEnergy
  ring

/-- **Local generalized Rayleigh quotient.**  For source and target correlations `a,b`, the
contrast direction has target/source energy ratio `(1-b)/(1-a)`.  This is the finite
algebraic mechanism by which a single near-degenerate target/source excursion can create a
small generalized eigenvalue. -/
theorem twoSitePencil_contrast_ratio (a b : ℝ) (ha : 1 - a ≠ 0) :
    twoSiteCovarianceEnergy b 1 (-1) / twoSiteCovarianceEnergy a 1 (-1) =
      (1 - b) / (1 - a) := by
  rw [twoSiteCovarianceEnergy_contrast, twoSiteCovarianceEnergy_contrast]
  field_simp

/-! ## Exact first-mode relaxation of the local trace contribution -/

/-- Per-edge contribution appearing when a target covariance is traced against the
tridiagonal precision of the source Markov covariance. -/
noncomputable def localPencilTraceContribution (source target : ℝ) : ℝ :=
  (1 + source ^ 2 - 2 * source * target) / (1 - source ^ 2)

/-- **localPencilTraceContribution where its denominator vanishes, named.** The guard `1 - source ^
2` is zero at `source = 1`. At unit source coherence the pencil is degenerate and the trace
contribution diverges. Lean returns `0` there rather than the value the modelled quantity takes,
and no type error marks the point. Consumers must require `1 - source ^ 2 ≠ 0`. -/
theorem localPencilTraceContribution_at_source1_is_junk (target : ℝ) :
    localPencilTraceContribution 1 target = 0 := by
  unfold localPencilTraceContribution
  norm_num

/-- Conditional mean of a first semigroup eigenfunction: `r = exp(-λ τ)` in the Jacobi
anchor, `mean` is the invariant mean, and `source` is the time-zero coordinate. -/
def firstModeConditionalMean (mean r source : ℝ) : ℝ :=
  mean + r * (source - mean)

/-- **firstModeConditionalMean pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `1 / 2`, which fixes the coefficients a
one-sided bound or an invariance leaves free. -/
theorem firstModeConditionalMean_at_reference_point :
    firstModeConditionalMean (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold firstModeConditionalMean
  norm_num

/-- **Exact affine-exponential relaxation, pointwise.**  Substituting a first-eigenmode
conditional mean splits the local trace contribution into its independent-slice value and a
single correction proportional to `r`.  Averaging this identity gives the covariance term
in the first spectral moment; setting `r = exp(-λ τ)` gives pure exponential relaxation. -/
theorem localPencilTraceContribution_firstMode (source mean r : ℝ)
    (hsource : 1 - source ^ 2 ≠ 0) :
    localPencilTraceContribution source (firstModeConditionalMean mean r source) =
      localPencilTraceContribution source mean -
        2 * r * (source * (source - mean) / (1 - source ^ 2)) := by
  unfold localPencilTraceContribution firstModeConditionalMean
  field_simp
  ring

end Calibrator
