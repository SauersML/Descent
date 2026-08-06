/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.DGP
import Descent.Spectral.EnsembleChannel

assert_below Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision
assert_below Descent.Program

namespace Descent.Spectral

/-!
# Permeability of a completed portability experiment

For a centered Gaussian estimator whose covariance in one observed direction is `Σ`, a
deployment tangent changes that covariance at rate `Γ`.  The local Fisher information in
one draw is

`p = 1/2 * (Γ / Σ)^2`.

This is the sound order-two core of the proposed permeability law.  It gives a concrete
method-design score: among candidate LD, haplotype, ancestry-tract, or longitudinal probes,
prefer directions with large covariance sensitivity relative to their own noise.  The
score is invariant to changing genotype coding units and adds across independent probes.

The known-mean centered Gaussian covariance experiment is derived below from its second
and fourth moments, including its exact information--variance constant. No CLT-to-LAN
transfer, Edgeworth hierarchy, universal support-floor model, or general minimax constant
is asserted. Those require a separately named experiment and uniform regularity.

The module also contains one exact direction-sensitive channel: the two-orientation
binary transition experiment from `EnsembleChannel`.  Every order-free readout collapses
the two orientations, while the ordered arrow has unit response, variance `1-θ²`, and
per-pair permeability `1/(1-θ²)`.  This supplies a concrete haplotype/ancestry-transition
positive control when orientation has biological meaning (for example parent-of-origin,
multiple feature channels, or longitudinal state).  Ordinary real scalar LD is
second-order reversal-even, so the calculation is not promoted to a theorem about arbitrary
genomic chains.
-/

open scoped BigOperators

/-- One-dimensional Gaussian covariance permeability. -/
noncomputable def scalarPermeability (covariance covarianceDerivative : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (covarianceDerivative / covariance) ^ 2

/-- **scalarPermeability at its junk point, named.** A vanishing covariance makes the relative
sensitivity, and with it the Fisher-type permeability, unbounded. The ratio is junk-zero and the
permeability reports `0`: a perfectly impermeable channel where the truth is a perfectly
transparent one. Consumers must guard the argument that makes the divisor vanish. -/
theorem scalarPermeability_zero_covariance_is_junk (covarianceDerivative : ℝ) :
    scalarPermeability 0 covarianceDerivative = 0 := by
  unfold scalarPermeability
  simp

/-! ## The named Gaussian covariance experiment -/

/-- Variance of a centered square from its second and fourth raw moments. -/
noncomputable def centeredSquareVarianceFromMoments
    (secondMoment fourthMoment : ℝ) : ℝ :=
  fourthMoment - secondMoment ^ 2

/-- **The variance of a squared standard Gaussian, pinned.** This definition carries no theorem
of its own. A standard Gaussian has second moment one and fourth moment three, so its square has
variance two -- the reference value that separates this body from `fourthMoment - secondMoment`
and from `fourthMoment ^ 2 - secondMoment ^ 2`. -/
theorem centeredSquareVarianceFromMoments_standard_gaussian :
    centeredSquareVarianceFromMoments 1 3 = 2 := by
  unfold centeredSquareVarianceFromMoments
  norm_num

/-- A centered Gaussian variable of variance `Σ` has square variance `2Σ²`.  This is the
moment identity that fixes the constant in Gaussian covariance information. -/
theorem centeredSquareVariance_gaussian (covariance : ℝ) :
    centeredSquareVarianceFromMoments covariance (3 * covariance ^ 2) =
      2 * covariance ^ 2 := by
  unfold centeredSquareVarianceFromMoments
  ring

/-- Second moment of the Gaussian covariance score, expressed only through raw moments.
For covariance tangent `Γ`, the score is
`Γ (X² - Σ) / (2Σ²)`, so its second moment is the coefficient squared times
`Var(X²)`. -/
noncomputable def covarianceScoreInformationFromMoments
    (covariance covarianceDerivative secondMoment fourthMoment : ℝ) : ℝ :=
  (covarianceDerivative / (2 * covariance ^ 2)) ^ 2 *
    centeredSquareVarianceFromMoments secondMoment fourthMoment

/-- A vanishing covariance sends `covarianceDerivative / (2 * covariance ^ 2)` to Mathlib's
junk `0`, and the information with it.  Zero information is what a genuinely uninformative
channel also reports, so the branch has to be named. -/
theorem covarianceScoreInformationFromMoments_at_zero_covariance_is_junk
    (covarianceDerivative secondMoment fourthMoment : ℝ) :
    covarianceScoreInformationFromMoments 0 covarianceDerivative secondMoment fourthMoment = 0 := by
  unfold covarianceScoreInformationFromMoments
  simp


/-- **Derivation of permeability from the Gaussian experiment.** Substituting
`E[X²]=Σ` and `E[X⁴]=3Σ²` into the covariance score gives exactly
`p = (1/2)(Γ/Σ)²`; the factor `1/2` is therefore already inside `p`. -/
theorem covarianceScoreInformation_gaussian
    (covariance covarianceDerivative : ℝ) (hcovariance : covariance ≠ 0) :
    covarianceScoreInformationFromMoments covariance covarianceDerivative
        covariance (3 * covariance ^ 2) =
      scalarPermeability covariance covarianceDerivative := by
  unfold covarianceScoreInformationFromMoments scalarPermeability
  rw [centeredSquareVariance_gaussian]
  field_simp [hcovariance]

/-- **Kurtosis correction to the Gaussian covariance score.** If
`E[X²]=Σ` and `E[X⁴]=κΣ²`, the variance of the Gaussian covariance score is

`((κ - 1)/4) (Γ/Σ)²`.

At `κ=3` this is ordinary Gaussian permeability. Away from Gaussianity it is a
quasi-score variance, not automatically the Fisher information of the true likelihood;
that distinction is essential for discrete genotype and haplotype features. -/
theorem covarianceScoreInformation_kurtosis
    (covariance covarianceDerivative kurtosis : ℝ)
    (hcovariance : covariance ≠ 0) :
    covarianceScoreInformationFromMoments covariance covarianceDerivative
        covariance (kurtosis * covariance ^ 2) =
      ((kurtosis - 1) / 4) * (covarianceDerivative / covariance) ^ 2 := by
  unfold covarianceScoreInformationFromMoments centeredSquareVarianceFromMoments
  field_simp [hcovariance]
  ring

/-! ## Distribution-robust covariance-moment permeability -/

/-- Response-to-noise permeability of a scalar moment experiment.  If a retained summary
has local mean derivative `Γ` and variance `V`, then averaging independent copies estimates
the tangent with reciprocal-variance information `Γ²/V`. -/
noncomputable def momentPermeability (response noiseVariance : ℝ) : ℝ :=
  Descent.Core.scaledSquare response noiseVariance

/-- **The permeability's junk branch, named.** At zero noise the permeability diverges and Lean
returns `0`, so a noiseless channel is reported as carrying no information. Consumers must
require `noiseVariance ≠ 0`. -/
theorem momentPermeability_zero_noise_is_junk (response : ℝ) :
    momentPermeability response 0 = 0 := by
  unfold momentPermeability Descent.Core.scaledSquare; simp

/-- Rescaling a scalar moment and its response by the same nonzero factor leaves
permeability unchanged: response squares and noise variance scale together. -/
theorem momentPermeability_scale
    (response noiseVariance scale : ℝ) (hscale : scale ≠ 0) :
    momentPermeability (scale * response) (scale ^ 2 * noiseVariance) =
      momentPermeability response noiseVariance := by
  unfold momentPermeability Descent.Core.scaledSquare
  field_simp [hscale]

/-- **Permeability of the named covariance-moment experiment.**  A centered-square
summary has noise variance `Var(X²)` and response `Γ`, so its local signal-to-noise
information is `Γ² / Var(X²)`.

Unlike `covarianceScoreInformationFromMoments`, this is not the variance of a Gaussian
quasi-score applied to non-Gaussian data.  It is the exact reciprocal-variance geometry
of the method-of-moments covariance estimator.  This is the relevant order-two design
quantity for discrete genotype, haplotype, burden, and ancestry-summary channels when
only their second and fourth moments are being used. -/
noncomputable def covarianceMomentPermeability
    (covarianceDerivative secondMoment fourthMoment : ℝ) : ℝ :=
  covarianceDerivative ^ 2 /
    centeredSquareVarianceFromMoments secondMoment fourthMoment

/-- With no centered-square variance the quotient is junk `0`, reporting an impermeable channel
where the model has no noise scale at all. -/
theorem covarianceMomentPermeability_at_zero_noise_is_junk
    (covarianceDerivative secondMoment fourthMoment : ℝ)
    (hzero : centeredSquareVarianceFromMoments secondMoment fourthMoment = 0) :
    covarianceMomentPermeability covarianceDerivative secondMoment fourthMoment = 0 := by
  unfold covarianceMomentPermeability
  rw [hzero, div_zero]


/-- Covariance-moment permeability is the generic scalar moment law applied to the
centered-square channel. -/
theorem covarianceMomentPermeability_eq_momentPermeability
    (covarianceDerivative secondMoment fourthMoment : ℝ) :
    covarianceMomentPermeability covarianceDerivative secondMoment fourthMoment =
      momentPermeability covarianceDerivative
        (centeredSquareVarianceFromMoments secondMoment fourthMoment) := rfl

/-! ### Exact permeability of the two-orientation arrow experiment -/

/-- Per-ordered-pair permeability for the binary orientation experiment from
`EnsembleChannel`.  The ordered arrow has unit mean response and variance `1 - θ²`. -/
noncomputable def binaryOrientationArrowPermeability (θ : ℝ) : ℝ :=
  momentPermeability 1 (binaryOrientationArrowVariance θ)

/-- **The arrow permeability inherits the junk branch of `momentPermeability`.** Wherever the
orientation variance vanishes the permeability diverges and Lean returns `0`, reporting a
noiseless arrow as carrying no information. Consumers must exclude those `θ`. -/
theorem binaryOrientationArrowPermeability_zero_variance_is_junk (θ : ℝ)
    (hθ : binaryOrientationArrowVariance θ = 0) :
    binaryOrientationArrowPermeability θ = 0 := by
  unfold binaryOrientationArrowPermeability
  rw [hθ, momentPermeability_zero_noise_is_junk]

/-- **Closed arrow information law.** One ordered adjacent pair carries permeability
`1/(1-θ²)` for the orientation-imbalance coordinate.  This is an exact law for the named
two-orientation experiment, not a universal claim about arbitrary non-reversible chains. -/
theorem binaryOrientationArrowPermeability_eq (θ : ℝ) :
    binaryOrientationArrowPermeability θ = 1 / (1 - θ ^ 2) := by
  simp [binaryOrientationArrowPermeability, momentPermeability,
    binaryOrientationArrowVariance,
      Descent.Core.scaledSquare]

/-- At the reversible center `θ = 0`, one ordered pair carries one unit of arrow
information in the natural normalization. -/
theorem binaryOrientationArrowPermeability_zero :
    binaryOrientationArrowPermeability 0 = 1 := by
  norm_num [binaryOrientationArrowPermeability, momentPermeability,
    binaryOrientationArrowVariance,
      Descent.Core.scaledSquare]

/-- `m` independent ordered pairs carry `m/(1-θ²)` total arrow permeability. -/
noncomputable def totalBinaryOrientationArrowPermeability (m θ : ℝ) : ℝ :=
  m * binaryOrientationArrowPermeability θ

theorem totalBinaryOrientationArrowPermeability_eq (m θ : ℝ) :
    totalBinaryOrientationArrowPermeability m θ = m / (1 - θ ^ 2) := by
  rw [totalBinaryOrientationArrowPermeability,
    binaryOrientationArrowPermeability_eq]
  ring

/-- Permeability of the vector-valued three-cycle arrow witness.  Its observed arrow is
the binary orientation sign scaled by `1/3`, so its mean response is `1/3` and its variance
is `(1-θ²)/9`. -/
noncomputable def threeCycleOrientationArrowPermeability (θ : ℝ) : ℝ :=
  momentPermeability (1 / 3) ((1 / 3 : ℝ) ^ 2 * (1 - θ ^ 2))

/-- The three-cycle vector witness carries exactly the same orientation information as the
unit-scaled binary arrow.  This is coding-scale invariance, not an additional information
source. -/
theorem threeCycleOrientationArrowPermeability_eq_binary (θ : ℝ) :
    threeCycleOrientationArrowPermeability θ =
      binaryOrientationArrowPermeability θ := by
  unfold threeCycleOrientationArrowPermeability binaryOrientationArrowPermeability
  simpa [binaryOrientationArrowVariance] using
    (momentPermeability_scale 1 (1 - θ ^ 2) (1 / 3) (by norm_num))

/-- The covariance-moment permeability of a Gaussian coordinate is exactly the scalar
Gaussian permeability already used by the completed-channel theory. -/
theorem covarianceMomentPermeability_gaussian
    (covariance covarianceDerivative : ℝ) (hcovariance : covariance ≠ 0) :
    covarianceMomentPermeability covarianceDerivative covariance
        (3 * covariance ^ 2) =
      scalarPermeability covariance covarianceDerivative := by
  unfold covarianceMomentPermeability scalarPermeability
  rw [centeredSquareVariance_gaussian]
  field_simp [hcovariance]

/-- For fourth-moment ratio `κ`, covariance-moment information is
`2/(κ-1)` times Gaussian permeability at the same covariance response.  Heavy tails
therefore reduce information; this is the reciprocal counterpart of the estimator-
variance inflation law. -/
theorem covarianceMomentPermeability_kurtosis_eq_gaussian_factor
    (covariance covarianceDerivative kurtosis : ℝ)
    (hcovariance : covariance ≠ 0) (hkurtosis : kurtosis ≠ 1) :
    covarianceMomentPermeability covarianceDerivative covariance
        (kurtosis * covariance ^ 2) =
      (2 / (kurtosis - 1)) *
        scalarPermeability covariance covarianceDerivative := by
  unfold covarianceMomentPermeability centeredSquareVarianceFromMoments
    scalarPermeability
  field_simp [hcovariance, sub_ne_zero.mpr hkurtosis]

/-- Linear attenuation of the covariance response reduces distribution-robust moment
permeability quadratically, independently of the feature's fourth moment. -/
theorem covarianceMomentPermeability_derivative_scale
    (covarianceDerivative secondMoment fourthMoment η : ℝ) :
    covarianceMomentPermeability (η * covarianceDerivative) secondMoment fourthMoment =
      η ^ 2 * covarianceMomentPermeability
        covarianceDerivative secondMoment fourthMoment := by
  unfold covarianceMomentPermeability
  ring

/-- Information in `m` independent covariance-moment summaries. -/
noncomputable def totalCovarianceMomentInformation
    (m covarianceDerivative secondMoment fourthMoment : ℝ) : ℝ :=
  m * covarianceMomentPermeability
    covarianceDerivative secondMoment fourthMoment

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem totalCovarianceMomentInformation_at_reference_point :
    totalCovarianceMomentInformation 2 2 2 2 = -4 := by
  norm_num [totalCovarianceMomentInformation, centeredSquareVarianceFromMoments,
    covarianceMomentPermeability]


/-- Effective target replicate count required to match a source experiment's total
information when per-replicate permeability changes.  Counts are real-valued design
quantities; an implemented study rounds upward. -/
noncomputable def replicatesForEqualPermeability
    (sourceReplicates sourcePermeability targetPermeability : ℝ) : ℝ :=
  sourceReplicates * sourcePermeability / targetPermeability

/-- **replicatesForEqualPermeability at zero targetPermeability, named.** A target channel with zero
permeability cannot be matched at any number of replicates. Lean returns `0`, reporting that
no replication is needed to match an unmatchable channel. Consumers must require
`targetPermeability ≠ 0`. -/
theorem replicatesForEqualPermeability_zero_targetpermeability_is_junk
    (sourceReplicates sourcePermeability : ℝ) :
    replicatesForEqualPermeability sourceReplicates sourcePermeability 0 = 0 := by
  unfold replicatesForEqualPermeability
  simp

/-- **General cohort-allocation law.** Multiplying target permeability by the prescribed
replicate count recovers exactly the source total information. -/
theorem replicatesForEqualPermeability_spec
    (sourceReplicates sourcePermeability targetPermeability : ℝ)
    (htarget : targetPermeability ≠ 0) :
    replicatesForEqualPermeability
        sourceReplicates sourcePermeability targetPermeability *
      targetPermeability = sourceReplicates * sourcePermeability := by
  unfold replicatesForEqualPermeability
  field_simp [htarget]

/-- Total covariance-moment permeability of finitely many independent channels.  Each
channel may have its own response and second/fourth moments.  Independence is the
load-bearing premise: correlated quadratic summaries require their full noise covariance,
not this diagonal sum. -/
noncomputable def diagonalCovarianceMomentPermeability {ι : Type*} [Fintype ι]
    (covarianceDerivative secondMoment fourthMoment : ι → ℝ) : ℝ :=
  ∑ i, covarianceMomentPermeability
    (covarianceDerivative i) (secondMoment i) (fourthMoment i)

/-- Vanishing identity: a design with no covariance sensitivity is impermeable. -/
theorem diagonalCovarianceMomentPermeability_zero_sensitivity_eq_zero {ι : Type*} [Fintype ι]
    (secondMoment fourthMoment : ι → ℝ) :
    diagonalCovarianceMomentPermeability 0 secondMoment fourthMoment = 0 := by
  unfold diagonalCovarianceMomentPermeability covarianceMomentPermeability
  simp


/-- A common linear response attenuation multiplies the information of the whole
independent non-Gaussian panel by `η²`. -/
theorem diagonalCovarianceMomentPermeability_derivative_scale
    {ι : Type*} [Fintype ι]
    (covarianceDerivative secondMoment fourthMoment : ι → ℝ) (η : ℝ) :
    diagonalCovarianceMomentPermeability
        (fun i ↦ η * covarianceDerivative i) secondMoment fourthMoment =
      η ^ 2 * diagonalCovarianceMomentPermeability
        covarianceDerivative secondMoment fourthMoment := by
  unfold diagonalCovarianceMomentPermeability
  simp_rw [covarianceMomentPermeability_derivative_scale]
  rw [Finset.mul_sum]

/-- A covariance-moment channel with nonzero square-noise variance seals exactly when
its covariance response is zero. -/
theorem covarianceMomentPermeability_eq_zero_iff
    {covarianceDerivative secondMoment fourthMoment : ℝ}
    (hnoise : centeredSquareVarianceFromMoments secondMoment fourthMoment ≠ 0) :
    covarianceMomentPermeability covarianceDerivative secondMoment fourthMoment = 0 ↔
      covarianceDerivative = 0 := by
  unfold covarianceMomentPermeability
  rw [div_eq_zero_iff]
  simp [hnoise]

/-- With positive square-noise variance in every independent channel, panel moment
permeability is zero exactly when every channel's response vanishes. -/
theorem diagonalCovarianceMomentPermeability_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (covarianceDerivative secondMoment fourthMoment : ι → ℝ)
    (hnoise : ∀ i,
      0 < centeredSquareVarianceFromMoments (secondMoment i) (fourthMoment i)) :
    diagonalCovarianceMomentPermeability
        covarianceDerivative secondMoment fourthMoment = 0 ↔
      ∀ i, covarianceDerivative i = 0 := by
  classical
  constructor
  · intro hsum i
    have hnonneg : ∀ j,
        0 ≤ covarianceMomentPermeability
          (covarianceDerivative j) (secondMoment j) (fourthMoment j) := by
      intro j
      unfold covarianceMomentPermeability
      exact div_nonneg (sq_nonneg _) (le_of_lt (hnoise j))
    have hle : covarianceMomentPermeability
        (covarianceDerivative i) (secondMoment i) (fourthMoment i) ≤
        diagonalCovarianceMomentPermeability
          covarianceDerivative secondMoment fourthMoment := by
      unfold diagonalCovarianceMomentPermeability
      exact Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
    have hzero : covarianceMomentPermeability
        (covarianceDerivative i) (secondMoment i) (fourthMoment i) = 0 := by
      apply le_antisymm
      · simpa [hsum] using hle
      · exact hnonneg i
    exact (covarianceMomentPermeability_eq_zero_iff
      (ne_of_gt (hnoise i))).mp hzero
  · intro hresponse
    unfold diagonalCovarianceMomentPermeability
    simp [hresponse, covarianceMomentPermeability]

/-! ## Correlated non-Gaussian covariance-moment channels -/

/-- **Precision-weighted covariance-moment permeability.**  If `response` is the vector
of derivatives of retained quadratic summaries and `precision` is the inverse of their
noise covariance matrix `Ω`, the exact generalized method-of-moments information for one
deployment tangent is

`responseᵀ precision response`.

The definition accepts the precision matrix directly.  Symmetry, positive definiteness,
and the proof that it is the inverse of the named summary covariance are model-specific
obligations.  This separation prevents marginal fourth moments or pairwise LD from being
silently treated as the full joint fourth-order experiment. -/
noncomputable def covarianceMomentPermeabilityWithPrecision {d : ℕ}
    (precision : Matrix (Fin d) (Fin d) ℝ) (response : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, response i * precision i j * response j

/-- The entrywise definition is the usual quadratic form `responseᵀ precision response`. -/
theorem covarianceMomentPermeabilityWithPrecision_eq_dotProduct_mulVec {d : ℕ}
    (precision : Matrix (Fin d) (Fin d) ℝ) (response : Fin d → ℝ) :
    covarianceMomentPermeabilityWithPrecision precision response =
      dotProduct response (precision.mulVec response) := by
  unfold covarianceMomentPermeabilityWithPrecision Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive-definite summary precision gives strictly positive information for every
nonzero biological response direction. -/
theorem covarianceMomentPermeabilityWithPrecision_pos {d : ℕ}
    (precision : Matrix (Fin d) (Fin d) ℝ) (response : Fin d → ℝ)
    (hprecision : precision.PosDef) (hresponse : response ≠ 0) :
    0 < covarianceMomentPermeabilityWithPrecision precision response := by
  rw [covarianceMomentPermeabilityWithPrecision_eq_dotProduct_mulVec]
  simpa using hprecision.2 response hresponse

/-- Under positive-definite precision, correlated covariance-moment permeability seals
exactly when the entire retained response vector vanishes. -/
theorem covarianceMomentPermeabilityWithPrecision_eq_zero_iff {d : ℕ}
    (precision : Matrix (Fin d) (Fin d) ℝ) (response : Fin d → ℝ)
    (hprecision : precision.PosDef) :
    covarianceMomentPermeabilityWithPrecision precision response = 0 ↔ response = 0 := by
  constructor
  · intro hzero
    by_contra hresponse
    have hpos := covarianceMomentPermeabilityWithPrecision_pos
      precision response hprecision hresponse
    linarith
  · intro hzero
    subst response
    simp [covarianceMomentPermeabilityWithPrecision]

/-- The diagonal precision constructed from channel-specific square-noise variances. -/
noncomputable def diagonalSquareNoisePrecision {d : ℕ}
    (secondMoment fourthMoment : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun i ↦
    1 / centeredSquareVarianceFromMoments (secondMoment i) (fourthMoment i)

/-- A channel with no centered-square variance gets Mathlib's junk precision `0` on the
diagonal, which reads as infinite noise rather than as an undefined channel. -/
theorem diagonalSquareNoisePrecision_at_zero_variance_is_junk {d : ℕ}
    (secondMoment fourthMoment : Fin d → ℝ) (i : Fin d)
    (hzero : centeredSquareVarianceFromMoments (secondMoment i) (fourthMoment i) = 0) :
    diagonalSquareNoisePrecision secondMoment fourthMoment i i = 0 := by
  unfold diagonalSquareNoisePrecision
  rw [Matrix.diagonal_apply_eq, hzero, div_zero]


/-- Positive square-noise variance in every independent channel makes the induced
diagonal precision positive definite. -/
theorem diagonalSquareNoisePrecision_posDef {d : ℕ}
    (secondMoment fourthMoment : Fin d → ℝ)
    (hnoise : ∀ i,
      0 < centeredSquareVarianceFromMoments (secondMoment i) (fourthMoment i)) :
    (diagonalSquareNoisePrecision secondMoment fourthMoment).PosDef := by
  unfold diagonalSquareNoisePrecision
  apply Matrix.PosDef.diagonal
  intro i
  exact one_div_pos.mpr (hnoise i)

/-- **Diagonal reduction.**  When quadratic-summary noise is independent, the full
precision-weighted law is exactly the sum of scalar non-Gaussian moment permeabilities. -/
theorem covarianceMomentPermeabilityWithPrecision_diagonal {d : ℕ}
    (covarianceDerivative secondMoment fourthMoment : Fin d → ℝ) :
    covarianceMomentPermeabilityWithPrecision
        (diagonalSquareNoisePrecision secondMoment fourthMoment)
        covarianceDerivative =
      diagonalCovarianceMomentPermeability
        covarianceDerivative secondMoment fourthMoment := by
  classical
  unfold covarianceMomentPermeabilityWithPrecision diagonalSquareNoisePrecision
    diagonalCovarianceMomentPermeability covarianceMomentPermeability
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diagonal_apply]
  ring

/-- Linear attenuation of every correlated moment response obeys the same exact
inverse-square information law. -/
theorem covarianceMomentPermeabilityWithPrecision_scale {d : ℕ}
    (precision : Matrix (Fin d) (Fin d) ℝ) (response : Fin d → ℝ) (η : ℝ) :
    covarianceMomentPermeabilityWithPrecision precision (fun i ↦ η * response i) =
      η ^ 2 * covarianceMomentPermeabilityWithPrecision precision response := by
  unfold covarianceMomentPermeabilityWithPrecision
  calc
    ∑ i, ∑ j, (η * response i) * precision i j * (η * response j) =
        ∑ i, η ^ 2 * ∑ j, response i * precision i j * response j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = η ^ 2 * ∑ i, ∑ j, response i * precision i j * response j := by
      rw [Finset.mul_sum]

/-- Symmetric two-channel precision matrix, useful for displaying the joint-noise cross
term explicitly. -/
noncomputable def twoChannelMomentPrecision
    (first second shared : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![first, shared], ![shared, second]]

/-- Two covariance-summary responses. -/
noncomputable def twoChannelMomentResponse (first second : ℝ) : Fin 2 → ℝ :=
  ![first, second]

/-- **Exact correlated two-channel moment law.**  The off-diagonal precision contributes
`2·shared·firstResponse·secondResponse`.  Depending on the inverse-noise geometry and the
response signs, correlated summaries can contribute less or more than a naive diagonal
calculation; they must not simply be counted as independent loci or probes. -/
theorem twoChannelMomentPermeabilityWithPrecision
    (firstPrecision secondPrecision sharedPrecision firstResponse secondResponse : ℝ) :
    covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentPrecision firstPrecision secondPrecision sharedPrecision)
        (twoChannelMomentResponse firstResponse secondResponse) =
      firstPrecision * firstResponse ^ 2 +
        2 * sharedPrecision * firstResponse * secondResponse +
        secondPrecision * secondResponse ^ 2 := by
  simp [covarianceMomentPermeabilityWithPrecision, twoChannelMomentPrecision,
    twoChannelMomentResponse, Fin.sum_univ_two]
  ring

/-! ### Adding a correlated probe: the innovation law -/

/-- Determinant of the noise covariance of two quadratic-summary channels. -/
noncomputable def twoChannelMomentNoiseDet
    (firstNoise secondNoise sharedNoise : ℝ) : ℝ :=
  firstNoise * secondNoise - sharedNoise ^ 2

/-- **The two-channel noise determinant, pinned.** This definition carries no result of its own.
The shared-noise term enters squared and subtracted, so a reference evaluation is what separates
it from `firstNoise * secondNoise - sharedNoise` and from a body that adds the shared term. -/
theorem twoChannelMomentNoiseDet_reference :
    twoChannelMomentNoiseDet 2 3 1 = 5 := by
  unfold twoChannelMomentNoiseDet
  norm_num

/-- Explicit inverse of the symmetric two-channel noise covariance
`[[v₁,c],[c,v₂]]`, expressed through its determinant. -/
noncomputable def twoChannelMomentNoisePrecision
    (firstNoise secondNoise sharedNoise : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let det := twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise
  twoChannelMomentPrecision
    (secondNoise / det) (firstNoise / det) (-sharedNoise / det)

/-- A singular two-channel noise determinant sends every entry to Mathlib's junk `0`, so the
precision matrix reads as a channel with no information rather than an undefined one. -/
theorem twoChannelMomentNoisePrecision_at_zero_determinant_is_junk
    (firstNoise secondNoise sharedNoise : ℝ)
    (hzero : twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise = 0) :
    twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise
      = twoChannelMomentPrecision 0 0 0 := by
  show twoChannelMomentPrecision
      (secondNoise / twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise)
      (firstNoise / twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise)
      (-sharedNoise / twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise) = _
  rw [hzero, div_zero, div_zero, div_zero]


/-- Response of the second channel not predicted by the first channel through their
noise covariance. -/
noncomputable def twoChannelConditionalMomentResponse
    (firstNoise sharedNoise firstResponse secondResponse : ℝ) : ℝ :=
  secondResponse - (sharedNoise / firstNoise) * firstResponse

/-- **twoChannelConditionalMomentResponse at its junk point, named.** A noiseless first channel
determines its own moment exactly, so conditioning on it should remove the whole shared
component. The divisor is zero, the regression coefficient is junk-zero, and the second response
is returned UNCHANGED -- the value for two independent channels. Consumers must exclude the
argument that makes the guard vanish. -/
theorem twoChannelConditionalMomentResponse_noiseless_first_is_junk
    (sharedNoise firstResponse secondResponse : ℝ) :
    twoChannelConditionalMomentResponse 0 sharedNoise firstResponse secondResponse =
      secondResponse := by
  unfold twoChannelConditionalMomentResponse
  simp

/-- **With no shared noise the second channel is read unadjusted.** The regression coefficient
that removes the first channel is exactly the shared-to-own noise ratio, and at zero shared noise
it vanishes; a body carrying any other numerator would still be a difference of responses. -/
theorem twoChannelConditionalMomentResponse_no_shared_noise
    (firstNoise firstResponse secondResponse : ℝ) :
    twoChannelConditionalMomentResponse firstNoise 0 firstResponse secondResponse
      = secondResponse := by
  unfold twoChannelConditionalMomentResponse
  simp

/-- Residual square-noise variance of the second channel after projecting out the first. -/
noncomputable def twoChannelConditionalMomentNoise
    (firstNoise secondNoise sharedNoise : ℝ) : ℝ :=
  secondNoise - sharedNoise ^ 2 / firstNoise

/-- **Conditional noise on a noiseless first channel, named.** A first channel with zero noise is
deterministic, so conditioning on it removes everything the two channels share and the shared
term is not merely undefined but maximally informative. Lean returns the second channel's noise
unchanged -- conditioning removed NOTHING -- which is the value for two independent channels.
Consumers must require `firstNoise ≠ 0`. -/
theorem twoChannelConditionalMomentNoise_noiseless_first_is_junk (secondNoise sharedNoise : ℝ) :
    twoChannelConditionalMomentNoise 0 secondNoise sharedNoise = secondNoise := by
  unfold twoChannelConditionalMomentNoise
  simp

/-- **Closed two-channel GMM information.**  Inverting the named noise covariance gives
the standard numerator divided by its determinant. -/
theorem twoChannelMomentNoisePermeability_closed
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ) :
    covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) =
      (secondNoise * firstResponse ^ 2 -
          2 * sharedNoise * firstResponse * secondResponse +
          firstNoise * secondResponse ^ 2) /
        twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise := by
  unfold twoChannelMomentNoisePrecision
  rw [twoChannelMomentPermeabilityWithPrecision]
  unfold twoChannelMomentNoiseDet
  ring

/-- Conditional noise is the covariance determinant divided by first-channel noise. -/
theorem twoChannelConditionalMomentNoise_eq_det_div
    (firstNoise secondNoise sharedNoise : ℝ) (hfirst : firstNoise ≠ 0) :
    twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise =
      twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise / firstNoise := by
  unfold twoChannelConditionalMomentNoise twoChannelMomentNoiseDet
  field_simp [hfirst]

/-- Positive first-channel noise and positive covariance determinant imply positive
conditional noise for the added channel. -/
theorem twoChannelConditionalMomentNoise_pos
    (firstNoise secondNoise sharedNoise : ℝ)
    (hfirst : 0 < firstNoise)
    (hdet : 0 < twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise) :
    0 < twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise := by
  rw [twoChannelConditionalMomentNoise_eq_det_div _ _ _ (ne_of_gt hfirst)]
  exact div_pos hdet hfirst

/-- **Base plus innovation decomposition.**  Information from two correlated probes is
the first probe's information plus the squared conditional response of the added probe,
normalized by its conditional noise.  This is the constructive method-design form of
`ΓᵀΩ⁻¹Γ`. -/
theorem twoChannelMomentInformation_eq_base_add_innovation
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hfirst : firstNoise ≠ 0)
    (hdet : twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise ≠ 0) :
    covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) =
      firstResponse ^ 2 / firstNoise +
        twoChannelConditionalMomentResponse
            firstNoise sharedNoise firstResponse secondResponse ^ 2 /
          twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise := by
  rw [twoChannelMomentNoisePermeability_closed,
    twoChannelConditionalMomentNoise_eq_det_div _ _ _ hfirst]
  unfold twoChannelConditionalMomentResponse twoChannelMomentNoiseDet at *
  field_simp [hfirst, hdet]
  ring_nf
  field_simp [hdet]
  ring

/-- Under a valid positive two-channel noise covariance, an added probe can never reduce
optimal moment information. -/
theorem twoChannelMomentInformation_ge_first
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hfirst : 0 < firstNoise)
    (hdet : 0 < twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise) :
    firstResponse ^ 2 / firstNoise ≤
      covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) := by
  rw [twoChannelMomentInformation_eq_base_add_innovation _ _ _ _ _
    (ne_of_gt hfirst) (ne_of_gt hdet)]
  have hconditional := twoChannelConditionalMomentNoise_pos
    firstNoise secondNoise sharedNoise hfirst hdet
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (le_of_lt hconditional))

/-- **Strict value-of-a-new-probe criterion.**  A second correlated probe strictly
improves information exactly when its response contains a nonzero innovation beyond what
the first probe's noise correlation predicts. -/
theorem twoChannelMomentInformation_strictly_improves
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hfirst : 0 < firstNoise)
    (hdet : 0 < twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise)
    (hinnovation : twoChannelConditionalMomentResponse
      firstNoise sharedNoise firstResponse secondResponse ≠ 0) :
    firstResponse ^ 2 / firstNoise <
      covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) := by
  rw [twoChannelMomentInformation_eq_base_add_innovation _ _ _ _ _
    (ne_of_gt hfirst) (ne_of_gt hdet)]
  have hconditional := twoChannelConditionalMomentNoise_pos
    firstNoise secondNoise sharedNoise hfirst hdet
  have hgain : 0 <
      twoChannelConditionalMomentResponse
          firstNoise sharedNoise firstResponse secondResponse ^ 2 /
        twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise :=
    div_pos (sq_pos_of_ne_zero hinnovation) hconditional
  linarith

/-- **Exact redundancy criterion.**  The second channel adds no information precisely
when its response equals the response predicted from the first through the shared noise. -/
theorem twoChannelMomentInformation_eq_first_iff
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hfirst : 0 < firstNoise)
    (hdet : 0 < twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise) :
    covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) =
        firstResponse ^ 2 / firstNoise ↔
      twoChannelConditionalMomentResponse
        firstNoise sharedNoise firstResponse secondResponse = 0 := by
  rw [twoChannelMomentInformation_eq_base_add_innovation _ _ _ _ _
    (ne_of_gt hfirst) (ne_of_gt hdet)]
  have hconditional := twoChannelConditionalMomentNoise_pos
    firstNoise secondNoise sharedNoise hfirst hdet
  constructor
  · intro hsum
    have hgain :
        twoChannelConditionalMomentResponse
            firstNoise sharedNoise firstResponse secondResponse ^ 2 /
          twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise = 0 := by
      linarith
    exact (div_eq_zero_iff.mp hgain).resolve_right (ne_of_gt hconditional) |>
      sq_eq_zero_iff.mp
  · intro hzero
    simp [hzero]

/-! ### Fixed-budget assay design -/

/-- Information delivered per unit acquisition cost. -/
noncomputable def informationPerUnitCost (information cost : ℝ) : ℝ :=
  Descent.Core.ratio information cost

/-- **informationPerUnitCost at zero cost, named.** Free information has unbounded value per unit
cost. Lean returns `0`, ranking the free measurement last. Consumers must require `cost ≠ 0`. -/
theorem informationPerUnitCost_zero_cost_is_junk (information : ℝ) :
    informationPerUnitCost information 0 = 0 := by
  unfold informationPerUnitCost Descent.Core.ratio
  simp

/-- **The rate does not depend on the units.** Measuring both information and cost in units `t`
times smaller leaves the rate unchanged, which is what makes it a rate rather than a difference. -/
theorem informationPerUnitCost_scale_invariant (information cost t : ℝ) (ht : t ≠ 0) :
    informationPerUnitCost (t * information) (t * cost)
      = informationPerUnitCost information cost := by
  unfold informationPerUnitCost Descent.Core.ratio
  exact mul_div_mul_left _ _ ht

/-- **Spending the cost back recovers the information.** Scale invariance holds for every rate of
the same degree and so leaves the constant free; this fixes it at one. -/
theorem informationPerUnitCost_mul_cost (information cost : ℝ) (hc : cost ≠ 0) :
    informationPerUnitCost information cost * cost = information := by
  unfold informationPerUnitCost Descent.Core.ratio
  field_simp

/-- Total information attainable by spending a fixed budget on exchangeable units of one
design. Fractional units represent the continuous design relaxation; an implemented study
rounds sample counts and rechecks the inequality. -/
noncomputable def informationAtBudget (budget information cost : ℝ) : ℝ :=
  budget * informationPerUnitCost information cost

/-- **Information bought is linear in the budget.** Doubling the budget doubles the information
at a fixed rate, and no budget buys nothing. A body that saturated would not be a budget times a
rate. -/
theorem informationAtBudget_linear (budget information cost c : ℝ) :
    informationAtBudget (c * budget) information cost
      = c * informationAtBudget budget information cost := by
  unfold informationAtBudget; ring

theorem informationAtBudget_zero (information cost : ℝ) :
    informationAtBudget 0 information cost = 0 := by
  unfold informationAtBudget; ring

/-- At positive budget, ordering designs by total attainable information is exactly the
same as ordering them by information per unit cost. -/
theorem informationAtBudget_lt_iff_informationPerUnitCost_lt
    (budget firstInformation firstCost secondInformation secondCost : ℝ)
    (hbudget : 0 < budget) :
    informationAtBudget budget firstInformation firstCost <
        informationAtBudget budget secondInformation secondCost ↔
      informationPerUnitCost firstInformation firstCost <
        informationPerUnitCost secondInformation secondCost := by
  unfold informationAtBudget
  exact mul_lt_mul_iff_right₀ hbudget

/-- **Exact augmentation threshold.**  Adding an assay with information gain `g` and
incremental cost `d` improves overall information efficiency exactly when `g/d` exceeds
the baseline design's information per cost. -/
theorem augmented_informationPerUnitCost_gt_iff
    (baseInformation gain baseCost addedCost : ℝ)
    (hbaseCost : 0 < baseCost) (haddedCost : 0 < addedCost) :
    informationPerUnitCost baseInformation baseCost <
        informationPerUnitCost
          (baseInformation + gain) (baseCost + addedCost) ↔
      informationPerUnitCost baseInformation baseCost <
        informationPerUnitCost gain addedCost := by
  unfold informationPerUnitCost Descent.Core.ratio
  constructor
  · intro h
    rw [div_lt_div_iff₀ hbaseCost (add_pos hbaseCost haddedCost)] at h
    rw [div_lt_div_iff₀ hbaseCost haddedCost]
    nlinarith
  · intro h
    rw [div_lt_div_iff₀ hbaseCost haddedCost] at h
    rw [div_lt_div_iff₀ hbaseCost (add_pos hbaseCost haddedCost)]
    nlinarith

/-- **Ordered-transition assay threshold.** Adding one binary arrow readout per unit is
worth its acquisition cost exactly when its permeability per added cost exceeds the
baseline experiment's information per cost.  This turns the one-versus-two-unit arrow
distinction into an actionable study-design comparison. -/
theorem binaryOrientationArrowAssay_moreEfficient_iff
    (baseInformation baseCost arrowCost θ : ℝ)
    (hbaseCost : 0 < baseCost) (harrowCost : 0 < arrowCost) :
    informationPerUnitCost baseInformation baseCost <
        informationPerUnitCost
          (baseInformation + binaryOrientationArrowPermeability θ)
          (baseCost + arrowCost) ↔
      informationPerUnitCost baseInformation baseCost <
        informationPerUnitCost (1 / (1 - θ ^ 2)) arrowCost := by
  rw [← binaryOrientationArrowPermeability_eq]
  exact augmented_informationPerUnitCost_gt_iff
    baseInformation (binaryOrientationArrowPermeability θ) baseCost arrowCost
      hbaseCost harrowCost

/-- Conditional information supplied by the second correlated moment probe. -/
noncomputable def twoChannelMomentInnovationInformation
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ) : ℝ :=
  twoChannelConditionalMomentResponse
      firstNoise sharedNoise firstResponse secondResponse ^ 2 /
    twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise

/-- Vanishing identity: with no response in either channel there is no innovation to read. -/
theorem twoChannelMomentInnovationInformation_no_response_eq_zero
    (firstNoise secondNoise sharedNoise : ℝ) :
    twoChannelMomentInnovationInformation firstNoise secondNoise sharedNoise 0 0 = 0 := by
  unfold twoChannelMomentInnovationInformation twoChannelConditionalMomentResponse
  simp


/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem twoChannelMomentInnovationInformation_at_zero_denominator_is_junk
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hzero : twoChannelConditionalMomentNoise firstNoise secondNoise sharedNoise = 0) :
    twoChannelMomentInnovationInformation firstNoise secondNoise sharedNoise firstResponse
      secondResponse = 0 := by
  unfold twoChannelMomentInnovationInformation
  rw [hzero, div_zero]


/-- The base-plus-innovation theorem with the added probe's information exposed as a
named method-design quantity. -/
theorem twoChannelMomentInformation_eq_base_add_named_innovation
    (firstNoise secondNoise sharedNoise firstResponse secondResponse : ℝ)
    (hfirst : firstNoise ≠ 0)
    (hdet : twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise ≠ 0) :
    covarianceMomentPermeabilityWithPrecision
        (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
        (twoChannelMomentResponse firstResponse secondResponse) =
      firstResponse ^ 2 / firstNoise +
        twoChannelMomentInnovationInformation
          firstNoise secondNoise sharedNoise firstResponse secondResponse := by
  exact twoChannelMomentInformation_eq_base_add_innovation
    firstNoise secondNoise sharedNoise firstResponse secondResponse hfirst hdet

/-- **Optimal assay-versus-cohort rule.**  For a valid two-probe noise covariance, paying
to retain the second probe improves fixed-budget efficiency exactly when its conditional
moment-information gain per added assay cost exceeds the first probe's information per
baseline cost.

Biologically, a haplotype, sequencing, ancestry-tract, or longitudinal measurement should
be added for its *conditional* response-to-noise per dollar—not because its marginal
association is large or because it adds another marker. -/
theorem twoChannelAugmentedAssay_moreEfficient_iff
    (firstNoise secondNoise sharedNoise firstResponse secondResponse
      baseCost addedCost : ℝ)
    (hfirst : 0 < firstNoise)
    (hdet : 0 < twoChannelMomentNoiseDet firstNoise secondNoise sharedNoise)
    (hbaseCost : 0 < baseCost) (haddedCost : 0 < addedCost) :
    informationPerUnitCost (firstResponse ^ 2 / firstNoise) baseCost <
        informationPerUnitCost
          (covarianceMomentPermeabilityWithPrecision
            (twoChannelMomentNoisePrecision firstNoise secondNoise sharedNoise)
            (twoChannelMomentResponse firstResponse secondResponse))
          (baseCost + addedCost) ↔
      informationPerUnitCost (firstResponse ^ 2 / firstNoise) baseCost <
        informationPerUnitCost
          (twoChannelMomentInnovationInformation
            firstNoise secondNoise sharedNoise firstResponse secondResponse)
          addedCost := by
  rw [twoChannelMomentInformation_eq_base_add_named_innovation _ _ _ _ _
    (ne_of_gt hfirst) (ne_of_gt hdet)]
  exact augmented_informationPerUnitCost_gt_iff
    (firstResponse ^ 2 / firstNoise)
    (twoChannelMomentInnovationInformation
      firstNoise secondNoise sharedNoise firstResponse secondResponse)
    baseCost addedCost hbaseCost haddedCost

/-- Permeability is non-negative. -/
theorem scalarPermeability_nonneg (covariance covarianceDerivative : ℝ) :
    0 ≤ scalarPermeability covariance covarianceDerivative := by
  unfold scalarPermeability
  positivity

/-- At nonzero covariance, the order-two channel seals exactly when its covariance
derivative vanishes. This is an order-two statement, not absolute non-identifiability. -/
theorem scalarPermeability_eq_zero_iff {covariance covarianceDerivative : ℝ}
    (hcovariance : covariance ≠ 0) :
    scalarPermeability covariance covarianceDerivative = 0 ↔ covarianceDerivative = 0 := by
  unfold scalarPermeability
  constructor
  · intro h
    have hratio : covarianceDerivative / covariance = 0 := by nlinarith
    exact (div_eq_zero_iff).mp hratio |>.resolve_right hcovariance
  · intro h
    simp [h]

/-- Changing the units of an estimator scales its covariance and covariance derivative by
the same nonzero factor and leaves permeability unchanged. -/
theorem scalarPermeability_rescale (covariance covarianceDerivative scale : ℝ)
    (hscale : scale ≠ 0) (hcovariance : covariance ≠ 0) :
    scalarPermeability (scale * covariance) (scale * covarianceDerivative) =
      scalarPermeability covariance covarianceDerivative := by
  unfold scalarPermeability
  have hscaled : scale * covariance ≠ 0 := mul_ne_zero hscale hcovariance
  congr 1
  field_simp

/-- If a support, assay, or tagging factor `η` attenuates the covariance derivative
linearly, it attenuates Gaussian permeability quadratically. This is the exact algebraic
core of the sealing law; proving that a biological support floor actually enters the
derivative linearly is a separate model-specific obligation. -/
theorem scalarPermeability_derivative_scale
    (covariance covarianceDerivative η : ℝ) :
    scalarPermeability covariance (η * covarianceDerivative) =
      η ^ 2 * scalarPermeability covariance covarianceDerivative := by
  unfold scalarPermeability
  ring

/-- Total order-two permeability of finitely many independent scalar estimator channels. -/
noncomputable def diagonalPermeability {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ) : ℝ :=
  ∑ i, scalarPermeability (covariance i) (covarianceDerivative i)

/-- The independent non-Gaussian panel law reduces exactly to the existing independent
Gaussian permeability when every channel has Gaussian fourth moment. -/
theorem diagonalCovarianceMomentPermeability_gaussian
    {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ)
    (hcovariance : ∀ i, covariance i ≠ 0) :
    diagonalCovarianceMomentPermeability covarianceDerivative covariance
        (fun i ↦ 3 * covariance i ^ 2) =
      diagonalPermeability covariance covarianceDerivative := by
  unfold diagonalCovarianceMomentPermeability diagonalPermeability
  apply Finset.sum_congr rfl
  intro i _
  exact covarianceMomentPermeability_gaussian
    (covariance i) (covarianceDerivative i) (hcovariance i)

/-- A common tagging or assay attenuation acts on every independent completion channel
by the same inverse-square law.  This is useful for panels in which the same call-rate,
imputation-quality, or conditional-support factor multiplies every covariance response.

The premise is deliberately algebraic: a biological model must still prove that its
channel derivatives are multiplied by `η`. -/
theorem diagonalPermeability_derivative_scale {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ) (η : ℝ) :
    diagonalPermeability covariance (fun i ↦ η * covarianceDerivative i) =
      η ^ 2 * diagonalPermeability covariance covarianceDerivative := by
  unfold diagonalPermeability
  simp_rw [scalarPermeability_derivative_scale]
  rw [Finset.mul_sum]

/-! ## Correlated multivariate Gaussian channels -/

/-- **Multivariate Gaussian permeability in whitened coordinates.** If a covariance
tangent `Γ` is whitened to

`W = Σ⁻¹ᐟ² Γ Σ⁻¹ᐟ²`,

then one Gaussian estimator draw carries information `½‖W‖_F²`.  This definition takes
`W` directly: existence and correctness of a chosen whitening map are model-specific
obligations, while the information geometry after whitening is universal. -/
noncomputable def multivariateGaussianPermeability {d : ℕ}
    (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (1 / 2 : ℝ) * PopGen.frobeniusNormSq whitenedCovarianceDerivative

/-- Multivariate permeability is nonnegative. -/
theorem multivariateGaussianPermeability_nonneg {d : ℕ}
    (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ multivariateGaussianPermeability whitenedCovarianceDerivative := by
  unfold multivariateGaussianPermeability
  exact mul_nonneg (by norm_num) (PopGen.frobeniusNormSq_nonneg _)

/-- The correlated Gaussian channel seals exactly when the entire whitened covariance
response vanishes. -/
theorem multivariateGaussianPermeability_eq_zero_iff {d : ℕ}
    (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) :
    multivariateGaussianPermeability whitenedCovarianceDerivative = 0 ↔
      whitenedCovarianceDerivative = 0 := by
  constructor
  · intro hzero
    ext i j
    by_contra hentry
    have hpositive : 0 < PopGen.frobeniusNormSq whitenedCovarianceDerivative :=
      PopGen.frobeniusNormSq_pos_of_exists_ne_zero
        whitenedCovarianceDerivative ⟨i, j, hentry⟩
    unfold multivariateGaussianPermeability at hzero
    nlinarith
  · intro hzero
    subst whitenedCovarianceDerivative
    simp [multivariateGaussianPermeability, PopGen.frobeniusNormSq]

/-- Linear attenuation of the full whitened covariance response attenuates correlated
Gaussian permeability quadratically. This is the matrix sealing law. -/
theorem multivariateGaussianPermeability_scale {d : ℕ}
    (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    multivariateGaussianPermeability (η • whitenedCovarianceDerivative) =
      η ^ 2 * multivariateGaussianPermeability whitenedCovarianceDerivative := by
  have hfrob : PopGen.frobeniusNormSq (η • whitenedCovarianceDerivative) =
      η ^ 2 * PopGen.frobeniusNormSq whitenedCovarianceDerivative := by
    unfold PopGen.frobeniusNormSq
    simp only [Matrix.smul_apply, smul_eq_mul, mul_pow]
    calc
      ∑ i, ∑ j, η ^ 2 * whitenedCovarianceDerivative i j ^ 2 =
          ∑ i, η ^ 2 * ∑ j, whitenedCovarianceDerivative i j ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = η ^ 2 * ∑ i, ∑ j, whitenedCovarianceDerivative i j ^ 2 := by
        rw [Finset.mul_sum]
  unfold multivariateGaussianPermeability
  rw [hfrob]
  ring

/-- The pre-existing independent-channel formula is exactly the diagonal face of the
multivariate Hilbert--Schmidt law.  Thus the scalar and matrix APIs are one theory rather
than competing approximations. -/
theorem multivariateGaussianPermeability_diagonal {d : ℕ}
    (covariance covarianceDerivative : Fin d → ℝ) :
    multivariateGaussianPermeability
        (Matrix.diagonal fun i ↦ covarianceDerivative i / covariance i) =
      diagonalPermeability covariance covarianceDerivative := by
  classical
  unfold multivariateGaussianPermeability PopGen.frobeniusNormSq
    diagonalPermeability scalarPermeability
  simp [Matrix.diagonal_apply, Finset.mul_sum]

/-- Information in `m` independent multivariate Gaussian estimator draws. -/
noncomputable def totalMultivariateGaussianInformation {d : ℕ}
    (m : ℝ) (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  m * multivariateGaussianPermeability whitenedCovarianceDerivative

/-- Vanishing identity: no samples, no information. -/
theorem totalMultivariateGaussianInformation_zero_samples_eq_zero {d : ℕ}
    (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ) :
    totalMultivariateGaussianInformation 0 whitenedCovarianceDerivative = 0 := by
  unfold totalMultivariateGaussianInformation
  ring


/-- The inverse-square cohort compensation law remains exact for correlated channels:
attenuation by `η` is offset by multiplying effective ensemble size by `1/η²`. -/
theorem inverse_square_replicates_compensate_multivariate_attenuation {d : ℕ}
    (m η : ℝ) (whitenedCovarianceDerivative : Matrix (Fin d) (Fin d) ℝ)
    (hη : η ≠ 0) :
    totalMultivariateGaussianInformation (m / η ^ 2)
        (η • whitenedCovarianceDerivative) =
      totalMultivariateGaussianInformation m whitenedCovarianceDerivative := by
  unfold totalMultivariateGaussianInformation
  rw [multivariateGaussianPermeability_scale]
  field_simp [hη]

/-- Symmetric whitened covariance response for two correlated completion channels.
The off-diagonal coordinate `shared` is the response shared between the two probes after
whitening; biologically it can arise from overlapping LD, haplotypes, ancestry tracts, or
longitudinal sampling. -/
noncomputable def twoChannelWhitenedDerivative
    (first second shared : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  twoChannelMomentPrecision first second shared

/-- **Exact two-channel correlated law.** Off-diagonal response contributes `shared²`
to permeability in addition to the two diagonal terms. It must not be discarded merely
because each probe has already been standardized. -/
theorem twoChannelWhitenedDerivative_permeability
    (first second shared : ℝ) :
    multivariateGaussianPermeability
        (twoChannelWhitenedDerivative first second shared) =
      (1 / 2 : ℝ) * (first ^ 2 + second ^ 2) + shared ^ 2 := by
  simp [multivariateGaussianPermeability, PopGen.frobeniusNormSq,
    twoChannelWhitenedDerivative, twoChannelMomentPrecision, Fin.sum_univ_two]
  ring

/-- A genuine shared covariance response strictly increases information relative to the
diagonal-only calculation. -/
theorem twoChannel_shared_response_strictly_increases_permeability
    (first second shared : ℝ) (hshared : shared ≠ 0) :
    multivariateGaussianPermeability
        (twoChannelWhitenedDerivative first second 0) <
      multivariateGaussianPermeability
        (twoChannelWhitenedDerivative first second shared) := by
  rw [twoChannelWhitenedDerivative_permeability,
    twoChannelWhitenedDerivative_permeability]
  nlinarith [sq_pos_of_ne_zero hshared]

/-- Information in `m` independent Gaussian estimator draws for one completed
deployment coordinate.  Here `m` is real-valued so the exact design law can also describe
effective cohort size; an actual study rounds the resulting requirement upward. -/
noncomputable def totalGaussianInformation
    (m covariance covarianceDerivative : ℝ) : ℝ :=
  m * scalarPermeability covariance covarianceDerivative

/-- Variance of the known-mean method-of-moments estimator for a one-dimensional
covariance tangent, expressed through the observed coordinate's second and fourth
moments. -/
noncomputable def covarianceTangentEstimatorVarianceFromMoments
    (m covarianceDerivative secondMoment fourthMoment : ℝ) : ℝ :=
  centeredSquareVarianceFromMoments secondMoment fourthMoment /
    (m * covarianceDerivative ^ 2)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem covarianceTangentEstimatorVarianceFromMoments_at_reference_point :
    covarianceTangentEstimatorVarianceFromMoments 1 1 1 3 = 2 := by
  norm_num [covarianceTangentEstimatorVarianceFromMoments, centeredSquareVarianceFromMoments]


/-- **covarianceTangentEstimatorVarianceFromMoments at zero m, named.** At zero replicates the
estimator has no sampling distribution and its variance is undefined. Lean returns `0`, the
variance of a perfect estimator, for an estimator built from nothing. Consumers must require
`m ≠ 0`. -/
theorem covarianceTangentEstimatorVarianceFromMoments_zero_m_is_junk
    (covarianceDerivative secondMoment fourthMoment : ℝ) :
    covarianceTangentEstimatorVarianceFromMoments 0 covarianceDerivative secondMoment
      fourthMoment = 0 := by
  unfold covarianceTangentEstimatorVarianceFromMoments
  simp

/-- **Exact non-Gaussian information--variance reciprocity.** For the named
covariance-moment experiment, total moment permeability times the known-mean tangent
estimator variance is one.  No Gaussian likelihood or kurtosis approximation enters. -/
theorem totalCovarianceMomentInformation_mul_estimatorVariance
    (m covarianceDerivative secondMoment fourthMoment : ℝ)
    (hm : m ≠ 0) (hderivative : covarianceDerivative ≠ 0)
    (hnoise : centeredSquareVarianceFromMoments secondMoment fourthMoment ≠ 0) :
    totalCovarianceMomentInformation m covarianceDerivative secondMoment fourthMoment *
        covarianceTangentEstimatorVarianceFromMoments
          m covarianceDerivative secondMoment fourthMoment = 1 := by
  unfold totalCovarianceMomentInformation covarianceMomentPermeability
    covarianceTangentEstimatorVarianceFromMoments
  field_simp [hm, hderivative, hnoise]

/-- Variance of the known-mean Gaussian method-of-moments estimator for a one-dimensional
covariance tangent, based on `m` independent draws. Since `Var(X²)=2Σ²`, dividing the
sample-square fluctuation by the covariance response `Γ` gives `2Σ²/(mΓ²)`.

This is an exact finite-sample variance in the centered Gaussian experiment when the mean
is known. Estimating the mean, dependence between draws, and non-Gaussian fourth moments
change the experiment and must be handled separately. -/
noncomputable def gaussianCovarianceTangentEstimatorVariance
    (m covariance covarianceDerivative : ℝ) : ℝ :=
  covarianceTangentEstimatorVarianceFromMoments m covarianceDerivative covariance
    (3 * covariance ^ 2)

/-- The Gaussian specialization reduces to the familiar closed form. -/
theorem gaussianCovarianceTangentEstimatorVariance_eq
    (m covariance covarianceDerivative : ℝ) :
    gaussianCovarianceTangentEstimatorVariance m covariance covarianceDerivative =
      2 * covariance ^ 2 / (m * covarianceDerivative ^ 2) := by
  unfold gaussianCovarianceTangentEstimatorVariance
    covarianceTangentEstimatorVarianceFromMoments
  rw [centeredSquareVariance_gaussian]

/-- **Exact fourth-moment inflation law.** A coordinate with standardized fourth-moment
ratio `κ` inflates the known-mean covariance-tangent estimator variance by
`(κ-1)/2` relative to a Gaussian coordinate with the same covariance response.

For standardized Hardy--Weinberg dosage, `κ = 1/[2q(1-q)]`; the factor therefore diverges
as minor-allele frequency `q` approaches zero. This is the sample-complexity penalty that
a Gaussian portability calculation misses for rare variants. -/
theorem covarianceTangentEstimatorVariance_kurtosis_eq_gaussian_factor
    (m covariance covarianceDerivative kurtosis : ℝ) :
    covarianceTangentEstimatorVarianceFromMoments m covarianceDerivative covariance
        (kurtosis * covariance ^ 2) =
      ((kurtosis - 1) / 2) *
        gaussianCovarianceTangentEstimatorVariance m covariance covarianceDerivative := by
  rw [gaussianCovarianceTangentEstimatorVariance_eq]
  unfold covarianceTangentEstimatorVarianceFromMoments centeredSquareVarianceFromMoments
  ring

/-- **Joint rarity/tagging design law.** If a coordinate has fourth-moment ratio `κ` and
tagging, assay, or support attenuates its covariance response linearly by `η`, then its
known-mean covariance-tangent estimator variance is

`(κ-1)/(2η²)`

times the Gaussian, unattenuated variance. Heavy genotype tails and incomplete tagging
therefore multiply rather than add. -/
theorem covarianceTangentEstimatorVariance_kurtosis_attenuation
    (m covariance covarianceDerivative kurtosis η : ℝ)
    (hm : m ≠ 0) (hderivative : covarianceDerivative ≠ 0) (hη : η ≠ 0) :
    covarianceTangentEstimatorVarianceFromMoments m (η * covarianceDerivative)
        covariance (kurtosis * covariance ^ 2) =
      ((kurtosis - 1) / (2 * η ^ 2)) *
        gaussianCovarianceTangentEstimatorVariance m covariance covarianceDerivative := by
  rw [gaussianCovarianceTangentEstimatorVariance_eq]
  unfold covarianceTangentEstimatorVarianceFromMoments centeredSquareVarianceFromMoments
  field_simp [hm, hderivative, hη]

/-- The named Gaussian tangent-estimator variance is positive for a positive replicate
budget, positive covariance, and a nonzero covariance response. -/
theorem gaussianCovarianceTangentEstimatorVariance_pos
    (m covariance covarianceDerivative : ℝ)
    (hm : 0 < m) (hcovariance : 0 < covariance)
    (hderivative : covarianceDerivative ≠ 0) :
    0 < gaussianCovarianceTangentEstimatorVariance
      m covariance covarianceDerivative := by
  rw [gaussianCovarianceTangentEstimatorVariance_eq]
  positivity

/-- **Exact information--variance reciprocity.** In the centered Gaussian covariance
experiment, the method-of-moments tangent estimator attains reciprocal total information:

`m · p · Var(θ̂) = 1`.

Because `p` already contains the Gaussian factor `1/2`, the corresponding variance is
`1/(m p)`, not `1/(2 m p)`. Any additional half in a closing risk law must come from an
explicitly half-scaled loss, not from Fisher information. -/
theorem totalGaussianInformation_mul_estimatorVariance
    (m covariance covarianceDerivative : ℝ)
    (hm : m ≠ 0) (hcovariance : covariance ≠ 0)
    (hderivative : covarianceDerivative ≠ 0) :
    totalGaussianInformation m covariance covarianceDerivative *
      gaussianCovarianceTangentEstimatorVariance
        m covariance covarianceDerivative = 1 := by
  rw [gaussianCovarianceTangentEstimatorVariance_eq]
  unfold totalGaussianInformation scalarPermeability
  field_simp [hm, hcovariance, hderivative]

/-- Equivalent reciprocal form of
`totalGaussianInformation_mul_estimatorVariance`. -/
theorem gaussianCovarianceTangentEstimatorVariance_eq_inv_information
    (m covariance covarianceDerivative : ℝ)
    (hm : m ≠ 0) (hcovariance : covariance ≠ 0)
    (hderivative : covarianceDerivative ≠ 0) :
    gaussianCovarianceTangentEstimatorVariance m covariance covarianceDerivative =
      1 / totalGaussianInformation m covariance covarianceDerivative := by
  have hp : scalarPermeability covariance covarianceDerivative ≠ 0 := by
    intro hzero
    exact hderivative ((scalarPermeability_eq_zero_iff hcovariance).mp hzero)
  have hinfo : totalGaussianInformation m covariance covarianceDerivative ≠ 0 := by
    exact mul_ne_zero hm hp
  apply (eq_div_iff hinfo).2
  simpa [mul_comm] using
    totalGaussianInformation_mul_estimatorVariance
      m covariance covarianceDerivative hm hcovariance hderivative

/-- Half-scaled quadratic loss for the Gaussian covariance tangent estimator.  Statistical
geometry often uses `loss = ½(θ̂-θ)²`, whose Hessian is one; ordinary squared-error loss
omits this half. Keeping the convention in the definition prevents the two constants from
being conflated. -/
noncomputable def gaussianCovarianceHalfSquaredRisk
    (m covariance covarianceDerivative : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    gaussianCovarianceTangentEstimatorVariance m covariance covarianceDerivative

/-- **The closing-law half, exactly located.** Under half-scaled quadratic loss the named
Gaussian experiment contributes `1/(2mp)`. Under ordinary squared error it contributes
`1/(mp)` by `gaussianCovarianceTangentEstimatorVariance_eq_inv_information`. -/
theorem gaussianCovarianceHalfSquaredRisk_eq
    (m covariance covarianceDerivative : ℝ)
    (hm : m ≠ 0) (hcovariance : covariance ≠ 0)
    (hderivative : covarianceDerivative ≠ 0) :
    gaussianCovarianceHalfSquaredRisk m covariance covarianceDerivative =
      1 / (2 * totalGaussianInformation m covariance covarianceDerivative) := by
  unfold gaussianCovarianceHalfSquaredRisk
  rw [gaussianCovarianceTangentEstimatorVariance_eq_inv_information
    m covariance covarianceDerivative hm hcovariance hderivative]
  ring

/-- **Exact inverse-square cohort law.** If imperfect tagging, assay sensitivity, or
conditional support attenuates a covariance derivative by a nonzero factor `η`, then
`m / η²` estimator replicates recover exactly the information supplied by `m` unattenuated
replicates.

Thus a model-specific proof of linear derivative attenuation immediately yields the
portable method-design rule: halving the usable LD/haplotype signal requires four times
as many independent target cohorts or estimator draws.  The theorem does not assert that
every biological support mechanism is linear. -/
theorem inverse_square_replicates_compensate_attenuation
    (m covariance covarianceDerivative η : ℝ) (hη : η ≠ 0) :
    totalGaussianInformation (m / η ^ 2) covariance (η * covarianceDerivative) =
      totalGaussianInformation m covariance covarianceDerivative := by
  unfold totalGaussianInformation
  rw [scalarPermeability_derivative_scale]
  field_simp [hη]

/-- Independent channels have zero total permeability exactly when every covariance
derivative vanishes. -/
theorem diagonalPermeability_eq_zero_iff {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ)
    (hcovariance : ∀ i, covariance i ≠ 0) :
    diagonalPermeability covariance covarianceDerivative = 0 ↔
      ∀ i, covarianceDerivative i = 0 := by
  classical
  constructor
  · intro hsum i
    have hle : scalarPermeability (covariance i) (covarianceDerivative i) ≤
        diagonalPermeability covariance covarianceDerivative := by
      unfold diagonalPermeability
      exact Finset.single_le_sum
        (fun j _ ↦ scalarPermeability_nonneg (covariance j) (covarianceDerivative j))
        (Finset.mem_univ i)
    have hzero : scalarPermeability (covariance i) (covarianceDerivative i) = 0 := by
      apply le_antisymm
      · simpa [hsum] using hle
      · exact scalarPermeability_nonneg _ _
    exact (scalarPermeability_eq_zero_iff (hcovariance i)).mp hzero
  · intro hderiv
    unfold diagonalPermeability
    simp [hderiv, scalarPermeability]

/-- A completion with `q` scalar derivative coordinates cannot distinguish `d` independent
tangent coordinates through an injective coordinate assignment unless `d ≤ q`. The exact
minimum may be larger; dimension alone never proves achievability. -/
theorem completion_count_lower_bound {d q : ℕ} (coordinate : Fin d → Fin q)
    (hcoordinate : Function.Injective coordinate) : d ≤ q := by
  simpa using Fintype.card_le_of_injective coordinate hcoordinate

/-! ## Constructive lag completion -/

/-- Sensitivity matrix of selected lagged covariance summaries.  Row `i` is the lag
chosen for statistic `i`; column `j` is deployment coordinate `j`.  Its entries are the
derivatives `∂γ(lag i)/∂h_j` supplied by a named LD, haplotype, ancestry-tract, or
longitudinal model. -/
noncomputable def lagSensitivityMatrix {d : ℕ}
    (lag : Fin d → ℕ) (covarianceDerivative : ℕ → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ covarianceDerivative (lag i) j

/-- Linearized change in the selected lag statistics along a deployment tangent. -/
noncomputable def lagObservationDerivative {d : ℕ}
    (lag : Fin d → ℕ) (covarianceDerivative : ℕ → Fin d → ℝ)
    (tangent : Fin d → ℝ) : Fin d → ℝ :=
  (lagSensitivityMatrix lag covarianceDerivative).mulVec tangent

/-- **Constructive completion criterion.** A set of `d` lagged covariance statistics
locally distinguishes all `d` deployment directions when the model-supplied
sensitivity matrix is nonsingular.  The converse holds by
finite-dimensional linear algebra and is not proved here, so read this as the
sufficient direction the determinant check actually certifies.  This is the actionable form
of lag completion:
candidate lags are accepted by a determinant check, not merely by counting them.

For PGS portability the coordinates can represent, for example, ancestry-tract age,
recombination-scale LD decay, selection-induced long haplotypes, and a phase/location
parameter.  The theorem is model agnostic about those meanings but exact once their
covariance derivatives are supplied. -/
theorem lagObservationDerivative_injective_of_det_ne_zero {d : ℕ}
    (lag : Fin d → ℕ) (covarianceDerivative : ℕ → Fin d → ℝ)
    (hdet : (lagSensitivityMatrix lag covarianceDerivative).det ≠ 0) :
    Function.Injective (lagObservationDerivative lag covarianceDerivative) := by
  intro tangent tangent' heq
  change (lagSensitivityMatrix lag covarianceDerivative).mulVec tangent =
    (lagSensitivityMatrix lag covarianceDerivative).mulVec tangent' at heq
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  change (lagSensitivityMatrix lag covarianceDerivative).mulVec (tangent - tangent') = 0
  rw [Matrix.mulVec_sub, heq, sub_self]

/-- Total order-two information exposed by a completed collection of lag summaries along
one deployment tangent.  `covariance i` is the asymptotic covariance of estimator channel
`i`; `lagObservationDerivative ... tangent` is its response to population change. -/
noncomputable def lagCompletionPermeability {d : ℕ}
    (covariance : Fin d → ℝ) (lag : Fin d → ℕ)
    (covarianceDerivative : ℕ → Fin d → ℝ) (tangent : Fin d → ℝ) : ℝ :=
  diagonalPermeability covariance
    (lagObservationDerivative lag covarianceDerivative tangent)

/-- **Completion and permeability coincide at order two.** With nonzero estimator
covariances and a nonsingular lag-sensitivity matrix, total Gaussian permeability is zero
exactly for the zero deployment tangent.  Consequently every genuine local population
shift is visible to at least one selected lag channel.

This does not turn marginal allele-frequency data into LD data: the selected lagged
statistics explicitly break the order-erasure gauge. -/
theorem lagCompletionPermeability_eq_zero_iff {d : ℕ}
    (covariance : Fin d → ℝ) (lag : Fin d → ℕ)
    (covarianceDerivative : ℕ → Fin d → ℝ) (tangent : Fin d → ℝ)
    (hcovariance : ∀ i, covariance i ≠ 0)
    (hdet : (lagSensitivityMatrix lag covarianceDerivative).det ≠ 0) :
    lagCompletionPermeability covariance lag covarianceDerivative tangent = 0 ↔
      tangent = 0 := by
  unfold lagCompletionPermeability
  rw [diagonalPermeability_eq_zero_iff _ _ hcovariance]
  constructor
  · intro hzero
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    simpa [lagObservationDerivative] using hzero i
  · intro hzero
    subst tangent
    simp [lagObservationDerivative]

/-! ### Geometric LD/tract-decay witness -/

/-- The first two lags, used as a concrete two-channel completion. -/
def firstTwoLags (i : Fin 2) : ℕ := i.val

/-- Parameter derivatives of the geometric covariance profile `γ(k) = A ρ^k`.
Coordinate zero is the covariance amplitude `A`; coordinate one is the persistence `ρ`.
For an LD-decay or ancestry-tract model, statistical admissibility additionally requires
the model's usual positivity and stationarity conditions; the derivative identity itself
is algebraic. -/
noncomputable def geometricLagCovarianceDerivative
    (amplitude persistence : ℝ) (k : ℕ) : Fin 2 → ℝ :=
  ![persistence ^ k,
    amplitude * (k : ℝ) * persistence ^ (k - 1)]

/-- The lag-zero/lag-one sensitivity determinant for `γ(k)=Aρ^k` is exactly `A`.
Lag zero measures amplitude; once that is known, lag one separates persistence. -/
theorem firstTwoLags_geometric_sensitivity_det
    (amplitude persistence : ℝ) :
    (lagSensitivityMatrix firstTwoLags
      (geometricLagCovarianceDerivative amplitude persistence)).det = amplitude := by
  rw [Matrix.det_fin_two]
  simp [lagSensitivityMatrix, firstTwoLags, geometricLagCovarianceDerivative]

/-- **Two-statistic completion for geometric dependence.** At nonzero covariance
amplitude, retaining lag zero and lag one locally identifies both amplitude and
persistence.  In applications these are the leading strength and decay-scale coordinates
of LD, IBD sharing, or ancestry-tract persistence. -/
theorem firstTwoLags_injective_of_amplitude_ne_zero
    (amplitude persistence : ℝ) (hamplitude : amplitude ≠ 0) :
    Function.Injective
      (lagObservationDerivative firstTwoLags
        (geometricLagCovarianceDerivative amplitude persistence)) := by
  apply lagObservationDerivative_injective_of_det_ne_zero
  rw [firstTwoLags_geometric_sensitivity_det]
  exact hamplitude

/-! ## First-order walls are not absolute walls -/

/-- A channel can have zero first derivative at the base point while changing at every
nonzero nearby parameter. -/
noncomputable def quadraticChannel (θ : ℝ) : ℝ := θ ^ 2

/-- **The channel's failure of additivity is exactly the cross term.** First-order blindness at
zero is shared by every even channel; this identity is not, and it is what a quartic body breaks. -/
theorem quadraticChannel_add (a b : ℝ) :
    quadraticChannel (a + b) = quadraticChannel a + 2 * a * b + quadraticChannel b := by
  unfold quadraticChannel
  ring

/-- The quadratic channel is first-order blind at zero. -/
theorem quadraticChannel_deriv_zero : deriv quadraticChannel 0 = 0 := by
  unfold quadraticChannel
  have hderiv : deriv (fun x : ℝ ↦ x ^ 2) 0 =
      2 * (0 : ℝ) ^ (2 - 1) * deriv (fun x : ℝ ↦ x) 0 := by
    exact deriv_pow (n := 2) differentiableAt_id
  rw [hderiv]
  norm_num

/-- But that local flatness is not absolute non-identifiability. -/
theorem quadraticChannel_visible_away_from_zero {θ : ℝ} (hθ : θ ≠ 0) :
    quadraticChannel θ ≠ quadraticChannel 0 := by
  simp [quadraticChannel, pow_ne_zero _ hθ]

end Descent.Spectral
