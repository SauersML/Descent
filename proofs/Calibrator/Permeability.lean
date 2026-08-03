import Mathlib

namespace Calibrator

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
-/

open scoped BigOperators

/-- One-dimensional Gaussian covariance permeability. -/
noncomputable def scalarPermeability (covariance covarianceDerivative : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (covarianceDerivative / covariance) ^ 2

/-! ## The named Gaussian covariance experiment -/

/-- Variance of a centered square from its second and fourth raw moments. -/
noncomputable def centeredSquareVarianceFromMoments
    (secondMoment fourthMoment : ℝ) : ℝ :=
  fourthMoment - secondMoment ^ 2

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

/-- A common tagging or assay attenuation acts on every independent completion channel
by the same inverse-square law.  This is useful for panels in which the same call-rate,
imputation-quality, or conditional-support factor multiplies every covariance response.

The premise is deliberately algebraic: a biological model must still prove that its
channel derivatives are multiplied by `η`. -/
theorem diagonalPermeability_derivative_scale {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ) (η : ℝ) :
    diagonalPermeability covariance (fun i => η * covarianceDerivative i) =
      η ^ 2 * diagonalPermeability covariance covarianceDerivative := by
  unfold diagonalPermeability
  simp_rw [scalarPermeability_derivative_scale]
  rw [Finset.mul_sum]

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
  unfold covarianceTangentEstimatorVarianceFromMoments
    gaussianCovarianceTangentEstimatorVariance centeredSquareVarianceFromMoments
  ring

/-- The named Gaussian tangent-estimator variance is positive for a positive replicate
budget, positive covariance, and a nonzero covariance response. -/
theorem gaussianCovarianceTangentEstimatorVariance_pos
    (m covariance covarianceDerivative : ℝ)
    (hm : 0 < m) (hcovariance : 0 < covariance)
    (hderivative : covarianceDerivative ≠ 0) :
    0 < gaussianCovarianceTangentEstimatorVariance
      m covariance covarianceDerivative := by
  unfold gaussianCovarianceTangentEstimatorVariance
    covarianceTangentEstimatorVarianceFromMoments
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
  unfold totalGaussianInformation scalarPermeability
    gaussianCovarianceTangentEstimatorVariance
    covarianceTangentEstimatorVarianceFromMoments centeredSquareVarianceFromMoments
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
        (fun j _ => scalarPermeability_nonneg (covariance j) (covarianceDerivative j))
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
  fun i j => covarianceDerivative (lag i) j

/-- Linearized change in the selected lag statistics along a deployment tangent. -/
noncomputable def lagObservationDerivative {d : ℕ}
    (lag : Fin d → ℕ) (covarianceDerivative : ℕ → Fin d → ℝ)
    (tangent : Fin d → ℝ) : Fin d → ℝ :=
  (lagSensitivityMatrix lag covarianceDerivative).mulVec tangent

/-- **Constructive completion criterion.** A set of `d` lagged covariance statistics
locally distinguishes all `d` deployment directions exactly when the model-supplied
sensitivity matrix is nonsingular.  This is the actionable form of lag completion:
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
theorem firstTwoLags_complete_geometric_dependence
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

/-- The quadratic channel is first-order blind at zero. -/
theorem quadraticChannel_deriv_zero : deriv quadraticChannel 0 = 0 := by
  unfold quadraticChannel
  have hderiv : deriv (fun x : ℝ => x ^ 2) 0 =
      2 * (0 : ℝ) ^ (2 - 1) * deriv (fun x : ℝ => x) 0 := by
    exact deriv_pow (n := 2) differentiableAt_id
  rw [hderiv]
  norm_num

/-- But that local flatness is not absolute non-identifiability. -/
theorem quadraticChannel_visible_away_from_zero {θ : ℝ} (hθ : θ ≠ 0) :
    quadraticChannel θ ≠ quadraticChannel 0 := by
  simp [quadraticChannel, pow_ne_zero _ hθ]

end Calibrator
