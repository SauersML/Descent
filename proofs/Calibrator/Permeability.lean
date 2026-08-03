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

No CLT-to-LAN transfer, Edgeworth hierarchy, universal support-floor model, or minimax
constant is asserted here. Those require a named statistical experiment and uniform
regularity.
-/

open scoped BigOperators

/-- One-dimensional Gaussian covariance permeability. -/
noncomputable def scalarPermeability (covariance covarianceDerivative : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (covarianceDerivative / covariance) ^ 2

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
  lagSensitivityMatrix lag covarianceDerivative *ᵥ tangent

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
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  change lagSensitivityMatrix lag covarianceDerivative *ᵥ (tangent - tangent') = 0
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
    exact hzero i
  · intro hzero
    subst tangent
    simp [lagObservationDerivative]

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
