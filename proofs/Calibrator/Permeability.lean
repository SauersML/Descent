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

No CLT-to-LAN transfer, Edgeworth hierarchy, support-floor scaling, or minimax constant is
asserted here. Those require a named statistical experiment and uniform regularity.
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

/-- Total order-two permeability of finitely many independent scalar estimator channels. -/
noncomputable def diagonalPermeability {ι : Type*} [Fintype ι]
    (covariance covarianceDerivative : ι → ℝ) : ℝ :=
  ∑ i, scalarPermeability (covariance i) (covarianceDerivative i)

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
  rw [hderiv, deriv_id]
  norm_num

/-- But that local flatness is not absolute non-identifiability. -/
theorem quadraticChannel_visible_away_from_zero {θ : ℝ} (hθ : θ ≠ 0) :
    quadraticChannel θ ≠ quadraticChannel 0 := by
  simp [quadraticChannel, pow_ne_zero _ hθ]

end Calibrator
