/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Calibrator

/-!
# Fixed-epoch frequency-spectrum stability

This file formalizes the finite algebra that drives the sharp fixed-epoch inverse modulus for
population histories.  A model with at most `K` epochs is identified from `2K - 3` independent
frequency-spectrum coordinates.  The collision construction is the alternating binomial
finite difference of order `2K - 3`; its Laplace response is exactly a power of that order.

The formal results include:

* the exact sample and spectrum-coordinate counts;
* the inverse Hölder exponent and its concrete values for two, three, and four epochs;
* the exact spectrum-precision and independent-sample multipliers needed to improve history
  error by a prescribed factor;
* the alternating-binomial identity producing an order-`p` collision;
* the first-order-versus-order-`p` scaling relation that makes exponent `1 / p` sharp.

The `K`-epoch restriction is not a convenience. `SpectrumIdentifiability` shows that without a
finite-dimensional sieve there is no exponent to prove: the reciprocal Kingman rate sum
converges, so on any interval there are nonzero smooth histories the spectrum cannot see at any
sample size, and the minimax risk is bounded away from zero rather than converging slowly. The
exponent below describes the sieve, and the sieve is what makes it meaningful.

The analytic Chebyshev-system upper bound and the calendar/coalescent-time bi-Lipschitz theorem
require a developed theory of bounded piecewise-constant histories and are not asserted here.
The algebra below is unconditional and is the load-bearing sharpness mechanism those analytic
steps consume.

The last section records the exact operator boundary that separates this finite-epoch result
from unrestricted smooth histories.  A linear observation identifies a model class exactly
when the class difference set meets its kernel only at zero; with `n` coordinates, every
`(n+1)`-dimensional sieve has a nonzero invisible direction.  Thus finite-sample analyticity
alone cannot replace the finite-complexity hypothesis.
-/

open scoped BigOperators

/-- Number of nonredundant spectrum coordinates needed by a `K`-epoch model. -/
def epochSpectrumCoordinateCount (K : ℕ) : ℕ :=
  2 * K - 3

/-- Smallest lineage sample size supplying `2K - 3` unfolded spectrum entries. -/
def epochLineageSampleSize (K : ℕ) : ℕ :=
  2 * K - 2

/-- The fixed-epoch inverse Hölder exponent. -/
noncomputable def fixedEpochInverseExponent (K : ℕ) : ℝ :=
  (epochSpectrumCoordinateCount K : ℝ)⁻¹

/-- A sample of size `2K - 2` has exactly `2K - 3` nontrivial unfolded spectrum entries. -/
theorem epochLineageSampleSize_sub_one (K : ℕ) (hK : 2 ≤ K) :
    epochLineageSampleSize K - 1 = epochSpectrumCoordinateCount K := by
  unfold epochLineageSampleSize epochSpectrumCoordinateCount
  omega

/-- The collision order is positive for every model with at least two epochs. -/
theorem epochSpectrumCoordinateCount_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < epochSpectrumCoordinateCount K := by
  unfold epochSpectrumCoordinateCount
  omega

/-- Two-epoch inference is Lipschitz. -/
@[simp] theorem fixedEpochInverseExponent_two :
    fixedEpochInverseExponent 2 = 1 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Three epochs already have cube-root stability. -/
@[simp] theorem fixedEpochInverseExponent_three :
    fixedEpochInverseExponent 3 = 1 / 3 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Four epochs have fifth-root stability. -/
@[simp] theorem fixedEpochInverseExponent_four :
    fixedEpochInverseExponent 4 = 1 / 5 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Precision multiplier in the expected spectrum needed to improve history error by `factor`. -/
def spectrumPrecisionMultiplier (K factor : ℕ) : ℕ :=
  factor ^ epochSpectrumCoordinateCount K

/-- Independent-data multiplier under root-sample spectrum error. -/
def independentSampleMultiplier (K factor : ℕ) : ℕ :=
  factor ^ (2 * epochSpectrumCoordinateCount K)

/-- The actionable spectrum-precision table for halving history error. -/
theorem spectrumPrecisionMultiplier_halving_table :
    spectrumPrecisionMultiplier 2 2 = 2 ∧
      spectrumPrecisionMultiplier 3 2 = 8 ∧
      spectrumPrecisionMultiplier 4 2 = 32 ∧
      spectrumPrecisionMultiplier 5 2 = 128 := by
  norm_num [spectrumPrecisionMultiplier, epochSpectrumCoordinateCount]

/-- The corresponding independent-sample table when spectrum error is proportional to
`sampleSize⁻¹ᐟ²`. -/
theorem independentSampleMultiplier_halving_table :
    independentSampleMultiplier 2 2 = 4 ∧
      independentSampleMultiplier 3 2 = 64 ∧
      independentSampleMultiplier 4 2 = 1024 ∧
      independentSampleMultiplier 5 2 = 16384 := by
  norm_num [independentSampleMultiplier, epochSpectrumCoordinateCount]

/-- Statistical exponent inherited from root-sample estimation of the spectrum. -/
noncomputable def fixedEpochSampleRateExponent (K : ℕ) : ℝ :=
  (2 * epochSpectrumCoordinateCount K : ℝ)⁻¹

/-- A five-epoch history has the slow `sampleSize⁻¹ᐟ¹⁴` rate. -/
@[simp] theorem fixedEpochSampleRateExponent_five :
    fixedEpochSampleRateExponent 5 = 1 / 14 := by
  norm_num [fixedEpochSampleRateExponent, epochSpectrumCoordinateCount]

/-! ## The alternating-binomial collision -/

/-- Alternating binomial response evaluated at a geometric attenuation `x`. -/
noncomputable def alternatingBinomialResponse (order : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (order + 1), (-x) ^ j * (order.choose j : ℝ)

/-- **Exact finite-difference identity.**  The order-`p` alternating collision has response
`(1 - x)^p`. -/
theorem alternatingBinomialResponse_eq (order : ℕ) (x : ℝ) :
    alternatingBinomialResponse order x = (1 - x) ^ order := by
  have h := add_pow (-x) 1 order
  simpa [alternatingBinomialResponse, sub_eq_add_neg, add_comm] using h.symm

/-- At zero attenuation the normalized collision is fully visible. -/
@[simp] theorem alternatingBinomialResponse_zero (order : ℕ) :
    alternatingBinomialResponse order 0 = 1 := by
  rw [alternatingBinomialResponse_eq]
  simp

/-- At unit attenuation every positive-order collision is invisible. -/
@[simp] theorem alternatingBinomialResponse_one (order : ℕ) (horder : order ≠ 0) :
    alternatingBinomialResponse order 1 = 0 := by
  rw [alternatingBinomialResponse_eq]
  simp [horder]

/-- Evaluating at `1 - resolution` exposes the exact order of vanishing. -/
theorem alternatingBinomialResponse_one_sub (order : ℕ) (resolution : ℝ) :
    alternatingBinomialResponse order (1 - resolution) = resolution ^ order := by
  rw [alternatingBinomialResponse_eq]
  congr 1
  ring

/-- A normalized pair of collision histories differs at first order in `resolution`. -/
noncomputable def collisionHistoryDistance (scale resolution : ℝ) : ℝ :=
  scale * resolution

/-- Its normalized frequency-spectrum discrepancy is order `order`. -/
noncomputable def collisionSpectrumDiscrepancy
    (order : ℕ) (scale resolution : ℝ) : ℝ :=
  scale ^ order * alternatingBinomialResponse order (1 - resolution)

/-- The frequency-spectrum discrepancy is exactly the `order`-th power of history distance.
This is the algebraic sharpness statement: any inverse modulus with exponent larger than
`1 / order` fails on this collision family as the resolution tends to zero. -/
theorem collisionSpectrumDiscrepancy_eq_distance_pow
    (order : ℕ) (scale resolution : ℝ) :
    collisionSpectrumDiscrepancy order scale resolution =
      collisionHistoryDistance scale resolution ^ order := by
  rw [collisionSpectrumDiscrepancy, alternatingBinomialResponse_one_sub,
    collisionHistoryDistance, mul_pow]

/-- Specialization to the sharp collision order of a `K`-epoch model. -/
theorem fixedEpochCollision_spectrum_eq_history_pow
    (K : ℕ) (scale resolution : ℝ) :
    collisionSpectrumDiscrepancy (epochSpectrumCoordinateCount K) scale resolution =
      collisionHistoryDistance scale resolution ^ epochSpectrumCoordinateCount K :=
  collisionSpectrumDiscrepancy_eq_distance_pow _ _ _

/-- Each additional epoch adds two independent spectrum coordinates to the collision order. -/
theorem epochSpectrumCoordinateCount_succ (K : ℕ) (hK : 2 ≤ K) :
    epochSpectrumCoordinateCount (K + 1) = epochSpectrumCoordinateCount K + 2 := by
  unfold epochSpectrumCoordinateCount
  omega

/-! ## Exact nullspace boundary for unrestricted history classes -/

/-- A model class is identifiable under a linear observation when the observation is injective
on that class. -/
def IdentifiableUnderLinearObservation
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (observation : V →ₗ[ℝ] W) (modelClass : Set V) : Prop :=
  Set.InjOn observation modelClass

/-- **Intrinsic identifiability criterion.**  The data identify a class exactly when no
nonzero difference of two admissible histories belongs to the observation kernel. -/
theorem identifiableUnderLinearObservation_iff_difference_kernel
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (observation : V →ₗ[ℝ] W) (modelClass : Set V) :
    IdentifiableUnderLinearObservation observation modelClass ↔
      ∀ left ∈ modelClass, ∀ right ∈ modelClass,
        left - right ∈ LinearMap.ker observation → left = right := by
  constructor
  · intro hinjective left hleft right hright hkernel
    apply hinjective hleft hright
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hkernel
    exact hkernel
  · intro hkernel left hleft right hright hequal
    apply hkernel left hleft right hright
    rw [LinearMap.mem_ker, map_sub, hequal, sub_self]

/-- **Finite-spectrum nonidentifiability.**  Any linear observation with only `n` spectrum
coordinates has a nonzero null direction on an `(n+1)`-dimensional coefficient sieve.

Taking the coefficients to multiply `e⁻ᵗ, t e⁻ᵗ, …, tⁿ e⁻ᵗ` gives the finite-sample analytic
counterexample: real analyticity does not make an infinite-dimensional history class
identifiable at any fixed lineage sample size. -/
theorem finiteSpectrumObservation_has_nonzero_nullDirection
    (n : ℕ)
    (observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∃ direction : Fin (n + 1) → ℝ,
      direction ≠ 0 ∧ observation direction = 0 := by
  have hdim : Module.finrank ℝ (Fin n → ℝ) < Module.finrank ℝ (Fin (n + 1) → ℝ) := by
    simp
  have hkernel : LinearMap.ker observation ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨direction, hdirectionKernel, hdirectionNonzero⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hkernel
  exact ⟨direction, hdirectionNonzero, LinearMap.mem_ker.mp hdirectionKernel⟩

/-- Adding one observation coordinate and one free coefficient preserves the dimension-based
nullspace obstruction; merely increasing finite sample size never identifies an
infinite-dimensional analytic class. -/
theorem everyFiniteSpectrumSize_has_nonzero_nullDirection :
    ∀ n : ℕ, ∀ observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      ∃ direction : Fin (n + 1) → ℝ,
        direction ≠ 0 ∧ observation direction = 0 :=
  finiteSpectrumObservation_has_nonzero_nullDirection

end Calibrator
