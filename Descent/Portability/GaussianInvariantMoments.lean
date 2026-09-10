/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteCovarianceMoments
import Descent.Portability.GaussianPanelLaw
import Descent.Portability.GaussianEvenMoments
import Mathlib.Algebra.MvPolynomial.Degrees

assert_below Descent.Decision Descent.Program

/-!
Finite permutation-invariant polynomial moments identify the covariance orbit
of an actual centered Gaussian measure, with degree bound four times the number
of coordinate permutations minus two. No nonsingularity is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianInvariantMoments

open MeasureTheory ProbabilityTheory GaussianCovarianceSeparation GaussianPanelLaw
open GaussianEvenMoments GaussianHermiteLaw
open scoped BigOperators

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def invariantPower (v : D → ℝ) (k : ℕ) : MvPolynomial D ℝ :=
  ∑ π : Equiv.Perm D, (∑ i, MvPolynomial.C (v i) * MvPolynomial.X (π i)) ^ (2 * k)

theorem invariantPower_eval (v x : D → ℝ) (k : ℕ) :
    MvPolynomial.eval x (invariantPower v k) =
      ∑ π : Equiv.Perm D, (projection v (relabel π x)) ^ (2 * k) := by
  simp [invariantPower, projection_apply]

theorem invariantPower_relabel (v x : D → ℝ) (k : ℕ) (ρ : Equiv.Perm D) :
    MvPolynomial.eval (relabel ρ x) (invariantPower v k) =
      MvPolynomial.eval x (invariantPower v k) := by
  simp only [invariantPower_eval]
  change (∑ π : Equiv.Perm D, (projection v (relabel (ρ * π) x)) ^ (2 * k)) = _
  exact Equiv.sum_comp (Equiv.mulLeft ρ)
    (fun π : Equiv.Perm D ↦ (projection v (relabel π x)) ^ (2 * k))

theorem invariantPower_degree (v : D → ℝ) (k : ℕ) :
    (invariantPower v k).totalDegree ≤ 2 * k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π _
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have hl : (∑ i : D, MvPolynomial.C (v i) * MvPolynomial.X (π i)).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
      MvPolynomial.totalDegree_mul (MvPolynomial.C (v i)) (MvPolynomial.X (π i))
  simpa only [mul_one] using Nat.mul_le_mul_left (2 * k) hl

omit [DecidableEq D] in
theorem projected_power_integrable (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) (n : ℕ) :
    Integrable (fun x ↦ (projection v x) ^ n) μ := by
  have hi := integrable_power (ProbabilityTheory.variance (projection v) μ).toNNReal n
  rw [← projection_mean μ hμ v, ← IsGaussian.map_eq_gaussianReal (projection v)] at hi
  exact (integrable_map_measure (f := projection v) (g := fun x : ℝ ↦ x ^ n)
    (by fun_prop) (by fun_prop)).mp hi

omit [DecidableEq D] in
theorem projected_even_moment (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) (k : ℕ) :
    (∫ x, (projection v x) ^ (2 * k) ∂μ) =
      evenConstant k * quadraticValue (covariance μ).val v ^ k := by
  have hh := even_power_moment (ProbabilityTheory.variance (projection v) μ).toNNReal k
  rw [← projection_mean μ hμ v, ← IsGaussian.map_eq_gaussianReal (projection v)] at hh
  rw [integral_map (by fun_prop) (by fun_prop)] at hh
  rw [Real.coe_toNNReal _ (variance_nonneg _ _), projection_variance] at hh
  exact hh

theorem invariantPower_integrable (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) (k : ℕ) :
    Integrable (fun x ↦ MvPolynomial.eval x (invariantPower v k)) μ := by
  simp only [invariantPower_eval]
  apply integrable_finset_sum
  intro π _
  have hi := projected_power_integrable (μ.map (relabel π)) (centered_relabel μ hμ π) v (2 * k)
  exact (integrable_map_measure (f := relabel π)
    (g := fun x : D → ℝ ↦ (projection v x) ^ (2 * k)) (by fun_prop) (by fun_prop)).mp hi

theorem invariantPower_moment (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) (k : ℕ) :
    (∫ x, MvPolynomial.eval x (invariantPower v k) ∂μ) =
      evenConstant k *
        ∑ π : Equiv.Perm D, quadraticValue (permuteCovariance (covariance μ) π).val v ^ k := by
  simp only [invariantPower_eval]
  rw [integral_finset_sum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro π _
    have hh := projected_even_moment (μ.map (relabel π)) (centered_relabel μ hμ π) v k
    rw [integral_map (by fun_prop) (by fun_prop), covariance_relabel] at hh
    exact hh
  · intro π _
    have hi := projected_power_integrable (μ.map (relabel π)) (centered_relabel μ hμ π) v (2 * k)
    exact (integrable_map_measure (f := relabel π)
      (g := fun x : D → ℝ ↦ (projection v x) ^ (2 * k)) (by fun_prop) (by fun_prop)).mp hi

/-- A finite degree bound on invariant moments suffices to identify the entire
unordered Gaussian panel law. The assumptions refer to actual measure integrals. -/
theorem covariance_orbit_of_invariant_moments (μ ν : Measure (D → ℝ))
    [IsGaussian μ] [IsGaussian ν] (hμ : Centered μ) (hν : Centered ν)
    (hmoment : ∀ p : MvPolynomial D ℝ,
      p.totalDegree ≤ 4 * Fintype.card (Equiv.Perm D) - 2 →
      (∀ (π : Equiv.Perm D) (x : D → ℝ),
        MvPolynomial.eval (relabel π x) p = MvPolynomial.eval x p) →
      (∫ x, MvPolynomial.eval x p ∂μ) = ∫ x, MvPolynomial.eval x p ∂ν) :
    ∃ π : Equiv.Perm D, permuteCovariance (covariance μ) π = covariance ν := by
  apply FiniteCovarianceMoments.orbit_eq_of_variance_moments
  intro v k hk
  have hd : (invariantPower v k).totalDegree ≤ 4 * Fintype.card (Equiv.Perm D) - 2 :=
    (invariantPower_degree v k).trans (by omega)
  have hh := hmoment (invariantPower v k) hd (fun π x ↦ invariantPower_relabel v x k π)
  rw [invariantPower_moment μ hμ, invariantPower_moment ν hν] at hh
  exact mul_left_cancel₀ (ne_of_gt (evenConstant_pos k)) hh

theorem bag_law_of_invariant_moments (μ ν : Measure (D → ℝ))
    [IsGaussian μ] [IsGaussian ν] (hμ : Centered μ) (hν : Centered ν)
    (hmoment : ∀ p : MvPolynomial D ℝ,
      p.totalDegree ≤ 4 * Fintype.card (Equiv.Perm D) - 2 →
      (∀ (π : Equiv.Perm D) (x : D → ℝ),
        MvPolynomial.eval (relabel π x) p = MvPolynomial.eval x p) →
      (∫ x, MvPolynomial.eval x p ∂μ) = ∫ x, MvPolynomial.eval x p ∂ν) :
    μ.map bag = ν.map bag :=
  (bag_law_eq_iff μ ν hμ hν).mpr (covariance_orbit_of_invariant_moments μ ν hμ hν hmoment)

end Descent.Portability.GaussianInvariantMoments
