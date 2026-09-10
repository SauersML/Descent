/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianCovarianceSeparation
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Covariance

assert_below Descent.Decision Descent.Program

/-!
Centered Gaussian panels with their actual covariance matrix. Finite coordinate
relabeling is the unordered observation; singular covariance is permitted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianPanelLaw

open MeasureTheory ProbabilityTheory GaussianCovarianceSeparation BoundedContinuousFunction
open scoped BigOperators

variable {D : Type*} [Fintype D]

noncomputable def projection (v : D → ℝ) : (D → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj i

theorem projection_apply (v x : D → ℝ) : projection v x = ∑ i, v i * x i := by
  simp [projection]

noncomputable def covariance (μ : Measure (D → ℝ)) : SymmetricCovariance D :=
  ⟨fun i j ↦ ProbabilityTheory.covariance (fun x : D → ℝ ↦ x i) (fun x ↦ x j) μ,
    fun i j ↦ covariance_comm (fun x : D → ℝ ↦ x i) (fun x : D → ℝ ↦ x j)⟩

def Centered (μ : Measure (D → ℝ)) : Prop := ∀ i, (∫ x, x i ∂μ) = 0

theorem coordinate_memLp (μ : Measure (D → ℝ)) [IsGaussian μ] (i : D) :
    MemLp (fun x : D → ℝ ↦ x i) 2 μ :=
  IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by simp)

theorem projection_mean (μ : Measure (D → ℝ)) [IsGaussian μ] (hμ : Centered μ) (v : D → ℝ) :
    (∫ x, projection v x ∂μ) = 0 := by
  have hm (i : D) : (∫ x, x i ∂μ) = 0 := hμ i
  simp only [projection_apply]
  rw [integral_finset_sum]
  · simp only [integral_const_mul, hm, mul_zero, Finset.sum_const_zero]
  · intro i _
    exact (IsGaussian.integrable_dual μ (ContinuousLinearMap.proj i)).const_mul (v i)

theorem projection_variance (μ : Measure (D → ℝ)) [IsGaussian μ] (v : D → ℝ) :
    ProbabilityTheory.variance (projection v) μ = quadraticValue (covariance μ).val v := by
  rw [← covariance_self (by fun_prop : AEMeasurable (projection v) μ)]
  have hp : (projection v : (D → ℝ) → ℝ) = fun x ↦ ∑ i, v i * x i :=
    funext (projection_apply v)
  rw [hp, covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_left, covariance_mul_right, quadraticValue, covariance]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact fun i ↦ (coordinate_memLp μ i).const_mul (v i)
  · exact fun i ↦ (coordinate_memLp μ i).const_mul (v i)

theorem gaussian_characteristic (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) :
    charFunDual μ (projection v) = (gaussianFourier (covariance μ).val v : ℂ) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, projection_mean μ hμ,
    projection_variance]
  simp [gaussianFourier, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg]
  congr 1
  ring

noncomputable def relabel (π : Equiv.Perm D) : (D → ℝ) →L[ℝ] (D → ℝ) :=
  Pi.compRightL ℝ (fun _ : D ↦ ℝ) π

omit [Fintype D] in
@[simp] theorem relabel_apply (π : Equiv.Perm D) (x : D → ℝ) (i : D) :
    relabel π x i = x (π i) := rfl

theorem centered_relabel (μ : Measure (D → ℝ)) (hμ : Centered μ) (π : Equiv.Perm D) :
    Centered (μ.map (relabel π)) := by
  intro i
  rw [integral_map (relabel π).measurable.aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable]
  exact hμ (π i)

theorem covariance_relabel (μ : Measure (D → ℝ)) (π : Equiv.Perm D) :
    covariance (μ.map (relabel π)) = permuteCovariance (covariance μ) π := by
  apply Subtype.ext
  ext i j
  exact covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (relabel π).measurable.aemeasurable

def panelSetoid (D : Type*) : Setoid (D → ℝ) where
  r x y := ∃ π : Equiv.Perm D, (fun i ↦ x (π i)) = y
  iseqv := {
    refl := fun x ↦ ⟨1, rfl⟩
    symm := by
      rintro x y ⟨π, rfl⟩
      exact ⟨π.symm, by ext i; simp⟩
    trans := by
      rintro x y z ⟨π, rfl⟩ ⟨ρ, rfl⟩
      exact ⟨π * ρ, rfl⟩ }

abbrev Bag (D : Type*) := Quotient (panelSetoid D)

def bag (x : D → ℝ) : Bag D := Quotient.mk _ x

omit [Fintype D] in
theorem bag_measurable : Measurable (bag : (D → ℝ) → Bag D) := measurable_quotient_mk''

omit [Fintype D] in
theorem bag_relabel (π : Equiv.Perm D) (x : D → ℝ) : bag (relabel π x) = bag x := by
  symm
  apply Quotient.sound
  exact ⟨π, rfl⟩

noncomputable def symmetricPhase (v x : D → ℝ) : ℂ := by
  classical
  exact ∑ π : Equiv.Perm D, probCharDual (projection v) (relabel π x)

theorem symmetricPhase_continuous (v : D → ℝ) : Continuous (symmetricPhase v) := by
  classical
  apply continuous_finset_sum
  intro π _
  exact (probCharDual (projection v)).continuous.comp (relabel π).continuous

theorem symmetricPhase_relabel (v x : D → ℝ) (ρ : Equiv.Perm D) :
    symmetricPhase v (relabel ρ x) = symmetricPhase v x := by
  classical
  change (∑ π : Equiv.Perm D, probCharDual (projection v) (relabel (ρ * π) x)) = _
  exact Equiv.sum_comp (Equiv.mulLeft ρ)
    (fun π : Equiv.Perm D ↦ probCharDual (projection v) (relabel π x))

noncomputable def bagPhase (v : D → ℝ) : Bag D → ℂ :=
  Quotient.lift (symmetricPhase v) (by
    rintro x y ⟨π, rfl⟩
    exact (symmetricPhase_relabel v x π).symm)

theorem bagPhase_measurable (v : D → ℝ) : Measurable (bagPhase v) :=
  measurable_from_quotient.mpr (symmetricPhase_continuous v).measurable

theorem symmetricPhase_integral (μ : Measure (D → ℝ)) [IsGaussian μ]
    (hμ : Centered μ) (v : D → ℝ) :
    (∫ x, symmetricPhase v x ∂μ) = (orbitFourier (covariance μ) v : ℂ) := by
  classical
  unfold symmetricPhase
  rw [integral_finset_sum]
  · simp only [orbitFourier, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro π _
    have hh := gaussian_characteristic (μ.map (relabel π)) (centered_relabel μ hμ π) v
    rw [charFunDual_apply, integral_map (by fun_prop) (by fun_prop), covariance_relabel] at hh
    exact hh
  · intro π _
    exact (probCharDual ((projection v).comp (relabel π))).integrable μ

theorem bag_law_identifies_covariance_orbit (μ ν : Measure (D → ℝ))
    [IsGaussian μ] [IsGaussian ν] (hμ : Centered μ) (hν : Centered ν)
    (hbag : μ.map bag = ν.map bag) :
    ∃ π : Equiv.Perm D, permuteCovariance (covariance μ) π = covariance ν := by
  apply (orbitFourier_eq_iff _ _).mp
  funext v
  have hh := congrArg (fun law ↦ ∫ b, bagPhase v b ∂law) hbag
  dsimp only at hh
  rw [integral_map bag_measurable.aemeasurable (bagPhase_measurable v).aestronglyMeasurable,
    integral_map bag_measurable.aemeasurable (bagPhase_measurable v).aestronglyMeasurable] at hh
  change (∫ x, symmetricPhase v x ∂μ) = ∫ x, symmetricPhase v x ∂ν at hh
  rw [symmetricPhase_integral μ hμ, symmetricPhase_integral ν hν] at hh
  exact Complex.ofReal_injective hh

theorem projection_surjective : Function.Surjective (projection : (D → ℝ) → (D → ℝ) →L[ℝ] ℝ) := by
  classical
  intro L
  refine ⟨fun i ↦ L (Pi.single i 1), ?_⟩
  ext x
  rw [projection_apply, ← ContinuousLinearMap.sum_comp_single ℝ (fun _ : D ↦ ℝ) L x]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (x i) • (Pi.single i (1 : ℝ) : D → ℝ) = (Pi.single i (x i) : D → ℝ) := by
    ext j
    by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  calc
    L (Pi.single i 1) * x i = x i * L (Pi.single i 1) := mul_comm _ _
    _ = L ((x i) • (Pi.single i (1 : ℝ) : D → ℝ)) := by rw [map_smul]; rfl
    _ = L.comp (ContinuousLinearMap.single ℝ (fun _ : D ↦ ℝ) i) (x i) := by rw [hs]; rfl

theorem centered_gaussian_eq_of_covariance_eq (μ ν : Measure (D → ℝ))
    [IsGaussian μ] [IsGaussian ν] (hμ : Centered μ) (hν : Centered ν)
    (hcov : covariance μ = covariance ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  obtain ⟨v, rfl⟩ := projection_surjective L
  rw [gaussian_characteristic μ hμ, gaussian_characteristic ν hν, hcov]

/-- The complete unordered-panel law identifies exactly the coordinate
permutation orbit of the actual covariance, including singular Gaussian laws. -/
theorem bag_law_eq_iff (μ ν : Measure (D → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hμ : Centered μ) (hν : Centered ν) :
    μ.map bag = ν.map bag ↔
      ∃ π : Equiv.Perm D, permuteCovariance (covariance μ) π = covariance ν := by
  constructor
  · exact bag_law_identifies_covariance_orbit μ ν hμ hν
  · rintro ⟨π, hπ⟩
    have he : μ.map (relabel π) = ν := centered_gaussian_eq_of_covariance_eq _ _
      (centered_relabel μ hμ π) hν ((covariance_relabel μ π).trans hπ)
    rw [← he, Measure.map_map bag_measurable (relabel π).measurable]
    congr 1
    funext x
    exact (bag_relabel π x).symm

end Descent.Portability.GaussianPanelLaw
