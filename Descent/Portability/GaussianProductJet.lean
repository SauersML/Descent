/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianProductDensity
import Descent.Portability.GaussianVarianceJet

assert_below Descent.Decision Descent.Program

/-!
The actual independent Gaussian experiment with variances 1+ελ has explicit
parameter derivatives through third order. Summing the logarithmic coordinate
profiles gives the multivariate derivatives without supplying a Taylor
coefficient or derivative identity as an assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GaussianProductJet

open scoped BigOperators Topology
open Filter GaussianVarianceJet GaussianProductDensity

variable {ι : Type*} [Fintype ι]

/-- The actual density ratio along a fixed diagonal covariance direction. -/
noncomputable def density (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  productRatio (fun i ↦ 1 + ε * l i) x

/-- Log density along the variance perturbation. -/
noncomputable def profile (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, logProfile (1 + ε * l i) (x i)

/-- The first log density derivative, summed over the actual coordinate laws. -/
noncomputable def first (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, l i * logFirst (1 + ε * l i) (x i)

/-- The second log density derivative along the covariance direction. -/
noncomputable def second (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, l i ^ 2 * logSecond (1 + ε * l i) (x i)

/-- The third log density derivative along the covariance direction. -/
noncomputable def third (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, l i ^ 3 * logThird (1 + ε * l i) (x i)

/-- The affine coordinate variance has its exact parameter derivative. -/
theorem variance_hasDerivAt (l ε : ℝ) : HasDerivAt (fun t ↦ 1 + t * l) l ε := by
  simpa only [Pi.add_apply, zero_add, one_mul] using
    (hasDerivAt_const ε 1).add ((hasDerivAt_id ε).mul_const l)

/-- Validity of all coordinate variances holds on a neighborhood of every valid parameter. -/
theorem eventually_positive (l : ι → ℝ) (ε : ℝ) (hε : ∀ i, 0 < 1 + ε * l i) :
    ∀ᶠ t in 𝓝 ε, ∀ i, 0 < 1 + t * l i := by
  apply eventually_all.mpr
  intro i
  exact (variance_hasDerivAt (l i) ε).continuousAt.tendsto.eventually (eventually_gt_nhds (hε i))

/-- Every fixed finite direction gives a valid Gaussian family near zero. -/
theorem eventually_positive_at_zero (l : ι → ℝ) :
    ∀ᶠ ε in 𝓝 0, ∀ i, 0 < 1 + ε * l i :=
  eventually_positive l 0 (by intro i; norm_num)

/-- Exponentiating the actual sum of coordinate log profiles gives the product density. -/
theorem density_eq_exp (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) : density l ε x = Real.exp (profile l ε x) := by
  rw [profile, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact ratio_eq_exp _ _ (hε i)

/-- The first log density derivative follows by differentiating every actual coordinate profile. -/
theorem profile_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ profile l t x) (first l ε x) ε := by
  have hc (i : ι) : HasDerivAt (fun t ↦ logProfile (1 + t * l i) (x i))
      (l i * logFirst (1 + ε * l i) (x i)) ε := by
    have hh := (logProfile_hasDerivAt _ (x i) (hε i).ne').comp ε
      (variance_hasDerivAt (l i) ε)
    simpa only [Function.comp_def, mul_comm] using hh
  unfold profile first
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ ↦ hc i) using 1
  funext t
  simp only [Finset.sum_apply]

/-- The second log derivative follows from the actual coordinate first derivatives. -/
theorem first_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ first l t x) (second l ε x) ε := by
  have hc (i : ι) : HasDerivAt (fun t ↦ l i * logFirst (1 + t * l i) (x i))
      (l i ^ 2 * logSecond (1 + ε * l i) (x i)) ε := by
    have hh := ((logFirst_hasDerivAt _ (x i) (hε i).ne').comp ε
      (variance_hasDerivAt (l i) ε)).const_mul (l i)
    convert hh using 1
    ring
  unfold first second
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ ↦ hc i) using 1
  funext t
  simp only [Finset.sum_apply]

/-- The third log derivative follows from the actual coordinate second derivatives. -/
theorem second_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ second l t x) (third l ε x) ε := by
  have hc (i : ι) : HasDerivAt (fun t ↦ l i ^ 2 * logSecond (1 + t * l i) (x i))
      (l i ^ 3 * logThird (1 + ε * l i) (x i)) ε := by
    have hh := ((logSecond_hasDerivAt _ (x i) (hε i).ne').comp ε
      (variance_hasDerivAt (l i) ε)).const_mul (l i ^ 2)
    convert hh using 1
    ring
  unfold second third
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ ↦ hc i) using 1
  funext t
  simp only [Finset.sum_apply]

/-- The actual multivariate density has the derivative computed from its log profile. -/
theorem density_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ density l t x) (density l ε x * first l ε x) ε := by
  have hh := (profile_hasDerivAt l ε x hε).exp
  have he : (fun t ↦ density l t x) =ᶠ[𝓝 ε] (fun t ↦ Real.exp (profile l t x)) := by
    filter_upwards [eventually_positive l ε hε] with t ht
    exact density_eq_exp l t x ht
  have hd := hh.congr_of_eventuallyEq he
  simpa only [← density_eq_exp l ε x hε, mul_comm] using hd

/-- The exact second density derivative for the full finite Gaussian experiment. -/
theorem density_first_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ density l t x * first l t x)
      (density l ε x * (first l ε x ^ 2 + second l ε x)) ε := by
  have hh := (density_hasDerivAt l ε x hε).mul (first_hasDerivAt l ε x hε)
  convert hh using 1
  ring

/-- The exact third density derivative supplies the quadratic remainder integrand. -/
theorem density_second_hasDerivAt (l : ι → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hε : ∀ i, 0 < 1 + ε * l i) :
    HasDerivAt (fun t ↦ density l t x * (first l t x ^ 2 + second l t x))
      (density l ε x * (first l ε x ^ 3 + 3 * first l ε x * second l ε x + third l ε x)) ε := by
  have hh := (density_hasDerivAt l ε x hε).mul
    (((first_hasDerivAt l ε x hε).pow 2).add (second_hasDerivAt l ε x hε))
  convert hh using 1
  simp only [Pi.add_apply, Pi.pow_apply]
  ring

/-- The reference point gives density ratio one in every dimension. -/
theorem density_zero (l x : ι → ℝ) : density l 0 x = 1 := by
  simp [density, productRatio, ratio_one]

/-- Exact first derivative at the reference point. -/
theorem first_zero (l x : ι → ℝ) :
    first l 0 x = (∑ i, l i * (x i ^ 2 - 1)) / 2 := by
  simp only [first, zero_mul, add_zero, logFirst, inv_one, one_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact second log derivative at the reference point. -/
theorem second_zero (l x : ι → ℝ) :
    second l 0 x = (∑ i, l i ^ 2 * (1 - 2 * x i ^ 2)) / 2 := by
  simp only [second, zero_mul, add_zero, logSecond, inv_one, one_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a trace-free direction the derived density coefficient has the report's spectral form. -/
theorem quadratic_coefficient (l x : ι → ℝ) (hl : ∑ i, l i = 0) :
    (first l 0 x ^ 2 + second l 0 x) / 2 =
      (∑ i, l i ^ 2) / 4 - (∑ i, l i ^ 2 * x i ^ 2) / 2 +
        (∑ i, l i * x i ^ 2) ^ 2 / 8 := by
  rw [first_zero, second_zero]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hl, sub_zero]
  have he : (∑ i, l i ^ 2 * (2 * x i ^ 2)) = 2 * ∑ i, l i ^ 2 * x i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

end Descent.Portability.GaussianProductJet
