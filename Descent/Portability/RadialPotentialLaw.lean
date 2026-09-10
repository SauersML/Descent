/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactParameterIntegralLaw
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
An explicit radial potential for a continuously differentiable finite-dimensional
field. Symmetry of the derivative is needed only on the segment from the anchor
to the evaluation point. Differentiation under the integral is justified by
compactness, and the potential's derivative is evaluated by the fundamental theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RadialPotentialLaw

open MeasureTheory Set CompactParameterIntegralLaw

variable {D : Type*} [Fintype D] [DecidableEq D]

def basis (j : D) : D → ℝ := Pi.single j 1

noncomputable def segment (a p : D → ℝ) (t : ℝ) : D → ℝ := a + t • (p - a)

noncomputable def radialDensity (B : D → (D → ℝ) → ℝ) (a p : D → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (p i - a i) * B i (segment a p t)

/-- Twice the radial line integral, matching the diploid derivative convention ∂F=2b. -/
noncomputable def potential (B : D → (D → ℝ) → ℝ) (a p : D → ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, radialDensity B a p t

/-- Coordinate-line derivative, including its exact basis vector. -/
theorem update_hasDerivAt (p : D → ℝ) (j : D) (x : ℝ) :
    HasDerivAt (fun u ↦ Function.update p j u) (basis j) x := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa [basis] using hasDerivAt_id x
  · simpa [basis, Function.update_of_ne hij, Pi.single_eq_of_ne hij] using
      hasDerivAt_const x (p i)

/-- Linear functionals are exactly the sum of their coordinate actions. -/
theorem linear_coordinates (L : (D → ℝ) →L[ℝ] ℝ) (p : D → ℝ) :
    L p = ∑ i, p i * L (basis i) := by
  have hp : p = ∑ i, p i • basis i := by
    funext j
    simp [basis, Finset.sum_apply, Pi.single_apply]
  calc
    L p = L (∑ i, p i • basis i) := congrArg L hp
    _ = _ := by simp

noncomputable def coordinateDerivative (B : D → (D → ℝ) → ℝ)
    (a p : D → ℝ) (j : D) (x t : ℝ) : ℝ :=
  let u := Function.update p j x
  ∑ i, (basis j i * B i (segment a u t) +
    (u i - a i) * fderiv ℝ (B i) (segment a u t) (t • basis j))

/-- The actual derivative of the radial integrand is computed before imposing closedness. -/
theorem radialDensity_coordinate_hasDerivAt (B : D → (D → ℝ) → ℝ)
    (hB : ∀ i, ContDiff ℝ 1 (B i)) (a p : D → ℝ) (j : D) (x t : ℝ) :
    HasDerivAt (fun u ↦ radialDensity B a (Function.update p j u) t)
      (coordinateDerivative B a p j x t) x := by
  have hu := update_hasDerivAt p j x
  have hs : HasDerivAt (fun u ↦ segment a (Function.update p j u) t)
      (t • basis j) x := by
    exact ((hu.sub_const a).const_smul t).const_add a
  unfold radialDensity coordinateDerivative
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hasDerivAt_pi.mp hu i).sub_const (a i)).mul
    (((hB i).differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt x hs)

/-- The integrand is jointly continuous in the coordinate parameter and path parameter. -/
theorem radialDensity_joint_continuous (B : D → (D → ℝ) → ℝ)
    (hB : ∀ i, ContDiff ℝ 1 (B i)) (a p : D → ℝ) (j : D) :
    Continuous (fun xt : ℝ × ℝ ↦ radialDensity B a (Function.update p j xt.1) xt.2) := by
  have hu : Continuous (fun xt : ℝ × ℝ ↦ Function.update p j xt.1) := by
    apply continuous_pi
    intro i
    by_cases hij : i = j
    · subst i
      simpa using (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [Function.update_of_ne hij] using (continuous_const :
        Continuous (fun _ : ℝ × ℝ ↦ p i))
  have hs : Continuous (fun xt : ℝ × ℝ ↦ segment a (Function.update p j xt.1) xt.2) :=
    continuous_const.add (continuous_snd.smul (hu.sub continuous_const))
  unfold radialDensity
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp hu |>.sub continuous_const).mul ((hB i).continuous.comp hs)

/-- Continuous first derivatives supply joint continuity of the computed parameter derivative. -/
theorem coordinateDerivative_joint_continuous (B : D → (D → ℝ) → ℝ)
    (hB : ∀ i, ContDiff ℝ 1 (B i)) (a p : D → ℝ) (j : D) :
    Continuous (fun xt : ℝ × ℝ ↦ coordinateDerivative B a p j xt.1 xt.2) := by
  have hu : Continuous (fun xt : ℝ × ℝ ↦ Function.update p j xt.1) := by
    apply continuous_pi
    intro i
    by_cases hij : i = j
    · subst i
      simpa using (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [Function.update_of_ne hij] using (continuous_const :
        Continuous (fun _ : ℝ × ℝ ↦ p i))
  have hs : Continuous (fun xt : ℝ × ℝ ↦ segment a (Function.update p j xt.1) xt.2) :=
    continuous_const.add (continuous_snd.smul (hu.sub continuous_const))
  unfold coordinateDerivative
  apply continuous_finset_sum
  intro i _
  exact (continuous_const.mul ((hB i).continuous.comp hs)).add
    (((continuous_apply i).comp hu |>.sub continuous_const).mul
      (((hB i).continuous_fderiv (by norm_num)).comp hs |>.clm_apply
        (continuous_snd.smul continuous_const)))

/-- Closedness turns the coordinate derivative into the derivative along the ray. -/
theorem coordinateDerivative_closed (B : D → (D → ℝ) → ℝ)
    (a p : D → ℝ) (j : D) (t : ℝ)
    (hclosed : ∀ i, fderiv ℝ (B i) (segment a p t) (basis j) =
      fderiv ℝ (B j) (segment a p t) (basis i)) :
    coordinateDerivative B a p j (p j) t = B j (segment a p t) +
      t * fderiv ℝ (B j) (segment a p t) (p - a) := by
  unfold coordinateDerivative
  simp only [Function.update_eq_self, Finset.sum_add_distrib, map_smul, smul_eq_mul]
  have hfirst : (∑ i, basis j i * B i (segment a p t)) =
      B j (segment a p t) := by simp [basis, Pi.single_apply]
  rw [hfirst, linear_coordinates]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hclosed i]
  simp only [Pi.sub_apply]
  ring

omit [DecidableEq D] in
/-- The line-integral derivative evaluates exactly at its endpoint by the FTC. -/
theorem radial_endpoint_integral (B : D → (D → ℝ) → ℝ)
    (hB : ∀ i, ContDiff ℝ 1 (B i)) (a p : D → ℝ) (j : D) :
    (∫ t in (0 : ℝ)..1, B j (segment a p t) +
      t * fderiv ℝ (B j) (segment a p t) (p - a)) = B j p := by
  have hs (t : ℝ) : HasDerivAt (segment a p) (p - a) t := by
    simpa only [one_smul] using ((hasDerivAt_id t).smul_const (p - a)).const_add a
  have hd (t : ℝ) : HasDerivAt (fun u ↦ u * B j (segment a p u))
      (B j (segment a p t) + t * fderiv ℝ (B j) (segment a p t) (p - a)) t := by
    simpa only [one_mul] using (hasDerivAt_id t).mul
      (((hB j).differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (hs t))
  have hc : Continuous (segment a p) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hi : IntervalIntegrable (fun t ↦ B j (segment a p t) +
      t * fderiv ℝ (B j) (segment a p t) (p - a)) volume 0 1 := by
    have hcont : Continuous (fun t ↦ B j (segment a p t) +
        t * fderiv ℝ (B j) (segment a p t) (p - a)) :=
      ((hB j).continuous.comp hc).add (continuous_id.mul
        (((hB j).continuous_fderiv (by norm_num)).comp hc |>.clm_apply continuous_const))
    exact hcont.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) hi
  simpa [segment] using h

/-- An explicit potential has derivative twice the field whenever the intervening ray is closed. -/
theorem potential_coordinate_hasDerivAt (B : D → (D → ℝ) → ℝ)
    (hB : ∀ i, ContDiff ℝ 1 (B i)) (a p : D → ℝ) (j : D)
    (hclosed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      fderiv ℝ (B i) (segment a p t) (basis j) =
        fderiv ℝ (B j) (segment a p t) (basis i)) :
    HasDerivAt (fun x ↦ potential B a (Function.update p j x)) (2 * B j p) (p j) := by
  have h := hasDerivAt_interval_integral
    (fun x t ↦ radialDensity B a (Function.update p j x) t)
    (coordinateDerivative B a p j) (radialDensity_joint_continuous B hB a p j)
    (coordinateDerivative_joint_continuous B hB a p j)
    (radialDensity_coordinate_hasDerivAt B hB a p j) (p j)
  have he : (∫ t in (0 : ℝ)..1, coordinateDerivative B a p j (p j) t) = B j p := by
    calc
      _ = ∫ t in (0 : ℝ)..1, B j (segment a p t) +
          t * fderiv ℝ (B j) (segment a p t) (p - a) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply coordinateDerivative_closed B a p j t
        exact hclosed t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
      _ = _ := radial_endpoint_integral B hB a p j
  rw [he] at h
  exact h.const_mul 2

end Descent.Portability.RadialPotentialLaw
