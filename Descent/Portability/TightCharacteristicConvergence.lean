/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TightAlgebraConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

assert_below Descent.Decision Descent.Program

/-!
For tight real probability laws, pointwise convergence of their characteristic
functions to the characteristic function of a candidate probability law implies
weak convergence. Characteristic polynomials supply the separating algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TightCharacteristicConvergence

open scoped Topology BoundedContinuousFunction RealInnerProductSpace
open Filter MeasureTheory Real RCLike BoundedContinuousFunction
open IndependentShiftOperator TightAlgebraConvergence

/-- Pointwise characteristic convergence identifies the weak limit under actual tightness. -/
theorem weak_convergence_of_tight_characteristic (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ)
    (htight : IsTightMeasureSet
      (Set.insert (ν : Measure ℝ) (Set.range (fun n ↦ (μ n : Measure ℝ)))))
    (hchar : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop
      (nhds (charFun (ν : Measure ℝ) t))) :
    Tendsto μ atTop (nhds ν) := by
  let A : StarSubalgebra ℂ (ℝ →ᵇ ℂ) :=
    charPoly (L := bilinFormOfRealInner) continuous_probChar continuous_inner
  have hsep : (A.map (toContinuousMapStarₐ ℂ)).SeparatesPoints :=
    separatesPoints_charPoly continuous_probChar probChar_ne_one continuous_inner
      (fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩)
  have hpoly : ∀ g ∈ A, Tendsto (fun n ↦ ∫ x, g x ∂(μ n : Measure ℝ)) atTop
      (nhds (∫ x, g x ∂(ν : Measure ℝ))) := by
    intro g hg
    obtain ⟨w, hw⟩ := (mem_charPoly g).mp hg
    have hsum (P : ProbabilityMeasure ℝ) :
        ∫ x, g x ∂(P : Measure ℝ) = ∑ t ∈ w.support, w t * charFun (P : Measure ℝ) t := by
      rw [hw]
      change (∫ x, ∑ t ∈ w.support, w t * innerProbChar t x ∂(P : Measure ℝ)) = _
      rw [integral_finset_sum w.support (fun t _ ↦
        (integrable (P : Measure ℝ) (innerProbChar t)).const_mul (w t))]
      apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul, charFun_eq_integral_innerProbChar]
    simp only [hsum]
    exact tendsto_finset_sum _ (fun t _ ↦ tendsto_const_nhds.mul (hchar t))
  let AReal : Subalgebra ℝ Observable := (A.restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuousBounded ℝ lipschitzWith_ofReal)
  have hsepReal : (AReal.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
    rw [RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict]
    exact Subalgebra.SeparatesPoints.rclike_to_real hsep
  apply weak_convergence_of_tight_algebra μ ν AReal hsepReal htight
  intro g hg
  have h := hpoly _ hg
  change Tendsto (fun n ↦ ∫ x, (g x : ℂ) ∂(μ n : Measure ℝ)) atTop
    (nhds (∫ x, (g x : ℂ) ∂(ν : Measure ℝ))) at h
  simpa only [integral_complex_ofReal, Complex.ofReal_re, Function.comp_def] using
    (Complex.continuous_re.tendsto _).comp h

end Descent.Portability.TightCharacteristicConvergence
