/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ProbabilityTestClosure
import Mathlib.MeasureTheory.Measure.Tight

assert_below Descent.Decision Descent.Program

/-!
Tightness turns local Stone-Weierstrass approximation into convergence of all
bounded continuous probability tests. Gaussian damping bounds approximants
outside the compact set independently of their original global norms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TightAlgebraConvergence

open scoped Topology BoundedContinuousFunction ENNReal
open Filter MeasureTheory IndependentShiftOperator ProbabilityTestClosure

/-- Damping approaches the original test in uniform norm, not just pointwise. -/
theorem damp_tendsto_zero (f : Observable) :
    Tendsto (fun ε : ℝ ↦ damp ε f) (nhds 0) (nhds f) := by
  have hc : Continuous (fun ε : ℝ ↦ damp ε f) :=
    continuous_const.mul (NormedSpace.exp_continuous.comp
      (((continuous_id.smul continuous_const).mul continuous_const).neg))
  simpa only [damp, zero_smul, zero_mul, neg_zero, NormedSpace.exp_zero, mul_one]
    using hc.tendsto 0

/-- A compact approximation of the original tests controls their globally bounded dampings. -/
theorem damp_integral_approx (P : ProbabilityMeasure ℝ) (f g : Observable)
    (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ) {K : Set ℝ} (hK : IsCompact K)
    (hfg : ∀ x ∈ K, |g x - f x| < δ)
    (htail : (P : Measure ℝ).real Kᶜ ≤ η) :
    dist (∫ x, damp ε f x ∂(P : Measure ℝ)) (∫ x, damp ε g x ∂(P : Measure ℝ)) ≤
      δ + 2 * η * (Real.sqrt ε)⁻¹ := by
  have hmeas := hK.isClosed.measurableSet
  have hf := norm_integral_sub_setIntegral_le (μ := (P : Measure ℝ))
    (Filter.Eventually.of_forall (fun x ↦ show ‖Real.mulExpNegMulSq ε (f x)‖ ≤
      (Real.sqrt ε)⁻¹ from Real.abs_mulExpNegMulSq_le hε)) hmeas
    (integrable_mulExpNegMulSq_comp f.toContinuousMap hε)
  have hg := norm_integral_sub_setIntegral_le (μ := (P : Measure ℝ))
    (Filter.Eventually.of_forall (fun x ↦ show ‖Real.mulExpNegMulSq ε (g x)‖ ≤
      (Real.sqrt ε)⁻¹ from Real.abs_mulExpNegMulSq_le hε)) hmeas
    (integrable_mulExpNegMulSq_comp g.toContinuousMap hε)
  have hmid := abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure
    (P := (P : Measure ℝ)) hK hmeas f.toContinuousMap g.toContinuousMap hε hfg
  change |∫ x in K, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ) -
      ∫ x in K, Real.mulExpNegMulSq ε (f x) ∂(P : Measure ℝ)| ≤
    δ * (P : Measure ℝ).real K at hmid
  have hm : δ * (P : Measure ℝ).real K ≤ δ :=
    mul_le_of_le_one_right hδ measureReal_le_one
  have ht : (P : Measure ℝ).real Kᶜ * (Real.sqrt ε)⁻¹ ≤ η * (Real.sqrt ε)⁻¹ :=
    mul_le_mul_of_nonneg_right htail (by positivity)
  simp only [Real.norm_eq_abs] at hf hg
  simp only [damp_apply, Real.dist_eq]
  have ht1 := abs_sub_le (∫ x, Real.mulExpNegMulSq ε (f x) ∂(P : Measure ℝ))
    (∫ x in K, Real.mulExpNegMulSq ε (f x) ∂(P : Measure ℝ))
    (∫ x, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))
  have ht2 := abs_sub_le (∫ x in K, Real.mulExpNegMulSq ε (f x) ∂(P : Measure ℝ))
    (∫ x in K, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))
    (∫ x, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))
  rw [abs_sub_comm (∫ x in K, Real.mulExpNegMulSq ε (f x) ∂(P : Measure ℝ))
    (∫ x in K, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))] at ht2
  rw [abs_sub_comm (∫ x in K, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))
    (∫ x, Real.mulExpNegMulSq ε (g x) ∂(P : Measure ℝ))] at ht2
  linarith

/-- Approximation uniformly over all sampled measures and the candidate limit
transfers convergence. -/
theorem integral_tendsto_of_approximation (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (f : Observable)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : Observable,
      Tendsto (fun n ↦ ∫ x, g x ∂(μ n : Measure ℝ)) atTop
        (nhds (∫ x, g x ∂(ν : Measure ℝ))) ∧
      (∀ n, dist (∫ x, f x ∂(μ n : Measure ℝ)) (∫ x, g x ∂(μ n : Measure ℝ)) ≤ ε) ∧
      dist (∫ x, f x ∂(ν : Measure ℝ)) (∫ x, g x ∂(ν : Measure ℝ)) ≤ ε) :
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ)) atTop
      (nhds (∫ x, f x ∂(ν : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hg, hμ, hν⟩ := happrox (ε / 3) (by positivity)
  filter_upwards [(Metric.tendsto_nhds.mp hg) (ε / 3) (by positivity)] with n hn
  have ht1 := dist_triangle (∫ x, f x ∂(μ n : Measure ℝ))
    (∫ x, g x ∂(μ n : Measure ℝ)) (∫ x, f x ∂(ν : Measure ℝ))
  have ht2 := dist_triangle (∫ x, g x ∂(μ n : Measure ℝ))
    (∫ x, g x ∂(ν : Measure ℝ)) (∫ x, f x ∂(ν : Measure ℝ))
  rw [dist_comm (∫ x, g x ∂(ν : Measure ℝ)) (∫ x, f x ∂(ν : Measure ℝ))] at ht2
  linarith [hμ n]

/-- Tightness and convergence on a separating algebra determine actual weak convergence. -/
theorem weak_convergence_of_tight_algebra (μ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ) (A : Subalgebra ℝ Observable)
    (hsep : (A.map (BoundedContinuousFunction.toContinuousMapₐ ℝ)).SeparatesPoints)
    (htight : IsTightMeasureSet
      (Set.insert (ν : Measure ℝ) (Set.range (fun n ↦ (μ n : Measure ℝ)))))
    (hA : ∀ f ∈ A, Tendsto (fun n ↦ ∫ x, f x ∂(μ n : Measure ℝ))
      atTop (nhds (∫ x, f x ∂(ν : Measure ℝ)))) :
    Tendsto μ atTop (nhds ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply integral_tendsto_of_approximation μ ν f
  intro ε hε
  have hc : ∀ᶠ ρ : ℝ in nhds 0, dist (damp ρ f) f < ε / 2 :=
    (damp_tendsto_zero f).eventually (Metric.ball_mem_nhds f (by positivity))
  have hc' : ∀ᶠ ρ : ℝ in nhdsWithin 0 (Set.Ioi 0), dist (damp ρ f) f < ε / 2 :=
    hc.filter_mono inf_le_left
  have hp : ∀ᶠ ρ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, hclose⟩ := (hp.and hc').exists
  let η := ε * Real.sqrt ρ / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK, htail⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    htight (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨g', hg', happrox⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hsep f.toContinuousMap hK (show 0 < ε / 4 by positivity)
  obtain ⟨g, hgA, hgg'⟩ := Subalgebra.mem_map.mp hg'
  have hfg : ∀ x ∈ K, |g x - f x| < ε / 4 := by
    intro x hx
    have h := happrox x hx
    rw [← hgg'] at h
    exact h
  refine ⟨damp ρ g, integral_tendsto_of_mem_closure μ ν A hA (damp_mem_closure A ρ hgA), ?_⟩
  have herr : ∀ P : ProbabilityMeasure ℝ,
      (P : Measure ℝ) ∈ Set.insert (ν : Measure ℝ) (Set.range (fun n ↦ (μ n : Measure ℝ))) →
      dist (∫ x, f x ∂(P : Measure ℝ)) (∫ x, damp ρ g x ∂(P : Measure ℝ)) ≤ ε := by
    intro P hP
    have ht : (P : Measure ℝ).real Kᶜ ≤ η :=
      ENNReal.toReal_le_of_le_ofReal hη.le (htail _ hP)
    have hd := damp_integral_approx P f g ρ (ε / 4) η hρ (by positivity) hK hfg ht
    have heq : ε / 4 + 2 * η * (Real.sqrt ρ)⁻¹ = ε / 2 := by
      dsimp [η]
      have hs : Real.sqrt ρ ≠ 0 := by positivity
      field_simp
      ring
    rw [heq] at hd
    have hn := integral_dist_le P f (damp ρ f)
    rw [dist_comm f (damp ρ f)] at hn
    have hh := dist_triangle (∫ x, f x ∂(P : Measure ℝ))
      (∫ x, damp ρ f x ∂(P : Measure ℝ)) (∫ x, damp ρ g x ∂(P : Measure ℝ))
    linarith
  exact ⟨fun n ↦ herr (μ n) (Set.mem_insert_of_mem _ ⟨n, rfl⟩),
    herr ν (Set.mem_insert _ _)⟩

end Descent.Portability.TightAlgebraConvergence
