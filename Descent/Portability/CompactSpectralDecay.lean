/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompactSpectralIdentification
import Mathlib.Topology.Order.MonotoneConvergence

assert_below Descent.Decision Descent.Program

/-!
Compactness forces the constructed singular values and optimal finite-query
errors to vanish. No quantitative biological decay rate is assumed or asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CompactSpectralDecay

open scoped Topology
open Filter CompactSingularSequence CompactSpectralIdentification AdaptiveLinearMeasurements

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Distinct leading directions have orthogonal images under the original target. -/
theorem images_orthogonal (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (i j : ℕ) (hij : i ≠ j) :
    inner ℝ (L (direction L hc i)) (L (direction L hc j)) = 0 := by
  rw [original_cross]
  have ho : inner ℝ (direction L hc i) (direction L hc j) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [real_inner_comm]
      exact directions_orthogonal L hc i j h
    · exact directions_orthogonal L hc j i h
  rw [ho, mul_zero]

/-- Compactness of the actual target, rather than an assumed singular expansion,
forces its decreasing singular scales to converge to zero. -/
theorem singularValue_tendsto_zero (L : E →L[ℝ] F) (hc : IsCompactOperator L) :
    Tendsto (singularValue L hc) atTop (𝓝 0) := by
  obtain ⟨K, hK, himage⟩ :=
    (show IsCompactOperator L.toLinearMap from hc).image_closedBall_subset_compact 1
  obtain ⟨w, _, φ, hφ, hw⟩ := hK.tendsto_subseq
    (x := fun n ↦ L (direction L hc n)) (fun n ↦
      himage ⟨direction L hc n, by simpa using (direction_spec L hc n).1, rfl⟩)
  have hinner : Tendsto (fun n ↦ inner ℝ (L (direction L hc (φ n)))
      (L (direction L hc (φ (n + 1))))) atTop (𝓝 (inner ℝ w w)) :=
    hw.inner (hw.comp (tendsto_add_atTop_nat 1))
  have hz (n : ℕ) : inner ℝ (L (direction L hc (φ n)))
      (L (direction L hc (φ (n + 1)))) = 0 :=
    images_orthogonal L hc _ _ (ne_of_lt (hφ (Nat.lt_succ_self n)))
  simp only [hz] at hinner
  have hww : inner ℝ w w = 0 := tendsto_nhds_unique hinner tendsto_const_nhds
  have hwzero : w = 0 := by
    rw [real_inner_self_eq_norm_sq] at hww
    exact norm_eq_zero.mp (pow_eq_zero hww)
  subst w
  have hnorm := hw.norm
  have hvalues (n : ℕ) : ‖L (direction L hc n)‖ = singularValue L hc n := by
    rw [← direction_image]
    exact (direction_spec L hc n).2.1
  simp only [Function.comp_def, hvalues, norm_zero] at hnorm
  exact (tendsto_iff_tendsto_subseq_of_antitone
    (singularValue_antitone L hc) hφ.tendsto_atTop).mpr hnorm

/-- Optimal worst-case error converges to zero for every fixed residual radius. -/
theorem optimal_risk_tendsto_zero (L : E →L[ℝ] F) (hc : IsCompactOperator L) (radius : ℝ) :
    Tendsto (fun q ↦ radius ^ 2 * singularValue L hc q ^ 2) atTop (𝓝 0) := by
  simpa only [zero_pow two_ne_zero, mul_zero] using
    ((singularValue_tendsto_zero L hc).pow 2).const_mul (radius ^ 2)

/-- Every positive error tolerance has an actual finite-query attaining procedure. -/
theorem finite_queries_for_tolerance (L : E →L[ℝ] F) (hc : IsCompactOperator L)
    (radius ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, ∃ procedure : Procedure E F q, UniformRisk procedure L radius ε := by
  have he := (optimal_risk_tendsto_zero L hc radius).eventually (gt_mem_nhds hε)
  obtain ⟨q, hq⟩ := he.exists
  refine ⟨q, spectralProcedure L hc q, ?_⟩
  intro x hx
  exact (spectralProcedure_risk L hc q radius x hx).trans hq.le

end Descent.Portability.CompactSpectralDecay
