/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmoothedCoordinateLaws

assert_below Descent.Decision Descent.Program

/-!
# Averaging a report over the noise cube

PL Theorem 7.4, the convergence step. Conditioned on an atom of the finitely supported
outcome law, the expected report under the uniformly smoothed law is the average of the
report over a cube of radius `ε` centred at that atom. This module builds that cube law
and the estimate that drives the convergence: if the report stays within `δ` of its value
at the atom throughout the cube, its cube average is within `δ` of that value, and
continuity of the report at the atom supplies the radius.

No dominated convergence is needed on this route, and no null-set argument: the report is
continuous at each atom because its denominator is nonzero there, which is the definedness
condition the finite theorems already carry.

## Scope

What is NOT proved here: the identification of the smoothed product law with the mixture
over atoms of the shifted cube laws, which is what turns the estimate below into the
statement that the expected report converges. The matched moments of the smoothed product
law are `SmoothedCoordinateLaws.smoothedProduct_moment_match`, and the finitely supported
core is `IndependentRadialLaws.independent_radial_obstruction`.

## Empirical status

None. The bodies here are a uniform law on a box and an averaging estimate, which are
claims about a model; what carries an empirical status is a named quantity in a subsystem
module asserting that this algebra computes something measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CubeAverageConvergence

open Foundations SmoothedCoordinateLaws

noncomputable section

/-- The uniform law on one noise coordinate `[-ε, ε]`. -/
def noiseLaw (ε : ℝ) : MeasureTheory.Measure ℝ :=
  (ENNReal.ofReal (1 / (2 * ε))) •
    MeasureTheory.volume.restrict (Set.Icc (-ε) ε)

/-- The noise law is finite, hence sigma-finite. -/
instance noiseLaw_isFiniteMeasure {ε : ℝ} :
    MeasureTheory.IsFiniteMeasure (noiseLaw ε) := by
  constructor
  unfold noiseLaw
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The noise law is a probability law. -/
theorem noiseLaw_univ (ε : ℝ) (hε : 0 < ε) : noiseLaw ε Set.univ = 1 := by
  have harg : 1 / (2 * ε) * (ε - -ε) = 1 := by
    have hne : ε ≠ 0 := hε.ne'
    field_simp
  unfold noiseLaw
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), harg,
    ENNReal.ofReal_one]

/-- All of the noise law's mass sits in the window. -/
theorem noiseLaw_Icc (ε : ℝ) (hε : 0 < ε) : noiseLaw ε (Set.Icc (-ε) ε) = 1 := by
  have harg : 1 / (2 * ε) * (ε - -ε) = 1 := by
    have hne : ε ≠ 0 := hε.ne'
    field_simp
  unfold noiseLaw
  rw [MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.restrict_apply_self, Real.volume_Icc, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), harg, ENNReal.ofReal_one]

variable {N : Type*} [Fintype N]

/-- The uniform law on the noise cube `[-ε, ε]^N`. -/
def cubeLaw (N : Type*) [Fintype N] (ε : ℝ) : MeasureTheory.Measure (N → ℝ) :=
  MeasureTheory.Measure.pi fun _ : N ↦ noiseLaw ε

/-- The cube law is a probability law. -/
theorem cubeLaw_univ (ε : ℝ) (hε : 0 < ε) : cubeLaw N ε Set.univ = 1 := by
  unfold cubeLaw
  rw [← Set.pi_univ, MeasureTheory.Measure.pi_pi]
  simp [noiseLaw_univ ε hε]

/-- All of the cube law's mass sits in the cube. -/
theorem cubeLaw_box (ε : ℝ) (hε : 0 < ε) :
    cubeLaw N ε (Set.univ.pi fun _ : N ↦ Set.Icc (-ε) ε) = 1 := by
  unfold cubeLaw
  rw [MeasureTheory.Measure.pi_pi]
  simp [noiseLaw_Icc ε hε]

/-- Almost every noise vector lies in the cube. -/
theorem cubeLaw_ae_mem (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ u ∂(cubeLaw N ε), ∀ i, u i ∈ Set.Icc (-ε) ε := by
  have hset : {u : N → ℝ | ¬ ∀ i, u i ∈ Set.Icc (-ε) ε} =
      (Set.univ.pi fun _ : N ↦ Set.Icc (-ε) ε)ᶜ := by
    ext u
    simp [Set.mem_pi]
  rw [MeasureTheory.ae_iff, hset,
    MeasureTheory.measure_compl (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
      (by rw [cubeLaw_box ε hε]; exact ENNReal.one_ne_top),
    cubeLaw_univ ε hε, cubeLaw_box ε hε, tsub_self]

/-- **Continuity supplies the cube radius.** If `g` is continuous at `a`, then for every
`δ > 0` there is a radius within which `g` stays `δ`-close to `g a`. -/
theorem exists_cube_radius (g : (N → ℝ) → ℝ) (a : N → ℝ) (hg : ContinuousAt g a)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : N → ℝ, (∀ i, u i ∈ Set.Icc (-ρ) ρ) →
      |g (a + u) - g a| ≤ δ := by
  rw [Metric.continuousAt_iff] at hg
  obtain ⟨η, hη, hball⟩ := hg δ hδ
  refine ⟨η / 2, by linarith, fun u hu ↦ ?_⟩
  have hnorm : ‖u‖ ≤ η / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hu i).1, (hu i).2⟩
  have hd : dist (a + u) a < η := by
    rw [dist_eq_norm, add_sub_cancel_left]
    linarith
  have := hball hd
  rw [Real.dist_eq] at this
  linarith

/-- **The cube-average estimate.** If `g` stays within `δ` of `g a` on the cube, its
average over the cube is within `δ` of `g a`. -/
theorem abs_cubeAverage_sub_le (g : (N → ℝ) → ℝ) (a : N → ℝ) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (hclose : ∀ u : N → ℝ, (∀ i, u i ∈ Set.Icc (-ε) ε) → |g (a + u) - g a| ≤ δ)
    (hint : MeasureTheory.Integrable (fun u ↦ g (a + u)) (cubeLaw N ε)) :
    |(∫ u, g (a + u) ∂(cubeLaw N ε)) - g a| ≤ δ := by
  have hprob : MeasureTheory.IsProbabilityMeasure (cubeLaw N ε) :=
    ⟨cubeLaw_univ ε hε⟩
  have hsub : (∫ u, (g (a + u) - g a) ∂(cubeLaw N ε)) =
      (∫ u, g (a + u) ∂(cubeLaw N ε)) - g a := by
    rw [MeasureTheory.integral_sub hint (MeasureTheory.integrable_const _),
      MeasureTheory.integral_const, hprob.measure_univ]
    simp
  have hae : ∀ᵐ u ∂(cubeLaw N ε), ‖g (a + u) - g a‖ ≤ δ := by
    filter_upwards [cubeLaw_ae_mem (N := N) ε hε] with u hu
    rw [Real.norm_eq_abs]
    exact hclose u hu
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const hae
  rw [hsub, hprob.measure_univ] at hbound
  simpa using hbound

end

end Descent.Portability.CubeAverageConvergence
