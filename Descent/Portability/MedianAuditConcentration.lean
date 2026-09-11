/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMedianGeometry
import Descent.Portability.IIDAverageLaw
import Mathlib.Probability.Moments.SubGaussian

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 25. An actual independent product
of block experiments amplifies a one-quarter block failure bound into the
stated exponential median bound. Hoeffding's lemma is applied only to the
binary failure indicators, so the underlying outcome statistic may be unbounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MedianAuditConcentration

open MeasureTheory ProbabilityTheory FiniteMedianGeometry
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The binary indicator that a single block statistic misses its target interval. -/
noncomputable def failure (f : Ω → ℝ) (γ r : ℝ) : Ω → ℝ :=
  {ω | r < |f ω - γ|}.indicator (fun _ ↦ 1)

/-- The actual failure indicator is measurable whenever the block statistic is. -/
theorem failure_measurable (f : Ω → ℝ) (γ r : ℝ) (hf : Measurable f) :
    Measurable (failure f γ r) := by
  unfold failure
  exact measurable_const.indicator (measurableSet_lt measurable_const ((hf.sub_const γ).abs))

/-- Its expectation is the actual probability of a failed block. -/
theorem failure_mean (μ : Measure Ω) (f : Ω → ℝ) (γ r : ℝ) (hf : Measurable f) :
    (∫ ω, failure f γ r ω ∂μ) = μ.real {ω | r < |f ω - γ|} := by
  exact integral_indicator_one (measurableSet_lt measurable_const ((hf.sub_const γ).abs))

/-- The indicator lies between zero and one for every outcome. -/
theorem failure_bounded (f : Ω → ℝ) (γ r : ℝ) (ω : Ω) :
    failure f γ r ω ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold failure
  by_cases h : r < |f ω - γ| <;> simp [Set.indicator_apply, h]

/-- Independent block failures have an exponential majority tail. -/
theorem majority_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (γ r : ℝ) (hf : Measurable f) (K : ℕ) (hK : 0 < K)
    (hq : μ.real {ω | r < |f ω - γ|} ≤ 1 / 4) :
    (Measure.pi (fun _ : Fin K ↦ μ)).real
      {z | (K : ℝ) / 2 ≤ ∑ i, failure f γ r (z i)} ≤ Real.exp (-(K : ℝ) / 8) := by
  let q := ∫ ω, failure f γ r ω ∂μ
  have hq' : q ≤ 1 / 4 := by simpa only [q, failure_mean μ f γ r hf] using hq
  let X (i : Fin K) (z : Fin K → Ω) := failure f γ r (z i) - q
  have hm := failure_measurable f γ r hf
  have hi : Integrable (failure f γ r) μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (Filter.Eventually.of_forall (failure_bounded f γ r))
  have hind : iIndepFun X (Measure.pi (fun _ : Fin K ↦ μ)) :=
    iIndepFun_pi (μ := fun _ : Fin K ↦ μ) (X := fun _ ↦ fun ω ↦ failure f γ r ω - q)
      (fun _ ↦ (hm.sub_const q).aemeasurable)
  have hsub (i : Fin K) : HasSubgaussianMGF (X i) (1 / 4)
      (Measure.pi (fun _ : Fin K ↦ μ)) := by
    have hc := hasSubgaussianMGF_of_mem_Icc
      (hm.comp (measurable_pi_apply i)).aemeasurable
      (Filter.Eventually.of_forall (fun z : Fin K → Ω ↦ failure_bounded f γ r (z i)))
    have he : (∫ z : Fin K → Ω, failure f γ r (z i) ∂Measure.pi (fun _ : Fin K ↦ μ)) = q :=
      integral_comp_eval (μ := fun _ : Fin K ↦ μ) hi.aestronglyMeasurable
    rw [he] at hc
    norm_num at hc
    exact hc
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ ↦ (1 / 4 : ℝ≥0)) (fun i _ ↦ hsub i)
    (show 0 ≤ (K : ℝ) / 4 by positivity)
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hexp : Real.exp (-((K : ℝ) / 4) ^ 2 /
      (2 * ∑ _i : Fin K, ((1 / 4 : ℝ≥0) : ℝ))) = Real.exp (-(K : ℝ) / 8) := by
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    field_simp
    ring
  rw [hexp] at ht
  apply (measureReal_mono (show
    {z : Fin K → Ω | (K : ℝ) / 2 ≤ ∑ i, failure f γ r (z i)} ⊆
    {z | (K : ℝ) / 4 ≤ ∑ i, X i z} from ?_)).trans ht
  intro z hz
  change (K : ℝ) / 4 ≤ ∑ i, (failure f γ r (z i) - q)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (K : ℝ) / 2 ≤ ∑ i, failure f γ r (z i) at hz
  nlinarith [mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

/-- The actual independent block median obeys the exponential bound. -/
theorem median_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (γ r : ℝ) (hf : Measurable f) (m : ℕ)
    (hq : μ.real {ω | r < |f ω - γ|} ≤ 1 / 4) :
    (Measure.pi (fun _ : Fin (2 * m + 1) ↦ μ)).real
      {z | r < |median (fun i ↦ f (z i)) - γ|} ≤ Real.exp (-((2 * m + 1 : ℕ) : ℝ) / 8) := by
  apply (measureReal_mono (show
    {z : Fin (2 * m + 1) → Ω | r < |median (fun i ↦ f (z i)) - γ|} ⊆
    {z | ((2 * m + 1 : ℕ) : ℝ) / 2 ≤ ∑ i, failure f γ r (z i)} from ?_)).trans
    (majority_tail μ f γ r hf (2 * m + 1) (by omega) hq)
  intro z hz
  have hh := failure_sum (fun i ↦ f (z i)) γ r hz
  simpa only [failure, Set.indicator_apply, Set.mem_setOf_eq] using hh

end Descent.Portability.MedianAuditConcentration
