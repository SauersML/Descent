/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Finite-sample fixed-bin confidence bounds, conditional on a fixed assignment of
independent bounded outcomes to bins. Sub-Gaussian control is derived from the
actual bounded observations; no concentration inequality is supplied as a hypothesis.
The random-assignment iid experiment is assembled separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FixedBinHoeffdingLaw

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Hoeffding's parameter for the actual centered sum of independent [0,1] observations. -/
theorem centered_sum_subGaussian (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1)
    (s : Finset I) (η : ℝ) (he : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = η) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - η)) ((s.card : ℝ≥0) / 4) μ := by
  have hic : iIndepFun (fun i ω ↦ X i ω - η) μ :=
    hi.comp (fun _ x ↦ x - η) (fun _ ↦ measurable_id.sub_const η)
  have hsub (i : I) (his : i ∈ s) :
      HasSubgaussianMGF (fun ω ↦ X i ω - η) (1 / 4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    rw [he i his] at h
    norm_num at h
    exact h
  have h := HasSubgaussianMGF.sum_of_iIndepFun hic hsub
  convert h using 1
  simp

/-- Two-sided control of the actual sum, including observations with unequal laws but common mean. -/
theorem centered_sum_tail (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1)
    (s : Finset I) (η : ℝ) (he : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = η)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    μ.real {ω | δ < |∑ i ∈ s, (X i ω - η)|} ≤
      2 * Real.exp (-δ ^ 2 / (2 * ((s.card : ℝ) / 4))) := by
  have hsg := centered_sum_subGaussian X hi hm hb s η he
  have hpos := hsg.measure_ge_le hδ
  have hneg := hsg.neg.measure_ge_le hδ
  have hsub : {ω | δ < |∑ i ∈ s, (X i ω - η)|} ⊆
      {ω | δ ≤ ∑ i ∈ s, (X i ω - η)} ∪
        {ω | δ ≤ -(∑ i ∈ s, (X i ω - η))} := by
    intro ω hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr (by linarith)
  have hbound := (measureReal_mono hsub).trans
    (measureReal_union_le (μ := μ) _ _)
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat,
    Pi.neg_apply] at hpos hneg
  linarith

/-- The report's simultaneous confidence radius for a bin containing `count` observations. -/
noncomputable def radius (K count : ℕ) (α : ℝ) : ℝ :=
  Real.sqrt (Real.log (2 * K / α) / (2 * count))

/-- Exact evaluation of the two-sided Hoeffding bound at the stated radius. -/
theorem radius_tail_value (K count : ℕ) (hK : 0 < K) (hc : 0 < count)
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    2 * Real.exp (-((count : ℝ) * radius K count α) ^ 2 /
      (2 * ((count : ℝ) / 4))) = α / K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hcr : (0 : ℝ) < count := by exact_mod_cast hc
  have harg : 0 < 2 * (K : ℝ) / α := div_pos (by positivity) hα.1
  have harg1 : 1 ≤ 2 * (K : ℝ) / α := by
    apply (le_div_iff₀ hα.1).mpr
    have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [hα.2]
  have hlog : 0 ≤ Real.log (2 * (K : ℝ) / α) := Real.log_nonneg harg1
  have hs : (radius K count α) ^ 2 = Real.log (2 * (K : ℝ) / α) / (2 * count) :=
    Real.sq_sqrt (div_nonneg hlog (by positivity))
  have hex : -((count : ℝ) * radius K count α) ^ 2 /
      (2 * ((count : ℝ) / 4)) = -Real.log (2 * (K : ℝ) / α) := by
    rw [mul_pow, hs]
    field_simp
    ring
  rw [hex, Real.exp_neg, Real.exp_log harg]
  field_simp

/-- The empirical mean in a fixed nonempty bin obeys the report's α/K error bound. -/
theorem fixed_subset_confidence (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1)
    (s : Finset I) (hs : 0 < s.card) (η : ℝ)
    (he : ∀ i ∈ s, (∫ ω, X i ω ∂μ) = η)
    (K : ℕ) (hK : 0 < K) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    μ.real {ω | radius K s.card α < |(∑ i ∈ s, X i ω) / s.card - η|} ≤ α / K := by
  have hsr : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hsum (ω : Ω) : (∑ i ∈ s, X i ω) / s.card - η =
      (∑ i ∈ s, (X i ω - η)) / s.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hevent : {ω | radius K s.card α < |(∑ i ∈ s, X i ω) / s.card - η|} =
      {ω | (s.card : ℝ) * radius K s.card α < |∑ i ∈ s, (X i ω - η)|} := by
    ext ω
    rw [hsum, abs_div, abs_of_pos hsr, lt_div_iff₀ hsr, mul_comm]
  rw [hevent]
  have h := centered_sum_tail X hi hm hb s η he
    ((s.card : ℝ) * radius K s.card α) (mul_nonneg hsr.le (Real.sqrt_nonneg _))
  rw [radius_tail_value K s.card hK hs α hα] at h
  exact h

/-- Membership of the frozen bin assignment; its cardinality is the realized bin count. -/
def binRows {K : ℕ} (assignment : I → Fin K) (j : Fin K) : Finset I :=
  Finset.univ.filter (fun i ↦ assignment i = j)

/-- Conditional on all assignments, the probability that any nonempty bin misses is at most α. -/
theorem fixed_assignment_confidence {K : ℕ} (hK : 0 < K)
    (assignment : I → Fin K) (η : Fin K → ℝ)
    (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 1)
    (he : ∀ i, (∫ ω, X i ω ∂μ) = η (assignment i))
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    μ.real {ω | ∃ j : Fin K, 0 < (binRows assignment j).card ∧
      radius K (binRows assignment j).card α <
        |(∑ i ∈ binRows assignment j, X i ω) / (binRows assignment j).card - η j|} ≤ α := by
  let bad := fun j : Fin K ↦ {ω | 0 < (binRows assignment j).card ∧
    radius K (binRows assignment j).card α <
      |(∑ i ∈ binRows assignment j, X i ω) / (binRows assignment j).card - η j|}
  have hj (j : Fin K) : μ.real (bad j) ≤ α / K := by
    by_cases hc : 0 < (binRows assignment j).card
    · have h := fixed_subset_confidence X hi hm hb (binRows assignment j) hc (η j)
        (fun i his ↦ by simpa only [(Finset.mem_filter.mp his).2] using he i) K hK α hα
      simpa only [bad, hc, true_and] using h
    · simp only [bad, hc, false_and, setOf_false, measureReal_empty]
      positivity
  have hevent : {ω | ∃ j : Fin K, 0 < (binRows assignment j).card ∧
      radius K (binRows assignment j).card α <
        |(∑ i ∈ binRows assignment j, X i ω) / (binRows assignment j).card - η j|} =
      ⋃ j, bad j := by ext ω; simp [bad]
  rw [hevent]
  calc
    μ.real (⋃ j, bad j) ≤ ∑ j, μ.real (bad j) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _j : Fin K, α / K := Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = α := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp

end Descent.Portability.FixedBinHoeffdingLaw
