/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.JointAuditExperiment
import Descent.Portability.BernsteinUpperConfidence

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Corollary 26: the proposed audit cost under
its actual independent Bernoulli selection law. Centering, variance and
bounded increments are computed from the endpoint law. The Bernstein cost
certificate includes deterministic request rates and zero variance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BernoulliBudgetLaw

open MeasureTheory ProbabilityTheory JointAuditExperiment BoundedAuditCompletion
open IndependentContrastLaw BernsteinTailBound
open scoped BigOperators

/-- A centered contribution to proposed labeling cost. -/
noncomputable def centeredCost (p c a : ℝ) : ℝ := c * (a - p)

/-- Centered cost is measurable in the proposed request coin. -/
theorem centered_measurable (p c : ℝ) : Measurable (centeredCost p c) := by
  unfold centeredCost
  fun_prop

/-- The Bernoulli coin is actually zero or one, not an arbitrary value in their convex hull. -/
theorem request_binary (p : ℝ) : ∀ᵐ a ∂requestLaw p, a = 0 ∨ a = 1 := by
  unfold requestLaw endpointLaw
  apply ae_add_measure_iff.mpr
  constructor <;> apply Measure.ae_smul_measure <;> simp

/-- The centered cost contribution has exact expectation zero. -/
theorem centered_mean (p c : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∫ a, centeredCost p c a ∂requestLaw p) = 0 := by
  rw [requestLaw, endpoint_integral 0 1 p (by norm_num) hp]
  simp only [upperMass, sub_zero, div_one, centeredCost]
  ring

/-- Its second moment is the actual Bernoulli cost variance. -/
theorem centered_second (p c : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∫ a, centeredCost p c a ^ 2 ∂requestLaw p) = c ^ 2 * p * (1 - p) := by
  rw [requestLaw, endpoint_integral 0 1 p (by norm_num) hp]
  simp only [upperMass, sub_zero, div_one, centeredCost]
  ring

/-- The centered cost increment is bounded by its nonnegative unit cost. -/
theorem centered_bound (p c : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hc : 0 ≤ c) :
    ∀ᵐ a ∂requestLaw p, |centeredCost p c a| ≤ c := by
  have hs := endpointLaw_support 0 1 p (by norm_num : (0 : ℝ) ≤ 1)
  filter_upwards [hs] with a ha
  have hab : |a - p| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  simpa only [centeredCost, abs_mul, abs_of_nonneg hc, mul_one] using
    mul_le_mul_of_nonneg_left hab hc

variable {ι : Type*} [Fintype ι]

/-- The exact proposed-cost variance, computed from the registered request rates and costs. -/
noncomputable def costVariance (c p : ι → ℝ) : ℝ := ∑ i, c i ^ 2 * p i * (1 - p i)

/-- The largest individual labeling cost is the common Bernstein increment bound. -/
noncomputable def maxCost [Nonempty ι] (c : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty c

/-- Every unit cost is below the maximum cost. -/
theorem le_maxCost [Nonempty ι] (c : ι → ℝ) (i : ι) : c i ≤ maxCost c :=
  Finset.le_sup' (f := c) (Finset.mem_univ i)

/-- The full Bernoulli request vector has a normalized product law. -/
theorem requestFrame_probability (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    IsProbabilityMeasure (requestFrame p) := by
  letI (i : ι) := request_probability (p i) (hp i)
  unfold requestFrame
  infer_instance

/-- Total proposed cost minus its mean is precisely the sum of centered unit costs. -/
theorem cost_error (c p a : ι → ℝ) :
    contrast c a - contrast c p = ∑ i, centeredCost (p i) (c i) (a i) := by
  simp only [contrast, centeredCost, mul_sub, Finset.sum_sub_distrib]

/-- The actual independent selection law obeys the proposed-cost Bernstein tail bound. -/
theorem cost_tail (c p : ι → ℝ) (M x : ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hc : ∀ i, 0 ≤ c i) (hM : 0 ≤ M) (hcap : ∀ i, c i ≤ M) (hx : 0 < x) :
    (requestFrame p).real {a | contrast c p + radius M (costVariance c p) x < contrast c a} ≤
      Real.exp (-x) := by
  let ν (i : ι) := requestLaw (p i)
  letI (i : ι) : IsProbabilityMeasure (ν i) := request_probability (p i) (hp i)
  let X (i : ι) (a : ι → ℝ) := centeredCost (p i) (c i) (a i)
  have hm (i : ι) : Measurable (X i) :=
    (centered_measurable (p i) (c i)).comp (measurable_pi_apply i)
  have hind : iIndepFun X (Measure.pi ν) := iIndepFun_pi (μ := ν)
    (X := fun i ↦ centeredCost (p i) (c i))
    (fun i ↦ (centered_measurable (p i) (c i)).aemeasurable)
  have hb (i : ι) (_hi : i ∈ Finset.univ) : ∀ᵐ a ∂Measure.pi ν, |X i a| ≤ M := by
    have hh := (measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (centered_bound (p i) (c i) (hp i) (hc i))
    filter_upwards [hh] with a ha
    exact ha.trans (hcap i)
  have hz (i : ι) (_hi : i ∈ Finset.univ) : (∫ a, X i a ∂Measure.pi ν) = 0 := by
    change (∫ a, centeredCost (p i) (c i) (a i) ∂Measure.pi ν) = 0
    rw [integral_comp_eval (μ := ν) (f := centeredCost (p i) (c i))
      (centered_measurable (p i) (c i)).aestronglyMeasurable]
    exact centered_mean (p i) (c i) (hp i)
  have hv : (∑ i, ∫ a, X i a ^ 2 ∂Measure.pi ν) ≤ costVariance c p := by
    apply le_of_eq
    unfold costVariance
    apply Finset.sum_congr rfl
    intro i _
    change (∫ a, centeredCost (p i) (c i) (a i) ^ 2 ∂Measure.pi ν) = _
    rw [integral_comp_eval (μ := ν) (f := fun y ↦ centeredCost (p i) (c i) y ^ 2)
      ((centered_measurable (p i) (c i)).pow_const 2).aestronglyMeasurable]
    exact centered_second (p i) (c i) (hp i)
  have ht := BernsteinUpperConfidence.bernstein_upper X Finset.univ hind hm M
    (costVariance c p) x hM hx hb hz hv
  have he : {a | contrast c p + radius M (costVariance c p) x < contrast c a} =
      {a | radius M (costVariance c p) x < ∑ i, X i a} := by
    ext a
    change (contrast c p + radius M (costVariance c p) x < contrast c a) ↔
      (radius M (costVariance c p) x < ∑ i, centeredCost (p i) (c i) (a i))
    rw [← cost_error]
    constructor <;> intro ha <;> linarith
  rw [he]
  exact ht

/-- The one-sided confidence exponent has exactly the requested tail probability. -/
theorem upper_tail_value (δ : ℝ) (hδ : 0 < δ) : Real.exp (-Real.log (1 / δ)) = δ := by
  rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ)]
  simp

/-- A hard budget above the computed tail threshold has abort probability at most delta. -/
theorem abort_probability [Nonempty ι] (c p : ι → ℝ) (hard δ : ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hc : ∀ i, 0 ≤ c i) (hδ : 0 < δ ∧ δ < 1)
    (hbudget : contrast c p + radius (maxCost c) (costVariance c p) (Real.log (1 / δ)) ≤ hard) :
    (requestFrame p).real {a | hard < contrast c a} ≤ δ := by
  letI := requestFrame_probability p hp
  have hM : 0 ≤ maxCost c := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hc i).trans (le_maxCost c i)
  have hx : 0 < Real.log (1 / δ) := Real.log_pos ((lt_div_iff₀ hδ.1).mpr (by linarith [hδ.2]))
  have ht := cost_tail c p (maxCost c) (Real.log (1 / δ)) hp hc hM (le_maxCost c) hx
  rw [upper_tail_value δ hδ.1] at ht
  exact (measureReal_mono (show {a | hard < contrast c a} ⊆
    {a | contrast c p + radius (maxCost c) (costVariance c p) (Real.log (1 / δ)) < contrast c a}
    from fun _ ha ↦ lt_of_le_of_lt hbudget ha)).trans ht

end Descent.Portability.BernoulliBudgetLaw
