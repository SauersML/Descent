/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MedianAuditConcentration
import Descent.Portability.SecondMomentAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 25. Actual independent blocks of
iid target observations give a median-of-means confidence certificate for
every member of a fixed finite paired-improvement library. The block failure
bound is derived from actual means and variances; no fourth moment is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PairedMedianOfMeans

open MeasureTheory ProbabilityTheory IIDAverageLaw FiniteMedianGeometry
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual block mean is measurable. -/
theorem average_measurable (f : Ω → ℝ) (hf : Measurable f) (s : ℕ) :
    Measurable (average f s) := by
  unfold average
  fun_prop

/-- The mean of a finite iid block has finite second moment. -/
theorem average_memLp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (s : ℕ) :
    MemLp (average f s) 2 (Measure.pi (fun _ : Fin s ↦ μ)) := by
  have hi (i : Fin s) : MemLp (fun z : Fin s → Ω ↦ f (z i)) 2
      (Measure.pi (fun _ : Fin s ↦ μ)) :=
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin s ↦ μ) i)
  exact (memLp_finset_sum _ (fun i _ ↦ hi i)).const_mul (1 / (s : ℝ))

/-- Chebyshev's one-quarter block failure bound follows from the actual iid block variance. -/
theorem block_failure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (s : ℕ) (hs : 0 < s)
    (V : ℝ) (hV : Var[f; μ] ≤ V) :
    (Measure.pi (fun _ : Fin s ↦ μ)).real
      {z | 2 * Real.sqrt (V / s) < |average f s z - ∫ ω, f ω ∂μ|} ≤ 1 / 4 := by
  have hmean := average_integral μ f (hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)) s hs
  have hm := average_memLp μ f hf s
  have hcenter := hm.sub (memLp_const (∫ ω, f ω ∂μ))
  have he : (∫ z, ‖average f s z - ∫ ω, f ω ∂μ‖ ^ 2
      ∂Measure.pi (fun _ : Fin s ↦ μ)) ≤ V / s := by
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← hmean, ← variance_eq_integral hm.aemeasurable, average_variance μ f hf s hs]
    exact div_le_div_of_nonneg_right hV (Nat.cast_nonneg s)
  have hi : Integrable (fun z ↦ ‖average f s z - ∫ ω, f ω ∂μ‖ ^ 2)
      (Measure.pi (fun _ : Fin s ↦ μ)) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hcenter.integrable_sq
  have ht := SecondMomentAuditConfidence.norm_markov (Measure.pi (fun _ : Fin s ↦ μ))
    (fun z ↦ average f s z - ∫ ω, f ω ∂μ) (V / s) (1 / 4) (by norm_num) hi he
  have hr : Real.sqrt ((V / s) / (1 / 4)) = 2 * Real.sqrt (V / s) := by
    rw [show (V / s) / (1 / 4) = 4 * (V / s) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  simpa only [hr, Real.norm_eq_abs] using ht

/-- The actual median-of-means estimator, evaluated on an odd collection of iid blocks. -/
noncomputable def estimate (f : Ω → ℝ) (m s : ℕ)
    (z : Fin (2 * m + 1) → Fin s → Ω) : ℝ := median (fun j ↦ average f s (z j))

/-- The genuine product experiment has the exponential paired-estimation error bound. -/
theorem paired_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfm : Measurable f) (hf : MemLp f 2 μ) (m s : ℕ) (hs : 0 < s)
    (V : ℝ) (hV : Var[f; μ] ≤ V) :
    (Measure.pi (fun _ : Fin (2 * m + 1) ↦ Measure.pi (fun _ : Fin s ↦ μ))).real
      {z | 2 * Real.sqrt (V / s) < |estimate f m s z - ∫ ω, f ω ∂μ|} ≤
      Real.exp (-((2 * m + 1 : ℕ) : ℝ) / 8) := by
  exact MedianAuditConcentration.median_tail (Measure.pi (fun _ : Fin s ↦ μ)) (average f s)
    (∫ ω, f ω ∂μ) (2 * Real.sqrt (V / s)) (average_measurable f hfm s) m
    (block_failure μ f hf s hs V hV)

/-- The stated logarithmic block count bounds the union of all registered comparison errors. -/
theorem library_exponent (J K : ℕ) (hJ : 0 < J) (δ : ℝ) (hδ : 0 < δ)
    (hK : 8 * Real.log ((J : ℝ) / δ) ≤ K) :
    (J : ℝ) * Real.exp (-(K : ℝ) / 8) ≤ δ := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have he : Real.exp (-(K : ℝ) / 8) ≤ Real.exp (-Real.log ((J : ℝ) / δ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log (div_pos hj hδ)] at he
  have hh := mul_le_mul_of_nonneg_left he hj.le
  have hid : (J : ℝ) * ((J : ℝ) / δ)⁻¹ = δ := by field_simp
  rwa [hid] at hh

/-- One fixed iid label study certifies every predeclared paired comparison simultaneously. -/
theorem simultaneous (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ) (hJ : 0 < J)
    (f : Fin J → Ω → ℝ) (hfm : ∀ j, Measurable (f j)) (hf : ∀ j, MemLp (f j) 2 μ)
    (m s : ℕ) (hs : 0 < s) (V : Fin J → ℝ) (hV : ∀ j, Var[f j; μ] ≤ V j)
    (δ : ℝ) (hδ : 0 < δ) (hK : 8 * Real.log ((J : ℝ) / δ) ≤ (2 * m + 1 : ℕ)) :
    (Measure.pi (fun _ : Fin (2 * m + 1) ↦ Measure.pi (fun _ : Fin s ↦ μ))).real
      {z | ∃ j, 2 * Real.sqrt (V j / s) < |estimate (f j) m s z - ∫ ω, f j ω ∂μ|} ≤ δ := by
  let bad (j : Fin J) :=
    {z | 2 * Real.sqrt (V j / s) < |estimate (f j) m s z - ∫ ω, f j ω ∂μ|}
  have hu : {z | ∃ j, 2 * Real.sqrt (V j / s) <
      |estimate (f j) m s z - ∫ ω, f j ω ∂μ|} = ⋃ j, bad j := by ext z; simp [bad]
  rw [hu]
  apply (measureReal_iUnion_fintype_le bad).trans
  apply (Finset.sum_le_sum (fun j _ ↦ paired_tail μ (f j) (hfm j) (hf j) m s hs
    (V j) (hV j))).trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact library_exponent J (2 * m + 1) hJ δ hδ hK

end Descent.Portability.PairedMedianOfMeans
