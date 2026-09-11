/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditCenteredObservations
import Descent.Portability.BernsteinConfidence

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 9. The actual independent augmented
audit law satisfies simultaneous confidence bounds for a fixed finite decision
library. Means, variances, ranges, and independence are derived from that law;
only the outcome support, honest mean bands, and design constraints are inputs.
The coefficient vectors include the frame normalization, e.g. B_ji / N.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteAuditConfidence

open MeasureTheory ProbabilityTheory AugmentedAuditLaw AuditVarianceGeometry
open BoundedAuditCompletion SharedAuditCompletion IndependentContrastLaw AuditCenteredObservations
open BernsteinTailBound
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The exact worst-case variance bound for one contrast, computed from its design. -/
noncomputable def varianceBound (L U p q lo hi w : ι → ℝ) : ℝ :=
  ∑ i, w i ^ 2 * envelope (L i) (U i) (p i) (q i)
    (clip (lo i) (hi i) (vertex (L i) (U i) (p i) (q i)))

/-- The exact maximum bounded-increment constant over the nonempty target frame. -/
noncomputable def rangeBound [Nonempty ι] (L U p w : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |w i| * (U i - L i) / p i)

/-- Every row's range contribution is bounded by the computed maximum. -/
theorem le_rangeBound [Nonempty ι] (L U p w : ι → ℝ) (i : ι) :
    |w i| * (U i - L i) / p i ≤ rangeBound L U p w :=
  Finset.le_sup' (f := fun i ↦ |w i| * (U i - L i) / p i) (Finset.mem_univ i)

/-- Valid outcome intervals and request probabilities make the computed range nonnegative. -/
theorem rangeBound_nonneg [Nonempty ι] (L U p w : ι → ℝ)
    (hLU : ∀ i, L i ≤ U i) (hp : ∀ i, 0 < p i) : 0 ≤ rangeBound L U p w := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hh : 0 ≤ |w i| * (U i - L i) / p i :=
    div_nonneg (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (hLU i))) (hp i).le
  exact hh.trans (le_rangeBound L U p w i)

/-- The contrast estimation error is precisely the sum of centered audit observations. -/
theorem contrast_error (μ : ι → Measure ℝ) (w z : ι → ℝ) :
    contrast w z - (∑ i, w i * ∫ y, y ∂μ i) = ∑ i, centered (μ i) (w i) (z i) := by
  simp only [contrast, centered, mul_sub, Finset.sum_sub_distrib]

/-- Bernstein's inequality instantiated on the actual target audit experiment. -/
theorem contrast_tail (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi w : ι → ℝ) (M x : ℝ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i)
    (hM : 0 ≤ M) (hcap : ∀ i, |w i| * (U i - L i) / p i ≤ M) (hx : 0 < x) :
    (frameLaw μ p q).real {z | radius M (varianceBound L U p q lo hi w) x <
      |contrast w z - (∑ i, w i * ∫ y, y ∂μ i)|} ≤ 2 * Real.exp (-x) := by
  let ν (i : ι) := auditLaw (μ i) (p i) (q i)
  letI (i : ι) : IsProbabilityMeasure (ν i) :=
    auditLaw_probability (μ i) (p i) (q i) ⟨(hp i).1.le, (hp i).2⟩
  let X (i : ι) (z : ι → ℝ) := centered (μ i) (w i) (z i)
  have hY (i : ι) := memLp_of_bounded (hs i) measurable_id.aestronglyMeasurable 2
  have hm (i : ι) : Measurable (X i) :=
    (centered_measurable (μ i) (w i)).comp (measurable_pi_apply i)
  have hIndep : iIndepFun X (Measure.pi ν) :=
    iIndepFun_pi (μ := ν) (X := fun i ↦ centered (μ i) (w i))
      (fun i ↦ (centered_measurable (μ i) (w i)).aemeasurable)
  have hb (i : ι) (_his : i ∈ Finset.univ) : ∀ᵐ z ∂Measure.pi ν, |X i z| ≤ M := by
    have hh := (measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (centered_range (μ i) (p i) (q i) (L i) (U i) (w i) (hp i) (hq i) (hs i))
    filter_upwards [hh] with z hz
    exact hz.trans (hcap i)
  have hmean (i : ι) (_his : i ∈ Finset.univ) : (∫ z, X i z ∂Measure.pi ν) = 0 := by
    change (∫ z, centered (μ i) (w i) (z i) ∂Measure.pi ν) = 0
    rw [integral_comp_eval (μ := ν) (f := centered (μ i) (w i))
      (centered_measurable (μ i) (w i)).aestronglyMeasurable]
    exact centered_mean (μ i) (p i) (q i) (w i) (hp i) (hY i)
  have hv : (∑ i, ∫ z, X i z ^ 2 ∂Measure.pi ν) ≤ varianceBound L U p q lo hi w := by
    unfold varianceBound
    apply Finset.sum_le_sum
    intro i _
    change (∫ z, centered (μ i) (w i) (z i) ^ 2 ∂Measure.pi ν) ≤ _
    rw [integral_comp_eval (μ := ν) (f := fun y ↦ centered (μ i) (w i) y ^ 2)
      ((centered_measurable (μ i) (w i)).pow_const 2).aestronglyMeasurable]
    rw [centered_second_moment (μ i) (p i) (q i) (w i) (hp i) (hY i)]
    exact mul_le_mul_of_nonneg_left
      (worst_case_upper (μ i) (L i) (U i) (p i) (q i) (lo i) (hi i)
        (hp i) (hs i) (hband i)) (sq_nonneg _)
  have ht := BernsteinConfidence.bernstein X Finset.univ hIndep hm M
    (varianceBound L U p q lo hi w) x hM hx hb hmean hv
  change (frameLaw μ p q).real {z | radius M (varianceBound L U p q lo hi w) x <
    |∑ i, centered (μ i) (w i) (z i)|} ≤ 2 * Real.exp (-x) at ht
  simpa only [← contrast_error] using ht

/-- The finite-library exponent is strictly positive on the claimed confidence domain. -/
theorem confidence_exponent_pos (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    0 < Real.log (2 * K / δ) := by
  apply Real.log_pos
  apply (lt_div_iff₀ hδ.1).mpr
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [hδ.2]

/-- The two-sided tail at the chosen exponent is exactly δ/K. -/
theorem confidence_tail_value (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) :
    2 * Real.exp (-Real.log (2 * K / δ)) = δ / K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * (K : ℝ) / δ)]
  field_simp

/-- One audit certifies the entire registered finite library with failure probability at most δ. -/
theorem finite_library (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (K : ℕ) (hK : 0 < K) (w : Fin K → ι → ℝ)
    (M : Fin K → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i)
    (hM : ∀ j, 0 ≤ M j) (hcap : ∀ j i, |w j i| * (U i - L i) / p i ≤ M j) :
    (frameLaw μ p q).real {z | ∃ j, radius (M j) (varianceBound L U p q lo hi (w j))
      (Real.log (2 * K / δ)) < |contrast (w j) z - (∑ i, w j i * ∫ y, y ∂μ i)|} ≤ δ := by
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  let bad (j : Fin K) := {z | radius (M j) (varianceBound L U p q lo hi (w j))
    (Real.log (2 * K / δ)) < |contrast (w j) z - (∑ i, w j i * ∫ y, y ∂μ i)|}
  have hj (j : Fin K) : (frameLaw μ p q).real (bad j) ≤ δ / K := by
    have hh := contrast_tail μ L U p q lo hi (w j) (M j) (Real.log (2 * K / δ))
      hp hq hs hband (hM j) (hcap j) (confidence_exponent_pos K hK δ hδ)
    rw [confidence_tail_value K hK δ hδ.1] at hh
    exact hh
  have he : {z | ∃ j, radius (M j) (varianceBound L U p q lo hi (w j))
      (Real.log (2 * K / δ)) < |contrast (w j) z - (∑ i, w j i * ∫ y, y ∂μ i)|} =
      ⋃ j, bad j := by ext z; simp [bad]
  rw [he]
  calc
    (frameLaw μ p q).real (⋃ j, bad j) ≤ ∑ j, (frameLaw μ p q).real (bad j) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _j : Fin K, δ / K := Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp

/-- The manuscript's finite-library theorem with its variance and range constants both computed. -/
theorem finite_library_exact_range [Nonempty ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (K : ℕ) (hK : 0 < K) (w : Fin K → ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p q).real {z | ∃ j,
      radius (rangeBound L U p (w j)) (varianceBound L U p q lo hi (w j))
        (Real.log (2 * K / δ)) < |contrast (w j) z - (∑ i, w j i * ∫ y, y ∂μ i)|} ≤ δ := by
  exact finite_library μ L U p q lo hi K hK w (fun j ↦ rangeBound L U p (w j)) δ hδ
    hp hq hs hband
    (fun j ↦ rangeBound_nonneg L U p (w j) (fun i ↦ (hq i).1.trans (hq i).2)
      (fun i ↦ (hp i).1))
    (fun j i ↦ le_rangeBound L U p (w j) i)

end Descent.Portability.FiniteAuditConfidence
