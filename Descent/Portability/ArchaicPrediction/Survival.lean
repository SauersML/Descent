/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Survivor reweighting of uncertain haplotype states

Theorem 8: the effective rate decreases at exactly the negative survivor-
weighted variance. The finite probability distribution, exponential survival,
normalization, differentiation, and variance identity are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {H : Type*} [Fintype H]

noncomputable def mixtureSurvival (π r : H → ℝ) (Λ : ℝ) : ℝ :=
  ∑ h, π h * Real.exp (-Λ * r h)

noncomputable def survivalNumerator (π r : H → ℝ) (Λ : ℝ) : ℝ :=
  ∑ h, π h * r h * Real.exp (-Λ * r h)

noncomputable def survivorWeight (π r : H → ℝ) (Λ : ℝ) (h : H) : ℝ :=
  π h * Real.exp (-Λ * r h) / mixtureSurvival π r Λ

noncomputable def effectiveRate (π r : H → ℝ) (Λ : ℝ) : ℝ :=
  survivalNumerator π r Λ / mixtureSurvival π r Λ

theorem mixtureSurvival_pos (π r : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (hsum : ∑ h, π h = 1) (Λ : ℝ) : 0 < mixtureSurvival π r Λ := by
  obtain ⟨h, _, hh⟩ := (Finset.sum_pos_iff_of_nonneg (fun h _ => hπ h)).mp
    (show 0 < ∑ h, π h by rw [hsum]; norm_num)
  exact Finset.sum_pos' (fun h _ => mul_nonneg (hπ h) (Real.exp_pos _).le)
    ⟨h, Finset.mem_univ h, mul_pos hh (Real.exp_pos _)⟩

theorem survivorWeight_probability (π r : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (hsum : ∑ h, π h = 1) (Λ : ℝ) :
    (∀ h, 0 ≤ survivorWeight π r Λ h) ∧ ∑ h, survivorWeight π r Λ h = 1 := by
  have hp := mixtureSurvival_pos π r hπ hsum Λ
  constructor
  · intro h; exact div_nonneg (mul_nonneg (hπ h) (Real.exp_pos _).le) hp.le
  · simp only [survivorWeight, ← Finset.sum_div]
    exact div_self hp.ne'

theorem effectiveRate_mean (π r : H → ℝ) (Λ : ℝ) :
    ∑ h, survivorWeight π r Λ h * r h = effectiveRate π r Λ := by
  simp only [survivorWeight, effectiveRate, survivalNumerator, Finset.sum_div]
  apply Finset.sum_congr rfl
  intros; ring

lemma survival_derivative (π r : H → ℝ) (Λ : ℝ) :
    HasDerivAt (mixtureSurvival π r) (-survivalNumerator π r Λ) Λ := by
  convert HasDerivAt.sum (u := Finset.univ) (fun h _ =>
    (((hasDerivAt_id Λ).neg.mul_const (r h)).exp.const_mul (π h))) using 1
  · funext x; simp [mixtureSurvival]
  · rw [survivalNumerator, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros; simp only [Pi.neg_apply, id_eq]; ring

lemma survivalNumerator_derivative (π r : H → ℝ) (Λ : ℝ) :
    HasDerivAt (survivalNumerator π r)
      (-(∑ h, π h * r h ^ 2 * Real.exp (-Λ * r h))) Λ := by
  convert HasDerivAt.sum (u := Finset.univ) (fun h _ =>
    (((hasDerivAt_id Λ).neg.mul_const (r h)).exp.const_mul (π h * r h))) using 1
  · funext x; simp [survivalNumerator]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros; simp only [Pi.neg_apply, id_eq]; ring

/-- Differentiation of the marginal rate gives the negative variance. -/
theorem effectiveRate_derivative (π r : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (hsum : ∑ h, π h = 1) (Λ : ℝ) :
    HasDerivAt (effectiveRate π r)
      (-(∑ h, survivorWeight π r Λ h * (r h - effectiveRate π r Λ) ^ 2)) Λ := by
  have hp := mixtureSurvival_pos π r hπ hsum Λ
  have hs := (survivorWeight_probability π r hπ hsum Λ).2
  have hm := effectiveRate_mean π r Λ
  have hv : (∑ h, survivorWeight π r Λ h * (r h - effectiveRate π r Λ) ^ 2) =
      (∑ h, π h * r h ^ 2 * Real.exp (-Λ * r h)) / mixtureSurvival π r Λ -
        effectiveRate π r Λ ^ 2 := by
    have hex (h : H) : survivorWeight π r Λ h * (r h - effectiveRate π r Λ) ^ 2 =
        survivorWeight π r Λ h * r h ^ 2 -
        2 * effectiveRate π r Λ * (survivorWeight π r Λ h * r h) +
        effectiveRate π r Λ ^ 2 * survivorWeight π r Λ h := by ring
    simp_rw [hex, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hm, hs]
    have hsecond : (∑ h, survivorWeight π r Λ h * r h ^ 2) =
        (∑ h, π h * r h ^ 2 * Real.exp (-Λ * r h)) / mixtureSurvival π r Λ := by
      simp only [survivorWeight, Finset.sum_div]
      apply Finset.sum_congr rfl
      intros; ring
    rw [hsecond]; ring
  convert (survivalNumerator_derivative π r Λ).div (survival_derivative π r Λ) hp.ne' using 1
  rw [hv]
  dsimp [effectiveRate]
  have halg (s n z : ℝ) : -(z / s - (n / s) ^ 2) = ((-z) * s - n * (-n)) / s ^ 2 := by
    by_cases h : s = 0
    · simp [h]
    · field_simp; ring
  exact halg _ _ _

theorem effectiveRate_deriv_nonpos (π r : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (hsum : ∑ h, π h = 1) (Λ : ℝ) : deriv (effectiveRate π r) Λ ≤ 0 := by
  rw [(effectiveRate_derivative π r hπ hsum Λ).deriv]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun h _ =>
    mul_nonneg ((survivorWeight_probability π r hπ hsum Λ).1 h) (sq_nonneg _))

/-- Chain rule from baseline cumulative hazard to the marginal hazard. -/
theorem marginal_hazard (π r : H → ℝ) (hπ : ∀ h, 0 ≤ π h) (hsum : ∑ h, π h = 1)
    (Λ : ℝ → ℝ) (t baselineRate : ℝ) (hΛ : HasDerivAt Λ baselineRate t) :
    HasDerivAt (fun s => -Real.log (mixtureSurvival π r (Λ s)))
      (baselineRate * effectiveRate π r (Λ t)) t := by
  have hp := mixtureSurvival_pos π r hπ hsum (Λ t)
  convert (((survival_derivative π r (Λ t)).comp t hΛ).log hp.ne').neg using 1
  dsimp [effectiveRate]
  ring

end Descent.Portability.ArchaicPrediction
