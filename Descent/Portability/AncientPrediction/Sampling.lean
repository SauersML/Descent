/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncientPrediction.Certificate
import Mathlib.Probability.Moments.SubGaussian

assert_below Descent.Decision Descent.Program

/-!
# Modern sampling certificates

Two-sided Hoeffding bounds and the uniform no-worsening event. Independence is
required within each coordinate's sample; independence between coordinates or
between moment estimators is not required. The data-dependent selected update
can be arbitrary provided its reported certificate is nonpositive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncientPrediction

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two-sided deviation bound, derived from both Chernoff tails. -/
theorem subGaussian_absolute_tail {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε < |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hs : {ω | ε < |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := by
    intro ω hω
    change ε < |X ω| at hω
    rcases le_total 0 (X ω) with hx | hx
    · exact Or.inl (by simpa only [abs_of_nonneg hx] using (le_of_lt hω))
    · exact Or.inr (by simpa only [abs_of_nonpos hx] using (le_of_lt hω))
  have hp := hX.measure_ge_le hε
  have hn := hX.neg.measure_ge_le hε
  calc
    _ ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) := measureReal_mono hs
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Hoeffding for bounded independent observations. Means need not be identical:
this estimates the average of the observations' true expectations. -/
theorem bounded_sample_mean_tail {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hInd : iIndepFun X μ) (hm : ∀ i, AEMeasurable (X i) μ)
    (lo hi : ℝ) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc lo hi)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε < |((∑ i, X i ω) / n) - (∑ i, ∫ z, X i z ∂μ) / n|} ≤
      2 * Real.exp (-((n : ℝ) * ε) ^ 2 /
        (2 * (n : ℝ) * (((‖hi - lo‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  let Z : Fin n → Ω → ℝ := fun i ω => X i ω - ∫ z, X i z ∂μ
  have hz : ∀ i, HasSubgaussianMGF (Z i) ((‖hi - lo‖₊ / 2) ^ 2) μ :=
    fun i => hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
  have hindZ : iIndepFun Z μ := hInd.comp
    (fun i x => x - ∫ z, X i z ∂μ) (fun _ => measurable_id.sub_const _)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindZ (s := Finset.univ)
    (fun i _ => hz i)
  have ht := subGaussian_absolute_tail hsum (mul_nonneg (Nat.cast_nonneg n) hε)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he : {ω | ε < |((∑ i, X i ω) / n) - (∑ i, ∫ z, X i z ∂μ) / n|} =
      {ω | (n : ℝ) * ε < |∑ i, Z i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Z, Finset.sum_sub_distrib, ← sub_div, abs_div,
      abs_of_pos hn', lt_div_iff₀ hn', mul_comm ε]
  rw [he]
  simpa [mul_assoc] using ht

omit [IsProbabilityMeasure μ] in
/-- A finite union bound needs no independence between the reported moments. -/
theorem simultaneous_moment_tail {J : Type*} [Fintype J]
    (error : J → Ω → ℝ) (ε budget : J → ℝ)
    (htail : ∀ j, μ.real {ω | ε j < |error j ω|} ≤ budget j) :
    μ.real {ω | ∃ j, ε j < |error j ω|} ≤ ∑ j, budget j := by
  have he : {ω | ∃ j, ε j < |error j ω|} = ⋃ j, {ω | ε j < |error j ω|} := by
    ext ω
    simp
  rw [he]
  exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun j _ => htail j)

/-- Probability of worsening after selecting weights from the same moment
estimates. The premises bound the coordinate estimation tails, not the risk
or the selected weights; `bounded_sample_mean_tail` supplies those premises. -/
theorem selected_update_failure_bound {G I : Type*} [Fintype G] [Fintype I]
    (u : G → I → ℝ) (V : G → I → I → ℝ)
    (uhat : Ω → G → I → ℝ) (Vhat : Ω → G → I → I → ℝ)
    (εu εV budgetU budgetV : G → ℝ) (chosen : Ω → I → ℝ)
    (hεV : ∀ g, 0 ≤ εV g)
    (hU : ∀ g i, μ.real {ω | εu g < |u g i - uhat ω g i|} ≤ budgetU g)
    (hV : ∀ g i j, μ.real {ω | εV g < |V g i j - Vhat ω g i j|} ≤ budgetV g)
    (hc : ∀ ω g, certifiedBound (uhat ω g) (Vhat ω g) (εu g) (εV g) (chosen ω) ≤ 0) :
    μ.real {ω | ∃ g, 0 < coordinateRisk (u g) (V g) (chosen ω)} ≤
      ∑ g, (Fintype.card I : ℝ) * budgetU g +
      ∑ g, (Fintype.card I : ℝ) ^ 2 * budgetV g := by
  let badU : Set Ω := {ω | ∃ gi : G × I, εu gi.1 < |u gi.1 gi.2 - uhat ω gi.1 gi.2|}
  let badV : Set Ω := {ω | ∃ gij : G × I × I,
    εV gij.1 < |V gij.1 gij.2.1 gij.2.2 - Vhat ω gij.1 gij.2.1 gij.2.2|}
  have hsubset : {ω | ∃ g, 0 < coordinateRisk (u g) (V g) (chosen ω)} ⊆ badU ∪ badV := by
    intro ω hω
    by_contra hbad
    have hnot := not_or.mp hbad
    have hu : ∀ g i, |u g i - uhat ω g i| ≤ εu g := by
      intro g i
      exact le_of_not_gt (fun h => hnot.1 ⟨(g, i), h⟩)
    have hv : ∀ g i j, |V g i j - Vhat ω g i j| ≤ εV g := by
      intro g i j
      exact le_of_not_gt (fun h => hnot.2 ⟨(g, i, j), h⟩)
    obtain ⟨g, hg⟩ := hω
    exact (not_lt_of_ge (simultaneous_no_worsening u (uhat ω) V (Vhat ω)
      εu εV (chosen ω) hεV hu hv (hc ω) g)) hg
  have hbu := simultaneous_moment_tail (μ := μ)
    (fun gi : G × I => fun ω => u gi.1 gi.2 - uhat ω gi.1 gi.2)
    (fun gi => εu gi.1) (fun gi => budgetU gi.1) (fun gi => hU gi.1 gi.2)
  have hbv := simultaneous_moment_tail (μ := μ)
    (fun gij : G × I × I => fun ω => V gij.1 gij.2.1 gij.2.2 - Vhat ω gij.1 gij.2.1 gij.2.2)
    (fun gij => εV gij.1) (fun gij => budgetV gij.1) (fun gij => hV gij.1 gij.2.1 gij.2.2)
  have htot := (measureReal_mono hsubset).trans ((measureReal_union_le badU badV).trans
    (add_le_add hbu hbv))
  simpa [Fintype.sum_prod_type, pow_two, mul_assoc] using htot

end Descent.Portability.AncientPrediction
