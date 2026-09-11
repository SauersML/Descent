/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SparseBinaryAudit

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 20. The full-frame uniform audit
and the audit restricted to a decision disagreement set have the same exact
expected label budget. Their attained worst-case prospective variances are
alpha/(4 B) and alpha^2/(4 B), respectively. Every unsampled row is proved
irrelevant to the paired contrast. The budget condition B <= |D| is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DisagreementAuditPayoff

open MeasureTheory ProbabilityTheory SharedAuditCompletion IndependentContrastLaw
open BoundedAuditCompletion SparseBinaryAudit
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Uniform request probabilities across the whole target frame. -/
noncomputable def uniform (B : ℝ) (_i : ι) : ℝ := B / Fintype.card ι

/-- Request probabilities that spend the entire expected budget on the disagreement set. -/
noncomputable def targeted (D : Finset ι) (B : ℝ) (i : ι) : ℝ :=
  if i ∈ D then B / D.card else 0

/-- The paired contrast retains normalization by the size of the complete target frame. -/
noncomputable def weight (b : ι → ℝ) (i : ι) : ℝ := b i / Fintype.card ι

/-- The disagreement fraction is an exact frame proportion. -/
noncomputable def fraction (D : Finset ι) : ℝ := (D.card : ℝ) / Fintype.card ι

/-- Binary decision differences have exactly the squared coefficients used by the payoff law. -/
theorem binary_difference_shape (d₀ d₁ : ι → Bool) (i : ι) :
    ((if d₁ i then (1 : ℝ) else 0) - (if d₀ i then 1 else 0)) ^ 2 =
      if i ∈ Finset.univ.filter (fun j ↦ d₀ j ≠ d₁ j) then 1 else 0 := by
  cases h₀ : d₀ i <;> cases h₁ : d₁ i <;> simp [h₀, h₁]

/-- The whole-frame uniform design is admissible at every budget allowed for the smaller cell. -/
theorem uniform_admissible (D : Finset ι) (b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : B ≤ D.card) : Admissible (uniform B) (weight b) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hDN : (D.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ D
  have hp : 0 < B / Fintype.card ι := div_pos hB hN
  refine ⟨fun _ ↦ ⟨hp.le, ?_⟩, fun _ _ ↦ hp⟩
  exact (div_le_one hN).mpr (hcap.trans hDN)

/-- The targeted design needs positivity only on genuinely nonzero decision coefficients. -/
theorem targeted_admissible (D : Finset ι) (b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : B ≤ D.card)
    (hb : ∀ i, b i ^ 2 = if i ∈ D then 1 else 0) :
    Admissible (targeted D B) (weight b) := by
  have hD : (0 : ℝ) < D.card := hB.trans_le hcap
  have hp : 0 < B / D.card := div_pos hB hD
  constructor
  · intro i
    by_cases hi : i ∈ D
    · exact ⟨by simpa only [targeted, if_pos hi] using hp.le,
        by simpa only [targeted, if_pos hi] using (div_le_one hD).mpr hcap⟩
    · simp [targeted, hi]
  · intro i hw
    have hi : i ∈ D := by
      by_contra hn
      have hz : b i = 0 := sq_eq_zero_iff.mp (by simpa only [if_neg hn] using hb i)
      exact hw (by simp [weight, hz])
    simpa only [targeted, if_pos hi] using hp

/-- Both designs spend exactly B labels in expectation, including zero probabilities off the cell. -/
theorem equal_expected_budgets (D : Finset ι) (B : ℝ) (hB : 0 < B) (hcap : B ≤ D.card) :
    (∑ i : ι, uniform B i) = B ∧ (∑ i, targeted D B i) = B := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hD : (D.card : ℝ) ≠ 0 := (hB.trans_le hcap).ne'
  constructor
  · simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel₀ B hN
  · simp only [targeted, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel₀ B hD

/-- A constant request rate on the active cell has an exactly computed variance envelope. -/
theorem cell_variance_identity (D : Finset ι) (b p : ι → ℝ) (t : ℝ)
    (hb : ∀ i, b i ^ 2 = if i ∈ D then 1 else 0)
    (hp : ∀ i ∈ D, p i = t) :
    (∑ i, weight b i ^ 2 / (4 * p i)) = (D.card : ℝ) / (4 * (Fintype.card ι : ℝ) ^ 2 * t) := by
  have he (i : ι) : weight b i ^ 2 / (4 * p i) =
      if i ∈ D then 1 / (4 * (Fintype.card ι : ℝ) ^ 2 * t) else 0 := by
    by_cases hi : i ∈ D
    · simp only [weight, div_pow, hb i, if_pos hi, hp i hi]
      ring
    · simp only [weight, div_pow, hb i, if_neg hi, zero_div]
  simp_rw [he]
  simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The two exact envelope values give the alpha and alpha-squared laws. -/
theorem envelope_values (D : Finset ι) (b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : B ≤ D.card)
    (hb : ∀ i, b i ^ 2 = if i ∈ D then 1 else 0) :
    (∑ i, weight b i ^ 2 / (4 * uniform B i)) = fraction D / (4 * B) ∧
    (∑ i, weight b i ^ 2 / (4 * targeted D B i)) = fraction D ^ 2 / (4 * B) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hD : (D.card : ℝ) ≠ 0 := (hB.trans_le hcap).ne'
  constructor
  · rw [cell_variance_identity D b (uniform B) _ hb (fun _ _ ↦ rfl)]
    unfold fraction
    field_simp
  · rw [cell_variance_identity D b (targeted D B) (B / D.card) hb
      (fun i hi ↦ by simp only [targeted, if_pos hi])]
    unfold fraction
    field_simp

/-- Actual prospective audit variances obey the two bounds for every bounded outcome law. -/
theorem prospective_bounds (D : Finset ι) (b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : B ≤ D.card)
    (hb : ∀ i, b i ^ 2 = if i ∈ D then 1 else 0)
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (0 : ℝ) 1) :
    Var[contrast (weight b); frameLaw μ (uniform B) (fun _ ↦ 1 / 2)] ≤ fraction D / (4 * B) ∧
    Var[contrast (weight b); frameLaw μ (targeted D B) (fun _ ↦ 1 / 2)] ≤
      fraction D ^ 2 / (4 * B) := by
  obtain ⟨hu, ht⟩ := envelope_values D b B hB hcap hb
  constructor
  · exact (variance_upper μ _ _ (uniform_admissible D b B hB hcap) hs).trans_eq hu
  · exact (variance_upper μ _ _ (targeted_admissible D b B hB hcap hb) hs).trans_eq ht

/-- One explicit fair binary law attains both worst-case values, so the comparison is sharp. -/
theorem simultaneous_attainment (D : Finset ι) (b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (hcap : B ≤ D.card)
    (hb : ∀ i, b i ^ 2 = if i ∈ D then 1 else 0) :
    Var[contrast (weight b); frameLaw (fun _ ↦ endpointLaw 0 1 (1 / 2))
      (uniform B) (fun _ ↦ 1 / 2)] = fraction D / (4 * B) ∧
    Var[contrast (weight b); frameLaw (fun _ ↦ endpointLaw 0 1 (1 / 2))
      (targeted D B) (fun _ ↦ 1 / 2)] = fraction D ^ 2 / (4 * B) := by
  obtain ⟨hu, ht⟩ := envelope_values D b B hB hcap hb
  exact ⟨(variance_attained _ _ (uniform_admissible D b B hB hcap)).trans hu,
    (variance_attained _ _ (targeted_admissible D b B hB hcap hb)).trans ht⟩

/-- The precise worst-case variance ratio is the inverse disagreement fraction. -/
theorem variance_ratio (D : Finset ι) (B : ℝ) (hB : 0 < B) (hcap : B ≤ D.card) :
    (fraction D / (4 * B)) / (fraction D ^ 2 / (4 * B)) = 1 / fraction D := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hα : 0 < fraction D := div_pos (hB.trans_le hcap) hN
  field_simp

end Descent.Portability.DisagreementAuditPayoff
