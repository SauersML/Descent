/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditTrace

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 15. Every positive-probability
unit-cost audit obeys the uncertainty-weighted leverage cost lower bound.
Normalization is already included in the rows: taking rows u_i/N recovers
the manuscript's factor N squared. Isotropic covariance and proportional
allocation attain the bound exactly when feasible.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditCost

open AuditCovarianceSpectrum SpectralAuditDesign SpectralAuditTrace
open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The total uncertainty-weighted leverage in the chosen repair coordinates. -/
noncomputable def leverageSum (κ : ι → ℝ) (u : ι → E) : ℝ :=
  ∑ i, Real.sqrt (κ i) * ‖u i‖

/-- Weighted Cauchy-Schwarz supplies an exact trace obstruction for every positive allocation. -/
theorem trace_cost_lower (κ p : ι → ℝ) (u : ι → E)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) :
    leverageSum κ u ^ 2 / (∑ i, p i) ≤ ∑ i, κ i / p i * ‖u i‖ ^ 2 := by
  have hh := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i ↦ Real.sqrt (κ i) * ‖u i‖) (fun i _ ↦ hp i)
  change leverageSum κ u ^ 2 / (∑ i, p i) ≤
    ∑ i, (Real.sqrt (κ i) * ‖u i‖) ^ 2 / p i at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, Real.sq_sqrt (hκ i)]
  ring

/-- The exact lower bound on worst-direction variance at a given expected label budget. -/
theorem cost_lower_bound (κ p : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (hB : 0 < B)
    (hd : 0 < Module.finrank ℝ E) (hbudget : (∑ i, p i) ≤ B) :
    leverageSum κ u ^ 2 / ((Module.finrank ℝ E : ℝ) * B) ≤ objective κ u p := by
  have hP : 0 < ∑ i, p i := Finset.sum_pos (fun i _ ↦ hp i) Finset.univ_nonempty
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  have hs := trace_cost_lower κ p u hκ hp
  have ht := trace_le_dimension (fun i ↦ κ i / p i) u
    (fun i ↦ div_nonneg (hκ i) (hp i).le)
  have hb : leverageSum κ u ^ 2 / B ≤ leverageSum κ u ^ 2 / (∑ i, p i) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hP hbudget
  have hh := hb.trans (hs.trans ht)
  apply (div_le_iff₀ (mul_pos hdim hB)).mpr
  have he := (div_le_iff₀ hB).mp hh
  change leverageSum κ u ^ 2 ≤ objective κ u p * ((Module.finrank ℝ E : ℝ) * B)
  nlinarith

/-- An isotropic covariance attains equality between trace and dimension times top variance. -/
theorem isotropic_trace (w : ι → ℝ) (u : ι → E) (α : ℝ)
    (hd : 0 < Module.finrank ℝ E) (hiso : covariance w u = α • LinearMap.id) :
    (∑ i, w i * ‖u i‖ ^ 2) = (Module.finrank ℝ E : ℝ) * largest w u := by
  obtain ⟨a, ha, he⟩ := largest_attained w u hd
  have hλ : largest w u = α := by
    rw [← he, ← quadratic, hiso, LinearMap.smul_apply, LinearMap.id_apply,
      inner_smul_right, real_inner_self_eq_norm_sq, ha]
    ring
  rw [← covariance_trace, hiso, map_smul, hλ]
  simp [mul_comm]

/-- Proportional positive probabilities attain equality in the weighted Cauchy-Schwarz step. -/
theorem proportional_trace (κ p : ι → ℝ) (u : ι → E) (t B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (ht : 0 < t)
    (halloc : ∀ i, p i = t * (Real.sqrt (κ i) * ‖u i‖)) (hbudget : (∑ i, p i) = B) :
    (∑ i, κ i / p i * ‖u i‖ ^ 2) * B = leverageSum κ u ^ 2 := by
  have hsum : B = t * leverageSum κ u := by
    rw [← hbudget, leverageSum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ halloc i)
  have heach (i : ι) : κ i / p i * ‖u i‖ ^ 2 = (Real.sqrt (κ i) * ‖u i‖) / t := by
    have hs : (Real.sqrt (κ i) * ‖u i‖) ^ 2 = κ i * ‖u i‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hκ i)]
    apply (eq_div_iff ht.ne').mpr
    have hpos := (hp i).ne'
    field_simp
    rw [halloc i]
    nlinarith
  simp_rw [heach]
  rw [← Finset.sum_div, hsum]
  change leverageSum κ u / t * (t * leverageSum κ u) = leverageSum κ u ^ 2
  field_simp
  ring

/-- Feasible isotropic, proportional allocations achieve the cost lower bound exactly. -/
theorem attained_cost_bound (κ p : ι → ℝ) (u : ι → E) (B t α : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (hB : 0 < B) (ht : 0 < t)
    (hd : 0 < Module.finrank ℝ E)
    (halloc : ∀ i, p i = t * (Real.sqrt (κ i) * ‖u i‖)) (hbudget : (∑ i, p i) = B)
    (hiso : covariance (fun i ↦ κ i / p i) u = α • LinearMap.id) :
    objective κ u p = leverageSum κ u ^ 2 / ((Module.finrank ℝ E : ℝ) * B) := by
  have hi := isotropic_trace (fun i ↦ κ i / p i) u α hd hiso
  have hc := proportional_trace κ p u t B hκ hp ht halloc hbudget
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  apply (eq_div_iff (mul_pos hdim hB).ne').mpr
  rw [hi] at hc
  change objective κ u p * ((Module.finrank ℝ E : ℝ) * B) = leverageSum κ u ^ 2
  nlinarith

end Descent.Portability.SpectralAuditCost
