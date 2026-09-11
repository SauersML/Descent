/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SpectralAuditCost

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 15: necessity of the equality
conditions in the labeling-cost lower bound. For positive total leverage,
equality requires full budget use, an isotropic actual covariance operator,
and the specified proportional allocation. A sum-of-squares identity proves
the allocation condition, rather than assuming equality in Cauchy-Schwarz.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralCostEquality

open AuditCovarianceSpectrum SpectralAuditDesign SpectralAuditTrace SpectralAuditCost
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Equality of trace with dimension times top variance forces an isotropic covariance. -/
theorem isotropic_of_trace_equality (w : ι → ℝ) (u : ι → E)
    (ht : (∑ i, w i * ‖u i‖ ^ 2) = (Module.finrank ℝ E : ℝ) * largest w u) :
    covariance w u = largest w u • LinearMap.id := by
  have hsum : (∑ j, eigenvalues w u j) =
      ∑ _j : Fin (Module.finrank ℝ E), largest w u := by
    calc
      _ = LinearMap.trace ℝ E (covariance w u) :=
        ((symmetric w u).trace_eq_sum_eigenvalues rfl).symm
      _ = (Module.finrank ℝ E : ℝ) * largest w u := (covariance_trace w u).trans ht
      _ = _ := by simp
  have he (j : Fin (Module.finrank ℝ E)) : eigenvalues w u j = largest w u :=
    (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ eigenvalue_le_largest w u j)).mp hsum j
      (Finset.mem_univ j)
  apply (basis w u).toBasis.ext
  intro j
  have hh := (symmetric w u).apply_eigenvectorBasis rfl j
  change covariance w u (basis w u j) = eigenvalues w u j • basis w u j at hh
  change covariance w u (basis w u j) = largest w u • basis w u j
  rw [hh, he j]

/-- The weighted Cauchy-Schwarz slack is exactly a sum of nonnegative squared residuals. -/
theorem allocation_slack [Nonempty ι] (a p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    (∑ i, (a i - ((∑ j, a j) / (∑ j, p j)) * p i) ^ 2 / p i) =
      (∑ i, a i ^ 2 / p i) - (∑ i, a i) ^ 2 / (∑ i, p i) := by
  let t := (∑ j, a j) / (∑ j, p j)
  have he (i : ι) : (a i - t * p i) ^ 2 / p i =
      a i ^ 2 / p i - (2 * t) * a i + t ^ 2 * p i := by
    field_simp [(hp i).ne']
    ring
  change (∑ i, (a i - t * p i) ^ 2 / p i) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  dsimp [t]
  have hP : 0 < ∑ i, p i := Finset.sum_pos (fun i _ ↦ hp i) Finset.univ_nonempty
  field_simp [hP.ne']
  ring

/-- Vanishing Cauchy-Schwarz slack forces every row's allocation ratio. -/
theorem allocation_of_equality [Nonempty ι] (a p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (he : (∑ i, a i ^ 2 / p i) = (∑ i, a i) ^ 2 / (∑ i, p i)) :
    ∀ i, a i = ((∑ j, a j) / (∑ j, p j)) * p i := by
  have hz := allocation_slack a p hp
  rw [he, sub_self] at hz
  have hnon (i : ι) (_hi : i ∈ Finset.univ) :
      0 ≤ (a i - ((∑ j, a j) / (∑ j, p j)) * p i) ^ 2 / p i :=
    div_nonneg (sq_nonneg _) (hp i).le
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hz i (Finset.mem_univ i)
  have hs : (a i - ((∑ j, a j) / (∑ j, p j)) * p i) ^ 2 = 0 :=
    (div_eq_zero_iff.mp hi).resolve_right (hp i).ne'
  nlinarith [sq_nonneg (a i - ((∑ j, a j) / (∑ j, p j)) * p i)]

/-- With nonzero total leverage, the cost equality conditions are both necessary and sufficient. -/
theorem cost_equality_iff [Nonempty ι] (κ p : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (hB : 0 < B)
    (hd : 0 < Module.finrank ℝ E) (hbudget : (∑ i, p i) ≤ B)
    (hS : 0 < leverageSum κ u) :
    objective κ u p = leverageSum κ u ^ 2 / ((Module.finrank ℝ E : ℝ) * B) ↔
      (∑ i, p i) = B ∧
      covariance (fun i ↦ κ i / p i) u = objective κ u p • LinearMap.id ∧
      ∀ i, p i = (B / leverageSum κ u) * (Real.sqrt (κ i) * ‖u i‖) := by
  have hP : 0 < ∑ i, p i := Finset.sum_pos (fun i _ ↦ hp i) Finset.univ_nonempty
  have hdim : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  constructor
  · intro he
    let T := ∑ i, κ i / p i * ‖u i‖ ^ 2
    have hcs : leverageSum κ u ^ 2 ≤ T * (∑ i, p i) :=
      (div_le_iff₀ hP).mp (trace_cost_lower κ p u hκ hp)
    have ht : T ≤ (Module.finrank ℝ E : ℝ) * objective κ u p :=
      trace_le_dimension (fun i ↦ κ i / p i) u
        (fun i ↦ div_nonneg (hκ i) (hp i).le)
    have hvalue := (eq_div_iff (mul_pos hdim hB).ne').mp he
    have hTpos : 0 < T := by nlinarith
    have htb : T * B ≤ leverageSum κ u ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right ht hB.le
      nlinarith
    have hpb : T * (∑ i, p i) ≤ T * B :=
      mul_le_mul_of_nonneg_left hbudget hTpos.le
    have hused : (∑ i, p i) = B := by nlinarith
    have htrace : T = (Module.finrank ℝ E : ℝ) * objective κ u p := by
      rw [hused] at hcs
      nlinarith
    refine ⟨hused, isotropic_of_trace_equality _ u htrace, ?_⟩
    have heach (i : ι) : (Real.sqrt (κ i) * ‖u i‖) ^ 2 / p i =
        κ i / p i * ‖u i‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hκ i)]
      ring
    have hslack : (∑ i, (Real.sqrt (κ i) * ‖u i‖) ^ 2 / p i) =
        (∑ i, Real.sqrt (κ i) * ‖u i‖) ^ 2 / (∑ i, p i) := by
      simp_rw [heach]
      change T = leverageSum κ u ^ 2 / (∑ i, p i)
      apply (eq_div_iff hP.ne').mpr
      nlinarith
    have ha := allocation_of_equality (fun i ↦ Real.sqrt (κ i) * ‖u i‖) p hp hslack
    intro i
    have hi := ha i
    change Real.sqrt (κ i) * ‖u i‖ = (leverageSum κ u / (∑ i, p i)) * p i at hi
    rw [hused] at hi
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hS.ne').mpr
    field_simp [hB.ne'] at hi
    nlinarith
  · rintro ⟨hb, hiso, halloc⟩
    exact attained_cost_bound κ p u B (B / leverageSum κ u) (objective κ u p)
      hκ hp hB (div_pos hB hS) hd halloc hb hiso

/-- Zero total leverage means zero actual directional audit variance, regardless of budget use. -/
theorem zero_leverage_variance (κ p : ι → ℝ) (u : ι → E)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (hS : leverageSum κ u = 0) :
    objective κ u p = 0 := by
  have hn (i : ι) (_hi : i ∈ Finset.univ) : 0 ≤ Real.sqrt (κ i) * ‖u i‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have he (i : ι) : κ i = 0 ∨ u i = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hS i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hi with hk | hu
    · left
      have hh := Real.sq_sqrt (hκ i)
      rw [hk] at hh
      simpa using hh.symm
    · exact Or.inr (norm_eq_zero.mp hu)
  apply le_antisymm ?_ (objective_nonneg κ u p hκ hp)
  apply (AuditRayleighGeometry.largest_le_iff (fun i ↦ κ i / p i) u
    (fun i ↦ div_nonneg (hκ i) (hp i).le) 0).mpr
  intro a _ha
  have hz : (∑ i, κ i / p i * (inner ℝ a (u i)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rcases he i with hk | hu
    · simp [hk]
    · simp [hu]
  exact hz.le

/-- The complete equality classification retains the zero-leverage budget degeneracy. -/
theorem cost_equality_complete [Nonempty ι] (κ p : ι → ℝ) (u : ι → E) (B : ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hp : ∀ i, 0 < p i) (hB : 0 < B)
    (hd : 0 < Module.finrank ℝ E) (hbudget : (∑ i, p i) ≤ B) :
    objective κ u p = leverageSum κ u ^ 2 / ((Module.finrank ℝ E : ℝ) * B) ↔
      leverageSum κ u = 0 ∨ ((∑ i, p i) = B ∧
        covariance (fun i ↦ κ i / p i) u = objective κ u p • LinearMap.id ∧
        ∀ i, p i = (B / leverageSum κ u) * (Real.sqrt (κ i) * ‖u i‖)) := by
  by_cases hz : leverageSum κ u = 0
  · simp [hz, zero_leverage_variance κ p u hκ hp hz]
  · have hn : 0 ≤ leverageSum κ u := Finset.sum_nonneg
      (fun i _ ↦ mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    simpa only [hz, false_or] using cost_equality_iff κ p u B hκ hp hB hd hbudget
      (lt_of_le_of_ne hn (Ne.symm hz))

end Descent.Portability.SpectralCostEquality
