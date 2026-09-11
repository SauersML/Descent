/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteSphereNet
import Descent.Portability.FiniteAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
The uniform probability step in Decision-Directed Portability, Theorem 10.
A proved finite cover converts scalar directional tails into a norm tail,
with precisely 5^dimension directions and the factor two in the manuscript.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteNetConfidence

open MeasureTheory FiniteSphereNet
open scoped BigOperators

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace Ω]

/-- Uniform directional tail bounds give the dimension-explicit vector tail bound. -/
theorem norm_tail (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → E)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (ht : ∀ a : E, ‖a‖ ≤ 1 → μ.real {ω | b < |inner ℝ a (Z ω)|} ≤ q) :
    μ.real {ω | 2 * b < ‖Z ω‖} ≤ (5 ^ Module.finrank ℝ E : ℕ) * q := by
  classical
  obtain ⟨s, _hne, hcard, hunit, hcover⟩ := exists_half_net (E := E)
  let bad (a : s) : Set Ω := {ω | b < |inner ℝ (a : E) (Z ω)|}
  have hsub : {ω | 2 * b < ‖Z ω‖} ⊆ ⋃ a : s, bad a := by
    intro ω hω
    by_contra hn
    have hdir : ∀ a ∈ s, |inner ℝ a (Z ω)| ≤ b := by
      intro a ha
      by_contra hh
      have hm : ω ∈ bad ⟨a, ha⟩ := lt_of_not_ge hh
      exact hn (Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hm⟩)
    exact (not_lt_of_ge (norm_le_twice s hcover (Z ω) b hb hdir)) hω
  calc
    μ.real {ω | 2 * b < ‖Z ω‖} ≤ μ.real (⋃ a : s, bad a) := measureReal_mono hsub
    _ ≤ ∑ a : s, μ.real (bad a) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _a : s, q := Finset.sum_le_sum (fun a _ ↦ ht a (hunit a a.property))
    _ = (s.card : ℝ) * q := by simp
    _ ≤ (5 ^ Module.finrank ℝ E : ℕ) * q := by
      apply mul_le_mul_of_nonneg_right _ hq
      exact_mod_cast hcard

/-- The logarithmic exponent pays for every net direction, including dimension zero. -/
theorem norm_confidence (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → E)
    (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 < δ)
    (ht : ∀ a : E, ‖a‖ ≤ 1 → μ.real {ω | b < |inner ℝ a (Z ω)|} ≤
      2 * Real.exp (-Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ))) :
    μ.real {ω | 2 * b < ‖Z ω‖} ≤ δ := by
  have hK : 0 < 5 ^ Module.finrank ℝ E := by positivity
  have hh := norm_tail μ Z b _ hb (by positivity) ht
  rw [FiniteAuditConfidence.confidence_tail_value _ hK δ hδ] at hh
  have hk : ((5 ^ Module.finrank ℝ E : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have he : ((5 ^ Module.finrank ℝ E : ℕ) : ℝ) *
      (δ / (5 ^ Module.finrank ℝ E : ℕ)) = δ := by field_simp
  rwa [he] at hh

end Descent.Portability.FiniteNetConfidence
