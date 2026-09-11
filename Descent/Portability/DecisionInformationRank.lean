/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservableClosureLaw
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 2. Identification by linear mean
summaries on any nonempty open admissible set is equivalent to kernel
inclusion and linear factorization. The exact minimum number of scalar
linear summaries is the rank of the decision map, with an explicit basis
construction attaining it. The open-domain necessity argument tests actual
nearby admissible means; it does not assume arbitrary signed vectors are
valid mean vectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DecisionInformationRank

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Equal observed summaries force equal decision contrasts throughout the admissible domain. -/
def IdentifiesOn (S : Set V) (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, A x = A y → B x = B y

/-- Kernel inclusion suffices on every admissible domain, with no openness assumption. -/
theorem identifies_of_kernel (S : Set V) (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F)
    (hker : LinearMap.ker A ≤ LinearMap.ker B) : IdentifiesOn S A B := by
  intro x _ y _ hxy
  have ha : x - y ∈ LinearMap.ker A := by simpa only [LinearMap.mem_ker, map_sub, hxy, sub_self]
  have hb := hker ha
  simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using hb

/-- An open set contains a nonzero multiple of every direction around any one of its points. -/
theorem small_admissible_shift (S : Set V) (hS : IsOpen S) (x : V) (hx : x ∈ S) (v : V) :
    ∃ t : ℝ, 0 < t ∧ x + t • v ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hx
  let t := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have ht : 0 < t := div_pos hε hden
  refine ⟨t, ht, hball ?_⟩
  change dist (x + t • v) x < ε
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have he : t * (‖v‖ + 1) = ε := div_mul_cancel₀ ε hden.ne'
  nlinarith

/-- Identification on an actual open mean domain rules out every invisible decision direction. -/
theorem kernel_of_identifies (S : Set V) (hS : IsOpen S) (hne : S.Nonempty)
    (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) (hid : IdentifiesOn S A B) :
    LinearMap.ker A ≤ LinearMap.ker B := by
  obtain ⟨x, hx⟩ := hne
  intro v hv
  have ha : A v = 0 := hv
  obtain ⟨t, ht, hy⟩ := small_admissible_shift S hS x hx v
  have he : A x = A (x + t • v) := by rw [map_add, map_smul, ha, smul_zero, add_zero]
  have hh := hid x hx (x + t • v) hy he
  rw [map_add, map_smul] at hh
  have hz : t • B v = 0 := by
    apply add_left_cancel (a := B x)
    simpa only [add_zero] using hh.symm
  exact (smul_eq_zero.mp hz).resolve_left ht.ne'

/-- Exact observational identification is equivalent to the linear algebraic kernel condition. -/
theorem identifies_iff_kernel (S : Set V) (hS : IsOpen S) (hne : S.Nonempty)
    (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) :
    IdentifiesOn S A B ↔ LinearMap.ker A ≤ LinearMap.ker B :=
  ⟨kernel_of_identifies S hS hne A B, identifies_of_kernel S A B⟩

/-- Every determining linear summary admits an actual linear reconstruction of all contrasts. -/
theorem identifies_iff_factorization (S : Set V) (hS : IsOpen S) (hne : S.Nonempty)
    (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) :
    IdentifiesOn S A B ↔ ∃ C : E →ₗ[ℝ] F, C.comp A = B := by
  rw [identifies_iff_kernel S hS hne A B, ObservableClosureLaw.linear_factorization_iff]

variable [FiniteDimensional ℝ F]

/-- Every determining finite-dimensional summary has at least the rank of the decision map. -/
theorem summary_dimension_lower [FiniteDimensional ℝ E]
    (S : Set V) (hS : IsOpen S) (hne : S.Nonempty)
    (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) (hid : IdentifiesOn S A B) :
    Module.finrank ℝ (LinearMap.range B) ≤ Module.finrank ℝ E := by
  obtain ⟨C, hC⟩ := (identifies_iff_factorization S hS hne A B).mp hid
  have hrange : LinearMap.range B ≤ LinearMap.range C := by
    rw [← hC]
    exact LinearMap.range_comp_le_range _ _
  exact (Submodule.finrank_mono hrange).trans C.finrank_range_le

/-- A basis of the target range gives exactly rank-many scalar linear summaries. -/
noncomputable def minimalSummary (B : V →ₗ[ℝ] F) :
    V →ₗ[ℝ] (Fin (Module.finrank ℝ (LinearMap.range B)) → ℝ) :=
  (Module.finBasis ℝ (LinearMap.range B)).equivFun.toLinearMap.comp B.rangeRestrict

/-- The constructed rank-many summaries determine every contrast on every admissible domain. -/
theorem minimalSummary_identifies (S : Set V) (B : V →ₗ[ℝ] F) :
    IdentifiesOn S (minimalSummary B) B := by
  intro x _ y _ hxy
  have he : B.rangeRestrict x = B.rangeRestrict y :=
    (Module.finBasis ℝ (LinearMap.range B)).equivFun.injective hxy
  exact congrArg Subtype.val he

/-- The minimum number of scalar linear mean summaries is exactly the decision-map rank. -/
theorem exact_summary_count (S : Set V) (hS : IsOpen S) (hne : S.Nonempty)
    (B : V →ₗ[ℝ] F) :
    IsLeast {q : ℕ | ∃ A : V →ₗ[ℝ] (Fin q → ℝ), IdentifiesOn S A B}
      (Module.finrank ℝ (LinearMap.range B)) := by
  refine ⟨⟨minimalSummary B, minimalSummary_identifies S B⟩, ?_⟩
  rintro q ⟨A, hA⟩
  have hh := summary_dimension_lower S hS hne A B hA
  simpa using hh

end Descent.Portability.DecisionInformationRank
