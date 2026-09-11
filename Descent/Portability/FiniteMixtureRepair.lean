/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionLossContrasts
import Mathlib.MeasureTheory.Integral.Bochner.Basic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 22: transport to actual mixtures of
unchanged group joint laws. Both separate squared losses are integrable.
The mixture is an explicitly constructed probability measure, and its
expected paired gain is exactly the mixture of group gains. No restriction
to disjoint groups or common conditional variances is imposed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteMixtureRepair

open MeasureTheory
open scoped BigOperators

variable {J Ω : Type*} [Fintype J] [MeasurableSpace Ω]

/-- The actual finite mixture of the supplied group joint laws. -/
noncomputable def mixture (π : J → ℝ) (μ : J → Measure Ω) : Measure Ω :=
  ∑ j, ENNReal.ofReal (π j) • μ j

/-- Nonnegative normalized mixture weights define an actual probability law. -/
theorem mixture_probability (π : J → ℝ) (μ : J → Measure Ω)
    [∀ j, IsProbabilityMeasure (μ j)] (hπ : ∀ j, 0 ≤ π j) (hsum : ∑ j, π j = 1) :
    IsProbabilityMeasure (mixture π μ) := by
  constructor
  simp only [mixture, Measure.finset_sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hπ j), hsum, ENNReal.ofReal_one]

/-- Groupwise integrability implies integrability under the actual mixture. -/
theorem mixture_integrable (π : J → ℝ) (μ : J → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ j, Integrable f (μ j)) : Integrable f (mixture π μ) := by
  unfold mixture
  exact integrable_finset_sum_measure.mpr (fun j _ ↦ (hf j).smul_measure ENNReal.ofReal_ne_top)

/-- Integration under the mixture equals the finite mixture of actual group integrals. -/
theorem mixture_integral (π : J → ℝ) (μ : J → Measure Ω) (f : Ω → ℝ)
    (hπ : ∀ j, 0 ≤ π j) (hf : ∀ j, Integrable f (μ j)) :
    (∫ x, f x ∂mixture π μ) = ∑ j, π j * ∫ x, f x ∂μ j := by
  unfold mixture
  rw [integral_finset_sum_measure (fun j _ ↦ (hf j).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (hπ _), smul_eq_mul]

/-- Prospective paired gain, defined using the two separate actual expected losses. -/
noncomputable def gain (μ : Measure Ω) (Y f d : Ω → ℝ) : ℝ :=
  (∫ x, (Y x - f x) ^ 2 ∂μ) - ∫ x, (Y x - (f x + d x)) ^ 2 ∂μ

/-- Both losses remain finite under every finite mixture of the same group laws. -/
theorem mixture_losses_integrable (π : J → ℝ) (μ : J → Measure Ω) (Y f d : Ω → ℝ)
    (hbase : ∀ j, Integrable (fun x ↦ (Y x - f x) ^ 2) (μ j))
    (hnew : ∀ j, Integrable (fun x ↦ (Y x - (f x + d x)) ^ 2) (μ j)) :
    Integrable (fun x ↦ (Y x - f x) ^ 2) (mixture π μ) ∧
      Integrable (fun x ↦ (Y x - (f x + d x)) ^ 2) (mixture π μ) :=
  ⟨mixture_integrable π μ _ hbase, mixture_integrable π μ _ hnew⟩

/-- Gain transports linearly between actual group laws and their actual mixture law. -/
theorem mixture_gain (π : J → ℝ) (μ : J → Measure Ω) (Y f d : Ω → ℝ)
    (hπ : ∀ j, 0 ≤ π j)
    (hbase : ∀ j, Integrable (fun x ↦ (Y x - f x) ^ 2) (μ j))
    (hnew : ∀ j, Integrable (fun x ↦ (Y x - (f x + d x)) ^ 2) (μ j)) :
    gain (mixture π μ) Y f d = ∑ j, π j * gain (μ j) Y f d := by
  unfold gain
  rw [mixture_integral π μ _ hπ hbase, mixture_integral π μ _ hπ hnew,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ ↦ by ring)

/-- Nonnegative gains in every unchanged group law ensure safety for every mixture weight vector. -/
theorem stable_mixture_safety (π : J → ℝ) (μ : J → Measure Ω)
    [∀ j, IsProbabilityMeasure (μ j)] (Y f d : Ω → ℝ)
    (hπ : ∀ j, 0 ≤ π j) (hsum : ∑ j, π j = 1)
    (hbase : ∀ j, Integrable (fun x ↦ (Y x - f x) ^ 2) (μ j))
    (hnew : ∀ j, Integrable (fun x ↦ (Y x - (f x + d x)) ^ 2) (μ j))
    (hsafe : ∀ j, 0 ≤ gain (μ j) Y f d) :
    IsProbabilityMeasure (mixture π μ) ∧ 0 ≤ gain (mixture π μ) Y f d := by
  refine ⟨mixture_probability π μ hπ hsum, ?_⟩
  rw [mixture_gain π μ Y f d hπ hbase hnew]
  exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hπ j) (hsafe j))

end Descent.Portability.FiniteMixtureRepair
