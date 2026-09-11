/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWELayerPartition
import Descent.Portability.HWEPatternAmplitude
import Descent.Portability.RademacherReindex

assert_below Descent.Decision Descent.Program

/-!
The actual homogeneous HWE count-layer law, for every finite interaction order.
Its probability is the binomial mass and its conditional amplitude is represented
on exactly m-r independent fair signs. Both statements are derived from the
original genotype experiment, rather than supplied conditional distributions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEHomogeneousLayer

open scoped BigOperators
open Foundations HWEInteractionLaw HWEHeterozygosityLaw HWEPatternConditioning
open HWEPatternAmplitude HWELayerPartition HWELogCoordinates
open RademacherArrayWeakLimit RademacherParityLaw RademacherReindex BalancedHWEWeakLimit

/-- Exact scaled interaction amplitude on a layer with r heterozygotes among m loci. -/
noncomputable def layerAmplitude (h : HardyWeinbergModel) (m r : ℕ) (c : ℝ)
    (b : Fin (m - r) → Bool) : ℝ :=
  c * h.standardizedGenotype .het ^ r * Real.sqrt 2 ^ (m - r) * parity b *
    Real.exp (-weightedSum (fun _ ↦ coordinate (h.altFreq - 1 / 2)) b)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Homogeneous frequencies reduce the amplitude's pattern dependence to its cardinality. -/
theorem homogeneous_pattern_amplitude (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (s : Finset ι)
    (b : {i // i ∉ s} → Bool) :
    interaction (fun _ : ι ↦ h) (patternVector s b) =
      h.standardizedGenotype .het ^ s.card * Real.sqrt 2 ^ (Fintype.card ι - s.card) *
        parity b * Real.exp (-weightedSum (fun _ ↦ coordinate (h.altFreq - 1 / 2)) b) := by
  simpa [Fintype.card_subtype_compl] using
    interaction_pattern_amplitude (fun _ : ι ↦ h) (fun _ ↦ h0) (fun _ ↦ h1) s b

/-- Every size-r pattern has the same actual amplitude law on m-r fair signs. -/
theorem pattern_statistic (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (s : Finset ι)
    (r : ℕ) (hs : s.card = r) (c : ℝ) (f : ℝ → ℝ) :
    (independentLaw (fun _ : {i // i ∉ s} ↦ signLaw)).expectation
      (fun b ↦ f (c * interaction (fun _ : ι ↦ h) (patternVector s b))) =
        (independentLaw (fun _ : Fin (Fintype.card ι - r) ↦ signLaw)).expectation
          (fun b ↦ f (layerAmplitude h (Fintype.card ι) r c b)) := by
  let e : {i // i ∉ s} ≃ Fin (Fintype.card ι - r) :=
    (Fintype.equivFin _).trans (finCongr (by simp [Fintype.card_subtype_compl, hs]))
  have he (b : {i // i ∉ s} → Bool) :
      c * interaction (fun _ : ι ↦ h) (patternVector s b) =
        (c * h.standardizedGenotype .het ^ r * Real.sqrt 2 ^ (Fintype.card ι - r)) *
          parity b * Real.exp (-weightedSum (fun _ ↦ coordinate (h.altFreq - 1 / 2)) b) := by
    rw [homogeneous_pattern_amplitude h h0 h1, hs]
    ring
  simp only [he, layerAmplitude]
  exact amplitude_expectation_reindex e _ _ f

/-- Exact count-layer expectation for every real statistic of the original scaled interaction. -/
theorem homogeneous_layer_statistic (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (r : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    (independentLaw (fun _ : ι ↦ squareBiasedLocus h h0 h1)).expectation
      (fun x ↦ if count x = (r : ℝ) then f (c * interaction (fun _ : ι ↦ h) x) else 0) =
        (((Fintype.card ι).choose r : ℝ) * probability h ^ r *
          (1 - probability h) ^ (Fintype.card ι - r)) *
            (independentLaw (fun _ : Fin (Fintype.card ι - r) ↦ signLaw)).expectation
              (fun b ↦ f (layerAmplitude h (Fintype.card ι) r c b)) := by
  rw [← homogeneous_count_mass (ι := ι) h h0 h1 r]
  rw [layer_expectation (fun _ : ι ↦ h) (fun _ ↦ h0) (fun _ ↦ h1) r
    (fun x ↦ f (c * interaction (fun _ : ι ↦ h) x))]
  rw [layer_expectation (fun _ : ι ↦ h) (fun _ ↦ h0) (fun _ ↦ h1) r (fun _ ↦ 1)]
  simp only [FiniteIndependentMoments.expectation_const, mul_one, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.card = r
  · simp only [hs, if_true]
    rw [pattern_statistic h h0 h1 s r hs c f]
  · simp only [hs, if_false, zero_mul]

end Descent.Portability.HWEHomogeneousLayer
