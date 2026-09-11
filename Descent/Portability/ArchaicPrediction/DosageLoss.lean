/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Moments
import Descent.Portability.ArchaicPrediction.Dimension

assert_below Descent.Decision Descent.Program

/-!
# Exact phase information lost by dosage-only prediction

The scalar dosage vector is fixed across a phase fiber. Any predictor using
only that vector therefore supplies a constant on the fiber. These theorems
identify its optimal constant and exact irreducible error. For invariant
responses, uniform cube measure pushes forward to uniform unordered phases.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem phase_mean (c : Finset I → ℝ) :
    cubeMean (fun _ : I => 1 / 2) (phaseExpansion c) = c ∅ := by
  simpa [phaseCharacter] using phase_coefficient c ∅

/-- Parseval with the constant removed is exactly the phase-response variance. -/
theorem uniform_phase_variance (c : Finset I → ℝ) :
    cubeMean (fun _ : I => 1 / 2) (fun x => (phaseExpansion c x - c ∅) ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset I)).erase ∅, c S ^ 2 := by
  have hv := variance_as_second_moment (cubeWeight (fun _ : I => 1 / 2))
    (cubeWeight_sum _) (phaseExpansion c)
  change cubeMean _ (fun x => (phaseExpansion c x - cubeMean _ (phaseExpansion c)) ^ 2) =
    cubeMean _ (fun x => phaseExpansion c x ^ 2) - cubeMean _ (phaseExpansion c) ^ 2 at hv
  rw [phase_mean, phase_parseval] at hv
  rw [hv]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Finset I)) (fun S => c S ^ 2)
    (Finset.mem_univ ∅)
  linarith

/-- Theorem 4's dosage-only minimum and the exact excess risk of any other constant. -/
theorem dosage_only_phase_loss (c : Finset I → ℝ) (b : ℝ) :
    cubeMean (fun _ : I => 1 / 2) (fun x => (phaseExpansion c x - b) ^ 2) =
      (∑ S ∈ (Finset.univ : Finset (Finset I)).erase ∅, c S ^ 2) + (c ∅ - b) ^ 2 := by
  have h := best_constant_risk (cubeWeight (fun _ : I => 1 / 2))
    (cubeWeight_sum _) (phaseExpansion c) b
  change cubeMean _ (fun x => (phaseExpansion c x - b) ^ 2) =
    cubeMean _ (fun x => (phaseExpansion c x - cubeMean _ (phaseExpansion c)) ^ 2) +
      (cubeMean _ (phaseExpansion c) - b) ^ 2 at h
  simpa only [phase_mean, uniform_phase_variance] using h

theorem dosage_only_phase_minimum (c : Finset I → ℝ) :
    IsLeast (Set.range (fun b : ℝ => cubeMean (fun _ : I => 1 / 2)
      (fun x => (phaseExpansion c x - b) ^ 2)))
      (∑ S ∈ (Finset.univ : Finset (Finset I)).erase ∅, c S ^ 2) := by
  constructor
  · refine ⟨c ∅, ?_⟩
    change cubeMean (fun _ : I => 1 / 2) (fun x => (phaseExpansion c x - c ∅) ^ 2) = _
    rw [uniform_phase_variance]
  · rintro _ ⟨b, rfl⟩
    change _ ≤ cubeMean (fun _ : I => 1 / 2) (fun x => (phaseExpansion c x - b) ^ 2)
    rw [dosage_only_phase_loss]
    exact le_add_of_nonneg_right (sq_nonneg _)

end Descent.Portability.ArchaicPrediction
