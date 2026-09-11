/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IIDBinExperiment

assert_below Descent.Decision Descent.Program

/-!
The fixed-bin calibration certificate for an arbitrary finite joint law of bins
and binary labels. Bin masses and conditional event rates are recovered from
that law, and an exact reconstruction connects it to the iid validation experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteBinCalibrationLaw

open scoped BigOperators
open MeasureTheory HWEInteractionLaw IIDBinExperiment FixedBinHoeffdingLaw

variable {K : ℕ}

/-- The observed bin marginal of the supplied joint law. -/
noncomputable def binLaw (p : FiniteReportLaw (Fin K × Bool)) : FiniteReportLaw (Fin K) where
  mass j := ∑ b, p.mass (j, b)
  mass_nonneg j := Finset.sum_nonneg (fun b _ ↦ p.mass_nonneg (j, b))
  mass_sum := by rw [← Fintype.sum_prod_type]; exact p.mass_sum

theorem bin_mass (p : FiniteReportLaw (Fin K × Bool)) (j : Fin K) :
    (binLaw p).mass j = p.mass (j, false) + p.mass (j, true) := by simp [binLaw, add_comm]

/-- On positive-mass bins this is the conditional event probability. Values on
zero-mass bins have no effect on the reconstructed joint law or its reports. -/
noncomputable def rate (p : FiniteReportLaw (Fin K × Bool)) (j : Fin K) : ℝ :=
  p.mass (j, true) / (binLaw p).mass j

theorem rate_bounds (p : FiniteReportLaw (Fin K × Bool)) (j : Fin K) :
    0 ≤ rate p j ∧ rate p j ≤ 1 := by
  have hb := (binLaw p).mass_nonneg j
  have ht := p.mass_nonneg (j, true)
  refine ⟨div_nonneg ht hb, ?_⟩
  by_cases hz : (binLaw p).mass j = 0
  · simp [rate, hz]
  · apply (div_le_one (lt_of_le_of_ne hb (Ne.symm hz))).mpr
    rw [bin_mass]
    linarith [p.mass_nonneg (j, false)]

theorem mass_mul_rate (p : FiniteReportLaw (Fin K × Bool)) (j : Fin K) :
    (binLaw p).mass j * rate p j = p.mass (j, true) := by
  by_cases hz : (binLaw p).mass j = 0
  · have ht : p.mass (j, true) = 0 := by
      have he := bin_mass p j
      linarith [p.mass_nonneg (j, false), p.mass_nonneg (j, true)]
    simp [hz, ht]
  · unfold rate
    field_simp

/-- Every binary bin law is exactly recovered from its marginal and conditional rates. -/
theorem row_reconstruction (p : FiniteReportLaw (Fin K × Bool)) :
    rowLaw (binLaw p) (rate p) (rate_bounds p) = p := by
  apply FiniteReportLaw.ext
  rintro ⟨j, b⟩
  cases b
  · change (binLaw p).mass j * (1 - rate p j) = p.mass (j, false)
    rw [mul_sub, mul_one, mass_mul_rate, bin_mass]
    ring
  · exact mass_mul_rate p j

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The failure probability bound applies to iid draws from the supplied joint law itself. -/
theorem iid_miss_probability (p : FiniteReportLaw (Fin K × Bool)) (hK : 0 < K)
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (FiniteDiscreteMeasure.measure (independentLaw (fun _ : I ↦ p))).real
      {sample | Miss (fun i ↦ (sample i).1) (rate p) α (fun i ↦ (sample i).2)} ≤ α := by
  have h := iid_confidence (I := I) hK (binLaw p) (rate p) (rate_bounds p) α hα
  simpa only [sampleLaw, row_reconstruction] using h

/-- Simultaneous coverage at least 1-α, with the actual random nonempty-bin counts. -/
theorem simultaneous_coverage (p : FiniteReportLaw (Fin K × Bool)) (hK : 0 < K)
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    1 - α ≤ (FiniteDiscreteMeasure.measure (independentLaw (fun _ : I ↦ p))).real
      {sample | ∀ j : Fin K, 0 < (binRows (fun i ↦ (sample i).1) j).card →
        |(∑ i ∈ binRows (fun i ↦ (sample i).1) j, label (sample i).2) /
          (binRows (fun i ↦ (sample i).1) j).card - rate p j| ≤
            radius K (binRows (fun i ↦ (sample i).1) j).card α} := by
  let bad : Set (I → Fin K × Bool) :=
    {sample | Miss (fun i ↦ (sample i).1) (rate p) α (fun i ↦ (sample i).2)}
  have hset : {sample : I → Fin K × Bool |
      ∀ j : Fin K, 0 < (binRows (fun i ↦ (sample i).1) j).card →
        |(∑ i ∈ binRows (fun i ↦ (sample i).1) j, label (sample i).2) /
          (binRows (fun i ↦ (sample i).1) j).card - rate p j| ≤
            radius K (binRows (fun i ↦ (sample i).1) j).card α} = badᶜ := by
    ext sample
    simp only [bad, Set.mem_setOf_eq, Set.mem_compl_iff, Miss, not_exists, not_and, not_lt]
  rw [hset, measureReal_compl (Set.toFinite bad).measurableSet]
  have huniv : (FiniteDiscreteMeasure.measure (independentLaw (fun _ : I ↦ p))).real
      Set.univ = 1 := by simp [Measure.real]
  rw [huniv]
  have h := iid_miss_probability (I := I) p hK α hα
  linarith

/-- Clipping the confidence interval to [0,1] preserves coverage of the true bin rate. -/
theorem clipped_coverage (η estimate δ : ℝ) (hη : 0 ≤ η ∧ η ≤ 1)
    (herror : |estimate - η| ≤ δ) :
    η ∈ Set.Icc (max 0 (estimate - δ)) (min 1 (estimate + δ)) := by
  have h := abs_le.mp herror
  exact ⟨max_le hη.1 (by linarith), le_min hη.2 (by linarith)⟩

end Descent.Portability.FiniteBinCalibrationLaw
