/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.InterleavedMutationExponential
import Descent.Portability.StoppedAncestralTiming

assert_below Descent.Decision Descent.Program

/-!
Integrating mutation proposal counts up to an independent exponential
ancestry proposal produces the geometric event-race coefficients. This is
the scalar analytic input for comparing timed ancestry with joint transfer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExponentialPoissonRace

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

/-- The exact gamma integral underlying the event-race expansion. -/
theorem poisson_race_integral (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (count : ℕ) :
    (∫ time : ℝ in Ioi 0,
      ancestry * Real.exp (-(ancestry * time)) *
        (Real.exp (-((mutation : ℝ) * time)) * ((mutation : ℝ) * time) ^ count /
          (count.factorial : ℝ))) =
      ancestry * (mutation : ℝ) ^ count /
        (ancestry + (mutation : ℝ)) ^ (count + 1) := by
  have hsum : 0 < ancestry + (mutation : ℝ) := add_pos_of_pos_of_nonneg ha mutation.property
  have heq (time : ℝ) :
      ancestry * Real.exp (-(ancestry * time)) *
          (Real.exp (-((mutation : ℝ) * time)) * ((mutation : ℝ) * time) ^ count /
            (count.factorial : ℝ)) =
        (ancestry * (mutation : ℝ) ^ count / (count.factorial : ℝ)) *
          (time ^ count * Real.exp (-((ancestry + (mutation : ℝ)) * time))) := by
    rw [mul_pow]
    have hexp : Real.exp (-((ancestry + (mutation : ℝ)) * time)) =
        Real.exp (-(ancestry * time)) * Real.exp (-((mutation : ℝ) * time)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (count : ℝ) + 1) (by positivity) hsum
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hgamma
  rw [hgamma, Real.Gamma_nat_eq_factorial]
  rw [show (count : ℝ) + 1 = ((count + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast]
  have hf : (count.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, one_pow]
  field_simp

/-- Expected Poisson count probability under the actual exponential wait law. -/
theorem poisson_expMeasure (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (count : ℕ) :
    (∫ time : ℝ, poissonPMFReal (mutation * Real.toNNReal time) count
      ∂expMeasure ancestry) =
      ancestry * (mutation : ℝ) ^ count /
        (ancestry + (mutation : ℝ)) ^ (count + 1) := by
  change (∫ time : ℝ, poissonPMFReal (mutation * Real.toNNReal time) count
    ∂volume.withDensity (exponentialPDF ancestry)) = _
  have hm : Measurable (exponentialPDF ancestry) :=
    (measurable_exponentialPDFReal ancestry).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hp (time : ℝ) :
      (exponentialPDF ancestry time).toReal •
          poissonPMFReal (mutation * Real.toNNReal time) count =
        (Ici (0 : ℝ)).indicator (fun time ↦
          ancestry * Real.exp (-(ancestry * time)) *
            (Real.exp (-((mutation : ℝ) * time)) * ((mutation : ℝ) * time) ^ count /
              (count.factorial : ℝ))) time := by
    by_cases ht : 0 ≤ time
    · simp [exponentialPDF_of_nonneg ht, ENNReal.toReal_ofReal (by positivity :
          0 ≤ ancestry * Real.exp (-(ancestry * time))), smul_eq_mul,
        Set.indicator, ht, poissonPMFReal, Real.coe_toNNReal time ht]
    · simp [exponentialPDF_of_neg (lt_of_not_ge ht), Set.indicator, ht]
  simp_rw [hp]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact poisson_race_integral ancestry ha mutation count

noncomputable def raceCoefficient (ancestry : ℝ) (mutation : ℝ≥0) (count : ℕ) : ℝ :=
  ancestry * (mutation : ℝ) ^ count / (ancestry + (mutation : ℝ)) ^ (count + 1)

theorem raceCoefficient_geometric (ancestry : ℝ) (mutation : ℝ≥0) (count : ℕ) :
    raceCoefficient ancestry mutation count =
      (ancestry / (ancestry + (mutation : ℝ))) *
        ((mutation : ℝ) / (ancestry + (mutation : ℝ))) ^ count := by
  simp only [raceCoefficient, pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

theorem raceCoefficient_summable (ancestry : ℝ) (ha : 0 < ancestry) (mutation : ℝ≥0) :
    Summable (raceCoefficient ancestry mutation) := by
  have hp : 0 < ancestry + (mutation : ℝ) := add_pos_of_pos_of_nonneg ha mutation.property
  have hratio : (mutation : ℝ) / (ancestry + (mutation : ℝ)) < 1 := by
    rw [div_lt_one hp]
    linarith
  change Summable (fun count ↦ raceCoefficient ancestry mutation count)
  simp_rw [raceCoefficient_geometric]
  exact (summable_geometric_of_lt_one (div_nonneg mutation.property hp.le) hratio).mul_left _

theorem poisson_coefficient_integrable (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (count : ℕ) :
    Integrable (fun time : ℝ ↦ poissonPMFReal (mutation * Real.toNNReal time) count)
      (expMeasure ancestry) := by
  letI := isProbabilityMeasure_expMeasure ha
  have hm : Measurable (fun time : ℝ ↦ poissonPMFReal (mutation * Real.toNNReal time) count) := by
    have hex : Measurable (fun time : ℝ ↦ (mutation : ℝ) * max time 0) := by fun_prop
    simpa only [poissonPMFReal, NNReal.coe_mul, Real.coe_toNNReal'] using
      ((hex.neg.exp).mul (hex.pow_const count)).div_const (count.factorial : ℝ)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro time
  rw [Real.norm_eq_abs, abs_of_nonneg poissonPMFReal_nonneg]
  have h := (poissonPMFRealSum (mutation * Real.toNNReal time)).summable.le_tsum
    count (fun _ _ ↦ poissonPMFReal_nonneg)
  rwa [(poissonPMFRealSum _).tsum_eq] at h

/-- Integration and summation can be interchanged for every bounded
nonnegative count readout; the result is the geometric race series. -/
theorem poisson_series_expMeasure (ancestry : ℝ) (ha : 0 < ancestry) (mutation : ℝ≥0)
    (readout : ℕ → ℝ) (hreadout : ∀ count, 0 ≤ readout count ∧ readout count ≤ 1) :
    (∫ time : ℝ, ∑' count,
      poissonPMFReal (mutation * Real.toNNReal time) count * readout count
        ∂expMeasure ancestry) =
      ∑' count, raceCoefficient ancestry mutation count * readout count := by
  have hint (count : ℕ) :=
    (poisson_coefficient_integrable ancestry ha mutation count).mul_const (readout count)
  have hsum : Summable (fun count ↦ ∫ time : ℝ,
      ‖poissonPMFReal (mutation * Real.toNNReal time) count * readout count‖
        ∂expMeasure ancestry) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg poissonPMFReal_nonneg (hreadout _).1), integral_mul_const,
      poisson_expMeasure ancestry ha]
    apply (raceCoefficient_summable ancestry ha mutation).of_nonneg_of_le
    · intro count
      exact mul_nonneg (by positivity) (hreadout count).1
    · intro count
      exact mul_le_of_le_one_right (by positivity) (hreadout count).2
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_mul_const, poisson_expMeasure ancestry ha, raceCoefficient]

open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue
open InterleavedMutationLaw InterleavedMutationMeasurability InterleavedMutationExponential

/-- A fixed proposal kernel can be used at every duration. The Poisson mean
scales with duration, including its null proposals, while the physical law
agrees exactly with the original exposure-parameterized construction. -/
theorem interval_fixed_uniformization {n count : ℕ} (templates : Fin count → Branch n)
    (rates : Fin count → ℝ≥0) (duration : ℝ≥0) (source target : SiteState n) :
    (intervalLaw (replaceExposure templates (fun index ↦ duration * rates index)) source).mass
        target =
      ∑' proposals, poissonPMFReal
          (duration * proposalParameter (replaceExposure templates rates)) proposals *
        (countLaw (replaceExposure templates rates) source proposals).mass target := by
  simp only [countLaw, propagate_mass]
  rw [poisson_matrix_exponential, interval_matrix_exponential, physicalGenerator_scale]
  simp only [NNReal.coe_mul, ← smul_smul, generator_matrix]

/-- The complete catalogue transition over an exponential ancestry wait has
an exact geometric proposal-count expansion. -/
theorem interval_expMeasure {n count : ℕ} (templates : Fin count → Branch n)
    (rates : Fin count → ℝ≥0) (ancestry : ℝ) (ha : 0 < ancestry)
    (source target : SiteState n) :
    (∫ time : ℝ, FiniteReportLaw.mass
      (intervalLaw (replaceExposure templates
        (fun index ↦ Real.toNNReal time * rates index)) source) target
        ∂expMeasure ancestry) =
      ∑' proposals, raceCoefficient ancestry
          (proposalParameter (replaceExposure templates rates)) proposals *
        (countLaw (replaceExposure templates rates) source proposals).mass target := by
  simp_rw [interval_fixed_uniformization]
  simp only [mul_comm (Real.toNNReal _)]
  apply poisson_series_expMeasure ancestry ha
  intro proposals
  constructor
  · exact (countLaw _ source proposals).mass_nonneg target
  · rw [← (countLaw (replaceExposure templates rates) source proposals).mass_sum]
    exact Finset.single_le_sum (fun output _ ↦ (countLaw _ source proposals).mass_nonneg output)
      (Finset.mem_univ target)

theorem raceCoefficient_sum (ancestry : ℝ) (ha : 0 < ancestry) (mutation : ℝ≥0) :
    (∑' count, raceCoefficient ancestry mutation count) = 1 := by
  have hp : 0 < ancestry + (mutation : ℝ) := add_pos_of_pos_of_nonneg ha mutation.property
  have hratio : (mutation : ℝ) / (ancestry + (mutation : ℝ)) < 1 := by
    rw [div_lt_one hp]
    linarith
  simp_rw [raceCoefficient_geometric]
  rw [tsum_mul_left]
  have hgeo : (∑' k : ℕ, ((mutation : ℝ) / (ancestry + (mutation : ℝ))) ^ k) =
      (1 - (mutation : ℝ) / (ancestry + (mutation : ℝ)))⁻¹ :=
    tsum_geometric_of_lt_one (div_nonneg mutation.property hp.le) hratio
  rw [hgeo]
  field_simp [ne_of_gt ha, ne_of_gt hp]
  ring

theorem raceCoefficient_succ (ancestry : ℝ) (mutation : ℝ≥0) (count : ℕ) :
    raceCoefficient ancestry mutation (count + 1) =
      ((mutation : ℝ) / (ancestry + (mutation : ℝ))) *
        raceCoefficient ancestry mutation count := by
  simp only [raceCoefficient_geometric, pow_succ]
  ring

variable {S : Type*} [Fintype S]

noncomputable def kernelCount (kernel : S → FiniteReportLaw S) (source : S) (count : ℕ) :
    FiniteReportLaw S :=
  ExactFiniteHistoryLaw.propagate (pointMass source) (fun _ ↦ kernel) count

private theorem race_coordinate_summable (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (kernel : S → FiniteReportLaw S) (source target : S) :
    Summable (fun count ↦
      raceCoefficient ancestry mutation count * (kernelCount kernel source count).mass target) := by
  apply (raceCoefficient_summable ancestry ha mutation).of_nonneg_of_le
  · intro count
    exact mul_nonneg (by unfold raceCoefficient; positivity)
      ((kernelCount kernel source count).mass_nonneg target)
  · intro count
    apply mul_le_of_le_one_right (by unfold raceCoefficient; positivity)
    rw [← (kernelCount kernel source count).mass_sum]
    exact Finset.single_le_sum (fun output _ ↦
      (kernelCount kernel source count).mass_nonneg output) (Finset.mem_univ target)

/-- The normalized transition before the independent ancestry proposal. -/
noncomputable def raceKernelLaw (ancestry : ℝ) (ha : 0 < ancestry) (mutation : ℝ≥0)
    (kernel : S → FiniteReportLaw S) (source : S) : FiniteReportLaw S where
  mass := fun target ↦ ∑' count,
    raceCoefficient ancestry mutation count * (kernelCount kernel source count).mass target
  mass_nonneg := fun target ↦ tsum_nonneg (fun count ↦
    mul_nonneg (by unfold raceCoefficient; positivity)
      ((kernelCount kernel source count).mass_nonneg target))
  mass_sum := by
    rw [← Summable.tsum_finsetSum
      (fun target _ ↦ race_coordinate_summable ancestry ha mutation kernel source target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact raceCoefficient_sum ancestry ha mutation

/-- Exact first-event recurrence, with mutation proposals composed after the
older state. This identity includes all arbitrarily long proposal histories. -/
theorem raceKernel_first_step (ancestry : ℝ) (ha : 0 < ancestry) (mutation : ℝ≥0)
    (kernel : S → FiniteReportLaw S) (source target : S) :
    (raceKernelLaw ancestry ha mutation kernel source).mass target =
      (ancestry / (ancestry + (mutation : ℝ))) * (pointMass source).mass target +
        ((mutation : ℝ) / (ancestry + (mutation : ℝ))) *
          ((raceKernelLaw ancestry ha mutation kernel source).bind kernel).mass target := by
  change (∑' count, raceCoefficient ancestry mutation count *
    (kernelCount kernel source count).mass target) = _
  rw [(race_coordinate_summable ancestry ha mutation kernel source target).tsum_eq_zero_add]
  simp only [raceCoefficient_succ]
  have hzero : raceCoefficient ancestry mutation 0 =
      ancestry / (ancestry + (mutation : ℝ)) := by simp [raceCoefficient]
  rw [hzero]
  congr 1
  simp only [kernelCount, ExactFiniteHistoryLaw.propagate]
  simp only [mul_assoc, tsum_mul_left]
  congr 1
  change (∑' count, raceCoefficient ancestry mutation count *
      ∑ middle, (kernelCount kernel source count).mass middle * (kernel middle).mass target) =
    ∑ middle, (∑' count, raceCoefficient ancestry mutation count *
      (kernelCount kernel source count).mass middle) * (kernel middle).mass target
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun middle _ ↦
    (race_coordinate_summable ancestry ha mutation kernel source middle).mul_right
      ((kernel middle).mass target))]
  apply tsum_congr
  intro count
  simp only [Finset.mul_sum, mul_assoc]

/-- Integrating any finite stochastic semigroup against an exponential wait
is exactly the normalized geometric resolvent used in the first-step law. -/
theorem kernel_exponential_expMeasure [DecidableEq S] (ancestry : ℝ) (ha : 0 < ancestry)
    (mutation : ℝ≥0) (kernel : S → FiniteReportLaw S) (source target : S) :
    (∫ time : ℝ, (NormedSpace.exp ℝ
      (((mutation * Real.toNNReal time : ℝ≥0) : ℝ) • (kernelMatrix kernel - 1))) source target
        ∂expMeasure ancestry) =
      (raceKernelLaw ancestry ha mutation kernel source).mass target := by
  simp_rw [← poisson_matrix_exponential]
  have hcount (proposals : ℕ) : (kernelMatrix kernel ^ proposals) source target =
      (kernelCount kernel source proposals).mass target :=
    (propagate_mass kernel proposals source target).symm
  simp_rw [hcount]
  apply poisson_series_expMeasure ancestry ha
  intro count
  constructor
  · exact (kernelCount kernel source count).mass_nonneg target
  · rw [← (kernelCount kernel source count).mass_sum]
    exact Finset.single_le_sum (fun output _ ↦
      (kernelCount kernel source count).mass_nonneg output) (Finset.mem_univ target)

theorem interval_expMeasure_eq_raceKernelLaw {n count : ℕ}
    (templates : Fin count → Branch n) (rates : Fin count → ℝ≥0)
    (ancestry : ℝ) (ha : 0 < ancestry) (source target : SiteState n) :
    (∫ time : ℝ, FiniteReportLaw.mass
      (intervalLaw (replaceExposure templates
        (fun index ↦ Real.toNNReal time * rates index)) source) target
        ∂expMeasure ancestry) =
      (raceKernelLaw ancestry ha (proposalParameter (replaceExposure templates rates))
        (intervalKernel (replaceExposure templates rates)) source).mass target := by
  exact interval_expMeasure templates rates ancestry ha source target

end Descent.Portability.ExponentialPoissonRace
