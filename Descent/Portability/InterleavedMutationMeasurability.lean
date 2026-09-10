/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.InterleavedMutationLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

assert_below Descent.Decision Descent.Program

/-!
Measurability of the derived mutation law as branch exposures vary. Clades and
representatives are fixed while their nonnegative exposures are measurable
functions of ancestry waiting times or other continuous inputs. Measurability
of the probability kernel is proved from its finite transitions and its
convergent Poisson series; it is not an additional kernel assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InterleavedMutationMeasurability

open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue InterleavedMutationLaw
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {n count : ℕ}

def replaceExposure (templates : Fin count → Branch n) (exposures : Fin count → ℝ≥0) :
    Fin count → Branch n :=
  fun index ↦ { templates index with exposure := exposures index }

theorem mutationKernel_replaceExposure (templates : Fin count → Branch n)
    (exposures : Fin count → ℝ≥0) (index : Fin count) (state : SiteState n) :
    mutationKernel (replaceExposure templates exposures index) state =
      mutationKernel (templates index) state := rfl

/-- Real-valued summable series of measurable terms are measurable. Coordinate
summability below supplies the required pointwise convergence. -/
theorem measurable_real_tsum {terms : ℕ → Ω → ℝ}
    (hmeas : ∀ index, Measurable (terms index))
    (hsum : ∀ input, Summable (fun index ↦ terms index input)) :
    Measurable (fun input ↦ ∑' index, terms index input) := by
  apply measurable_of_tendsto_metrizable
    (f := fun cutoff input ↦ ∑ index ∈ Finset.range cutoff, terms index input)
  · intro cutoff
    exact Finset.measurable_sum _ (fun index _ ↦ hmeas index)
  · rw [tendsto_pi_nhds]
    intro input
    exact (hsum input).hasSum.tendsto_sum_nat

theorem proposalParameter_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index)) :
    Measurable (fun input ↦
      (proposalParameter (replaceExposure templates (fun index ↦ exposure index input)) : ℝ)) := by
  simp only [proposalParameter_eq, replaceExposure]
  apply measurable_const.add
  exact Finset.measurable_sum _ (fun index _ ↦ measurable_subtype_coe.comp (hexposure index))

theorem mark_mass_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (mark : Option (Fin count)) :
    Measurable (fun input ↦
      (markLaw (replaceExposure templates (fun index ↦ exposure index input))).mass mark) := by
  cases mark with
  | none => exact measurable_const.div (proposalParameter_measurable templates exposure hexposure)
  | some index =>
      exact (measurable_subtype_coe.comp (hexposure index)).div
        (proposalParameter_measurable templates exposure hexposure)

theorem intervalKernel_mass_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state target : SiteState n) :
    Measurable (fun input ↦ FiniteReportLaw.mass
      (intervalKernel (replaceExposure templates (fun index ↦ exposure index input)) state)
        target) := by
  change Measurable (fun input ↦ ∑ mark,
    (markLaw (replaceExposure templates (fun index ↦ exposure index input))).mass mark *
      FiniteReportLaw.mass
        (markedKernel (replaceExposure templates (fun index ↦ exposure index input)) state mark)
          target)
  apply Finset.measurable_sum
  intro mark _
  apply (mark_mass_measurable templates exposure hexposure mark).mul
  cases mark with
  | none => exact measurable_const
  | some index =>
      simpa only [markedKernel, mutationKernel_replaceExposure] using
        (measurable_const : Measurable (fun _ : Ω ↦
          (mutationKernel (templates index) state).mass target))

theorem count_mass_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state target : SiteState n) (proposals : ℕ) :
    Measurable (fun input ↦ FiniteReportLaw.mass
      (countLaw (replaceExposure templates (fun index ↦ exposure index input)) state proposals)
        target) := by
  induction proposals generalizing target with
  | zero => exact measurable_const
  | succ proposals ih =>
      change Measurable (fun input ↦ ∑ middle,
        FiniteReportLaw.mass
          (countLaw (replaceExposure templates (fun index ↦ exposure index input)) state proposals)
            middle *
        FiniteReportLaw.mass
          (intervalKernel (replaceExposure templates (fun index ↦ exposure index input)) middle)
            target)
      apply Finset.measurable_sum
      intro middle _
      exact (ih middle).mul
        (intervalKernel_mass_measurable templates exposure hexposure middle target)

theorem poissonCoefficient_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (proposals : ℕ) :
    Measurable (fun input ↦ poissonPMFReal
      (proposalParameter (replaceExposure templates (fun index ↦ exposure index input)))
        proposals) := by
  have hp := proposalParameter_measurable templates exposure hexposure
  exact ((hp.neg.exp).mul (hp.pow_const proposals)).div_const _

theorem countContribution_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state target : SiteState n) (proposals : ℕ) :
    Measurable (fun input ↦ poissonPMFReal
      (proposalParameter (replaceExposure templates (fun index ↦ exposure index input))) proposals *
        FiniteReportLaw.mass
          (countLaw (replaceExposure templates (fun index ↦ exposure index input)) state proposals)
            target) :=
  (poissonCoefficient_measurable templates exposure hexposure proposals).mul
    (count_mass_measurable templates exposure hexposure state target proposals)

private theorem coordinate_summable (branches : Fin count → Branch n)
    (state target : SiteState n) :
    Summable (fun proposals ↦ poissonPMFReal (proposalParameter branches) proposals *
      (countLaw branches state proposals).mass target) := by
  apply (poissonPMFRealSum (proposalParameter branches)).summable.of_nonneg_of_le
  · intro proposals
    exact mul_nonneg poissonPMFReal_nonneg ((countLaw branches state proposals).mass_nonneg target)
  · intro proposals
    have hmass : (countLaw branches state proposals).mass target ≤ 1 := by
      rw [← (countLaw branches state proposals).mass_sum]
      exact Finset.single_le_sum (fun output _ ↦
        (countLaw branches state proposals).mass_nonneg output) (Finset.mem_univ target)
    exact mul_le_of_le_one_right poissonPMFReal_nonneg hmass

/-- The exact infinite mutation law is measurable in all branch exposures. -/
theorem interval_mass_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state target : SiteState n) :
    Measurable (fun input ↦ FiniteReportLaw.mass
      (intervalLaw (replaceExposure templates (fun index ↦ exposure index input)) state) target) :=
  measurable_real_tsum (countContribution_measurable templates exposure hexposure state target)
    (fun input ↦ coordinate_summable
      (replaceExposure templates (fun index ↦ exposure index input)) state target)

/-- Measurable readouts may depend on the same waiting times as the law. This
permits nested older-to-younger interval composition before integrating time. -/
theorem interval_expectation_measurable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state : SiteState n) (readout : Ω → SiteState n → ℝ)
    (hreadout : ∀ output, Measurable (fun input ↦ readout input output)) :
    Measurable (fun input ↦ FiniteReportLaw.expectation
      (intervalLaw (replaceExposure templates (fun index ↦ exposure index input)) state)
        (readout input)) := by
  apply Finset.measurable_sum
  intro output _
  exact (interval_mass_measurable templates exposure hexposure state output).mul (hreadout output)

/-- In particular, real waiting-time coordinates give measurable mutation
exposures. `toNNReal` agrees with the waiting time on its nonnegative support. -/
theorem waiting_exposure_measurable (rate : ℝ≥0) (waiting : Ω → ℝ)
    (hwaiting : Measurable waiting) :
    Measurable (fun input ↦ rate * Real.toNNReal (waiting input)) :=
  measurable_const.mul hwaiting.real_toNNReal

private theorem abs_expectation_le (law : FiniteReportLaw (SiteState n))
    (readout : SiteState n → ℝ) (bound : ℝ) (hbound : ∀ output, |readout output| ≤ bound) :
    |law.expectation readout| ≤ bound := by
  calc
    |law.expectation readout| ≤ ∑ output, |law.mass output * readout output| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ output, law.mass output * |readout output| := by
      simp only [abs_mul, abs_of_nonneg (law.mass_nonneg _)]
    _ ≤ ∑ output, law.mass output * bound := Finset.sum_le_sum (fun output _ ↦
      mul_le_mul_of_nonneg_left (hbound output) (law.mass_nonneg output))
    _ = bound := by rw [← Finset.sum_mul, FiniteReportLaw.mass_sum, one_mul]

/-- Bounded measurable genotype readouts have integrable conditional
expectations under every finite waiting-time measure. A portability ratio
requires its own justified bound; this theorem does not supply one. -/
theorem interval_expectation_integrable (templates : Fin count → Branch n)
    (exposure : Fin count → Ω → ℝ≥0) (hexposure : ∀ index, Measurable (exposure index))
    (state : SiteState n) (readout : Ω → SiteState n → ℝ)
    (hreadout : ∀ output, Measurable (fun input ↦ readout input output))
    (measure : Measure Ω) [IsFiniteMeasure measure] (bound : ℝ)
    (hbound : ∀ input output, |readout input output| ≤ bound) :
    Integrable (fun input ↦ FiniteReportLaw.expectation
      (intervalLaw (replaceExposure templates (fun index ↦ exposure index input)) state)
        (readout input)) measure := by
  apply Integrable.of_bound
    (Measurable.aestronglyMeasurable
      (interval_expectation_measurable templates exposure hexposure state readout hreadout)) bound
  exact Filter.Eventually.of_forall (fun input ↦ by
    rw [Real.norm_eq_abs]
    exact abs_expectation_le _ _ bound (hbound input))

section FiniteComposition

variable {State Next : Type*} [Fintype State] [Fintype Next]

/-- Composition preserves the measurability proved for each derived interval
law, including dependence on common waiting-time variables. -/
theorem bind_mass_measurable (law : Ω → FiniteReportLaw State)
    (kernel : Ω → State → FiniteReportLaw Next)
    (hlaw : ∀ state, Measurable (fun input ↦ (law input).mass state))
    (hkernel : ∀ state target, Measurable (fun input ↦ (kernel input state).mass target))
    (target : Next) : Measurable (fun input ↦ ((law input).bind (kernel input)).mass target) := by
  apply Finset.measurable_sum
  intro state _
  exact (hlaw state).mul (hkernel state target)

end FiniteComposition

end Descent.Portability.InterleavedMutationMeasurability
