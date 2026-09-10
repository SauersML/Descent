/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MatrixOperatorBridge

assert_below Descent.Decision Descent.Program

/-!
Poisson uniformization makes finite Markov observable semigroups contractions.
The normalized law is constructed before identifying its matrix exponential.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator NNReal

namespace Descent.Portability.MarkovPoissonLaw

open ProbabilityTheory InterleavedMutationExponential EvolutionaryObservability
open MatrixOperatorBridge ControlledCoarseGraining
variable {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
private theorem coordinate_summable (kernel : S → FiniteReportLaw S)
    (parameter : ℝ≥0) (source target : S) :
    Summable (fun count ↦ poissonPMFReal parameter count *
      (powerLaw kernel count source).mass target) := by
  apply (poissonPMFRealSum parameter).summable.of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg ((powerLaw kernel count source).mass_nonneg target)
  · intro count
    have hmass : (powerLaw kernel count source).mass target ≤ 1 := by
      rw [← (powerLaw kernel count source).mass_sum]
      exact Finset.single_le_sum
        (fun state _ ↦ (powerLaw kernel count source).mass_nonneg state) (Finset.mem_univ target)
    exact mul_le_of_le_one_right poissonPMFReal_nonneg hmass

noncomputable def poissonLaw (kernel : S → FiniteReportLaw S)
    (parameter : ℝ≥0) (source : S) : FiniteReportLaw S where
  mass target := ∑' count,
    poissonPMFReal parameter count * (powerLaw kernel count source).mass target
  mass_nonneg target := tsum_nonneg fun count ↦
    mul_nonneg poissonPMFReal_nonneg ((powerLaw kernel count source).mass_nonneg target)
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun target _ ↦
      coordinate_summable kernel parameter source target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact (poissonPMFRealSum parameter).tsum_eq

/-- The complete Poisson mixture equals the finite Markov matrix exponential. -/
theorem poissonLaw_matrix (kernel : S → FiniteReportLaw S) (parameter : ℝ≥0) :
    kernelMatrix (poissonLaw kernel parameter) =
      NormedSpace.exp ℝ ((parameter : ℝ) • (kernelMatrix kernel - 1)) := by
  ext source target
  change (∑' count, poissonPMFReal parameter count * (powerLaw kernel count source).mass target) = _
  simp only [powerLaw_mass]
  exact poisson_matrix_exponential parameter (kernelMatrix kernel) source target

noncomputable def generator (kernel : S → FiniteReportLaw S) (rate : ℝ≥0) : Matrix S S ℝ :=
  (rate : ℝ) • (kernelMatrix kernel - 1)

/-- Contractivity is derived from the normalized Poisson law, not assumed. -/
theorem evolution_norm_le_one (kernel : S → FiniteReportLaw S) (rate : ℝ≥0)
    (time : ℝ) (htime : 0 ≤ time) :
    ‖evolution (operator (generator kernel rate)) time‖ ≤ 1 := by
  have hexposure : ((rate * Real.toNNReal time : ℝ≥0) : ℝ) = time * (rate : ℝ) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal time htime]
    ring
  have hexp : evolution (operator (generator kernel rate)) time =
      operator (kernelMatrix (poissonLaw kernel (rate * Real.toNNReal time))) := by
    rw [poissonLaw_matrix, operator_exp]
    simp only [evolution, generator, operator_smul, smul_smul, hexposure]
  rw [hexp]
  exact markov_operator_norm_le_one _


/-- A finite conservative Markov generator, specified by its actual entries. -/
structure FiniteGenerator (S : Type*) [Fintype S] where
  matrix : Matrix S S ℝ
  off_nonneg : ∀ source target, source ≠ target → 0 ≤ matrix source target
  row_sum : ∀ source, ∑ target, matrix source target = 0

noncomputable def normalizationRate (model : FiniteGenerator S) : ℝ≥0 :=
  ⟨1 + ∑ state, |model.matrix state state|, by positivity⟩

omit [DecidableEq S] in
theorem normalizationRate_pos (model : FiniteGenerator S) : 0 < (normalizationRate model : ℝ) := by
  dsimp [normalizationRate]
  positivity

noncomputable def normalizedKernel (model : FiniteGenerator S) (source : S) :
    FiniteReportLaw S where
  mass target := (if source = target then 1 else 0) +
    model.matrix source target / (normalizationRate model : ℝ)
  mass_nonneg target := by
    have hrate := normalizationRate_pos model
    by_cases heq : source = target
    · subst target
      rw [if_pos rfl]
      have hdiag : |model.matrix source source| ≤ ∑ state, |model.matrix state state| :=
        Finset.single_le_sum (fun state _ ↦ abs_nonneg (model.matrix state state))
          (Finset.mem_univ source)
      have hlower : -(normalizationRate model : ℝ) ≤ model.matrix source source := by
        dsimp [normalizationRate]
        linarith [neg_abs_le (model.matrix source source)]
      have hdiv : -1 ≤ model.matrix source source / (normalizationRate model : ℝ) := by
        apply (le_div_iff₀ hrate).mpr
        simpa using hlower
      linarith
    · rw [if_neg heq, zero_add]
      exact div_nonneg (model.off_nonneg source target heq) (le_of_lt hrate)
  mass_sum := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, model.row_sum]
    simp

/-- Every finite conservative generator has an exact positive-rate uniformization. -/
theorem normalized_generator (model : FiniteGenerator S) :
    generator (normalizedKernel model) (normalizationRate model) = model.matrix := by
  ext source target
  change (normalizationRate model : ℝ) *
    (((if source = target then 1 else 0) +
      model.matrix source target / (normalizationRate model : ℝ)) -
      (1 : Matrix S S ℝ) source target) = model.matrix source target
  rw [Matrix.one_apply]
  by_cases heq : source = target <;> simp only [heq, if_true, if_false]
  all_goals field_simp [ne_of_gt (normalizationRate_pos model)]
  all_goals ring

/-- Contractivity now applies to arbitrary finite conservative generator entries. -/
theorem finiteGenerator_evolution_norm_le_one (model : FiniteGenerator S)
    (time : ℝ) (htime : 0 ≤ time) : ‖evolution (operator model.matrix) time‖ ≤ 1 := by
  rw [← normalized_generator model]
  exact evolution_norm_le_one _ _ _ htime

end Descent.Portability.MarkovPoissonLaw
