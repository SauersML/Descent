/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralEpochLaw

assert_below Descent.Decision Descent.Program

/-!
The four-nucleotide mutation kernel with no silent mutation: each mutation
chooses uniformly among the other three nucleotides. This is the JC69 kernel
specified by https://tskit.dev/msprime/docs/stable/mutations.html .

The closed branch law below is derived from the mutation-count distribution,
including recurrent and back mutations. Nucleotide endpoint states alone do
not encode tskit's site presence or allele-index ordering; those require the
mutation history as well and are not asserted to follow from this marginal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NucleotideMutationLaw

open FiniteReportLaw ProbabilityTheory AncestralEpochLaw
open scoped NNReal

abbrev Nucleotide := Fin 4

noncomputable def jumpLaw (start : Nucleotide) : FiniteReportLaw Nucleotide where
  mass := fun target ↦ if target = start then 0 else 1 / 3
  mass_nonneg := by intro target; split <;> norm_num
  mass_sum := by
    have h (target : Nucleotide) : (if target = start then 0 else 1 / 3 : ℝ) =
        1 / 3 - (if target = start then 1 / 3 else 0) := by
      split_ifs <;> ring
    simp_rw [h]
    norm_num [Finset.sum_sub_distrib]

noncomputable def uniformMean (readout : Nucleotide → ℝ) : ℝ := (∑ base, readout base) / 4

private theorem jump_expectation (start : Nucleotide) (readout : Nucleotide → ℝ) :
    (jumpLaw start).expectation readout = (4 * uniformMean readout - readout start) / 3 := by
  fin_cases start <;> simp [expectation, jumpLaw, uniformMean, Fin.sum_univ_succ] <;> ring

private theorem jump_uniformMean (readout : Nucleotide → ℝ) :
    uniformMean (fun start ↦ (jumpLaw start).expectation readout) = uniformMean readout := by
  simp only [jump_expectation]
  simp [uniformMean, Fin.sum_univ_succ]
  ring

noncomputable def countLaw (start : Nucleotide) (count : ℕ) : FiniteReportLaw Nucleotide :=
  ExactFiniteHistoryLaw.propagate (pointMass start) (fun _ ↦ jumpLaw) count

/-- The exact conditional expectation after a specified number of mutations.
The negative eigenvalue accounts for the absence of silent mutations. -/
theorem count_expectation (start : Nucleotide) (count : ℕ) (readout : Nucleotide → ℝ) :
    (countLaw start count).expectation readout = uniformMean readout +
      (-1 / 3 : ℝ) ^ count * (readout start - uniformMean readout) := by
  induction count generalizing readout with
  | zero => simp [countLaw, ExactFiniteHistoryLaw.propagate, expectation_pointMass]
  | succ count ih =>
      change ((countLaw start count).bind jumpLaw).expectation readout = _
      rw [expectation_bind, ih, jump_uniformMean, jump_expectation, pow_succ]
      ring

private theorem coordinate_summable (parameter : ℝ≥0) (start target : Nucleotide) :
    Summable (fun count ↦ poissonPMFReal parameter count * (countLaw start count).mass target) := by
  apply (poissonPMFRealSum parameter).summable.of_nonneg_of_le
  · intro count
    exact mul_nonneg poissonPMFReal_nonneg ((countLaw start count).mass_nonneg target)
  · intro count
    have h : (countLaw start count).mass target ≤ 1 := by
      rw [← (countLaw start count).mass_sum]
      exact Finset.single_le_sum (fun base _ ↦ (countLaw start count).mass_nonneg base)
        (Finset.mem_univ target)
    exact mul_le_of_le_one_right poissonPMFReal_nonneg h

/-- Parameter is mutation rate times branch length, for one discrete site. -/
noncomputable def branchLaw (parameter : ℝ≥0) (start : Nucleotide) :
    FiniteReportLaw Nucleotide where
  mass := fun target ↦ ∑' count, poissonPMFReal parameter count * (countLaw start count).mass target
  mass_nonneg := fun target ↦ tsum_nonneg (fun count ↦
    mul_nonneg poissonPMFReal_nonneg ((countLaw start count).mass_nonneg target))
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun target _ ↦ coordinate_summable parameter start target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact (poissonPMFRealSum parameter).tsum_eq

private theorem eigen_summable (parameter : ℝ≥0) :
    Summable (fun count ↦ poissonPMFReal parameter count * (-1 / 3 : ℝ) ^ count) := by
  apply (poissonPMFRealSum parameter).summable.of_norm_bounded
  intro count
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg poissonPMFReal_nonneg, abs_pow]
  exact mul_le_of_le_one_right poissonPMFReal_nonneg (pow_le_one₀ (by norm_num) (by norm_num))

/-- Exact JC69 expectation after integrating over every possible mutation count. -/
theorem branch_expectation (parameter : ℝ≥0) (start : Nucleotide)
    (readout : Nucleotide → ℝ) :
    (branchLaw parameter start).expectation readout = uniformMean readout +
      Real.exp (-4 * (parameter : ℝ) / 3) * (readout start - uniformMean readout) := by
  have hexpand : (branchLaw parameter start).expectation readout =
      ∑' count, poissonPMFReal parameter count * (countLaw start count).expectation readout := by
    unfold expectation branchLaw
    simp only [← tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun target _ ↦
      (coordinate_summable parameter start target).mul_right (readout target))]
    apply tsum_congr
    intro count
    simp only [Finset.mul_sum, mul_assoc]
  rw [hexpand]
  simp_rw [count_expectation, mul_add, ← mul_assoc]
  rw [Summable.tsum_add ((poissonPMFRealSum parameter).summable.mul_right (uniformMean readout))
    ((eigen_summable parameter).mul_right (readout start - uniformMean readout))]
  rw [tsum_mul_right, tsum_mul_right, (poissonPMFRealSum parameter).tsum_eq,
    one_mul, poisson_generating_function]
  congr 2
  ring

/-- Probability of each nucleotide, derived as an indicator expectation. -/
theorem branch_mass (parameter : ℝ≥0) (start target : Nucleotide) :
    (branchLaw parameter start).mass target = 1 / 4 +
      Real.exp (-4 * (parameter : ℝ) / 3) * ((if target = start then 1 else 0) - 1 / 4) := by
  have h := branch_expectation parameter start (fun base ↦ if base = target then 1 else 0)
  simpa [expectation, uniformMean, eq_comm] using h

private theorem branch_uniformMean (parameter : ℝ≥0) (readout : Nucleotide → ℝ) :
    uniformMean (fun start ↦ (branchLaw parameter start).expectation readout) =
      uniformMean readout := by
  simp only [branch_expectation]
  simp [uniformMean, Fin.sum_univ_succ]
  ring

/-- Splitting a branch at migration or null ancestry events leaves its
nucleotide law unchanged when the mutation exposure is additive. -/
theorem branch_compose (first second : ℝ≥0) (start : Nucleotide) :
    (branchLaw first start).bind (branchLaw second) = branchLaw (first + second) start := by
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  rw [expectation_bind, branch_expectation, branch_uniformMean,
    branch_expectation, branch_expectation]
  have he : Real.exp (-4 * ((first + second : ℝ≥0) : ℝ) / 3) =
      Real.exp (-4 * (first : ℝ) / 3) * Real.exp (-4 * (second : ℝ) / 3) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Probability of no mutation is distinct from the probability of recovering
the same nucleotide after recurrent mutations. This event is retained by the
mutation count even when the nucleotide endpoint loses that information. -/
theorem no_mutation_mass (parameter : ℝ≥0) :
    poissonPMFReal parameter 0 = Real.exp (-(parameter : ℝ)) := by
  simp [poissonPMFReal]

/-- The full nucleotide mutation sequence, before marginalizing intermediate
states, has the same closed terminal expectation. -/
theorem branch_history_expectation (parameter : ℝ≥0) (start : Nucleotide)
    (readout : Nucleotide → ℝ) :
    (∑' count, poissonPMFReal parameter count *
      ∑ path : ExactFiniteHistoryLaw.Path Nucleotide count,
        ExactFiniteHistoryLaw.pathMass (pointMass start) (fun _ ↦ jumpLaw) path *
          readout (ExactFiniteHistoryLaw.terminal path)) =
      uniformMean readout + Real.exp (-4 * (parameter : ℝ) / 3) *
        (readout start - uniformMean readout) := by
  simp_rw [ExactFiniteHistoryLaw.path_sum_eq_expectation]
  rw [← branch_expectation parameter start readout]
  unfold expectation branchLaw
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun target _ ↦
    (coordinate_summable parameter start target).mul_right (readout target))]
  apply tsum_congr
  intro count
  simp only [countLaw, Finset.mul_sum, mul_assoc]

end Descent.Portability.NucleotideMutationLaw
