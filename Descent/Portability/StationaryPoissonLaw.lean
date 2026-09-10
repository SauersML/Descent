/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteHorizonLoss

assert_below Descent.Decision Descent.Program

/-!
Stationarity is preserved by finite powers and by the normalized Poisson mixture.
Thus stationary finite CTMC experiments can use the exact probability kernels
whose matrices are their generator exponentials.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix NNReal

namespace Descent.Portability.StationaryPoissonLaw

open FiniteHorizonLoss MarkovPoissonLaw EvolutionaryObservability
open InterleavedMutationExponential MarkovCoarseGraining

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem stationary_power (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (count : ℕ) :
    Stationary law (powerLaw kernel count) := by
  intro target
  simp only [powerLaw_mass]
  induction count generalizing target with
  | zero => simp [Matrix.one_apply]
  | succ count ih =>
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hall (state : S) :
        (∑ source, law.mass source * (kernelMatrix kernel ^ count) source state) =
          law.mass state := by
      exact ih state
    simp_rw [← mul_assoc, ← Finset.sum_mul, hall]
    exact hstationary target

theorem stationary_poisson (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (parameter : ℝ≥0) :
    Stationary law (poissonLaw kernel parameter) := by
  intro target
  change (∑ source, law.mass source *
    ∑' count, ProbabilityTheory.poissonPMFReal parameter count *
      (powerLaw kernel count source).mass target) = law.mass target
  have hcoord (source : S) : Summable (fun count ↦
      ProbabilityTheory.poissonPMFReal parameter count *
        (powerLaw kernel count source).mass target) := by
    apply (ProbabilityTheory.poissonPMFRealSum parameter).summable.of_nonneg_of_le
    · intro count
      exact mul_nonneg ProbabilityTheory.poissonPMFReal_nonneg
        ((powerLaw kernel count source).mass_nonneg target)
    · intro count
      have hmass : (powerLaw kernel count source).mass target ≤ 1 := by
        rw [← (powerLaw kernel count source).mass_sum]
        exact Finset.single_le_sum
          (fun state _ ↦ (powerLaw kernel count source).mass_nonneg state)
          (Finset.mem_univ target)
      exact mul_le_of_le_one_right ProbabilityTheory.poissonPMFReal_nonneg hmass
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun source _ ↦
    (hcoord source).mul_left (law.mass source))]
  have hterm (count : ℕ) :
      (∑ source, law.mass source * (ProbabilityTheory.poissonPMFReal parameter count *
        (powerLaw kernel count source).mass target)) =
      ProbabilityTheory.poissonPMFReal parameter count * law.mass target := by
    simp_rw [mul_left_comm (law.mass _), ← Finset.mul_sum,
      stationary_power law kernel hstationary count target]
  simp_rw [hterm]
  rw [tsum_mul_right, (ProbabilityTheory.poissonPMFRealSum parameter).tsum_eq, one_mul]

theorem stationary_stateLaw (law : FiniteReportLaw S) (kernel : S → FiniteReportLaw S)
    (hstationary : Stationary law kernel) (rate : ℝ≥0) (time : ℝ) :
    Stationary law (stateLaw kernel rate time) :=
  stationary_poisson law kernel hstationary _

end Descent.Portability.StationaryPoissonLaw
