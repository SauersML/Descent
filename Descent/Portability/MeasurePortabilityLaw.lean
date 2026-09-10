/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Probability.Moments.Variance

assert_below Descent.Decision Descent.Program

namespace Descent.Portability.MeasurePortabilityLaw

open MeasureTheory ProbabilityTheory

/-!
# Exact score accuracy under an arbitrary probability measure

The sample space may be continuous, discrete, or mixed. Genotypes and phenotype may have
arbitrary joint dependence. For finitely many scored markers with fixed deployed weights,
the actual measure-theoretic covariance and variance yield the exact squared correlation
formula in the genotype covariance matrix and genotype/phenotype covariance vector.

Each random variable is explicitly in `L²(μ)`. These hypotheses are essential: an arbitrary
real-valued environment need not have a finite variance, and squared correlation is then
not an unrestricted real-valued metric. Zero score or phenotype variance is represented
by `none`. No positive expectation functional on all random variables is assumed.

The probability measure is an input to this theorem. The theorem neither derives it from
demography alone nor assumes a Gaussian phenotype, linkage equilibrium, or shared effects.
Weights are fixed deployed weights; a trained random weight vector can be handled by first
conditioning on it or by separately modeling its joint distribution with deployment data.
-/

variable {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The deployed linear score, evaluated on the actual random genotype coordinates. -/
noncomputable def linearScore (weights : J → ℝ) (genotype : J → Ω → ℝ) : Ω → ℝ :=
  fun sample ↦ ∑ marker, weights marker * genotype marker sample

omit [IsProbabilityMeasure μ] in
/-- A finite weighted score has a finite second moment when every scored coordinate does. -/
theorem linearScore_memLp (weights : J → ℝ) (genotype : J → Ω → ℝ)
    (hgenotype : ∀ marker, MemLp (genotype marker) 2 μ) :
    MemLp (linearScore weights genotype) 2 μ := by
  exact memLp_finsetSum Finset.univ
    (fun marker _ ↦ (hgenotype marker).const_mul (weights marker))

/-- The numerator's unsquared covariance is an exact weighted sum under the joint law. -/
theorem covariance_linearScore (weights : J → ℝ) (genotype : J → Ω → ℝ)
    (phenotype : Ω → ℝ) (hgenotype : ∀ marker, MemLp (genotype marker) 2 μ)
    (hphenotype : MemLp phenotype 2 μ) :
    covariance (linearScore weights genotype) phenotype μ =
      ∑ marker, weights marker * covariance (genotype marker) phenotype μ := by
  unfold linearScore
  rw [covariance_fun_sum_left
    (fun marker ↦ (hgenotype marker).const_mul (weights marker)) hphenotype]
  simp only [covariance_const_mul_left]

/-- Every pairwise linkage covariance contributes to score variance; no diagonal or
independence approximation is made. -/
theorem variance_linearScore (weights : J → ℝ) (genotype : J → Ω → ℝ)
    (hgenotype : ∀ marker, MemLp (genotype marker) 2 μ) :
    variance (linearScore weights genotype) μ =
      ∑ first, ∑ second,
        weights first * weights second * covariance (genotype first) (genotype second) μ := by
  unfold linearScore
  rw [variance_fun_sum (fun marker ↦ (hgenotype marker).const_mul (weights marker))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, mul_assoc, mul_left_comm]

/-- Squared correlation on its square-integrable, nondegenerate variance domain. Variables
without finite second moments are rejected by the definition itself. -/
noncomputable def squaredCorrelation (score phenotype : Ω → ℝ) : Option ℝ := by
  classical
  exact if MemLp score 2 μ ∧ MemLp phenotype 2 μ ∧
      0 < variance score μ ∧ 0 < variance phenotype μ then
    some (covariance score phenotype μ ^ 2 / (variance score μ * variance phenotype μ))
  else none

omit [IsProbabilityMeasure μ] in
/-- A missing finite second moment produces an undefined metric, not a converted integral
or variance value that happens to be accepted as a numerical accuracy. -/
theorem squaredCorrelation_eq_none_of_not_memLp (score phenotype : Ω → ℝ)
    (h : ¬ MemLp score 2 μ ∨ ¬ MemLp phenotype 2 μ) :
    squaredCorrelation μ score phenotype = none := by
  rcases h with hscore | hphenotype
  · simp [squaredCorrelation, hscore]
  · simp [squaredCorrelation, hphenotype]

/-- Exact domain-safe accuracy law under an arbitrary probability measure. The covariance
matrix, covariance vector, and phenotype variance are all derived from the same joint law. -/
theorem squaredCorrelation_linearScore (weights : J → ℝ) (genotype : J → Ω → ℝ)
    (phenotype : Ω → ℝ) (hgenotype : ∀ marker, MemLp (genotype marker) 2 μ)
    (hphenotype : MemLp phenotype 2 μ) :
    squaredCorrelation μ (linearScore weights genotype) phenotype =
      if 0 < (∑ first, ∑ second,
          weights first * weights second * covariance (genotype first) (genotype second) μ) ∧
          0 < variance phenotype μ then
        some ((∑ marker, weights marker * covariance (genotype marker) phenotype μ) ^ 2 /
          ((∑ first, ∑ second,
            weights first * weights second * covariance (genotype first) (genotype second) μ) *
              variance phenotype μ))
      else none := by
  classical
  simp only [squaredCorrelation, linearScore_memLp μ weights genotype hgenotype,
    hphenotype, true_and]
  rw [covariance_linearScore μ weights genotype phenotype hgenotype hphenotype,
    variance_linearScore μ weights genotype hgenotype]

/-- On positive score and phenotype variance the exact law returns a real value, with
the standard quadratic-form denominator and the squared predictive covariance numerator. -/
theorem squaredCorrelation_linearScore_of_positive
    (weights : J → ℝ) (genotype : J → Ω → ℝ) (phenotype : Ω → ℝ)
    (hgenotype : ∀ marker, MemLp (genotype marker) 2 μ)
    (hphenotype : MemLp phenotype 2 μ)
    (hscore : 0 < variance (linearScore weights genotype) μ)
    (houtcome : 0 < variance phenotype μ) :
    squaredCorrelation μ (linearScore weights genotype) phenotype =
      some ((∑ marker, weights marker * covariance (genotype marker) phenotype μ) ^ 2 /
        ((∑ first, ∑ second,
          weights first * weights second * covariance (genotype first) (genotype second) μ) *
            variance phenotype μ)) := by
  rw [squaredCorrelation_linearScore μ weights genotype phenotype hgenotype hphenotype]
  rw [variance_linearScore μ weights genotype hgenotype] at hscore
  exact if_pos ⟨hscore, houtcome⟩

end Descent.Portability.MeasurePortabilityLaw
