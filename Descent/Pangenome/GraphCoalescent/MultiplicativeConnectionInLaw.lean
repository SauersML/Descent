/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (F3) in law: the scaled connection clock of a compressed pangenome

`Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence` proves that the probability
that the graph's report is connected at scaled time `U` converges to `Pr(T_p ≤ U)` at every
`U ≥ 0`.  Convergence in law is the statement about the laws themselves: the laws of the scaled
connection times converge to the law of `T_p` in the weak topology on probability measures on `ℝ`.

This file proves the criterion that turns the first into the second: distribution functions that
converge at every point give convergence in law (`tendsto_probabilityMeasure_of_tendsto_cdf`).  The
half-open intervals form a π-system containing arbitrarily small neighborhoods of every point, and
the measure of `(a, b]` is the increment of the distribution function, so Mathlib's π-system form of
the portmanteau theorem applies.

## Main results

- `tendsto_probabilityMeasure_of_tendsto_cdf`: convergence of the distribution functions at every
  point gives convergence in law.

## Empirical status

None.  Every declaration here is a statement about probability measures on the real line and their
distribution functions.
-/

namespace Descent.Pangenome.GraphCoalescent

open MeasureTheory ProbabilityTheory Filter Topology Set

noncomputable section

/-! ### Distribution functions and convergence in law -/

/-- The measure of a half-open interval is the increment of the distribution function. -/
theorem coe_probabilityMeasure_Ioc (ρ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    ((ρ (Ioc a b) : NNReal) : ℝ) = cdf (ρ : Measure ℝ) b - cdf (ρ : Measure ℝ) a := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, measureReal_def]
  conv_lhs => rw [← measure_cdf (ρ : Measure ℝ)]
  rw [StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf (ρ : Measure ℝ)).mono hab))]

/-- **Distribution functions converging at every point give convergence in law.** -/
theorem tendsto_probabilityMeasure_of_tendsto_cdf {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : ∀ x, Tendsto (fun i ↦ cdf (μ i : Measure ℝ) x) l (𝓝 (cdf (ν : Measure ℝ) x))) :
    Tendsto μ l (𝓝 ν) := by
  refine (isPiSystem_Ioc_mem (univ : Set ℝ) univ).tendsto_probabilityMeasure_of_tendsto_of_mem
    ?_ ?_ ?_
  · rintro s ⟨a, -, b, -, -, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    refine ⟨Ioc (x - ε / 2) (x + ε / 2),
      ⟨x - ε / 2, mem_univ _, x + ε / 2, mem_univ _, by linarith, rfl⟩,
      Ioc_mem_nhds (by linarith) (by linarith), fun y hy ↦ hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  · rintro s ⟨a, -, b, -, hab, rfl⟩
    rw [← NNReal.tendsto_coe]
    simp only [coe_probabilityMeasure_Ioc _ hab.le]
    exact (h b).sub (h a)

end

end Descent.Pangenome.GraphCoalescent
