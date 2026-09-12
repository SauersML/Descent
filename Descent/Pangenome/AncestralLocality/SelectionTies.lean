/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionClosure
import Descent.Pangenome.AncestralLocality.SelectionDecisions

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Two models of selection: size bias and the selection kernel

`SelectionClosure` models fecundity selection by size-biasing the parents, `sizeBias s p`.
`SelectionDecisions` models selection as a kernel event at rate `σ`, the replacement kernel
`selectionKernel s σ`. This module identifies what the two share.

The denominator of the size bias is the mean fitness `meanFitness s p`
(`sum_mul_eq_meanFitness`, `sizeBias_eq_div_meanFitness`). Under unbiased copying `halfMix`, one
generation of size-biased reproduction moves a population by the classical selective drift
`p_z (s(z) - s̄(p))` divided by the mean fitness (`reproduce_halfMix_sizeBias_sub`). The selection
kernel moves a population of mass one by the same drift divided by `σ`, which is
`reproduce_selectionKernel` of `SelectionDecisions`. So the two models push every state in the
same direction, at rates in the ratio `σ : s̄(p)` (`selectionKernel_drift_eq_sizeBias_drift`).

Scope. The identification is for one generation, on vectors of mass one with nonzero mean fitness;
no statement about iterated dynamics or the ancestral selection graph is made here.

## Empirical status

None. The bodies here are finite sums of supplied real numbers; the fitness and the population are
supplied, and no measurement can bear on these identities.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H : Type*} [Fintype H]

/-- The denominator of the size bias is the mean fitness. -/
theorem sum_mul_eq_meanFitness (s p : H → ℝ) : ∑ y, s y * p y = meanFitness s p := by
  unfold meanFitness
  exact Finset.sum_congr rfl fun y _ ↦ mul_comm _ _

/-- The size bias divides by the mean fitness. -/
theorem sizeBias_eq_div_meanFitness (s p : H → ℝ) (x : H) :
    sizeBias s p x = s x * p x / meanFitness s p := by
  rw [sizeBias, sum_mul_eq_meanFitness]

/-- **One generation of size-biased copying is the selective drift over the mean fitness.** -/
theorem reproduce_halfMix_sizeBias_sub [DecidableEq H] (s : H → ℝ) {p : H → ℝ}
    (hs : meanFitness s p ≠ 0) (z : H) :
    reproduce halfMix (sizeBias s p) z - p z =
      p z * (s z - meanFitness s p) / meanFitness s p := by
  have hsum : ∑ x, sizeBias s p x = 1 := by
    simp only [sizeBias_eq_div_meanFitness, ← Finset.sum_div]
    rw [sum_mul_eq_meanFitness]
    exact div_self hs
  rw [reproduce_halfMix_eq hsum, sizeBias_eq_div_meanFitness, eq_div_iff hs, sub_mul,
    div_mul_cancel₀ _ hs]
  ring

/-- **The two selection models drift together.** On a vector of mass one with nonzero mean
fitness, the selection kernel at rate `σ` and one generation of size-biased copying move every
state in the same direction, at rates in the ratio `σ : s̄(p)`. -/
theorem selectionKernel_drift_eq_sizeBias_drift [DecidableEq H] (s : H → ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) {p : H → ℝ} (hp : ∑ x, p x = 1) (hs : meanFitness s p ≠ 0) (z : H) :
    σ * (reproduce (selectionKernel s σ) p z - p z) =
      meanFitness s p * (reproduce halfMix (sizeBias s p) z - p z) := by
  rw [reproduce_selectionKernel s hσ hp z, reproduce_halfMix_sizeBias_sub s hs z, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hs]

end

end Descent.Pangenome.AncestralLocality
