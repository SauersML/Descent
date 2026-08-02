import Mathlib

namespace Calibrator

/-!
# Reversible Markov spectral kernels

For a centered observable of a stationary reversible Markov chain, the spectral theorem
reduces each real transition eigenvalue `λ ∈ (-1,1)` to the Poisson kernel

`(1 - λ²) / (1 + λ² - 2 λ cos s)`.

This module proves the algebraic kernel laws used by that representation; it does not
claim the representation for arbitrary nonreversible chains.  Positive `λ` describes
persistence and concentrates power near frequency zero. Negative `λ` is its reflected,
alternating counterpart and concentrates power near frequency `π`.

For genetics, a two-state local-ancestry or haplotype-state chain has second eigenvalue
`1 - a - b`. Recombination and switching rates therefore control the spectral shape
directly. The endpoint contrast below is an exact diagnostic law, not a generic distance
between populations.
-/

/-- Poisson kernel written as a function of `x = cos s`. -/
noncomputable def markovPoissonKernel (λ x : ℝ) : ℝ :=
  (1 - λ ^ 2) / (1 + λ ^ 2 - 2 * λ * x)

/-- Reversing the transition eigenvalue reflects the frequency coordinate. -/
theorem markovPoissonKernel_neg (λ x : ℝ) :
    markovPoissonKernel (-λ) x = markovPoissonKernel λ (-x) := by
  unfold markovPoissonKernel
  congr 1 <;> ring

/-- At zero frequency, a persistent eigenmode has gain `(1+λ)/(1-λ)`. -/
theorem markovPoissonKernel_at_one (λ : ℝ) (hλ : λ ≠ 1) :
    markovPoissonKernel λ 1 = (1 + λ) / (1 - λ) := by
  unfold markovPoissonKernel
  field_simp
  ring

/-- At frequency `π`, the same eigenmode has reciprocal endpoint gain. -/
theorem markovPoissonKernel_at_neg_one (λ : ℝ) (hλ : λ ≠ -1) :
    markovPoissonKernel λ (-1) = (1 - λ) / (1 + λ) := by
  unfold markovPoissonKernel
  field_simp
  ring

/-- The `λ = 0.9` mode has the exact `19` versus `1/19` endpoint contrast. -/
theorem markovPoissonKernel_nine_tenths :
    markovPoissonKernel (9 / 10 : ℝ) 1 = 19 ∧
      markovPoissonKernel (9 / 10 : ℝ) (-1) = 1 / 19 := by
  constructor <;> norm_num [markovPoissonKernel]

/-- The nonconstant eigenvalue of a two-state transition matrix with switching
probabilities `a` and `b`. -/
def twoStatePersistence (a b : ℝ) : ℝ := 1 - a - b

/-- Independent state draws are the zero-persistence point `a + b = 1`. -/
theorem twoStatePersistence_eq_zero_iff (a b : ℝ) :
    twoStatePersistence a b = 0 ↔ a + b = 1 := by
  unfold twoStatePersistence
  constructor <;> intro h <;> linarith

/-- Swapping persistence for alternation mirrors the spectral kernel exactly. -/
theorem persistent_alternating_mirror (λ x : ℝ) :
    markovPoissonKernel (-λ) x = markovPoissonKernel λ (-x) :=
  markovPoissonKernel_neg λ x

end Calibrator
