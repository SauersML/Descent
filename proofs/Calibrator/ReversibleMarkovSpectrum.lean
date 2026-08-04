/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Reversible Markov spectral kernels

For a centered observable of a stationary reversible Markov chain, the spectral theorem
reduces each real transition eigenvalue `lam ∈ (-1,1)` to the Poisson kernel

`(1 - lam²) / (1 + lam² - 2 lam cos s)`.

This module proves the algebraic kernel laws used by that representation; it does not
claim the representation for arbitrary nonreversible chains.  Positive `lam` describes
persistence and concentrates power near frequency zero. Negative `lam` is its reflected,
alternating counterpart and concentrates power near frequency `π`.

For genetics, a two-state local-ancestry or haplotype-state chain has second eigenvalue
`1 - a - b`. Recombination and switching rates therefore control the spectral shape
directly. The endpoint contrast below is an exact diagnostic law, not a generic distance
between populations.

## Two repairs, recorded here rather than only in a commit message

**The eigenvalue is named `lam`, not `λ`.** `λ` is reserved lambda syntax in Lean 4, so
every binder using it as a variable was a parse error (`unexpected token 'λ'; expected '_'
or identifier`) and this module did not compile at all. The rename is mechanical and
changes no statement. The mathematical notation `λ` survives in prose above; only the
binders changed.

**The import was `import Mathlib`.** That pulls the whole library, and the root
`Mathlib.olean` is not always present in this checkout, so the file could fail for a second
and unrelated reason. The imports are now the five this file actually uses. This matters
beyond one module: a wholesale import makes every downstream module wait on the entire
library, and `Calibrator.SpectralDegradation` and `Calibrator.FoldedSpectrum` are
downstream of this one.
-/

/-- Poisson kernel written as a function of `x = cos s`. -/
noncomputable def markovPoissonKernel (lam x : ℝ) : ℝ :=
  (1 - lam ^ 2) / (1 + lam ^ 2 - 2 * lam * x)

/-- **markovPoissonKernel where its denominator vanishes, named.** The guard `1 + lam ^ 2 - 2 * lam
* x` is zero at `lam = 1`, `x = 1`. At unit persistence and unit argument the Poisson kernel is
on its singularity, where it diverges. Lean returns `0` there rather than the value the modelled
quantity takes, and no type error marks the point. Consumers must require `1 + lam ^ 2 - 2 * lam
* x ≠ 0`. -/
theorem markovPoissonKernel_at_lam1x1_is_junk :
    markovPoissonKernel 1 1 = 0 := by
  unfold markovPoissonKernel
  norm_num

/-- Reversing the transition eigenvalue reflects the frequency coordinate. -/
theorem markovPoissonKernel_neg (lam x : ℝ) :
    markovPoissonKernel (-lam) x = markovPoissonKernel lam (-x) := by
  unfold markovPoissonKernel
  congr 1 <;> ring

/-- At zero frequency, a persistent eigenmode has gain `(1+lam)/(1-lam)`. -/
theorem markovPoissonKernel_at_one (lam : ℝ) (hlam : lam ≠ 1) :
    markovPoissonKernel lam 1 = (1 + lam) / (1 - lam) := by
  unfold markovPoissonKernel
  have h : (1 : ℝ) - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
  have hd : 1 + lam ^ 2 - 2 * lam * 1 = (1 - lam) ^ 2 := by ring
  rw [hd, div_eq_div_iff (pow_ne_zero 2 h) h]
  ring

/-- At frequency `π`, the same eigenmode has reciprocal endpoint gain. -/
theorem markovPoissonKernel_at_neg_one (lam : ℝ) (hlam : lam ≠ -1) :
    markovPoissonKernel lam (-1) = (1 - lam) / (1 + lam) := by
  unfold markovPoissonKernel
  have h : (1 : ℝ) + lam ≠ 0 := fun hcontra ↦ hlam (by linarith [hcontra])
  have hd : 1 + lam ^ 2 - 2 * lam * (-1) = (1 + lam) ^ 2 := by ring
  rw [hd, div_eq_div_iff (pow_ne_zero 2 h) h]
  ring

/-- The `lam = 0.9` mode has the exact `19` versus `1/19` endpoint contrast. -/
theorem markovPoissonKernel_nine_tenths :
    markovPoissonKernel (9 / 10 : ℝ) 1 = 19 ∧
      markovPoissonKernel (9 / 10 : ℝ) (-1) = 1 / 19 := by
  constructor <;> norm_num [markovPoissonKernel]

/-- The nonconstant eigenvalue of a two-state transition matrix with switching
probabilities `a` and `b`. -/
def twoStatePersistence (a b : ℝ) : ℝ := 1 - a - b

/-- **Persistence and total switching probability partition one.** The vanishing criterion below
holds for every body that is zero on `a + b = 1`; this fixes the slope as well. -/
theorem twoStatePersistence_add_switch (a b : ℝ) :
    twoStatePersistence a b + (a + b) = 1 := by
  unfold twoStatePersistence
  ring

/-- Independent state draws are the zero-persistence point `a + b = 1`. -/
theorem twoStatePersistence_eq_zero_iff (a b : ℝ) :
    twoStatePersistence a b = 0 ↔ a + b = 1 := by
  unfold twoStatePersistence
  constructor <;> intro h <;> linarith

/-- Swapping persistence for alternation mirrors the spectral kernel exactly. -/
theorem persistent_alternating_mirror (lam x : ℝ) :
    markovPoissonKernel (-lam) x = markovPoissonKernel lam (-x) :=
  markovPoissonKernel_neg lam x

end Calibrator
