/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The Moran model, and why the coalescent does not care which model it came from

Kingman (1982), *On the genealogy of large populations* (**K-G**), section 4, is about
robustness: the `n`-coalescent is the large-`N` limit not just of Wright-Fisher reproduction
but of any exchangeable family-size law with bounded moments, and the only trace the model
leaves is the time scale.  If the family-size variance tends to `σ²` then (4.3)-(4.4) put
the coalescent on the clock `R_t = ℛ_{[N σ⁻² t]}` -- the variance, and nothing else about the
model, sets the rate.

`Descent.Coalescent.WrightFisher` counts the Wright-Fisher case, where `σ² = 1` and the unit
is `N` generations.  This file does K-G's own degenerate example, the Moran model (4.5):

  `P{ν = 2} = N⁻¹`,  `P{ν = 0} = N⁻¹`,  `P{ν = 1} = 1 - 2N⁻¹`.

One individual has two children, one has none, the rest have one.  Its variance is `2N⁻¹`,
not a constant -- which is why K-G says "for this one must use the different time change
`r = ½N²t`", and that factor is `N/σ²` with `σ² = 2N⁻¹`.  It is all arithmetic, and doing it
makes the contrast with Wright-Fisher explicit rather than a remark.

The factor of two that K-G mentions separating Moran from Wright-Fisher conclusions is the
same one: the two models' time scales differ by `2N` versus `N²/2`, and per generation that
is a factor of `N/2`.

## Main results

- `moranMass`: the family-size law (4.5).
- `moranMass_sum`: it is a probability distribution.
- `moranMean`: `E(ν) = 1`, as (2.1) forces for any model with constant population size.
- `moranVariance`: `Var(ν) = 2/N`, K-G's stated value.
- `moranTimeScale`: so the natural unit is `N²/2` generations, K-G's `r = ½N²t`.
-/

namespace Coalescent

open Finset

/-- K-G (4.5): the Moran model's family-size law, as a mass function on `{0, 1, 2}`. -/
noncomputable def moranMass (N : ℕ) : ℕ → ℝ
  | 0 => 1 / (N : ℝ)
  | 1 => 1 - 2 / (N : ℝ)
  | 2 => 1 / (N : ℝ)
  | _ => 0

/-- The Moran law is a probability distribution. -/
theorem moranMass_sum {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range 3, moranMass N k = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [moranMass]
  field_simp
  ring

/-- **Every moment of (4.5) is this one expansion.**  `range 3` has three elements and
`moranMass` is given case by case, so a moment `Σ w(k) P{ν = k}` is three products and
nothing else; the two families of size `0` and `2` carry the same mass `N⁻¹`, which is why
they appear here summed.  Naming the expansion once leaves each moment below with only its
own arithmetic, and that arithmetic needs no hypothesis on `N`: `x / 0 = 0` in Lean, so the
cancellations are identities in `N⁻¹` rather than facts about a nonzero `N`. -/
theorem moranMass_moment {N : ℕ} (w : ℕ → ℝ) :
    ∑ k ∈ range 3, w k * moranMass N k
      = w 1 * (1 - 2 / (N : ℝ)) + (w 0 + w 2) * (1 / (N : ℝ)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [moranMass]
  ring

/-- **`E(ν) = 1`.**  Forced by K-G (2.1), `Σ ν_j = N`: with a constant population size the
mean family size is one whatever the model.  The Moran law satisfies it, which is the check
that (4.5) describes a population that neither grows nor shrinks. -/
theorem moranMean {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range 3, (k : ℝ) * moranMass N k = 1 := by
  rw [moranMass_moment]
  push_cast
  ring

/-- The second moment, `E(ν²) = 1 + 2/N`. -/
theorem moranSecondMoment {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range 3, (k : ℝ) ^ 2 * moranMass N k = 1 + 2 / (N : ℝ) := by
  rw [moranMass_moment]
  push_cast
  ring

/-- **K-G (4.5): `Var(ν) = 2/N`.**  Not a constant, which is the whole point of Kingman's
"degenerate example": the hypothesis (4.2) that the variance tends to a finite nonzero limit
fails, and the time change has to be taken from the variance itself. -/
theorem moranVariance {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ range 3, (k : ℝ) ^ 2 * moranMass N k)
      - (∑ k ∈ range 3, (k : ℝ) * moranMass N k) ^ 2 = 2 / (N : ℝ) := by
  rw [moranSecondMoment hN, moranMean hN]
  ring

/-- **The Moran clock: `N²/2` generations, K-G's `r = ½N²t`.**  K-G (4.4) puts the
coalescent on the scale `N σ⁻²`; with `σ² = 2/N` that is `N²/2`, against Wright-Fisher's `N`
(where `σ² = 1`).  Per generation the two models differ by a factor `N/2` -- which is why
their conclusions are quoted with a factor of two between them once the Moran model's
mutation convention is also taken into account. -/
theorem moranTimeScale {N : ℕ} (hN : 0 < N) :
    (N : ℝ) / (2 / (N : ℝ)) = (N : ℝ) ^ 2 / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  field_simp

/-- **Wright-Fisher's clock, for contrast: `N` generations.**  The variance is one, so
`N σ⁻² = N`.  The two theorems together are K-G section 4's point: the model enters the
coalescent only through this number. -/
theorem wrightFisherTimeScale {N : ℕ} (hN : 0 < N) : (N : ℝ) / 1 = (N : ℝ) := by
  ring

end Coalescent

end Descent
