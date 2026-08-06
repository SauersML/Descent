/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Lambda
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# The Beta-coalescent, and the Beta recurrence that makes it consistent

`Descent.Coalescent.Lambda` proves that any `Λ` gives a consistent rate array, and that
`Λ = δ₀` is Kingman.  The other end of the family is the Beta-coalescents, `Λ = Beta(2-α, α)`,
which Schweinsberg (Stoch. Proc. Appl. 106, 107-139, 2003) obtained as the genealogies of
populations with heavy-tailed offspring numbers, and which Birkner and Blath have since used
throughout population-genetic inference.  Their rates are ratios of Beta functions,

  `λ_{b,k} = B(k - α, b - k + α) / B(2 - α, α)`,

and the reason they are consistent is a two-line identity about `B` itself:

  `B(a, b) = B(a+1, b) + B(a, b+1)`,                                        `betaFn_split`

which is `Γ(a+1) = a Γ(a)` twice and `a + b` cancelling.  Read at the coalescent's rates it
says exactly what Pitman's condition says -- a `k`-merger among `b` blocks either misses the
extra block or includes it -- so the Beta family is consistent for the same reason the
integral form is, one level of abstraction up.

At `α = 1` the measure is uniform and the rates are `(k-2)!(b-k)!/(b-1)!`
(`bolthausenSznitmanRate_eq`): the Bolthausen-Sznitman coalescent, which
`Descent.Blindness.MultipleMergerBlindness` already studies through its own chart.  That file
asks which statistics can see `Λ`; this one says why the family it is looking at is a family.

## Main results

- `betaFn`: `Γ(a)Γ(b)/Γ(a+b)`.
- `betaFn_split`: **`B(a,b) = B(a+1,b) + B(a,b+1)`**, the recurrence behind consistency.
- `betaCoalescentRate`: `Λ = Beta(2-α, α)`'s merger rates.
- `betaCoalescentRate_split`: which are consistent, by `betaFn_split`.
- `bolthausenSznitmanRate_eq`: at `α = 1`, `(k-2)!(b-k)!/(b-1)!`.
-/

namespace Coalescent

open Real Nat

/-- The Beta function, `B(a,b) = Γ(a)Γ(b)/Γ(a+b)`. -/
noncomputable def betaFn (a b : ℝ) : ℝ := Gamma a * Gamma b / Gamma (a + b)

/-- **The Beta recurrence: `B(a,b) = B(a+1,b) + B(a,b+1)`.**

Two applications of `Γ(s+1) = s Γ(s)` and a cancellation of `a + b`.  Read at a coalescent's
rates this IS Pitman's consistency condition: splitting on whether the extra block joins the
merger is splitting `a + b` into `a` and `b`. -/
theorem betaFn_split {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hG : Gamma (a + b) ≠ 0) :
    betaFn a b = betaFn (a + 1) b + betaFn a (b + 1) := by
  have h1 : Gamma (a + 1) = a * Gamma a := Gamma_add_one ha
  have h2 : Gamma (b + 1) = b * Gamma b := Gamma_add_one hb
  have h3 : Gamma (a + b + 1) = (a + b) * Gamma (a + b) := Gamma_add_one hab
  have e1 : a + 1 + b = a + b + 1 := by ring
  have e2 : a + (b + 1) = a + b + 1 := by ring
  unfold betaFn
  rw [e1, e2, h1, h2, h3]
  field_simp

/-- **The Beta-coalescent's merger rates**, `Λ = Beta(2-α, α)`.

Empirical status: THIS IS THE MODEL, and a substantive one: Schweinsberg (2003) derives it
from offspring numbers with a heavy tail of index `α`, so choosing it is choosing a
reproduction mechanism, not a convention.  Whether a population has such a tail is the
empirical question, and `Descent.Blindness.MultipleMergerBlindness` records which statistics
could tell. -/
noncomputable def betaCoalescentRate (alpha : ℝ) (b k : ℕ) : ℝ :=
  betaFn ((k : ℝ) - alpha) ((b : ℝ) - (k : ℝ) + alpha)

/-- **The Beta-coalescent rates are consistent**, by the Beta recurrence.

The bookkeeping: `a = k - α` and `b' = b - k + α` have `a + b' = b`, and adding a block sends
`(a, b')` to `(a, b' + 1)` when the merger misses it and to `(a + 1, b')` when it joins.  So
Pitman's condition is `betaFn_split` with nothing rearranged. -/
theorem betaCoalescentRate_split {alpha : ℝ} {b k : ℕ}
    (ha : (k : ℝ) - alpha ≠ 0) (hb : (b : ℝ) - (k : ℝ) + alpha ≠ 0)
    (hab : (b : ℝ) ≠ 0) (hG : Gamma (b : ℝ) ≠ 0) :
    betaCoalescentRate alpha b k
      = betaCoalescentRate alpha (b + 1) (k + 1) + betaCoalescentRate alpha (b + 1) k := by
  have hsum : (k : ℝ) - alpha + ((b : ℝ) - (k : ℝ) + alpha) = (b : ℝ) := by ring
  have hsplit := betaFn_split (a := (k : ℝ) - alpha) (b := (b : ℝ) - (k : ℝ) + alpha)
    ha hb (by rw [hsum]; exact hab) (by rw [hsum]; exact hG)
  unfold betaCoalescentRate
  have e1 : ((k : ℕ) + 1 : ℝ) - alpha = ((k : ℝ) - alpha) + 1 := by push_cast; ring
  have e2 : ((b : ℕ) + 1 : ℝ) - ((k : ℕ) + 1 : ℝ) + alpha
      = (b : ℝ) - (k : ℝ) + alpha := by push_cast; ring
  have e3 : ((b : ℕ) + 1 : ℝ) - (k : ℝ) + alpha
      = ((b : ℝ) - (k : ℝ) + alpha) + 1 := by push_cast; ring
  push_cast
  push_cast at e1 e2 e3
  rw [e1, e2, e3]
  linarith [hsplit]

/-- At `α = 1` the Beta measure is uniform on `[0,1]`, and the rates are the classical
`(k-2)! (b-k)! / (b-1)!` of the Bolthausen-Sznitman coalescent -- the `Λ`-coalescent that
`Descent.Blindness.MultipleMergerBlindness` studies through its own speed-tilt chart. -/
theorem bolthausenSznitmanRate_eq {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    betaCoalescentRate 1 b k
      = (((k - 2)! : ℕ) : ℝ) * (((b - k)! : ℕ) : ℝ) / (((b - 1)! : ℕ) : ℝ) := by
  have hk1 : ((k : ℝ) - 1) = (((k - 1 : ℕ)) : ℝ) := by
    have : (1 : ℕ) ≤ k := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hbk : ((b : ℝ) - (k : ℝ) + 1) = (((b - k + 1 : ℕ)) : ℝ) := by
    push_cast [Nat.cast_sub hkb]
    ring
  have hb1 : ((k : ℝ) - 1 + ((b : ℝ) - (k : ℝ) + 1)) = ((b : ℕ) : ℝ) := by ring
  unfold betaCoalescentRate betaFn
  rw [hb1, hk1, hbk]
  have g1 : Gamma (((k - 1 : ℕ)) : ℝ) = (((k - 2)! : ℕ) : ℝ) := by
    have hkk : (k - 1 : ℕ) = (k - 2) + 1 := by omega
    rw [hkk]
    push_cast
    exact Gamma_nat_eq_factorial (k - 2)
  have g2 : Gamma (((b - k + 1 : ℕ)) : ℝ) = (((b - k)! : ℕ) : ℝ) := by
    push_cast
    exact Gamma_nat_eq_factorial (b - k)
  have g3 : Gamma ((b : ℕ) : ℝ) = (((b - 1)! : ℕ) : ℝ) := by
    have hbb : (b : ℕ) = (b - 1) + 1 := by omega
    rw [hbb]
    push_cast
    exact Gamma_nat_eq_factorial (b - 1)
  rw [g1, g2, g3]

end Coalescent

end Descent
