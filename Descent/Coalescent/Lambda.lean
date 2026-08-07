/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Descent.Blindness.MultipleMergerBlindness
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 1 module(s) -- `Descent.Blindness.MultipleMergerBlindness`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent

/-!
# Beyond Kingman: `Λ`-coalescents, and why Kingman's is the `δ₀` case

Kingman's 1982 coalescent is the special case of a family introduced seventeen years later
by Pitman, *Coalescents with multiple collisions* (Ann. Probab. 27, 1870-1902, 1999) and
Sagitov, *The general coalescent with asynchronous mergers of ancestral lines* (J. Appl.
Prob. 36, 1116-1125, 1999).  In that generality, when `b` blocks are present any `k` of them
merge at rate

  `λ_{b,k} = ∫₀¹ x^{k-2} (1-x)^{b-k} Λ(dx)`

for a finite measure `Λ` on `[0,1]`.  `Descent.Blindness.MultipleMergerBlindness` already
carries that integral as `lambdaCoalescentMergerRate` and works out which statistics can see
`Λ`.  What it does not carry, and what this file adds, is the structural fact that makes the
family a family at all.

**Pitman's consistency condition.**  A rate array `λ_{b,k}` comes from a coalescent -- one
process whose restrictions to every sample size agree -- exactly when

  `λ_{b,k} = λ_{b+1,k} + λ_{b+1,k+1}`.                                      Pitman (1999)

Read backwards it says: watching `b` blocks, a `k`-merger among them is either a `k`-merger
among `b+1` blocks that misses the extra one, or a `(k+1)`-merger that includes it.  That is
the same bookkeeping `Descent.Coalescent.Restriction` does for states, at the level of rates,
and it is what `Descent.Coalescent.Infinite`'s projective limit needs in order to have
anything to take a limit of.

Three things are proved here:

* `lambdaRate_consistent`: the integral form satisfies it, by the algebra
  `(1-x)^{b+1-k} + x(1-x)^{b-k} = (1-x)^{b-k}` under the integral sign.  This is why
  `Λ`-coalescents exist.
* `kingmanRate_consistent`: so does the Kingman array `λ_{b,2} = 1`, `λ_{b,k} = 0` for
  `k > 2` -- binary mergers only.
* `lambdaRate_dirac_zero`: and the two agree, because `Λ = δ₀` gives exactly the Kingman
  array.  So `Descent.Coalescent`'s entire development is the `δ₀` fibre of this family, and
  `totalRate_kingman` shows its total rate is `deathRate`.

## Main results

- `IsConsistentRates`: Pitman's condition.
- `lambdaRate_consistent`: the `Λ`-integral form is consistent.
- `kingmanRate_consistent`: the binary-only array is consistent.
- `lambdaRate_dirac_zero`: `Λ = δ₀` IS Kingman.
- `totalRate_kingman`: whose total rate is `Descent.Coalescent.Rates.deathRate`.
-/

namespace Coalescent

open MeasureTheory

/-- **Pitman's consistency condition.**  A `k`-merger among `b` blocks is a `k`-merger among
`b+1` that misses the extra block, or a `(k+1)`-merger that includes it.  A rate array
satisfying this, and only such an array, comes from a single process compatible across
sample sizes. -/
def IsConsistentRates (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ b k : ℕ, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1)

/-- The pointwise identity behind consistency of the `Λ` form: splitting on whether the
extra block joins the merger is splitting `1 = (1-x) + x`. -/
theorem lambdaIntegrand_split {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) (x : ℝ) :
    x ^ (k - 2) * (1 - x) ^ (b - k)
      = x ^ (k - 2) * (1 - x) ^ (b + 1 - k) + x ^ (k + 1 - 2) * (1 - x) ^ (b + 1 - (k + 1)) := by
  have h1 : b + 1 - k = (b - k) + 1 := by omega
  have h2 : k + 1 - 2 = (k - 2) + 1 := by omega
  have h3 : b + 1 - (k + 1) = b - k := by omega
  rw [h1, h2, h3, pow_succ, pow_succ]
  ring

/-- **The `Λ`-coalescent rates are consistent.**  Pitman's condition holds for the integral
form, by linearity of the integral over the pointwise split.  This is the theorem that makes
`Λ`-coalescents exist as processes rather than as a family of unrelated rate arrays.

The integrability hypotheses are the honest cost of stating it for a general finite measure:
on `[0,1]` the integrands are bounded and the hypotheses are automatic, but `Λ` here is any
measure on `ℝ`, as `Descent.Blindness.MultipleMergerBlindness` defines it. -/
theorem lambdaRate_consistent (Λ : Measure ℝ) {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b)
    (h1 : Integrable (fun x : ℝ ↦ x ^ (k - 2) * (1 - x) ^ (b + 1 - k)) Λ)
    (h2 : Integrable (fun x : ℝ ↦ x ^ (k + 1 - 2) * (1 - x) ^ (b + 1 - (k + 1))) Λ) :
    Blindness.lambdaCoalescentMergerRate Λ b k
      = Blindness.lambdaCoalescentMergerRate Λ (b + 1) k + Blindness.lambdaCoalescentMergerRate Λ (b
        + 1) (k + 1) := by
  unfold Blindness.lambdaCoalescentMergerRate
  rw [← integral_add h1 h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ lambdaIntegrand_split hk hkb x)

/-- Kingman's array: binary mergers at unit rate, nothing else.  K-C (1.3) as a member of
Pitman's family. -/
noncomputable def kingmanRate (_b k : ℕ) : ℝ := if k = 2 then 1 else 0

/-- **Kingman's array is consistent.**  Trivially, but the triviality is the content: binary
mergers are compatible across sample sizes because a pair among `b` blocks is a pair among
`b+1` blocks that misses the extra one, and there is no `3`-merger to correct it. -/
theorem kingmanRate_consistent : IsConsistentRates kingmanRate := by
  intro b k hk _
  unfold kingmanRate
  have hk1 : ¬ (k + 1 = 2) := by omega
  by_cases h : k = 2 <;> simp [h, hk1]

/-- **`Λ = δ₀` is Kingman.**  A point mass at zero puts all the merger mass on the smallest
possible merger: `x^{k-2}` vanishes at `x = 0` unless `k = 2`, and then the integrand is
`1`.  So the whole of `Descent.Coalescent` -- the state space, the rates, the jump chain,
the Ewens formula -- is the `δ₀` fibre of Pitman's family. -/
theorem lambdaRate_dirac_zero {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    Blindness.lambdaCoalescentMergerRate (Measure.dirac 0) b k = kingmanRate b k := by
  unfold Blindness.lambdaCoalescentMergerRate kingmanRate
  rw [integral_dirac]
  by_cases h : k = 2
  · subst h
    norm_num
  · rw [if_neg h]
    have hk3 : k - 2 ≠ 0 := by omega
    rw [zero_pow hk3]
    ring

/-! ### Consistency forces Kingman's `1`

`Descent.Coalescent.Rates` takes the per-pair rate to be `1` and calls it a choice of time
unit.  That is true, but it is not the whole story: once multiple mergers are excluded,
consistency forces the binary rate to be the SAME at every sample size.  A coalescent whose
pair rate depended on how many other lineages were present would not restrict to itself. -/

/-- **A binary-merger coalescent has a sample-size-independent pair rate.**  If no three
blocks ever merge at once, Pitman's condition reads `λ_{b,2} = λ_{b+1,2}`: the extra block
contributes nothing, because the `(k+1)`-term that would account for it is zero.

So the `1` in K-C (1.3) is not merely a unit convention -- the convention is only free to
choose one number, and consistency is what makes one number enough. -/
theorem binaryRate_const_of_consistent {lam : ℕ → ℕ → ℝ} (hcons : IsConsistentRates lam)
    (hbin : ∀ b k, 3 ≤ k → lam b k = 0) {b : ℕ} (hb : 2 ≤ b) :
    lam b 2 = lam (b + 1) 2 := by
  have h := hcons b 2 (le_refl 2) hb
  rw [hbin (b + 1) 3 (by omega)] at h
  linarith

/-- **And therefore it is `λ_{2,2}` at every sample size.**  Induction on the sample size:
the pair rate never changes, so a binary-merger coalescent is determined by one number. -/
theorem binaryRate_eq_base {lam : ℕ → ℕ → ℝ} (hcons : IsConsistentRates lam)
    (hbin : ∀ b k, 3 ≤ k → lam b k = 0) : ∀ b : ℕ, 2 ≤ b → lam b 2 = lam 2 2 := by
  intro b hb
  induction b with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have : m + 1 = 2 := by omega
        rw [this]
      · rw [← binaryRate_const_of_consistent hcons hbin hm]
        exact ih hm

/-- **Kingman's array is the only normalised binary-merger coalescent.**  Consistent, no
multiple mergers, unit pair rate at the smallest sample: that pins every entry.

This is the sense in which K-C (1.3) is not a modelling choice among many.  Given that
lineages merge two at a time, the rate array is forced. -/
theorem eq_kingmanRate {lam : ℕ → ℕ → ℝ} (hcons : IsConsistentRates lam)
    (hbin : ∀ b k, 3 ≤ k → lam b k = 0) (hnorm : lam 2 2 = 1) {b k : ℕ}
    (hk : 2 ≤ k) (hkb : k ≤ b) : lam b k = kingmanRate b k := by
  unfold kingmanRate
  by_cases h : k = 2
  · subst h
    rw [if_pos rfl, binaryRate_eq_base hcons hbin b hkb, hnorm]
  · rw [if_neg h]
    exact hbin b k (by omega)

/-- The total rate out of a state with `b` blocks: every `k`-subset that can merge, at its
own rate.  For Kingman this is `C(b,2)`; in general it is what
`Descent.Coalescent.StateSpace.card_covers` would count if covers allowed multiple
mergers. -/
noncomputable def totalRate (lam : ℕ → ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 b, (b.choose k : ℝ) * lam b k

/-- **Kingman's total rate is `deathRate`.**  The general formula collapses to `C(b,2)`
because every term but `k = 2` carries rate zero -- which is exactly the sense in which the
`n`-coalescent is the multiple-merger coalescent with no multiple mergers. -/
theorem totalRate_kingman {b : ℕ} (hb : 2 ≤ b) :
    totalRate kingmanRate b = deathRate b := by
  unfold totalRate kingmanRate
  rw [Finset.sum_eq_single 2]
  · rw [if_pos rfl, mul_one]
    have h := card_covers_eq_deathRate (Delta b)
    rw [card_covers, blocks_bot] at h
    exact h
  · intro k _ hk2
    rw [if_neg hk2, mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 2, hb⟩) h

end Coalescent

end Descent
