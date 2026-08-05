/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Tactic

namespace Descent

/-!
# The variance of the tree height, and why one locus is never enough

`Descent.Coalescent.Rates` proves `E(T_n) = 2 - 2/n < 2`: the expected time back to a
sample's most recent common ancestor is bounded however large the sample.  A bounded mean is
easy to misread as a small quantity, and the misreading has a practical form -- that a single
locus's genealogy, being shallow and bounded, is a reliable summary of the population's
history.

It is not, and the reason is the variance.  K-C (1.12) writes `T_n = Σ_{r=2}^n τ_r` with the
`τ_r` INDEPENDENT and exponential of rate `d_r` (K-G (5.6)), so the variances add:

  `Var(T_n) = Σ_{r=2}^{n} d_r⁻²`.

The first term alone is `d_2⁻² = 1`, and every later term is positive.  So the variance is at
least `1` for every sample size, while the mean is under `2` -- which gives

  `E(T_n)²/4 < Var(T_n)`,                                   `coefficientOfVariation_gt_half`

the standard deviation exceeding half the mean, uniformly in `n`.  The tree height does not
concentrate, and no amount of extra sampling at one locus makes it concentrate: the extra
sample members contribute to the top of the tree, where the waiting times are short, and the
single long wait at `k = 2` that dominates both moments is common to every sample.

This is the coalescent's own statement of why population-genetic inference is done across
loci rather than across individuals.  Independent loci give independent trees; more
individuals give a better-resolved version of ONE tree, whose height was never the average of
anything.

## What is proved and what is assumed

* ASSUMED: that the `τ_r` are independent, so that the variances add.  This is K-C Theorem 1,
  and `Descent.Coalescent.Program` item 4 records it as settled in the constructive direction
  (`Law.coalescentLaw_prod`) and open in the converse.  `varTransitTime` is therefore the
  variance of the CONSTRUCTED coalescent, which is the one the corpus has.
* DERIVED: everything else.  `d_r⁻² ≤ d_r⁻¹` because `d_r ≥ 1` for `r ≥ 2`, so the variance is
  bounded by the mean and hence by `2`; and the `k = 2` term bounds it below by `1`.

## Main results

- `varTransitTime`: `Σ_{r=2}^{n} d_r⁻²`.
- `one_le_varTransitTime`: **at least `1`, for every sample size**.
- `varTransitTime_le_meanTransitTime`, `varTransitTime_lt_two`: and under `2`.
- `coefficientOfVariation_gt_half`: **`E(T_n)²/4 < Var(T_n)`** -- the height never
  concentrates.
-/

namespace Coalescent

open Finset

/-- `Var(T_n)`, the variance of the transit time: the sum of `d_r⁻²` over the `n - 1` phases,
the variances of independent exponentials adding.

Empirical status: DERIVED given independence, which is ASSUMED and named -- see the module
docstring.  The summand `d_r⁻²` is the variance of an exponential of rate `d_r`, which
`Descent.Coalescent.HoldingTime` supplies the density for. -/
noncomputable def varTransitTime (n : ℕ) : ℝ :=
  ∑ k ∈ range (n - 1), (1 / deathRate (k + 2)) ^ 2

@[simp] theorem varTransitTime_one : varTransitTime 1 = 0 := by
  simp [varTransitTime]

theorem varTransitTime_nonneg (n : ℕ) : 0 ≤ varTransitTime n := by
  unfold varTransitTime
  refine sum_nonneg fun k _ ↦ ?_
  positivity

/-- The ladder is at least `1` from `k = 2` on, so its reciprocal is at most `1`.  This is
what makes the variance smaller than the mean rather than larger. -/
theorem one_le_deathRate_succ_succ (k : ℕ) : (1 : ℝ) ≤ deathRate (k + 2) := by
  unfold deathRate
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  push_cast
  nlinarith

theorem one_div_deathRate_le_one (k : ℕ) : 1 / deathRate (k + 2) ≤ 1 := by
  have h := one_le_deathRate_succ_succ k
  rw [div_le_one (by linarith)]
  linarith

/-- **The variance is bounded by the mean.**  Termwise, because squaring a number in `[0,1]`
does not increase it, and every `d_r⁻¹` is in `[0,1]`. -/
theorem varTransitTime_le_meanTransitTime (n : ℕ) :
    varTransitTime n ≤ meanTransitTime n := by
  unfold varTransitTime meanTransitTime
  refine sum_le_sum fun k _ ↦ ?_
  have hle := one_div_deathRate_le_one k
  have hpos : (0 : ℝ) ≤ 1 / deathRate (k + 2) := by
    have := one_le_deathRate_succ_succ k
    positivity
  nlinarith

/-- And therefore under `2`, the same bound the mean obeys. -/
theorem varTransitTime_lt_two (n : ℕ) : varTransitTime n < 2 :=
  lt_of_le_of_lt (varTransitTime_le_meanTransitTime n) (meanTransitTime_lt_two n)

/-- **At least `1`, for every sample size.**  The `k = 2` phase -- the final wait, while two
lineages remain -- has variance `d_2⁻² = 1` on its own, and every earlier phase adds more.
That single wait is common to every sample, which is why enlarging the sample cannot shrink
the spread. -/
theorem one_le_varTransitTime {n : ℕ} (hn : 2 ≤ n) : 1 ≤ varTransitTime n := by
  have hmem : (0 : ℕ) ∈ range (n - 1) := mem_range.mpr (by omega)
  have hnn : ∀ k ∈ range (n - 1), (0 : ℝ) ≤ (1 / deathRate (k + 2)) ^ 2 := by
    intro k _
    positivity
  have hsingle : (1 / deathRate (0 + 2)) ^ 2 ≤ varTransitTime n :=
    single_le_sum hnn hmem
  have hd : deathRate (0 + 2) = 1 := by
    rw [show (0 : ℕ) + 2 = 2 from rfl]
    exact deathRate_two
  rw [hd] at hsingle
  simpa using hsingle

/-- **The tree height never concentrates.**  Its standard deviation exceeds half its mean at
every sample size: the mean is under `2`, so its square is under `4` and a quarter of that
under `1`, while the variance is at least `1`.

A single locus therefore reports a time to common ancestry whose spread is comparable to its
value, no matter how many individuals were sequenced.  Inference about demography needs
independent trees, which means independent loci; more individuals resolve one tree better and
do not average anything.  `Descent.Coalescent.BranchLength.height_bounded_length_unbounded`
says what more individuals DO buy -- length, and hence variants -- and this says what they do
not. -/
theorem coefficientOfVariation_gt_half {n : ℕ} (hn : 2 ≤ n) :
    meanTransitTime n ^ 2 / 4 < varTransitTime n := by
  have hlt := meanTransitTime_lt_two n
  have hnn := meanTransitTime_nonneg n
  have hvar := one_le_varTransitTime hn
  have hsq : meanTransitTime n ^ 2 < 4 := by nlinarith
  linarith

/-- The pair case, where both moments are exact: mean `1`, variance `1`.  A single pair of
sequences reports a coalescence time whose standard deviation IS its mean -- the exponential's
signature, and the sharpest form of the statement above. -/
theorem varTransitTime_two : varTransitTime 2 = 1 := by
  unfold varTransitTime
  rw [show (2 : ℕ) - 1 = 1 from rfl, sum_range_one, show (0 : ℕ) + 2 = 2 from rfl,
    deathRate_two]
  norm_num

end Coalescent

end Descent
