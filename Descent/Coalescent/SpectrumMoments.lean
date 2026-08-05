/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SegregatingSites
import Mathlib.Tactic

namespace Descent

/-!
# Second moments: `Var(S_n)`, and why Watterson's estimator converges like `1/log n`

`Descent.Coalescent.SegregatingSites` computes `E(S_n) = θ a_{n-1}` and proves Watterson's
estimator unbiased.  An unbiased estimator with unbounded variance is useless, and the corpus
had no variance at all -- `Descent.Coalescent.Program` recorded that as an open item, since
without it the mean-zero Tajima numerator is a test that cannot be sized.

The variance follows from the same tree by the law of total variance.  Conditionally on the
tree of total length `L`, `S` is Poisson with mean `½θL`, so

  `Var(S) = E(Var(S | L)) + Var(E(S | L)) = ½θ E(L) + (½θ)² Var(L)`,

and `Var(L)` needs only that the phase durations are independent, which
`Descent.Coalescent.TransitVariance` already assumes and names.  While `k` lineages are alive
the tree gains length at rate `k`, so that phase contributes `k² Var(τ_k) = (k/d_k)²` -- the
SQUARE of the segment length `Descent.Coalescent.BranchLength` derives.  Since `k/d_k` is
`2/(k-1)`,

  `Var(L_n) = 4 Σ_{i=1}^{n-1} i⁻²`,        hence   `Var(S_n) = θ a_{n-1} + θ² b_{n-1}`,

with `b_m = Σ_{i≤m} i⁻²` -- Watterson (1975)'s second constant, and the `b` that appears in
every published formula for Tajima's `D`.

## The consequence that matters

`b_m` is BOUNDED -- `harmonicSumSq_le_two` -- while `a_m` diverges.  So

  `Var(θ_W) = θ/a_{n-1} + θ² b_{n-1}/a_{n-1}²  →  0`,

and `exists_varWattersonEstimator_lt` proves it: the estimator is consistent.  But it is
consistent in `a_{n-1} ≈ log n`, so halving the standard error costs a squaring of the sample
size.  That is the precise sense in which sequencing more individuals at one locus buys
information, and the precise sense in which it buys very little -- the same `log n` that
`Descent.Coalescent.BranchLength` finds in the tree length, appearing now as a rate of
convergence.

`Descent.Coalescent.TransitVariance` says the tree HEIGHT does not concentrate at all; this
says the tree LENGTH does, logarithmically.  Both are the same ladder read at different
weights, and the difference is the weight `k`.

## What is still not here

`Var(π)` and `Cov(π, θ_W)`, hence the exact denominator of Tajima's `D`.  Those need the
joint law of pairwise differences across pairs, not merely the tree's total length, and the
corpus has no such joint law.  What is closed is the `S`-side second moment, which is the
half that shares the tree with everything else in this group.

## Main results

- `harmonicSumSq`: `b_m = Σ_{i≤m} i⁻²`, and `harmonicSumSq_le_two`: it is bounded.
- `varTotalBranchLength_eq`: **`Var(L_n) = 4 b_{n-1}`**, from squared segment lengths.
- `varSegregatingSites_eq_totalVariance`: **the law of total variance, as an identity**.
- `varWattersonEstimator_le`: a bound falling like `1/a_{n-1}`.
- `exists_varWattersonEstimator_lt`: **the estimator is consistent** -- and only in `log n`.
-/

namespace Coalescent

open Finset

/-! ### `b_m`, and the fact that it is bounded -/

/-- `b_m = Σ_{i=1}^{m} i⁻²`, Watterson's second constant.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of reciprocal squares. -/
noncomputable def harmonicSumSq (m : ℕ) : ℝ := ∑ i ∈ range m, 1 / ((i : ℝ) + 1) ^ 2

@[simp] theorem harmonicSumSq_zero : harmonicSumSq 0 = 0 := by simp [harmonicSumSq]

theorem harmonicSumSq_succ (m : ℕ) :
    harmonicSumSq (m + 1) = harmonicSumSq m + 1 / ((m : ℝ) + 1) ^ 2 := by
  unfold harmonicSumSq
  rw [sum_range_succ]

theorem harmonicSumSq_nonneg (m : ℕ) : 0 ≤ harmonicSumSq m := by
  unfold harmonicSumSq
  refine sum_nonneg fun i _ ↦ ?_
  positivity

/-- The telescoping bound: `b_m ≤ 2 - 1/m` for `m ≥ 1`, because `(i+1)⁻² ≤ i⁻¹ - (i+1)⁻¹`.
Stated in the sharp form because the induction needs it; `harmonicSumSq_le_two` is the
consequence anyone uses. -/
theorem harmonicSumSq_le {m : ℕ} (hm : 1 ≤ m) : harmonicSumSq m ≤ 2 - 1 / (m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [harmonicSumSq]
  | succ p hp ih =>
      have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have hstep : 1 / ((p : ℝ) + 1) ^ 2 ≤ 1 / (p : ℝ) - 1 / ((p : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hppos) (by linarith : ((p : ℝ) + 1) ≠ 0),
          div_le_div_iff₀ (by positivity) (mul_pos hppos (by linarith))]
        nlinarith
      have := harmonicSumSq_succ p
      push_cast
      linarith [ih]

/-- **`b_m < 2`, for every `m`.**  The bounded constant beside the divergent one: this is why
Watterson's estimator is consistent at all. -/
theorem harmonicSumSq_le_two (m : ℕ) : harmonicSumSq m ≤ 2 := by
  cases m with
  | zero => norm_num [harmonicSumSq]
  | succ p =>
      have h := harmonicSumSq_le (by omega : 1 ≤ p + 1)
      have hpos : (0 : ℝ) < 1 / ((p : ℝ) + 1) := by positivity
      push_cast at h
      linarith

/-! ### The variance of the tree length -/

/-- `Var(L_n)`, the variance of the total branch length: the phase durations being
independent, the squared lineage-count weights add.

Empirical status: DERIVED given independence, which is ASSUMED and named at
`Descent.Coalescent.TransitVariance`.  The summand is the SQUARE of
`BranchLength.expectedSegmentLength`, because a phase of mean duration `d_k⁻¹` contributing
length at rate `k` contributes variance `k² d_k⁻²` -- and that `d_k⁻²` is computed from the
density in `Descent.Coalescent.HoldingSecondMoment`, not quoted. -/
noncomputable def varTotalBranchLength (n : ℕ) : ℝ :=
  ∑ j ∈ range (n - 1), expectedSegmentLength (j + 2) ^ 2

/-- **`Var(L_n) = 4 b_{n-1}`.**  Each phase contributes `(2/(k-1))²`, and the sum of those is
four times the reciprocal-square sum.  Note the contrast with `BranchLength.expectedTotalBranchLength_eq_harmonic`: the mean is `2 a_{n-1}` and diverges,
the variance is `4 b_{n-1}` and does not. -/
theorem varTotalBranchLength_eq (n : ℕ) :
    varTotalBranchLength n = 4 * harmonicSumSq (n - 1) := by
  unfold varTotalBranchLength harmonicSumSq
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [expectedSegmentLength_eq, div_pow]
  ring

theorem varTotalBranchLength_nonneg (n : ℕ) : 0 ≤ varTotalBranchLength n := by
  rw [varTotalBranchLength_eq]
  have := harmonicSumSq_nonneg (n - 1)
  linarith

/-- **The tree length concentrates.**  Its variance is under `8` whatever the sample size,
while its mean grows without bound -- so the coefficient of variation vanishes, unlike the
tree height's, which `TransitVariance.coefficientOfVariation_gt_half` bounds below. -/
theorem varTotalBranchLength_le_eight (n : ℕ) : varTotalBranchLength n ≤ 8 := by
  rw [varTotalBranchLength_eq]
  have := harmonicSumSq_le_two (n - 1)
  linarith

/-! ### The variance of the site count -/

/-- `Var(S_n) = θ a_{n-1} + θ² b_{n-1}`, Watterson (1975).

Empirical status: DERIVED.  It is the law of total variance applied to the Poisson mutation
premise of `SegregatingSites.expectedSegregatingSites`, whose two verdicts it inherits: the
tree factors are derived from the rate ladder, the Poisson-with-mean-`½θL` conditional law is
assumed.  `varSegregatingSites_eq_totalVariance` is the decomposition made explicit. -/
noncomputable def varSegregatingSites (θ : ℝ) (n : ℕ) : ℝ :=
  θ * harmonicSum (n - 1) + θ ^ 2 * harmonicSumSq (n - 1)

/-- **The law of total variance, as an identity.**  `Var(S) = ½θ E(L) + (½θ)² Var(L)`: the
first term is the Poisson noise given the tree, the second is the tree's own variability
transmitted through the mutation rate.  Writing it this way shows there is no third term, and
that the two contributions are the mean and the variance of the SAME `L`. -/
theorem varSegregatingSites_eq_totalVariance (θ : ℝ) (n : ℕ) :
    varSegregatingSites θ n
      = θ / 2 * expectedTotalBranchLength n + (θ / 2) ^ 2 * varTotalBranchLength n := by
  rw [expectedTotalBranchLength_eq_harmonic, varTotalBranchLength_eq]
  unfold varSegregatingSites
  ring

theorem varSegregatingSites_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    0 ≤ varSegregatingSites θ n := by
  unfold varSegregatingSites
  have h1 := harmonicSum_nonneg (n - 1)
  have h2 := harmonicSumSq_nonneg (n - 1)
  have : 0 ≤ θ ^ 2 := sq_nonneg θ
  nlinarith

/-! ### And of the estimator -/

/-- `Var(θ_W) = Var(S)/a_{n-1}²`: Watterson's estimator divides `S` by a constant, so its
variance divides by the square.

Empirical status: DERIVED from `varSegregatingSites` and
`SegregatingSites.wattersonEstimator`. -/
noncomputable def varWattersonEstimator (θ : ℝ) (n : ℕ) : ℝ :=
  varSegregatingSites θ n / harmonicSum (n - 1) ^ 2

/-- **A bound falling like `1/a_{n-1}`.**  Both terms of the variance carry at least one
factor of `a_{n-1}` in the denominator, and `b` is bounded, so the whole thing is at most
`(θ + 2θ²)/a_{n-1}` once `a_{n-1} ≥ 1` -- which holds from `n = 2` on. -/
theorem varWattersonEstimator_le {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} (hn : 1 ≤ harmonicSum (n - 1)) :
    varWattersonEstimator θ n ≤ (θ + 2 * θ ^ 2) / harmonicSum (n - 1) := by
  have ha : (0 : ℝ) < harmonicSum (n - 1) := by linarith
  have hb := harmonicSumSq_le_two (n - 1)
  have hb0 := harmonicSumSq_nonneg (n - 1)
  have hsq : 0 ≤ θ ^ 2 := sq_nonneg θ
  unfold varWattersonEstimator varSegregatingSites
  rw [div_le_div_iff₀ (pow_pos ha 2) ha]
  have h1 : θ ^ 2 * harmonicSumSq (n - 1) ≤ 2 * θ ^ 2 := by nlinarith
  have h2 : (2 : ℝ) * θ ^ 2 * harmonicSum (n - 1)
      ≤ 2 * θ ^ 2 * harmonicSum (n - 1) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsq)
      (mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ harmonicSum (n - 1) - 1))]
  nlinarith [mul_le_mul_of_nonneg_right h1 ha.le, h2]

/-- **Watterson's estimator is consistent.**  For every tolerance there is a sample size at
which its variance is below that tolerance.

The rate is the point.  The bound falls like `1/a_{n-1}`, and `a_{n-1}` is the harmonic
number, so the sample size needed for a given precision grows EXPONENTIALLY in that
precision.  A study that doubles its cohort improves this estimator by the difference between
two logarithms.  `Descent.Coalescent.BranchLength.tendsto_expectedTotalBranchLength_atTop` is
the same `log n` seen as growth; here it is seen as a rate of convergence, and the two are
the same statement about the same sum. -/
theorem exists_varWattersonEstimator_lt {θ : ℝ} (hθ : 0 ≤ θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, varWattersonEstimator θ n < ε := by
  obtain ⟨m, hm⟩ := (tendsto_harmonicSum_atTop.eventually_ge_atTop
    (max 1 ((θ + 2 * θ ^ 2 + 1) / ε))).exists
  have hmax1 : (1 : ℝ) ≤ max 1 ((θ + 2 * θ ^ 2 + 1) / ε) := le_max_left _ _
  have hmax2 : (θ + 2 * θ ^ 2 + 1) / ε ≤ max 1 ((θ + 2 * θ ^ 2 + 1) / ε) := le_max_right _ _
  have hone : (1 : ℝ) ≤ harmonicSum m := le_trans hmax1 hm
  have hbig : (θ + 2 * θ ^ 2 + 1) / ε ≤ harmonicSum m := le_trans hmax2 hm
  have hpos : (0 : ℝ) < harmonicSum m := by linarith
  refine ⟨m + 1, ?_⟩
  have hidx : m + 1 - 1 = m := rfl
  have hbound := varWattersonEstimator_le hθ (n := m + 1) (by rw [hidx]; exact hone)
  rw [hidx] at hbound
  have hkey : (θ + 2 * θ ^ 2) / harmonicSum m < ε := by
    rw [div_lt_iff₀ hpos]
    have hmul : (θ + 2 * θ ^ 2 + 1) ≤ ε * harmonicSum m := by
      rw [div_le_iff₀ hε] at hbig
      linarith
    linarith
  linarith

/-! ### Tajima's variance, where the corpus can check it -/

/-- Tajima (1989)'s expression for `Var(π)`:
`(n+1)/(3(n-1)) · θ + 2(n²+n+3)/(9n(n-1)) · θ²`.

Empirical status: DERIVED, in `Descent.Coalescent.TajimaVariance`.  It was written here to be
CHECKED -- `varPairwise_two_eq` verifies it at `n = 2` -- and
`TajimaVariance.varPairwiseFromTree_eq_tajima` now derives it for every `n ≥ 2` from the
tree: the per-pair variance, the two coalescence-time covariances, the two shared-path
lengths, and the counts of the pair classes. -/
noncomputable def tajimaVarPairwise (θ : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / (3 * ((n : ℝ) - 1)) * θ
    + 2 * ((n : ℝ) ^ 2 + (n : ℝ) + 3) / (9 * (n : ℝ) * ((n : ℝ) - 1)) * θ ^ 2

/-- **At `n = 2` Tajima's formula is this corpus's `Var(S₂)`.**  A sample of two has one pair,
so `π` IS `S`, and the two developments must agree: Tajima's expression collapses to
`θ + θ²`, which is `varSegregatingSites θ 2` with `a_1 = b_1 = 1`.

This is the only sample size at which the check is available, because for `n ≥ 3` the pairwise
differences overlap and `Var(π)` stops being a function of the tree's total length.  That it
passes is evidence the two conventions match; it is not the general formula, and
`Descent.Coalescent.Program` says so. -/
theorem varPairwise_two_eq (θ : ℝ) :
    tajimaVarPairwise θ 2 = varSegregatingSites θ 2 := by
  have h1 : harmonicSum (2 - 1) = 1 := by norm_num
  have h2 : harmonicSumSq (2 - 1) = 1 := by
    norm_num [harmonicSumSq]
  unfold tajimaVarPairwise varSegregatingSites
  rw [h1, h2]
  norm_num

end Coalescent

end Descent
