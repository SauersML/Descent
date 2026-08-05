/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.BranchLength
import Mathlib.Tactic

namespace Descent

/-!
# Watterson's estimator, pairwise diversity, and Tajima's `D`, from the tree

`Descent.Coalescent.BranchLength` derives the expected total length of the `n`-coalescent
tree, `E(L_n) = 2 a_{n-1}`, from the rate ladder and nothing else.  This file puts mutations
on that tree and reads off the three summary statistics that every empirical population-
genetics paper reports.

The mutation mechanism is the one K-G p.34 states: *"mutations occur in a Poisson way at a
rate `½θ`, independently, to the equivalence classes of `R_t`"*.  A Poisson process of rate
`½θ` run along a total branch length `L` has mean `½θL` points, so under the infinite-sites
convention -- every mutation lands at a previously unmutated site, hence is visible as its
own segregating site -- the expected number of segregating sites in a sample of `n` is

  `E(S_n) = ½ θ E(L_n) = θ a_{n-1}`,                                   Watterson (1975)

and `S_n / a_{n-1}` is an unbiased estimator of `θ`.  At `n = 2` the tree is two branches of
the same length and `a_1 = 1`, so `E(S_2) = θ`: the mean number of pairwise differences,
`π`, estimates `θ` with no normalisation at all.  Two estimators of one parameter is the
whole of Tajima (1989): their difference has expectation zero under the null, so a departure
from zero is evidence against the model that produced both.

## What is derived and what is assumed, exactly

* DERIVED: `E(S_n) = θ a_{n-1}`, from `expectedTotalBranchLength_eq_harmonic`, which is
  itself derived from the ladder `d_k`, which `StateSpace.card_covers_eq_deathRate` derives
  from the cardinality of the state space.  Nothing in that chain is posited.
* DERIVED: unbiasedness of Watterson's estimator, and `E(π) = θ`, and `E(π - θ_W) = 0`.
* ASSUMED, and marked at `expectedSegregatingSites`: that mutation is Poisson at rate `½θ`
  along the branches, independent of the genealogy, and that every mutation is visible
  (infinite sites).  The first is K-G's modelling premise; the second is a statement about
  the marker technology, not about the population.  Neither is derived here, and both are
  false in regimes the corpus records elsewhere -- recurrent mutation is exactly K-G's
  criticism of the Ohta-Kimura model (3.7).

## Why this is not a fourth name for `θ`

`Descent.Coalescent.Mutation` has `θ` as the mutation-drift balance `2Nβ → θ` and derives
Ewens's (3.8) from it; `Descent.Coalescent.NeutralMutation` has its normalisation.  This file
adds no new `θ`: `expectedSegregatingSites` takes the same scalar and multiplies the tree
length by it.  The only new definition with a formula in it is `wattersonEstimator`, and its
content is a division.

## Main results

- `expectedSegregatingSites_eq`: **`E(S_n) = θ a_{n-1}`**, Watterson (1975).
- `wattersonEstimator_unbiased`: `E(S_n)/a_{n-1} = θ`, for `n ≥ 2`.
- `expectedPairwiseDifferences_eq`: `E(π) = θ`, the `n = 2` case.
- `expectedTajimaNumerator_eq_zero`: **`E(π - θ_W) = 0`**, the null Tajima (1989) tests.
- `tendsto_expectedSegregatingSites_atTop`: `E(S_n) → ∞` for `θ > 0`, while the tree height
  stays under `2` -- `variantDiscovery_unbounded` states the pair.
-/

namespace Coalescent

open Finset Filter Topology

/-! ### Mutations on the tree -/

/-- `E(S_n)`, the expected number of segregating sites in a sample of `n` under the
infinite-sites model with scaled mutation rate `θ`: half `θ` times the expected total branch
length.

Empirical status: MIXED.  The tree factor `E(L_n)` is DERIVED
(`expectedTotalBranchLength_eq_harmonic`, off the rate ladder, which is a cardinality).  The
mutation factor is ASSUMED: mutations Poisson at rate `½θ` per unit branch length,
independent of the genealogy (K-G p.34), and every mutation visible at a fresh site
(infinite sites).  The head is `MIXED` because the two halves carry different verdicts, and
the sentences above are the two verdicts the term promises.  Recurrent mutation breaks the
second half and is exactly what K-G (3.7) objects to in the Ohta-Kimura model. -/
noncomputable def expectedSegregatingSites (θ : ℝ) (n : ℕ) : ℝ :=
  θ / 2 * expectedTotalBranchLength n

/-- **Watterson (1975): `E(S_n) = θ a_{n-1}`.**  The harmonic number is not a fitted constant
and not a convention; it is the total length of the coalescent tree divided by two, and the
two cancels against the `½θ` of the Poisson rate. -/
theorem expectedSegregatingSites_eq (θ : ℝ) (n : ℕ) :
    expectedSegregatingSites θ n = θ * harmonicSum (n - 1) := by
  unfold expectedSegregatingSites
  rw [expectedTotalBranchLength_eq_harmonic]
  ring

@[simp] theorem expectedSegregatingSites_one (θ : ℝ) : expectedSegregatingSites θ 1 = 0 := by
  rw [expectedSegregatingSites_eq]
  simp

/-- A sample of two segregates at `θ` sites in expectation: `a_1 = 1`. -/
theorem expectedSegregatingSites_two (θ : ℝ) : expectedSegregatingSites θ 2 = θ := by
  rw [expectedSegregatingSites_eq]
  norm_num

theorem expectedSegregatingSites_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) :
    0 ≤ expectedSegregatingSites θ n := by
  rw [expectedSegregatingSites_eq]
  exact mul_nonneg hθ (harmonicSum_nonneg _)

/-! ### The estimator

Watterson's estimator inverts the formula above.  Unbiasedness is then an identity, and
saying so is the point: an estimator is unbiased *because* the expectation it inverts was
computed from the mechanism, not because a simulation failed to reject it. -/

/-- Watterson's `θ_W = S / a_{n-1}`.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is `expectedSegregatingSites` solved for `θ`,
and `wattersonEstimator_unbiased` is that statement.  Whether a given sample's `S` was
generated by the model is the empirical question; the division is not. -/
noncomputable def wattersonEstimator (S : ℝ) (n : ℕ) : ℝ := S / harmonicSum (n - 1)

/-- The harmonic normaliser is nonzero as soon as the sample has two members, which is what
makes the estimator defined.  Below that there are no pairs and nothing to estimate. -/
theorem harmonicSum_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < harmonicSum (n - 1) := by
  have h1 : (1 : ℕ) ≤ n - 1 := by omega
  have := harmonicSum_strictMono (lt_of_lt_of_le Nat.zero_lt_one h1)
  simpa using this

/-- **Watterson's estimator is unbiased.**  Substituting the derived expectation returns
`θ` exactly. -/
theorem wattersonEstimator_unbiased {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    wattersonEstimator (expectedSegregatingSites θ n) n = θ := by
  have hpos := harmonicSum_pos_of_two_le hn
  unfold wattersonEstimator
  rw [expectedSegregatingSites_eq, mul_div_assoc, div_self hpos.ne', mul_one]

/-! ### Pairwise diversity

`π` is the mean number of differences between two sampled sequences.  Two sequences are a
sample of size two, so `E(π)` is `E(S_2)`, and that is `θ`.  No new calculation is needed,
and doing it as a definition rather than a second derivation is the point: a corpus with two
derivations of `θ` has two places to be wrong. -/

/-- `E(π)`, the expected number of pairwise differences: the two-sample case of `E(S)`.

Empirical status: DERIVED -- it is `expectedSegregatingSites θ 2`, definitionally. -/
noncomputable def expectedPairwiseDifferences (θ : ℝ) : ℝ := expectedSegregatingSites θ 2

/-- **`E(π) = θ`.**  Tajima's estimator is unbiased too, and for the simplest possible
reason: a pair of sequences has a tree of two branches, each of expected length `1`. -/
theorem expectedPairwiseDifferences_eq (θ : ℝ) : expectedPairwiseDifferences θ = θ :=
  expectedSegregatingSites_two θ

/-! ### Tajima's `D`

Tajima (1989) compares the two estimators.  Under the null -- a constant-size neutral
population, which is exactly the model this file has been computing in -- their difference
has mean zero, and the whole test is that a departure indicates a violated premise.  Which
premise is a separate question the statistic cannot answer, and
`Descent.Blindness` is where the corpus records that kind of non-identifiability. -/

/-- The numerator of Tajima's `D`: `π - θ_W`, both estimators taken at their expectations.

Empirical status: DERIVED.  Both terms are computed above from the same tree; this
subtracts them. -/
noncomputable def expectedTajimaNumerator (θ : ℝ) (n : ℕ) : ℝ :=
  expectedPairwiseDifferences θ - wattersonEstimator (expectedSegregatingSites θ n) n

/-- **Tajima's `D` has mean-zero numerator under the coalescent null.**  This is what makes
the statistic a test: both estimators target `θ`, so their difference targets nothing, and
any systematic departure is a fact about the population rather than about the estimators.

The theorem is stated at the expectations rather than the sampling distribution.  The
variance of `D`, and hence its calibration, is NOT here: it requires the second moments of
the tree, which need the joint law of the holding times and not merely their means. -/
theorem expectedTajimaNumerator_eq_zero {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    expectedTajimaNumerator θ n = 0 := by
  unfold expectedTajimaNumerator
  rw [expectedPairwiseDifferences_eq, wattersonEstimator_unbiased hn]
  ring

/-! ### Sample size

The contrast `BranchLength.height_bounded_length_unbounded` becomes, with mutations on the
tree, a statement about data: doubling the sample does not push the common ancestor back,
and does keep finding new variants. -/

/-- **Segregating sites accumulate without bound.**  For any positive mutation rate, the
expected number of segregating sites in a sample of `n` exceeds any bound for `n` large --
this is `E(L_n) → ∞` with a positive factor. -/
theorem tendsto_expectedSegregatingSites_atTop {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n : ℕ ↦ expectedSegregatingSites θ (n + 1)) atTop atTop := by
  have hcomp : (fun n : ℕ ↦ expectedSegregatingSites θ (n + 1))
      = fun n : ℕ ↦ θ * harmonicSum n := by
    funext n
    rw [expectedSegregatingSites_eq, show n + 1 - 1 = n from rfl]
  rw [hcomp]
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [tendsto_harmonicSum_atTop.eventually_ge_atTop (b / θ)] with n hn
  have hmul : θ * (b / θ) ≤ θ * harmonicSum n := mul_le_mul_of_nonneg_left hn hθ.le
  have hbe : θ * (b / θ) = b := by field_simp
  rw [hbe] at hmul
  exact hmul

/-- **The pair, stated once.**  Every sample has a most recent common ancestor at expected
depth under `2`; no bound holds on the number of variants a large enough sample segregates.
A study that stops enrolling because "the tree is already deep enough" has confused the two.

This is the coalescent's own version of the corpus's recurring theme: a bounded summary and
an unbounded one, computed from the same process, and a design that reads the first as
speaking for the second. -/
theorem variantDiscovery_unbounded {θ : ℝ} (hθ : 0 < θ) (B : ℝ) :
    (∀ n : ℕ, meanTransitTime n < 2) ∧ ∃ n : ℕ, B < expectedSegregatingSites θ n := by
  refine ⟨meanTransitTime_lt_two, ?_⟩
  obtain ⟨n, hn⟩ :=
    ((tendsto_expectedSegregatingSites_atTop hθ).eventually_gt_atTop B).exists
  exact ⟨n + 1, hn⟩

end Coalescent

end Descent
