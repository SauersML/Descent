/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Ewens
import Descent.Coalescent.BranchLength
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# How many alleles a sample shows: `E(K_n) = Σ_{i<n} θ/(θ+i)`

`Descent.Coalescent.Ewens` proves the normalisation of K-G (3.8) by running Kingman's Chinese
restaurant: seating the `(n+1)`-st sample member at an existing class of size `λ` multiplies
the Ewens weight by `λ`, starting a new class multiplies it by `θ`, and the seatings of one
state therefore contribute `θ + n`.  Those three facts are a probability distribution over
seatings that nobody had divided out.

Dividing it out is this file.  `seating_new_class_prob` is the quotient

  `w(ξ + new class) / Σ_o w(ξ + o) = θ/(θ + n)`,

so the `(n+1)`-st sample member starts a new allelic class with probability `θ/(θ+n)`
whatever the current configuration -- the configuration cancels.  That independence of the
current state is the whole reason the expected number of classes is a SUM rather than a
recursion over configurations: `K_n` is a sum of `n` indicators, the `i`-th having mean
`θ/(θ+i)`, and expectation is linear whether or not they are independent.

  `E(K_n) = Σ_{i=0}^{n-1} θ/(θ+i)`.                              Ewens (1972), Watterson (1975)

This is the estimator population genetics actually uses on allele counts, as opposed to the
one `Descent.Coalescent.SegregatingSites` builds on site counts.  Two different summaries of
the same genealogy, two different estimators of the same `θ`, and their agreement or
disagreement is testable in exactly the way `expectedTajimaNumerator_eq_zero` makes the
site-based pair testable.

## What it says

* `expectedNumClasses_one_eq_harmonicSum`: at `θ = 1` the count IS the harmonic number that
  `Descent.Coalescent.BranchLength` derives as half the tree length.  Not an analogy -- the
  same `Σ 1/(i+1)`, reached from the mutation side rather than the branch side.
* `expectedNumClasses_two_eq`: at `n = 2`, `E(K_2) = 2 - 1/(1+θ)`, and `1/(1+θ)` is exactly
  the identity-by-descent probability K-G computes on p.34 and
  `Descent.Coalescent.Mutation.tendsto_identityByDescent` proves as a limit.  A pair shows one
  allele with that probability and two otherwise, so the two developments agree at the only
  sample size where both have a closed form.
* `tendsto_expectedNumClasses_atTop`: for `θ ≥ 1` the count diverges, like `θ log n`.  New
  alleles never stop appearing, for the same reason `E(L_n)` never stops growing: both are
  harmonic sums, and the tree's terminal branches are where both live.
* `expectedNumClasses_le`: and it never exceeds `n`, which is the check that the indicators
  are indicators.

## Main results

- `ewensWeight_pos`: the weight is positive, so the seating quotient is a probability.
- `seating_new_class_prob`: **`θ/(θ+n)`**, derived from the two Chinese-restaurant lemmas.
- `expectedNumClasses`: `E(K_n) = Σ_{i<n} θ/(θ+i)`.
- `expectedNumClasses_one_eq_harmonicSum`, `expectedNumClasses_two_eq`: the two bridges.
- `tendsto_expectedNumClasses_atTop`: unbounded.
-/

namespace Coalescent

open Finset Filter Topology
open scoped Classical

/-! ### The seating probability -/

/-- The Ewens weight is positive for a positive `θ`: a power of `θ` times a product of
factorials.  This is what lets the seating weights be divided into probabilities. -/
theorem ewensWeight_pos {n : ℕ} {θ : Descent.Core.Theta} (hθ : 0 < θ.value) (ξ : ER n) : 0 <
  ewensWeight θ ξ := by
  unfold ewensWeight
  refine mul_pos (pow_pos hθ _) ?_
  refine Finset.prod_pos fun c _ ↦ ?_
  exact_mod_cast Nat.factorial_pos _

/-- **The `(n+1)`-st sample member starts a new allelic class with probability `θ/(θ+n)`.**

Derived, not posited: the numerator is `Ewens.ewensWeight_extend_none` and the denominator is
`Ewens.sum_seatings_ewensWeight`, and the state `ξ` cancels between them.  That cancellation
is the content -- the chance of seeing a new allele depends on how many individuals have been
examined and not at all on what was seen in them. -/
theorem seating_new_class_prob {n : ℕ} {θ : Descent.Core.Theta} (hθ : 0 < θ.value) (ξ : ER n) (hb :
  1 ≤ blocks ξ) :
    ewensWeight θ (extend ξ none) / (∑ o : Option (Quotient ξ), ewensWeight θ (extend ξ o))
      = θ.value / (θ.value + (n : ℝ)) := by
  have hw : 0 < ewensWeight θ ξ := ewensWeight_pos hθ ξ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < θ.value + (n : ℝ) := by linarith
  rw [ewensWeight_extend_none θ ξ hb, sum_seatings_ewensWeight θ ξ hb,
    div_eq_div_iff (ne_of_gt (mul_pos hden hw)) (ne_of_gt hden)]
  ring

/-! ### The expected number of classes -/

/-- `E(K_n)`, the expected number of distinct alleles in a sample of `n` under the
infinite-alleles model with scaled mutation rate `θ`.

Empirical status: DERIVED.  `K_n` is the sum of the `n` indicators "the `i`-th sample member
starts a new class", whose means `seating_new_class_prob` computes off the Ewens weights, and
expectation is linear.  What is ASSUMED is the infinite-alleles convention itself -- every
mutation produces an allele never seen before -- which is K-G's model on p.33 and is a
statement about the marker, not the population. -/
noncomputable def expectedNumClasses (θ : Descent.Core.Theta) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, θ.value / (θ.value + (i : ℝ))

@[simp] theorem expectedNumClasses_zero (θ : Descent.Core.Theta) : expectedNumClasses θ 0 = 0 := by
  simp [expectedNumClasses]

theorem expectedNumClasses_succ (θ : Descent.Core.Theta) (n : ℕ) :
    expectedNumClasses θ (n + 1) = expectedNumClasses θ n + θ.value / (θ.value + (n : ℝ)) := by
  unfold expectedNumClasses
  rw [sum_range_succ]

/-- A sample of one shows one allele, whatever `θ`: the first draw always starts a class. -/
theorem expectedNumClasses_one {θ : Descent.Core.Theta} (hθ : 0 < θ.value) : expectedNumClasses θ 1
  = 1 := by
  unfold expectedNumClasses
  rw [sum_range_one, Nat.cast_zero, add_zero]
  exact div_self (ne_of_gt hθ)

/-- **`E(K_2) = 2 - 1/(1+θ)`.**  A pair shows one allele when neither line has mutated since
their common ancestor, which K-G computes on p.34 as `(1+θ)⁻¹` and
`Descent.Coalescent.Mutation.tendsto_identityByDescent` proves; otherwise it shows two.  So
`E(K_2) = 1·(1+θ)⁻¹ + 2·(1 - (1+θ)⁻¹)`, and that is what this says.

The two developments reach the same number from opposite directions -- one by a geometric sum
over coalescence times, the other by a Chinese restaurant -- and their agreement at `n = 2` is
the only place both have a closed form to compare. -/
theorem expectedNumClasses_two_eq {θ : Descent.Core.Theta} (hθ : 0 < θ.value) :
    expectedNumClasses θ 2 = 2 - 1 / (1 + θ.value) := by
  have hθ0 : θ.value ≠ 0 := ne_of_gt hθ
  have h2 : θ.value + (1 : ℝ) ≠ 0 := by linarith
  have hsum : θ.value / (θ.value + 1) + 1 / (θ.value + 1) = 1 := by
    rw [← add_div, div_self h2]
  have hcomm : (1 : ℝ) + θ.value = θ.value + 1 := by ring
  unfold expectedNumClasses
  rw [sum_range_succ, sum_range_one, Nat.cast_zero, Nat.cast_one, add_zero,
    div_self hθ0, hcomm]
  linarith

/-! ### Two bridges and a divergence -/

/-- **At `θ = 1` the allele count is the harmonic number.**  The same `Σ 1/(i+1)` that
`BranchLength.expectedTotalBranchLength_eq_harmonic` produces as half the expected tree
length, arrived at from the mutation side.  A corpus in which these were two constants would
have two places to be wrong; they are one. -/
theorem expectedNumClasses_one_eq_harmonicSum (n : ℕ) :
    expectedNumClasses ⟨1⟩ n = harmonicSum n := by
  unfold expectedNumClasses harmonicSum
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- For `θ ≥ 1` each class-opening probability dominates the harmonic term, because
`θ/(θ+i) ≥ 1/(1+i)` reduces to `i ≤ θi`. -/
theorem harmonicSum_le_expectedNumClasses {θ : Descent.Core.Theta} (hθ : 1 ≤ θ.value) (n : ℕ) :
    harmonicSum n ≤ expectedNumClasses θ n := by
  unfold harmonicSum expectedNumClasses
  refine sum_le_sum fun i _ ↦ ?_
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hden1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hden2 : (0 : ℝ) < θ.value + (i : ℝ) := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [mul_nonneg hi (sub_nonneg.mpr hθ)]

/-- **The number of alleles diverges.**  For `θ ≥ 1` a large enough sample shows more
distinct alleles than any bound -- growth like `θ log n`, the same harmonic growth as the
tree length, and for the same reason: new alleles arrive on terminal branches, whose total
length is what `BranchLength.tendsto_expectedTotalBranchLength_atTop` sends to infinity. -/
theorem tendsto_expectedNumClasses_atTop {θ : Descent.Core.Theta} (hθ : 1 ≤ θ.value) :
    Tendsto (fun n : ℕ ↦ expectedNumClasses θ n) atTop atTop :=
  tendsto_atTop_mono (harmonicSum_le_expectedNumClasses hθ) tendsto_harmonicSum_atTop

/-- And it never exceeds the sample size: each seating opens at most one class.  The check
that the summands are probabilities and not an expression that happens to sum. -/
theorem expectedNumClasses_le {θ : Descent.Core.Theta} (hθ : 0 < θ.value) (n : ℕ) :
    expectedNumClasses θ n ≤ (n : ℝ) := by
  unfold expectedNumClasses
  have hterm : ∀ i ∈ range n, θ.value / (θ.value + (i : ℝ)) ≤ 1 := by
    intro i _
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hden : (0 : ℝ) < θ.value + (i : ℝ) := by linarith
    rw [div_le_one hden]
    linarith
  calc ∑ i ∈ range n, θ.value / (θ.value + (i : ℝ)) ≤ ∑ _i ∈ range n, (1 : ℝ) := sum_le_sum hterm
    _ = (n : ℝ) := by simp

/-- The count is monotone in the sample size: examining another individual cannot reduce the
number of alleles seen. -/
theorem expectedNumClasses_monotone {θ : Descent.Core.Theta} (hθ : 0 < θ.value) :
    Monotone fun n : ℕ ↦ expectedNumClasses θ n := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [expectedNumClasses_succ]
  have hi : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 < θ.value / (θ.value + (n : ℝ)) := div_pos hθ (by linarith)
  linarith

end Coalescent

end Descent
