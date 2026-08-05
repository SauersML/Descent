/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace Descent

/-!
# The total length of the coalescent tree, and why it is unbounded while its height is not

`Descent.Coalescent.Rates` gives the height of the tree: `E(T_n) = 2 - 2/n` (K-G (5.7)),
bounded by `2` however large the sample.  That bound is the reason the coalescent has an
entrance boundary, and the corpus has used it repeatedly.  It is also, read carelessly, an
argument that large samples buy nothing -- and that reading is wrong, because the quantity a
sequencing study spends its money on is not the height of the tree but its TOTAL LENGTH.

The two behave completely differently, and this file is the difference.  While the block
count sits at `k`, the tree accrues length at rate `k` -- one unit per lineage per unit time
-- so the expected length contributed by the `k`-lineage phase is `k · d_k⁻¹`, and the
telescoping that made the height converge does not happen here:

  `k / d_k = k · 2/(k(k-1)) = 2/(k-1)`,

so `E(L_n) = 2 Σ_{i=1}^{n-1} i⁻¹`, the harmonic series, which diverges.  A sample of `n`
has a tree of expected height under `2` and expected length about `2 log n`.

This is a *mechanism to formula* step of the kind the corpus is built to make explicit.
Nothing here posits a length formula: the ladder `d_k` is a cardinality of the state space
(`StateSpace.card_covers_eq_deathRate`), the holding time in a `k`-block state has mean
`d_k⁻¹` (K-G (5.6), `Rates.meanTransitTime`'s summand), and the coefficient `k` is the
number of lineages alive, which is what `|R_t|` counts.  `E(L_n)` is those three facts
multiplied and summed, and everything downstream -- Watterson's estimator in
`Descent.Coalescent.SegregatingSites` -- is a consequence of this sum rather than a
separate stipulation.

The harmonic number is the `a_n` of the population-genetics literature (Watterson 1975);
it is written here as a real-valued `Finset` sum rather than imported as Mathlib's
rational-valued `harmonic`, because every consumer in this corpus is real-valued and a cast
at each use site would be four casts to save one definition.

## Main results

- `harmonicSum`: `a_m = Σ_{i=1}^{m} i⁻¹`.
- `expectedSegmentLength_eq`: the `k`-lineage phase contributes `2/(k-1)`, K-G (5.6) times
  the lineage count.
- `expectedTotalBranchLength_eq_harmonic`: **`E(L_n) = 2 a_{n-1}`**, the total-length law.
- `expectedTotalBranchLength_two`: `E(L_2) = 2`, which is `2 E(T_2)` -- two lineages, so
  length is twice height, and the two developments agree where they overlap.
- `expectedTotalBranchLength_strictMono`: every extra sampled individual adds length.
- `tendsto_expectedTotalBranchLength_atTop`: **it diverges**, while
  `Rates.meanTransitTime_lt_two` caps the height at `2`.  The contrast is
  `height_bounded_length_unbounded`.
-/

namespace Coalescent

open Finset Filter Topology

/-! ### The harmonic number -/

/-- `a_m = Σ_{i=1}^{m} i⁻¹`, Watterson's constant, as a real-valued sum.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a finite sum of reciprocals. -/
noncomputable def harmonicSum (m : ℕ) : ℝ := ∑ i ∈ range m, 1 / ((i : ℝ) + 1)

@[simp] theorem harmonicSum_zero : harmonicSum 0 = 0 := by simp [harmonicSum]

@[simp] theorem harmonicSum_one : harmonicSum 1 = 1 := by norm_num [harmonicSum]

theorem harmonicSum_succ (m : ℕ) :
    harmonicSum (m + 1) = harmonicSum m + 1 / ((m : ℝ) + 1) := by
  unfold harmonicSum
  rw [sum_range_succ]

theorem harmonicSum_nonneg (m : ℕ) : 0 ≤ harmonicSum m := by
  unfold harmonicSum
  refine sum_nonneg fun i _ ↦ ?_
  positivity

theorem harmonicSum_strictMono : StrictMono harmonicSum := by
  refine strictMono_nat_of_lt_succ fun m ↦ ?_
  rw [harmonicSum_succ]
  have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-- **The harmonic series diverges.**  This is the one fact about `a_m` that the whole point
of the file rests on, and it is Mathlib's, not the corpus's. -/
theorem tendsto_harmonicSum_atTop : Tendsto harmonicSum atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine h.congr fun n ↦ ?_
  simp [harmonicSum]

/-! ### Length accrues at the lineage count

The tree of a sample of `n` is a set of lineages that merge; at a moment when `k` of them
are alive, the tree gains `k` units of branch length per unit of time.  The expected time
spent with `k` alive is `d_k⁻¹` (K-G (5.6)), so the phase contributes `k/d_k`. -/

/-- The expected branch length contributed by the phase with `k` lineages alive: the lineage
count times the mean holding time.

Empirical status: DERIVED, not posited.  The factor `k` is the number of lineages, i.e. the
block count `|R_t|` of `Descent.Coalescent.StateSpace.blocks`; the factor `d_k⁻¹` is the mean
of K-C (1.7)'s exponential holding time, computed in
`Descent.Coalescent.HoldingTime`.  Neither is introduced here. -/
noncomputable def expectedSegmentLength (k : ℕ) : ℝ := (k : ℝ) / deathRate k

/-- **The telescope that does not telescope.**  `k/d_k = 2/(k-1)`.  The height sum
`Σ d_k⁻¹ = Σ 2(1/(k-1) - 1/k)` collapses because its summand is a difference; multiplying by
`k` destroys exactly that structure and leaves a harmonic term. -/
theorem expectedSegmentLength_eq (j : ℕ) :
    expectedSegmentLength (j + 2) = 2 / ((j : ℝ) + 1) := by
  have hd : deathRate (j + 2) = ((j : ℝ) + 2) * ((j : ℝ) + 1) / 2 := by
    unfold deathRate
    push_cast
    ring
  unfold expectedSegmentLength
  rw [hd]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Two lineages accrue length at rate two, and wait a mean time one: `E = 2`. -/
theorem expectedSegmentLength_two : expectedSegmentLength 2 = 2 := by
  simpa using expectedSegmentLength_eq 0

/-! ### The total -/

/-- `E(L_n)`, the expected total branch length of the `n`-coalescent tree: summed over the
`n - 1` phases the block count passes through, exactly as `Rates.meanTransitTime` sums the
same phases without the lineage-count weight.

Empirical status: DERIVED, not posited -- it is `Σ_k k · d_k⁻¹` with both factors supplied
elsewhere; see `expectedSegmentLength`.  In generations, multiply by `2 N_e`, the factor
`Descent.Foundations.Conventions.coalescentTimeScale` fixes. -/
noncomputable def expectedTotalBranchLength (n : ℕ) : ℝ :=
  ∑ j ∈ range (n - 1), expectedSegmentLength (j + 2)

/-- **`E(L_n) = 2 a_{n-1}`.**  The total-length law of the coalescent, which is what makes
Watterson's estimator an estimator: the expected number of mutations on the tree is
proportional to this, so the harmonic number is the normalising constant a sample of `n`
must be divided by. -/
theorem expectedTotalBranchLength_eq_harmonic (n : ℕ) :
    expectedTotalBranchLength n = 2 * harmonicSum (n - 1) := by
  unfold expectedTotalBranchLength harmonicSum
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [expectedSegmentLength_eq]
  ring

@[simp] theorem expectedTotalBranchLength_one : expectedTotalBranchLength 1 = 0 := by
  simp [expectedTotalBranchLength]

/-- **`E(L_2) = 2`**, and `E(T_2) = 1`: with two lineages the tree is two branches of the
same length, so its length is twice its height.  The two sums agree where the weight is
constant, which is the check that the weight is the lineage count and not something else. -/
theorem expectedTotalBranchLength_two : expectedTotalBranchLength 2 = 2 := by
  rw [expectedTotalBranchLength_eq_harmonic]
  norm_num

/-- The `n = 2` case of the general law, stated against `Rates.meanTransitTime` so that the
agreement is a theorem rather than two numbers a reader must compare. -/
theorem expectedTotalBranchLength_two_eq_two_mul_height :
    expectedTotalBranchLength 2 = 2 * meanTransitTime 2 := by
  rw [expectedTotalBranchLength_two, meanTransitTime_two]
  ring

theorem expectedTotalBranchLength_nonneg (n : ℕ) : 0 ≤ expectedTotalBranchLength n := by
  rw [expectedTotalBranchLength_eq_harmonic]
  have := harmonicSum_nonneg (n - 1)
  linarith

/-- **Every extra individual lengthens the tree.**  Strictly: adding the `(n+1)`-st sample
member adds `2/n` in expectation.  Contrast `Rates.meanTransitTime`, whose increments are
`2/n - 2/(n+1)` and sum to a finite total. -/
theorem expectedTotalBranchLength_succ_sub (n : ℕ) :
    expectedTotalBranchLength (n + 2) - expectedTotalBranchLength (n + 1)
      = 2 / ((n : ℝ) + 1) := by
  have h2 : n + 2 - 1 = n + 1 := rfl
  have h1 : n + 1 - 1 = n := rfl
  rw [expectedTotalBranchLength_eq_harmonic, expectedTotalBranchLength_eq_harmonic, h2, h1,
    harmonicSum_succ]
  ring

theorem expectedTotalBranchLength_strictMono :
    StrictMono fun n : ℕ ↦ expectedTotalBranchLength (n + 1) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h := expectedTotalBranchLength_succ_sub n
  have hpos : (0 : ℝ) < 2 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **The total length diverges.**  A sample of `n` has a tree whose expected length grows
like `2 log n` without bound. -/
theorem tendsto_expectedTotalBranchLength_atTop :
    Tendsto (fun n : ℕ ↦ expectedTotalBranchLength (n + 1)) atTop atTop := by
  have hcomp : (fun n : ℕ ↦ expectedTotalBranchLength (n + 1))
      = fun n : ℕ ↦ 2 * harmonicSum n := by
    funext n
    rw [expectedTotalBranchLength_eq_harmonic, show n + 1 - 1 = n from rfl]
  rw [hcomp]
  refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_harmonicSum_atTop
  have := harmonicSum_nonneg n
  linarith

/-- **The contrast, stated once.**  However large the sample, its tree is under `2` tall;
and for every bound, a large enough sample has a tree longer than it.  The same ladder `d_k`
produces both, and the only difference is the weight `k` that counts how many lineages are
accruing length at once.

This is the formal content of the practical fact that increasing sample size keeps
discovering rare variants long after it has stopped pushing the common ancestor further
back: rare variants live on the short terminal branches, whose number grows with `n`, and
the common ancestor lives at the root, whose depth does not. -/
theorem height_bounded_length_unbounded (B : ℝ) :
    (∀ n : ℕ, meanTransitTime n < 2) ∧ ∃ n : ℕ, B < expectedTotalBranchLength n := by
  refine ⟨meanTransitTime_lt_two, ?_⟩
  obtain ⟨n, hn⟩ := (tendsto_expectedTotalBranchLength_atTop.eventually_gt_atTop B).exists
  exact ⟨n + 1, hn⟩

end Coalescent

end Descent
