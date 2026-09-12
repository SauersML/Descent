/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.EstimatorSign
import Mathlib.Algebra.Order.Chebyshev

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The site frequency spectrum a graph reports at width `w`, and its bias in Tajima's `D`

`Descent.Pangenome.GraphSpectrum` reads Fu's spectrum at the graph's width, and
`Descent.Pangenome.GraphCoalescent.EstimatorSign` scores Tajima's numerator at a declared sample
size with `E(π) = θ` held fixed. Both count the graph's nodes. A study that keeps haplotype paths
counts panel haplotypes instead. This file derives that study's diversity and Tajima numerator,
and shows the sign of the bias is a property of the fiber sizes rather than of the width.

## Which spectrum the report can see

A report is an equivalence relation at or above `graphKer s` (`Observation.graphKer_le_observed`),
so a variant the graph expresses is carried by a union of fibers, that is by a set `S` of the `w`
nodes. The graph can count it in two ways.

- In nodes, `|S|` runs over `1, …, w - 1`. Under `Reduction` the graph coalescent is Kingman's on
  `w` nodes, so this is Fu's spectrum of a sample of `w`, `E(ξ_i) = θ/i`
  (`GraphSpectrum.graphSpectrum_eq`, `GraphSpectrum.graphSpectrum_total_eq`).
- In haplotypes, the frequency is `c(S) = ∑_{a ∈ S} c_a`, the number of panel paths through the
  allele, where `c_a` is the size of fiber `a`. This spectrum is the node spectrum pushed through
  subset sums of the fiber sizes. It is not Fu's spectrum at `n`. For fibers of one size `c`, the
  node class `i` lands on the haplotype count `ic`, and every count that is not a multiple of `c`
  is empty. Its total is still `θ a_{w-1}`.

The pushforward itself needs the exchangeability of the nodes that carry a variant, which the
corpus does not state, so it is not formalized. The two functionals Tajima's `D` reads need less.
`S` is the total, which the pushforward does not change
(`WidthProfile.graphExpectedSegregatingSites_eq`). `π` is a mean over pairs of haplotypes, and for
a pair the graph reports:

- `0` differences when both haplotypes sit on one node, because the graph holds them as one
  object (`graphPairDifferences_of_eq`);
- `E(S_2) = θ` differences when they sit on two nodes, because two nodes are a Kingman sample of
  two (`graphPairDifferences_of_ne`).

## Results

- `graphHaplotypeDiversity_eq`: `π` read over the panel's haplotypes is
  `θ (n² - ∑_a c_a²)/(n (n - 1))`, `θ` times the share of ordered pairs of distinct haplotypes on
  different nodes.
- `graphHaplotypeTajimaNumerator_eq`: the numerator a haplotype-counting study computes at its
  panel size is `θ ((n² - ∑_a c_a²)/(n (n - 1)) - a_{w-1}/a_{n-1})`. The Kingman spectrum at `n`
  gives zero (`SegregatingSites.expectedTajimaNumerator_eq_zero`), so this is the whole bias.
- `graphHaplotypeTajimaNumerator_eq_sub`, `graphHaplotypeTajimaNumerator_le_graphTajimaNumerator`:
  it is `EstimatorSign`'s numerator less `θ - π = θ (∑_a c_a² - n)/(n (n - 1)) ≥ 0`
  (`expectedPairwiseDifferences_sub_graphHaplotypeDiversity`).
- `graphHaplotypeTajimaNumerator_eq_kingman_of_width_eq`,
  `graphHaplotypeTajimaNumerator_eq_zero_of_width_le_one`: no bias when the interface merges
  nothing, and none when it merges everything, where both estimators vanish.
- `graphHaplotypeTajimaNumerator_le_balanced`: by Cauchy–Schwarz `w ∑_a c_a² ≥ n²`
  (`mul_self_le_width_mul_fiberSquareSum`), so the numerator is at most
  `θ (n (w - 1)/(w (n - 1)) - a_{w-1}/a_{n-1})`, with equality for fibers of one size
  (`width_mul_fiberSquareSum_of_card_eq`).
- `harmonicSum_ratio_lt_balanced`: that bound is strictly positive for `2 ≤ w < n`, and equal
  fibers attain it (`graphHaplotypeTajimaNumerator_pos_of_card_eq`).
- `tajimaSign_oneThreeInterface`: the sign is not fixed. At `n = 4` with fibers of sizes `1` and
  `3`, `EstimatorSign`'s numerator is positive and the haplotype numerator is `-θ/22`
  (`graphHaplotypeTajimaNumerator_oneThreeInterface`).

So the bias has a closed form in `n`, `w` and `∑_a c_a²`. Equal fibers push `D` up, and one large
fiber can push it down.

## Scope

Everything here is on the graph coalescent of `Reduction`, started at `graphKer s`. On the panel
coalescent started at `⊥` and read through the report, a variant has a node-level carrier set only
while its lineage is alone in its report class. A block `B` of `ξ` is a union of fibers exactly
when `B` is a class of `observed s ξ` holding one block of `ξ`, a hidden load of one
(`HiddenLoads`). That spectrum depends on the hidden loads and is not formalized, and neither is
the variance of the numerator.

## Empirical status

None. The bodies compose `Coalescent.expectedPairwiseDifferences`, Watterson's estimator at the
graph's width and the fiber sizes of the interface.
-/

namespace Descent.Pangenome.GraphCoalescent

open Finset

/-! ### What the graph reports for a pair of haplotypes -/

/-- **The expected number of differences the graph reports between haplotypes `i` and `j`.**

Empirical status: DERIVED. Haplotypes on one node are one object to the graph
(`Observation.observed`), so it reports no difference between them. Haplotypes on two nodes are
two lineages of the graph coalescent, which is Kingman's (`Reduction`), so they differ at `E(S_2)`
sites, `Coalescent.expectedPairwiseDifferences`. -/
noncomputable def graphPairDifferences {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n)
    (i j : Fin n) : ℝ :=
  if s i = s j then 0 else Coalescent.expectedPairwiseDifferences θ

/-- Two haplotypes on one node differ at no site the graph can show.

Assumes: `s i = s j`. -/
theorem graphPairDifferences_of_eq {n : ℕ} (θ : Descent.Core.Theta) {s : Fin n → Fin n}
    {i j : Fin n} (h : s i = s j) : graphPairDifferences θ s i j = 0 :=
  if_pos h

/-- Two haplotypes on distinct nodes differ at `E(S_2)` sites, as two Kingman lineages do.

Assumes: `s i ≠ s j`. -/
theorem graphPairDifferences_of_ne {n : ℕ} (θ : Descent.Core.Theta) {s : Fin n → Fin n}
    {i j : Fin n} (h : s i ≠ s j) :
    graphPairDifferences θ s i j = Coalescent.expectedPairwiseDifferences θ :=
  if_neg h

/-- The pair expectation as `θ` less `θ` on the pairs that share a node. -/
theorem graphPairDifferences_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n)
    (i j : Fin n) :
    graphPairDifferences θ s i j = θ.value - θ.value * (if s j = s i then 1 else 0) := by
  unfold graphPairDifferences
  rw [Coalescent.expectedPairwiseDifferences_eq]
  by_cases h : s i = s j
  · rw [if_pos h, if_pos h.symm]
    ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

/-! ### Diversity read over the panel's haplotypes -/

/-- **`π` as a haplotype-counting study reads it off the graph**: the mean over ordered pairs of
distinct panel haplotypes of the differences the graph reports between them. The diagonal adds
nothing, since a haplotype shares its own node.

Empirical status: DERIVED. It is Tajima's `π` over the `n` panel haplotypes, with each pair's
expectation from `graphPairDifferences`. -/
noncomputable def graphHaplotypeDiversity {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    ℝ :=
  (∑ i, ∑ j, graphPairDifferences θ s i j) / ((n : ℝ) * ((n : ℝ) - 1))

/-- **The squared fiber sizes** `∑_a c_a²` over the occupied nodes: the number of ordered pairs of
haplotypes, a haplotype with itself included, that share a node.

Empirical status: NOT AN EMPIRICAL CLAIM. A sum of squared cardinalities. -/
noncomputable def fiberSquareSum {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  ∑ a ∈ univ.image s, ((Linkage.stateFiber s a).card : ℝ) * (Linkage.stateFiber s a).card

/-- Counting the same-node pairs haplotype by haplotype gives the squared fiber sizes. -/
theorem sum_fiberCard_eq_fiberSquareSum {n : ℕ} (s : Fin n → Fin n) :
    ∑ i, (Linkage.fiberCard s i : ℝ) = fiberSquareSum s := by
  calc ∑ i, (Linkage.fiberCard s i : ℝ)
      = ∑ a ∈ univ.image s, ∑ i ∈ univ.filter (fun i ↦ s i = a),
          (Linkage.fiberCard s i : ℝ) :=
        (sum_fiberwise_of_maps_to (fun i _ ↦ mem_image_of_mem s (mem_univ i)) _).symm
    _ = fiberSquareSum s := by
        unfold fiberSquareSum
        refine sum_congr rfl fun a _ ↦ ?_
        have hconst : ∀ i ∈ univ.filter (fun i ↦ s i = a),
            (Linkage.fiberCard s i : ℝ) = ((Linkage.stateFiber s a).card : ℝ) := by
          intro i hi
          have hia : s i = a := (mem_filter.mp hi).2
          simp only [Linkage.fiberCard, Linkage.fiber, hia]
        rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
        rfl

/-- **Diversity over haplotypes**: `π = θ (n² - ∑_a c_a²)/(n (n - 1))`. -/
theorem graphHaplotypeDiversity_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    graphHaplotypeDiversity θ s
      = θ.value * ((n : ℝ) * n - fiberSquareSum s) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hrow : ∀ i : Fin n, ∑ j, graphPairDifferences θ s i j
      = (n : ℝ) * θ.value - θ.value * (Linkage.fiberCard s i : ℝ) := by
    intro i
    simp only [graphPairDifferences_eq]
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
      sum_boole]
    rfl
  unfold graphHaplotypeDiversity
  simp only [hrow]
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
    sum_fiberCard_eq_fiberSquareSum]
  ring

/-- Every occupied node holds at least one haplotype, so `∑_a c_a² ≥ ∑_a c_a = n`. -/
theorem le_fiberSquareSum {n : ℕ} (s : Fin n → Fin n) : (n : ℝ) ≤ fiberSquareSum s := by
  have hnat : ∑ a ∈ univ.image s, (Linkage.stateFiber s a).card = n := by
    simpa using Linkage.sum_card_stateFiber s
  have hsum : ∑ a ∈ univ.image s, ((Linkage.stateFiber s a).card : ℝ) = n := by
    exact_mod_cast hnat
  rw [← hsum]
  unfold fiberSquareSum
  refine sum_le_sum fun a ha ↦ ?_
  have h1 : (1 : ℝ) ≤ (Linkage.stateFiber s a).card := by
    exact_mod_cast Linkage.card_stateFiber_pos ha
  calc ((Linkage.stateFiber s a).card : ℝ)
      = ((Linkage.stateFiber s a).card : ℝ) * 1 := (mul_one _).symm
    _ ≤ ((Linkage.stateFiber s a).card : ℝ) * (Linkage.stateFiber s a).card :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **What the same-node pairs take out of `π`**: `θ - π = θ (∑_a c_a² - n)/(n (n - 1))`.

Assumes: `2 ≤ n`. -/
theorem expectedPairwiseDifferences_sub_graphHaplotypeDiversity {n : ℕ} (hn : 2 ≤ n)
    (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    Coalescent.expectedPairwiseDifferences θ - graphHaplotypeDiversity θ s
      = θ.value * (fiberSquareSum s - n) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  rw [graphHaplotypeDiversity_eq, Coalescent.expectedPairwiseDifferences_eq, sub_eq_iff_eq_add,
    div_add_div_same, eq_div_iff hd]
  ring

/-- A faithful interface puts every haplotype on its own node, so `∑_a c_a² = n`.

Assumes: `s` injective. -/
theorem fiberSquareSum_of_injective {n : ℕ} {s : Fin n → Fin n} (hs : Function.Injective s) :
    fiberSquareSum s = n := by
  rw [← sum_fiberCard_eq_fiberSquareSum]
  have h1 : ∀ i, Linkage.fiberCard s i = 1 := by
    intro i
    unfold Linkage.fiberCard Linkage.fiber Linkage.stateFiber
    rw [card_eq_one]
    exact ⟨i, by ext j; simp [hs.eq_iff]⟩
  simp [h1]

/-- **A graph that merges nothing reports Kingman's `π`.**

Assumes: `2 ≤ n` and `Linkage.width s = n`. -/
theorem graphHaplotypeDiversity_eq_of_width_eq {n : ℕ} (hn : 2 ≤ n) (θ : Descent.Core.Theta)
    {s : Fin n → Fin n} (h : Linkage.width s = n) :
    graphHaplotypeDiversity θ s = Coalescent.expectedPairwiseDifferences θ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  rw [graphHaplotypeDiversity_eq, fiberSquareSum_of_injective (injective_of_width_eq h),
    Coalescent.expectedPairwiseDifferences_eq, div_eq_iff hd]
  ring

/-- **A graph that merges everything reports no diversity**: every pair shares the one node.

Assumes: `Linkage.width s ≤ 1`. -/
theorem graphHaplotypeDiversity_eq_zero_of_width_le_one {n : ℕ} (θ : Descent.Core.Theta)
    {s : Fin n → Fin n} (h : Linkage.width s ≤ 1) : graphHaplotypeDiversity θ s = 0 := by
  have h' : (univ.image s).card ≤ 1 := h
  have hall : ∀ i j : Fin n, s i = s j := fun i j ↦
    card_le_one.mp h' (s i) (mem_image_of_mem s (mem_univ i)) (s j)
      (mem_image_of_mem s (mem_univ j))
  have hzero : ∑ i, ∑ j, graphPairDifferences θ s i j = 0 :=
    sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ graphPairDifferences_of_eq θ (hall i j)
  unfold graphHaplotypeDiversity
  rw [hzero, zero_div]

/-- **Cauchy–Schwarz on the fiber sizes**: `n² ≤ w ∑_a c_a²`. -/
theorem mul_self_le_width_mul_fiberSquareSum {n : ℕ} (s : Fin n → Fin n) :
    (n : ℝ) * n ≤ (Linkage.width s : ℝ) * fiberSquareSum s := by
  have hnat : ∑ a ∈ univ.image s, (Linkage.stateFiber s a).card = n := by
    simpa using Linkage.sum_card_stateFiber s
  have hsum : ∑ a ∈ univ.image s, ((Linkage.stateFiber s a).card : ℝ) = n := by
    exact_mod_cast hnat
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.image s)
    (f := fun a ↦ ((Linkage.stateFiber s a).card : ℝ))
  simp only [sq] at hcs
  rw [hsum] at hcs
  exact hcs

/-- **Diversity is at most its balanced value**, `θ n (w - 1)/(w (n - 1))`.

Assumes: `2 ≤ n` and `0 ≤ θ.value`. -/
theorem graphHaplotypeDiversity_le_balanced {n : ℕ} (hn : 2 ≤ n) {θ : Descent.Core.Theta}
    (hθ : 0 ≤ θ.value) (s : Fin n → Fin n) :
    graphHaplotypeDiversity θ s
      ≤ θ.value * ((n : ℝ) * ((Linkage.width s : ℝ) - 1))
          / ((Linkage.width s : ℝ) * ((n : ℝ) - 1)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hw : (0 : ℝ) < Linkage.width s := by exact_mod_cast Linkage.width_pos s
  have hcs := mul_self_le_width_mul_fiberSquareSum s
  have hd1 : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hd2 : 0 < (Linkage.width s : ℝ) * ((n : ℝ) - 1) := mul_pos hw (by linarith)
  have key : 0 ≤ θ.value * ((n : ℝ) - 1)
      * ((Linkage.width s : ℝ) * fiberSquareSum s - (n : ℝ) * n) :=
    mul_nonneg (mul_nonneg hθ (by linarith)) (by linarith)
  rw [graphHaplotypeDiversity_eq, div_le_div_iff₀ hd1 hd2]
  nlinarith [key]

/-- If every occupied node holds `c` haplotypes then `w ∑_a c_a² = n²`, the equality case of
`mul_self_le_width_mul_fiberSquareSum`.

Assumes: every fiber has size `c`. -/
theorem width_mul_fiberSquareSum_of_card_eq {n c : ℕ} {s : Fin n → Fin n}
    (hc : ∀ a ∈ univ.image s, (Linkage.stateFiber s a).card = c) :
    (Linkage.width s : ℝ) * fiberSquareSum s = (n : ℝ) * n := by
  have hnat : ∑ a ∈ univ.image s, (Linkage.stateFiber s a).card = n := by
    simpa using Linkage.sum_card_stateFiber s
  rw [sum_congr rfl hc, sum_const, smul_eq_mul] at hnat
  have hn : (n : ℝ) = (Linkage.width s : ℝ) * c := by
    exact_mod_cast hnat.symm
  have hc' : ∀ a ∈ univ.image s,
      ((Linkage.stateFiber s a).card : ℝ) * (Linkage.stateFiber s a).card = (c : ℝ) * c := by
    intro a ha
    rw [hc a ha]
  have hsq : fiberSquareSum s = (Linkage.width s : ℝ) * ((c : ℝ) * c) := by
    unfold fiberSquareSum
    rw [sum_congr rfl hc', sum_const, nsmul_eq_mul]
    rfl
  rw [hsq, hn]
  ring

/-! ### Tajima's numerator over haplotypes -/

/-- **Tajima's numerator as a haplotype-counting study computes it from a graph**: diversity over
the panel's haplotypes less Watterson's estimator of the graph's segregating sites at the panel
size `n`.

Empirical status: DERIVED. The diversity is `graphHaplotypeDiversity`; the sites are
`WidthProfile.graphExpectedSegregatingSites`; the divisor's sample size is the panel's, which is
what a study counting haplotype paths uses. -/
noncomputable def graphHaplotypeTajimaNumerator {n : ℕ} (θ : Descent.Core.Theta)
    (s : Fin n → Fin n) : ℝ :=
  graphHaplotypeDiversity θ s
    - Coalescent.wattersonEstimator (graphExpectedSegregatingSites θ s) n

/-- **The bias, exactly**: `θ ((n² - ∑_a c_a²)/(n (n - 1)) - a_{w-1}/a_{n-1})`. -/
theorem graphHaplotypeTajimaNumerator_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    graphHaplotypeTajimaNumerator θ s
      = θ.value * ((n : ℝ) * n - fiberSquareSum s) / ((n : ℝ) * ((n : ℝ) - 1))
        - θ.value * Coalescent.harmonicSum (Linkage.width s - 1)
          / Coalescent.harmonicSum (n - 1) := by
  unfold graphHaplotypeTajimaNumerator Coalescent.wattersonEstimator
  rw [graphHaplotypeDiversity_eq, graphExpectedSegregatingSites_eq]

/-- **The haplotype numerator is `EstimatorSign`'s less the diversity the same-node pairs
remove.** `graphTajimaNumerator` holds `π` at `θ`; counting haplotypes subtracts `θ - π`. -/
theorem graphHaplotypeTajimaNumerator_eq_sub {n : ℕ} (θ : Descent.Core.Theta)
    (s : Fin n → Fin n) :
    graphHaplotypeTajimaNumerator θ s
      = graphTajimaNumerator θ s n
        - (Coalescent.expectedPairwiseDifferences θ - graphHaplotypeDiversity θ s) := by
  unfold graphHaplotypeTajimaNumerator graphTajimaNumerator
  ring

/-- **Counting haplotypes never raises the numerator** above `EstimatorSign`'s at the panel size.

Assumes: `2 ≤ n` and `0 ≤ θ.value`. -/
theorem graphHaplotypeTajimaNumerator_le_graphTajimaNumerator {n : ℕ} (hn : 2 ≤ n)
    {θ : Descent.Core.Theta} (hθ : 0 ≤ θ.value) (s : Fin n → Fin n) :
    graphHaplotypeTajimaNumerator θ s ≤ graphTajimaNumerator θ s n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hgap : 0 ≤ Coalescent.expectedPairwiseDifferences θ - graphHaplotypeDiversity θ s := by
    rw [expectedPairwiseDifferences_sub_graphHaplotypeDiversity hn θ s]
    exact div_nonneg (mul_nonneg hθ (by linarith [le_fiberSquareSum s])) hd.le
  rw [graphHaplotypeTajimaNumerator_eq_sub]
  linarith

/-- **No bias when nothing is merged.** At full width the haplotype numerator is Kingman's, which
is zero.

Assumes: `2 ≤ n` and `Linkage.width s = n`. -/
theorem graphHaplotypeTajimaNumerator_eq_zero_of_width_eq {n : ℕ} (hn : 2 ≤ n)
    (θ : Descent.Core.Theta) {s : Fin n → Fin n} (h : Linkage.width s = n) :
    graphHaplotypeTajimaNumerator θ s = 0 := by
  have hpos := Coalescent.harmonicSum_pos_of_two_le hn
  unfold graphHaplotypeTajimaNumerator Coalescent.wattersonEstimator
  rw [graphHaplotypeDiversity_eq_of_width_eq hn θ h, Coalescent.expectedPairwiseDifferences_eq,
    graphExpectedSegregatingSites_eq, h, mul_div_assoc, div_self hpos.ne', mul_one, sub_self]

/-- The full-width case is the Kingman spectrum's numerator at `n`.

Assumes: `2 ≤ n` and `Linkage.width s = n`. -/
theorem graphHaplotypeTajimaNumerator_eq_kingman_of_width_eq {n : ℕ} (hn : 2 ≤ n)
    (θ : Descent.Core.Theta) {s : Fin n → Fin n} (h : Linkage.width s = n) :
    graphHaplotypeTajimaNumerator θ s = Coalescent.expectedTajimaNumerator θ n := by
  rw [graphHaplotypeTajimaNumerator_eq_zero_of_width_eq hn θ h,
    Coalescent.expectedTajimaNumerator_eq_zero hn θ]

/-- **No bias when everything is merged**: both estimators vanish.

Assumes: `Linkage.width s ≤ 1`. -/
theorem graphHaplotypeTajimaNumerator_eq_zero_of_width_le_one {n : ℕ} (θ : Descent.Core.Theta)
    {s : Fin n → Fin n} (h : Linkage.width s ≤ 1) : graphHaplotypeTajimaNumerator θ s = 0 := by
  unfold graphHaplotypeTajimaNumerator Coalescent.wattersonEstimator
  rw [graphHaplotypeDiversity_eq_zero_of_width_le_one θ h, graphExpectedSegregatingSites_eq,
    show Linkage.width s - 1 = 0 by omega, Coalescent.harmonicSum_zero, mul_zero, zero_div,
    sub_zero]

/-- **The bias is at most its balanced value**, `θ (n (w - 1)/(w (n - 1)) - a_{w-1}/a_{n-1})`.

Assumes: `2 ≤ n` and `0 ≤ θ.value`. -/
theorem graphHaplotypeTajimaNumerator_le_balanced {n : ℕ} (hn : 2 ≤ n)
    {θ : Descent.Core.Theta} (hθ : 0 ≤ θ.value) (s : Fin n → Fin n) :
    graphHaplotypeTajimaNumerator θ s
      ≤ θ.value * ((n : ℝ) * ((Linkage.width s : ℝ) - 1)
          / ((Linkage.width s : ℝ) * ((n : ℝ) - 1))
        - Coalescent.harmonicSum (Linkage.width s - 1) / Coalescent.harmonicSum (n - 1)) := by
  have hπ : graphHaplotypeDiversity θ s
      ≤ θ.value * ((n : ℝ) * ((Linkage.width s : ℝ) - 1)
          / ((Linkage.width s : ℝ) * ((n : ℝ) - 1))) := by
    rw [← mul_div_assoc]
    exact graphHaplotypeDiversity_le_balanced hn hθ s
  have hW : Coalescent.wattersonEstimator (graphExpectedSegregatingSites θ s) n
      = θ.value * (Coalescent.harmonicSum (Linkage.width s - 1)
          / Coalescent.harmonicSum (n - 1)) := by
    unfold Coalescent.wattersonEstimator
    rw [graphExpectedSegregatingSites_eq, mul_div_assoc]
  unfold graphHaplotypeTajimaNumerator
  rw [hW, mul_sub]
  linarith

/-! ### The balanced value is positive -/

/-- `a_m ≤ m`: each of the `m` reciprocals is at most one. -/
theorem harmonicSum_le_self (m : ℕ) : Coalescent.harmonicSum m ≤ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Coalescent.harmonicSum_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    push_cast
    linarith

/-- The comparison behind `harmonicSum_ratio_lt_balanced` at `w = k + 2` and `n = k + 3 + d`,
cross-multiplied: `w (n - 1) a_{w-1} < (w - 1) n a_{n-1}`. -/
theorem harmonic_cross_lt (k d : ℕ) :
    ((k : ℝ) + 2) * ((k : ℝ) + 2 + d) * Coalescent.harmonicSum (k + 1)
      < ((k : ℝ) + 1) * ((k : ℝ) + 3 + d) * Coalescent.harmonicSum (k + 2 + d) := by
  have hA : Coalescent.harmonicSum (k + 1) ≤ (k : ℝ) + 1 := by
    have h := harmonicSum_le_self (k + 1)
    push_cast at h
    exact h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  induction d with
  | zero =>
    have e : (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = 1 / ((k : ℝ) + 2) := by
      push_cast
      ring
    rw [show k + 2 + 0 = k + 1 + 1 from rfl, Coalescent.harmonicSum_succ (k + 1), e]
    have ht1 : 1 / ((k : ℝ) + 2) * ((k : ℝ) + 2) = 1 := div_mul_cancel₀ 1 (by positivity)
    have hlt : 1 / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have h' : 1 / ((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 2) = (k : ℝ) + 2 := by
      rw [ht1, one_mul]
    push_cast
    linarith [hA, h', hlt]
  | succ d ih =>
    have e : (1 : ℝ) / (((k + 2 + d : ℕ) : ℝ) + 1) = 1 / ((k : ℝ) + 3 + d) := by
      push_cast
      ring
    rw [show k + 2 + (d + 1) = k + 2 + d + 1 from rfl, Coalescent.harmonicSum_succ (k + 2 + d), e]
    have ht0 : 0 < 1 / ((k : ℝ) + 3 + d) := by positivity
    have ht1 : 1 / ((k : ℝ) + 3 + d) * ((k : ℝ) + 3 + d) = 1 := div_mul_cancel₀ 1 (by positivity)
    have hmono : Coalescent.harmonicSum (k + 1) ≤ Coalescent.harmonicSum (k + 2 + d) :=
      Coalescent.harmonicSum_strictMono.monotone (by omega)
    have h3 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) ht0.le
    have h5 : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 3 + d) * ((k : ℝ) + 3 + d)) = (k : ℝ) + 1 := by
      rw [ht1, mul_one]
    push_cast
    linarith [ih, h3, h4, h5, hA]

/-- **The balanced value is positive.** For `2 ≤ w < n`, `a_{w-1}/a_{n-1} < n (w - 1)/(w (n - 1))`.
Equivalently `(w - 1)/(w a_{w-1})` decreases strictly in `w`.

Assumes: `2 ≤ w` and `w < n`. -/
theorem harmonicSum_ratio_lt_balanced {w n : ℕ} (hw : 2 ≤ w) (hwn : w < n) :
    Coalescent.harmonicSum (w - 1) / Coalescent.harmonicSum (n - 1)
      < (n : ℝ) * ((w : ℝ) - 1) / ((w : ℝ) * ((n : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = k + 3 + d := ⟨n - (k + 3), by omega⟩
  have hc := harmonic_cross_lt k d
  have hB : 0 < Coalescent.harmonicSum (k + 3 + d - 1) :=
    Coalescent.harmonicSum_pos_of_two_le (by omega)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hD : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) * (((k + 3 + d : ℕ) : ℝ) - 1) := by
    push_cast
    exact mul_pos (by positivity) (by linarith)
  rw [div_lt_div_iff₀ hB hD, show k + 2 - 1 = k + 1 by omega,
    show k + 3 + d - 1 = k + 2 + d by omega]
  push_cast
  linarith [hc]

/-- **Equal fibers push `D` up.** If every node holds the same number of haplotypes and
`2 ≤ w < n`, the haplotype numerator is strictly positive.

Assumes: `0 < θ.value`, `2 ≤ Linkage.width s`, `Linkage.width s < n`, and every fiber of size
`c`. -/
theorem graphHaplotypeTajimaNumerator_pos_of_card_eq {n c : ℕ} {θ : Descent.Core.Theta}
    (hθ : 0 < θ.value) {s : Fin n → Fin n} (h2 : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) (hc : ∀ a ∈ univ.image s, (Linkage.stateFiber s a).card = c) :
    0 < graphHaplotypeTajimaNumerator θ s := by
  have hbal := width_mul_fiberSquareSum_of_card_eq hc
  have hgap := harmonicSum_ratio_lt_balanced h2 hlt
  have hw : (0 : ℝ) < Linkage.width s := by exact_mod_cast (by omega : 0 < Linkage.width s)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hd1 : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  have hd2 : (Linkage.width s : ℝ) * ((n : ℝ) - 1) ≠ 0 := (mul_pos hw (by linarith)).ne'
  have hπ : graphHaplotypeDiversity θ s
      = θ.value * ((n : ℝ) * ((Linkage.width s : ℝ) - 1)
          / ((Linkage.width s : ℝ) * ((n : ℝ) - 1))) := by
    rw [graphHaplotypeDiversity_eq, ← mul_div_assoc, div_eq_div_iff hd1 hd2]
    linear_combination (-(θ.value * ((n : ℝ) - 1))) * hbal
  have hW : Coalescent.wattersonEstimator (graphExpectedSegregatingSites θ s) n
      = θ.value * (Coalescent.harmonicSum (Linkage.width s - 1)
          / Coalescent.harmonicSum (n - 1)) := by
    unfold Coalescent.wattersonEstimator
    rw [graphExpectedSegregatingSites_eq, mul_div_assoc]
  unfold graphHaplotypeTajimaNumerator
  rw [hπ, hW, ← mul_sub]
  exact mul_pos hθ (by linarith)

/-! ### The sign is not fixed -/

/-- **Four haplotypes on fibers of sizes one and three**: haplotype `0` alone on node `0`, and
haplotypes `1, 2, 3` merged on node `1`.

Empirical status: NOT AN EMPIRICAL CLAIM. A four-haplotype interface chosen to show that the sign
of the haplotype numerator is not fixed. -/
def oneThreeInterface : Fin 4 → Fin 4 := ![0, 1, 1, 1]

theorem width_oneThreeInterface : Linkage.width oneThreeInterface = 2 := by decide +kernel

theorem fiberSquareSum_oneThreeInterface : fiberSquareSum oneThreeInterface = 10 := by
  have h : ∑ a ∈ univ.image oneThreeInterface,
      (Linkage.stateFiber oneThreeInterface a).card * (Linkage.stateFiber oneThreeInterface a).card
        = 10 := by decide +kernel
  unfold fiberSquareSum
  exact_mod_cast h

/-- At `n = 4` with fibers of sizes one and three the haplotype numerator is `-θ/22`. -/
theorem graphHaplotypeTajimaNumerator_oneThreeInterface (θ : Descent.Core.Theta) :
    graphHaplotypeTajimaNumerator θ oneThreeInterface = -(θ.value / 22) := by
  have h3 : Coalescent.harmonicSum 3 = 11 / 6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Coalescent.harmonicSum_succ, Coalescent.harmonicSum_two]
    norm_num
  rw [graphHaplotypeTajimaNumerator_eq, fiberSquareSum_oneThreeInterface, width_oneThreeInterface,
    show (2 : ℕ) - 1 = 1 from rfl, show (4 : ℕ) - 1 = 3 from rfl, h3, Coalescent.harmonicSum_one]
  push_cast
  ring

/-- **One interface, opposite signs.** At `n = 4` with fibers of sizes one and three,
`EstimatorSign`'s numerator is positive and the haplotype numerator is negative.

Assumes: `0 < θ.value`. -/
theorem tajimaSign_oneThreeInterface {θ : Descent.Core.Theta} (hθ : 0 < θ.value) :
    0 < graphTajimaNumerator θ oneThreeInterface 4
      ∧ graphHaplotypeTajimaNumerator θ oneThreeInterface < 0 := by
  refine ⟨graphTajimaNumerator_pos_of_width_lt hθ (le_of_eq width_oneThreeInterface.symm)
    (by rw [width_oneThreeInterface]; norm_num), ?_⟩
  rw [graphHaplotypeTajimaNumerator_oneThreeInterface]
  linarith

end Descent.Pangenome.GraphCoalescent
