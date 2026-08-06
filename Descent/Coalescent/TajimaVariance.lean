/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.PairwiseTimes
import Descent.Coalescent.SpectrumMoments
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Tajima's `Var(π)`, derived

`Descent.Coalescent.SpectrumMoments` wrote Tajima (1989)'s expression down in order to check
it, verified it at `n = 2`, and recorded the general case as open.
`Descent.Coalescent.PairwiseTimes`
then computed the two coalescence-time covariances it needs.  This file supplies the last
ingredient -- the SHARED PATH LENGTHS -- and assembles everything into

  `Var(π) = (n+1)/(3(n-1)) · θ  +  2(n²+n+3)/(9n(n-1)) · θ²`.

## The decomposition

`π` is the average of the `C = C(n,2)` pairwise difference counts.  Given the tree, `π_p` is
Poisson with mean `θ T_p`, so

  `Var(π_p) = θ E(T_p) + θ² Var(T_p) = θ + θ²`,

because a pairwise coalescence time is exponential of rate one whatever `n` is -- restriction
consistency, `Restriction.restrict_restrict`.  For two distinct pairs the conditional counts
are NOT independent: mutations falling on the part of the tree both paths traverse are counted
twice.  With `S_pq` the length of that shared part, and mutation rate `θ/2` per unit length,

  `Cov(π_p, π_q) = (θ/2) E(S_pq) + θ² Cov(T_p, T_q)`.

Two pairs meet in three ways.  They are equal; they share one lineage, and then live in a
three-sample; or they are disjoint, and then live in a four-sample.  Restriction consistency
makes those sub-samples honest coalescents, so four numbers finish the calculation:

  `Cov(T_p,T_q) = 1/3`,  `E(S_pq) = 1`      for pairs sharing a lineage;
  `Cov(T_p,T_q) = 2/9`,  `E(S_pq) = 2/3`    for disjoint pairs.

The covariances are `PairwiseTimes.covariance_pairTime` and `.covariance_disjoint_pairTime`.
The shared lengths are computed here, by the same method: enumerate the topologies, sum, and
take expectations against the clock moments `HoldingSecondMoment` proves.

## The surprise in the four-sample

Disjoint pairs look as though they should share nothing -- in the balanced tree `((01)(23))`
the pairing `(01,23)` really does share nothing.  But the OTHER two pairings of the same four
leaves, `(02,13)` and `(03,12)`, both traverse the two edges above the cherries, and share
`τ₃ + 2τ₂` of them.  Getting this wrong is easy and costs the whole `θ` coefficient; an
earlier pass of this development asserted that disjoint pairs never overlap, which would have
made `Var(π)`'s `θ` term vanish like `2/n` instead of tending to `1/3`.  The enumeration
below is what caught it.

## Main results

- `sharedPath3`, `sum_sharedPath3`: **the three-sample shared lengths are topology-free**,
  summing to `3τ₃ + 2τ₂` -- the same polynomial as the sum of the pairwise TIMES.
- `sharedPath4`, `sum_sharedPath4`: the four-sample's are not, and the average is `2/3`.
- `pairCount`, `sharingCount`, `disjointCount`, `count_split`: the pair classes, and that
  they exhaust the unordered pairs of pairs.
- `varPairwiseFromTree_eq_tajima`: **the assembly IS Tajima's formula**.
-/

namespace Coalescent

open Finset

/-! ### Shared path lengths, three-sample -/

/-- The length of the tree shared by the paths of two pairs `p ≠ q` that meet in a lineage,
in a three-sample whose first merger is the pair `c`.

If either pair is the one that merges first, the shared part is the single branch below their
common ancestor, of length `τ₃`.  If not -- the two long pairs -- the shared part is the edge
above the first cherry and the branch down to the odd leaf, `τ₃ + 2τ₂`.

Empirical status: NOT AN EMPIRICAL CLAIM.  It reads the tree off the jump chain and the
clock, as `pairTime` does. -/
def sharedPath3 (c p q : Fin 3) (t₃ t₂ : ℝ) : ℝ :=
  if c = p ∨ c = q then t₃ else t₃ + 2 * t₂

/-- **The three-sample shared lengths are topology-free too.**  Whichever pair merged first,
exactly one of the three pairs-of-pairs excludes it, so the sum is `3τ₃ + 2τ₂`. -/
theorem sum_sharedPath3 (c : Fin 3) (t₃ t₂ : ℝ) :
    sharedPath3 c 0 1 t₃ t₂ + sharedPath3 c 0 2 t₃ t₂ + sharedPath3 c 1 2 t₃ t₂
      = 3 * t₃ + 2 * t₂ := by
  fin_cases c <;> norm_num [sharedPath3, Fin.ext_iff] <;> ring

/-- And it is the SAME polynomial as the sum of the pairwise times, `sum_pairTime`.  Stated
because it is a coincidence of the three-sample and not a general fact: at four leaves the two
sums differ. -/
theorem sum_sharedPath3_eq_sum_pairTime (c c' : Fin 3) (t₃ t₂ : ℝ) :
    sharedPath3 c 0 1 t₃ t₂ + sharedPath3 c 0 2 t₃ t₂ + sharedPath3 c 1 2 t₃ t₂
      = ∑ p : Fin 3, pairTime c' p t₃ t₂ := by
  rw [sum_sharedPath3, sum_pairTime]

/-- **`E(S) = 1` for two pairs sharing a lineage.**  Three pairs-of-pairs, summing to
`3τ₃ + 2τ₂`, whose expectation is `3` at the three-sample's clock moments. -/
theorem expected_sharedPath3 {e3 e2 : ℝ} (h3 : e3 = 1 / 3) (h2 : e2 = 1) :
    (3 * e3 + 2 * e2) / 3 = 1 := by
  subst h3 h2
  norm_num

/-! ### Shared path lengths, four-sample -/

/-- The shared length of two DISJOINT pairs in a four-sample whose first merger is `01` and
whose second merger is `s`, for the pairing `d` (`0` is `(01,23)`, `1` is `(02,13)`, `2` is
`(03,12)`).

The pairing that respects the first cherry shares nothing.  The other two traverse the edge
above the first cherry; in the balanced tree they also traverse the edge above the second, so
they share `τ₃ + 2τ₂` rather than `τ₃`.

Empirical status: NOT AN EMPIRICAL CLAIM, for the reason `sharedPath3` carries. -/
def sharedPath4 (s d : Fin 3) (t₃ t₂ : ℝ) : ℝ :=
  if d = 0 then 0 else if s = 0 then t₃ + 2 * t₂ else t₃

/-- **The four-sample shared lengths are not topology-free.**  `2τ₃ + 4τ₂` under the balanced
tree, `2τ₃` under either caterpillar. -/
theorem sum_sharedPath4 (s : Fin 3) (t₃ t₂ : ℝ) :
    sharedPath4 s 0 t₃ t₂ + sharedPath4 s 1 t₃ t₂ + sharedPath4 s 2 t₃ t₂
      = if s = 0 then 2 * t₃ + 4 * t₂ else 2 * t₃ := by
  fin_cases s <;> norm_num [sharedPath4, Fin.ext_iff] <;> ring

/-- Summed over the three resolutions of the second merger. -/
theorem sum_over_second_merger_sharedPath4 (t₃ t₂ : ℝ) :
    (2 * t₃ + 4 * t₂) + 2 * (2 * t₃) = 6 * t₃ + 4 * t₂ := by
  ring

/-- **`E(S) = 2/3` for two disjoint pairs.**  Nine terms -- three pairings by three
topologies -- summing to `6τ₃ + 4τ₂`, whose expectation is `6`. -/
theorem expected_sharedPath4 {e3 e2 : ℝ} (h3 : e3 = 1 / 3) (h2 : e2 = 1) :
    (6 * e3 + 4 * e2) / 9 = 2 / 3 := by
  subst h3 h2
  norm_num

/-! ### Counting the pair classes -/

/-- `C(n,2)`, the number of pairs. -/
noncomputable def pairCount (n : ℝ) : ℝ := n * (n - 1) / 2

/-- The number of unordered pairs-of-pairs sharing exactly one lineage: choose the shared
lineage, then two others. -/
noncomputable def sharingCount (n : ℝ) : ℝ := n * (n - 1) * (n - 2) / 2

/-- The number of unordered pairs-of-pairs that are disjoint: choose four lineages, then one
of the three ways to split them. -/
noncomputable def disjointCount (n : ℝ) : ℝ := n * (n - 1) * (n - 2) * (n - 3) / 8

/-- **The two classes exhaust the pairs-of-pairs.**  `sharing + disjoint = C(C-1)/2`, which is
the check that no configuration has been missed -- two distinct pairs share one lineage or
none, and there is no third case. -/
theorem count_split (n : ℝ) :
    sharingCount n + disjointCount n = pairCount n * (pairCount n - 1) / 2 := by
  unfold sharingCount disjointCount pairCount
  ring

/-! ### The assembly -/

/-- `Var(π)` assembled from the tree: the per-pair variance `θ + θ²`, plus the covariances of
the two classes weighted by their counts, all over `C²`.

Empirical status: DERIVED.  Every constant in it is proved: `E(T) = Var(T) = 1` from the
exponential clock, `Cov = 1/3` and `E(S) = 1` for sharing pairs, `Cov = 2/9` and `E(S) = 2/3`
for disjoint ones.  What is ASSUMED, as everywhere in this group, is that the holding times
are independent -- `Descent.Coalescent.Program` item 4 -- and that mutation is Poisson at rate
`θ/2` along the branches, flagged at `SegregatingSites.expectedSegregatingSites`. -/
noncomputable def varPairwiseFromTree (θ : Descent.Core.Theta) (n : ℝ) : ℝ :=
  (pairCount n + sharingCount n + (2 / 3) * disjointCount n) / pairCount n ^ 2 * θ.value
    + (pairCount n + 2 * (sharingCount n / 3 + (2 / 9) * disjointCount n))
        / pairCount n ^ 2 * θ.value ^ 2

/-- **The assembly is Tajima's formula.**

  `Var(π) = (n+1)/(3(n-1)) θ + 2(n²+n+3)/(9n(n-1)) θ²`.

The `θ` coefficient's numerator collapses to `n(n-1)·n(n+1)/12` and the `θ²` coefficient's to
`n(n-1)(n²+n+3)/18`; dividing by `C² = n²(n-1)²/4` gives Tajima's two fractions.  The
`n² + n + 3` that looks arbitrary in the published formula is `9 + 6(n-2) + (n-2)(n-3)`: one
term for the pair itself, one for the sharing class, one for the disjoint class. -/
theorem varPairwiseFromTree_eq_tajima {n : ℕ} (hn : 2 ≤ n) (θ : Descent.Core.Theta) :
    varPairwiseFromTree θ (n : ℝ) = tajimaVarPairwise θ n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold varPairwiseFromTree tajimaVarPairwise pairCount sharingCount disjointCount
  field_simp
  ring

/-- The `n = 2` case, against the check `SpectrumMoments.varPairwise_two_eq` already made:
with one pair there are no covariances, and `Var(π) = Var(S) = θ + θ²`. -/
theorem varPairwiseFromTree_two (θ : Descent.Core.Theta) :
    varPairwiseFromTree θ (2 : ℝ) = varSegregatingSites θ 2 := by
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, varPairwiseFromTree_eq_tajima (by norm_num)]
  exact varPairwise_two_eq θ

end Coalescent

end Descent
