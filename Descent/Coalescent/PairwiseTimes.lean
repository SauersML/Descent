/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Descent.Coalescent.HoldingTime

namespace Descent

/-!
# Pairwise coalescence times in a three-sample, and why their symmetric sums forget the tree

`Descent.Coalescent.SpectrumMoments` closes the `S`-side second moments and records what
`Var(π)` still needs: `E(T_ij T_kl)` for two pairs sharing a lineage.  By restriction
consistency (K-G (7.2), `Restriction.restrict_restrict`) any two such pairs live in a
three-sample, so that is the object to compute in.

A three-sample's genealogy is two holding times and a choice.  It spends `τ₃` with three
lineages, then `τ₂` with two; one of the three pairs merges first, and the jump chain picks
which uniformly (`JumpChain.jumpProb`, `C(3,2) = 3` covers).  Writing `c` for the pair that
merges first, the pairwise coalescence times are

  `T_c = τ₃`,   `T_p = τ₃ + τ₂` for the other two.

The observation this file is built on is that the SYMMETRIC functions of those three numbers
do not depend on `c`:

  `Σ_p T_p = 3τ₃ + 2τ₂`,   `Σ_p T_p² = τ₃² + 2(τ₃+τ₂)²`,

and therefore the cross-sum `Σ_{p≠q} T_p T_q`, being the difference of the square of the
first and the second, does not either.  So the quantities `Var(π)` is built from need no
average over topologies at all: the choice the jump chain makes is invisible to them.

That is what makes the computation finite.  With the holding-time moments -- `E τ₃ = 1/3`,
`E τ₃² = 2/9`, `E τ₂ = 1`, `E τ₂² = 2`, all integrals against K-C (1.7)'s density that
`Descent.Coalescent.HoldingSecondMoment` proves -- the cross-sum has expectation `4`, so the
average over the three unordered pairs-of-pairs is

  `E(T_ij T_ik) = 4/3`,   hence   `Cov(T_ij, T_ik) = 1/3`.

## What this closes and what it does not

CLOSED: the three-sample half of `Var(π)`'s missing input, and the structural reason it is
computable -- topology-independence of the symmetric sums.

NOT CLOSED: the four-sample case, `E(T_ij T_kl)` for DISJOINT pairs, and the combinatorial
sum over pair classes that assembles them into Tajima's expression.  Also not closed: the
covariance of the mutation counts, which adds `θ · E(shared path length)` to
`θ² Cov(T,T')` because overlapping paths share mutations.  `Descent.Coalescent.Program`
records both.

The moment hypotheses are written as hypotheses rather than derived inline because the
expectation functional itself -- an integral against the product of two hold measures -- is
not built in this corpus; `HoldingSecondMoment` proves the one-dimensional integrals and the
independence that turns `E(τ₃τ₂)` into `E τ₃ · E τ₂` is the corpus's standing assumption,
tracked as `Program` item 4.

## Main results

- `pairTime`: the three pairwise times of a three-sample.
- `sum_pairTime`, `sum_sq_pairTime`: **their symmetric sums forget which pair merged first**.
- `cross_pairTime`: hence so does the cross-sum, `3τ₃² + 4τ₃τ₂ + τ₂²`.
- `expected_cross_pairTime`: with the coalescent's moments it is `4`.
- `covariance_pairTime`: **`Cov(T_ij, T_ik) = 1/3`**.
-/

namespace Coalescent

open Finset

/-- The coalescence time of pair `p` in a three-sample whose first merger is pair `c`, given
the two holding times.

Empirical status: NOT AN EMPIRICAL CLAIM.  It reads the tree off the jump chain and the
clock: the pair that merges first waits `τ₃`, the other two wait until the root. -/
def pairTime (c p : Fin 3) (t₃ t₂ : ℝ) : ℝ := if p = c then t₃ else t₃ + t₂

/-- **The total of the three pairwise times forgets the topology.**  Whichever pair merged
first, the three times sum to `3τ₃ + 2τ₂`. -/
theorem sum_pairTime (c : Fin 3) (t₃ t₂ : ℝ) :
    ∑ p : Fin 3, pairTime c p t₃ t₂ = 3 * t₃ + 2 * t₂ := by
  fin_cases c <;> simp [pairTime, Fin.sum_univ_three] <;> ring

/-- **And so does the sum of their squares.**  `τ₃² + 2(τ₃+τ₂)²`, for every topology. -/
theorem sum_sq_pairTime (c : Fin 3) (t₃ t₂ : ℝ) :
    ∑ p : Fin 3, pairTime c p t₃ t₂ ^ 2 = t₃ ^ 2 + 2 * (t₃ + t₂) ^ 2 := by
  fin_cases c <;> simp [pairTime, Fin.sum_univ_three] <;> ring

/-- **The cross-sum, therefore, also forgets it.**  `Σ_{p<q} T_p T_q` is half the difference
between the square of the total and the total of the squares, and both of those are
topology-free, so it is `3τ₃² + 4τ₃τ₂ + τ₂²`.

This is the fact that makes `Var(π)` computable without averaging over tree shapes: the jump
chain's choice, which is where all the combinatorial difficulty of the coalescent lives, does
not enter. -/
theorem cross_pairTime (c : Fin 3) (t₃ t₂ : ℝ) :
    ((∑ p : Fin 3, pairTime c p t₃ t₂) ^ 2 - ∑ p : Fin 3, pairTime c p t₃ t₂ ^ 2) / 2
      = 3 * t₃ ^ 2 + 4 * t₃ * t₂ + t₂ ^ 2 := by
  rw [sum_pairTime, sum_sq_pairTime]
  ring

/-- Topology-independence, stated as such: any two first-merging pairs give the same
symmetric sums.  A corollary of the two theorems above, recorded because it is the
statement the computation rests on rather than a step inside it. -/
theorem pairTime_symmetric_sums_topology_free (c c' : Fin 3) (t₃ t₂ : ℝ) :
    (∑ p : Fin 3, pairTime c p t₃ t₂) = (∑ p : Fin 3, pairTime c' p t₃ t₂)
      ∧ (∑ p : Fin 3, pairTime c p t₃ t₂ ^ 2)
        = (∑ p : Fin 3, pairTime c' p t₃ t₂ ^ 2) := by
  constructor
  · rw [sum_pairTime, sum_pairTime]
  · rw [sum_sq_pairTime, sum_sq_pairTime]

/-! ### With the coalescent's moments -/

/-- **The cross-sum's expectation is `4`.**

The hypotheses are the moments of K-C (1.7)'s clock at the two rates a three-sample passes
through, `d₃ = 3` and `d₂ = 1`: `HoldingSecondMoment.integral_id_mul_holdDensity` gives
`E τ = 1/d` and `.integral_sq_mul_holdDensity` gives `E τ² = 2/d²`, so `E τ₃ = 1/3`,
`E τ₃² = 2/9`, `E τ₂ = 1`, `E τ₂² = 2`.  The remaining hypothesis, `E(τ₃τ₂) = E τ₃ · E τ₂`,
is independence of the clocks -- the corpus's standing assumption, tracked as `Program`
item 4 and not proved here. -/
theorem expected_cross_pairTime {e3 e3sq e2 e2sq e32 : ℝ}
    (h3 : e3 = 1 / 3) (h3sq : e3sq = 2 / 9) (h2 : e2 = 1) (h2sq : e2sq = 2)
    (hindep : e32 = e3 * e2) :
    3 * e3sq + 4 * e32 + e2sq = 4 := by
  subst h3 h3sq h2 h2sq hindep
  norm_num

/-- **`E(T_ij T_ik) = 4/3`.**  The cross-sum counts the three unordered pairs-of-pairs, and
they are exchangeable, so each has expectation a third of the total. -/
theorem expected_pairTime_product {e3 e3sq e2 e2sq e32 : ℝ}
    (h3 : e3 = 1 / 3) (h3sq : e3sq = 2 / 9) (h2 : e2 = 1) (h2sq : e2sq = 2)
    (hindep : e32 = e3 * e2) :
    (3 * e3sq + 4 * e32 + e2sq) / 3 = 4 / 3 := by
  rw [expected_cross_pairTime h3 h3sq h2 h2sq hindep]

/-- **`Cov(T_ij, T_ik) = 1/3`.**  Two pairwise coalescence times that share a lineage are
POSITIVELY correlated, and by exactly a third of their common mean.

That positive correlation is the whole reason Tajima's `Var(π)` is not the naive
`Var(S)/C(n,2)`: the pairwise differences a sample reports are not independent readings of
the same tree, they are overlapping readings, and the overlap is a third. -/
theorem covariance_pairTime {e3 e3sq e2 e2sq e32 : ℝ}
    (h3 : e3 = 1 / 3) (h3sq : e3sq = 2 / 9) (h2 : e2 = 1) (h2sq : e2sq = 2)
    (hindep : e32 = e3 * e2) :
    (3 * e3sq + 4 * e32 + e2sq) / 3 - 1 = 1 / 3 := by
  rw [expected_pairTime_product h3 h3sq h2 h2sq hindep]
  norm_num

/-- The mean pairwise time is `1` whatever the sample size, which is what makes the
subtraction above a covariance: `E(T_ij) = E(T_ik) = 1`.  Here it is inside the three-sample,
from the same two moments. -/
theorem expected_pairTime {e3 e2 : ℝ} (h3 : e3 = 1 / 3) (h2 : e2 = 1) :
    (3 * e3 + 2 * e2) / 3 = 1 := by
  subst h3 h2
  norm_num


/-! ### The four-sample, where the topology stops being invisible

Two DISJOINT pairs live in a four-sample, and there the trick above fails: the symmetric sums
are not topology-free, and an average over the second merger is needed.  Fixing the first
merger as the pair `01` costs no generality -- relabelling is a symmetry of the coalescent --
and the second merger is uniform on the three pairs of the three remaining blocks.

Writing `A = τ₄`, `B = τ₄+τ₃`, `C = τ₄+τ₃+τ₂` for the three heights, the three ways to
resolve the second merger give

  balanced `{2,3}`:      `T₀₁ = A`, `T₂₃ = B`, the rest `C`;
  caterpillar `{01},2`:  `T₀₁ = A`, `T₀₂ = T₁₂ = B`, the rest `C`;
  caterpillar `{01},3`:  `T₀₁ = A`, `T₀₃ = T₁₃ = B`, the rest `C`.

`sum_disjointProducts` computes the three disjoint products in each case -- `AB + 2C²` for
the balanced tree and `AC + 2BC` for either caterpillar, which are different polynomials, so
there is no topology-free shortcut.  Averaging over the three, `sum_over_second_merger` gives
a polynomial in the holding times, and the moments turn it into `E(T_ij T_kl) = 11/9`, hence
`Cov = 2/9`.

Pairs indexed as `01, 02, 03, 12, 13, 23` in `Fin 6`; the disjoint pairings are
`(01,23)`, `(02,13)`, `(03,12)`.
-/

/-- The pairwise times of a four-sample whose first merger is the pair `01`, indexed by the
second merger `s` (`0` balanced, `1` and `2` the two caterpillars).

Empirical status: NOT AN EMPIRICAL CLAIM.  As in `pairTime`, it reads the tree off the jump
chain and the clock. -/
def pairTime4 (s : Fin 3) (p : Fin 6) (t₄ t₃ t₂ : ℝ) : ℝ :=
  if p = 0 then t₄
  else if (s = 0 ∧ p = 5) ∨ (s = 1 ∧ (p = 1 ∨ p = 3)) ∨ (s = 2 ∧ (p = 2 ∨ p = 4)) then
    t₄ + t₃
  else t₄ + t₃ + t₂

/-- **The three disjoint products, per topology.**  `AB + 2C²` for the balanced tree,
`AC + 2BC` for either caterpillar -- different polynomials, which is why the four-sample
needs the average the three-sample did not. -/
theorem sum_disjointProducts (s : Fin 3) (t₄ t₃ t₂ : ℝ) :
    pairTime4 s 0 t₄ t₃ t₂ * pairTime4 s 5 t₄ t₃ t₂
        + pairTime4 s 1 t₄ t₃ t₂ * pairTime4 s 4 t₄ t₃ t₂
        + pairTime4 s 2 t₄ t₃ t₂ * pairTime4 s 3 t₄ t₃ t₂
      = if s = 0 then t₄ * (t₄ + t₃) + 2 * (t₄ + t₃ + t₂) ^ 2
        else t₄ * (t₄ + t₃ + t₂) + 2 * (t₄ + t₃) * (t₄ + t₃ + t₂) := by
  fin_cases s <;> norm_num [pairTime4, Fin.ext_iff] <;> ring

/-- **Summed over the three resolutions.**  `(AB + 2C²) + 2(AC + 2BC)`, expanded in the
holding times.  Dividing by three is the average the jump chain's uniform choice imposes. -/
theorem sum_over_second_merger (t₄ t₃ t₂ : ℝ) :
    (t₄ * (t₄ + t₃) + 2 * (t₄ + t₃ + t₂) ^ 2)
        + 2 * (t₄ * (t₄ + t₃ + t₂) + 2 * (t₄ + t₃) * (t₄ + t₃ + t₂))
      = 9 * t₄ ^ 2 + 6 * t₃ ^ 2 + 2 * t₂ ^ 2 + 15 * (t₄ * t₃) + 10 * (t₄ * t₂)
          + 8 * (t₃ * t₂) := by
  ring

/-- **`E(T_ij T_kl) = 11/9` for disjoint pairs.**

The hypotheses are the moments of K-C (1.7)'s clock at the three rates a four-sample passes
through, `d₄ = 6`, `d₃ = 3`, `d₂ = 1`, from `HoldingSecondMoment`: `E τ = 1/d`, `E τ² = 2/d²`.
Independence of the clocks turns each cross moment into a product, as at `expected_cross_pairTime`.

The polynomial is divided by nine: three for the average over the second merger, three for
the three disjoint pairings the sum ranges over. -/
theorem expected_disjoint_pairTime_product {e4 e4sq e3 e3sq e2 e2sq : ℝ}
    (h4 : e4 = 1 / 6) (h4sq : e4sq = 1 / 18) (h3 : e3 = 1 / 3) (h3sq : e3sq = 2 / 9)
    (h2 : e2 = 1) (h2sq : e2sq = 2) :
    (9 * e4sq + 6 * e3sq + 2 * e2sq + 15 * (e4 * e3) + 10 * (e4 * e2) + 8 * (e3 * e2)) / 9
      = 11 / 9 := by
  subst h4 h4sq h3 h3sq h2 h2sq
  norm_num

/-- **`Cov(T_ij, T_kl) = 2/9` for disjoint pairs.**  Positively correlated, but less than the
`1/3` of two pairs sharing a lineage -- they share only the part of the tree above both their
most recent common ancestors, and that is less of it. -/
theorem covariance_disjoint_pairTime {e4 e4sq e3 e3sq e2 e2sq : ℝ}
    (h4 : e4 = 1 / 6) (h4sq : e4sq = 1 / 18) (h3 : e3 = 1 / 3) (h3sq : e3sq = 2 / 9)
    (h2 : e2 = 1) (h2sq : e2sq = 2) :
    (9 * e4sq + 6 * e3sq + 2 * e2sq + 15 * (e4 * e3) + 10 * (e4 * e2) + 8 * (e3 * e2)) / 9 - 1
      = 2 / 9 := by
  rw [expected_disjoint_pairTime_product h4 h4sq h3 h3sq h2 h2sq]
  norm_num

end Coalescent

end Descent
