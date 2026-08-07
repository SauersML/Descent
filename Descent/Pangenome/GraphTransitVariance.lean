/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.TransitVariance
import Descent.Pangenome.ConstructionCoalescent

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The spread of the graph coalescent's transit time, and which conclusion survives it

`Descent.Pangenome.GraphCoalescent` lists "the variance of the graph coalescent's transit
time" among the things it does not contain.  This file is that entry, and the reason it is
worth a module rather than a line is that the answer splits: one of the two conclusions
`Descent.Coalescent.TransitVariance` draws is destroyed by a graph's compression and the other
is not.

## What is destroyed

`Var(T_n)` is a sum of `d_r⁻²` over the `n - 1` phases, so it is monotone in the sample size
(`varTransitTime_mono_of_le`).  A graph entering at `w` therefore reports a SMALLER variance
than the panel has, by exactly the phases between `w` and `n` -- `graphVarianceDeficit_eq`.
As with the mean in `Descent.Pangenome.GraphCoalescent.Deficit` and the spectrum in
`Descent.Pangenome.GraphSpectrum`, the direction is fixed and a coarser construction loses
more (`graphVarianceDeficit_antitone`).

So a study reading a variance off a graph and comparing it to a null computed at `n` is
comparing two different quantities, and the sign of the difference is known in advance.

## What survives

`TransitVariance.one_le_varTransitTime` says the variance is at least `1` for every sample of
at least two, because the final wait -- the phase with two lineages left -- has variance `1`
on its own and every earlier phase only adds.  That argument never used `n` beyond requiring
`2 ≤ n`.

`one_le_graphVarTransitTime` is therefore the same statement at `w`, needing only that the
graph did not collapse its panel to a single node.  The conclusion
`TransitVariance` draws from it -- that the tree height never concentrates, so a single locus
reports a time to common ancestry whose spread is comparable to its value -- is untouched by
graph compression, and untouched by the choice of builder.

**This is the useful half of the file.**  The corpus has now priced four things a graph
distorts: the mean transit time, Watterson's estimator, the spectrum's support, and the
variance.  It is worth knowing that the non-concentration argument is not among them, because
it is the one that constrains study design, and a reader who has seen the other four has no
reason to assume it holds.

## Empirical status

None.  Every result composes definitions already in the corpus.  The independence premise
under which `varTransitTime` is a variance at all is `TransitVariance`'s and is unchanged
here.

## Main results

- `varTransitTime_mono_of_le`: the variance is monotone in sample size.
- `graphVarianceDeficit_nonneg`, `graphVarianceDeficit_antitone`: a graph understates the
  spread, and a coarser build understates it more.
- `one_le_graphVarTransitTime`: **the surviving conclusion.**  The spread is at least `1` at
  the graph's own width, so non-concentration is not a casualty of compression.
-/

namespace Descent.Pangenome.GraphCoalescent

open Descent.Coalescent

/-! ### The variance grows with the sample -/

/-- **The transit variance is monotone in sample size.**  It is a sum of nonnegative phase
variances over `range (n - 1)`, and enlarging the sample only appends phases.

This is what makes every statement below one-directional; without it the graph's variance
would merely differ from the panel's rather than fall short of it. -/
theorem varTransitTime_mono_of_le {m n : ℕ} (h : m ≤ n) :
    varTransitTime m ≤ varTransitTime n := by
  unfold varTransitTime
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.sub_le_sub_right h 1)) ?_
  intro k _ _
  positivity

/-! ### What a graph reports, and what it leaves out -/

/-- **The spread the graph coalescent reports**: the panel's formula at the graph's own
entrance point.

Empirical status: DERIVED.  It is `Coalescent.varTransitTime` at `Linkage.width s`, which is
`Descent.Pangenome.GraphCoalescent.Reduction`'s identification of the sample size and not a
new assumption. -/
noncomputable def graphVarTransitTime {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  varTransitTime (Linkage.width s)

/-- **The spread a graph does not report**: the panel's variance less the graph's.

Empirical status: DERIVED.  Both terms are `Coalescent.varTransitTime`. -/
noncomputable def graphVarianceDeficit {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  varTransitTime n - graphVarTransitTime s

/-- The deficit is exactly the phases between the graph's width and the panel's size. -/
theorem graphVarianceDeficit_eq {n : ℕ} (s : Fin n → Fin n) :
    graphVarianceDeficit s = varTransitTime n - varTransitTime (Linkage.width s) := rfl

/-- **A graph never reports a wider spread than the panel has.**  The width is at most `n`
and the variance is monotone. -/
theorem graphVarianceDeficit_nonneg {n : ℕ} (s : Fin n → Fin n) :
    0 ≤ graphVarianceDeficit s := by
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  have := varTransitTime_mono_of_le hle
  rw [graphVarianceDeficit_eq]
  linarith

/-- **A coarser construction understates the spread more.**  The same bracket as the mean and
the spectrum, on the second moment. -/
theorem graphVarianceDeficit_antitone {n : ℕ} {s t : Fin n → Fin n}
    (h : graphKer s ≤ graphKer t) :
    graphVarianceDeficit s ≤ graphVarianceDeficit t := by
  have hts : Linkage.width t ≤ Linkage.width s := width_antitone h
  have := varTransitTime_mono_of_le hts
  rw [graphVarianceDeficit_eq, graphVarianceDeficit_eq]
  linarith

/-- **A faithful graph loses no spread.**  If the interface merges nothing then the width is
`n` and the deficit vanishes, so the shortfall is a property of the compression rather than
of reading a variance off a graph at all.

Assumes: `Linkage.width s = n`. -/
theorem graphVarianceDeficit_eq_zero {n : ℕ} {s : Fin n → Fin n} (h : Linkage.width s = n) :
    graphVarianceDeficit s = 0 := by
  rw [graphVarianceDeficit_eq, h, sub_self]

/-! ### The conclusion that survives -/

/-- **Non-concentration is not a casualty of compression.**

The variance is at least `1` at the graph's own width, for the same reason it is at the
panel's: the final two-lineage wait contributes `1` by itself and every earlier phase adds
more.  The argument never mentioned `n` except to require two lineages, and a graph that
merged its panel to at least two nodes still has them.

So of the four things this corpus has now priced a graph for distorting -- the mean transit
time, Watterson's `θ_W`, the spectrum's support and the variance's magnitude -- the
non-concentration bound is not among them.  It holds at `w`, for every builder, and it is the
one of the five that constrains study design.

Assumes: `2 ≤ Linkage.width s`, i.e. the graph did not collapse the panel to a point. -/
theorem one_le_graphVarTransitTime {n : ℕ} {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s) :
    1 ≤ graphVarTransitTime s :=
  one_le_varTransitTime hw

/-- **And the spread is still bounded by the mean at the graph's width**, so the graph
coalescent is not a process with a qualitatively different shape -- it is Kingman's, entered
later, with every inequality `TransitVariance` proves holding at `w`. -/
theorem graphVarTransitTime_le_graphMeanTransitTime {n : ℕ} (s : Fin n → Fin n) :
    graphVarTransitTime s ≤ meanTransitTime (Linkage.width s) :=
  varTransitTime_le_meanTransitTime (Linkage.width s)

end Descent.Pangenome.GraphCoalescent
