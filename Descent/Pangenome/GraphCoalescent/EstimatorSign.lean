/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.WidthProfile

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The graph does not bias Tajima's `D`; declaring the wrong sample size does

`Descent.Coalescent.SegregatingSites` proves `expectedTajimaNumerator_eq_zero`: under the
coalescent null the two estimators of `θ` agree in expectation, which is what makes Tajima's
`D` a test.  The proof uses `n` twice -- once in `E(S) = θ a_{n-1}` and once in the
`a_{n-1}` that `wattersonEstimator` divides by -- and it is exact because the two `n`s are
the same number.

A pangenome graph breaks that.  Its data are a sample of `Linkage.width s`
(`Descent.Pangenome.GraphCoalescent.Reduction`), while the sample size a study writes down is
whatever it believes it has.  When the two differ the `n`s no longer cancel, and this file
computes what is left.

**The whole artefact is the ratio `a_{w-1} / a_{m-1}` between the true sample size and the
declared one, and its sign is decided by which of the two is larger.**

## Why the defect is entirely in Watterson's term

`E(π) = θ` carries no sample size at all -- `expectedPairwiseDifferences` is `E(S)` at `2`,
so it is `θ` whatever the graph did, provided the graph still has two nodes to compare.
Watterson's term carries the sample size twice.  So the graph moves one term of the
difference and not the other, which is exactly the asymmetry Tajima's `D` was built on and
exactly why the artefact does not cancel.

This is the same asymmetry that makes `π` the more robust statistic under missing data, and
it says the robustness has a reason rather than being an empirical regularity: `π` is a
two-sample quantity and two is a number no sampling accident changes.

## The sign, and why it is the opposite of the one `WidthProfile` finds

A study whose graph collapsed a locus and which divides by the PANEL's `a_{n-1}`
underestimates `θ_W`, leaves `π` alone, and so reports a POSITIVE numerator
(`graphTajimaNumerator_pos_of_width_lt`) -- the direction of balancing selection or a
population contraction, not of a sweep.

`Descent.Pangenome.GraphCoalescent.WidthProfile` finds the opposite direction, and the two
are not in conflict because they are different comparisons.  There, two LOCI are each read at
their own `w`, and the collapsed one has the site-frequency spectrum of a smaller sample,
which is skewed towards rare variants.  Here, ONE locus read at `w` is scored against a
DECLARED `m`.  A scan that compares windows to each other sees the first; a study that
computes `D` from a declared sample size sees the second.  Both are artefacts of the same
`w`, and they point opposite ways, so the sign of the bias a pangenome graph induces is not a
property of the graph -- it is a property of the statistic.

That is the useful form of the result, and it is why `graphTajimaNumerator` carries the
declared size as an explicit argument rather than assuming one.

## The repair is free

`graphTajimaNumerator_eq_zero_of_consistent`: declare the graph's own `w` and the numerator
is zero again, exactly. Nothing has to be estimated, because `w` is a property of the graph
the study already has.

## Main results

- `graphTajimaNumerator`: `π - θ_W` when the data are a `w`-sample and the declared size is
  `m`.
- `graphTajimaNumerator_eq`: **the artefact, exactly** -- `θ (1 - a_{w-1} / a_{m-1})`.
- `graphTajimaNumerator_eq_zero_of_consistent`: **the repair.**  Declaring `w` restores the
  null exactly.
- `graphTajimaNumerator_pos_of_width_lt`: declaring the panel's larger `n` makes it positive.
- `graphTajimaNumerator_neg_of_lt_width`: declaring a smaller size makes it negative, so the
  sign is genuinely a function of the mismatch and not a direction the graph prefers.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### The numerator a study actually computes -/

/-- **Tajima's numerator as a study computes it from a pangenome graph**: pairwise diversity,
which the graph does not touch, less Watterson's estimator applied to the graph's segregating
sites at a DECLARED sample size `m`.

Empirical status: DERIVED.  Both terms are the corpus's own
(`Coalescent.expectedPairwiseDifferences`, `Coalescent.wattersonEstimator`); the only new
content is that the sites are the graph's, which is
`Descent.Pangenome.GraphCoalescent.WidthProfile.graphExpectedSegregatingSites`, and that the
divisor's `m` need not equal the graph's `w`. -/
noncomputable def graphTajimaNumerator {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n)
    (m : ℕ) : ℝ :=
  Coalescent.expectedPairwiseDifferences θ
    - Coalescent.wattersonEstimator (graphExpectedSegregatingSites θ s) m

/-- **The artefact, exactly**: `θ (1 - a_{w-1} / a_{m-1})`.

Everything the graph did to the statistic is in that ratio, and both of its arguments are
integers the study has: `w` is a property of the graph and `m` is what the study declared. -/
theorem graphTajimaNumerator_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n)
    (m : ℕ) :
    graphTajimaNumerator θ s m
      = θ.value * (1 - Coalescent.harmonicSum (Linkage.width s - 1)
          / Coalescent.harmonicSum (m - 1)) := by
  unfold graphTajimaNumerator Coalescent.wattersonEstimator
  rw [Coalescent.expectedPairwiseDifferences_eq, graphExpectedSegregatingSites_eq]
  ring

/-! ### The repair -/

/-- **Declaring the graph's own sample size restores the null exactly.**  No estimation and
no correction factor: `w` is a property of the graph the study already holds, and using it
makes the two `a`'s cancel as they do in
`Descent.Coalescent.SegregatingSites.expectedTajimaNumerator_eq_zero`.

Assumes: `2 ≤ Linkage.width s`, so the graph has a pair to compare. -/
theorem graphTajimaNumerator_eq_zero_of_consistent {n : ℕ} (θ : Descent.Core.Theta)
    {s : Fin n → Fin n} (h2 : 2 ≤ Linkage.width s) :
    graphTajimaNumerator θ s (Linkage.width s) = 0 := by
  have hpos : 0 < Coalescent.harmonicSum (Linkage.width s - 1) :=
    Coalescent.harmonicSum_pos_of_two_le h2
  rw [graphTajimaNumerator_eq, div_self hpos.ne']
  ring

/-! ### The sign is a function of the mismatch

Both directions are proved, and that is the point of the section.  A bias that always pointed
one way could be argued to be a property of pangenome graphs; one whose sign flips with a
number the analyst chose is a property of the analysis. -/

/-- **Declaring the panel's size makes Tajima's `D` positive.**  A study whose graph collapsed
a locus, and which divides by the panel's `a_{n-1}` rather than the graph's `a_{w-1}`,
underestimates `θ_W`, leaves `π` untouched, and reports a strictly positive numerator -- the
direction of balancing selection or a contraction.

Assumes: `0 < θ.value`, `2 ≤ Linkage.width s`, and `Linkage.width s < m`. -/
theorem graphTajimaNumerator_pos_of_width_lt {n : ℕ} {θ : Descent.Core.Theta}
    (hθ : 0 < θ.value) {s : Fin n → Fin n} {m : ℕ} (h2 : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < m) : 0 < graphTajimaNumerator θ s m := by
  have hpos : 0 < Coalescent.harmonicSum (Linkage.width s - 1) :=
    Coalescent.harmonicSum_pos_of_two_le h2
  have hmono : Coalescent.harmonicSum (Linkage.width s - 1)
      < Coalescent.harmonicSum (m - 1) := Coalescent.harmonicSum_strictMono (by omega)
  have hposm : 0 < Coalescent.harmonicSum (m - 1) := lt_trans hpos hmono
  have hratio : Coalescent.harmonicSum (Linkage.width s - 1)
      / Coalescent.harmonicSum (m - 1) < 1 := (div_lt_one hposm).mpr hmono
  rw [graphTajimaNumerator_eq]
  exact mul_pos hθ (by linarith)

/-- **And declaring a smaller size makes it negative.**  Proved so that the sign is on record
as a function of the mismatch rather than a direction pangenome graphs push.

Assumes: `0 < θ.value`, `2 ≤ m`, and `m < Linkage.width s`. -/
theorem graphTajimaNumerator_neg_of_lt_width {n : ℕ} {θ : Descent.Core.Theta}
    (hθ : 0 < θ.value) {s : Fin n → Fin n} {m : ℕ} (h2 : 2 ≤ m)
    (hlt : m < Linkage.width s) : graphTajimaNumerator θ s m < 0 := by
  have hposm : 0 < Coalescent.harmonicSum (m - 1) := Coalescent.harmonicSum_pos_of_two_le h2
  have hmono : Coalescent.harmonicSum (m - 1)
      < Coalescent.harmonicSum (Linkage.width s - 1) :=
    Coalescent.harmonicSum_strictMono (by omega)
  have hratio : 1 < Coalescent.harmonicSum (Linkage.width s - 1)
      / Coalescent.harmonicSum (m - 1) := (one_lt_div hposm).mpr hmono
  rw [graphTajimaNumerator_eq]
  have : θ.value * (1 - Coalescent.harmonicSum (Linkage.width s - 1)
      / Coalescent.harmonicSum (m - 1)) < θ.value * 0 :=
    mul_lt_mul_of_pos_left (by linarith) hθ
  linarith [this]

/-- **The whole defect is in Watterson's term.**  Pairwise diversity is `E(S)` at two, so it
carries no sample size and the graph cannot move it; subtracting the artefact from the
numerator leaves exactly `π`.

This is the formal content of the observation that `π` is the robust statistic: not that it
happens to be less sensitive, but that the number it depends on is `2`, which no collapse of
a graph and no declaration by an analyst can change. -/
theorem graphTajimaNumerator_add_watterson {n : ℕ} (θ : Descent.Core.Theta)
    (s : Fin n → Fin n) (m : ℕ) :
    graphTajimaNumerator θ s m
        + Coalescent.wattersonEstimator (graphExpectedSegregatingSites θ s) m
      = Coalescent.expectedPairwiseDifferences θ := by
  unfold graphTajimaNumerator
  ring

end Descent.Pangenome.GraphCoalescent
