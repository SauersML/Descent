/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SiteFrequencySpectrum
import Descent.Pangenome.ConstructionCoalescent

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The site frequency spectrum a pangenome graph reports, and where it stops

`Descent.Pangenome.GraphCoalescent` closes with a list of what the group does not contain.
One entry is "the site-frequency spectrum at `w`".  This file is that entry.

`Descent.Coalescent.SiteFrequencySpectrum` proves Fu's `E(ξ_i) = θ/i` and, in
`sum_expectedSpectrum`, that the classes `i = 1, …, n-1` total Watterson's `E(S_n)` exactly.
Both facts are about a sample of `n`.  `Descent.Pangenome.GraphCoalescent.Reduction` shows a
graph hands the coalescent a sample of `Linkage.width s`, whatever `n` the study wrote down.
Composing them says what a study reading its spectrum off a graph actually reports.

## The two defects, and why only one of them is the one people look for

The heights are unchanged.  `graphSpectrum_eq` is `θ/i` again, with no `w` in it: a graph does
not distort the frequency classes it can express, because `E(ξ_i) = θ/i` never mentioned the
sample size.  So the shape results carry over verbatim, and a study fitting demography to the
SHAPE of a graph spectrum is not, on this account, misled.

**The support is truncated.**  The classes run to `w - 1` and not to `n - 1`, so
`graphSpectrum_total_eq` gives `E(S) = θ · a_{w-1}`, and `graphSpectrum_missing_eq` names the
difference exactly: the classes `i = w, …, n-1` are absent, and their total is
`θ · (a_{n-1} - a_{w-1})`.  The variants that go missing are precisely the COMMON ones -- the
high-frequency classes, which are the classes a graph's merging destroys, because two
haplotypes merged into one node can no longer disagree.

This is the opposite of the usual worry.  A graph is normally suspected of losing rare
variation; what it provably loses here is the top of the spectrum, and it loses it by
truncation rather than by attenuation.

## Where the construction comes in

`graphSpectrum_missing_antitone` puts the previous file's bracket on this quantity: a coarser
construction has a smaller `w`, so it truncates earlier and the missing mass is larger.  The
orientation is again fixed in advance -- closure loses more of the common classes than
pruning does -- so the difference between two pipelines' spectra has a known sign at the top
end before any data is seen.

## What is not claimed

The heights are exact only under the same neutrality and infinite-sites premises
`SiteFrequencySpectrum` already carries; nothing here weakens or strengthens them.  Nothing
here claims a real graph's spectrum has been measured against this.

## Empirical status

None.  Every result composes definitions already in the corpus.

## Main results

- `graphSpectrum_eq`: the class heights are `θ/i`, unchanged by the graph.
- `graphSpectrum_total_eq`: the classes total `θ · a_{w-1}`, not `θ · a_{n-1}`.
- `graphSpectrum_missing_eq`: **the exact loss**, `θ · (a_{n-1} - a_{w-1})`, carried entirely
  by the high-frequency classes.
- `graphSpectrum_missing_nonneg`, `graphSpectrum_missing_antitone`: the loss is never
  negative, and a coarser construction loses more.
-/

namespace Descent.Pangenome.GraphCoalescent

open Descent.Coalescent

/-! ### The spectrum a graph can express -/

/-- **The `i`-th frequency class as a graph reports it.**  The height is the coalescent's own
`E(ξ_i)`, because a graph changes the sample size and not the mutation process; what the
graph changes is which `i` exist, and that is carried by `graphSpectrumClasses` below.

Empirical status: DERIVED.  It is `Coalescent.expectedSpectrum` with no new content; the
content is in the range of `i` it is summed over. -/
noncomputable def graphSpectrum (θ : Descent.Core.Theta) (i : ℕ) : ℝ :=
  expectedSpectrum θ i

/-- **The heights do not move.**  `E(ξ_i) = θ/i` mentions no sample size, so a graph that
compressed its panel reports the same height for every class it can still express.

The consequence worth stating: a study fitting demography to the SHAPE of a graph spectrum is
not misled by the compression.  The defect is elsewhere. -/
theorem graphSpectrum_eq (θ : Descent.Core.Theta) (i : ℕ) :
    graphSpectrum θ i = θ.value / (i : ℝ) :=
  expectedSpectrum_eq θ i

/-- **How many classes a graph has**: one for each `i = 1, …, w-1`, where `w` is the graph's
width.  This is the whole difference between a graph spectrum and a panel spectrum, and it is
a consequence of `Reduction`'s identification of the entrance point rather than a new
assumption.

Empirical status: DERIVED.  `Linkage.width s` is the graph's node count, which
`GraphCoalescent.blocks_graphKer` identifies with the coalescent's block count. -/
def graphSpectrumClasses {n : ℕ} (s : Fin n → Fin n) : ℕ := Linkage.width s - 1

/-- **The graph's classes total `θ · a_{w-1}`.**  `Coalescent.sum_expectedSpectrum` at the
graph's own sample size: the spectrum sums to Watterson's `E(S)` evaluated at `w`, not at
`n`. -/
theorem graphSpectrum_total_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    ∑ j ∈ Finset.range (graphSpectrumClasses s), graphSpectrum θ (j + 1)
      = expectedSegregatingSites θ (Linkage.width s) := by
  unfold graphSpectrumClasses graphSpectrum
  exact sum_expectedSpectrum θ (Linkage.width s)

/-! ### What is missing, and which end of the spectrum it comes from -/

/-- **The spectrum mass a graph does not report**: the panel's total less the graph's.

The classes `i = w, …, n-1` have no counterpart in a graph of width `w`, and they are the
HIGH-frequency classes.  That is forced by what merging does: two haplotypes merged into one
node cannot disagree at any site, so the variants a graph destroys are exactly the ones many
haplotypes shared.

Empirical status: DERIVED.  Both terms are `Coalescent.expectedSegregatingSites`. -/
noncomputable def graphSpectrumMissing {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    ℝ :=
  expectedSegregatingSites θ n - expectedSegregatingSites θ (Linkage.width s)

/-- **The loss, exactly**: `θ · (a_{n-1} - a_{w-1})`.

This is the numerator counterpart of `Deficit.graphWatterson`.  There the sample size in the
DENOMINATOR was wrong; here the number of classes actually summed is short, and the shortfall
is a difference of harmonic numbers with both indices known to the study. -/
theorem graphSpectrumMissing_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    graphSpectrumMissing θ s
      = θ.value * (harmonicSum (n - 1) - harmonicSum (Linkage.width s - 1)) := by
  unfold graphSpectrumMissing
  rw [expectedSegregatingSites_eq, expectedSegregatingSites_eq]
  ring

/-- **A graph never reports more spectrum than the panel has.**  The width is at most `n`, the
harmonic sum is monotone, and the loss is therefore nonnegative.

Assumes: `0 ≤ θ.value`. -/
theorem graphSpectrumMissing_nonneg {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n)
    (hθ : 0 ≤ θ.value) : 0 ≤ graphSpectrumMissing θ s := by
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  have hmono : harmonicSum (Linkage.width s - 1) ≤ harmonicSum (n - 1) :=
    harmonicSum_strictMono.monotone (Nat.sub_le_sub_right hle 1)
  rw [graphSpectrumMissing_eq]
  exact mul_nonneg hθ (by linarith)

/-- **A coarser construction loses more of the spectrum.**

`ConstructionCoalescent.width_antitone` puts the coarser build at the smaller width, and the
harmonic sum is monotone, so the truncation bites earlier and the missing mass is larger.

With `graphSpectrumMissing_eq` naming which classes are lost, this fixes the sign of the
construction confound at the top of the spectrum: a closure-maximal build reports fewer
common variants than a restriction-minimal one, and the difference is `θ` times a gap between
harmonic numbers rather than an unknown.

Assumes: `0 ≤ θ.value`. -/
theorem graphSpectrumMissing_antitone {n : ℕ} (θ : Descent.Core.Theta) {s t : Fin n → Fin n}
    (h : graphKer s ≤ graphKer t) (hθ : 0 ≤ θ.value) :
    graphSpectrumMissing θ s ≤ graphSpectrumMissing θ t := by
  have hts : Linkage.width t ≤ Linkage.width s := width_antitone h
  have hmono : harmonicSum (Linkage.width t - 1) ≤ harmonicSum (Linkage.width s - 1) :=
    harmonicSum_strictMono.monotone (Nat.sub_le_sub_right hts 1)
  rw [graphSpectrumMissing_eq, graphSpectrumMissing_eq]
  have := mul_le_mul_of_nonneg_left (sub_le_sub_left hmono (harmonicSum (n - 1))) hθ
  linarith

/-- **A faithful graph loses nothing.**  If the interface merges no two panel haplotypes then
the width is `n`, the class count is `n - 1`, and the missing mass is zero.

This is the complement that keeps the results above from reading as a blanket charge against
graphs: the loss is a property of the compression, and a graph that compressed nothing pays
none of it.

Assumes: `Linkage.width s = n`. -/
theorem graphSpectrumMissing_eq_zero {n : ℕ} (θ : Descent.Core.Theta) {s : Fin n → Fin n}
    (h : Linkage.width s = n) : graphSpectrumMissing θ s = 0 := by
  rw [graphSpectrumMissing_eq, h, sub_self, mul_zero]

end Descent.Pangenome.GraphCoalescent
