/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SiteFrequencySpectrum
import Descent.Pangenome.GraphCoalescent.MergerDepth
import Descent.Pangenome.Linkage.Chain

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# A graph that collapses more at one locus than another manufactures a sweep there

Everything so far has been about one interface.  A real pangenome graph is a chain of them
(`Descent.Pangenome.Linkage.Chain`), and the widths along that chain are not equal: graph
builders collapse copy-number polymorphic loci -- segmental duplications, VNTRs -- into a
single copy through which the haplotypes loop, while leaving unique sequence uncollapsed.
So `w` is a FUNCTION OF POSITION, and `Descent.Pangenome.GraphCoalescent.Reduction` says the
graph coalescent's sample size is `w`.

**The graph therefore reports a different sample size at every locus, and the profile of
sample sizes is a property of the build rather than of the population.**

That is not a small bookkeeping point, because the two headline signatures of a selective
sweep are both monotone in sample size and both move the wrong way:

* **Diversity falls.**  `E(S) = θ a_{w-1}`, so a collapsed locus reports fewer segregating
  sites than an uncollapsed one at the same `θ` (`expectedSegregatingSites_lt_of_width_lt`).
  A reduction in diversity relative to its neighbours is the necessary hallmark that sweep
  scans key on.
* **And rare variants become MORE common, not less.**  The singleton share is `1 / a_{w-1}`
  (`graphSingletonShare_eq`), which is DECREASING in `w`, so the collapsed locus shows a
  relative excess of singletons (`graphSingletonShare_lt_of_width_lt`) -- the skew towards
  rare variants that a sweep produces and that a plain loss of data would not.

A locus the builder collapsed thus presents both marks at once, in the right directions, with
no selection anywhere in the model.  The magnitudes are exact and are functions of the two
widths alone.

## What this does and does not claim

It does not claim any published sweep is an artefact.  It claims that the width profile of a
graph is a confounder with the same sign as selection on both statistics, that its size is
computable from the build, and that a scan which does not condition on it has no way to
separate the two.  The existing practice of dropping extremely low-diversity windows is a
crude version of exactly this conditioning; the theorems below say what the correct
adjustment is, since `a_{w-1}` is known once `w` is.

## Why it is not the same statement as `Deficit`

`Descent.Pangenome.GraphCoalescent.Deficit` compares the graph to the PANEL -- one interface
against the `n` it came from -- and finds a bias in `θ`. That bias is global: it moves every
locus the same way and a scan comparing loci to each other would not see it.  What is here is
the comparison of one locus to ANOTHER, where the two `w`s differ, and it survives every
normalisation that removes a global factor.  A confounder that cancels in a genome-wide mean
and does not cancel in a scan is the more dangerous of the two, and it is the one a
per-interface theory was needed to state.

## Main results

- `widthProfile`: the graph's sample size, locus by locus along a chain.
- `graphMeanTransitTime_lt_of_width_lt`: collapsed loci have shallower trees.
- `graphExpectedSegregatingSites`, `expectedSegregatingSites_lt_of_width_lt`: **and less
  diversity**, at equal `θ`.
- `graphSingletonShare_eq`: the singleton share at a locus is `1 / a_{w-1}`.
- `graphSingletonShare_lt_of_width_lt`: **and it is larger where the graph collapsed more**,
  so the SFS skews towards rare variants exactly as under a sweep.
- `mergerDepth_lt_of_width_lt`: the collapsed locus is also where the build's simultaneous
  merger is deepest, which is the `Ξ` signature of `MergerDepth` varying along the genome.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### The profile -/

/-- **The graph coalescent's sample size, locus by locus.**  One entry per interface of the
chain, each the number of graph states occupied there.

Empirical status: DERIVED.  Each entry is `Descent.Pangenome.Linkage.width` of the
corresponding interface, and that this is the sample size rather than a summary of the
topology is `Descent.Pangenome.GraphCoalescent.Reduction`. -/
def widthProfile {n : ℕ} (c : Linkage.Chain (Fin n)) : List ℕ := c.map Linkage.width

@[simp] theorem widthProfile_length {n : ℕ} (c : Linkage.Chain (Fin n)) :
    (widthProfile c).length = c.length := by
  simp [widthProfile]

/-! ### Shallower trees where the graph collapsed more -/

/-- **A collapsed locus has a shallower tree.**  K-G (5.7) is increasing in the sample size,
so the graph reports a smaller time to the most recent common ancestor exactly where it
merged more haplotypes.

Assumes: `1 ≤ Linkage.width s₁`, the nondegeneracy under which K-G (5.7) has its closed
form. -/
theorem graphMeanTransitTime_lt_of_width_lt {n : ℕ} {s₁ s₂ : Fin n → Fin n}
    (h1 : 1 ≤ Linkage.width s₁) (hlt : Linkage.width s₁ < Linkage.width s₂) :
    graphMeanTransitTime s₁ < graphMeanTransitTime s₂ := by
  have h2 : 1 ≤ Linkage.width s₂ := le_trans h1 (le_of_lt hlt)
  have p1 : (0 : ℝ) < (Linkage.width s₁ : ℝ) := by exact_mod_cast h1
  have p2 : (0 : ℝ) < (Linkage.width s₂ : ℝ) := by exact_mod_cast h2
  have hcast : (Linkage.width s₁ : ℝ) < (Linkage.width s₂ : ℝ) := by exact_mod_cast hlt
  have hkey : (2 : ℝ) / (Linkage.width s₂ : ℝ) < 2 / (Linkage.width s₁ : ℝ) := by
    rw [div_lt_div_iff₀ p2 p1]
    linarith
  rw [graphMeanTransitTime_eq h1, graphMeanTransitTime_eq h2]
  linarith

/-- The merger depth moves the other way: the collapsed locus is where the build's
simultaneous merger is deepest.  So the `Ξ`-signature of
`Descent.Pangenome.GraphCoalescent.MergerDepth` is itself a function of position, and it
peaks exactly where the diversity trough is.

Assumes: `Linkage.width s₂ ≤ n`, which `Linkage.width_le_card` gives for any interface. -/
theorem mergerDepth_lt_of_width_lt {n : ℕ} {s₁ s₂ : Fin n → Fin n}
    (hlt : Linkage.width s₁ < Linkage.width s₂) : mergerDepth s₂ < mergerDepth s₁ := by
  have h2 : Linkage.width s₂ ≤ n := by simpa using Linkage.width_le_card s₂
  unfold mergerDepth
  omega

/-! ### Less diversity, at equal `θ` -/

/-- **The diversity a graph reports at one interface**: Watterson's expectation at the
graph's own sample size rather than the panel's.

Empirical status: DERIVED.  It is `Coalescent.expectedSegregatingSites` evaluated at
`Linkage.width s`; the identification of that argument as the sample size is
`Descent.Pangenome.GraphCoalescent.Reduction` and is not assumed here. -/
noncomputable def graphExpectedSegregatingSites {n : ℕ} (θ : Descent.Core.Theta)
    (s : Fin n → Fin n) : ℝ :=
  Coalescent.expectedSegregatingSites θ (Linkage.width s)

theorem graphExpectedSegregatingSites_eq {n : ℕ} (θ : Descent.Core.Theta)
    (s : Fin n → Fin n) :
    graphExpectedSegregatingSites θ s
      = θ.value * Coalescent.harmonicSum (Linkage.width s - 1) :=
  Coalescent.expectedSegregatingSites_eq θ _

/-- **The diversity trough.**  At one and the same `θ`, the locus the graph collapsed more
reports strictly fewer segregating sites.  This is the necessary hallmark that sweep scans
key on, produced here by the build.

Assumes: `0 < θ.value` and `2 ≤ Linkage.width s₁` -- below two states there are no pairs and
Watterson's expectation is zero for a reason that has nothing to do with this. -/
theorem expectedSegregatingSites_lt_of_width_lt {n : ℕ} {θ : Descent.Core.Theta}
    (hθ : 0 < θ.value) {s₁ s₂ : Fin n → Fin n} (h2 : 2 ≤ Linkage.width s₁)
    (hlt : Linkage.width s₁ < Linkage.width s₂) :
    graphExpectedSegregatingSites θ s₁ < graphExpectedSegregatingSites θ s₂ := by
  have hmono : Coalescent.harmonicSum (Linkage.width s₁ - 1)
      < Coalescent.harmonicSum (Linkage.width s₂ - 1) :=
    Coalescent.harmonicSum_strictMono (by omega)
  rw [graphExpectedSegregatingSites_eq, graphExpectedSegregatingSites_eq]
  exact mul_lt_mul_of_pos_left hmono hθ

/-! ### And a relative excess of rare variants

`Descent.Coalescent.SiteFrequencySpectrum.singletonShare_eq` computes the singleton share of
a sample of `n` as `1 / a_{n-1}`: the mutation rate cancels, and what is left is a pure
function of the sample size, decaying like `1 / log n`.  Read at the graph's sample size it
becomes a function of position along the genome. -/

/-- **The share of the graph's reported variation that is singletons**, at one interface.

Empirical status: DERIVED.  `Descent.Coalescent.SiteFrequencySpectrum.singletonShare_eq`
shows the share is `1 / a_{k-1}` for a sample of `k`, with `θ` cancelling;
`graphSingletonShare_eq` is that identity at `k = Linkage.width s`. -/
noncomputable def graphSingletonShare {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  1 / Coalescent.harmonicSum (Linkage.width s - 1)

/-- The share is what the spectrum says it is, at the graph's sample size.

Assumes: `θ.value ≠ 0` and `2 ≤ Linkage.width s`. -/
theorem graphSingletonShare_eq {n : ℕ} {θ : Descent.Core.Theta} (hθ : θ.value ≠ 0)
    {s : Fin n → Fin n} (h2 : 2 ≤ Linkage.width s) :
    Coalescent.expectedSpectrum θ 1 / graphExpectedSegregatingSites θ s
      = graphSingletonShare s :=
  Coalescent.singletonShare_eq hθ h2

/-- **The skew towards rare variants.**  The singleton share is DECREASING in sample size, so
the locus the graph collapsed more reports a strictly LARGER share of singletons.

This is the direction that makes the artefact resemble selection rather than mere data loss.
A window that had simply lost variants at random would keep the spectrum's shape; a window
whose sample size fell reports the shape of a smaller sample, which is skewed towards the
rare end -- the same direction a sweep skews it.

Assumes: `2 ≤ Linkage.width s₁` and `Linkage.width s₁ < Linkage.width s₂`. -/
theorem graphSingletonShare_lt_of_width_lt {n : ℕ} {s₁ s₂ : Fin n → Fin n}
    (h2 : 2 ≤ Linkage.width s₁) (hlt : Linkage.width s₁ < Linkage.width s₂) :
    graphSingletonShare s₂ < graphSingletonShare s₁ := by
  have hpos1 : 0 < Coalescent.harmonicSum (Linkage.width s₁ - 1) :=
    Coalescent.harmonicSum_pos_of_two_le h2
  have hmono : Coalescent.harmonicSum (Linkage.width s₁ - 1)
      < Coalescent.harmonicSum (Linkage.width s₂ - 1) :=
    Coalescent.harmonicSum_strictMono (by omega)
  have hpos2 : 0 < Coalescent.harmonicSum (Linkage.width s₂ - 1) := lt_trans hpos1 hmono
  unfold graphSingletonShare
  rw [div_lt_div_iff₀ hpos2 hpos1]
  linarith

/-- **Both marks at once.**  At equal `θ`, the collapsed locus reports strictly less
diversity AND a strictly larger share of singletons than its uncollapsed neighbour.  Stated
as one conjunction because it is the conjunction that resembles a sweep: either alone has
innocent explanations, and a scan looks for both.

Assumes: `0 < θ.value`, `2 ≤ Linkage.width s₁`, `Linkage.width s₁ < Linkage.width s₂`. -/
theorem sweepSignature_of_width_lt {n : ℕ} {θ : Descent.Core.Theta} (hθ : 0 < θ.value)
    {s₁ s₂ : Fin n → Fin n} (h2 : 2 ≤ Linkage.width s₁)
    (hlt : Linkage.width s₁ < Linkage.width s₂) :
    graphExpectedSegregatingSites θ s₁ < graphExpectedSegregatingSites θ s₂ ∧
      graphSingletonShare s₂ < graphSingletonShare s₁ :=
  ⟨expectedSegregatingSites_lt_of_width_lt hθ h2 hlt,
    graphSingletonShare_lt_of_width_lt h2 hlt⟩

/-- **A uniform graph has no profile and no artefact.**  Where the widths agree, both
statistics agree, so the confounder is exactly the VARIATION in the width profile and not
its level.  This is why the effect survives a global normalisation and why `Deficit`'s bias
and this one are different findings. -/
theorem no_signature_of_width_eq {n : ℕ} (θ : Descent.Core.Theta) {s₁ s₂ : Fin n → Fin n}
    (h : Linkage.width s₁ = Linkage.width s₂) :
    graphExpectedSegregatingSites θ s₁ = graphExpectedSegregatingSites θ s₂ ∧
      graphSingletonShare s₁ = graphSingletonShare s₂ := by
  constructor
  · rw [graphExpectedSegregatingSites_eq, graphExpectedSegregatingSites_eq, h]
  · unfold graphSingletonShare
    rw [h]

end Descent.Pangenome.GraphCoalescent
