/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Deficit

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The construction bracket reaches the coalescent, and it reaches it in one direction

`Descent.Pangenome.Construction` shows that the object a pangenome pipeline produces is not
determined by the alignments: closure and pruning bracket it in the refinement lattice, and
`support_mono` shows what that does to a node frequency spectrum.  This file carries the same
bracket into `Descent.Pangenome.GraphCoalescent`, where the corpus already prices what a
graph's compression costs in tree depth.

Those two developments were independent.  `Construction` knows about equivalence relations on
positions and nothing about coalescents; `Deficit` knows that a graph enters Kingman's
coalescent at `Linkage.width s` rather than at `n`, and treats that width as given.  Neither
can say what a change of BUILDER does to a coalescent estimate.  Put them together and it is
a theorem.

## The chain

`Coalescent.Interpolation.blocks_antitone` says coarsening loses blocks, `blocks_graphKer`
says the graph's block count is its width, and the transit deficit `2/w - 2/n` is decreasing
in `w`.  So:

**A coarser construction yields a smaller entrance point, a shallower reported tree, and a
strictly larger deficit** -- `width_antitone` and `transitDeficit_mono`.

This is not a caution about a possible confound.  It is the sign of one.  A pipeline that
forces more homology than another does not perturb the coalescent estimate in an unknown
direction; it moves `w` down, and `Deficit`'s `graphWatterson_lt` already says the reported
`θ_W` is `θ · a_{w-1} / a_{n-1}`, strictly below `θ` and further below the more it merges.
`graphWatterson_antitone` is that statement.

## Why this is the useful half of the bracket

`Construction.prune_le_closure` says every construction built from a sub-alignment set sits
at or below the closure of the full one.  Read through the chain here, the closure is the end
of the bracket with the SMALLEST `w`, hence the largest deficit and the most understated
`θ_W`.  A restriction-minimal build sits at the other end.  So the interval a study should be
reporting has a computable orientation: it is not that two builders disagree, it is that one
of them is systematically lower, and which one is known before any data is seen.

## What is not claimed

Nothing here says either endpoint is correct, and nothing identifies the truth within the
bracket.  The width of the interval is an empirical quantity about a particular panel and a
particular pair of pipelines; this file says only that the interval is oriented and that the
orientation is forced.

## Empirical status

None.  Every result is an order-theoretic consequence of definitions already in the corpus.

## Main results

- `width_antitone`: a coarser construction has a smaller graph width.
- `transitDeficit_mono`: **the headline.**  Coarsening only inflates the transit deficit.
- `graphWatterson_antitone`: and only depresses the reported `θ_W`.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### Coarsening loses width, and so costs depth -/

/-- **A coarser construction has a smaller graph.**  If the interface `t` merges everything
`s` merges and possibly more, then `t`'s graph has no more nodes than `s`'s.

This is `Coalescent.blocks_antitone` read through `blocks_graphKer`, and it is the step that turns a
statement about equivalence relations into a statement about the object a builder emits. -/
theorem width_antitone {n : ℕ} {s t : Fin n → Fin n} (h : graphKer s ≤ graphKer t) :
    Linkage.width t ≤ Linkage.width s := by
  have := Coalescent.blocks_antitone h
  rwa [blocks_graphKer, blocks_graphKer] at this

/-- **Coarsening only inflates the transit deficit.**

`transitDeficit` is `2/w - 2/n`, decreasing in `w`, and a coarser construction has a smaller
`w`.  So of two builders over one panel, the one that forces more homology reports a
shallower tree and pays a strictly larger deficit against the panel's own depth.

Assumes: `1 ≤ n`, and `1 ≤ Linkage.width t` -- the nondegeneracy under which K-G (5.7) has
its closed form.  The corresponding bound for `s` follows, since `t` is the coarser of the
two and `width_antitone` puts its width below. -/
theorem transitDeficit_mono {n : ℕ} {s t : Fin n → Fin n} (h : graphKer s ≤ graphKer t)
    (hn : 1 ≤ n) (hwt : 1 ≤ Linkage.width t) :
    transitDeficit s ≤ transitDeficit t := by
  have hts : Linkage.width t ≤ Linkage.width s := width_antitone h
  have hws : 1 ≤ Linkage.width s := le_trans hwt hts
  rw [transitDeficit_eq hn hws, transitDeficit_eq hn hwt]
  have h0 : (0 : ℝ) < (Linkage.width t : ℝ) := by exact_mod_cast hwt
  have h0s : (0 : ℝ) < (Linkage.width s : ℝ) := by exact_mod_cast hws
  have h1 : (Linkage.width t : ℝ) ≤ (Linkage.width s : ℝ) := by exact_mod_cast hts
  have hdiv : (2 : ℝ) / (Linkage.width s : ℝ) ≤ 2 / (Linkage.width t : ℝ) := by
    rw [div_le_div_iff₀ h0s h0]
    linarith
  linarith

/-- **and only depresses the reported `θ_W`.**

`Deficit.graphWatterson` is `θ · a_{w-1} / a_{n-1}`, the number a study reports when it reads
its segregating sites off the graph and its sample size off the panel.  The harmonic sum
`a_{w-1}` is increasing in `w`, so a coarser construction reports a smaller `θ_W`.

Together with `transitDeficit_mono` this fixes the sign of the whole confound: forcing more
homology understates diversity, and never overstates it.  The closure end of
`Construction`'s bracket is therefore the LOW end for `θ_W`, and it is known to be the low
end without measuring anything. -/
theorem graphWatterson_antitone {n : ℕ} (θ : Descent.Core.Theta) {s t : Fin n → Fin n}
    (h : graphKer s ≤ graphKer t) (hθ : 0 ≤ θ.value) :
    graphWatterson θ t ≤ graphWatterson θ s := by
  have hts : Linkage.width t ≤ Linkage.width s := width_antitone h
  rw [graphWatterson_eq, graphWatterson_eq]
  have hmono : Coalescent.harmonicSum (Linkage.width t - 1) ≤
      Coalescent.harmonicSum (Linkage.width s - 1) :=
    Coalescent.harmonicSum_strictMono.monotone (Nat.sub_le_sub_right hts 1)
  have hden : (0 : ℝ) ≤ Coalescent.harmonicSum (n - 1) := Coalescent.harmonicSum_nonneg _
  have key : Coalescent.harmonicSum (Linkage.width t - 1) / Coalescent.harmonicSum (n - 1)
      ≤ Coalescent.harmonicSum (Linkage.width s - 1) / Coalescent.harmonicSum (n - 1) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr hden)
  exact mul_le_mul_of_nonneg_left key hθ

/-! ### The categorical form

The two sign laws above were stated against a raw inequality of kernels because that is the
order-theoretic calculation they use.  An analysis, however, changes one graph presentation
into another.  The following corollaries expose exactly that interface: a morphism in the
presentation category is the evidence that the target construction is coarser, and no caller
has to unpack it back into an equivalence-relation inequality.
-/

/-- **A categorical coarsening can only increase the coalescent transit deficit.** -/
theorem transitDeficit_mono_of_presentationHom {n : ℕ} {s t : Fin n → Fin n}
    (h : Presentation.Hom (graphPresentation s) (graphPresentation t))
    (hn : 1 ≤ n) (hwt : 1 ≤ Linkage.width t) :
    transitDeficit s ≤ transitDeficit t :=
  transitDeficit_mono (Presentation.kernel_le_of_hom h) hn hwt

/-- **A categorical coarsening can only decrease graph-based Watterson estimation.** -/
theorem graphWatterson_antitone_of_presentationHom {n : ℕ} (θ : Descent.Core.Theta)
    {s t : Fin n → Fin n}
    (h : Presentation.Hom (graphPresentation s) (graphPresentation t))
    (hθ : 0 ≤ θ.value) :
    graphWatterson θ t ≤ graphWatterson θ s :=
  graphWatterson_antitone θ (Presentation.kernel_le_of_hom h) hθ

end Descent.Pangenome.GraphCoalescent
