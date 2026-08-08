/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SegregatingSites
import Descent.Pangenome.PanelGraph

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The pangenome growth curve is a harmonic sum, and openness is the neutral null

`Descent.Pangenome.PanelGraph.nodeCount_eq_add_segregatingCount` says a positional graph
is its reference plus its segregating loci -- `pan = reference + S`, exactly, panel by
panel.  `Descent.Coalescent.SegregatingSites` says what `S` does in expectation under the
neutral coalescent: `E(S) = θ a_{m-1}`.  This file is their composition, and the
composition settles the shape of the curve every pangenome project plots -- the
"gene discovery" or "pan-genome growth" curve, pan size against panel size -- before any
data are collected.

## What the composition yields

* **The curve** (`expectedPanSize_eq`): `base + θ a_{m-1}`.  A saturating-LOOKING curve
  with no saturation in it: harmonic, not asymptotic to any ceiling.
* **The increment** (`expectedPanSize_step`): the `(m+1)`-th genome contributes `θ / m`
  expected new nodes -- `Descent.Core.ratio` at the corpus's own kernel.  This is the
  discovery rate a sequencing project reads off its last release.
* **Flattening forever, closing never** (`expectedPanSize_step_antitone`,
  `expectedPanSize_step_pos`): increments fall monotonically and are positive at every
  panel size.  A curve that flattens is therefore not evidence of a closed pangenome, and
  a fitted "openness" exponent adds nothing the null did not already predict
  qualitatively.
* **Openness is the null** (`expectedPanSize_unbounded`): the expected pan size exceeds
  every bound, under the dullest model the corpus contains -- neutral, panmictic, constant
  size, no gene gain machinery at all.  An OPEN pangenome is what boredom predicts, so
  observing openness discriminates nothing.  `Descent.Pangenome.CoreAccessory` shows the
  growth exponent is not even an estimand (it fails Kingman's sampling-consistency razor);
  this file adds that its qualitative reading carries no information either.
* **The curve is Watterson in disguise** (`wattersonEstimator_panExcess`): the excess of
  the curve over its reference, fed to Watterson's estimator, returns `θ` exactly.  A
  pangenome growth curve is not a new statistic about a gene pool; it is `S` with a
  constant offset, and everything the corpus proves about `S` -- including the width
  truncation of `Descent.Pangenome.GraphSpectrum`, which caps the same curve at
  `θ a_{w-1}` when read off a graph of width `w` -- applies to it verbatim.
* **The pair case saturates at the saturation kernel**
  (`complement_fstEquilibrium_eq_saturation`): at mutation-drift equilibrium the
  probability that a pair of lineages is NOT identical by descent is
  `1 - 1/(1+θ) = θ/(1+θ)` -- `Descent.Core.saturation`, the same coordinate the corpus
  root identifies across three other chapters.  By
  `PanelGraph.segregatesAt_pair_iff_het` that probability is the equilibrium bubble
  density of the two-haplotype graph, so the pangenome's bubble density enters the same
  one-parameter family as `F_ST` and heterozygosity, on the complementary branch.

## What is not claimed

No claim that any real panel is neutral or panmictic, and no claim about the magnitude of
any real curve.  The direction of use is the corpus's usual one: the null produces the
qualitative phenomena -- growth, flattening, openness -- so those phenomena cannot be
cited as evidence against it.  `base` is a modelling input naming the reference's node
count, not a derived quantity.

## Empirical status

MIXED, inherited: the tree factor in `E(S)` is derived from the rate ladder, the Poisson
mutation mechanism and the infinite-sites convention are assumed, and both verdicts are
recorded at `Coalescent.expectedSegregatingSites`.  Everything added here is algebra over
that quantity.

## Main results

- `expectedPanSize_eq`: **the growth curve is `base + θ a_{m-1}`.**
- `expectedPanSize_step`: **the `(m+1)`-th genome is worth `θ/m` new nodes.**
- `expectedPanSize_step_antitone`, `expectedPanSize_step_pos`: flattens forever, closes
  never.
- `expectedPanSize_unbounded`: **an open pangenome is the neutral prediction.**
- `wattersonEstimator_panExcess`: the curve's excess IS Watterson's estimator.
- `complement_fstEquilibrium_eq_saturation`: **equilibrium pair bubble density is
  `Core.saturation θ`** -- one minus the mutation-drift `F_ST`.
-/

namespace Descent.Pangenome.Growth

/-- **The expected pan size**: the size law `PanelGraph.nodeCount_eq_add_segregatingCount`
taken in expectation under the neutral coalescent.  A reference of `base` nodes plus the
expected segregating-locus count of a panel of `mSample` haplotypes.

Empirical status: MIXED, inherited from `Coalescent.expectedSegregatingSites` -- the tree
factor is derived, the Poisson-mutation and infinite-sites premises are assumed, and the
verdicts are recorded there.  `base` is a modelling input, not a derived quantity. -/
noncomputable def expectedPanSize (θ : Descent.Core.Theta) (base : ℝ) (mSample : ℕ) : ℝ :=
  base + Coalescent.expectedSegregatingSites θ mSample

/-- **The growth curve is a harmonic sum**: `base + θ a_{m-1}`.  Heaps-like flattening
with no ceiling, from Watterson's formula and nothing else. -/
theorem expectedPanSize_eq (θ : Descent.Core.Theta) (base : ℝ) (mSample : ℕ) :
    expectedPanSize θ base mSample
      = base + θ.value * Coalescent.harmonicSum (mSample - 1) := by
  unfold expectedPanSize
  rw [Coalescent.expectedSegregatingSites_eq]

/-- A panel of one discovers nothing beyond its reference: the curve starts at `base`. -/
theorem expectedPanSize_one (θ : Descent.Core.Theta) (base : ℝ) :
    expectedPanSize θ base 1 = base := by
  unfold expectedPanSize
  rw [Coalescent.expectedSegregatingSites_one, add_zero]

/-- **The discovery increment: the `(m+1)`-th genome is worth `θ/m` new nodes.**  The
harmonic step of the curve, written through the corpus's ratio kernel so the rate has one
spelling.  This is the number a sequencing consortium's "new sequence per added genome"
figure estimates, and it depends on the panel only through its size. -/
theorem expectedPanSize_step (θ : Descent.Core.Theta) (base : ℝ) {mSample : ℕ}
    (hm : 0 < mSample) :
    expectedPanSize θ base (mSample + 1) - expectedPanSize θ base mSample
      = Descent.Core.ratio θ.value mSample := by
  obtain ⟨k, rfl⟩ : ∃ k, mSample = k + 1 :=
    ⟨mSample - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  rw [expectedPanSize_eq, expectedPanSize_eq, Nat.add_sub_cancel, Nat.add_sub_cancel,
    Coalescent.harmonicSum_succ]
  unfold Descent.Core.ratio
  push_cast
  ring

/-- **The curve flattens forever.**  The increment at a larger panel never exceeds the
increment at a smaller one, so the flattening every release note reports is arithmetic,
not biology: it is what the null does, at every panel size, for every `θ`. -/
theorem expectedPanSize_step_antitone (θ : Descent.Core.Theta) (base : ℝ) {m₁ m₂ : ℕ}
    (hθ : 0 ≤ θ.value) (h1 : 0 < m₁) (h12 : m₁ ≤ m₂) :
    expectedPanSize θ base (m₂ + 1) - expectedPanSize θ base m₂
      ≤ expectedPanSize θ base (m₁ + 1) - expectedPanSize θ base m₁ := by
  rw [expectedPanSize_step θ base h1, expectedPanSize_step θ base (h1.trans_le h12)]
  unfold Descent.Core.ratio
  have h1' : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast h1
  have h12' : ((m₁ : ℕ) : ℝ) ≤ ((m₂ : ℕ) : ℝ) := by exact_mod_cast h12
  exact div_le_div_of_nonneg_left hθ h1' h12'

/-- **The curve closes never.**  At every panel size the increment is strictly positive
for a positive mutation rate, so no finite panel exhausts the pangenome and "the curve has
flattened" is not "the pangenome is closed" -- the two are compatible at every `m`. -/
theorem expectedPanSize_step_pos (θ : Descent.Core.Theta) (base : ℝ) {mSample : ℕ}
    (hθ : 0 < θ.value) (hm : 0 < mSample) :
    0 < expectedPanSize θ base (mSample + 1) - expectedPanSize θ base mSample := by
  rw [expectedPanSize_step θ base hm]
  unfold Descent.Core.ratio
  exact div_pos hθ (by exact_mod_cast hm)

/-- **An open pangenome is the neutral prediction.**  For any positive mutation rate the
expected pan size exceeds every bound as the panel grows -- under a model with no gene
gain, no adaptation, and no population structure whatever.  Observing that a pangenome is
open therefore discriminates nothing: the dullest model in the corpus predicts it.  What
COULD carry information is a departure from the harmonic SHAPE, and that comparison
requires stating the null this theorem is. -/
theorem expectedPanSize_unbounded {θ : Descent.Core.Theta} (hθ : 0 < θ.value)
    (base B : ℝ) : ∃ mSample : ℕ, B < expectedPanSize θ base mSample := by
  obtain ⟨mSample, hm⟩ :=
    ((Coalescent.tendsto_expectedSegregatingSites_atTop hθ).eventually_gt_atTop
      (B - base)).exists
  exact ⟨mSample + 1, by unfold expectedPanSize; linarith⟩

/-- **The growth curve is Watterson's estimator in disguise.**  Subtract the reference and
divide by the harmonic normaliser and the curve returns `θ` exactly -- so a pangenome
growth curve is not a new instrument for gene-pool richness, it is `S` with a constant
offset, unbiased for the same reason and biased by everything that biases `S`, including
the graph-width truncation `Descent.Pangenome.GraphSpectrum` prices. -/
theorem wattersonEstimator_panExcess {mSample : ℕ} (hm : 2 ≤ mSample)
    (θ : Descent.Core.Theta) (base : ℝ) :
    Coalescent.wattersonEstimator (expectedPanSize θ base mSample - base) mSample
      = θ.value := by
  have h : expectedPanSize θ base mSample - base
      = Coalescent.expectedSegregatingSites θ mSample := by
    unfold expectedPanSize
    ring
  rw [h, Coalescent.wattersonEstimator_unbiased hm]

/-- **The equilibrium pair bubble density is the saturation kernel.**  At mutation-drift
equilibrium the probability that a pair of lineages escapes identity by descent is one
minus the equilibrium `F_ST`, and that complement is `θ/(1+θ)` -- `Descent.Core.saturation`
at the scaled mutation rate.  By `PanelGraph.segregatesAt_pair_iff_het` the escaping pairs
are exactly the loci where a two-haplotype positional graph carries a bubble, so the
pangenome's equilibrium bubble density lands on the same one-parameter saturation family
the corpus root already identifies in three other chapters -- on the branch complementary
to `F_ST`'s.  One curve, four readings.

Assumes: `0 ≤ Descent.Core.scaledMutationRate Ne μ`, which every physical rate satisfies;
without it the denominator `1 + θ` could vanish and both sides carry junk values. -/
theorem complement_fstEquilibrium_eq_saturation (Ne μ nDemes : ℝ)
    (hθ : 0 ≤ Descent.Core.scaledMutationRate Ne μ) :
    Descent.Core.complement
        (Descent.Core.fstIslandEquilibrium (Descent.Core.BigM.ofRate Ne 0)
          (Descent.Core.Theta.ofRate Ne μ) nDemes)
      = Descent.Core.saturation (Descent.Core.scaledMutationRate Ne μ) := by
  rw [Descent.Core.fstIslandEquilibrium_no_migration]
  unfold Descent.Core.complement Descent.Core.saturation
  have h1 : (0 : ℝ) < 1 + Descent.Core.scaledMutationRate Ne μ := by linarith
  field_simp
  ring

end Descent.Pangenome.Growth
