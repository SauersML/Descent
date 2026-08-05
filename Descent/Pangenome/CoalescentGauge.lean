/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SegregatingSites
import Descent.Pangenome.GaugeInvariance

/-!
# The reference tree is a gauge, and the coalescent's estimators of `θ` are not invariant

`Descent.Coalescent.SegregatingSites` derives, from the rate ladder and nothing else, that
Watterson's `θ_W = S / a_{n-1}` and pairwise `π` both estimate `θ`, so their difference --
the numerator of Tajima's `D` -- has expectation zero:
`Coalescent.expectedTajimaNumerator_eq_zero`.  That theorem is about the MODEL.  It says
what the two estimators do to a sample the coalescent produced, and it mentions no
reference, because a coalescent tree has none.

`Descent.Pangenome.GaugeCounterexample` and `Descent.Pangenome.GaugeInvariance` are about
the DATA the estimators are actually fed.  A pangenome variant catalogue exists only
relative to a spanning tree of the pangenome graph, the cotree edges being the variants,
and `segregating_add_hidden` gives the exact dependence: `S_T + |hidden_T| = b₁`.  What
moves with the tree is how many sample-monomorphic edges the tree absorbs.

Neither half can state the consequence, and that is why this file exists.  The coalescent
half has `wattersonEstimator` and `expectedTajimaNumerator` but no notion of a reference;
the pangenome half has two reference trees over one dataset but computes its `θ_W` through
a hand-carried constant (`thetaW6`'s factor `4`, which is `6 / a₃`) rather than through the
estimator the null theorem is stated about.  Put them in one file and the consequence is a
theorem: **the number a study compares to the coalescent null is not a function of the
data.**

## What this file does NOT claim

It does not claim the coalescent null is wrong.  `expectedTajimaNumerator_eq_zero` is an
identity between two expectations and nothing here touches it.  The claim is about the
other side of the test -- that the observed statistic put opposite that zero carries a
choice the null does not know about, so a departure from zero is evidence against the
model only to the extent that the reference tree was not what produced it.

## Main results

- `wattersonEstimator_three`: `θ_W = (2/3) S` at `n = 3`, off `Coalescent.harmonicSum 2`.
- `thetaW6_eq_watterson`: `GaugeCounterexample.thetaW6` IS six times the coalescent's
  Watterson estimator at `n = 3`.  This is the identification the two developments needed,
  and it retires the hand-computed `a₃ = 3/2`.
- `wattersonEstimator_gauge_defect`: **the exact defect**, in general:
  `θ_W(T₁) - θ_W(T₂) = (|hidden_{T₂}| - |hidden_{T₁}|) / a_{n-1}` for trees of a common
  variant count.  Watterson's estimator is gauge-covariant, and the gauge field is the
  hidden-edge count.
- `tajimaNumerator_gauge_defect`: the same defect with the opposite sign in Tajima's
  numerator, because `π` at the sequence level is gauge-free and contributes nothing.
- `referenceTree_is_gauge_for_tajima`: **the headline.**  The null holds for every `θ` and
  every `n`; `[A]` and `[G]` are both spanning trees of one graph; and on one dataset the
  realized numerator is `0` under the first and strictly negative under the second.
- `wattersonEstimator_gauge_invariant_of_allPolymorphic`: the complementary positive
  result.  When every edge is polymorphic in the sample -- the full panel that defined the
  graph -- the defect vanishes and `θ_W` is gauge-invariant.
-/

namespace Descent.Pangenome

universe u

/-! ### Watterson's constant, instantiated rather than computed

The literature's `a_n = Σ_{i<n} i⁻¹` is this corpus's `Coalescent.harmonicSum (n - 1)`.
A sample of three therefore divides by `harmonicSum 2 = 3/2`, and the `3/2` that
`GaugeCounterexample` carries in prose is a value of the general sum. -/

/-- Watterson's estimator at `n = 3`: `θ_W = S / a₃ = (2/3) S`.  The constant comes from
`Coalescent.harmonicSum_two`, not from arithmetic performed here. -/
theorem wattersonEstimator_three (Shat : ℝ) :
    Coalescent.wattersonEstimator Shat 3 = 2 / 3 * Shat := by
  show Shat / Coalescent.harmonicSum 2 = 2 / 3 * Shat
  rw [Coalescent.harmonicSum_two]
  ring

/-- **The identification.**  `GaugeCounterexample.thetaW6` -- six times Watterson's
estimator on the triallelic witness, defined there as `4 * S` so that it stays in `ℕ` --
is six times `Coalescent.wattersonEstimator` at `n = 3`.  The factor `4` is `6 / a₃`, and
this theorem is what makes that a derivation rather than a remark. -/
theorem thetaW6_eq_watterson (t : RefTree) (sample : List Hap) :
    (thetaW6 t sample : ℝ) = 6 * Coalescent.wattersonEstimator (S t sample : ℝ) 3 := by
  unfold thetaW6
  rw [wattersonEstimator_three]
  push_cast
  ring

/-! ### The realized statistic

`Coalescent.expectedTajimaNumerator` is `E(π) - E(θ_W)`, a function of `θ` and the sample
size.  What a study computes is the same difference at the REALIZED values, and that object
takes a reference tree, because `S` does.  Naming it separately is the point: the null is
about the first, the gauge dependence is about the second, and conflating them is what let
the dependence go unstated. -/

/-- The realized numerator of Tajima's `D` on a pangenome sample under reference tree `t`:
sequence-level `π` minus Watterson's estimator at `n = 3`, both as reals.

Empirical status: DERIVED.  `π` is `GaugeCounterexample.piSeq6` unscaled and `θ_W` is
`Coalescent.wattersonEstimator`; this file introduces neither and subtracts them. -/
noncomputable def tajimaNumerator (t : RefTree) (sample : List Hap) : ℝ :=
  (piSeq6 sample : ℝ) / 6 - Coalescent.wattersonEstimator (S t sample : ℝ) 3

/-- The witness's integer-scaled numerator is six times the real one, so every value
`GaugeCounterexample` computes by `decide` is a statement about `tajimaNumerator`. -/
theorem tajimaNum6_eq_six_mul (t : RefTree) (sample : List Hap) :
    (tajimaNum6 t sample : ℝ) = 6 * tajimaNumerator t sample := by
  have hW := thetaW6_eq_watterson t sample
  unfold tajimaNum6 tajimaNumerator
  push_cast
  linarith

/-! ### The exact defect, in general -/

/-- **Watterson's estimator is gauge-covariant, and the gauge field is the hidden-edge
count.**  For two reference trees of a common variant count -- which for spanning trees of
a connected graph is automatic -- the two estimates differ by exactly the difference in
how many sample-monomorphic edges each tree absorbed, divided by the harmonic normaliser.

This is `GaugeInvariance.segregating_add_hidden` pushed through
`Coalescent.wattersonEstimator`.  No positivity hypothesis on `a_{n-1}` is needed: at
`n ≤ 1` both sides are zero for the same reason. -/
theorem wattersonEstimator_gauge_defect {E : Type u} (edges : List E) (T₁ T₂ : Gauge.Tree E)
    (sample : List (Gauge.Walk E)) (n : ℕ)
    (hsize : Gauge.variantCount edges T₁ = Gauge.variantCount edges T₂) :
    Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₁ sample : ℝ) n
        - Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₂ sample : ℝ) n
      = ((Gauge.hiddenCount edges T₂ sample : ℝ) - (Gauge.hiddenCount edges T₁ sample : ℝ))
          / Coalescent.harmonicSum (n - 1) := by
  have hnat : Gauge.segregatingCount edges T₁ sample + Gauge.hiddenCount edges T₁ sample
      = Gauge.segregatingCount edges T₂ sample + Gauge.hiddenCount edges T₂ sample := by
    rw [Gauge.segregating_add_hidden, Gauge.segregating_add_hidden, hsize]
  have hreal : ((Gauge.segregatingCount edges T₁ sample : ℝ)
        + (Gauge.hiddenCount edges T₁ sample : ℝ))
      = (Gauge.segregatingCount edges T₂ sample : ℝ)
        + (Gauge.hiddenCount edges T₂ sample : ℝ) := by
    exact_mod_cast hnat
  have hkey : (Gauge.segregatingCount edges T₁ sample : ℝ)
        - (Gauge.segregatingCount edges T₂ sample : ℝ)
      = (Gauge.hiddenCount edges T₂ sample : ℝ)
        - (Gauge.hiddenCount edges T₁ sample : ℝ) := by
    linarith
  unfold Coalescent.wattersonEstimator
  rw [div_sub_div_same, hkey]

/-- **The same defect, with the sign the test sees.**  Sequence-level `π` takes no
reference tree, so it cancels out of the difference and the whole gauge dependence of
Tajima's numerator is Watterson's.  A catalogue built against a tree that absorbs more of
the sample's monomorphic edges reports a LARGER `S`, hence a larger `θ_W`, hence a more
negative numerator -- the direction a neutrality test reads as a selective sweep. -/
theorem tajimaNumerator_gauge_defect {E : Type u} (edges : List E) (T₁ T₂ : Gauge.Tree E)
    (sample : List (Gauge.Walk E)) (n : ℕ) (piHat : ℝ)
    (hsize : Gauge.variantCount edges T₁ = Gauge.variantCount edges T₂) :
    (piHat - Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₁ sample : ℝ) n)
        - (piHat
            - Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₂ sample : ℝ) n)
      = ((Gauge.hiddenCount edges T₁ sample : ℝ) - (Gauge.hiddenCount edges T₂ sample : ℝ))
          / Coalescent.harmonicSum (n - 1) := by
  have h := wattersonEstimator_gauge_defect edges T₁ T₂ sample n hsize
  have hflip : ((Gauge.hiddenCount edges T₁ sample : ℝ)
        - (Gauge.hiddenCount edges T₂ sample : ℝ)) / Coalescent.harmonicSum (n - 1)
      = -((((Gauge.hiddenCount edges T₂ sample : ℝ)
        - (Gauge.hiddenCount edges T₁ sample : ℝ))) / Coalescent.harmonicSum (n - 1)) := by
    ring
  rw [hflip, ← h]
  ring

/-- **The complementary positive result.**  When every edge is polymorphic in the sample --
the defining situation for the full panel the graph was built from -- the hidden count is
zero under every tree, the defect vanishes, and Watterson's estimator is gauge-invariant.
The dependence is a SUBSAMPLING phenomenon, which is exactly the regime every
per-population statistic is computed in. -/
theorem wattersonEstimator_gauge_invariant_of_allPolymorphic {E : Type u} (edges : List E)
    (T₁ T₂ : Gauge.Tree E) (sample : List (Gauge.Walk E)) (n : ℕ)
    (hpoly : ∀ e, e ∈ edges → Gauge.polymorphic sample e = true)
    (hsize : Gauge.variantCount edges T₁ = Gauge.variantCount edges T₂) :
    Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₁ sample : ℝ) n
      = Coalescent.wattersonEstimator (Gauge.segregatingCount edges T₂ sample : ℝ) n := by
  rw [Gauge.segregatingCount_gauge_invariant edges T₁ T₂ sample hpoly hsize]

/-! ### The witness, in the coalescent's own vocabulary -/

/-- Under the tree keeping the majority allele the realized numerator is exactly zero:
`π = 2/3` and `θ_W = (2/3) · 1 = 2/3`.  This is the value the coalescent null predicts. -/
theorem tajimaNumerator_subsample_A : tajimaNumerator Allele.A subsample = 0 := by
  have hS : S Allele.A subsample = 1 := subsample_S_not_invariant.1
  unfold tajimaNumerator
  rw [wattersonEstimator_three, subsample_piSeq_value, hS]
  norm_num

/-- Under the tree keeping the allele no sampled walk carries, the SAME data give
`θ_W = (2/3) · 2 = 4/3` against the same `π = 2/3`, and the numerator is `-2/3`. -/
theorem tajimaNumerator_subsample_G : tajimaNumerator Allele.G subsample = -(2 / 3) := by
  have hS : S Allele.G subsample = 2 := subsample_S_not_invariant.2
  unfold tajimaNumerator
  rw [wattersonEstimator_three, subsample_piSeq_value, hS]
  norm_num

/-- Watterson's estimator itself, not merely the witness's scaled stand-in, takes two
values on one dataset. -/
theorem wattersonEstimator_not_gauge_invariant :
    Coalescent.wattersonEstimator (S Allele.A subsample : ℝ) 3
      ≠ Coalescent.wattersonEstimator (S Allele.G subsample : ℝ) 3 := by
  have hA : S Allele.A subsample = 1 := subsample_S_not_invariant.1
  have hG : S Allele.G subsample = 2 := subsample_S_not_invariant.2
  simp only [wattersonEstimator_three, hA, hG]
  norm_num

/-- **THE HEADLINE.  The reference tree is a gauge, and Tajima's `D` is not invariant
under it.**

Read the four clauses in order.

(i) The coalescent null, unconditionally: for every `θ` and every sample size at least
two, the two estimators of `θ` have the same expectation, so the numerator of Tajima's `D`
has expectation zero.  This is `Coalescent.expectedTajimaNumerator_eq_zero`, untouched.

(ii) `[A]` and `[G]` are both spanning trees of the same two-node graph.  Nothing about
the population, the sample, or the sequences differs between them; they are two names for
the same variation.

(iii) On one dataset the realized numerator is `0` under the first and strictly negative
under the second.  A neutrality test run on this sample reports "consistent with the null"
or "excess of rare variants" according to which tree the catalogue was written against.

(iv) And the gap is not noise to be averaged away: it is `θ_W(G) - θ_W(A)`, the defect
`wattersonEstimator_gauge_defect` computes exactly, because sequence-level `π` cancels.

The force of the result is that (i) cannot see (ii).  `expectedTajimaNumerator` takes `θ`
and `n`; there is no argument of it for the reference tree, so no amount of care with the
null constrains the choice.  The test compares a model quantity that has no gauge against
a data quantity that has one. -/
theorem referenceTree_is_gauge_for_tajima :
    (∀ (θ : ℝ) (n : ℕ), 2 ≤ n → Coalescent.expectedTajimaNumerator θ n = 0)
      ∧ IsSpanningTree [Allele.A] ∧ IsSpanningTree [Allele.G]
      ∧ tajimaNumerator Allele.A subsample = 0
      ∧ tajimaNumerator Allele.G subsample < 0
      ∧ (∀ t₁ t₂ : RefTree, tajimaNumerator t₁ subsample - tajimaNumerator t₂ subsample
          = Coalescent.wattersonEstimator (S t₂ subsample : ℝ) 3
              - Coalescent.wattersonEstimator (S t₁ subsample : ℝ) 3) := by
  refine ⟨fun θ n hn ↦ Coalescent.expectedTajimaNumerator_eq_zero hn θ,
    treeA_spanning, treeG_spanning, tajimaNumerator_subsample_A, ?_, ?_⟩
  · rw [tajimaNumerator_subsample_G]
    norm_num
  · intro t₁ t₂
    unfold tajimaNumerator
    ring

/-- **And the panel case, for contrast.**  Over the full panel every edge is polymorphic,
so `wattersonEstimator_gauge_invariant_of_allPolymorphic` applies and Watterson's estimator
is the same under every reference tree of the Betti-number size.  The gauge dependence
above is not a defect of the graph; it is what subsampling a graph-defined catalogue does,
and every per-population statistic is a subsample. -/
theorem wattersonEstimator_panel_gauge_invariant (T₁ T₂ : Gauge.Tree Allele) (n : ℕ)
    (hsize : Gauge.variantCount allEdges T₁ = Gauge.variantCount allEdges T₂) :
    Coalescent.wattersonEstimator
        (Gauge.segregatingCount allEdges T₁ Gauge.samplePanel : ℝ) n
      = Coalescent.wattersonEstimator
        (Gauge.segregatingCount allEdges T₂ Gauge.samplePanel : ℝ) n :=
  wattersonEstimator_gauge_invariant_of_allPolymorphic allEdges T₁ T₂ Gauge.samplePanel n
    Gauge.panel_allPolymorphic hsize

end Descent.Pangenome
