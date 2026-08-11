/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.ARoneFrontier

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.GeneticFrontier`

Part of the split of `Descent/Portability/MetricSpecificPortability.lean`, which was 3,946 lines.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

/-!
## The frontier in genotype terms

The section above is parameterised by an abstract band decay, and this one keeps
it that way on purpose.  Two substitutions are available and neither is an
identity.  `LDDecayTheory.ldRetentionPerGen r Ne` is a per-GENERATION retention:
feeding it in as the decay makes linkage disequilibrium fall off with physical
separation at the rate it falls off with time.  The stationary law relating
separation to LD is Sved's, carried here as
`LDDecayTheory.ohtaKimuraSigmaDSq`.  Choosing between them is a modelling step
and belongs at the call site, where it can be named.

The `κ` of the band quantities is likewise a fraction of DIRECTIONS — a
contiguous low-frequency band of the AR(1) symbol — and not the fraction of
MARKERS a clumping tool reports.  Those are different objects: at one `(decay,
κ)` a uniformly thinned panel, a random panel and a contiguous panel retain
different shares of the whitened detection weight, so the retained weight of a
pruned panel is not a function of `(decay, κ)` at all.  `LDPanelRetention` and
`ldPanelRetentionFraction` therefore stay marker-side bookkeeping and are not
fed to the band bodies.

What this buys: `pruning_loses_detection_iff_whiteningGain_exceeds_one` makes
the connection to the corpus's existing detection quantity an implication rather
than a remark — the whitening gain `ldWhiteningGain` exceeds its no-linkage
value exactly when pruning strictly loses detection weight, because the
inverse-kernel trace that the gain measures is built out of the very directions
pruning discards.  And `clumping_minimizes_detection_on_ld_kernel` states the
prohibition over a genetic pruning rule on the LD kernel itself.

Scope is unchanged and is not weakened by the instantiation: these are results
about linear, projection-type reductions of the LD kernel.  Extension to
arbitrary measurable reductions would need a joint data-processing inequality
for the detection/reconstruction pair, which does not exist.
-/

section GeneticFrontier

/-- A valid marker-panel reduction has a nonempty original panel and cannot
retain more markers than the panel contains. `retainedMarkers` of `totalMarkers`
survive; this is the rank budget in the units a clumping tool reports. Carrying
the validity facts as data keeps division by zero and fractions above one out of
the LD-frontier interface.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a TYPE, not a quantity. It bundles two
validity facts, `retainedMarkers ≤ totalMarkers` and `0 < totalMarkers`, so that division by
zero and fractions above one cannot enter the LD-frontier interface. A structure carrying
facts about its own fields asserts nothing about any population, and no simulation could
return a panel that contradicts it. The empirical content is in the bodies that CONSUME a
retention -- what a real pruning rule retains, and what that costs a score. -/
structure LDPanelRetention where
  retainedMarkers : ℕ
  totalMarkers : ℕ
  retained_le_total : retainedMarkers ≤ totalMarkers
  totalMarkers_pos : 0 < totalMarkers

/-- **The panel class is inhabited**, so the statements taking an
`LDPanelRetention` are about something rather than about an empty
class. One marker of two retained is chosen deliberately over the degenerate
fills: it satisfies `0 < retainedMarkers` and `retainedMarkers < totalMarkers`
as well, which are the side conditions those theorems carry, so the witness
exercises the interval case rather than an endpoint where the fraction is `0`
or `1`. -/
def LDPanelRetention.halfRetained : LDPanelRetention where
  retainedMarkers := 1
  totalMarkers := 2
  retained_le_total := by norm_num
  totalMarkers_pos := by norm_num

theorem LDPanelRetention.nonempty : Nonempty LDPanelRetention :=
  ⟨LDPanelRetention.halfRetained⟩

/-- Fraction of a panel's markers that survive pruning.

    Empirical status: NOT AN EMPIRICAL CLAIM. Retained over total is the definition of a
    retained FRACTION; the two counts are fields of the structure, so the quotient is fixed
    once the panel is. What pruning actually retains on a real panel is empirical, but that
    is a claim about `retainedMarkers`, not about this division. -/
noncomputable def ldPanelRetentionFraction (panel : LDPanelRetention) : ℝ :=
  (panel.retainedMarkers : ℝ) / (panel.totalMarkers : ℝ)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ldPanelRetentionFraction_at_zero_denominator_is_junk (panel : LDPanelRetention)
    (hzero : (panel.totalMarkers : ℝ) = 0) :
    ldPanelRetentionFraction panel = 0 := by
  unfold ldPanelRetentionFraction
  rw [hzero, div_zero]

theorem ldPanelRetentionFraction_mem (panel : LDPanelRetention)
    (h0 : 0 < panel.retainedMarkers) (h1 : panel.retainedMarkers < panel.totalMarkers) :
    0 < ldPanelRetentionFraction panel ∧ ldPanelRetentionFraction panel < 1 := by
  have hr : (0 : ℝ) < (panel.retainedMarkers : ℝ) := by exact_mod_cast h0
  have ht : (0 : ℝ) < (panel.totalMarkers : ℝ) := by
    exact_mod_cast panel.totalMarkers_pos
  have hlt : (panel.retainedMarkers : ℝ) < (panel.totalMarkers : ℝ) := by
    exact_mod_cast h1
  unfold ldPanelRetentionFraction
  exact ⟨div_pos hr ht, (div_lt_one ht).mpr hlt⟩

/-- The Ohta–Kimura retention lies in `[0, 1)` for admissible parameters, so it
is an admissible AR(1) decay.  This is the compatibility check that lets the two
corpus modules be chained at all. -/
theorem ldRetentionPerGen_abs_lt_one {recomb Ne : ℝ}
    (hr0 : 0 ≤ recomb) (hr1 : recomb ≤ 1) (hNe : 1 < Ne) :
    |PopGen.ldRetentionPerGen recomb Ne| < 1 := by
  have hnn : 0 ≤ PopGen.ldRetentionPerGen recomb Ne :=
    PopGen.ld_retention_nonneg recomb Ne hr1 (le_of_lt hNe)
  have hlt : PopGen.ldRetentionPerGen recomb Ne < 1 := by
    have hfac : 0 < 1 - 1 / (2 * Ne) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    have hfac1 : 1 - 1 / (2 * Ne) < 1 := by
      have hpos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
      linarith
    unfold PopGen.ldRetentionPerGen
    nlinarith [mul_nonneg hr0 (le_of_lt hfac), hfac1]
  rw [abs_lt]
  exact ⟨by linarith, hlt⟩

/-- Less recombination, more retention.  Extracted here in the form the frontier
needs; it is the step the corpus already performs inside
`ImitationRigidity.ldWhiteningGain_of_ldRetention_antitone`. -/
theorem ldRetentionPerGen_strictAnti_recomb {r₁ r₂ Ne : ℝ}
    (hNe : 1 < Ne) (hlt : r₁ < r₂) :
    PopGen.ldRetentionPerGen r₂ Ne < PopGen.ldRetentionPerGen r₁ Ne := by
  have hfac : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  unfold PopGen.ldRetentionPerGen
  nlinarith [hlt, hfac]

/-- **Tight-linkage floor on the detection share**, `κ - sin(πκ)/π`.  It carries no decay
parameter because it is the value the frontier saturates to as the band decay approaches one,
and `ldTightLinkageFloor_le_ldBandDetectionShare` shows that curve bounds the band detection
share at every decay.

Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk4.py`,
    `test_tight_linkage_share`). It claims the `rho -> 1` limit of
    `ldBandDetectionShare`, and the limit is taken ON THE INTEGRAL rather than
    on the closed form: quadrature of the reciprocal symbol at `rho = 0.999999`
    agrees to 0.00 sems at every `kappa` in {0.1, 0.3, 0.6, 0.9}, predictions
    0.00164, 0.04248, 0.29727 and 0.80164.

    Power: the prediction spans 0.00164 to 0.80164, a factor of 490. -/
noncomputable def ldTightLinkageDetectionShare (panel : LDPanelRetention) : ℝ :=
  ldPanelRetentionFraction panel -
    Real.sin (Real.pi * ldPanelRetentionFraction panel) / Real.pi

/-- The whitening gain exceeds its no-linkage value exactly when there is
linkage to exploit. -/
theorem ldWhiteningGain_one_lt_iff {decay : ℝ}
    (hd0 : 0 ≤ decay) (hd1 : decay < 1) :
    1 < Blindness.ldWhiteningGain decay ↔ 0 < decay := by
  have hden : (0 : ℝ) < 1 - decay ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - decay)
      (by linarith : (0:ℝ) < 1 + decay)]
  unfold Blindness.ldWhiteningGain
  rw [one_lt_div hden]
  constructor
  · intro h
    rcases eq_or_lt_of_le hd0 with heq | hpos
    · exfalso
      rw [← heq] at h
      norm_num at h
    · exact hpos
  · intro h
    nlinarith [mul_pos h h]

/-- The pruning deficit is strictly positive exactly when there is linkage. -/
theorem ldPruningDetectionDeficit_pos_iff {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    0 < ldPruningDetectionDeficit decay kappa ↔ 0 < decay := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  unfold ldPruningDetectionDeficit
  constructor
  · intro h
    rcases eq_or_lt_of_le hd0 with heq | hpos
    · exfalso
      rw [← heq] at h
      norm_num at h
    · exact hpos
  · intro h
    exact div_pos (mul_pos (by linarith) hsin) hden

/-- **The corpus's detection quantity is what clumping destroys.**

`ImitationRigidity.ldWhiteningGain` is the per-variant limit of `tr K⁻¹`, the
quantity every whitened detection threshold in this corpus is stated in.  It
exceeds its no-linkage value `1` precisely when the LD kernel has spectral
spread — and that is precisely the condition under which pruning to a band of
directions loses detection weight strictly faster than it loses directions.

This is the implication the inverse-ordering result explains: the inverse-kernel
trace is built out of the small-eigenvalue directions, clumping keeps the large
ones, so the gain being larger than one and the pruning deficit being positive
are the same fact seen from two sides.  Both sides are functions of the band
decay, and `kappa` is a fraction of DIRECTIONS of the AR(1) symbol; the fraction
of MARKERS a clumping tool retains is a different object and is not it. -/
theorem pruning_loses_detection_iff_whiteningGain_exceeds_one
    {decay kappa : ℝ}
    (hd0 : 0 ≤ decay) (hd1 : decay < 1)
    (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    1 < Blindness.ldWhiteningGain decay ↔
      0 < ldPruningDetectionDeficit decay kappa := by
  rw [ldWhiteningGain_one_lt_iff hd0 hd1,
    ldPruningDetectionDeficit_pos_iff hd0 hk0 hk1]

/-- The deficit is strictly increasing in the AR(1) decay. -/
theorem ldPruningDetectionDeficit_strictMono {p₁ p₂ kappa : ℝ}
    (h₁ : 0 ≤ p₁) (h₂ : p₂ < 1) (hlt : p₁ < p₂)
    (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    ldPruningDetectionDeficit p₁ kappa < ldPruningDetectionDeficit p₂ kappa := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * kappa) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact mul_pos hpi hk0
    · nlinarith [mul_pos hpi (by linarith : (0:ℝ) < 1 - kappa)]
  have hd1 : 0 < Real.pi * (1 + p₁ ^ 2) := by positivity
  have hd2 : 0 < Real.pi * (1 + p₂ ^ 2) := by positivity
  have hprod : (0 : ℝ) < 1 - p₁ * p₂ := by
    nlinarith [mul_nonneg h₁ (by linarith : (0:ℝ) ≤ 1 - p₂)]
  unfold ldPruningDetectionDeficit
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos (mul_pos (mul_pos hsin hpi) (sub_pos.mpr hlt)) hprod]

/-- The deficit never exceeds `sin(πκ)/π`, at any decay. -/
theorem ldPruningDetectionDeficit_le_sin_div_pi {decay kappa : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    ldPruningDetectionDeficit decay kappa ≤
      Real.sin (Real.pi * kappa) / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * (1 + decay ^ 2) := by positivity
  have hsin : 0 ≤ Real.sin (Real.pi * kappa) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
    · exact mul_nonneg (le_of_lt hpi) hk0
    · nlinarith [mul_nonneg (le_of_lt hpi) (by linarith : (0:ℝ) ≤ 1 - kappa)]
  unfold ldPruningDetectionDeficit
  rw [div_le_div_iff₀ hden hpi]
  nlinarith [mul_nonneg (mul_nonneg hsin (le_of_lt hpi)) (sq_nonneg (1 - decay))]

/-- **The tight-linkage floor.**  At every band decay, keeping the low-frequency band holding a
fraction `κ` of the kernel's directions retains at least `κ - sin(πκ)/π` of the detection weight,
and no more than `κ`.  The lower end is approached as linkage tightens, so on a tightly linked
kernel the detection share is pinned near a curve carrying no free parameters at all — which is
what makes the prediction cheap to test. -/
theorem ldTightLinkageFloor_le_ldBandDetectionShare {decay kappa : ℝ}
    (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    kappa - Real.sin (Real.pi * kappa) / Real.pi ≤ ldBandDetectionShare decay kappa := by
  have hbound := ldPruningDetectionDeficit_le_sin_div_pi
    (decay := decay) (kappa := kappa) (le_of_lt hk0) (le_of_lt hk1)
  unfold ldBandDetectionShare
  unfold ldPruningDetectionDeficit at hbound
  linarith

/-- **The pruning prohibition on the LD kernel itself.**

`S` is the set of retained directions of a clumping pass: the low-frequency band
of the LD kernel, which by `ldKernelSymbol_mono_in_cos` is exactly a top-`|S|`
set by eigenvalue.  The conclusion is that among *all* relaxed rank-`|S|`
reductions of the same kernel — every linear dimension reduction with the same
budget, fractional ones included — the clumped panel has the minimum detection
efficiency.

The kernel is the AR(1) LD band at decay `decay`, indexed by marker separation. What that decay
is in terms of a recombination rate and an effective size is a modelling step, and it belongs at
the call site where it can be named: `PopGen.ldRetentionPerGen` is a per-GENERATION retention and
supplying it here would make linkage disequilibrium decay with physical distance at the rate it
decays with time. The stationary law relating separation to LD is Sved's,
`LDDecayTheory.ohtaKimuraSigmaDSq`.

Scope: relaxed projection-type reductions.  This is not a statement about
arbitrary measurable summaries of the genotypes, and no joint data-processing
inequality is available that would make it one. -/
theorem clumping_minimizes_detection_on_ld_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (decay cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hd0 : 0 ≤ decay) (hdabs : |decay| < 1)
    (hM : Spectral.IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    Spectral.detectionEfficiency
        (fun i ↦ Blindness.ldKernelSymbol decay (angle i))
        (Spectral.pruneAllocation S) ≤
      Spectral.detectionEfficiency
        (fun i ↦ Blindness.ldKernelSymbol decay (angle i)) M := by
  have habs : |decay| < 1 := hdabs
  have hp0 : 0 ≤ decay := hd0
  refine Spectral.topVariance_minimizes_detection
    (fun i ↦ Blindness.ldKernelSymbol decay (angle i)) M S
    (Blindness.ldKernelSymbol decay cutAngle)
    (fun i ↦ Blindness.ldKernelSymbol_pos habs) (Blindness.ldKernelSymbol_pos habs)
    hM ?_ ?_
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hin i hi)
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hout i hi)

/-- The same statement for the other task: a clumped panel maximises
reconstruction efficiency on the LD kernel.  Stated alongside the prohibition
because the pair is the trade-off — the clumping rule is not merely bad for
detection, it is bad for detection *because* it is optimal for reconstruction,
and the two conclusions come from the one threshold hypothesis. -/
theorem clumping_maximizes_reconstruction_on_ld_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (angle : ι → ℝ) (decay cutAngle : ℝ) (S : Finset ι) (M : ι → ℝ)
    (hd0 : 0 ≤ decay) (hdabs : |decay| < 1)
    (hM : Spectral.IsRankAllocation (S.card : ℝ) M)
    (hin : ∀ i ∈ S, Real.cos cutAngle ≤ Real.cos (angle i))
    (hout : ∀ i ∉ S, Real.cos (angle i) ≤ Real.cos cutAngle) :
    Spectral.reconstructionEfficiency
        (fun i ↦ Blindness.ldKernelSymbol decay (angle i)) M ≤
      Spectral.reconstructionEfficiency
        (fun i ↦ Blindness.ldKernelSymbol decay (angle i))
        (Spectral.pruneAllocation S) := by
  have habs : |decay| < 1 := hdabs
  have hp0 : 0 ≤ decay := hd0
  refine Spectral.topVariance_maximizes_reconstruction
    (fun i ↦ Blindness.ldKernelSymbol decay (angle i)) M S
    (Blindness.ldKernelSymbol decay cutAngle)
    (fun i ↦ Blindness.ldKernelSymbol_pos habs) hM ?_ ?_
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hin i hi)
  · intro i hi
    exact ldKernelSymbol_mono_in_cos habs hp0 (hout i hi)

end GeneticFrontier

end Descent.Portability
