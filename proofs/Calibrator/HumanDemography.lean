import Calibrator.PortabilityDrift

namespace Calibrator

/-!
# Human demographic parameters and the size of the portability gap

This file instantiates the drift machinery at measured human parameters and
asks whether neutral allele-frequency divergence can account for the observed
loss of polygenic score accuracy across continental groups. It cannot, and the
shortfall is large enough to be worth stating as a theorem rather than a
remark.

## The measured quantities

* Long-term human effective population size is on the order of `Ne = 10^4`.
* The out-of-Africa separation is roughly 50-100 kya, which at 25-30 years per
  generation is `t ≈ 1.7 × 10^3` to `4 × 10^3` generations.
* Pairwise `F_ST` between continental groups (say European and African
  ancestry) is roughly `0.10` to `0.15`.
* Polygenic scores trained in European-ancestry cohorts retain roughly `0.2`
  to `0.5` of their `R²` when evaluated in African-ancestry cohorts.

## The demographic model reproduces the observed divergence

`fstFromGenerations t Ne = 1 - exp (-t / (2 Ne))` at `t = 2500`, `Ne = 10^4`
gives `F_ST ≈ 0.118`, inside the measured band. So the coalescent layer of
this development is calibrated: it predicts the right amount of
allele-frequency divergence from independently measured demography.

## But the same divergence predicts almost no accuracy loss

`neutral_drift_ratio_ge_one_sub_fst` below shows that when the *only*
difference between source and target is drift in allele frequencies, the
ratio of target to source `R²` is bounded below by `1 - F_ST`, uniformly in
the heritability and the environmental variance. At `F_ST = 0.12` that floor
is `0.88`.

The measured ratio is `0.2` to `0.5`. The neutral model is therefore not
merely imprecise; it is off in a direction and by a margin that no choice of
heritability can repair, since the bound does not depend on `V_A` or `V_E`.

## What this forces

Since `(1 - F_ST)` is a floor and the observation lies far below it, the
accuracy loss must be carried by mechanisms this benchmark deliberately
excludes: mismatch between the linkage-disequilibrium structure of the two
populations, so that tag variants no longer proxy their causal partners;
heterogeneity in causal effect sizes from gene-environment interaction,
epistasis, or differential selection; and ascertainment of the discovery
sample. Those are exactly the channels carried elsewhere in this development
by the explicit tagging, effect-turnover, and context terms.

The biological content of this file is therefore a negative result with a
quantitative floor: allele-frequency divergence is real, is correctly
predicted by the demographic model, and is nearly irrelevant to portability.
-/

section NeutralDriftFloor

/-- Ratio of target to source `R²` when the two populations differ only by
neutral drift in allele frequencies. The source is the same model evaluated at
zero divergence.

    Empirical status: UNTESTED. -/
noncomputable def neutralDriftR2Ratio (V_A V_E fst : ℝ) : ℝ :=
  presentDayR2 V_A V_E fst / presentDayR2 V_A V_E 0

/-- Closed form for the neutral drift ratio. -/
theorem neutralDriftR2Ratio_eq (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hfst1 : fst < 1) :
    neutralDriftR2Ratio V_A V_E fst =
      (1 - fst) * (V_A + V_E) / ((1 - fst) * V_A + V_E) := by
  have h1f : 0 < 1 - fst := by linarith
  have hden : (1 - fst) * V_A + V_E ≠ 0 :=
    ne_of_gt (add_pos (mul_pos h1f hVA) hVE)
  have hsum : V_A + V_E ≠ 0 := ne_of_gt (add_pos hVA hVE)
  have hVA' : V_A ≠ 0 := ne_of_gt hVA
  unfold neutralDriftR2Ratio presentDayR2 presentDayPGSVariance
  field_simp
  ring

/-- **Neutral allele-frequency drift cannot cost more than `F_ST` of the
score's accuracy.**

If the source and target populations differ only in allele frequencies, by an
amount summarised by `F_ST`, then the ratio of target to source `R²` is at
least `1 - F_ST`. The bound is uniform: it holds for every additive genetic
variance and every environmental variance, so no choice of heritability makes
drift a larger effect. -/
theorem neutral_drift_ratio_ge_one_sub_fst (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst0 : 0 ≤ fst) (hfst1 : fst < 1) :
    1 - fst ≤ neutralDriftR2Ratio V_A V_E fst := by
  have h1f : 0 < 1 - fst := by linarith
  have hden : 0 < (1 - fst) * V_A + V_E := add_pos (mul_pos h1f hVA) hVE
  rw [neutralDriftR2Ratio_eq V_A V_E fst hVA hVE hfst1, le_div_iff₀ hden]
  nlinarith [mul_nonneg h1f.le (mul_nonneg hfst0 hVA.le)]

/-- Divergence accumulated in `t` generations at effective size `Ne` is at most
`t / (2 Ne)`, the coalescent time scale. -/
theorem fstFromGenerations_le_coalescentTau (t Ne : ℝ)
    (ht : 0 ≤ t) (hNe : 0 < Ne) :
    fstFromGenerations t Ne ≤ t / (2 * Ne) := by
  unfold fstFromGenerations fstFromTau coalescentTau
  have hfrac : 0 ≤ t / (2 * Ne) := div_nonneg ht (by linarith)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Demography bounds the portability loss directly.**

Chaining the two previous results: after `t` generations of separation at
effective size `Ne`, a score whose only cross-population difference is neutral
drift retains at least `1 - t / (2 Ne)` of its accuracy. For human continental
divergence, `t ≈ 2.5 × 10^3` and `Ne ≈ 10^4` give a floor of `0.875`. -/
theorem neutral_drift_ratio_ge_one_sub_coalescentTau
    (V_A V_E t Ne : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    1 - t / (2 * Ne) ≤ neutralDriftR2Ratio V_A V_E (fstFromGenerations t Ne) := by
  have hτ : 0 ≤ t / (2 * Ne) := div_nonneg ht (by linarith)
  have hfst0 : 0 ≤ fstFromGenerations t Ne := by
    unfold fstFromGenerations
    exact fst_from_tau_nonneg_of_nonneg _ (by unfold coalescentTau; exact hτ)
  have hfst1 : fstFromGenerations t Ne < 1 := by
    unfold fstFromGenerations
    exact fst_from_tau_lt_one _ (by unfold coalescentTau; exact hτ)
  have hbound := neutral_drift_ratio_ge_one_sub_fst V_A V_E
    (fstFromGenerations t Ne) hVA hVE hfst0 hfst1
  have hle := fstFromGenerations_le_coalescentTau t Ne ht hNe
  linarith

/-- **An observed accuracy ratio below `1 - F_ST` is not attributable to
allele-frequency drift.**

This is the form in which the empirical numbers bite. With continental
`F_ST ≈ 0.12` the neutral floor is `0.88`, while measured European-to-African
transfer retains `0.2` to `0.5`. The observation is strictly below anything
the neutral model can produce, so the residual must come from linkage
disequilibrium mismatch, effect-size heterogeneity, or ascertainment, and not
from the divergence in allele frequencies itself. -/
theorem observed_ratio_below_neutral_floor_needs_other_mechanism
    (V_A V_E fst observedRatio : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst0 : 0 ≤ fst) (hfst1 : fst < 1)
    (h_obs : observedRatio < 1 - fst) :
    observedRatio < neutralDriftR2Ratio V_A V_E fst :=
  lt_of_lt_of_le h_obs
    (neutral_drift_ratio_ge_one_sub_fst V_A V_E fst hVA hVE hfst0 hfst1)

/-- The shortfall that the non-drift channels have to explain, as a strictly
positive quantity. -/
theorem neutral_floor_shortfall_pos
    (V_A V_E fst observedRatio : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst0 : 0 ≤ fst) (hfst1 : fst < 1)
    (h_obs : observedRatio < 1 - fst) :
    0 < neutralDriftR2Ratio V_A V_E fst - observedRatio := by
  have := observed_ratio_below_neutral_floor_needs_other_mechanism
    V_A V_E fst observedRatio hVA hVE hfst0 hfst1 h_obs
  linarith

end NeutralDriftFloor

section AttributionToTagging

/-!
### Attributing the gap to preserved tagging

`presentDayPGSVarianceMutationDrift` already splits retained signal into two
multiplicative channels, `(1 - F_ST)` from allele-frequency divergence and
`shared_ld` for the fraction of tagging that survives the change in linkage
disequilibrium. The previous section showed the first channel is bounded below
by `1 - F_ST`. Here the same argument run on the product turns a measured
accuracy ratio into an upper bound on the second channel, which is the
quantitative form of "the loss is in the linkage disequilibrium".
-/

/-- Ratio of target to source `R²` when both allele-frequency divergence and
loss of shared tagging act.

    Empirical status: UNTESTED. -/
noncomputable def taggedDriftR2Ratio (V_A V_E fst shared_ld : ℝ) : ℝ :=
  presentDayR2MutationDrift V_A V_E fst shared_ld / presentDayR2 V_A V_E 0

/-- The accuracy ratio is at least the product of the two retention channels.
Same computation as the neutral case, with `1 - F_ST` replaced by
`(1 - F_ST) * shared_ld`. -/
theorem taggedDriftR2Ratio_ge_retention (V_A V_E fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst1 : fst < 1) (hs0 : 0 < shared_ld)
    (hk1 : (1 - fst) * shared_ld ≤ 1) :
    (1 - fst) * shared_ld ≤ taggedDriftR2Ratio V_A V_E fst shared_ld := by
  have h1f : 0 < 1 - fst := by linarith
  have hk0 : 0 < (1 - fst) * shared_ld := mul_pos h1f hs0
  have hden : 0 < (1 - fst) * shared_ld * V_A + V_E :=
    add_pos (mul_pos hk0 hVA) hVE
  have hsum : V_A + V_E ≠ 0 := ne_of_gt (add_pos hVA hVE)
  have hVA' : V_A ≠ 0 := ne_of_gt hVA
  have key : taggedDriftR2Ratio V_A V_E fst shared_ld =
      (1 - fst) * shared_ld * (V_A + V_E) /
        ((1 - fst) * shared_ld * V_A + V_E) := by
    unfold taggedDriftR2Ratio presentDayR2MutationDrift presentDayR2
      presentDayPGSVariance
    rw [presentDayPGSVarianceMutationDrift_eq]
    field_simp
    ring
  rw [key, le_div_iff₀ hden]
  nlinarith [mul_nonneg hk0.le (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (1 - fst) * shared_ld) hVA.le)]

/-- **A measured accuracy ratio caps how much tagging can have survived.**

If the observed target-to-source `R²` ratio is `observed`, then preserved
tagging satisfies `shared_ld ≤ observed / (1 - F_ST)`. With continental
`F_ST = 0.12` and a measured ratio of `0.3`, at most `0.34` of the tagging
carries over, so roughly two thirds of the score's predictive structure is
lost to linkage-disequilibrium mismatch rather than to allele frequencies.

This is the complement of `observed_ratio_below_neutral_floor_needs_other_mechanism`:
that result says drift cannot produce the gap, this one says how small the
tagging channel has to be for the gap to appear at all. -/
theorem sharedLD_le_observed_div_driftRetention
    (V_A V_E fst shared_ld observed : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst1 : fst < 1) (hs0 : 0 < shared_ld)
    (hk1 : (1 - fst) * shared_ld ≤ 1)
    (h_match : taggedDriftR2Ratio V_A V_E fst shared_ld = observed) :
    shared_ld ≤ observed / (1 - fst) := by
  have h1f : 0 < 1 - fst := by linarith
  have hge := taggedDriftR2Ratio_ge_retention V_A V_E fst shared_ld hVA hVE
    hfst1 hs0 hk1
  rw [h_match] at hge
  rw [le_div_iff₀ h1f]
  linarith [hge]

end AttributionToTagging

end Calibrator
