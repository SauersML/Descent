import Calibrator.PortabilityDrift
import Calibrator.LumpedRateBlindness

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
the heritability and the environmental variance.

**But `0.88` is the wrong number for the continental case, by a factor of eight in the
drift cost.** The `F_ST` slot here means `1 - H_target/H_source`, a *branch* quantity, and
feeding it a *pairwise* `F_ST` of `0.10`–`0.15` conflates two different things. Simulating
the actual configuration — both branches drifting 250 generations at `2N = 2000`, 8
replicates — gives pairwise `F_ST = 0.11884` but `1 - H_T/H_S = 0.01047`, so the true
drift-only floor is **`0.985`, not `0.88`**. Sister populations lose heterozygosity by about
the same amount, so their ratio sits near one.

The direction matters and it **strengthens** this file's thesis rather than weakening it: the
gap the non-drift channels must explain is `0.985 → 0.2`–`0.5`, not `0.88 → 0.2`–`0.5`.
(Relatedly, feeding pairwise Hudson `F_ST` to `neutralDriftR2Ratio` in place of branch `F`
costs `+3.43%`: `0.97002` against a true `0.93787`.)

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
  unfold neutralDriftR2Ratio presentDayR2 presentDayPGSVariance pgsVarianceFromHet
    TransportedMetrics.r2FromSignalVariance
  field_simp [hden, hsum, hVA']
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

This is the form in which the empirical numbers bite. Note that the floor must be computed
from the **branch** quantity `1 - H_T/H_S`, not from pairwise `F_ST`: at the continental
configuration those are `0.01047` and `0.11884` respectively, so the true drift-only floor is
`0.985` and not the `0.88` a pairwise reading gives. Measured European-to-African
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

/-! **Deleted: `taggedDriftR2Ratio V_A V_E fst shared_ld =
presentDayR2MutationDrift V_A V_E fst shared_ld / presentDayR2 V_A V_E 0`, together with
`taggedDriftR2Ratio_ge_retention`.**

This definition is absent on purpose. It applies the tagging factor to the denominator as
well. Loss of shared LD attenuates the score's covariance with the phenotype. It does
**not** reduce the target population's genetic variance. The target's phenotypic variance
is `(1-F)·V_A + V_E`, not `(1-F)·shared_ld·V_A + V_E`, so that body shrinks phenotypic
variance along with the signal and **overstates portability**. Wright–Fisher simulation
with genotype sampling noise removed, every frequency an exact rational and every
comparison in exact arithmetic:

| design | `shared_ld` | simulated | `taggedDriftR2Ratio` | error |
|---|---|---|---|---|
| symmetric, `2N=2000`, `t=250` | 0.739 | 0.7407 | 0.8522 | **+15.1%** |
| strong, `2N=400`, `t=100` | 0.583 | 0.5826 | 0.7328 | **+26.4%** |
| the docstring's own example | 0.34 | 0.3183 | 0.4606 | **+44.7%** |
| `h²=0.8`, `shared_ld=0.34` | 0.34 | 0.3400 | 0.7203 | **+111.9%** |

The error is exactly zero iff `shared_ld = 1`, which is why the sibling
`neutralDriftR2Ratio` validates at `0.0%` and this one does not. It grows with heritability:
`+9`–`15%` at `h² = 0.2`, `+28`–`49%` at `0.5`, `+60`–`112%` at `0.8`.
Measured in `proofs/validation/drift_diff/`. Use `taggedDriftR2RatioCorrected` below. -/

/-- **The tagged-drift accuracy ratio.**

    `k·(V_A + V_E) / ((1-F)·V_A + V_E)` with `k = (1-F)·shared_ld`. The tagging factor
    multiplies the signal only; the target's phenotypic variance carries `(1-F)·V_A + V_E`.
    A closed form of this shape reproduced the simulation **exactly** — `0.00000` in exact
    rationals, 12 of 12 replicates across two independent designs — where a form that also
    shrinks the denominator runs `+15%` to `+112%` high.

    Empirical status: **VALIDATED** (`proofs/validation/drift_diff/`). -/
noncomputable def taggedDriftR2RatioCorrected (V_A V_E fst shared_ld : ℝ) : ℝ :=
  (1 - fst) * shared_ld * (V_A + V_E) / ((1 - fst) * V_A + V_E)

/-- The accuracy ratio is at least the product of the two retention channels.
Same computation as the neutral case, with `1 - F_ST` replaced by
`(1 - F_ST) * shared_ld`. The drift channel divides a phenotypic variance
`(1 - F_ST)·V_A + V_E` that is no larger than the source's `V_A + V_E`, so the
ratio can only exceed the bare product of the two channels. `0 ≤ F_ST` is
load-bearing: simulation violated the bound in exactly the replicates where the
realised drift coefficient came out negative. -/
theorem taggedDriftR2RatioCorrected_ge_retention (V_A V_E fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst0 : 0 ≤ fst) (hfst1 : fst < 1) (hs0 : 0 < shared_ld) :
    (1 - fst) * shared_ld ≤ taggedDriftR2RatioCorrected V_A V_E fst shared_ld := by
  have h1f : 0 < 1 - fst := by linarith
  have hk0 : 0 < (1 - fst) * shared_ld := mul_pos h1f hs0
  have hden : 0 < (1 - fst) * V_A + V_E := add_pos (mul_pos h1f hVA) hVE
  unfold taggedDriftR2RatioCorrected
  rw [le_div_iff₀ hden]
  nlinarith [mul_nonneg hk0.le (mul_nonneg hfst0 hVA.le)]

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
    (hfst0 : 0 ≤ fst) (hfst1 : fst < 1) (hs0 : 0 < shared_ld)
    (h_match : taggedDriftR2RatioCorrected V_A V_E fst shared_ld = observed) :
    shared_ld ≤ observed / (1 - fst) := by
  have h1f : 0 < 1 - fst := by linarith
  have hge := taggedDriftR2RatioCorrected_ge_retention V_A V_E fst shared_ld hVA hVE
    hfst0 hfst1 hs0
  rw [h_match] at hge
  rw [le_div_iff₀ h1f]
  linarith [hge]

end AttributionToTagging

/-! ## A demographic parameter this file could never have fitted

The results above attribute the portability gap between measured parameters: `F_ST`, effective
size, migration rate, shared tagging. `Calibrator.LumpedRateBlindness` marks off a parameter that
is not merely hard to measure but absent from the observable law.

Take three demes in which two share a covariance signature. The direct exchange rate between those
two is invisible: the observable class is closed under the dynamics, and on that class the
generator does not depend on the exchange rate at all, so every generator-polynomial observable is
identical across the whole family and the identified set is the full range.

Three consequences. A fit reporting such a rate is reporting its prior, because the likelihood is
flat along that coordinate. The blindness is exact, so it is also a test: a method returning
different rates for datasets with the same observable law is defective, detectably and without new
data. And it is symmetry rather than degeneracy — the invisible direction is the antisymmetric
mode of the two lumped demes — so the repair is to break the lumping with any observable that
separates them, not to collect more samples under it.

This is `Calibrator.DeclaredInteractionClass` in demography: identification here is relative to a
declaration or it does not exist. -/

section UnidentifiableExchange

/-- The exchange rate between two covariance-indistinguishable demes is unidentifiable. Instance
    of `lumped_dynamics_blind_to_exchange`: every generator iterate is constant along the
    exchange-rate coordinate, so the observable is too at that order.

    Empirical status: DERIVED. Whether a given pair of human populations is lumpable at the
    resolution of the observable is the empirical question this asks to be answered explicitly
    rather than assumed. -/
theorem indistinguishableDemes_exchangeRate_unidentifiable
    (hubRate exchange exchange' : ℝ) (observable : Fin 3 → ℝ) (hlump : Lumped observable)
    (order : ℕ) :
    generatorIter (demeRate hubRate exchange) observable order =
      generatorIter (demeRate hubRate exchange') observable order :=
  lumped_dynamics_blind_to_exchange hubRate exchange exchange' observable hlump order

/-- The mechanism, in one identity: gene flow out of the hub never sees the leaf-to-leaf channel.

    Empirical status: DERIVED. -/
theorem hubFlow_carries_no_exchange_information
    (hubRate exchange : ℝ) (observable : Fin 3 → ℝ) (hlump : Lumped observable) :
    generatorApply (demeRate hubRate exchange) observable 0
      = 2 * hubRate * (observable 1 - observable 0) :=
  hubDrift_has_no_exchange_rate hubRate exchange observable hlump

end UnidentifiableExchange

end Calibrator
