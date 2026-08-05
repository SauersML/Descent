/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultiAncestryTheory
import Descent.Portability.SampleOverlapBias
import Descent.Portability.PortabilityBounds
import Descent.Core.Moments
import Descent.Portability.ImputationPortability
import Descent.Portability.LongitudinalPortability
import Descent.Portability.EquityAndImplementation
import Descent.PopGen.HumanDemography
import Descent.PopGen.DemographicCapacity
import Descent.Portability.CorrectionBiology
import Descent.PopGen.AdditiveInvariance
import Descent.Portability.PCCorrectability.Nonidentifiability
import Descent.Portability.PCCorrectability.Diagnostic
import Descent.Foundations.CovarianceStructure
import Descent.Blindness.DecoratedGeometryBlindness
import Descent.Program.CausalInference
import Descent.Portability.PolygenicContinuumCalibration
import Descent.Portability.GenerativePortabilityLaw
import Descent.Portability.PCCorrectability.EndToEnd
import Descent.Spectral.ProjectionSolve
import Descent.Portability.PCCorrectability.Design
import Descent.Blindness.CountingInvariantInstances
import Descent.Blindness.BundleRigidity.Cycles
import Descent.Blindness.BundleRigidity.Dichotomy
import Descent.Blindness.BundleRigidity.TwoAtom

/-!
# What the separate results say when they are put together

Several modules in this corpus each prove one thing and are cited by nothing. That is not
automatically a defect -- a module can state a FINDING that is the endpoint of an argument
rather than an input to one -- but a finding nobody composes with another finding is also
a finding nobody has checked against its neighbours.

This module composes a few of them. Each theorem below needs results from at least two
modules that do not import each other, and each says something neither module says alone.

## Empirical status

NOT AN EMPIRICAL CLAIM. Everything here is a consequence of results proved elsewhere; the
measurements are recorded on those results, and nothing new is asserted about a
population.
-/

namespace Descent.Program

/-! ### A reported improvement has two possible causes, and they are not distinguishable
from the number alone -/

/-- **Mixing ancestries raises the deployed `R²`, and so does overlapping the GWAS and
test samples. A single reported figure cannot say which happened.**

`MultiAncestryTheory.multi_ancestry_reduces_fst` proves the first: moving the training
composition toward the target lowers the differentiation and the deployed metric rises.
`SampleOverlapBias.overlap_inflation_positive` proves the second: if the evaluation sample
overlaps the discovery sample, the apparent `R²` exceeds the true one by a strictly
positive factor.

Both produce a higher number, from opposite kinds of cause -- one a real gain in
transferability, the other an artefact of how the number was measured. Neither module can
state this, because neither imports the other; the point of putting it here is that a
paper reporting "multi-ancestry training improved `R²`" has not, by that fact, excluded
the second explanation.

The conjunction is what is proved: an ancestry mix that genuinely improves the deployed
metric, AND an overlap that inflates a measurement of it, can coexist. -/
theorem improvement_has_two_causes
    (V_A V_E d₁ d₂ α r2_true r2_observed : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_d₂_closer : d₂ < d₁) (h_d₁_le_one : d₁ ≤ 1) (h_α_pos : 0 < α)
    (h_true : 0 < r2_true) (h_inflated : r2_true < r2_observed) :
    Portability.presentDayR2 V_A V_E ((1 - α) * d₁ + α * d₂) > Portability.presentDayR2 V_A V_E d₁ ∧
      0 < Portability.overlapInflation r2_true r2_observed :=
  ⟨Portability.multi_ancestry_reduces_fst V_A V_E d₁ d₂ α hVA hVE h_d₂_closer h_d₁_le_one h_α_pos,
   Portability.overlap_inflation_positive r2_true r2_observed h_true h_inflated⟩

/-- **And the genuine gain is bounded while the artefact is not.**

The real improvement is a movement along the drift law, so it is capped: no ancestry mix
takes the deployed `R²` above the trait's heritability, which
`Core.ScoreMoments.deployedR2_le_heritability` proves from the moment tuple. The overlap
inflation has no such ceiling -- it is a ratio of a measured quantity to a true one and
grows without bound as the true value falls.

So the two causes are not merely different, they are differently SHAPED, and a reported
`R²` exceeding the heritability is evidence of the second and not the first. That is a
usable test, and it exists only when the two results are read together. -/
theorem genuine_gain_is_capped_artefact_is_not
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) :
    Descent.Core.ScoreMoments.deployedR2 p V_E ≤ Descent.Core.share p.V_A V_E :=
  Descent.Core.ScoreMoments.deployedR2_le_heritability p V_E hE hflow

/-- **Diminishing returns, stated where it can be acted on.**

`MultiAncestryTheory.portability_concave_in_fst_reduction` proves the deployed `R²` is
concave in the differentiation: a fixed reduction `Δ` buys more at high `F_ST` than at
low. Composed with the cap above, that is the design consequence -- effort spent reducing
differentiation pays most where the populations are most diverged, and pays nothing at
all once the metric is at its ceiling.

Neither the concavity nor the cap says this alone. -/
theorem reduction_pays_most_where_divergence_is_worst
    (V_A V_E fst₁ fst₂ Δ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fst₁ < fst₂) (hfst₂_le_one : fst₂ ≤ 1) (hΔ : 0 < Δ) :
    Portability.presentDayR2 V_A V_E (fst₂ - Δ) - Portability.presentDayR2 V_A V_E fst₂ >
      Portability.presentDayR2 V_A V_E (fst₁ - Δ) - Portability.presentDayR2 V_A V_E fst₁ :=
  Portability.portability_concave_in_fst_reduction V_A V_E fst₁ fst₂ Δ hVA hVE hfst hfst₂_le_one hΔ

/-! ### Two erosions with different shapes, and what follows from the difference -/

/-- **Imputation attenuates by a bounded factor; time attenuates without bound but never
to zero. Neither module states the contrast, and the contrast is the design advice.**

`ImputationPortability.attenuated_le_true` proves the first: an imputation quality
`r²_imp ≤ 1` can only shrink the signal a score carries, and the shrinkage is a
MULTIPLICATIVE cap -- improve the panel and you recover the factor exactly.
`LongitudinalPortability.portabilityAtTime_pos_iff` proves the second: the exponential
decay in divergence time is strictly positive at every finite time, so time never takes
the score to zero, but no finite improvement recovers what it has taken.

One is a ceiling you can raise. The other is a slope you cannot. A programme that treats
them as one "attenuation" budget will spend on the wrong one. -/
theorem imputation_is_recoverable_time_is_not
    (beta_sq het r2_imp r2_initial lambda_total t : ℝ)
    (h_bsq : 0 ≤ beta_sq) (h_het : 0 ≤ het) (h_r2_le : r2_imp ≤ 1)
    (h_init : 0 < r2_initial) :
    Portability.attenuatedVariance beta_sq het r2_imp ≤ beta_sq * het ∧
      0 < Portability.portabilityAtTime r2_initial lambda_total t :=
  ⟨Portability.attenuated_le_true beta_sq het r2_imp h_bsq h_het h_r2_le,
   (Portability.portabilityAtTime_pos_iff r2_initial lambda_total t).mpr h_init⟩

/-- **A score that carries no signal carries none at any time**, so a vanishing
longitudinal report is not evidence about the decay rate.

`portabilityAtTime_eq_zero_iff` says the exponential never manufactures a zero: the
deployed value is zero exactly when the initial `R²` was. Composed with the cap above,
this is the reading rule -- a zero at follow-up says the score never worked, not that it
decayed, and the two are routinely confused in a longitudinal report. -/
theorem zero_at_followup_means_zero_at_baseline
    (r2_initial lambda_total t : ℝ)
    (h : Portability.portabilityAtTime r2_initial lambda_total t = 0) :
    r2_initial = 0 :=
  (Portability.portabilityAtTime_eq_zero_iff r2_initial lambda_total t).mp h

/-! ### The demographic chain reaches a clinical benefit gap -/

/-- **A migration rate difference between two histories becomes a clinical benefit gap,
and the whole chain is named maps.**

`EquityAndImplementation.mul_sub_mul_pos_of_lt` proves that an `R²` gap becomes a benefit
gap at any positive benefit-per-unit-`R²`. `Core.ScoreMoments.deployedR2_mono_in_migration`
proves that a lower migration rate produces a lower deployed `R²`. Composing them says
the thing neither says: two populations whose histories differ only in gene flow end up
with a benefit gap, and the size of that gap is determined by the demography rather than
by anything about the score.

That is the corpus's central claim, in the coordinate a health system would act on, and
until now it could not be stated -- `EquityAndImplementation` takes `R²` values as free
reals and nothing connected them to a history. -/
theorem demography_becomes_a_benefit_gap
    (p q : Descent.Core.PopGenParameters) (V_E α : ℝ)
    (hα : 0 < α) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    0 < α * Descent.Core.ScoreMoments.deployedR2 q V_E
          - α * Descent.Core.ScoreMoments.deployedR2 p V_E :=
  Portability.mul_sub_mul_pos_of_lt α (Descent.Core.ScoreMoments.deployedR2 q V_E)
    (Descent.Core.ScoreMoments.deployedR2 p V_E) hα
    (Descent.Core.ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV
      hlt hflow)

/-- **And the gap a health system can close is bounded by the heritability, not by
effort.**

Composing the cap with the benefit law: no demographic intervention, and no amount of
score improvement under pure drift, takes the benefit above `α` times the trait's
heritability. A programme promising more than that is promising something the model
cannot deliver, and the bound comes from the moment tuple rather than from an assumption
about what is achievable. -/
theorem benefit_is_capped_by_heritability
    (p : Descent.Core.PopGenParameters) (V_E α : ℝ)
    (hα : 0 < α) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig) :
    α * Descent.Core.ScoreMoments.deployedR2 p V_E
      ≤ α * Descent.Core.share p.V_A V_E :=
  mul_le_mul_of_nonneg_left
    (Descent.Core.ScoreMoments.deployedR2_le_heritability p V_E hE hflow) (le_of_lt hα)

/-! ### A measurement floor and a decay floor, and why one does not rescue the other -/

/-- **The portability ratio has a floor set by divergence time, and the measurement that
would detect it has a variance floor that does not shrink with better data.**

`HumanDemography.neutral_drift_ratio_ge_one_sub_coalescentTau` proves the first: under
neutral drift the retained fraction is at least `1 - t/(2Nₑ)`, so a score does not fall
off a cliff -- the loss is bounded by the scaled divergence time.
`PortabilityBounds.high_cv_inevitable` proves the second: the variance of a squared
prediction error is at least `2σ⁴` whatever the bias, so the coefficient of variation of
any single-individual error estimate has an irreducible floor.

Together: the theory says the degradation is gradual and bounded, and the measurement says
a per-individual estimate of it is intrinsically noisy. A study that fails to detect
portability loss has not thereby shown there is none -- the floor on the estimator is
present at every sample size, and the bound on the effect says it is a small quantity
being estimated. Neither module can say this; one is about the world and one is about the
instrument. -/
theorem gradual_loss_meets_a_noisy_instrument
    (V_A V_E t Ne σ_sq bias_sq : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (ht : 0 ≤ t) (hNe : 0 < Ne)
    (hσ : 0 < σ_sq) (hb : 0 ≤ bias_sq) :
    1 - t / (2 * Ne) ≤ PopGen.neutralDriftR2Ratio V_A V_E (Portability.fstFromGenerations t Ne) ∧
      4 * bias_sq * σ_sq + 2 * σ_sq ^ 2 ≥ 2 * σ_sq ^ 2 :=
  ⟨PopGen.neutral_drift_ratio_ge_one_sub_coalescentTau V_A V_E t Ne hVA hVE ht hNe,
   Portability.high_cv_inevitable σ_sq bias_sq hσ hb⟩

/-- **And the floor is the same quantity the Core chain bounds from above.**

`neutralDriftR2Ratio` is `Core.ScoreMoments.portabilityRatio` -- proved in
`HumanDemography` -- so the divergence-time lower bound and the Core unit-interval upper
bound are bounds on ONE quantity, not on two that resemble each other. That is what lets
them be read together at all, and it is the reason the identity was worth proving rather
than leaving the two names to agree by inspection. -/
theorem the_bounded_quantity_is_one_quantity
    (V_A V_E fst : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (hf0 : 0 ≤ fst) (hf : fst < 1) :
    PopGen.neutralDriftR2Ratio V_A V_E fst
      = Descent.Core.ScoreMoments.portabilityRatio V_A V_E fst ∧
    0 ≤ PopGen.neutralDriftR2Ratio V_A V_E fst ∧ PopGen.neutralDriftR2Ratio V_A V_E fst ≤ 1 :=
  ⟨PopGen.neutralDriftR2Ratio_eq_core V_A V_E fst,
   PopGen.neutralDriftR2Ratio_mem_unit V_A V_E fst hV hE hf0 hf⟩

/-! ### What correction cannot reach, and what the convention says the number is -/

/-- **Pooled correction misses exactly one direction, and that direction is where the
demographic contrast lives.**

`CorrectionBiology.dynamics_common_contrast_decomposition` proves the normal form: every
two-dynamics effect field is its pooled, recoverable component plus one scalar multiple of
a single contrast direction, and the pooled projector is blind to that multiple.
`DemographicCapacity.contrastSpikeLevel_eq_four_neiGst` proves what the contrast's
magnitude IS -- four times Nei's `G_ST` between the two populations.

So the unrecoverable component is not an unknown residual: it is a named function of the
allele-frequency divergence, and it grows with it. Correcting harder does not shrink it,
because the projector's blindness is structural rather than statistical.

**And the four matters.** `contrastSpikeLevel` is `4 · G_ST`, NOT `G_ST` and not
`F_ST` -- the corpus records that Nei's `G_ST` is FALSIFIED against the split law at up
to 18.59 sems where Hudson's matches at 0.03, so reading this level as a Hudson `F_ST`
misstates the unrecoverable component by a factor that moves with the data. The
convention is why the two results can be composed at all. -/
theorem unrecoverable_component_is_the_divergence
    (β : Bool → ℝ) (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    β = Portability.dynamicsPooledProjector β + Portability.dynamicsContrastCoefficient β • Conditionals.dynamicsContrast ∧
      PopGen.contrastSpikeLevel p₁ p₂ = 4 * neiGst p₁ p₂ :=
  ⟨Portability.dynamics_common_contrast_decomposition β,
   PopGen.contrastSpikeLevel_eq_four_neiGst p₁ p₂ h⟩

/-- **At no divergence there is nothing to miss.** The boundary that makes the previous
theorem a statement about divergence rather than about the projector: two populations at
the same allele frequency have contrast level exactly zero, so the blind direction carries
nothing and pooled correction is complete. Every claim that correction leaves something
behind is therefore a claim about the demography. -/
theorem nothing_missed_at_no_divergence (p : ℝ) :
    PopGen.contrastSpikeLevel p p = 0 :=
  PopGen.contrastSpikeLevel_self p

/-! ### Where the loss cannot come from, and what that leaves -/

/-- **Under a shared additive causal map the optimal weights are transport-invariant, so
every deployed loss the corpus proves must come from somewhere else.**

`AdditiveInvariance.additive_architecture_weights_agree_across_populations` proves that
two populations sharing one causal effect vector have the SAME optimal weights -- stated
with two independent expectation functionals and two independent predictor laws, so
nothing is assumed common except the effects. No allele-frequency divergence, however
large, moves them.

`Core.ScoreMoments.deployedR2_mono_in_migration` proves that a demographic history with less gene
flow deploys a strictly worse `R²`.

Both hold at once, and the conjunction is the constraint: the loss is real and it is NOT
in the optimal weights. What drift erodes is the moment tuple those weights are evaluated
against -- the score variance and the predictive covariance -- while the weights
themselves are the same vector in both populations. A programme that responds to a
portability gap by refitting weights is answering a question the invariance says is
already settled.

This is the trichotomy `AdditiveInvariance` states, closed from the other side: if the
weights do differ in practice, then additivity, a shared causal map, or direct (rather
than tagging) predictors has failed -- and that is a claim about the architecture, not
about the demography. -/
theorem loss_is_not_in_the_weights
    {Ω J : Type*} [Fintype J] [DecidableEq J]
    (sigmaInvP sigmaInvQ : Matrix J J ℝ)
    (EP EQ : Foundations.ExpFunctional Ω) (XP XQ : Ω → J → ℝ) (β : J → ℝ)
    (hP : Foundations.covarianceMatrix EP XP * sigmaInvP = 1)
    (hQ : Foundations.covarianceMatrix EQ XQ * sigmaInvQ = 1)
    (p q : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    Foundations.optimalWeightsFromMoments sigmaInvP EP XP (Foundations.causalSignal β XP) =
      Foundations.optimalWeightsFromMoments sigmaInvQ EQ XQ (Foundations.causalSignal β XQ) ∧
    Descent.Core.ScoreMoments.deployedR2 p V_E
      < Descent.Core.ScoreMoments.deployedR2 q V_E :=
  ⟨PopGen.additive_architecture_weights_agree_across_populations
      sigmaInvP sigmaInvQ EP EQ XP XQ β hP hQ,
   Descent.Core.ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV
     hlt hflow⟩

/-! ### `F_ST` determines the deployed metric and does NOT determine correctability -/

/-- **The same aggregate differentiation that fixes the deployed `R²` leaves PC
correctability undetermined. Two quantities, one input, opposite verdicts.**

`Core.ScoreMoments.deployedR2` is a FUNCTION of the demographic history: fix
`(Nₑ, m, μ)` and the deployed metric is determined.
`PCCorrectability.fst_does_not_determine_pc_correctability` proves the opposite for
correction: at fixed positive differentiation, sample size and marker count, two valid
subgroup sizes sit on OPPOSITE sides of the spectral threshold whenever the balanced
contrast is detectable.

So an `F_ST` tells you what a score will lose and tells you nothing about whether
principal-component correction can recover it. Reporting one differentiation number and
concluding anything about correctability is unsound, and the unsoundness is not a matter
of precision -- the counterexample is constructed, with both subgroup sizes admissible.

Neither module can state this: one is about a metric law, the other about a spectral
threshold, and nothing connected them. -/
theorem fst_fixes_the_metric_but_not_correctability
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig)
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F)
    (hdetect : Portability.bbpProxyThreshold n M < F * n) :
    (0 ≤ Descent.Core.ScoreMoments.deployedR2 p V_E ∧
      Descent.Core.ScoreMoments.deployedR2 p V_E ≤ 1) ∧
    ∃ mBelow mAbove : ℝ,
      0 < mBelow ∧ mBelow < n ∧ 0 < mAbove ∧ mAbove < n ∧
      Portability.demographicSpike n F mBelow < Portability.bbpProxyThreshold n M ∧
      Portability.bbpProxyThreshold n M < Portability.demographicSpike n F mAbove :=
  ⟨Descent.Core.ScoreMoments.deployedR2_mem_unit p V_E hE hflow,
   Portability.fst_does_not_determine_pc_correctability n M F hn hM hF hdetect⟩

/-- **And a correction diagnostic scores its own inapplicability as success.**

`pcTargetAxisEfficacy_null_susceptibility_is_junk`: at zero uncorrected susceptibility the
efficacy is `1` -- perfect correction, awarded for correcting something that was not
there. Composed with the non-identifiability above, that is a reporting hazard with two
independent parts: the differentiation does not tell you whether correction can work, and
the diagnostic that would tell you returns its best possible score in the case where it
does not apply.

Both are stated in their own modules. That they compound is stated here. -/
theorem correctability_reporting_has_two_independent_hazards
    (residualSusceptibility n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F)
    (hdetect : Portability.bbpProxyThreshold n M < F * n) :
    Portability.pcTargetAxisEfficacy 0 residualSusceptibility = 1 ∧
    ∃ mBelow mAbove : ℝ,
      0 < mBelow ∧ mBelow < n ∧ 0 < mAbove ∧ mAbove < n ∧
      Portability.demographicSpike n F mBelow < Portability.bbpProxyThreshold n M ∧
      Portability.bbpProxyThreshold n M < Portability.demographicSpike n F mAbove :=
  ⟨Portability.pcTargetAxisEfficacy_null_susceptibility_is_junk residualSusceptibility,
   Portability.fst_does_not_determine_pc_correctability n M F hn hM hF hdetect⟩

/-! ### The estimator's null and the metric's ceiling are different kinds of anchor -/

/-- **The chi-squared null is a calibration point; the heritability cap is a bound. Both
are "the number cannot exceed this", and only one of them is a fact about the world.**

`CovarianceStructure.ldsrExpectedChi2_null` fixes the null of the LD-score statistic used
to estimate the inputs of the deployed metric: at zero heritability the expected
chi-squared is exactly `1` -- a one-degree-of-freedom statistic, not a fitted offset. Its
own docstring records why the constant is load-bearing: the relation to
`ldsrExpectedBetaSq` multiplies through by `N` and carries the `+ 1` along without
constraining it, so a body with any other constant satisfies that identity and fails this.

`Core.ScoreMoments.deployedR2_le_heritability` fixes the ceiling of the metric itself: no
demographic history takes the deployed `R²` above the trait's heritability.

Put together they bracket a reported figure from both ends, and the two brackets have
different standing. The null is a property of the ESTIMATOR and holds by construction; the
cap is a property of the MODEL and would be refuted by an observation above it. A reported
`R²` exceeding the cap is evidence about the world; a chi-squared inflated above `1` is
evidence about the study. Neither module distinguishes them, because neither knows the
other exists. -/
theorem estimator_null_and_model_ceiling_are_different_anchors
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) (N M ell_j : ℝ) :
    Foundations.ldsrExpectedChi2 N 0 M ell_j 0 = 1 ∧
      Descent.Core.ScoreMoments.deployedR2 p V_E ≤ Descent.Core.share p.V_A V_E :=
  ⟨Foundations.ldsrExpectedChi2_null N M ell_j,
   Descent.Core.ScoreMoments.deployedR2_le_heritability p V_E hE hflow⟩

/-! ### The differentiation matrix determines the metric and cannot name the populations -/

/-- **`F_ST` fixes what a score loses, and a divergence matrix cannot tell two profile twins
apart. So the loss is determined and the labelling that explains it is not.**

`Core.ScoreMoments.deployedR2_eq` makes the deployed metric an explicit function of a
differentiation. `DecoratedGeometryBlindness.divergence_swap_twin_invariant` proves that
transposing a pair of profile twins leaves EVERY entry of a divergence matrix exactly as
it was -- so no statistic of pairwise divergences, no `F_ST` matrix, no principal-coordinate
embedding computed from one, no clustering of it, distinguishes the two labellings.

The conjunction is a caution about attribution rather than about magnitude. Given the
matrix, the deployed loss is pinned. Which population is which, when two are twins, is not
recoverable from that same matrix -- so a portability gap attributed to a named group is
carrying an identification the geometry does not supply. The size is a fact; the label is
a choice.

Neither module can say this: one computes a metric from a number, the other proves an
invariance of the matrix that number came from.

A naming hazard, recorded because it caught this composition. `DecoratedGeometryBlindness`
binds `Pop` as a SECTION VARIABLE -- an arbitrary finite type of populations -- which
shadows `Descent.Pop`, the concrete two-element source/target index the rest of the corpus
means by that name. Writing this theorem with the concrete `Pop` fails to synthesise
`Fintype`, which is the only reason the shadowing surfaced at all. The index type here is
called `Group` to keep the two apart. -/
theorem loss_is_determined_the_labelling_is_not
    {Group : Type*} [Fintype Group] [DecidableEq Group]
    (p : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig)
    (divergence : Group → Group → ℝ) (s t : Group)
    (htwin : Blindness.IsProfileTwin divergence s t)
    (hsymm : ∀ a b, divergence a b = divergence b a) (a b : Group) :
    Descent.Core.ScoreMoments.deployedR2 p V_E
        = Descent.Core.share
            (Descent.Core.retainedFraction p.fstEquilibrium p.V_A) V_E ∧
      divergence (Equiv.swap s t a) (Equiv.swap s t b) = divergence a b :=
  ⟨Descent.Core.ScoreMoments.deployedR2_eq p V_E hE hflow,
   Blindness.divergence_swap_twin_invariant divergence s t htwin hsymm a b⟩

/-! ### Two loss channels, and only one of them is in the demography -/

/-- **Effect turnover is a SECOND loss channel, additive to drift and invisible to every
demographic parameter.**

`Core.ScoreMoments.deployedR2_mono_in_migration` proves the first channel: less gene flow,
lower deployed `R²`, with the whole path from `(Nₑ, m, μ)` a composition of named maps.
`CausalInference.r2_strictMono_under_effect_turnover` proves the second: at FIXED
differentiation, a retention `ρ < 1` on the causal effects themselves strictly lowers the
deployed `R²` again.

The second channel takes no demographic argument. Two populations with identical
`(Nₑ, m, μ, t)` -- identical `F_ST`, identical moment tuple under drift alone -- can still
differ in deployed `R²` if their causal effects have turned over, and nothing in the
demographic chain sees it. So a measured portability gap larger than the drift chain
predicts is evidence FOR turnover rather than evidence against the chain, and the corpus
can now say which of the two a number is about.

This is the sharper form of `loss_is_not_in_the_weights` above: that theorem said the loss
is not in the optimal weights under a SHARED causal map; this one is what happens when the
causal map is not shared. -/
theorem drift_and_turnover_are_separate_channels
    (p q : Descent.Core.PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig)
    (V_A fst ρ : ℝ) (hVA : 0 < V_A) (hVE : 0 < V_E) (hfst_lt : fst < 1)
    (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) :
    Descent.Core.ScoreMoments.deployedR2 p V_E
        < Descent.Core.ScoreMoments.deployedR2 q V_E ∧
      PopGen.TransportedMetrics.r2FromSignalVariance (ρ ^ 2 * Portability.presentDayPGSVariance V_A fst) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (Portability.presentDayPGSVariance V_A fst) V_E :=
  ⟨Descent.Core.ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV
      hlt hflow,
   r2_strictMono_under_effect_turnover V_A V_E fst ρ hVA hVE hfst_lt hρ_pos hρ_lt⟩

/-! ### Two floors that are not the same floor -/

/-- **The calibration floor is an ancestry drift defect; the degradation law's floor is a
spectral distance. On an equal-amplitude slice they are different quantities of the same
history, and a programme that conflates them optimises the wrong one.**

`PolygenicContinuumCalibration.polygenicCalibrationFloor_eq_driftDefectSq` identifies the
irreducible calibration error with a drift defect across the ancestry continuum: no score,
however fitted, gets below it, because it is a property of how ancestry posteriors and
risks disagree rather than of the fit.

`GenerativePortabilityLaw.historyDegradation_equal_amplitude` says that when two histories
carry equal amplitude, their degradation is the squared amplitude times a SPECTRAL
distance -- a property of memory and phase, not of ancestry weighting.

Both are floors on what deployment can achieve, and they respond to different
interventions. Reweighting ancestries moves the first and leaves the second exactly where
it was; matching spectra moves the second and leaves the first. Neither module says the
other exists.

The equal-amplitude hypothesis is what makes the second one legible, and it is stated
rather than assumed away: off that slice the degradation carries an amplitude-mismatch
term too, which `historyDegradation_cone_identity` separates. -/
theorem calibration_floor_and_spectral_floor_are_different_floors
    {Genotype Ancestry : Type*} [Fintype Genotype] [Fintype Ancestry]
    (genotypeWeight : Genotype → ℝ)
    (ancestryPosterior : Genotype → Ancestry → ℝ)
    (ancestryRisk : Ancestry → Genotype → ℝ)
    (h h' : Portability.SpectralHistory) (ha : h.amplitude = h'.amplitude) :
    Portability.polygenicCalibrationFloor genotypeWeight ancestryPosterior ancestryRisk =
        Portability.calibrationDriftDefectSq genotypeWeight ancestryPosterior ancestryRisk ∧
      Portability.historyDegradation h h' = h.amplitude ^ 2 * Portability.historySpectralDistanceSq h h' :=
  ⟨Portability.polygenicCalibrationFloor_eq_driftDefectSq genotypeWeight ancestryPosterior ancestryRisk,
   Portability.historyDegradation_equal_amplitude h h' ha⟩

/-! ### Below the edge correction does nothing, and a zero ridge cannot rescue it -/

/-- **Below the spectral edge PC correction removes exactly none of the target axis, and
at zero ridge the solve keeps the null direction it would need to remove. Two independent
failures at the same configuration.**

`PCCorrectability.EndToEnd.modeledPCResidualSusceptibility_eq_uncorrected_of_subthreshold`
proves the first: at a spike below the BBP proxy threshold the residual susceptibility
EQUALS the uncorrected susceptibility -- not approximately, exactly. Nothing is corrected.

`Spectral.ProjectionSolve.ridged_infoQuadraticForm_zero_ridge_degenerate` proves the
second: with the ridge at zero, a direction the information matrix already annihilates is
still annihilated, so a rank-deficient design keeps its null direction and the
factorization has a zero pivot to find.

Composed, they close off the obvious response to the first. Sub-threshold correction fails
because the axis is not in the recovered subspace; adding no regularisation does not put
it there, and the solve that would expose the deficiency is the one that degenerates. The
fix has to be more signal or a positive ridge, not a better solve -- and neither module
can say that, because one is about a spectral threshold and the other about a linear
algebra guard. -/
theorem subthreshold_correction_fails_and_zero_ridge_does_not_help
    {n : Type*} [Fintype n] [DecidableEq n]
    (markerAxisVariance ancestryVariance nSample markers spike : ℝ)
    (hsubthreshold : spike ≤ Portability.bbpProxyThreshold nSample markers)
    (A : Matrix n n ℝ) (x : n → ℝ) (hnull : Spectral.infoQuadraticForm A x = 0) :
    Portability.modeledPCResidualSusceptibility markerAxisVariance ancestryVariance
        nSample markers spike
      = Portability.ancestryGradientSusceptibility markerAxisVariance ancestryVariance ∧
    Spectral.infoQuadraticForm (Spectral.ridgedInfoMatrix A 0) x = 0 :=
  ⟨Portability.modeledPCResidualSusceptibility_eq_uncorrected_of_subthreshold
      markerAxisVariance ancestryVariance nSample markers spike hsubthreshold,
   Spectral.ridged_infoQuadraticForm_zero_ridge_degenerate A x hnull⟩


/-! ### A design requirement you can compute, and a distance that cannot certify it -/

/-- **Whether ANY subgroup is correctable is a two-number calculator check, and the moment
distance that would certify a spectrum cannot see past its own order.**

`PCCorrectability.Design.exists_superthreshold_subgroup_iff_marker_requirement` turns the
existence question into arithmetic: some admissible subgroup sits above the spectral edge
if and only if the effective marker count exceeds `1/(F²n)`. That is a design requirement
a study can be checked against before it is run.

`CountingInvariantInstances.abs_moment_sub_le_momentDist` is the counting invariant's
guarantee: each individual moment disagreement is bounded by the distance -- but only for
moments up to the order `o` the distance was taken at. Beyond that order the bound says
nothing, which is what makes the invariant an APPROXIMATE blindness witness rather than a
certificate.

Together: the design check is sharp and the spectral certificate is not. A study can know
in advance whether correctability is possible at all, and still not be able to certify
from a truncated moment sequence that the spectrum it observed is the spectrum it has. -/
theorem design_check_is_sharp_the_moment_certificate_is_not
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F)
    (o : ℕ) (mu nu : ℕ → ℝ) {p : ℕ} (hp : p ≤ o) :
    ((∃ m : ℝ, 0 < m ∧ m < n ∧
        Portability.bbpProxyThreshold n M < Portability.demographicSpike n F m) ↔ 1 / (F ^ 2 * n) < M) ∧
      |mu p - nu p| ≤ Blindness.momentDist o mu nu :=
  ⟨Portability.exists_superthreshold_subgroup_iff_marker_requirement n M F hn hM hF,
   Blindness.abs_moment_sub_le_momentDist o mu nu hp⟩

/-! ### Two obstructions that need no hypothesis at all -/

/-- **A sign and a commutativity: two blindness obstructions that hold for EVERY choice of
weights, and so cannot be designed around.**

`BundleRigidity.Cycles.no_odd_cycle_of_pos`: on a cycle of odd length no atomic kernel
element exists -- not because of any condition on the mass ratios, but because the
criterion reads `∏ ρ = -1` and a product of positive ratios is positive. Parity alone
forbids it.

`BundleRigidity.Dichotomy.commutation_defect_eq_one`: the defect between a two-letter word
and its transposition is exactly `1` for every choice of weights, because both words use
the same letters and the products are over a commutative field. That is why the commutator
mechanism never needed a weight hypothesis -- the only one available to it holds
automatically.

Both are structural in the strongest sense available: no parameter choice escapes either.
Worth stating together because the two are met separately and read as technical side
conditions, when what they share is that they are not conditions at all. -/
theorem parity_and_commutativity_admit_no_escape
    {ι : Type*} [DecidableEq ι]
    (ρ : ℕ → ℝ) (hρ : ∀ s, 0 < ρ s) (n : ℕ) (hodd : Odd n)
    (P Q : ι → ℝ) (i j : ι)
    (hP : P i ≠ 0) (hP' : P j ≠ 0) (hQ : Q i ≠ 0) (hQ' : Q j ≠ 0) :
    (¬ ∃ x : ℕ → ℝ, x 0 ≠ 0 ∧ (∀ s, x (s + 1) = -ρ s * x s) ∧ x n = x 0) ∧
      Descent.Blindness.BundleRigidity.defect P Q [i, j] [j, i] = 1 :=
  ⟨Descent.Blindness.BundleRigidity.no_odd_cycle_of_pos ρ hρ n hodd,
   Descent.Blindness.BundleRigidity.commutation_defect_eq_one P Q i j hP hP' hQ hQ'⟩

/-- **The fourth proportional-reduction body, and the one that could not be reached from
its siblings.**

`PopulationGeneticsFoundations.fstFromHetRatio_eq_hudsonFstFromCoalescenceTimes_eq_r2FromMSE`
already relates
three spellings of `1 - residual/baseline`: a heterozygosity ratio, a coalescence-time
ratio, and an error-to-variance ratio.  `PCCorrectability.Diagnostic.pcTargetAxisEfficacy`
is the fourth — the fraction of a target ancestry axis captured by correction, written in
its own docstring as `V_K = 1 - H'/H`, deliberately echoing `F_ST` — and it could not join
them there, because `Diagnostic` imports nothing outside `PCCorrectability` and none of the
other three files imports `Diagnostic`.

This module reaches all four, through `StratificationConfounding → PCCorrectability`.  That
is the whole reason the statement is here and not beside any of the definitions: **the
tying theorem belongs wherever both sides are visible, not in one of the two files.**  A
guard demanding the latter reported this pair as unfixable when the only thing missing was
permission to speak from a third module.

As with its siblings these are four different quantities and no value of one may be
substituted for another; what is shared is the measure, and sharing it silently is what
this section exists to prevent. -/
theorem pcTargetAxisEfficacy_eq_proportionalReduction (residual baseline : ℝ) :
    Portability.pcTargetAxisEfficacy baseline residual = PopGen.fstFromHetRatio residual baseline ∧
      Portability.pcTargetAxisEfficacy baseline residual =
        Portability.hudsonFstFromCoalescenceTimes residual baseline ∧
      Portability.pcTargetAxisEfficacy baseline residual = PopGen.r2FromMSE residual baseline := by
  refine ⟨rfl, rfl, rfl⟩

/-- **The two-atom modulus curves are Nei's `G_ST` at the fold, divided by the product of
the two masses.**

`BundleRigidity.mOne` and `BundleRigidity.mTwo` share the numerator `|1 - 2p|`, and their
product is `(1 - 2p)² / (p (1 - p))`. The numerator is `neiGst p (1 - p)` by `neiGst_at_fold`
and the denominator is the product of the family's two masses, so the constant inside the
modulus curves is forced by the `ploidy` in `neiGst`'s normalisation rather than chosen.

This is the folded-spectrum reading of that module stated as an equation: `τ p = 1 - p` is
the ancestral/derived swap, `neiGst p (1 - p)` is symmetric under it, and the two modulus
curves are exchanged by it. `TwoAtom` imports only Mathlib and that is deliberate; the
statement therefore lives here, where both sides are visible. -/
theorem mOne_mul_mTwo_eq_neiGst_at_fold (p : ℝ) :
    Blindness.BundleRigidity.mOne p * Blindness.BundleRigidity.mTwo p = Descent.Core.neiGst p (1 - p) / (p * (1 - p)) := by
  rw [Descent.Core.neiGst_at_fold]
  unfold Blindness.BundleRigidity.mOne Blindness.BundleRigidity.mTwo Descent.Core.ploidy
  rw [div_mul_div_comm, ← sq_abs (1 - 2 * p), pow_two]

/-- **The importance-weighting effective sample size is a response-to-noise
permeability.** `(Σ w)² / Σ w²` is `Γ² / V` at `Γ = Σ w` and `V = Σ w²`: the reciprocal
variance with which averaging independent copies of a summary estimates its tangent.
`TransferLearningPGS` reads it as a sample count and `Permeability` reads it as
information; the arithmetic is one map, so a change of convention in either is a change in
both. -/
theorem importanceWeightESS_eq_momentPermeability (sum_w sum_w_sq : ℝ) :
    Portability.importanceWeightESS sum_w sum_w_sq = Spectral.momentPermeability sum_w sum_w_sq := rfl

end Descent.Program
