/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultiAncestryTheory
import Descent.Portability.SampleOverlapBias
import Descent.Portability.PortabilityBounds
import Descent.Core.Moments
import Descent.Portability.ImputationPortability
import Descent.Portability.LongitudinalPortability

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

namespace Descent

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
    presentDayR2 V_A V_E ((1 - α) * d₁ + α * d₂) > presentDayR2 V_A V_E d₁ ∧
      0 < overlapInflation r2_true r2_observed :=
  ⟨multi_ancestry_reduces_fst V_A V_E d₁ d₂ α hVA hVE h_d₂_closer h_d₁_le_one h_α_pos,
   overlap_inflation_positive r2_true r2_observed h_true h_inflated⟩

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
    presentDayR2 V_A V_E (fst₂ - Δ) - presentDayR2 V_A V_E fst₂ >
      presentDayR2 V_A V_E (fst₁ - Δ) - presentDayR2 V_A V_E fst₁ :=
  portability_concave_in_fst_reduction V_A V_E fst₁ fst₂ Δ hVA hVE hfst hfst₂_le_one hΔ

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
    attenuatedVariance beta_sq het r2_imp ≤ beta_sq * het ∧
      0 < portabilityAtTime r2_initial lambda_total t :=
  ⟨attenuated_le_true beta_sq het r2_imp h_bsq h_het h_r2_le,
   (portabilityAtTime_pos_iff r2_initial lambda_total t).mpr h_init⟩

/-- **A score that carries no signal carries none at any time**, so a vanishing
longitudinal report is not evidence about the decay rate.

`portabilityAtTime_eq_zero_iff` says the exponential never manufactures a zero: the
deployed value is zero exactly when the initial `R²` was. Composed with the cap above,
this is the reading rule -- a zero at follow-up says the score never worked, not that it
decayed, and the two are routinely confused in a longitudinal report. -/
theorem zero_at_followup_means_zero_at_baseline
    (r2_initial lambda_total t : ℝ)
    (h : portabilityAtTime r2_initial lambda_total t = 0) :
    r2_initial = 0 :=
  (portabilityAtTime_eq_zero_iff r2_initial lambda_total t).mp h

end Descent
