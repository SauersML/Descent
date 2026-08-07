/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.R2Decomposition
import Descent.Core.Ratios
import Descent.Foundations.TransportIdentities
import Descent.Portability.PGSCalibrationTheory.RecalibrationMethods

-- There is no `import Descent.Program.OpenQuestions` here, and there is no need for one:
-- `f1Score` lives DOWN in `Core/Decision.lean`, beside the rest of the clinical family,
-- and `f1_le_one` sits with it. An F1 formula is a classifier metric carrying no
-- programme content, so nothing in this file reaches the audit layer at the top of the
-- graph to obtain a harmonic mean of two arguments.

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.PrecisionRecall`

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
## Precision vs Recall in PGS Risk Stratification

Clinical PGS use involves classifying individuals as high-risk
or normal-risk. Precision and recall can have different portability.
-/

section PrecisionRecall

/-- **Precision (PPV) of high-risk classification.**
    PPV = P(actually high risk | PGS says high risk).
    Depends on prevalence via Bayes' theorem. -/
noncomputable def metricPPV (sensitivity specificity prevalence : ℝ) : ℝ :=
  sensitivity * prevalence /
    (sensitivity * prevalence + (1 - specificity) * (1 - prevalence))

/-- **Positive predictive value at zero prevalence, named.** With no cases in the population
there are no positive calls to be right about and the PPV is undefined; numerator and denominator
both vanish and Lean returns `0`. So a PERFECT test -- unit sensitivity, unit specificity --
reports that every positive call it makes is wrong. The failure is worst exactly where screening
programmes operate, at low prevalence, and it is indistinguishable from a test that genuinely
never calls a true positive. Consumers must require `0 < prevalence`. -/
theorem metricPPV_zero_prevalence_is_junk :
    metricPPV 1 1 0 = 0 := by
  unfold metricPPV
  norm_num

/-- **A perfectly specific test has predictive value one wherever it fires.**

At `specificity = 1` the false-positive term vanishes identically and the predictive value is one
at every prevalence, however small. That is the endpoint which fixes the form: the dependence on
prevalence is carried entirely by the false-positive term, so a body that let prevalence enter the
numerator would still be increasing in sensitivity and in prevalence, and would fail here.

It is also the reason the PPV portability gap is driven by specificity rather than sensitivity.
Two populations differing only in prevalence have equal predictive value when specificity is one,
and the gap opens only as specificity falls away from it. -/
theorem metricPPV_perfect_specificity (sensitivity prevalence : ℝ)
    (h : sensitivity * prevalence ≠ 0) :
    metricPPV sensitivity 1 prevalence = 1 := by
  unfold metricPPV
  norm_num
  exact div_self h

/-- Absolute portability gap for sensitivity between source and target use cases. -/
def sensitivityPortabilityGap (sensSource sensTarget : ℝ) : ℝ :=
  |sensTarget - sensSource|

/-- **The gap is a distance: symmetric, nonnegative, and zero exactly on agreement.** A signed
difference would satisfy neither the first nor the third, and the name says gap. -/
theorem sensitivityPortabilityGap_symm (a b : ℝ) :
    sensitivityPortabilityGap a b = sensitivityPortabilityGap b a := by
  unfold sensitivityPortabilityGap
  exact abs_sub_comm _ _

theorem sensitivityPortabilityGap_eq_zero_iff (a b : ℝ) :
    sensitivityPortabilityGap a b = 0 ↔ a = b := by
  unfold sensitivityPortabilityGap
  rw [abs_eq_zero, sub_eq_zero]
  exact eq_comm

/-! ### Calibrating one score across a continuum of ancestries

WHAT THE INDEX AND THE COVARIATE ARE. This is not optional bookkeeping; the wrong reading makes
every theorem below say `0 = 0`.

The COVARIATE is the SCORE. The INDEX is ancestry position. `π` is the ancestry posterior GIVEN
the score, and `η i` is ancestry `i`'s risk at that score. Each ancestry has its own calibration
curve in the score, the score's distribution genuinely varies with ancestry, and the drift is how
each ancestry's risk curve departs from the pooled curve.

The reading that destroys everything is index = principal-component position WHILE the components
are also regressors. Then the covariate determines the index, the ancestry posterior collapses to
a point mass, and `pointMass_driftDefect_zero` below shows the defect is identically zero. The
framework requires the index to be HIDDEN BEHIND the covariate, not measured alongside it.

A polygenic score deployed across many ancestries faces two calibration demands. INDEX-WISE:
calibrated within each ancestry separately. POOLED: calibrated on the mixture. The applied
literature treats these as competing objectives and reports a pooled-versus-worst-group gap as
evidence of the conflict.

Under squared loss they do not compete. `indexwiseLoss_eq_defect_add_sq` decomposes the
ancestry-averaged calibration loss into an irreducible term and the squared pooled residual,

    indexwiseLoss π η v = driftDefect π η + (pooledConditional π η - v) ^ 2

from which three things follow at once. The index-wise optimum IS the pooled-calibrated
predictor; the pooled residual there is exactly zero; and the achievable pairs trace a parabola,
not a frontier. Buying pooled miscalibration never buys index-wise accuracy.

The tension in the applied literature is real, but it is in the WORST-ancestry norm rather than
the averaged one. `pooledOptimum_worse_in_worst_ancestry` exhibits two ancestries at unequal
mixture weight where the pooled-calibrated value is strictly worse for the worse-served group
than a value that is itself pooled-miscalibrated. Averaging over ancestries and protecting the
worst ancestry are different objectives; averaging and pooling are not.

`driftDefect` is what no predictor removes: the dispersion of the ancestry-specific conditional
about its pooled average. It is simultaneously the unavoidable squared-loss regret, so the
calibration obstruction and the prediction regret are one number rather than two.

`pooledConditional_does_not_identify_drift` is the transport limit. Two drift fields with the same
pooled average differ at an individual ancestry, so pooled data cannot separate them. When
ancestries share covariate structure and differ only in the conditional, extrapolating to an
unmeasured ancestry returns nothing beyond the pooled average -- which is the sharpest statement
available about why a score fitted in one population does not transport to another by
recalibration alone.

Empirical status: DERIVED. The decomposition and the witnesses are exhibited; the mixture weights
and ancestry-specific conditionals of a real deployment are unmeasured inputs.
-/

/-- The pooled conditional: ancestry-specific risks averaged by mixture weight. -/
noncomputable def pooledConditional {m : ℕ} (π η : Fin m → ℝ) : ℝ := ∑ i, π i * η i

/-- Squared calibration error against every ancestry, averaged by mixture weight. -/
noncomputable def indexwiseLoss {m : ℕ} (π η : Fin m → ℝ) (v : ℝ) : ℝ :=
  ∑ i, π i * (η i - v) ^ 2

/-- Dispersion of the ancestry-specific conditional about the pooled one.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the weighted variance of supplied risks. -/
noncomputable def driftDefect {m : ℕ} (π η : Fin m → ℝ) : ℝ :=
  ∑ i, π i * (η i - pooledConditional π η) ^ 2

/-- **If the covariate determines the index, there is no drift and nothing below has content.**

The whole development lives on the ancestry posterior given the covariate being spread out. When
that posterior is a point mass -- which is exactly what happens if the ancestry coordinate is
itself among the regressors -- the defect is zero, the pooled and index-wise demands coincide
trivially, and every theorem in this section degenerates to `0 = 0`.

Stated so the degeneracy is visible rather than discovered later. It is the precondition for
reading any of the results as saying something about a deployment. -/
theorem pointMass_driftDefect_zero {m : ℕ} (η : Fin m → ℝ) (i₀ : Fin m) :
    driftDefect (fun j ↦ if j = i₀ then (1 : ℝ) else 0) η = 0 := by
  have hpool : pooledConditional (fun j ↦ if j = i₀ then (1 : ℝ) else 0) η = η i₀ := by
    unfold pooledConditional
    simp
  unfold driftDefect
  rw [hpool]
  simp

/-- **The pooled residual vanishes at the pooled conditional.** -/
theorem pooledConditional_residual_zero {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) :
    ∑ i, π i * (η i - pooledConditional π η) = 0 := by
  have hsplit : ∑ i, π i * (η i - pooledConditional π η)
      = (∑ i, π i * η i) - pooledConditional π η * ∑ i, π i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsplit, hπ, pooledConditional]
  ring

/-- **The index-wise loss splits into an irreducible defect and the squared pooled residual.**

Everything about the aggregate-versus-index-wise question follows from this one identity: the
minimiser is the pooled conditional, the defect is the value there, and the pooled residual at the
minimiser is zero. There is no frontier between the two demands to trade along. -/
theorem indexwiseLoss_eq_defect_add_sq {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (v : ℝ) :
    indexwiseLoss π η v = driftDefect π η + (pooledConditional π η - v) ^ 2 := by
  have hcross := pooledConditional_residual_zero π η hπ
  have key : ∀ i, π i * (η i - v) ^ 2
      = π i * (η i - pooledConditional π η) ^ 2
        + 2 * (pooledConditional π η - v) * (π i * (η i - pooledConditional π η))
        + (pooledConditional π η - v) ^ 2 * π i := by
    intro i; ring
  unfold indexwiseLoss driftDefect
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hcross, hπ]
  ring

/-- **The defect is the floor, and it is attained exactly at the pooled conditional.** -/
theorem driftDefect_le_indexwiseLoss {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (v : ℝ) :
    driftDefect π η ≤ indexwiseLoss π η v := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ v]
  nlinarith [sq_nonneg (pooledConditional π η - v)]

/-- **The unavoidable squared-loss regret IS the calibration defect**, not merely bounded by it.
The obstruction to calibrating across ancestries and the regret of predicting across them are one
number. -/
theorem indexwiseLoss_at_pooled {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) :
    indexwiseLoss π η (pooledConditional π η) = driftDefect π η := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ]
  ring

/-! #### The worst-ancestry norm is where the tension actually is -/

/-- Two ancestries at unequal mixture weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def twoAncestryWeights : Fin 2 → ℝ := ![3 / 4, 1 / 4]

/-- Their ancestry-specific risks at one covariate value.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def twoAncestryConditional : Fin 2 → ℝ := ![0, 1]

/-- The ancestry-risk witness equals the canonical two-person score witness. -/
theorem twoAncestryConditional_eq_reorderScore : twoAncestryConditional = reorderScore := by
  funext i
  fin_cases i <;> norm_num [twoAncestryConditional, reorderScore]

theorem twoAncestryWeights_sum : ∑ i, twoAncestryWeights i = 1 := by
  unfold twoAncestryWeights
  norm_num [Fin.sum_univ_two]

theorem twoAncestry_pooled_eq :
    pooledConditional twoAncestryWeights twoAncestryConditional = 1 / 4 := by
  unfold pooledConditional twoAncestryWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]

/-- **The pooled-calibrated predictor is strictly worse for the worse-served ancestry.**

At the pooled optimum `1/4` the worst ancestry carries error `3/4`; the midrange value `1/2`,
which is pooled-MIScalibrated, carries `1/2` in both. So protecting the worst ancestry and
calibrating the pool are genuinely different objectives, while calibrating the pool and
calibrating on ancestry-average are the same one. The gap reported in the applied literature is
this one, and it is a worst-case phenomenon rather than an aggregation phenomenon. -/
theorem pooledOptimum_worse_in_worst_ancestry :
    max |twoAncestryConditional 0 - 1 / 2| |twoAncestryConditional 1 - 1 / 2|
      < max |twoAncestryConditional 0 - 1 / 4| |twoAncestryConditional 1 - 1 / 4| := by
  unfold twoAncestryConditional
  norm_num

/-! #### Pooled data cannot identify the drift -/

/-- One drift field over two ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an algebraic nonidentifiability witness. -/
noncomputable def driftFieldA : Fin 2 → ℝ := ![1, -1]

/-- Another, with the ancestries exchanged.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an algebraic nonidentifiability witness. -/
noncomputable def driftFieldB : Fin 2 → ℝ := ![-1, 1]

/-! ### The repeated witness vectors are related by theorem, and audited

Seventeen definitions in this file are literal vectors, and two bodies occur more than
once: `![1/2, 1/2]` under four names and `![4/5, 1/5]` under two. Every one of those six
is tied to the others in its body-group by an equality theorem, and each group forms a
SINGLE connected component under those theorems -- not merely pairwise links that leave
two islands. `ancestryPairWeights_eq_uniformTwoWeights` and
`genotypeVisibleRisk_eq_binnedRiskByAncestry` are two of them.

The names stay. Each denotes a role in a distinct witness -- mixture weights, ancestry
weights, a bin-averaged risk, a genotype-visible risk -- and collapsing them would make
the witnesses share a symbol whose name fits only one of them. The theorem is what stops
the shared body from being a coincidence nobody checked.

The `Fin 4` sign vectors are NOT in this file and are NOT a cluster: `rad1`, `rad2`,
`balancedContrast` and `spreadContrast` live in `PortabilityMasterTheorem`, and no two
share a body. `balancedContrast` is the negation of `rad1`, which is a sign convention
meeting between an orthogonal-contrast pair and an exceedance witness in an unrelated
section, not an identity worth asserting.
-/

/-- Equal mixture weights. -/
noncomputable def uniformTwoWeights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- **The two drift fields are indistinguishable in the pooled average.** -/
theorem pooledConditional_does_not_identify_drift :
    pooledConditional uniformTwoWeights driftFieldA
      = pooledConditional uniformTwoWeights driftFieldB := by
  unfold pooledConditional uniformTwoWeights driftFieldA driftFieldB
  norm_num [Fin.sum_univ_two]

/-- **Yet they disagree at an ancestry.** With the pooled average all that the data constrain,
the ancestry-specific conditional is not recoverable: transporting a score to an unmeasured
ancestry by recalibrating on pooled data returns the pooled average and nothing more. -/
theorem driftFields_differ_at_first_ancestry : driftFieldA 0 ≠ driftFieldB 0 := by
  unfold driftFieldA driftFieldB
  norm_num

/-! #### Resolution: what refining the index buys, and what it cannot

Splitting the ancestry index into cells and calibrating per cell resolves part of the drift and
leaves the rest. The two parts are the between-cell and within-cell components of the drift
energy, and they sum to the total: refining moves energy from unresolved to resolved and creates
none. That is the finite form of the statement that the residual removed by refining is exactly
the drift energy the refinement resolves.

Two consequences, both witnessed concretely below on three ancestries at risks `0, 1, 2`.

Merging two ancestries into one cell strictly REDUCES the resolved energy, from `2/3` to `1/2`.
So resolved energy is monotone under refinement, and a coarser deployment -- calibrating on
continental groupings rather than finer ancestry -- resolves strictly less drift. It cannot be
made up elsewhere.

And the excess over the floor is exactly quadratic in how far the predictor sits from the pooled
conditional, with no linear term. That is why an ERROR IN THE INFERRED ANCESTRY GEOMETRY costs
only second order: the true optimum already annihilates the pooled direction, so the first-order
term that would otherwise appear is identically zero.
-/

/-- Three ancestries at equal mixture weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def threeAncestryWeights : Fin 3 → ℝ := fun _ ↦ 1 / 3

/-- Their ancestry-specific risks.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def threeAncestryConditional : Fin 3 → ℝ := ![0, 1, 2]

/-- The coarsening that merges the first two ancestries: two cells, at weights `2/3` and `1/3`,
carrying the within-cell mean risks `1/2` and `2`. -/
noncomputable def mergedCellWeights : Fin 2 → ℝ := ![2 / 3, 1 / 3]

/-- Cell-level risks after merging. -/
noncomputable def mergedCellConditional : Fin 2 → ℝ := ![1 / 2, 2]

/-- **Full resolution resolves the whole drift energy.** -/
theorem threeAncestry_full_resolution :
    driftDefect threeAncestryWeights threeAncestryConditional = 2 / 3 := by
  unfold driftDefect pooledConditional threeAncestryWeights threeAncestryConditional
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The merged deployment resolves strictly less.** -/
theorem mergedCells_resolution :
    driftDefect mergedCellWeights mergedCellConditional = 1 / 2 := by
  unfold driftDefect pooledConditional mergedCellWeights mergedCellConditional
  norm_num [Fin.sum_univ_two]

/-- **Merging ancestries strictly reduces the resolved drift energy.**

Calibrating on coarser groupings resolves less of the drift, and the shortfall is not recoverable
by any choice of predictor within the coarser scheme. This is the exact sense in which
finer ancestry resolution is not a modelling preference but a bound. -/
theorem merging_reduces_resolved_energy :
    driftDefect mergedCellWeights mergedCellConditional
      < driftDefect threeAncestryWeights threeAncestryConditional := by
  rw [mergedCells_resolution, threeAncestry_full_resolution]
  norm_num

/-- **The excess over the floor is exactly quadratic in the displacement, with no linear term.**

This is why an error in the inferred ancestry geometry costs only second order. The true optimum
already annihilates the pooled direction -- that is `pooledConditional_residual_zero` -- so the
cross term that would make geometry error first-order is identically zero. A deployment whose
ancestry axis is slightly wrong pays the square of that error, not the error. -/
theorem excess_is_exactly_quadratic {m : ℕ} (π η : Fin m → ℝ) (hπ : ∑ i, π i = 1) (e : ℝ) :
    indexwiseLoss π η (pooledConditional π η + e) - driftDefect π η = e ^ 2 := by
  rw [indexwiseLoss_eq_defect_add_sq π η hπ]
  ring

/-! #### The ancestry coordinate that explains the most variation can explain none of the drift

The drift operator sends a weight function on the ancestry continuum to the drift it captures.
Ordering ancestry coordinates by how much drift energy each carries is therefore the ordering that
minimises unresolved drift for a given number of coordinates.

Principal components order the same continuum by how much GENOTYPE variance each explains. Nothing
connects the two orderings, and the witness below shows they can be not merely different but
opposed: four ancestries, two candidate coordinates, and the coordinate that carries all of the
score variation carries none of the drift while the coordinate that carries all of the drift
carries none of the score variation.

So "use the leading principal components as ancestry coordinates" is not a neutral choice. It
optimises a criterion unrelated to calibration, and the direction it selects first can be exactly
the direction along which the risk curve does not move.

Two further consequences, which follow from the drift operator being built out of the drift
itself. The optimal coordinates are SCORE- AND TRAIT-SPECIFIC: change the score or the trait and
the operator changes, so there is no one universal ancestry map. And estimating them needs
phenotypes across the ancestry range, so the basis is supervised and does not extrapolate. What
`excess_is_exactly_quadratic` buys is that getting the basis slightly wrong costs the square of
the error rather than the error, provided the constant coordinate is always retained.
-/

/-- Four ancestries at equal posterior weight.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def fourAncestryWeights : Fin 4 → ℝ := fun _ ↦ 1 / 4

/-- A candidate ancestry coordinate: the contrast between the first pair and the second. -/
noncomputable def coordinateHighVariance : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) < 2 then 1 else -1

/-- A second candidate: the alternating contrast.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite contrast used in a proof witness. -/
noncomputable def coordinateHighDrift : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) % 2 = 0 then 1 else -1

/-- How the score varies across ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite score field used in a proof witness. -/
noncomputable def scoreAcrossAncestry : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) < 2 then 1 else -1

/-- How the risk curve drifts across ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite drift field used in a proof witness. -/
noncomputable def driftAcrossAncestry : Fin 4 → ℝ :=
  fun i ↦ if (i : ℕ) % 2 = 0 then 1 else -1

/-- Energy a candidate coordinate captures from a field on the ancestry index. -/
noncomputable def capturedEnergy {m : ℕ} (π w field : Fin m → ℝ) : ℝ :=
  (∑ i, π i * w i * field i) ^ 2

/-- **The first coordinate captures all of the score variation.** -/
theorem highVariance_captures_score :
    capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry = 1 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **And none of the drift.** -/
theorem highVariance_captures_no_drift :
    capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry = 0 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **The second coordinate captures none of the score variation.** -/
theorem highDrift_captures_no_score :
    capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry = 0 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **And all of the drift.** -/
theorem highDrift_captures_drift :
    capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry = 1 := by
  unfold capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry
  simp [Fin.sum_univ_four]
  try norm_num

/-- **The two orderings are opposed.** Ranking ancestry coordinates by explained score variation
puts the first ahead of the second; ranking them by captured drift puts the second ahead of the
first. A coordinate system chosen to explain variation is therefore not a coordinate system
chosen to explain portability, and here it is exactly the wrong one. -/
theorem variance_ordering_opposes_drift_ordering :
    capturedEnergy fourAncestryWeights coordinateHighDrift scoreAcrossAncestry
      < capturedEnergy fourAncestryWeights coordinateHighVariance scoreAcrossAncestry
    ∧ capturedEnergy fourAncestryWeights coordinateHighVariance driftAcrossAncestry
      < capturedEnergy fourAncestryWeights coordinateHighDrift driftAcrossAncestry := by
  rw [highVariance_captures_score, highVariance_captures_no_drift,
    highDrift_captures_no_score, highDrift_captures_drift]
  norm_num

/-! #### The atomic within/between split

The witness above shows merging two ancestries loses resolved energy. The identity below is why,
in general and exactly. For two ancestries at weights `w₁, w₂` carrying risks `a, b`, write `c`
for their weighted mean. Then against ANY reference `m`,

    w₁(a-m)² + w₂(b-m)² = (w₁+w₂)(c-m)² + w₁w₂/(w₁+w₂) · (a-b)²

The first term on the right is what a deployment that merges the two ancestries can still see;
the second is what it loses, and it is the weighted squared risk gap between them. The loss is
zero exactly when the two ancestries carry the same risk, which is when merging them was
harmless.

That is the whole content of resolution monotonicity: refinement resolves the pairwise risk gaps,
and coarsening returns them to the irreducible floor. -/
theorem within_between_split (w₁ w₂ a b m : ℝ) (hw : 0 < w₁ + w₂) :
    w₁ * (a - m) ^ 2 + w₂ * (b - m) ^ 2
      = (w₁ + w₂) * ((w₁ * a + w₂ * b) / (w₁ + w₂) - m) ^ 2
        + w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 := by
  field_simp
  ring

/-- **Merging two ancestries loses exactly the weighted squared risk gap.** Nonnegative always,
and zero exactly when the merged ancestries carried the same risk. -/
theorem merge_loss_nonneg (w₁ w₂ a b : ℝ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (hw : 0 < w₁ + w₂) :
    0 ≤ w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 := by
  have : 0 ≤ w₁ * w₂ / (w₁ + w₂) := by positivity
  positivity

/-- **And it is zero only when the merged ancestries carried the same risk**, which
is the second half of the claim above. With both weights positive the coefficient
is positive, so the loss vanishes exactly on equal risks -- merging costs nothing
only when there was nothing to merge. -/
theorem merge_loss_eq_zero_iff (w₁ w₂ a b : ℝ) (h₁ : 0 < w₁) (h₂ : 0 < w₂)
    (hzero : w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 = 0) :
    a = b := by
  have hsum : 0 < w₁ + w₂ := by linarith
  have hcoef : 0 < w₁ * w₂ / (w₁ + w₂) := div_pos (mul_pos h₁ h₂) hsum
  have hsq : (a - b) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (ne_of_gt hcoef)
    · exact h
  have : a - b = 0 := by
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  linarith

/-- **Equal risks make the merge free.** A deployment may coarsen its ancestry axis without cost
exactly across ancestries whose conditional risk agrees; every other merge is paid for. -/
theorem merge_loss_eq_zero_iff_equal_risk (w₁ w₂ a b : ℝ) (h₁ : 0 < w₁) (h₂ : 0 < w₂) :
    w₁ * w₂ / (w₁ + w₂) * (a - b) ^ 2 = 0 ↔ a = b := by
  have hw : 0 < w₁ + w₂ := by linarith
  have hc : w₁ * w₂ / (w₁ + w₂) ≠ 0 := by positivity
  constructor
  · intro h
    have hsq : (a - b) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hc
      · exact h'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linarith
  · intro h
    rw [h]
    ring

/-! #### The other half of the survival criterion -/

/-- The part of the threshold regret charged to ancestries below the threshold. -/
noncomputable def belowThresholdMass {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, π i * max (τ - η i) 0

/-- **A threshold below every ancestry-specific risk is also untouched by the drift.** With
`aboveThresholdMass_eq_zero` this is the full survival criterion: a decision threshold transports
across ancestries exactly when it lies outside the spread of their risks, on either side. -/
theorem belowThresholdMass_eq_zero {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ)
    (h : ∀ i, τ ≤ η i) :
    belowThresholdMass π η τ = 0 := by
  unfold belowThresholdMass
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [max_eq_right (by linarith [h i])]
  ring

/-- **Both sides charge at a threshold strictly inside the spread**, so no single prediction
serves every ancestry for that loss. Together with the two vanishing results this is exact: the
loss survives the drift if and only if its threshold avoids the interior of the risk range. -/
theorem belowThresholdMass_pos_inside :
    0 < belowThresholdMass uniformTwoWeights twoAncestryConditional (1 / 2) := by
  unfold belowThresholdMass uniformTwoWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]

/-! #### The obstruction is drift VISIBLE TO THE SCORE'S BINS, not total effect heterogeneity

The irreducible defect is the variance across ancestry of the BIN-AVERAGED risk, not of the
pointwise risk. Those come apart, and the distinction decides whether the portability floor is
estimable and possibly small or a restatement of "effect sizes differ across populations".

Below, two ancestries whose risks at a fine covariate resolution are `4/5` and `1/5` -- a large
pointwise disagreement -- average to `1/2` in both ancestries once binned. At the bin resolution
the defect is exactly zero: a score whose level sets average the drift away carries no irreducible
obstruction, however large the underlying effect heterogeneity. Sharpening the bins reveals it.

That is co-monotonicity in its operative form. Resolution and defect move together, so a claim to
have built a maximally discriminative score that is also calibrated across ancestry is a claim
that the drift is invisible to that score's level sets -- which is testable, on the fitted curves,
rather than a matter of opinion.
-/

/-- Two ancestries at equal weight in the deployment population.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def ancestryPairWeights : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Their risks at one fine covariate value: a large pointwise disagreement.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def fineRiskByAncestry : Fin 2 → ℝ := ![4 / 5, 1 / 5]

/-- Their BIN-AVERAGED risks, which agree: the bin averages the disagreement away.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def binnedRiskByAncestry : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The equal ancestry-pair weights reuse the earlier uniform two-ancestry quantity. -/
theorem ancestryPairWeights_eq_uniformTwoWeights : ancestryPairWeights = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [ancestryPairWeights, uniformTwoWeights]

/-- The coarsened equal-risk field has the same values as the uniform two-ancestry weights. -/
theorem binnedRiskByAncestry_eq_uniformTwoWeights :
    binnedRiskByAncestry = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [binnedRiskByAncestry, uniformTwoWeights]

/-- The fine-risk witness equals the earlier reversed target-risk witness. -/
theorem fineRiskByAncestry_eq_reorderTarget : fineRiskByAncestry = reorderTarget := by
  funext i
  fin_cases i <;> norm_num [fineRiskByAncestry, reorderTarget]

/-- **At the bin resolution there is no obstruction at all.** -/
theorem binnedRisk_driftDefect_zero :
    driftDefect ancestryPairWeights binnedRiskByAncestry = 0 := by
  unfold driftDefect pooledConditional ancestryPairWeights binnedRiskByAncestry
  norm_num [Fin.sum_univ_two]

/-- **At the fine resolution there is.** -/
theorem fineRisk_driftDefect_pos :
    0 < driftDefect ancestryPairWeights fineRiskByAncestry := by
  unfold driftDefect pooledConditional ancestryPairWeights fineRiskByAncestry
  norm_num [Fin.sum_univ_two]

/-- **Sharpening the score reveals drift the coarse bins hid.**

The same two ancestries carry no measurable obstruction when the score bins average their risks
together, and a strictly positive one when the bins separate them. So the portability floor is a
property of the score's resolution and not of the biology alone, and a score can be made
ancestry-calibrated by refusing to resolve -- at the exact cost of the resolution it gave up. -/
theorem refining_reveals_drift :
    driftDefect ancestryPairWeights binnedRiskByAncestry
      < driftDefect ancestryPairWeights fineRiskByAncestry := by
  rw [binnedRisk_driftDefect_zero]
  exact fineRisk_driftDefect_pos

/-! #### Resolution does not order the defect

`refining_reveals_drift` compares a binning with a REFINEMENT of that binning, and along a nested
chain the comparison is the conditional-Jensen one: coarsening can only shrink the visible defect.
The tempting generalisation -- that a predictor with more resolution carries more defect -- is
false, and the following instance refutes it outright.

Two independent fair bits `U` and `V`, an index taking two values with equal weight, and

    η(U, V) = 1/2 + (1/10) * sign U + t * (1/10) * sign V.

A predictor resolving `U` sees the whole non-drifting part and none of the drifting part: it has
positive resolution and zero defect. A predictor resolving `V` sees only the drifting part, which
averages away over the index: it has zero resolution and positive defect. So one predictor has
STRICTLY more resolution and STRICTLY less defect than the other, and no co-monotone frontier
exists over unrelated predictors.

The two are incomparable as σ-algebras, which is exactly the hypothesis `refining_reveals_drift`
supplies and this instance withholds.
-/

/-- The sign a bit carries: `-1` at `0`, `+1` at `1`. Used both for the two bits and for the
two index values. -/
noncomputable def bitSign : Fin 2 → ℝ := driftFieldB

/-- Two index values, equally weighted. -/
noncomputable def twoBitIndexWeights : Fin 2 → ℝ := binnedRiskByAncestry

/-- The conditional seen by a predictor that resolves `U`: it does not move with the index. -/
noncomputable def uResolvedConditional (u : Fin 2) : Fin 2 → ℝ :=
  fun _ ↦ 1 / 2 + (1 / 10) * bitSign u

/-- The conditional seen by a predictor that resolves `V`: it moves with the index and its
index-average is constant. -/
noncomputable def vResolvedConditional (v : Fin 2) : Fin 2 → ℝ :=
  fun i ↦ 1 / 2 + bitSign i * ((1 / 10) * bitSign v)

/-- **Resolving `U` exposes no drift.** -/
theorem uResolvedConditional_driftDefect_zero (u : Fin 2) :
    driftDefect twoBitIndexWeights (uResolvedConditional u) = 0 := by
  unfold driftDefect pooledConditional uResolvedConditional twoBitIndexWeights
    binnedRiskByAncestry
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Resolving `V` exposes drift**, at every value of the bit. -/
theorem vResolvedConditional_driftDefect_pos (v : Fin 2) :
    0 < driftDefect twoBitIndexWeights (vResolvedConditional v) := by
  unfold driftDefect pooledConditional vResolvedConditional
  fin_cases v <;> norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Resolving `U` has positive resolution**: the index-averaged conditional still varies across
the bit, which is what resolution measures. -/
theorem uResolvedConditional_resolution_pos :
    0 < driftDefect twoBitIndexWeights
      (fun u ↦ pooledConditional twoBitIndexWeights (uResolvedConditional u)) := by
  unfold driftDefect pooledConditional uResolvedConditional
  norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Resolving `V` has zero resolution.** The index average of the drifting part is constant, so
a predictor that sees only `V` predicts the same value everywhere.

With the three theorems above this is the refutation: `U` has positive resolution and zero
defect, `V` has zero resolution and positive defect. More resolution, less defect. -/
theorem vResolvedConditional_resolution_zero :
    driftDefect twoBitIndexWeights
      (fun v ↦ pooledConditional twoBitIndexWeights (vResolvedConditional v)) = 0 := by
  unfold driftDefect pooledConditional vResolvedConditional
  norm_num [Fin.sum_univ_two, bitSign, driftFieldB, twoBitIndexWeights,
    binnedRiskByAncestry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! #### Superposition of landscapes lives in `LandscapeSuperposition`

Pooling cohorts is a weighted sum of per-cohort landscapes, which is the shape
`indexwiseLoss` above already has, so a version of that theory was drafted here.
It is gone: `Descent/Blindness/LandscapeSuperposition.lean` has the same material
and more.

That file carries the decomposition of the pooled near-optimal set over feasible
level allocations, the overlap inclusion it implies, the persistence lemma in both
set and interval form, the vertex-of-the-simplex counterexample showing the
decomposition is not uniform in the weights, and the spherical calibration
arithmetic -- two barriered summands whose equal mixture is barrier-free. On that
last one it proves the mixture certificate positive across the whole overlap
range rather than at a single point, which the version here did not.

The connection worth keeping in mind from this module: the identity's usable half
is one-directional, and it is the same asymmetry `driftDefect` has. A barrier
excluded by some cohort at every split of the target is excluded by the pooled
fit; that pooling DISSOLVES a barrier does not follow, and needs configurations
built at the intermediate overlaps.
-/

/-- **The pooled calibration target decomposes into per-ancestry loss budgets.**

`indexwiseLoss` is a nonnegatively weighted sum of per-ancestry squared errors, so
it is a superposition landscape in the sense of `LandscapeSuperposition`, and that
file's decomposition specialises here. A prediction meets a pooled calibration
target exactly when there is a way of dividing the loss budget across ancestries
that the prediction meets ancestry by ancestry -- and the division witnessing it
is the prediction's own per-ancestry error.

Nonnegativity of the mixture weights is what makes the reverse direction true. -/
theorem pooledTarget_iff_exists_budget {m : ℕ} (π η : Fin m → ℝ) (ε v : ℝ)
    (hπ : ∀ i, 0 ≤ π i) :
    indexwiseLoss π η v ≤ ε ↔
      ∃ budget : Fin m → ℝ, (∑ i, π i * budget i) ≤ ε ∧ ∀ i, (η i - v) ^ 2 ≤ budget i := by
  constructor
  · intro h
    exact ⟨fun i ↦ (η i - v) ^ 2, h, fun i ↦ le_rfl⟩
  · rintro ⟨budget, hsum, hle⟩
    refine le_trans ?_ hsum
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) (hπ i)

/-- **A score no budget split can rescue is rejected by the pooled fit.**

The usable half of the decomposition, in the direction the corpus cares about. If
for every division of the loss budget across ancestries some ancestry is over its
share, then the pooled objective rejects the prediction too. Pooling cohorts
cannot rescue a score that fails ancestry-wise under every allocation.

The converse does not follow and is not stated: that pooling ADMITS a prediction
no single allocation admits would need a prediction constructed at the
intermediate errors, which no inclusion of this shape supplies. It is the same
asymmetry `driftDefect_le_indexwiseLoss` has -- a floor that transfers upward and
not down. -/
theorem pooledTarget_reject_of_every_budget_rejected {m : ℕ} (π η : Fin m → ℝ) (ε v : ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hreject : ∀ budget : Fin m → ℝ, (∑ i, π i * budget i) ≤ ε →
      ∃ i, budget i < (η i - v) ^ 2) :
    ¬ (indexwiseLoss π η v ≤ ε) := by
  intro h
  obtain ⟨budget, hsum, hle⟩ := (pooledTarget_iff_exists_budget π η ε v hπ).mp h
  obtain ⟨i, hi⟩ := hreject budget hsum
  exact absurd (hle i) (not_le.mpr hi)

/-! #### Heterogeneous cohorts can remove a barrier that each cohort alone has

The superposition decomposition above says a barrier persists unless some
allocation satisfies every cohort at once. This records the population geometry
where that escape is available, and how much minority data it takes.

For a design whose covariance couples the planted support to a decoy support with strength `α`, the
population loss at overlap fraction `x` away from the truth is
`φ_q(x) = x(1 - qx) / (1 - qx(1-x))` with `q = α²`. A barrier exists exactly when
that profile has an interior maximum, which happens exactly when `1 - 3q + q²`
turns negative -- so the transition is at the root of that quadratic.

The root is the golden-ratio conjugate squared, and the transition in `α` is the
golden-ratio conjugate itself. Mixing two cohorts with couplings `±ρ` in
proportion `π` gives an average coupling `ρ(2π - 1)`, so a minority fraction of
`½(1 - ρ_c/ρ)` suffices to bring the mixture below the transition. At the
strongest possible coupling that is `(3 - √5)/4`, a little over nineteen per cent.

The biological reading is the one the corpus cares about: a barrier created by
linkage between a causal locus and a decoy in one ancestry can be removed by
including a second ancestry in which the linkage has the opposite sign, and the
required minority fraction is bounded away from a half. It is not a statement
about better conditioning -- the eigenvalue extremes and the coherence can be
held fixed while this happens.
-/

/-! **`ogpOverlapProfile` is deleted.** It was `Core.overlapProfile q x`, and so is
`Blindness.populationOverlapProfile` -- the same profile named twice, in two modules that
do not import each other, each having separately proved the same junk-denominator branch
and the same `q 1 = 1 - q` endpoint. Those two facts are about the kernel, not about
either reading of it, and they now live beside it in `Core.Ratios` as
`overlapProfile_at_zero_denominator_is_junk` and `overlapProfile_at_one`. -/

/-- The sign of this quadratic decides whether the loss profile has an interior
maximum, and so whether the landscape has a barrier. -/
noncomputable def ogpTransitionPolynomial (q : ℝ) : ℝ := 1 - 3 * q + q ^ 2

/-- **The transition is at the golden-ratio conjugate squared.** -/
theorem ogpTransitionPolynomial_root :
    ogpTransitionPolynomial ((3 - Real.sqrt 5) / 2) = 0 := by
  unfold ogpTransitionPolynomial
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- **And so the transition in the coupling itself is the golden-ratio
conjugate**, since squaring it returns the root above.

Stated as a root of `ogpTransitionPolynomial` rather than as the bare arithmetic identity
`((√5 - 1)/2)² = (3 - √5)/2`: the name claims something about the overlap-gap transition,
and this is that claim.  The arithmetic is still what proves it. -/
theorem ogpCouplingThreshold_sq :
    ogpTransitionPolynomial (((Real.sqrt 5 - 1) / 2) ^ 2) = 0 ∧
      ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq : ((Real.sqrt 5 - 1) / 2) ^ 2 = (3 - Real.sqrt 5) / 2 := by nlinarith [h]
  exact ⟨by rw [hsq]; exact ogpTransitionPolynomial_root, hsq⟩

/-- **The minority fraction that removes the barrier at maximal coupling.**

Two cohorts with couplings of opposite sign, mixed in proportion `π`, have average
coupling `ρ(2π - 1)`. Setting that to the threshold and solving for the minority
share gives `½(1 - ρ_c/ρ)`; at `ρ = 1` it is `(3 - √5)/4`, a little over nineteen
per cent. Bounded away from a half: the minority cohort does not have to be
half the data. -/
theorem ogpMinorityFraction_at_unit_coupling :
    (1 - (Real.sqrt 5 - 1) / 2) / 2 = (3 - Real.sqrt 5) / 4 := by
  ring

/-! #### The sign restriction the nineteen per cent depends on

The construction above mixes couplings `ρ` and `-ρ`, and it closes the barrier by
passing the mixed coupling through zero at `π = 1/2`. That is a cancellation of
opposite signs, not an averaging of magnitudes, and the distinction decides
whether the minority share means anything for study design: real ancestries
usually differ in the *magnitude* of their linkage correlations, not the sign.
Sign flips occur -- a variant arising on a different haplotype background -- but
they are not the typical case.

The two results below say exactly that: the mixed coupling is the convex
combination of the two cohort couplings, and it reaches zero only at the balance
point. The complementary half -- that same-sign cohorts keep their sign under
every mixture, so no mixture reaches zero -- is
`sameSignAncestryPooling_preservesActiveCorrelation` in `LandscapeSuperposition`,
and is not restated here.

So the demonstrated mechanism is narrower than "diversity helps", and whether
same-sign cohorts of differing magnitude can also close a barrier is not settled
by this construction. -/
noncomputable def mixtureCoupling (ρ π : ℝ) : ℝ := ρ * (2 * π - 1)

/-- **The mixed coupling is the convex combination of `ρ` and `-ρ`.** Written this
way the mechanism is visible: the two cohorts enter with opposite signs. -/
theorem mixtureCoupling_eq_convex (ρ π : ℝ) :
    mixtureCoupling ρ π = π * ρ + (1 - π) * (-ρ) := by
  unfold mixtureCoupling
  ring

/-- **Opposite signs close the barrier at the balance point, and only there.** -/
theorem mixtureCoupling_eq_zero_iff (ρ π : ℝ) (hρ : ρ ≠ 0) :
    mixtureCoupling ρ π = 0 ↔ π = 1 / 2 := by
  unfold mixtureCoupling
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hρ
    · linarith
  · intro h
    rw [h]
    ring

/-! #### A direction invisible to the pooled design is invisible to every cohort

The exact-degeneracy counterpart, and it runs the other way from the barrier
result. Pooling cannot manufacture identifiability: if a coefficient direction
carries no signal in the pooled design, it carries none in any cohort. What
pooling does is the converse -- a direction invisible in one cohort can be visible
in the pool, because the pooled quadratic form is a nonnegatively weighted sum and
vanishes only when every term does.

So heterogeneous cohorts shrink the exactly-unidentifiable set by intersecting
it, which is the precise sense in which adding an ancestry can resolve an
ambiguity that no single ancestry resolves. -/
theorem pooledQuadratic_eq_zero_iff {K : ℕ} (π : Fin K → ℝ) (Q : Fin K → ℝ)
    (hπ : ∀ g, 0 < π g) (hQ : ∀ g, 0 ≤ Q g) (g : Fin K)
    (hzero : ∑ h, π h * Q h = 0) :
    Q g = 0 := by
  have hnn : ∀ h ∈ (Finset.univ : Finset (Fin K)), 0 ≤ π h * Q h :=
    fun h _ ↦ mul_nonneg (hπ h).le (hQ h)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero g (Finset.mem_univ g)
  exact (mul_eq_zero.mp this).resolve_left (hπ g).ne'

/-! #### Heterogeneity fattens the lower tail, so barriers close by filling not deleting

The intuition that pooling cohorts removes a barrier by DELETING the distant
cluster is backwards, and the correction is a one-line concavity argument.

The large-deviation rate for an anomalously small residual is built from
`log (1 + 2λs)` in the per-cohort residual scales `s`. That function is concave,
so a mixture of cohorts has rate at most that of a single cohort at the average
scale. Holding the average covariance fixed, heterogeneity cannot make a
candidate's anomalously good fit exponentially less likely -- it makes it at
least as likely.

So at fixed average covariance a barrier closes by FILLING the intermediate
region, not by removing the far cluster. That matches the decomposition above,
whose usable half certifies persistence and says nothing about dissolution: the
dissolution direction needs configurations built at intermediate overlaps, and
this says the tails there are if anything fatter than the homogeneous
comparison would suggest.
-/

/-- **Two cohorts have a smaller rate than one cohort at their average scale.**

Concavity of the logarithm, applied at the residual scales. `π` and `1 - π` are
the cohort proportions and `s₁`, `s₂` the per-cohort residual scales; the
right-hand side is the rate of a homogeneous design whose scale is the mixture
average. A smaller rate means a fatter lower tail. -/
theorem mixtureRate_le_averagedRate (π s₁ s₂ lam : ℝ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hs₁ : 0 < 1 + 2 * lam * s₁) (hs₂ : 0 < 1 + 2 * lam * s₂) :
    π * Real.log (1 + 2 * lam * s₁) + (1 - π) * Real.log (1 + 2 * lam * s₂)
      ≤ Real.log (1 + 2 * lam * (π * s₁ + (1 - π) * s₂)) := by
  have hcon : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have h := hcon.2 (Set.mem_Ioi.mpr hs₁) (Set.mem_Ioi.mpr hs₂) hπ0
    (by linarith : (0:ℝ) ≤ 1 - π) (by ring : π + (1 - π) = 1)
  have hmix : π • (1 + 2 * lam * s₁) + (1 - π) • (1 + 2 * lam * s₂)
      = 1 + 2 * lam * (π * s₁ + (1 - π) * s₂) := by
    simp only [smul_eq_mul]
    ring
  rw [hmix] at h
  simpa [smul_eq_mul] using h

/-! #### The frequency-spectrum inverse problem locks complexity to ill-posedness

For a demographic history with at most `K` epochs, the sharp stability exponent
for recovering it from the expected site-frequency spectrum is `1 / (2K - 3)`.
Read through the sample size the spectrum comes from, that constant is not an
arbitrary function of `K`.

A sample of `n = 2K - 2` haplotypes has exactly `n - 1 = 2K - 3` spectrum entries,
so the exponent is the reciprocal of the number of entries available. Each extra
epoch demands two more samples AND costs two in the exponent: the model's
complexity and the inverse problem's ill-posedness move together, and no
sampling effort separates them.

Two epochs are Lipschitz-stable. Three already have cube-root instability, four
fifth-root. -/

/-! **`epochSampleSize` is deleted.** It was `Core.pairedEpochCount K`, and so is
`PopGen.epochLineageSampleSize` -- one quantity under two names, in two subsystems,
each with its own small theory proved about it. The theorems below name the kernel
directly rather than reintroduce a third name for it; the named quantity belongs in
`FrequencySpectrumStability`, where the frequency spectrum it counts entries of lives,
and this module only ever needed the count. -/

/-- Number of unfolded spectrum entries at that sample size. -/
def spectrumEntries (n : ℕ) : ℕ := n - 1

/-- **The stability exponent's denominator is the number of spectrum entries.**
Not a coincidence of the parameterisation: it says the recoverable resolution is
set by how many numbers the spectrum has, and each epoch consumes two of them. -/
theorem spectrumEntries_pairedEpochCount (K : ℕ) (hK : 2 ≤ K) :
    spectrumEntries (Descent.Core.pairedEpochCount K) = 2 * K - 3 := by
  unfold spectrumEntries Descent.Core.pairedEpochCount
  omega

/-- **Two epochs are Lipschitz-stable.** -/
theorem spectrumEntries_two_epochs : spectrumEntries (Descent.Core.pairedEpochCount 2) = 1 := by
  decide

/-- **Three epochs are cube-root stable.** -/
theorem spectrumEntries_three_epochs : spectrumEntries (Descent.Core.pairedEpochCount 3) = 3 := by
  decide

/-- **Four epochs are fifth-root stable.** -/
theorem spectrumEntries_four_epochs : spectrumEntries (Descent.Core.pairedEpochCount 4) = 5 := by
  decide

/-! #### Drift invisible to genotype is irreducible by any amount of genotyping

The defect splits into a part measurable with respect to the genotype-distribution structure and a
part orthogonal to it. Only the first is attackable by more reference panels, deeper sequencing,
or better ancestry inference: the second is invisible to every genotype-measurable statistic, so
no quantity of genotype data touches it.

The witness is two ancestries whose genotype distributions coincide -- so any genotype-based
method assigns them the same value, and any inferred ancestry coordinate merges them -- carrying
different conditional risks. At the genotype-visible resolution the defect is zero. The true
defect is positive. The gap is irreducible.

This is the formal shape of the binding empirical objection to the whole extrapolation programme.
Harpak and colleagues report that variation in individual-level prediction accuracy is only weakly
predicted by genetic distance and is explained comparably well by socioeconomic measures. If that
is so, a large part of the drift field sits in exactly the orthogonal component witnessed here,
and the fill-distance machinery -- which prices extrapolation in a metric induced by the GENOTYPE
marginals -- is pricing the wrong thing. More diverse genotyping shrinks the attackable part and
leaves the rest untouched.

The theory gives the accounting and not the causal decomposition. It says which portion of a
measured portability gap is in principle reachable by genetic data; it does not say how large
that portion is, and the empirical claim is that it may be the smaller one.
-/

/-- Two ancestries indistinguishable by genotype: any genotype-measurable statistic, and hence any
inferred ancestry coordinate, assigns them the common value.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a nonidentifiability witness. -/
noncomputable def genotypeVisibleRisk : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Their true conditional risks, which differ.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a nonidentifiability witness. -/
noncomputable def trueRiskUnderSocialDrift : Fin 2 → ℝ := ![4 / 5, 1 / 5]

/-- The genotype-visible witness deliberately reuses the earlier coarsened risk field. -/
theorem genotypeVisibleRisk_eq_binnedRiskByAncestry :
    genotypeVisibleRisk = binnedRiskByAncestry := by
  funext i
  fin_cases i <;> norm_num [genotypeVisibleRisk, binnedRiskByAncestry]

/-- The genotype-visible witness is also the earlier uniform two-ancestry vector. -/
theorem genotypeVisibleRisk_eq_uniformTwoWeights :
    genotypeVisibleRisk = uniformTwoWeights := by
  funext i
  fin_cases i <;> norm_num [genotypeVisibleRisk, uniformTwoWeights]

/-- The social-drift witness deliberately reuses the earlier fine risk field. -/
theorem trueRiskUnderSocialDrift_eq_fineRiskByAncestry :
    trueRiskUnderSocialDrift = fineRiskByAncestry := by
  funext i
  fin_cases i <;> norm_num [trueRiskUnderSocialDrift, fineRiskByAncestry]

/-- The same reversed conditional is also the repository's post-hoc-recalibration witness. -/
theorem trueRiskUnderSocialDrift_eq_reorderTarget :
    trueRiskUnderSocialDrift = reorderTarget := by
  funext i
  fin_cases i <;> norm_num [trueRiskUnderSocialDrift, reorderTarget]

/-- **Genotype data sees no obstruction here.** -/
theorem genotypeVisible_driftDefect_zero :
    driftDefect ancestryPairWeights genotypeVisibleRisk = 0 := by
  unfold driftDefect pooledConditional ancestryPairWeights genotypeVisibleRisk
  norm_num [Fin.sum_univ_two]

/-- **The obstruction is nonetheless there.** -/
theorem trueRisk_driftDefect_pos :
    0 < driftDefect ancestryPairWeights trueRiskUnderSocialDrift := by
  unfold driftDefect pooledConditional ancestryPairWeights trueRiskUnderSocialDrift
  norm_num [Fin.sum_univ_two]

/-- **So no amount of genotyping closes it.** Every genotype-measurable statistic takes the same
value on the two ancestries, so every predictor built from genotype data alone assigns them the
same risk and carries the full gap. Diversifying the reference panel moves the attackable
component and cannot move this one. -/
theorem genotype_invisible_drift_irreducible :
    driftDefect ancestryPairWeights genotypeVisibleRisk
      < driftDefect ancestryPairWeights trueRiskUnderSocialDrift := by
  rw [genotypeVisible_driftDefect_zero]
  exact trueRisk_driftDefect_pos

/-! #### A decision loss wants a median, not the mean that meta-analysis estimates

Under squared loss the single best target is the ancestry-weighted MEAN, which is what a
fixed-effects meta-analysis across cohorts estimates. Under a threshold decision loss it is a
weighted MEDIAN of the ancestry-conditional risks. When the ancestry distribution is skewed --
and a GWAS-derived `π` is heavily skewed -- these are different numbers, so the quantity the
literature estimates is not the quantity a deployment decision needs.

The witness below has three ancestries at weights `2/5, 3/10, 3/10` carrying risks `0, 0, 1`. The
weighted mean is `3/10`; the weighted median is `0`. Absolute loss at `0` is `3/10`, and at the
mean it is `21/50` -- strictly worse. The pooled mean is not merely a different summary, it is
suboptimal for the decision.
-/

/-- A skewed ancestry distribution.

Empirical status: NOT AN EMPIRICAL CLAIM -- these rational weights define a proof witness. -/
noncomputable def skewedAncestryWeights : Fin 3 → ℝ := ![2 / 5, 3 / 10, 3 / 10]

/-- Ancestry-conditional risks at the operating point.

Empirical status: NOT AN EMPIRICAL CLAIM -- these values define a proof witness. -/
noncomputable def skewedAncestryRisks : Fin 3 → ℝ := ![0, 0, 1]

/-- Ancestry-weighted absolute loss, the criterion a threshold decision induces. -/
noncomputable def absoluteLoss {m : ℕ} (π η : Fin m → ℝ) (v : ℝ) : ℝ :=
  ∑ i, π i * |η i - v|

/-- Reference evaluation at two atoms with distinct masses and locations. -/
theorem absoluteLoss_at_reference_point :
    absoluteLoss (![1, 3] : Fin 2 → ℝ) (![2, 5] : Fin 2 → ℝ) 4 = 5 := by
  norm_num [absoluteLoss, Fin.sum_univ_two]

/-- **The pooled mean is `3/10`.** -/
theorem skewedAncestry_pooled_mean :
    pooledConditional skewedAncestryWeights skewedAncestryRisks = 3 / 10 := by
  unfold pooledConditional skewedAncestryWeights skewedAncestryRisks
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The median beats the mean under absolute loss.**

So the target a decision loss wants is not the one a meta-analysis reports. Estimating the pooled
effect and deploying it at a threshold optimises the wrong functional, and the gap widens with the
skew of the ancestry distribution. -/
theorem median_beats_mean_under_absolute_loss :
    absoluteLoss skewedAncestryWeights skewedAncestryRisks 0
      < absoluteLoss skewedAncestryWeights skewedAncestryRisks (3 / 10) := by
  unfold absoluteLoss skewedAncestryWeights skewedAncestryRisks
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, abs_of_nonneg, abs_of_nonpos]

/-! #### Unequal per-ancestry sample sizes inflate the effective resolution

Splitting the index into `k` cells and estimating within each costs an estimation term
proportional to the EFFECTIVE cell count `N * ∑ πᵢ / nᵢ`, not to `k`.  For equal cell
weights this is minimized by equal allocation and any departure costs a harmonic factor.  For
unequal weights the square-root law proved below replaces proportional allocation.

The equal-weight two-cell case is stated first: the penalty is at least four, attained by equal
allocation, and grows without bound as the split becomes lopsided.  The subsequent theorems then
separate posterior-weighted and worst-ancestry recruitment objectives.
-/

/-- **The harmonic penalty for unequal allocation.** -/
theorem harmonic_allocation_penalty (n₁ n₂ : ℝ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    4 ≤ (n₁ + n₂) * (1 / n₁ + 1 / n₂) := by
  have hexp : (n₁ + n₂) * (1 / n₁ + 1 / n₂) = 2 + n₁ / n₂ + n₂ / n₁ := by
    field_simp
    ring
  rw [hexp]
  have hkey : 2 ≤ n₁ / n₂ + n₂ / n₁ := by
    rw [div_add_div _ _ (ne_of_gt h₂) (ne_of_gt h₁), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (n₁ - n₂)]
  linarith

/-- **Equal allocation attains it**, so the bound is the exact cost of departing from
proportional design rather than a loose estimate. -/
theorem harmonic_allocation_penalty_equal (n : ℝ) (h : 0 < n) :
    (n + n) * (1 / n + 1 / n) = 4 := by
  field_simp
  ring

/-! #### Recruitment depends on the deployment objective

The preceding equal-weight witness does not justify proportional recruitment for unequal ancestry
weights.  For the stated `L²(π)` estimation term `∑ πᵢ / nᵢ`, the exact two-cell lower
bound is attained by square-root (Neyman) allocation, `nᵢ ∝ √πᵢ`.  A worst-ancestry
objective is different again: with equal per-sample noise it is minimized by equal precision,
independently of the deployment mixture.  Thus an objective must be fixed before a recruitment
rule can be called optimal.
-/

/-- The two-cell contribution to posterior-weighted mean squared estimation error.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the algebraic objective being optimized. -/
noncomputable def twoCellL2EstimationPenalty (p n₁ n₂ : ℝ) : ℝ :=
  p / n₁ + (1 - p) / n₂

/-- **twoCellL2EstimationPenalty at its junk point, named.** An empty first cell makes its
estimation penalty unbounded. The divisor is zero, that term vanishes, and the penalty reduces
to the second cell alone -- so a design that samples one ancestry not at all is charged only for
the ancestry it did sample. Consumers must exclude the argument that makes the guard vanish. -/
theorem twoCellL2EstimationPenalty_empty_first_cell_is_junk (p n₂ : ℝ) :
    twoCellL2EstimationPenalty p 0 n₂ = (1 - p) / n₂ := by
  unfold twoCellL2EstimationPenalty
  simp

/-- The two-cell worst-ancestry estimation error when both cells have equal observation noise.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the algebraic objective being optimized. -/
noncomputable def twoCellWorstEstimationPenalty (n₁ n₂ : ℝ) : ℝ :=
  max (1 / n₁) (1 / n₂)

/-- **twoCellWorstEstimationPenalty at its junk point, named.** Two empty cells give an unbounded
worst-case estimation penalty. Both reciprocals are junk-zero and the maximum is `0`: the best
possible worst case, certified for a design with no data in either cell. Consumers must guard
the argument that makes the divisor vanish. -/
theorem twoCellWorstEstimationPenalty_empty_cells_is_junk :
    twoCellWorstEstimationPenalty 0 0 = 0 := by
  unfold twoCellWorstEstimationPenalty
  simp

/-- **The exact `L²(π)` recruitment bound.**  Its right side is the total sample size times
the weighted estimation penalty.  Equality holds precisely on the square-root allocation ray. -/
theorem twoCell_l2_allocation_lower_bound (p n₁ n₂ : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (Real.sqrt p + Real.sqrt (1 - p)) ^ 2 ≤
      (n₁ + n₂) * twoCellL2EstimationPenalty p n₁ n₂ := by
  have hsqp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp₀
  have hsqc : Real.sqrt (1 - p) ^ 2 = 1 - p :=
    Real.sq_sqrt (sub_nonneg.mpr hp₁)
  have hscaled :
      ((n₁ + n₂) * twoCellL2EstimationPenalty p n₁ n₂ -
          (Real.sqrt p + Real.sqrt (1 - p)) ^ 2) * (n₁ * n₂) =
        (Real.sqrt p * n₂ - Real.sqrt (1 - p) * n₁) ^ 2 := by
    unfold twoCellL2EstimationPenalty
    field_simp [ne_of_gt hn₁, ne_of_gt hn₂]
    ring_nf
    rw [hsqp, hsqc]
    ring
  nlinarith [sq_nonneg (Real.sqrt p * n₂ - Real.sqrt (1 - p) * n₁),
    mul_pos hn₁ hn₂]

/-- **Worst-ancestry recruitment has a different lower bound.**  Equal precision minimizes the
largest cell variance; deployment prevalence does not enter this objective. -/
theorem twoCell_worst_allocation_lower_bound (n₁ n₂ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    2 / (n₁ + n₂) ≤ twoCellWorstEstimationPenalty n₁ n₂ := by
  rcases le_total n₁ n₂ with h₁₂ | h₂₁
  · apply le_trans _ (le_max_left _ _)
    rw [div_le_div_iff₀ (add_pos hn₁ hn₂) hn₁]
    nlinarith
  · apply le_trans _ (le_max_right _ _)
    rw [div_le_div_iff₀ (add_pos hn₁ hn₂) hn₂]
    nlinarith

/-- Equal recruitment attains the worst-ancestry lower bound exactly. -/
theorem twoCell_worst_allocation_equal (n : ℝ) (hn : 0 < n) :
    twoCellWorstEstimationPenalty n n = 2 / (n + n) := by
  unfold twoCellWorstEstimationPenalty
  rw [max_self]
  field_simp
  norm_num

/-- **Proportional recruitment can be strictly suboptimal even for the `L²(π)` objective.**
At deployment weight `4/5`, both allocations below use `15n` samples.  The square-root allocation
`10n:5n` has lower weighted estimation error than the proportional allocation `12n:3n`. -/
theorem squareRoot_allocation_beats_proportional (n : ℝ) (hn : 0 < n) :
    twoCellL2EstimationPenalty (4 / 5) (10 * n) (5 * n) <
      twoCellL2EstimationPenalty (4 / 5) (12 * n) (3 * n) := by
  unfold twoCellL2EstimationPenalty
  field_simp [ne_of_gt hn]
  nlinarith

/-! #### Resolution monotonicity in general, not just on a witness

The merge witness shows coarsening loses drift energy in one instance; the atomic split shows
exactly what a two-way merge costs. The general statement is that a CELL of any size, collapsed
to its weighted mean, retains at most the energy it had, and the shortfall is the within-cell
dispersion.

This is weighted Cauchy-Schwarz, and it is what makes resolution monotone under arbitrary
refinement rather than only under pairwise merges: any coarsening is a composition of cell
collapses, and each one loses energy.

Biologically it says the same thing at every granularity. A deployment that calibrates on
continental groupings resolves at most what one calibrating on finer ancestry resolves, whatever
the groupings are, and the deficit is the spread of risk inside each grouping. -/
theorem cell_collapse_loses_energy {m : ℕ} (s : Finset (Fin m)) (π w : Fin m → ℝ)
    (hπ : ∀ i, 0 ≤ π i) :
    (∑ i ∈ s, π i * w i) ^ 2 ≤ (∑ i ∈ s, π i) * ∑ i ∈ s, π i * w i ^ 2 := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i ↦ Real.sqrt (π i)) (fun i ↦ Real.sqrt (π i) * w i)
  have hprod : ∀ i ∈ s, Real.sqrt (π i) * (Real.sqrt (π i) * w i) = π i * w i := by
    intro i _
    rw [← mul_assoc, Real.mul_self_sqrt (hπ i)]
  have hsq1 : ∀ i ∈ s, Real.sqrt (π i) ^ 2 = π i := by
    intro i _
    rw [Real.sq_sqrt (hπ i)]
  have hsq2 : ∀ i ∈ s, (Real.sqrt (π i) * w i) ^ 2 = π i * w i ^ 2 := by
    intro i _
    rw [mul_pow, Real.sq_sqrt (hπ i)]
  calc (∑ i ∈ s, π i * w i) ^ 2
      = (∑ i ∈ s, Real.sqrt (π i) * (Real.sqrt (π i) * w i)) ^ 2 := by
        rw [Finset.sum_congr rfl hprod]
    _ ≤ (∑ i ∈ s, Real.sqrt (π i) ^ 2) * ∑ i ∈ s, (Real.sqrt (π i) * w i) ^ 2 := key
    _ = (∑ i ∈ s, π i) * ∑ i ∈ s, π i * w i ^ 2 := by
        rw [Finset.sum_congr rfl hsq1, Finset.sum_congr rfl hsq2]

/-- **A cell of unit weight retains at most its energy.** The normalised form, which is the one
that composes: collapsing a cell to its mean can only lose. -/
theorem cell_collapse_loses_energy_normalised {m : ℕ} (s : Finset (Fin m)) (π w : Fin m → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hs : ∑ i ∈ s, π i = 1) :
    (∑ i ∈ s, π i * w i) ^ 2 ≤ ∑ i ∈ s, π i * w i ^ 2 := by
  have h := cell_collapse_loses_energy s π w hπ
  rwa [hs, one_mul] at h

/-! #### Which decision losses survive the drift

A threshold decision loss at `τ` charges only for outcomes on the wrong side of `τ`. If every
ancestry-specific risk lies on one side of the threshold, the drift moves no decision and the
loss is unaffected: the score is simultaneously optimal for that loss at every ancestry. If the
threshold falls strictly inside the range of ancestry-specific risks, no single prediction is
optimal for all of them.

That is the exact criterion. A clinical threshold set outside the spread of ancestry-specific
risks transports; one set inside it does not, however well the score is calibrated.
-/

/-- The part of the threshold regret charged to ancestries above the threshold. -/
noncomputable def aboveThresholdMass {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, π i * max (η i - τ) 0

/-- **A threshold above every ancestry-specific risk is untouched by the drift.** -/
theorem aboveThresholdMass_eq_zero {m : ℕ} (π η : Fin m → ℝ) (τ : ℝ)
    (h : ∀ i, η i ≤ τ) :
    aboveThresholdMass π η τ = 0 := by
  unfold aboveThresholdMass
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [max_eq_right (by linarith [h i])]
  ring

/-- **A threshold strictly inside the drift range is not.** With two ancestries at risks `0` and
`1` and a threshold at one half, the above-threshold mass is positive, so the decision the loss
recommends differs between ancestries and no single prediction serves both. -/
theorem aboveThresholdMass_pos_inside :
    0 < aboveThresholdMass uniformTwoWeights twoAncestryConditional (1 / 2) := by
  unfold aboveThresholdMass uniformTwoWeights twoAncestryConditional
  norm_num [Fin.sum_univ_two]

/-! #### Why a threshold inside the drift range admits no single decision

`aboveThresholdMass_eq_zero` and `belowThresholdMass_eq_zero` say a threshold outside the range of
ancestry-specific risks is untouched. The reason a threshold INSIDE the range cannot be served is
sharper than "the regret is positive": the two ancestries fall on opposite sides of it, so the
decision the loss recommends is literally different at each, and no single prediction is the
right decision at both.

That is the deployment question, stated exactly. It is not "is the score calibrated" but "does
the spread of ancestry-specific risk at my operating point straddle my clinical cutoff". The
first is an aggregate diagnostic; the second is decidable from the fitted per-ancestry curves and
is the one that determines whether the cutoff transports. -/
theorem threshold_inside_separates_ancestries (τ : ℝ) (h0 : 0 < τ) (h1 : τ < 1) :
    twoAncestryConditional 0 < τ ∧ τ < twoAncestryConditional 1 := by
  have e0 : twoAncestryConditional 0 = 0 := by unfold twoAncestryConditional; norm_num
  have e1 : twoAncestryConditional 1 = 1 := by unfold twoAncestryConditional; norm_num
  rw [e0, e1]
  exact ⟨h0, h1⟩

/-- **A threshold outside the range does not separate them.** Both ancestries sit on the same side,
so the decision is the same at each and the cutoff transports unchanged. The pair with the theorem
above is the survival criterion in decision form. -/
theorem threshold_outside_does_not_separate (τ : ℝ) (h : 1 < τ) :
    twoAncestryConditional 0 < τ ∧ twoAncestryConditional 1 < τ := by
  have e0 : twoAncestryConditional 0 = 0 := by unfold twoAncestryConditional; norm_num
  have e1 : twoAncestryConditional 1 = 1 := by unfold twoAncestryConditional; norm_num
  rw [e0, e1]
  exact ⟨by linarith, h⟩

/-- **Equal risks across ancestries leave nothing to obstruct.** The defect vanishes exactly when
the conditional does not drift, which is the other degenerate case worth naming beside
`pointMass_driftDefect_zero`: there the index was determined by the covariate, here the index
exists but carries no risk variation. Either way the framework says nothing, and a deployment
should know which of the two it is in. -/
theorem constantConditional_driftDefect_zero {m : ℕ} (π : Fin m → ℝ) (c : ℝ)
    (hπ : ∑ i, π i = 1) :
    driftDefect π (fun _ ↦ c) = 0 := by
  have hpool : pooledConditional π (fun _ ↦ c) = c := by
    unfold pooledConditional
    rw [← Finset.sum_mul, hπ, one_mul]
  unfold driftDefect
  rw [hpool]
  simp

/-! #### The score's own distribution cannot see how it aligns with ancestry

`pooledConditional_does_not_identify_drift` says the pooled conditional cannot see drift across
ancestries. This is the same failure one layer up, in the metric: the DISTRIBUTION of a score's
values across a population does not determine how those values are arranged relative to ancestry
distance.

Three ancestries at metric positions `0, 1, 3`, equally weighted, and a score taking the values
`0, 1, 2`. Permuting which ancestry receives which value leaves the score's distribution exactly
unchanged, and the ancestry geometry exactly unchanged, while the alignment energy moves from
`10/3` to `2`. So no functional of the score's marginal distribution -- not its mean, variance,
quantiles, or full histogram -- can detect alignment.
-/

/-- Three ancestries at positions `0`, `1`, `3` on the line.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite counterexample. -/
noncomputable def ancestryPosition : Fin 3 → ℝ := ![0, 1, 3]

/-- The third ancestry occupies position three in the finite counterexample. -/
@[simp] theorem ancestryPosition_two : ancestryPosition 2 = 3 := rfl

/-- Distance between two ancestries on the line.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the metric of a finite counterexample. -/
noncomputable def threeAncestryDistance : Fin 3 → Fin 3 → ℝ :=
  fun i j ↦ |ancestryPosition i - ancestryPosition j|

/-- A score assigning values `0, 1, 2` to the three ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this reuses the finite drift witness. -/
noncomputable def ancestryScore : Fin 3 → ℝ := threeAncestryConditional

/-- The same three values, permuted between the ancestries.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite counterexample. -/
noncomputable def ancestryScoreSwapped : Fin 3 → ℝ := ![0, 2, 1]

/-- Dirichlet-type energy coupling ancestry distance to score differences.

Empirical status: NOT AN EMPIRICAL CLAIM -- this defines the counterexample's energy. -/
noncomputable def ancestryAlignmentEnergy (m : Fin 3 → ℝ) : ℝ :=
  (1 / 9) * ∑ i, ∑ j, threeAncestryDistance i j * (m i - m j) ^ 2

/-- **The two scores have the same marginal**, being the same values permuted. -/
theorem ancestryScoreSwapped_is_permutation :
    ancestryScoreSwapped = ancestryScore ∘ ![0, 2, 1] := by
  funext i
  fin_cases i <;> rfl

/-- **The aligned arrangement's energy.** -/
theorem ancestryAlignmentEnergy_score : ancestryAlignmentEnergy ancestryScore = 10 / 3 := by
  unfold ancestryAlignmentEnergy threeAncestryDistance ancestryPosition ancestryScore
  simp only [Fin.sum_univ_three, threeAncestryConditional, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- **The permuted arrangement's energy**, against the same metric and the same score values.

With `ancestryScoreSwapped_is_permutation` this is the separation: identical ancestry geometry,
identical score distribution, different alignment. -/
theorem ancestryAlignmentEnergy_swapped : ancestryAlignmentEnergy ancestryScoreSwapped = 2 := by
  unfold ancestryAlignmentEnergy threeAncestryDistance ancestryPosition ancestryScoreSwapped
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-! #### A rare ancestry is not proportionately harmless

The drift defect is an `L²` quantity, and the functional built from it moves like the SQUARE ROOT
of a subgroup's mass, not like the mass. So the standard dismissal -- "that ancestry is one per
cent of the sample, so it can move a global statistic by at most one per cent" -- is wrong by a
square root, and wrong in the direction that understates the damage.

Concretely: a population that is `1 - ε` one ancestry and `ε` another, whose conditionals differ
by one, has drift defect `ε (1 - ε)`. The mixture was perturbed by `ε`; the calibration functional
`√defect` moved by `√(ε(1-ε)) ≍ √ε`. No Lipschitz constant in the mass exists, and the theorem
below says so in the form that needs no square roots: the defect strictly exceeds the square of
the rare group's share.

This is the exact mechanism behind the failure of any uniform-Lipschitz claim for a variance-type
decoration functional: on the exceptional set of mass `ε` the values differ by `O(1)`, which
contributes `O(ε)` to a SQUARED quantity and therefore `O(√ε)` to the functional itself.
-/

/-- A population that is `1 - ε` one ancestry and `ε` another.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed two-point weight. -/
noncomputable def rareAncestryWeights (ε : ℝ) : Fin 2 → ℝ := ![1 - ε, ε]

/-- The rare ancestry carries a conditional risk one unit away from the common one.

Empirical status: NOT AN EMPIRICAL CLAIM -- this reuses the canonical two-ancestry witness. -/
noncomputable def rareAncestryRisks : Fin 2 → ℝ := twoAncestryConditional

/-- **The rare ancestry's defect, exactly.** -/
theorem rareAncestry_driftDefect_eq (ε : ℝ) :
    driftDefect (rareAncestryWeights ε) rareAncestryRisks = ε * (1 - ε) := by
  unfold driftDefect pooledConditional rareAncestryWeights rareAncestryRisks
    twoAncestryConditional
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **And it exceeds the square of the rare group's share**, for any share below one half.

Read as a rate: the defect is `Θ(ε)` where a Lipschitz response to an `ε` perturbation of the
mixture would be `O(ε²)`. The calibration functional is the square root of this, so it moves like
`√ε`. A subgroup at one per cent of the sample moves it by ten per cent. -/
theorem rareAncestry_defect_exceeds_share_squared (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    ε ^ 2 < driftDefect (rareAncestryWeights ε) rareAncestryRisks := by
  rw [rareAncestry_driftDefect_eq]
  nlinarith

/-- **And the converse**, which the "exactly when" above asserts and the theorem before it does
not supply. If every ancestry carries positive weight and the defect vanishes, then every
ancestry's conditional equals the pooled one -- so the defect is zero precisely on the
non-drifting conditionals, and a zero defect is evidence about the biology rather than an
artefact of the weighting.

The positivity hypothesis is needed and is not decoration: an ancestry of weight zero contributes
nothing to the defect and its conditional is unconstrained. -/
theorem constantConditional_of_driftDefect_zero {m : ℕ} (π η : Fin m → ℝ)
    (hpos : ∀ i, 0 < π i) (h : driftDefect π η = 0) (i : Fin m) :
    η i = pooledConditional π η := by
  unfold driftDefect at h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ π j * (η j - pooledConditional π η) ^ 2 :=
    fun j _ ↦ mul_nonneg (hpos j).le (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  have hsq : (η i - pooledConditional π η) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (hpos i).ne'
  have hx : η i - pooledConditional π η = 0 := by
    exact sq_eq_zero_iff.mp hsq
  linarith

/-- **The gap is bounded by the two sensitivities it compares.** Symmetry and the vanishing
criterion are shared by every positive multiple of this distance; the triangle bound is not,
so it is the one that fixes the multiple at one. -/
theorem sensitivityPortabilityGap_le_add_abs (a b : ℝ) :
    sensitivityPortabilityGap a b ≤ |a| + |b| := by
  unfold sensitivityPortabilityGap
  calc |b - a| ≤ |b| + |a| := abs_sub b a
    _ = |a| + |b| := by ring

/-- Absolute portability gap for PPV between source and target prevalences. -/
noncomputable def ppvPortabilityGap
    (sensitivity specificity prevalenceSource prevalenceTarget : ℝ) : ℝ :=
  |metricPPV sensitivity specificity prevalenceTarget -
    metricPPV sensitivity specificity prevalenceSource|

/-- **Equal prevalences leave no gap, whatever the operating point.**

RENAMED off `_at_reference_point`. The old name claimed to pin the body's scale,
and a statement of `0` cannot: `c · 0 = 0` for every `c`, so every rescaling of
this gap satisfies it. The vanishing is nonetheless real content — it says the
gap is a function of the DIFFERENCE between the two prevalences and not of their
level, which is exactly the property that makes it a portability gap rather than
a second copy of the PPV.

Note the quantifiers are what give it its strength: it holds for every
`sensitivity` and `specificity`, so it also says the operating point cannot
manufacture a gap on its own. That is worth keeping and is not what a reference
evaluation is for.

The scale is pinned separately, by `ppvPortabilityGap_at_reference_point` below,
which is what this theorem cannot do. -/
theorem ppvPortabilityGap_self (sensitivity specificity prevalence : ℝ) :
    ppvPortabilityGap sensitivity specificity prevalence prevalence = 0 := by
  unfold ppvPortabilityGap
  simp

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ppvPortabilityGap_at_reference_point :
    ppvPortabilityGap 1 (1 / 2) (1 / 5) (1 / 2) = 1 / 3 ∧
      ppvPortabilityGap 1 (1 / 2) (1 / 2) (1 / 5) = 1 / 3 := by
  constructor <;>
    · unfold ppvPortabilityGap metricPPV
      norm_num [abs_of_nonneg, abs_of_nonpos]

/-- **The gap is bounded by the two predictive values it compares.** Strict positivity under a
prevalence shift is shared by every positive multiple of this distance; the triangle bound is
not, so it is what fixes the multiple at one. -/
theorem ppvPortabilityGap_le_add_abs
    (sensitivity specificity prevalenceSource prevalenceTarget : ℝ) :
    ppvPortabilityGap sensitivity specificity prevalenceSource prevalenceTarget
      ≤ |metricPPV sensitivity specificity prevalenceTarget|
        + |metricPPV sensitivity specificity prevalenceSource| := by
  unfold ppvPortabilityGap
  exact abs_sub _ _

/-- **PPV is strictly increasing in prevalence.**
    At fixed sensitivity and specificity, higher prevalence yields higher PPV.
    This is the concrete base-rate sensitivity of PPV. -/
theorem ppv_increases_with_prevalence
    (se sp K₁ K₂ : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_K1 : 0 < K₁) (h_K1' : K₁ < 1)
    (h_K2' : K₂ < 1)
    (h_order : K₁ < K₂) :
    metricPPV se sp K₁ < metricPPV se sp K₂ := by
  unfold metricPPV
  have h_d1 : 0 < se * K₁ + (1 - sp) * (1 - K₁) := by nlinarith
  have h_d2 : 0 < se * K₂ + (1 - sp) * (1 - K₂) := by nlinarith
  have h_d1_ne : se * K₁ + (1 - sp) * (1 - K₁) ≠ 0 := ne_of_gt h_d1
  have h_d2_ne : se * K₂ + (1 - sp) * (1 - K₂) ≠ 0 := ne_of_gt h_d2
  field_simp [h_d1_ne, h_d2_ne]
  nlinarith [mul_pos h_se (sub_pos.mpr h_sp1)]

/-- **The sensitivity gap between a use case and itself is zero, definitionally.**

`sensitivityPortabilityGap` takes the source and target sensitivities as two separate
arguments, so passing the same `se` twice gives `|se - se|`. **Keep it as its own lemma
rather than folding it into the conclusion of `ppv_gap_pos_under_prevalence_shift`
below**, where `sensitivityPortabilityGap se se` would read as a *proved* consequence of a
prevalence shift rather than as the definitional zero it is. Nothing about prevalence enters here,
and nothing can: prevalence is not an
argument of `sensitivityPortabilityGap`. -/
@[simp] theorem sensitivityPortabilityGap_self (se : ℝ) :
    sensitivityPortabilityGap se se = 0 := by
  unfold sensitivityPortabilityGap
  simp

/-- **A pure prevalence shift moves PPV by a strictly positive amount.**

This is the whole empirical content of the metric split: at fixed sensitivity and
specificity, PPV is prevalence-dependent and its portability gap cannot be zero. The
companion claim — that sensitivity's gap *is* zero — is not proved here and is not
provable here; it is `sensitivityPortabilityGap_self`, an identity, and holds because
sensitivity is defined without reference to prevalence. Keeping the two apart is the
point: one is a fact about `metricPPV`, the other is a fact about an argument list.

**Do not restate this as `sensitivityPortabilityGap se se < ppvPortabilityGap …`.** That
is this statement with `0` spelled as `|se - se|`, and it reads as a comparison of two
measured gaps when only one side is measured at all. -/
theorem ppv_gap_pos_under_prevalence_shift
    (se sp K_source K_target : ℝ)
    (h_se : 0 < se) (h_sp1 : sp < 1)
    (h_Ks : 0 < K_source) (h_Ks' : K_source < 1)
    (h_Kt' : K_target < 1)
    (h_order : K_source < K_target) :
    0 < ppvPortabilityGap se sp K_source K_target := by
  have h_ppv :
      metricPPV se sp K_source < metricPPV se sp K_target :=
    ppv_increases_with_prevalence
      se sp K_source K_target h_se h_sp1 h_Ks h_Ks' h_Kt' h_order
  have h_gap_pos :
      0 < metricPPV se sp K_target - metricPPV se sp K_source := sub_pos.mpr h_ppv
  unfold ppvPortabilityGap
  rw [abs_of_pos h_gap_pos]
  exact h_gap_pos

/-- **Number needed to screen (NNS) portability.**
    NNS = 1/PPV. If PPV drops, NNS increases → more individuals
    need screening for each true positive. -/
theorem nns_increases_with_ppv_drop
    (ppv₁ ppv₂ : ℝ)
    (h_ppv₂ : 0 < ppv₂)
    (h_drop : ppv₂ < ppv₁) :
    1 / ppv₁ < 1 / ppv₂ :=
  div_lt_div_of_pos_left one_pos h_ppv₂ h_drop

/-! **F1 score captures precision-recall balance.**
`F1 = 2 × PPV × sensitivity / (PPV + sensitivity)`, and F1 portability reflects
both precision and recall portability.

`Core.f1Score` is the definition and `Core.f1_le_one` the bound; both moved down with the
rest of the clinical family. Do not restate the formula here -- its `Empirical status:
UNTESTED` marker belongs with that one definition, and the reason this file no longer holds
the theorem is that holding it cost a `Portability -> Program` import. -/

end PrecisionRecall

end Descent.Portability
