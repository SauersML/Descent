/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Moments

/-!
# Core: the decision half of the metric family

**Depth 3. Imports `Core.Moments` and, through it, `Core.Parameters`, `Core.Fst`,
`Core.Ratios` and `Core.Scaling`. Nothing else from this corpus.**

## What this file is for

`Core.Moments` carries the demography-to-metric spine
`PopGenParameters → fstEquilibrium → momentsUnderDrift → <metric>`, and the metrics it
reaches are the SECOND-MOMENT ones: `R²`, a calibration slope, a mean squared error, a
Brier score, an AUC argument, a portability ratio. Those are the numbers a methods paper
reports.

They are not the numbers a clinic acts on. A screening programme is a THRESHOLD on a
score, and what it produces is a positive predictive value, a negative predictive value,
a net benefit at an exchange rate between a missed case and an unnecessary treatment, and
a reclassification index against whatever it was doing before. The corpus has all of
those, in `Portability/ClinicalUtilityFairness`, `Portability/PGSCalibrationTheory/
DecisionImplications` and `Portability/MetricSpecificPortability/PrecisionRecall`, at
depths in the high twenties and low thirties -- and every one of them takes a sensitivity
and a specificity as FREE REALS. Not one is reachable from a demography. A corpus that
can prove migration raises `R²` and cannot say what that does to a predictive value has
stopped one step short of the claim it exists to make.

This file is that step. It is not a second copy of those definitions: it is the same
quantities restated on the objects the spine actually produces, so that they compose.
The bodies below route through `Core.share`, `Core.ratio`, `Core.sum`, `Core.difference`
and `Core.midpoint` for the same reason everything else in `Core` does -- a second
handwritten copy of a body is a copied derivation, and a copied derivation drifts. The
existing high-depth definitions should come to CALL these; that edit is not made here,
because it touches thirty modules and belongs with a build.

## The one thing a second-moment interface cannot do

A sensitivity and a specificity are not functions of `(Var S, Cov(S,Y), Var Y)`. They are
functions of the moments AND of a distributional assumption -- under a liability-threshold
model, of `Φ` evaluated at a standardised threshold. `Core` has no `Φ`, deliberately:
`Core.Moments.aucArgument` records the same limitation and answers it by writing the
ARGUMENT of the normal integral rather than a wrong closed form for it.

The answer taken here is different and, for this family, sharper. What every clinical
metric needs from the distribution is not `Φ` itself but the single fact that a better
discriminating score has a better operating point. `OperatingPointLaw` below is exactly
that fact and nothing more: a map from a discrimination level to a sensitivity and a
specificity, required to be strictly increasing in both. Every spine theorem in this file
is quantified over ALL such laws.

That is weaker than naming the Gaussian law, and it is the honest strength. The
conclusions -- more migration means a higher predictive value, a longer split means a
lower net benefit, deploying across a differentiation reclassifies patients the wrong way
-- do not depend on normality, and stating them under a hypothesis they do not need would
be claiming a Gaussian result for a fact that holds without one.
`Portability.ClinicalUtilityFairness.sensFromR2` and `specFromR2` are one instance of
this structure; the theorem exhibiting them as an `OperatingPointLaw` belongs in that
file, where `Φ` is.

## What is NOT here, and where it is

The TRANSIENT route. `Core.Moments` reaches its metric through `fstEquilibrium`, the
level a migration-mutation balance settles at, and through `fstFromTau`, the clean-split
law. The corpus's approach-to-equilibrium coordinate is
`Descent.Core.PopGenParameters.fstTransientAt`, and despite that name it is NOT in `Core`:
it is declared with `_root_.` into this record's namespace from
`Descent/Portability/PortabilityDrift/Generational.lean`, at depth thirty, and its body
calls `PopGen.fstTransientDecayFromScaled`. `Core` cannot reach it, and the name is taken,
so this file cannot define it either.

What this file does instead is the generation-indexed reading of the split law,
`fstAtGeneration`, which IS reachable, is Hudson by the corpus's standing rule, and
crosses the equilibrium level at a generation the record's own parameters determine. The
section at the end says what that does and does not establish about the two routes.

## Empirical status

Every definition here is a SHAPE. A predictive value is what it is given a sensitivity, a
specificity and a prevalence; there is no measurement that could bear on the arithmetic.
What carries an empirical status is `PopGenParameters.fstEquilibrium`, which these
theorems read through `Core.Moments.deployedR2`, and it states its own.
-/

namespace Descent.Core

/-! ### Two monotonicity laws for `share`

`Core.share a b = a / (a + b)` is the shape of every predictive value in this file: a
part against itself plus a competing part. Both the predictive values move by these two
lemmas and by nothing else, which is why they are stated once rather than re-derived at
each metric.

They live here rather than beside `share` in `Core.Ratios` because `Core.Ratios` is depth
0 and everything in the corpus is below it. These are used by this file alone, and a
lemma that breaks one file is not a lemma that breaks the corpus. -/

/-- **A bigger part is a bigger share**, against a fixed competing part. Strict, and it
needs the competing part to be strictly positive: with nothing to compete against, every
share is one and the map is constant. -/
theorem share_lt_share_of_lt_left (a₁ a₂ b : ℝ) (ha : 0 ≤ a₁) (hb : 0 < b) (h : a₁ < a₂) :
    share a₁ b < share a₂ b := by
  have h1 : 0 < a₁ + b := by linarith
  have h2 : 0 < a₂ + b := by linarith
  unfold share
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos (sub_pos.mpr h) hb]

/-- **A smaller competing part is a bigger share**, weakly, at a non-negative part. -/
theorem share_le_share_of_le_right (a b₁ b₂ : ℝ) (ha : 0 ≤ a) (hb : 0 < a + b₂)
    (h : b₂ ≤ b₁) :
    share a b₁ ≤ share a b₂ := by
  have h1 : 0 < a + b₁ := by linarith
  unfold share
  rw [div_le_div_iff₀ h1 hb]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]

/-- **And strictly, at a strictly positive part.** The strict form is the one the
predictive values need: a share of nothing does not move when its competitor shrinks. -/
theorem share_lt_share_of_lt_right (a b₁ b₂ : ℝ) (ha : 0 < a) (hb : 0 < a + b₂)
    (h : b₂ < b₁) :
    share a b₁ < share a b₂ := by
  have h1 : 0 < a + b₁ := by linarith
  unfold share
  rw [div_lt_div_iff₀ h1 hb]
  nlinarith [mul_pos ha (sub_pos.mpr h)]

/-! ### The operating point

A threshold on a score produces two numbers and only two: the fraction of cases it calls,
and the fraction of non-cases it clears. Everything a clinic can compute -- a predictive
value, a net benefit, a reclassification index -- is a function of those two and of the
prevalence.

Bundling them is not decoration. The corpus's existing clinical metrics take
`sensitivity` and `specificity` as separate free reals, and a caller who supplies a
specificity where a sensitivity was wanted gets a wrong predictive value with no type
error. `metricPPV` and `ppv` in the Portability layer take them in OPPOSITE orders. -/

/-- **The operating point of a thresholded score**: what a decision rule does to cases and
to non-cases. -/
structure OperatingPoint where
  /-- The fraction of cases the rule calls: `P(positive | case)`. -/
  sensitivity : ℝ
  /-- The fraction of non-cases the rule clears: `P(negative | non-case)`. -/
  specificity : ℝ

namespace OperatingPoint

/-- **An operating point a rule could actually have.** Both coordinates are conditional
probabilities, so both lie in the unit interval. A pair failing this did not come from a
threshold on a score, and every bound below assumes it. -/
structure Admissible (o : OperatingPoint) : Prop where
  /-- A sensitivity is a probability. -/
  sensitivity_nonneg : 0 ≤ o.sensitivity
  /-- A sensitivity is a probability. -/
  sensitivity_le_one : o.sensitivity ≤ 1
  /-- A specificity is a probability. -/
  specificity_nonneg : 0 ≤ o.specificity
  /-- A specificity is a probability. -/
  specificity_le_one : o.specificity ≤ 1

/-- **The rule that calls everyone.** Sensitivity one, specificity zero: the treat-all
strategy every decision curve is read against.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def treatAll : OperatingPoint where
  sensitivity := 1
  specificity := 0

/-- **The rule that calls no one.** The other baseline: sensitivity zero, specificity one.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def treatNone : OperatingPoint where
  sensitivity := 0
  specificity := 1

/-- **The rule that is always right.** Both coordinates one: the ceiling no score reaches
and every bound below is measured against.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def perfect : OperatingPoint where
  sensitivity := 1
  specificity := 1

/-- **The rule that flips a coin.** Both coordinates one half: what a score with no
discrimination produces at any threshold, and the floor an `OperatingPointLaw` starts
from.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def chance : OperatingPoint where
  sensitivity := 1 / 2
  specificity := 1 / 2

@[simp] theorem treatAll_sensitivity : treatAll.sensitivity = 1 := rfl
@[simp] theorem treatAll_specificity : treatAll.specificity = 0 := rfl
@[simp] theorem treatNone_sensitivity : treatNone.sensitivity = 0 := rfl
@[simp] theorem treatNone_specificity : treatNone.specificity = 1 := rfl
@[simp] theorem perfect_sensitivity : perfect.sensitivity = 1 := rfl
@[simp] theorem perfect_specificity : perfect.specificity = 1 := rfl
@[simp] theorem chance_sensitivity : chance.sensitivity = 1 / 2 := rfl
@[simp] theorem chance_specificity : chance.specificity = 1 / 2 := rfl

/-- **The four named points are admissible**, which is what makes the theorems below
statements about something rather than vacuous quantifications. -/
theorem treatAll_admissible : treatAll.Admissible where
  sensitivity_nonneg := by norm_num
  sensitivity_le_one := by norm_num
  specificity_nonneg := by norm_num
  specificity_le_one := by norm_num

/-- The treat-no-one baseline is an operating point. -/
theorem treatNone_admissible : treatNone.Admissible where
  sensitivity_nonneg := by norm_num
  sensitivity_le_one := by norm_num
  specificity_nonneg := by norm_num
  specificity_le_one := by norm_num

/-- The perfect rule is an operating point. -/
theorem perfect_admissible : perfect.Admissible where
  sensitivity_nonneg := by norm_num
  sensitivity_le_one := by norm_num
  specificity_nonneg := by norm_num
  specificity_le_one := by norm_num

/-- The coin flip is an operating point. -/
theorem chance_admissible : chance.Admissible where
  sensitivity_nonneg := by norm_num
  sensitivity_le_one := by norm_num
  specificity_nonneg := by norm_num
  specificity_le_one := by norm_num

/-! ### The predictive values

Two shares. `Core.share a b = a/(a+b)` is exactly the Bayes form: the mass a rule calls
correctly, against everything it calls. -/

/-- **Positive predictive value at a prevalence**, `sens·π / (sens·π + (1-spec)(1-π))`.

The number a patient who screened positive is told. It is not a property of the score: it
moves with the prevalence, so the same score deployed in a lower-prevalence population
reports a lower predictive value at the same threshold. That is why the prevalence is an
argument here and not a field of the operating point.

`Portability.MetricSpecificPortability.metricPPV` and
`Portability.ClinicalUtilityFairness.ppv` are this body written out with the sensitivity
and specificity as free reals, in that order and in the reverse order respectively.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def positivePredictiveValue (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  share (o.sensitivity * prevalence) ((1 - o.specificity) * (1 - prevalence))

/-- **Negative predictive value at a prevalence**, `spec(1-π) / (spec(1-π) + (1-sens)π)`.

The number a patient who screened negative is told, and the coordinate a screening
programme is actually judged on at low prevalence -- where it is near one whatever the
score does, which is the reason a programme cannot be defended on it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def negativePredictiveValue (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  share (o.specificity * (1 - prevalence)) ((1 - o.sensitivity) * prevalence)

/-- **Precision IS the positive predictive value.**

Two literatures, one number: machine learning says precision, medicine says PPV, and the
corpus carries both (`Foundations.TransportIdentities.precision` from a confusion matrix,
`MetricSpecificPortability.metricPPV` from an operating point). Routed through
`Core.identifiedWith` because a definition whose body is another quantity is a CLAIM that
the two are the same number, and written as a bare renaming that claim is invisible.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def precision (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  identifiedWith (o.positivePredictiveValue prevalence)

/-- **Recall IS the sensitivity**, and unlike precision it does not depend on the
prevalence at all. That asymmetry is the whole content of a precision-recall curve: one
axis is a property of the score and the other is a property of the population it is
deployed in.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def recall (o : OperatingPoint) : ℝ :=
  identifiedWith o.sensitivity

/-- **The `F₁` score**, the harmonic mean of precision and recall.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def f1 (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  ratio (2 * (o.precision prevalence) * (o.recall))
    (o.precision prevalence + o.recall)

/-- **The predictive value is the Bayes form**, definitionally. Stated so that a reader
who knows the textbook expression can see that `share` is it, and so that the existing
high-depth copies have something to be rewritten against. -/
theorem positivePredictiveValue_eq (o : OperatingPoint) (prevalence : ℝ) :
    o.positivePredictiveValue prevalence
      = o.sensitivity * prevalence /
          (o.sensitivity * prevalence + (1 - o.specificity) * (1 - prevalence)) := rfl

/-- **And the negative predictive value likewise.** -/
theorem negativePredictiveValue_eq (o : OperatingPoint) (prevalence : ℝ) :
    o.negativePredictiveValue prevalence
      = o.specificity * (1 - prevalence) /
          (o.specificity * (1 - prevalence) + (1 - o.sensitivity) * prevalence) := rfl

/-- **Precision unfolds to the predictive value**, which is the whole computational
content of the identification. -/
@[simp] theorem precision_eq (o : OperatingPoint) (prevalence : ℝ) :
    o.precision prevalence = o.positivePredictiveValue prevalence := rfl

/-- **Recall unfolds to the sensitivity.** -/
@[simp] theorem recall_eq (o : OperatingPoint) : o.recall = o.sensitivity := rfl

/-- **The predictive value lies in the unit interval**, on an admissible point at a
prevalence in range, away from the degenerate denominator. The bound every consumer
needs. -/
theorem positivePredictiveValue_mem_unit (o : OperatingPoint) (prevalence : ℝ)
    (h : o.Admissible) (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1)
    (hpos : 0 < o.sensitivity * prevalence + (1 - o.specificity) * (1 - prevalence)) :
    0 ≤ o.positivePredictiveValue prevalence ∧ o.positivePredictiveValue prevalence ≤ 1 := by
  have hs := h.sensitivity_nonneg
  have hq := h.specificity_le_one
  unfold positivePredictiveValue
  exact share_mem_unit _ _ (mul_nonneg hs hπ0)
    (mul_nonneg (by linarith) (by linarith)) hpos

/-- **And so does the negative predictive value.** -/
theorem negativePredictiveValue_mem_unit (o : OperatingPoint) (prevalence : ℝ)
    (h : o.Admissible) (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1)
    (hpos : 0 < o.specificity * (1 - prevalence) + (1 - o.sensitivity) * prevalence) :
    0 ≤ o.negativePredictiveValue prevalence ∧ o.negativePredictiveValue prevalence ≤ 1 := by
  have hq := h.specificity_nonneg
  have hs := h.sensitivity_le_one
  unfold negativePredictiveValue
  exact share_mem_unit _ _ (mul_nonneg hq (by linarith))
    (mul_nonneg (by linarith) hπ0) hpos

/-- **The predictive value at zero prevalence, named.** With no cases there are no
positive calls to be right about, numerator and denominator both vanish, and Lean returns
`0`. So a PERFECT rule -- unit sensitivity, unit specificity -- reports that every
positive call it makes is wrong.

The failure is worst exactly where screening programmes operate, and it is
indistinguishable from a rule that genuinely never calls a true positive. Consumers must
require a positive denominator, which is what `positivePredictiveValue_mem_unit` asks
for. -/
theorem positivePredictiveValue_zero_prevalence_is_junk :
    perfect.positivePredictiveValue 0 = 0 := by
  simp [positivePredictiveValue, share]

/-- **The negative predictive value at unit prevalence, named.** The mirror junk value:
with everyone a case there are no negative calls to be right about, and a perfect rule
reports that every one of them is wrong. -/
theorem negativePredictiveValue_unit_prevalence_is_junk :
    perfect.negativePredictiveValue 1 = 0 := by
  simp [negativePredictiveValue, share]

/-- **A perfectly specific rule has predictive value one wherever it fires**, at every
prevalence however small.

That is the endpoint which fixes the form: the dependence on prevalence is carried
entirely by the false-positive term, so a body that let prevalence into the numerator
alone would still be increasing in sensitivity and in prevalence, and would fail here. It
is also why a predictive-value gap between populations is driven by specificity rather
than by sensitivity. -/
theorem positivePredictiveValue_of_specificity_one (o : OperatingPoint) (prevalence : ℝ)
    (hspec : o.specificity = 1) (h : o.sensitivity * prevalence ≠ 0) :
    o.positivePredictiveValue prevalence = 1 := by
  have hz : (1 - o.specificity) * (1 - prevalence) = 0 := by rw [hspec]; ring
  unfold positivePredictiveValue share
  rw [hz, add_zero]
  exact div_self h

/-- **A perfectly sensitive rule has negative predictive value one wherever it clears.**
The mirror statement, and the reason a highly sensitive rule-out test is reported on the
negative predictive value. -/
theorem negativePredictiveValue_of_sensitivity_one (o : OperatingPoint) (prevalence : ℝ)
    (hsens : o.sensitivity = 1) (h : o.specificity * (1 - prevalence) ≠ 0) :
    o.negativePredictiveValue prevalence = 1 := by
  have hz : (1 - o.sensitivity) * prevalence = 0 := by rw [hsens]; ring
  unfold negativePredictiveValue share
  rw [hz, add_zero]
  exact div_self h

/-- **The treat-all rule's predictive value is the prevalence.** Calling everyone tells a
patient nothing they did not already know, and that number is the baseline every screening
programme has to beat. -/
theorem positivePredictiveValue_treatAll (prevalence : ℝ) :
    treatAll.positivePredictiveValue prevalence = prevalence := by
  show treatAll.sensitivity * prevalence /
      (treatAll.sensitivity * prevalence + (1 - treatAll.specificity) * (1 - prevalence))
    = prevalence
  rw [treatAll_sensitivity, treatAll_specificity,
    show (1:ℝ) * prevalence + (1 - 0) * (1 - prevalence) = 1 by ring, div_one, one_mul]

/-- **A more sensitive rule has a higher predictive value**, at a fixed specificity below
one. The first of the three directions the metric moves in. -/
theorem positivePredictiveValue_lt_of_sensitivity_lt (o₁ o₂ : OperatingPoint)
    (prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hspec : o₁.specificity = o₂.specificity) (hq : o₂.specificity < 1)
    (h0 : 0 ≤ o₁.sensitivity) (h : o₁.sensitivity < o₂.sensitivity) :
    o₁.positivePredictiveValue prevalence < o₂.positivePredictiveValue prevalence := by
  have hb : (0:ℝ) < (1 - o₂.specificity) * (1 - prevalence) :=
    mul_pos (by linarith) (by linarith)
  have hnum : o₁.sensitivity * prevalence < o₂.sensitivity * prevalence :=
    mul_lt_mul_of_pos_right h hπ
  unfold positivePredictiveValue
  rw [hspec]
  exact share_lt_share_of_lt_left (o₁.sensitivity * prevalence)
    (o₂.sensitivity * prevalence) ((1 - o₂.specificity) * (1 - prevalence))
    (mul_nonneg h0 (le_of_lt hπ)) hb hnum

/-- **A more specific rule has a higher predictive value**, at a fixed positive
sensitivity. The second direction, and the one that dominates at low prevalence. -/
theorem positivePredictiveValue_lt_of_specificity_lt (o₁ o₂ : OperatingPoint)
    (prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hsens : o₁.sensitivity = o₂.sensitivity) (hs : 0 < o₂.sensitivity)
    (hq2 : o₂.specificity ≤ 1) (h : o₁.specificity < o₂.specificity) :
    o₁.positivePredictiveValue prevalence < o₂.positivePredictiveValue prevalence := by
  have hnum : 0 < o₂.sensitivity * prevalence := mul_pos hs hπ
  have hb : (0:ℝ) ≤ (1 - o₂.specificity) * (1 - prevalence) :=
    mul_nonneg (by linarith) (by linarith)
  have hden : (0:ℝ) < o₂.sensitivity * prevalence
      + (1 - o₂.specificity) * (1 - prevalence) := by linarith
  have hlt : (1 - o₂.specificity) * (1 - prevalence)
      < (1 - o₁.specificity) * (1 - prevalence) :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  unfold positivePredictiveValue
  rw [hsens]
  exact share_lt_share_of_lt_right (o₂.sensitivity * prevalence)
    ((1 - o₁.specificity) * (1 - prevalence)) ((1 - o₂.specificity) * (1 - prevalence))
    hnum hden hlt

/-- **A commoner disease has a higher predictive value at the same operating point.**

The third direction, and the one that makes a predictive value not a property of the
score. A programme validated in a high-prevalence clinic and deployed in a screening
population reports a lower predictive value with the same rule, the same threshold and
the same sensitivity -- and nothing has gone wrong with the score. -/
theorem positivePredictiveValue_lt_of_prevalence_lt (o : OperatingPoint) (π₁ π₂ : ℝ)
    (hs : 0 < o.sensitivity) (hq : o.specificity < 1)
    (h0 : 0 < π₁) (h : π₁ < π₂) (h1 : π₂ ≤ 1) :
    o.positivePredictiveValue π₁ < o.positivePredictiveValue π₂ := by
  have hπ₁1 : π₁ < 1 := lt_of_lt_of_le h h1
  have hπ₂0 : (0:ℝ) < π₂ := by linarith
  have hB₁ : (0:ℝ) < (1 - o.specificity) * (1 - π₁) :=
    mul_pos (by linarith) (by linarith)
  have hB₂ : (0:ℝ) ≤ (1 - o.specificity) * (1 - π₂) :=
    mul_nonneg (by linarith) (by linarith)
  have hle : (1 - o.specificity) * (1 - π₂) ≤ (1 - o.specificity) * (1 - π₁) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hnum : o.sensitivity * π₁ < o.sensitivity * π₂ := mul_lt_mul_of_pos_left h hs
  have hden : (0:ℝ) < o.sensitivity * π₂ := mul_pos hs hπ₂0
  have step1 := share_lt_share_of_lt_left (o.sensitivity * π₁) (o.sensitivity * π₂)
    ((1 - o.specificity) * (1 - π₁)) (le_of_lt (mul_pos hs h0)) hB₁ hnum
  have step2 := share_le_share_of_le_right (o.sensitivity * π₂)
    ((1 - o.specificity) * (1 - π₁)) ((1 - o.specificity) * (1 - π₂))
    (le_of_lt hden) (by linarith) hle
  unfold positivePredictiveValue
  exact lt_of_lt_of_le step1 step2

/-- **A more specific rule has a higher negative predictive value.** -/
theorem negativePredictiveValue_lt_of_specificity_lt (o₁ o₂ : OperatingPoint)
    (prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hsens : o₁.sensitivity = o₂.sensitivity) (hs : o₂.sensitivity < 1)
    (h0 : 0 ≤ o₁.specificity) (h : o₁.specificity < o₂.specificity) :
    o₁.negativePredictiveValue prevalence < o₂.negativePredictiveValue prevalence := by
  have hb : (0:ℝ) < (1 - o₂.sensitivity) * prevalence := mul_pos (by linarith) hπ
  have hnum : o₁.specificity * (1 - prevalence) < o₂.specificity * (1 - prevalence) :=
    mul_lt_mul_of_pos_right h (by linarith)
  unfold negativePredictiveValue
  rw [hsens]
  exact share_lt_share_of_lt_left (o₁.specificity * (1 - prevalence))
    (o₂.specificity * (1 - prevalence)) ((1 - o₂.sensitivity) * prevalence)
    (mul_nonneg h0 (by linarith)) hb hnum

/-- **A more sensitive rule has a higher negative predictive value**, at a fixed positive
specificity. -/
theorem negativePredictiveValue_lt_of_sensitivity_lt (o₁ o₂ : OperatingPoint)
    (prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hspec : o₁.specificity = o₂.specificity) (hq : 0 < o₂.specificity)
    (hs2 : o₂.sensitivity ≤ 1) (h : o₁.sensitivity < o₂.sensitivity) :
    o₁.negativePredictiveValue prevalence < o₂.negativePredictiveValue prevalence := by
  have hnum : 0 < o₂.specificity * (1 - prevalence) := mul_pos hq (by linarith)
  have hb : (0:ℝ) ≤ (1 - o₂.sensitivity) * prevalence :=
    mul_nonneg (by linarith) (by linarith)
  have hden : (0:ℝ) < o₂.specificity * (1 - prevalence)
      + (1 - o₂.sensitivity) * prevalence := by linarith
  have hlt : (1 - o₂.sensitivity) * prevalence < (1 - o₁.sensitivity) * prevalence :=
    mul_lt_mul_of_pos_right (by linarith) hπ
  unfold negativePredictiveValue
  rw [hspec]
  exact share_lt_share_of_lt_right (o₂.specificity * (1 - prevalence))
    ((1 - o₁.sensitivity) * prevalence) ((1 - o₂.sensitivity) * prevalence)
    hnum hden hlt

/-- **A commoner disease has a LOWER negative predictive value at the same operating
point.** The prevalence dependence runs the opposite way to the positive predictive
value's, which is why the two cannot both be defended by choosing a deployment
population. -/
theorem negativePredictiveValue_lt_of_prevalence_lt (o : OperatingPoint) (π₁ π₂ : ℝ)
    (hq : 0 < o.specificity) (hs : o.sensitivity < 1)
    (h0 : 0 < π₁) (h : π₁ < π₂) (h1 : π₂ < 1) :
    o.negativePredictiveValue π₂ < o.negativePredictiveValue π₁ := by
  have hπ₁1 : π₁ < 1 := by linarith
  have hB₂ : (0:ℝ) < (1 - o.sensitivity) * π₂ := mul_pos (by linarith) (by linarith)
  have hB₁ : (0:ℝ) ≤ (1 - o.sensitivity) * π₁ :=
    mul_nonneg (by linarith) (by linarith)
  have hle : (1 - o.sensitivity) * π₁ ≤ (1 - o.sensitivity) * π₂ :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hnum : o.specificity * (1 - π₂) < o.specificity * (1 - π₁) :=
    mul_lt_mul_of_pos_left (by linarith) hq
  have hden : (0:ℝ) < o.specificity * (1 - π₁) := mul_pos hq (by linarith)
  have step1 := share_lt_share_of_lt_left (o.specificity * (1 - π₂))
    (o.specificity * (1 - π₁)) ((1 - o.sensitivity) * π₂)
    (le_of_lt (mul_pos hq (by linarith))) hB₂ hnum
  have step2 := share_le_share_of_le_right (o.specificity * (1 - π₁))
    ((1 - o.sensitivity) * π₂) ((1 - o.sensitivity) * π₁)
    (le_of_lt hden) (by linarith) hle
  unfold negativePredictiveValue
  exact lt_of_lt_of_le step1 step2

/-- **`F₁` at the perfect rule is one.** The reference value that fixes the coefficient:
a harmonic mean written without the two would be one half here and still symmetric, still
between its arguments, and still zero when either vanishes. -/
theorem f1_at_perfect (prevalence : ℝ) (h : prevalence ≠ 0) :
    perfect.f1 prevalence = 1 := by
  have hp : perfect.positivePredictiveValue prevalence = 1 :=
    positivePredictiveValue_of_specificity_one perfect prevalence rfl (by simpa using h)
  unfold f1 ratio precision recall identifiedWith
  rw [hp, perfect_sensitivity]
  norm_num

/-- **`F₁` at a rule that calls no one, named.** Precision and recall both vanish, the
harmonic mean divides by zero and Lean returns `0` -- which is also the value `F₁` takes
for a rule that is merely bad, so the junk point is indistinguishable from a real
verdict. Consumers must require `precision + recall ≠ 0`. -/
theorem f1_treatNone_is_junk (prevalence : ℝ) :
    treatNone.f1 prevalence = 0 := by
  simp [f1, ratio, precision, recall, identifiedWith, positivePredictiveValue, share]

/-! ### The decision-analytic half

A predictive value says how often a rule is right. It does not say whether using the rule
is worth it, because being wrong in the two directions costs different amounts. Decision
curve analysis fixes that exchange rate by the THRESHOLD: a clinician who treats at
predicted risk `t` has, by acting, declared a false positive to be worth `t/(1-t)` of a
false negative. -/

/-- **The threshold odds**, `t/(1-t)`: the exchange rate between a false positive and a
false negative that a decision threshold declares.

The whole content of decision curve analysis is that this number is not free. Choosing to
treat at a predicted risk of `t` IS choosing this exchange rate, and a decision curve is
the net benefit read as a function of it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def thresholdOdds (t : ℝ) : ℝ := ratio t (complement t)

/-- **A threshold of one half weighs the two errors equally.** The reference value. -/
theorem thresholdOdds_at_half : thresholdOdds (1 / 2) = 1 := by
  unfold thresholdOdds ratio complement; norm_num

/-- **A threshold of zero treats everyone free.** At `t = 0` a false positive costs
nothing, and the net benefit below reduces to the fraction of cases found. -/
@[simp] theorem thresholdOdds_at_zero : thresholdOdds 0 = 0 := by
  unfold thresholdOdds ratio complement; norm_num

/-- **The threshold odds at `t = 1`, named.** The exchange rate diverges -- a clinician
who will only treat at certainty has declared a false positive infinitely costly -- and
Lean returns `0`, the value meaning a false positive is FREE. The junk value is the exact
opposite of the quantity being modelled, and no type error marks it. Consumers must
require `t ≠ 1`. -/
theorem thresholdOdds_at_one_is_junk : thresholdOdds 1 = 0 := by
  unfold thresholdOdds ratio complement; norm_num

/-- **The threshold odds are positive on the interior**, which every net-benefit bound
below needs. -/
theorem thresholdOdds_pos (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 < thresholdOdds t := by
  unfold thresholdOdds ratio complement
  exact div_pos ht (by linarith)

/-- **The threshold odds are non-negative on the closed interval.** -/
theorem thresholdOdds_nonneg (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) : 0 ≤ thresholdOdds t := by
  unfold thresholdOdds ratio complement
  exact div_nonneg ht (by linarith)

/-- **A higher threshold is a steeper exchange rate.** Strictly increasing on the open
unit interval, which is what makes a decision curve a curve. -/
theorem thresholdOdds_lt_of_lt (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h : t₁ < t₂) (h1 : t₂ < 1) :
    thresholdOdds t₁ < thresholdOdds t₂ := by
  unfold thresholdOdds ratio complement
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Net benefit at a threshold**, `π·sens - (1-π)(1-spec)·t/(1-t)`.

True positives per person, minus false positives per person weighted by what the threshold
says a false positive costs. This is the canonical decision-curve quantity on a per-person
scale -- `Portability.PGSCalibrationTheory.DecisionImplications.decisionCurveNetBenefit`
is the same number with the true and false positive COUNTS supplied by hand, and its
`decisionCurveNetBenefit_eq_formula` proves that body is `tp/n - fp/n · t/(1-t)`. Here
`tp/n` is `π·sens` and `fp/n` is `(1-π)(1-spec)`, which is what makes this the same
quantity read off an operating point instead of a contingency table.

Unlike a predictive value it is not confined to the unit interval and is not a
probability: it is measured in true positives per person, and its whole use is
COMPARATIVE, against the treat-all and treat-none baselines below.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def netBenefit (o : OperatingPoint) (prevalence t : ℝ) : ℝ :=
  prevalence * o.sensitivity
    - (1 - prevalence) * (1 - o.specificity) * thresholdOdds t

/-- **The net benefit is the decision-curve formula**, with the true and false positive
rates read off the operating point. The bridge to the count-based spelling in the
Portability layer. -/
theorem netBenefit_eq (o : OperatingPoint) (prevalence t : ℝ) :
    o.netBenefit prevalence t
      = prevalence * o.sensitivity - (1 - prevalence) * (1 - o.specificity)
          * (t / (1 - t)) := rfl

/-- **Treating everyone has net benefit `π - (1-π)·t/(1-t)`.** The upper baseline of a
decision curve: a rule is worth using only if it beats this. -/
theorem netBenefit_treatAll (prevalence t : ℝ) :
    treatAll.netBenefit prevalence t
      = prevalence - (1 - prevalence) * thresholdOdds t := by
  unfold netBenefit
  rw [treatAll_sensitivity, treatAll_specificity]
  ring

/-- **Treating no one has net benefit zero**, at every prevalence and every threshold.
The lower baseline, and the reason net benefit is measured in the units it is: a rule
scoring below zero is worse than doing nothing. -/
@[simp] theorem netBenefit_treatNone (prevalence t : ℝ) :
    treatNone.netBenefit prevalence t = 0 := by
  unfold netBenefit
  rw [treatNone_sensitivity, treatNone_specificity]
  ring

/-- **A perfect rule's net benefit is the prevalence**, whatever the threshold: it finds
every case and generates no false positive, so the exchange rate never bites. This is the
ceiling every net benefit below is bounded by. -/
@[simp] theorem netBenefit_perfect (prevalence t : ℝ) :
    perfect.netBenefit prevalence t = prevalence := by
  unfold netBenefit
  rw [perfect_sensitivity, perfect_specificity]
  ring

/-- **At a zero threshold the net benefit is the fraction of cases found.** With a false
positive costing nothing, the only thing worth counting is true positives, and the rule
that maximises net benefit is the one that calls everyone. -/
theorem netBenefit_at_zero_threshold (o : OperatingPoint) (prevalence : ℝ) :
    o.netBenefit prevalence 0 = prevalence * o.sensitivity := by
  unfold netBenefit
  rw [thresholdOdds_at_zero]
  ring

/-- **A more sensitive rule has a higher net benefit.** -/
theorem netBenefit_lt_of_sensitivity_lt (o₁ o₂ : OperatingPoint) (prevalence t : ℝ)
    (hπ : 0 < prevalence) (hspec : o₁.specificity = o₂.specificity)
    (h : o₁.sensitivity < o₂.sensitivity) :
    o₁.netBenefit prevalence t < o₂.netBenefit prevalence t := by
  unfold netBenefit
  rw [hspec]
  have := mul_lt_mul_of_pos_left h hπ
  linarith

/-- **A more specific rule has a higher net benefit**, at a threshold that makes a false
positive cost something. -/
theorem netBenefit_lt_of_specificity_lt (o₁ o₂ : OperatingPoint) (prevalence t : ℝ)
    (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1)
    (hsens : o₁.sensitivity = o₂.sensitivity) (h : o₁.specificity < o₂.specificity) :
    o₁.netBenefit prevalence t < o₂.netBenefit prevalence t := by
  have hodds := thresholdOdds_pos t ht ht1
  have hc : (0:ℝ) < (1 - prevalence) * thresholdOdds t := mul_pos (by linarith) hodds
  unfold netBenefit
  rw [hsens]
  nlinarith [mul_pos hc (sub_pos.mpr h)]

/-- **A higher threshold is a lower net benefit**, whenever the rule produces false
positives at all. This is the decision curve sloping down, and it is why a rule can be
worth using at one threshold and not at another without anything about the rule
changing. -/
theorem netBenefit_lt_of_threshold_lt (o : OperatingPoint) (prevalence t₁ t₂ : ℝ)
    (hπ1 : prevalence < 1) (hq : o.specificity < 1)
    (h0 : 0 ≤ t₁) (h : t₁ < t₂) (h1 : t₂ < 1) :
    o.netBenefit prevalence t₂ < o.netBenefit prevalence t₁ := by
  have hodds := thresholdOdds_lt_of_lt t₁ t₂ h0 h h1
  have hc : (0:ℝ) < (1 - prevalence) * (1 - o.specificity) :=
    mul_pos (by linarith) (by linarith)
  unfold netBenefit
  nlinarith [mul_pos hc (sub_pos.mpr hodds)]

/-- **No rule beats a perfect one.** The net benefit is at most the prevalence on any
admissible operating point at a threshold in range -- the ceiling, in the units net
benefit is measured in. -/
theorem netBenefit_le_prevalence (o : OperatingPoint) (prevalence t : ℝ)
    (h : o.Admissible) (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    o.netBenefit prevalence t ≤ prevalence := by
  have hodds := thresholdOdds_nonneg t ht ht1
  have hs := h.sensitivity_le_one
  have hq := h.specificity_le_one
  have hfp : (0:ℝ) ≤ (1 - prevalence) * (1 - o.specificity) :=
    mul_nonneg (by linarith) (by linarith)
  have htp : prevalence * o.sensitivity ≤ prevalence := by
    nlinarith [mul_nonneg hπ0 (sub_nonneg.mpr hs)]
  unfold netBenefit
  linarith [mul_nonneg hfp hodds]

/-! ### Reclassification

The index a paper reports when it replaces one rule with another. It is two numbers, and
the corpus already records why they must be reported separately: a positive total is
consistent with a gain among cases and a loss among non-cases. -/

/-- **The event half of the net reclassification improvement**: what the new rule does to
cases.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def nriEventComponent (old new : OperatingPoint) : ℝ :=
  Descent.Core.difference new.sensitivity old.sensitivity

/-- **The non-event half**: what the new rule does to non-cases.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def nriNonEventComponent (old new : OperatingPoint) : ℝ :=
  Descent.Core.difference new.specificity old.specificity

/-- **The two-category net reclassification improvement between two operating points.**

At a fixed threshold, the net fraction of cases moved up is the sensitivity gain and the
net fraction of non-cases moved down is the specificity gain, so the index is their sum.
`Portability.ClinicalUtilityFairness.netReclassificationImprovement` is this sum with its
two components supplied by hand; this computes them from the rules being compared, which
is what lets a demographic history reach the index.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def nriFromOperatingPoints (old new : OperatingPoint) : ℝ :=
  Descent.Core.sum (nriEventComponent old new) (nriNonEventComponent old new)

/-- **Replacing a rule with itself reclassifies no one.** The property that makes this an
improvement index rather than a score: a body carrying an additive term in the operating
point would report improvement for a change that moved nobody. -/
@[simp] theorem nriFromOperatingPoints_self (o : OperatingPoint) :
    nriFromOperatingPoints o o = 0 := by
  unfold nriFromOperatingPoints nriEventComponent nriNonEventComponent
    Descent.Core.sum Descent.Core.difference
  ring

/-- **Reversing the comparison reverses the sign.** An index that did not satisfy this
would be reporting something about the pair rather than about the change. -/
theorem nriFromOperatingPoints_swap (old new : OperatingPoint) :
    nriFromOperatingPoints new old = - nriFromOperatingPoints old new := by
  unfold nriFromOperatingPoints nriEventComponent nriNonEventComponent
    Descent.Core.sum Descent.Core.difference
  ring

/-- **The two halves are recoverable from each other and the total.** This is why a single
NRI cannot be read: the identity forces the components to be reported separately, because
the total is consistent with a gain among cases and an equal loss among non-cases. -/
theorem nriFromOperatingPoints_sub_event (old new : OperatingPoint) :
    nriFromOperatingPoints old new - nriEventComponent old new
      = nriNonEventComponent old new := by
  unfold nriFromOperatingPoints Descent.Core.sum
  ring

/-- **A rule that is worse on both coordinates reclassifies patients the wrong way.** The
form the deployment results below take: a strictly dominated operating point has a
strictly negative index. -/
theorem nriFromOperatingPoints_neg (old new : OperatingPoint)
    (hs : new.sensitivity < old.sensitivity) (hq : new.specificity ≤ old.specificity) :
    nriFromOperatingPoints old new < 0 := by
  unfold nriFromOperatingPoints nriEventComponent nriNonEventComponent
    Descent.Core.sum Descent.Core.difference
  linarith

/-- **And a rule better on both reclassifies the right way.** -/
theorem nriFromOperatingPoints_pos (old new : OperatingPoint)
    (hs : old.sensitivity < new.sensitivity) (hq : old.specificity ≤ new.specificity) :
    0 < nriFromOperatingPoints old new := by
  unfold nriFromOperatingPoints nriEventComponent nriNonEventComponent
    Descent.Core.sum Descent.Core.difference
  linarith

/-- **The index is bounded by two on admissible points**, and by minus two below: both
coordinates move within the unit interval, so no reclassification can report more than
two. Stated because an unbounded-looking index invites a reader to treat a value of `0.3`
as small. -/
theorem nriFromOperatingPoints_mem_Icc (old new : OperatingPoint)
    (h₁ : old.Admissible) (h₂ : new.Admissible) :
    -2 ≤ nriFromOperatingPoints old new ∧ nriFromOperatingPoints old new ≤ 2 := by
  have a1 := h₁.sensitivity_nonneg
  have a2 := h₁.sensitivity_le_one
  have a3 := h₁.specificity_nonneg
  have a4 := h₁.specificity_le_one
  have b1 := h₂.sensitivity_nonneg
  have b2 := h₂.sensitivity_le_one
  have b3 := h₂.specificity_nonneg
  have b4 := h₂.specificity_le_one
  unfold nriFromOperatingPoints nriEventComponent nriNonEventComponent
    Descent.Core.sum Descent.Core.difference
  constructor <;> linarith

end OperatingPoint

end Descent.Core
