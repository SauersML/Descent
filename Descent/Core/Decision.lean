/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Moments

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

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
statements about something rather than vacuous quantifications.

Bundled into one theorem rather than written four times. Each of the four wants the same
four-line script and four copies of a script is a copied proof: if `Admissible` gains a
field, three of the four can be repaired and the fourth forgotten. The projections below
give the individual names back at no cost. -/
theorem namedPoints_admissible :
    treatAll.Admissible ∧ treatNone.Admissible ∧ perfect.Admissible ∧ chance.Admissible := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact { sensitivity_nonneg := by norm_num, sensitivity_le_one := by norm_num,
            specificity_nonneg := by norm_num, specificity_le_one := by norm_num }

/-- The treat-everyone baseline is an operating point. -/
theorem treatAll_admissible : treatAll.Admissible := namedPoints_admissible.1

/-- The treat-no-one baseline is an operating point. -/
theorem treatNone_admissible : treatNone.Admissible := namedPoints_admissible.2.1

/-- The perfect rule is an operating point. -/
theorem perfect_admissible : perfect.Admissible := namedPoints_admissible.2.2.1

/-- The coin flip is an operating point. -/
theorem chance_admissible : chance.Admissible := namedPoints_admissible.2.2.2

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

    Empirical status: **VALIDATED** (`simcov/battery_clinical.py`). Worst cell
    1.57 sems at 0.5 percent relative across the prevalence sweep.

    Power: the prevalence is swept 0.01 / 0.05 / 0.20 / 0.50, a factor of fifty,
    which is what puts the PREVALENCE DEPENDENCE on trial rather than a value at
    one point. The prevalence-free reading
    `sens / (sens + (1 - spec))` -- the number a balanced test set gives, and the
    commonest error in this family -- is carried as a named competitor on the
    same cells and is FALSIFIED at 1568.79 sems and 1741 percent relative. It is
    exactly right at `pi = 0.5` and wrong by a factor of seventeen at
    `pi = 0.01`, so a design at one prevalence could not have told the two apart
    and a design at one half could not have told them apart at all.

    Design, shared by all four rows of that battery. A rule with a fixed
    operating point applied to a drawn population, 200,000 per replicate and 40
    replicates, prevalence swept 0.01 / 0.05 / 0.20 / 0.50 -- a factor of fifty,
    which is what puts the PREVALENCE DEPENDENCE on trial rather than a value at
    one point. Each replicate is SPLIT: the operating point and the prevalence
    are read off half A and the quantity is predicted for half B and counted
    there, so the two never share an individual.

    That split is not fastidiousness, it is the whole design. Measured on ONE
    sample these bodies are algebraic identities on four counts -- with
    `sens = tp/(tp+fn)`, `prev = (tp+fn)/n` and `spec = tn/(tn+fp)` from the same
    sample, the predictive value IS `tp/(tp+fp)`, for every draw, with no model
    in between -- and the harness's own gate reported the first version of the
    run as DEGENERATE ORACLE for exactly that. Out of sample it is a prediction.

    Control: the total positive rate `sens*pi + (1-spec)*(1-pi)`, predicted from
    half A and counted on half B, pooled over all prevalences. It is the law of
    total probability on the same counts, the same split and the same rule, and
    it is none of the candidates -- so it fails when the draw or the split is
    broken and passes when the only thing left to be wrong is the body. -/
noncomputable def positivePredictiveValue (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  share (o.sensitivity * prevalence) ((1 - o.specificity) * (1 - prevalence))

/-- **Negative predictive value at a prevalence**, `spec(1-π) / (spec(1-π) + (1-sens)π)`.

The number a patient who screened negative is told, and the coordinate a screening
programme is actually judged on at low prevalence -- where it is near one whatever the
score does, which is the reason a programme cannot be defended on it.

    Empirical status: **VALIDATED** (`simcov/battery_clinical.py`), worst cell
    1.89 sems at 0.1 percent relative, on the design described on
    `positivePredictiveValue` above and the same control.

    Power: the prevalence-free reading `spec / (spec + (1 - sens))` is carried on
    the same cells and FALSIFIED at 503.20 sems. The relative miss is 19.6
    percent rather than the PPV's 1741, and that asymmetry is the substance of
    this declaration's own docstring: at low prevalence the negative predictive
    value is near one whatever the score does, so a wrong body is hard to see in
    the number and easy to see in the sems.

    Design, shared by all four rows of that battery. A rule with a fixed
    operating point applied to a drawn population, 200,000 per replicate and 40
    replicates, prevalence swept 0.01 / 0.05 / 0.20 / 0.50 -- a factor of fifty,
    which is what puts the PREVALENCE DEPENDENCE on trial rather than a value at
    one point. Each replicate is SPLIT: the operating point and the prevalence
    are read off half A and the quantity is predicted for half B and counted
    there, so the two never share an individual.

    That split is not fastidiousness, it is the whole design. Measured on ONE
    sample these bodies are algebraic identities on four counts -- with
    `sens = tp/(tp+fn)`, `prev = (tp+fn)/n` and `spec = tn/(tn+fp)` from the same
    sample, the predictive value IS `tp/(tp+fp)`, for every draw, with no model
    in between -- and the harness's own gate reported the first version of the
    run as DEGENERATE ORACLE for exactly that. Out of sample it is a prediction.

    Control: the total positive rate `sens*pi + (1-spec)*(1-pi)`, predicted from
    half A and counted on half B, pooled over all prevalences. It is the law of
    total probability on the same counts, the same split and the same rule, and
    it is none of the candidates -- so it fails when the draw or the split is
    broken and passes when the only thing left to be wrong is the body. -/
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

Spelled `recallRate` and not `recall`, for two reasons that agree. `recall` is a RESERVED
COMMAND KEYWORD in Lean 4, so `def recall` does not parse and `o.recall` fails at every
use site -- this file did carry that name and the whole `Descent.Core` target failed to
build on it. And `Foundations.ConfusionMatrix.recallRate` already spells the same
quantity this way, so the keyword forced the name the corpus had already chosen.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def recallRate (o : OperatingPoint) : ℝ :=
  identifiedWith o.sensitivity

/-- **The `F₁` score**, the harmonic mean of precision and recall.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def f1 (o : OperatingPoint) (prevalence : ℝ) : ℝ :=
  ratio (2 * (o.precision prevalence) * (o.recallRate))
    (o.precision prevalence + o.recallRate)

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
@[simp] theorem recallRate_eq (o : OperatingPoint) : o.recallRate = o.sensitivity := rfl

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
  unfold f1 ratio precision recallRate identifiedWith
  rw [hp, perfect_sensitivity]
  norm_num

/-- **`F₁` at a rule that calls no one, named.** Precision and recall both vanish, the
harmonic mean divides by zero and Lean returns `0` -- which is also the value `F₁` takes
for a rule that is merely bad, so the junk point is indistinguishable from a real
verdict. Consumers must require `precision + recall ≠ 0`. -/
theorem f1_treatNone_is_junk (prevalence : ℝ) :
    treatNone.f1 prevalence = 0 := by
  simp [f1, ratio, precision, recallRate, identifiedWith, positivePredictiveValue, share]

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

    Empirical status: **VALIDATED** (`simcov/battery_clinical.py`), worst cell
    1.29 sems at 0.1 percent relative, on the design described on
    `positivePredictiveValue` above and the same control. The threshold
    probability is 0.10, so the threshold odds are 1/9.

    Power: the inverted threshold odds `(1-t)/t` -- which agrees at `t = 0.5` and
    is the error a spot check at one threshold cannot catch -- is carried as a
    named competitor and FALSIFIED at 747.74 sems. The relative miss is 13958
    percent, which is what an unbounded quantity does when the false-positive
    penalty is off by a factor of eighty-one.

    Design, shared by all four rows of that battery. A rule with a fixed
    operating point applied to a drawn population, 200,000 per replicate and 40
    replicates, prevalence swept 0.01 / 0.05 / 0.20 / 0.50 -- a factor of fifty,
    which is what puts the PREVALENCE DEPENDENCE on trial rather than a value at
    one point. Each replicate is SPLIT: the operating point and the prevalence
    are read off half A and the quantity is predicted for half B and counted
    there, so the two never share an individual.

    That split is not fastidiousness, it is the whole design. Measured on ONE
    sample these bodies are algebraic identities on four counts -- with
    `sens = tp/(tp+fn)`, `prev = (tp+fn)/n` and `spec = tn/(tn+fp)` from the same
    sample, the predictive value IS `tp/(tp+fp)`, for every draw, with no model
    in between -- and the harness's own gate reported the first version of the
    run as DEGENERATE ORACLE for exactly that. Out of sample it is a prediction.

    Control: the total positive rate `sens*pi + (1-spec)*(1-pi)`, predicted from
    half A and counted on half B, pooled over all prevalences. It is the law of
    total probability on the same counts, the same split and the same rule, and
    it is none of the candidates -- so it fails when the draw or the split is
    broken and passes when the only thing left to be wrong is the body. -/
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

/-- **What a rule gives up against treating everyone**, as one expression.

`π(1 - sens)` is the cases the rule misses that treat-all would have caught;
`(1-π)·spec·t/(1-t)` is the unnecessary treatments it avoids, priced at what the threshold
says they cost. The whole of decision curve analysis is the comparison of those two terms,
and writing the difference as an identity rather than deriving it at each use is what makes
the comparison a `linarith` away everywhere below. -/
theorem treatAll_netBenefit_sub (o : OperatingPoint) (prevalence t : ℝ) :
    treatAll.netBenefit prevalence t - o.netBenefit prevalence t
      = prevalence * (1 - o.sensitivity)
        - (1 - prevalence) * o.specificity * thresholdOdds t := by
  unfold netBenefit
  rw [treatAll_sensitivity, treatAll_specificity]
  ring

/-- **Exactly when a rule is not worth using**, at a given threshold and prevalence.

The rule loses to treating everyone precisely when the cases it misses outweigh the
unnecessary treatments it avoids, at the exchange rate the threshold declares. A rule can
be on the wrong side of this at one threshold and the right side at another with nothing
about the rule changing, which is why a decision curve is reported as a curve rather than
as a number. -/
theorem netBenefit_lt_treatAll_iff (o : OperatingPoint) (prevalence t : ℝ) :
    o.netBenefit prevalence t < treatAll.netBenefit prevalence t ↔
      (1 - prevalence) * o.specificity * thresholdOdds t
        < prevalence * (1 - o.sensitivity) := by
  have hid := treatAll_netBenefit_sub o prevalence t
  constructor <;> intro h <;> linarith

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

    Empirical status: **VALIDATED** (`simcov/battery_clinical.py`), worst cell
    2.92 sems at 10.9 percent relative.

    The oracle here is a RECLASSIFICATION COUNT and not a restatement of this
    body: the same held-out individuals are classified by both rules, and the
    index is counted as (moved up among cases minus moved down among cases) plus
    (moved down among non-cases minus moved up among non-cases), which is the
    definition the index is named for. The first version of the run computed the
    truth from the two operating points -- that is this body -- and was reported
    DEGENERATE ORACLE.

    Power: the wrong-sign non-event component is carried on the same cells and
    FALSIFIED at 218.01 sems. The two rules differ in BOTH coordinates on purpose
    (sensitivity 0.55 to 0.75, specificity 0.90 to 0.80, so the two components
    have opposite signs); at equal specificity the non-event component vanishes
    and the wrong sign is invisible, which the first run demonstrated by
    returning DEGENERATE ORACLE on that competitor.

    Design, shared by all four rows of that battery. A rule with a fixed
    operating point applied to a drawn population, 200,000 per replicate and 40
    replicates, prevalence swept 0.01 / 0.05 / 0.20 / 0.50 -- a factor of fifty,
    which is what puts the PREVALENCE DEPENDENCE on trial rather than a value at
    one point. Each replicate is SPLIT: the operating point and the prevalence
    are read off half A and the quantity is predicted for half B and counted
    there, so the two never share an individual.

    That split is not fastidiousness, it is the whole design. Measured on ONE
    sample these bodies are algebraic identities on four counts -- with
    `sens = tp/(tp+fn)`, `prev = (tp+fn)/n` and `spec = tn/(tn+fp)` from the same
    sample, the predictive value IS `tp/(tp+fp)`, for every draw, with no model
    in between -- and the harness's own gate reported the first version of the
    run as DEGENERATE ORACLE for exactly that. Out of sample it is a prediction.

    Control: the total positive rate `sens*pi + (1-spec)*(1-pi)`, predicted from
    half A and counted on half B, pooled over all prevalences. It is the law of
    total probability on the same counts, the same split and the same rule, and
    it is none of the candidates -- so it fails when the draw or the split is
    broken and passes when the only thing left to be wrong is the body. -/
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

/-! ### What a discrimination level does to an operating point

This is the join, and it is the only place in this file where a modelling commitment is
made. Everything above is arithmetic on two probabilities; everything below is the
demography-to-metric spine. They meet here.

A sensitivity is not a function of `(Var S, Cov(S,Y), Var Y)`. Under a liability-threshold
model it is `Φ` of a standardised threshold displaced by `√R²`, and `Core` has no `Φ` --
the same wall `Core.Moments.aucArgument` meets and answers by writing the argument of the
normal integral rather than a wrong closed form for it.

The answer here is to name the ONE consequence of the distributional assumption that
every clinical metric actually uses: a better discriminating score has a better operating
point. Nothing below needs more than that, so nothing below assumes more than that. -/

/-- **An operating-point law**: how a threshold rule's two coordinates respond to the
score's discrimination.

The two monotonicity fields are the content. They say that raising `R²` -- by any means,
demographic or otherwise -- strictly improves both the fraction of cases called and the
fraction of non-cases cleared, at the fixed threshold the law is about. That is what a
liability-threshold model with a Gaussian link delivers, and it is what
`Portability.ClinicalUtilityFairness.sensFromR2` and `specFromR2` prove of the Gaussian
instance -- but it is strictly weaker than assuming the Gaussian, and every theorem below
is quantified over ALL laws satisfying it.

The fields are hypotheses of the structure rather than of each theorem for the same
reason `PopGenParameters` carries its positivity proofs as fields: a constraint added
once cannot be forgotten at a use site.

Why a `ℝ → OperatingPoint` and not a `ScoreMoments → OperatingPoint`: the corpus's own
minimality results say the second-moment metrics see the tuple only through the three
numbers, and every one of them factors through `R²`. A law reading more of the tuple
would be claiming the operating point depends on something `R²` does not capture, which
is a modelling claim with no measurement behind it. -/
structure OperatingPointLaw where
  /-- The operating point a score with this much explained variance reaches. -/
  point : ℝ → OperatingPoint
  /-- More explained variance, more cases called. -/
  sensitivity_strictMono : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ 1 →
    (point x).sensitivity < (point y).sensitivity
  /-- More explained variance, more non-cases cleared. -/
  specificity_strictMono : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ 1 →
    (point x).specificity < (point y).specificity
  /-- What the law returns on the unit interval is an operating point a rule could have. -/
  point_admissible : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (point x).Admissible

/-- **The chance-calibrated point at a discrimination level**, both coordinates
`(1 + R²)/2`: a coin flip at no discrimination, perfect at complete discrimination,
linear between.

This is a WITNESS and not a model. Nothing claims a real score behaves this way; what it
does is make `OperatingPointLaw` inhabited, so that the theorems quantified over laws are
statements about something rather than true and empty.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def chanceCalibratedPoint (x : ℝ) : OperatingPoint where
  sensitivity := midpoint 1 x
  specificity := midpoint 1 x

@[simp] theorem chanceCalibratedPoint_sensitivity (x : ℝ) :
    (chanceCalibratedPoint x).sensitivity = midpoint 1 x := rfl

@[simp] theorem chanceCalibratedPoint_specificity (x : ℝ) :
    (chanceCalibratedPoint x).specificity = midpoint 1 x := rfl

/-- **At no discrimination the chance-calibrated law is the coin flip**, which is the
anchor that makes it the law it claims to be rather than an arbitrary increasing map. -/
theorem chanceCalibratedPoint_at_zero :
    chanceCalibratedPoint 0 = OperatingPoint.chance := by
  unfold chanceCalibratedPoint OperatingPoint.chance midpoint
  norm_num

/-- **At complete discrimination it is the perfect rule.** The other anchor. -/
theorem chanceCalibratedPoint_at_one :
    chanceCalibratedPoint 1 = OperatingPoint.perfect := by
  unfold chanceCalibratedPoint OperatingPoint.perfect midpoint
  norm_num

namespace OperatingPointLaw

/-- **The class is inhabited.** A theorem quantified over an uninhabited structure is true
and empty, and every spine theorem below is quantified over this one.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def witness : OperatingPointLaw where
  point := chanceCalibratedPoint
  sensitivity_strictMono := by
    intro x y _ hxy _
    simp only [chanceCalibratedPoint_sensitivity]
    unfold midpoint
    linarith
  specificity_strictMono := by
    intro x y _ hxy _
    simp only [chanceCalibratedPoint_specificity]
    unfold midpoint
    linarith
  point_admissible := by
    intro x hx hx1
    constructor <;>
      simp only [chanceCalibratedPoint_sensitivity, chanceCalibratedPoint_specificity] <;>
      unfold midpoint <;> linarith

/-! ### Every clinical metric inherits `R²`'s ordering

Four theorems, and they are what the rest of the file is built on: each says a strictly
higher `R²` gives a strictly better clinical number, under any law. Everything after this
is a composition of one of these with a fact about a demography. -/

/-- **A better discriminating score has a higher predictive value.**

Both coordinates improve, so the numerator of the share rises and the competing
false-positive term falls; the two `share` lemmas take one step each. -/
theorem positivePredictiveValue_lt_of_r2_lt (L : OperatingPointLaw) (prevalence x y : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    (L.point x).positivePredictiveValue prevalence
      < (L.point y).positivePredictiveValue prevalence := by
  have hx1 : x ≤ 1 := by linarith
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hs1 := (L.point_admissible x hx hx1).sensitivity_nonneg
  have hq2 := (L.point_admissible y hy0 hy).specificity_le_one
  have hslt := L.sensitivity_strictMono x y hx hxy hy
  have hqlt := L.specificity_strictMono x y hx hxy hy
  have hq1 : (L.point x).specificity < 1 := lt_of_lt_of_le hqlt hq2
  have hs2 : 0 < (L.point y).sensitivity := lt_of_le_of_lt hs1 hslt
  have hB₁ : (0:ℝ) < (1 - (L.point x).specificity) * (1 - prevalence) :=
    mul_pos (by linarith) (by linarith)
  have hB₂ : (0:ℝ) ≤ (1 - (L.point y).specificity) * (1 - prevalence) :=
    mul_nonneg (by linarith) (by linarith)
  have hBlt : (1 - (L.point y).specificity) * (1 - prevalence)
      < (1 - (L.point x).specificity) * (1 - prevalence) :=
    mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have hnum : (L.point x).sensitivity * prevalence
      < (L.point y).sensitivity * prevalence := mul_lt_mul_of_pos_right hslt hπ
  have hden : (0:ℝ) < (L.point y).sensitivity * prevalence := mul_pos hs2 hπ
  have step1 := share_lt_share_of_lt_left ((L.point x).sensitivity * prevalence)
    ((L.point y).sensitivity * prevalence)
    ((1 - (L.point x).specificity) * (1 - prevalence))
    (mul_nonneg hs1 (le_of_lt hπ)) hB₁ hnum
  have step2 := share_lt_share_of_lt_right ((L.point y).sensitivity * prevalence)
    ((1 - (L.point x).specificity) * (1 - prevalence))
    ((1 - (L.point y).specificity) * (1 - prevalence))
    hden (by linarith) hBlt
  unfold OperatingPoint.positivePredictiveValue
  exact lt_trans step1 step2

/-- **A better discriminating score has a higher negative predictive value.** The mirror
theorem: the specificity carries the numerator here and the sensitivity the competing
term, and both move the right way. -/
theorem negativePredictiveValue_lt_of_r2_lt (L : OperatingPointLaw) (prevalence x y : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    (L.point x).negativePredictiveValue prevalence
      < (L.point y).negativePredictiveValue prevalence := by
  have hx1 : x ≤ 1 := by linarith
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hq1 := (L.point_admissible x hx hx1).specificity_nonneg
  have hs2 := (L.point_admissible y hy0 hy).sensitivity_le_one
  have hslt := L.sensitivity_strictMono x y hx hxy hy
  have hqlt := L.specificity_strictMono x y hx hxy hy
  have hs1 : (L.point x).sensitivity < 1 := lt_of_lt_of_le hslt hs2
  have hq2 : 0 < (L.point y).specificity := lt_of_le_of_lt hq1 hqlt
  have hB₁ : (0:ℝ) < (1 - (L.point x).sensitivity) * prevalence :=
    mul_pos (by linarith) hπ
  have hB₂ : (0:ℝ) ≤ (1 - (L.point y).sensitivity) * prevalence :=
    mul_nonneg (by linarith) (by linarith)
  have hBlt : (1 - (L.point y).sensitivity) * prevalence
      < (1 - (L.point x).sensitivity) * prevalence :=
    mul_lt_mul_of_pos_right (by linarith) hπ
  have hnum : (L.point x).specificity * (1 - prevalence)
      < (L.point y).specificity * (1 - prevalence) :=
    mul_lt_mul_of_pos_right hqlt (by linarith)
  have hden : (0:ℝ) < (L.point y).specificity * (1 - prevalence) :=
    mul_pos hq2 (by linarith)
  have step1 := share_lt_share_of_lt_left ((L.point x).specificity * (1 - prevalence))
    ((L.point y).specificity * (1 - prevalence))
    ((1 - (L.point x).sensitivity) * prevalence)
    (mul_nonneg hq1 (by linarith)) hB₁ hnum
  have step2 := share_lt_share_of_lt_right ((L.point y).specificity * (1 - prevalence))
    ((1 - (L.point x).sensitivity) * prevalence)
    ((1 - (L.point y).sensitivity) * prevalence)
    hden (by linarith) hBlt
  unfold OperatingPoint.negativePredictiveValue
  exact lt_trans step1 step2

/-- **A better discriminating score has a higher net benefit**, at any threshold in the
interior where a false positive costs something. -/
theorem netBenefit_lt_of_r2_lt (L : OperatingPointLaw) (prevalence t x y : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    (L.point x).netBenefit prevalence t < (L.point y).netBenefit prevalence t := by
  have hslt := L.sensitivity_strictMono x y hx hxy hy
  have hqlt := L.specificity_strictMono x y hx hxy hy
  have hodds := OperatingPoint.thresholdOdds_pos t ht ht1
  have hc : (0:ℝ) < (1 - prevalence) * OperatingPoint.thresholdOdds t :=
    mul_pos (by linarith) hodds
  have h1 : prevalence * (L.point x).sensitivity
      < prevalence * (L.point y).sensitivity := mul_lt_mul_of_pos_left hslt hπ
  unfold OperatingPoint.netBenefit
  nlinarith [mul_pos hc (sub_pos.mpr hqlt)]

/-- **Deploying a worse discriminating score reclassifies patients the wrong way.**

The reclassification index between the two operating points is strictly negative: the
rule loses cases AND gains false positives, so both halves of the index are negative and
neither can offset the other. This is the statement a decision-curve paper makes and the
one the corpus could not previously reach from a demography. -/
theorem nri_neg_of_r2_lt (L : OperatingPointLaw) (x y : ℝ)
    (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    OperatingPoint.nriFromOperatingPoints (L.point y) (L.point x) < 0 :=
  OperatingPoint.nriFromOperatingPoints_neg (L.point y) (L.point x)
    (L.sensitivity_strictMono x y hx hxy hy)
    (le_of_lt (L.specificity_strictMono x y hx hxy hy))

end OperatingPointLaw

/-! ### The moment tuple reaches the clinical metrics

Two admissibility facts about `momentsUnderDrift`, restated here because every theorem in
the rest of this file needs them and `Core.Moments` proves them inline at each use. -/

/-- **The drift tuple is admissible below complete differentiation.** -/
theorem momentsUnderDrift_admissible (V_A V_E f : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (hf : f < 1) : (ScoreMoments.momentsUnderDrift V_A V_E f).Admissible := by
  refine { scoreVariance_pos := ?_, outcomeVariance_pos := ?_, cauchy_schwarz := ?_ } <;>
    unfold ScoreMoments.momentsUnderDrift retainedFraction <;> simp
  · nlinarith
  · nlinarith
  · nlinarith [sq_nonneg ((1 - f) * V_A), mul_nonneg (le_of_lt hV) (le_of_lt hE)]

/-- **And its `R²` is strictly below one**, on a trait with environmental variance. The
strict bound the law's monotonicity fields need at the upper end. -/
theorem r2_momentsUnderDrift_lt_one (V_A V_E f : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (hf : f < 1) : (ScoreMoments.momentsUnderDrift V_A V_E f).r2 < 1 := by
  rw [ScoreMoments.r2_momentsUnderDrift V_A V_E f hV (le_of_lt hE) hf]
  unfold share retainedFraction
  rw [div_lt_one (by nlinarith)]
  linarith

/-- **The `R²` of a drift tuple is non-negative.** -/
theorem r2_momentsUnderDrift_nonneg (V_A V_E f : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (hf : f < 1) : 0 ≤ (ScoreMoments.momentsUnderDrift V_A V_E f).r2 :=
  (ScoreMoments.r2_mem_unit _ (momentsUnderDrift_admissible V_A V_E f hV hE hf)).1

/-- **Every history is differentiated, strictly.**

`Core.Parameters` proves `0 ≤ fstEquilibrium` and `fstEquilibrium < 1`; the missing end
is that the lower bound is never attained. `1/(1 + x)` is strictly positive at every
finite flow, however large, so there is no demographic history at which two populations
sit at zero differentiation.

That is what makes the deployment results below unconditional rather than conditional on
"appreciable differentiation": the case they would have had to exclude does not exist. -/
theorem fstEquilibrium_pos (p : PopGenParameters) : 0 < p.fstEquilibrium := by
  have hf := p.scaledFlow_nonneg
  unfold PopGenParameters.fstEquilibrium fstIslandEquilibrium fstFromFlow
  exact div_pos one_pos (by linarith)

namespace OperatingPointLaw

/-- **The predictive value a moment tuple produces**, at a law, a prevalence and the
tuple's own discrimination. The clinical counterpart of `ScoreMoments.r2`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentPPV (L : OperatingPointLaw) (m : ScoreMoments) (prevalence : ℝ) : ℝ :=
  (L.point m.r2).positivePredictiveValue prevalence

/-- **The negative predictive value a moment tuple produces.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentNPV (L : OperatingPointLaw) (m : ScoreMoments) (prevalence : ℝ) : ℝ :=
  (L.point m.r2).negativePredictiveValue prevalence

/-- **The net benefit a moment tuple produces**, at a decision threshold.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentNetBenefit (L : OperatingPointLaw) (m : ScoreMoments)
    (prevalence t : ℝ) : ℝ :=
  (L.point m.r2).netBenefit prevalence t

/-- **The precision a moment tuple produces.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentPrecision (L : OperatingPointLaw) (m : ScoreMoments)
    (prevalence : ℝ) : ℝ :=
  (L.point m.r2).precision prevalence

/-- **The recall a moment tuple produces**, which does not see the prevalence at all.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentRecall (L : OperatingPointLaw) (m : ScoreMoments) : ℝ :=
  (L.point m.r2).recallRate

/-- **Precision at a tuple is the predictive value at that tuple.** -/
@[simp] theorem momentPrecision_eq (L : OperatingPointLaw) (m : ScoreMoments)
    (prevalence : ℝ) : L.momentPrecision m prevalence = L.momentPPV m prevalence := rfl

/-- **Recall at a tuple is the sensitivity the law gives its `R²`.** -/
@[simp] theorem momentRecall_eq (L : OperatingPointLaw) (m : ScoreMoments) :
    L.momentRecall m = (L.point m.r2).sensitivity := rfl

/-- **More differentiation, a lower predictive value.** The chain carried into the
coordinate a patient is actually told, at the level of the tuple. -/
theorem momentPPV_momentsUnderDrift_anti (L : OperatingPointLaw)
    (V_A V_E f₁ f₂ prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    L.momentPPV (ScoreMoments.momentsUnderDrift V_A V_E f₂) prevalence
      < L.momentPPV (ScoreMoments.momentsUnderDrift V_A V_E f₁) prevalence :=
  L.positivePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (r2_momentsUnderDrift_nonneg V_A V_E f₂ hV hE h2)
    (ScoreMoments.r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2)
    (le_of_lt (r2_momentsUnderDrift_lt_one V_A V_E f₁ hV hE (by linarith)))

/-- **More differentiation, a lower negative predictive value.** -/
theorem momentNPV_momentsUnderDrift_anti (L : OperatingPointLaw)
    (V_A V_E f₁ f₂ prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    L.momentNPV (ScoreMoments.momentsUnderDrift V_A V_E f₂) prevalence
      < L.momentNPV (ScoreMoments.momentsUnderDrift V_A V_E f₁) prevalence :=
  L.negativePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (r2_momentsUnderDrift_nonneg V_A V_E f₂ hV hE h2)
    (ScoreMoments.r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2)
    (le_of_lt (r2_momentsUnderDrift_lt_one V_A V_E f₁ hV hE (by linarith)))

/-- **More differentiation, a lower net benefit.** The decision-curve coordinate, carried
by the same chain. -/
theorem momentNetBenefit_momentsUnderDrift_anti (L : OperatingPointLaw)
    (V_A V_E f₁ f₂ prevalence t : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (ht : 0 < t) (ht1 : t < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    L.momentNetBenefit (ScoreMoments.momentsUnderDrift V_A V_E f₂) prevalence t
      < L.momentNetBenefit (ScoreMoments.momentsUnderDrift V_A V_E f₁) prevalence t :=
  L.netBenefit_lt_of_r2_lt prevalence t _ _ hπ hπ1 ht ht1
    (r2_momentsUnderDrift_nonneg V_A V_E f₂ hV hE h2)
    (ScoreMoments.r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2)
    (le_of_lt (r2_momentsUnderDrift_lt_one V_A V_E f₁ hV hE (by linarith)))

/-- **Recall falls with differentiation too**, which is the precision-recall curve moving
as a whole rather than trading one axis against the other. A deployment that loses
discrimination is not buying recall with precision; it is losing both. -/
theorem momentRecall_momentsUnderDrift_anti (L : OperatingPointLaw) (V_A V_E f₁ f₂ : ℝ)
    (hV : 0 < V_A) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    L.momentRecall (ScoreMoments.momentsUnderDrift V_A V_E f₂)
      < L.momentRecall (ScoreMoments.momentsUnderDrift V_A V_E f₁) :=
  L.sensitivity_strictMono _ _
    (r2_momentsUnderDrift_nonneg V_A V_E f₂ hV hE h2)
    (ScoreMoments.r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2)
    (le_of_lt (r2_momentsUnderDrift_lt_one V_A V_E f₁ hV hE (by linarith)))

/-- **Three metrics, three behaviours, one differentiation.**

`Core.Moments.drift_moves_r2_alone` is the finding that the calibration slope and the mean
squared error are blind to drift while `R²` collapses. This is the same statement with the
clinical half attached: at a differentiation where the slope has not moved and the mean
squared error has not moved, the predictive value HAS fallen, the net benefit HAS fallen,
and the reclassification index is strictly negative.

A deployment audited on calibration and error reports two perfectly stable numbers while
patients are being told a materially worse predictive value. That conjunction is the
claim, which is why it is one theorem. -/
theorem drift_moves_the_clinic_and_not_the_calibration (L : OperatingPointLaw)
    (V_A V_E f prevalence t : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (ht : 0 < t) (ht1 : t < 1) (hV : 0 < V_A) (hE : 0 < V_E) (hf0 : 0 < f) (hf : f < 1) :
    (ScoreMoments.momentsUnderDrift V_A V_E f).calibrationSlope
        = (ScoreMoments.momentsUnderDrift V_A V_E 0).calibrationSlope ∧
    (ScoreMoments.momentsUnderDrift V_A V_E f).mse
        = (ScoreMoments.momentsUnderDrift V_A V_E 0).mse ∧
    L.momentPPV (ScoreMoments.momentsUnderDrift V_A V_E f) prevalence
        < L.momentPPV (ScoreMoments.momentsUnderDrift V_A V_E 0) prevalence ∧
    L.momentNetBenefit (ScoreMoments.momentsUnderDrift V_A V_E f) prevalence t
        < L.momentNetBenefit (ScoreMoments.momentsUnderDrift V_A V_E 0) prevalence t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ScoreMoments.calibrationSlope_momentsUnderDrift V_A V_E f hV hf,
      ScoreMoments.calibrationSlope_momentsUnderDrift V_A V_E 0 hV (by norm_num)]
  · exact ScoreMoments.mse_momentsUnderDrift_const V_A V_E f 0
  · exact momentPPV_momentsUnderDrift_anti L V_A V_E 0 f prevalence hπ hπ1 hV hE hf0 hf
  · exact momentNetBenefit_momentsUnderDrift_anti L V_A V_E 0 f prevalence t hπ hπ1 ht ht1
      hV hE hf0 hf

/-! ### The full chain: a demographic history reaches the clinic

`(Nₑ, m, μ) → F_ST → moments → R² → operating point → predictive value`. Six named maps.
The corpus had the first four and stopped. -/

/-- **The predictive value a demographic history produces.**

The composition this whole file exists for: what a patient in the target population is
told, as a function of the effective size, the migration rate and the mutation rate --
rather than of a sensitivity, a specificity and a prevalence supplied by hand.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedPPV (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2 p V_E)).positivePredictiveValue prevalence

/-- **The negative predictive value a demographic history produces.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNPV (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2 p V_E)).negativePredictiveValue prevalence

/-- **The net benefit a demographic history produces**, at a decision threshold.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNetBenefit (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2 p V_E)).netBenefit prevalence t

/-- **The precision a demographic history produces.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedPrecision (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2 p V_E)).precision prevalence

/-- **The recall a demographic history produces.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedRecall (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2 p V_E)).recallRate

/-- **The reclassification index of deploying across a differentiation.**

The source rule is the one the score's own population reaches -- the operating point at
`F_ST = 0` -- and the deployed rule is the one the target reaches. The index is what a
paper would report for the move from the first to the second, and the theorems below give
its sign.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNRI (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) : ℝ :=
  OperatingPoint.nriFromOperatingPoints
    (L.point (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2)
    (L.point (ScoreMoments.deployedR2 p V_E))

/-- **Deployed precision is the deployed predictive value.** -/
@[simp] theorem deployedPrecision_eq (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) :
    L.deployedPrecision p V_E prevalence = L.deployedPPV p V_E prevalence := rfl

/-- **The single chaining lemma.**

Every demographic monotonicity below is this composed with a fact about `deployedR2`.
Stated separately so that a change in how `Core.Moments` proves those facts is a
one-line repair at each call site rather than a rewrite of each proof. -/
theorem deployedPPV_lt_of_deployedR2_lt (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 ≤ V_E)
    (hp : 0 < p.mu + p.mig) (hq : 0 < q.mu + q.mig)
    (h : ScoreMoments.deployedR2 p V_E < ScoreMoments.deployedR2 q V_E) :
    L.deployedPPV p V_E prevalence < L.deployedPPV q V_E prevalence :=
  L.positivePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (ScoreMoments.deployedR2_mem_unit p V_E hE hp).1 h
    (ScoreMoments.deployedR2_mem_unit q V_E hE hq).2

/-- **The chaining lemma for the negative predictive value.** -/
theorem deployedNPV_lt_of_deployedR2_lt (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 ≤ V_E)
    (hp : 0 < p.mu + p.mig) (hq : 0 < q.mu + q.mig)
    (h : ScoreMoments.deployedR2 p V_E < ScoreMoments.deployedR2 q V_E) :
    L.deployedNPV p V_E prevalence < L.deployedNPV q V_E prevalence :=
  L.negativePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (ScoreMoments.deployedR2_mem_unit p V_E hE hp).1 h
    (ScoreMoments.deployedR2_mem_unit q V_E hE hq).2

/-- **The chaining lemma for net benefit.** -/
theorem deployedNetBenefit_lt_of_deployedR2_lt (L : OperatingPointLaw)
    (p q : PopGenParameters) (V_E prevalence t : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1) (hE : 0 ≤ V_E)
    (hp : 0 < p.mu + p.mig) (hq : 0 < q.mu + q.mig)
    (h : ScoreMoments.deployedR2 p V_E < ScoreMoments.deployedR2 q V_E) :
    L.deployedNetBenefit p V_E prevalence t < L.deployedNetBenefit q V_E prevalence t :=
  L.netBenefit_lt_of_r2_lt prevalence t _ _ hπ hπ1 ht ht1
    (ScoreMoments.deployedR2_mem_unit p V_E hE hp).1 h
    (ScoreMoments.deployedR2_mem_unit q V_E hE hq).2

/-- **The chaining lemma for recall.** -/
theorem deployedRecall_lt_of_deployedR2_lt (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 ≤ V_E) (hp : 0 < p.mu + p.mig) (hq : 0 < q.mu + q.mig)
    (h : ScoreMoments.deployedR2 p V_E < ScoreMoments.deployedR2 q V_E) :
    L.deployedRecall p V_E < L.deployedRecall q V_E :=
  L.sensitivity_strictMono _ _ (ScoreMoments.deployedR2_mem_unit p V_E hE hp).1 h
    (ScoreMoments.deployedR2_mem_unit q V_E hE hq).2

/-! ### The three demographic parameters, four metrics each -/

/-- **More migration, a higher predictive value.** The end-to-end law in the coordinate a
patient is told: raise the migration rate between the populations and the number on the
report goes up, with every step -- equilibrium, moments, `R²`, operating point, Bayes --
a named map rather than an assumption. -/
theorem deployedPPV_mono_in_migration (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    L.deployedPPV p V_E prevalence < L.deployedPPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu]; linarith
  exact deployedPPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV hlt hflow)

/-- **More mutation, a higher predictive value.** -/
theorem deployedPPV_mono_in_mutation (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    L.deployedPPV p V_E prevalence < L.deployedPPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmig]; linarith
  exact deployedPPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_mutation p q V_E hE hNe hmig hd hV hlt hflow)

/-- **A larger effective size, a higher predictive value.** -/
theorem deployedPPV_mono_in_Ne (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    L.deployedPPV p V_E prevalence < L.deployedPPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu, ← hmig]; exact hflow
  exact deployedPPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_Ne p q V_E hE hmu hmig hd hV hlt hflow)

/-- **More migration, a higher negative predictive value.** -/
theorem deployedNPV_mono_in_migration (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    L.deployedNPV p V_E prevalence < L.deployedNPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu]; linarith
  exact deployedNPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV hlt hflow)

/-- **More mutation, a higher negative predictive value.** -/
theorem deployedNPV_mono_in_mutation (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    L.deployedNPV p V_E prevalence < L.deployedNPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmig]; linarith
  exact deployedNPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_mutation p q V_E hE hNe hmig hd hV hlt hflow)

/-- **A larger effective size, a higher negative predictive value.** -/
theorem deployedNPV_mono_in_Ne (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    L.deployedNPV p V_E prevalence < L.deployedNPV q V_E prevalence := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu, ← hmig]; exact hflow
  exact deployedNPV_lt_of_deployedR2_lt L p q V_E prevalence hπ hπ1 (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_Ne p q V_E hE hmu hmig hd hV hlt hflow)

/-- **More migration, a higher net benefit.** The decision-curve coordinate moved by a
demographic parameter: whether deploying the score is worth doing at a given threshold
depends on the migration history of the two populations. -/
theorem deployedNetBenefit_mono_in_migration (L : OperatingPointLaw)
    (p q : PopGenParameters) (V_E prevalence t : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    L.deployedNetBenefit p V_E prevalence t < L.deployedNetBenefit q V_E prevalence t := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu]; linarith
  exact deployedNetBenefit_lt_of_deployedR2_lt L p q V_E prevalence t hπ hπ1 ht ht1
    (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV hlt hflow)

/-- **More mutation, a higher net benefit.** -/
theorem deployedNetBenefit_mono_in_mutation (L : OperatingPointLaw)
    (p q : PopGenParameters) (V_E prevalence t : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    L.deployedNetBenefit p V_E prevalence t < L.deployedNetBenefit q V_E prevalence t := by
  have hq : 0 < q.mu + q.mig := by rw [← hmig]; linarith
  exact deployedNetBenefit_lt_of_deployedR2_lt L p q V_E prevalence t hπ hπ1 ht ht1
    (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_mutation p q V_E hE hNe hmig hd hV hlt hflow)

/-- **A larger effective size, a higher net benefit.** -/
theorem deployedNetBenefit_mono_in_Ne (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence t : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    L.deployedNetBenefit p V_E prevalence t < L.deployedNetBenefit q V_E prevalence t := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu, ← hmig]; exact hflow
  exact deployedNetBenefit_lt_of_deployedR2_lt L p q V_E prevalence t hπ hπ1 ht ht1
    (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_Ne p q V_E hE hmu hmig hd hV hlt hflow)

/-- **More migration, a higher recall.** -/
theorem deployedRecall_mono_in_migration (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig)
    (hflow : 0 < p.mu + p.mig) :
    L.deployedRecall p V_E < L.deployedRecall q V_E := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu]; linarith
  exact deployedRecall_lt_of_deployedR2_lt L p q V_E (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV hlt hflow)

/-- **More mutation, a higher recall.** -/
theorem deployedRecall_mono_in_mutation (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu)
    (hflow : 0 < p.mu + p.mig) :
    L.deployedRecall p V_E < L.deployedRecall q V_E := by
  have hq : 0 < q.mu + q.mig := by rw [← hmig]; linarith
  exact deployedRecall_lt_of_deployedR2_lt L p q V_E (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_mutation p q V_E hE hNe hmig hd hV hlt hflow)

/-- **A larger effective size, a higher recall.** -/
theorem deployedRecall_mono_in_Ne (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne)
    (hflow : 0 < p.mu + p.mig) :
    L.deployedRecall p V_E < L.deployedRecall q V_E := by
  have hq : 0 < q.mu + q.mig := by rw [← hmu, ← hmig]; exact hflow
  exact deployedRecall_lt_of_deployedR2_lt L p q V_E (le_of_lt hE) hflow hq
    (ScoreMoments.deployedR2_mono_in_Ne p q V_E hE hmu hmig hd hV hlt hflow)

/-! ### The fourth demographic parameter

`nDemes` is a field of `PopGenParameters` and `Core.Moments.deployedR2_anti_in_demes`
carries it to `R²`. These carry it the rest of the way. The empirical stake is on the
record: `simcov/battery_falsrepair_c2.py` falsifies the many-deme limit at `d = 20` where
the finite-deme form matches the same cells, so the deme count moves the measured
differentiation -- and these say which way it moves the number a patient is told.

Migration must be strictly positive in all four: at `m = 0` the deme count multiplies
nothing and there is no monotonicity to state. -/

/-- **More demes, a lower predictive value.** -/
theorem deployedPPV_anti_in_demes (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    L.deployedPPV q V_E prevalence < L.deployedPPV p V_E prevalence := by
  have hp : 0 < p.mu + p.mig := by have := p.mu_nonneg; linarith
  have hq : 0 < q.mu + q.mig := by
    have hqm : (0:ℝ) < q.mig := by rw [← hmig]; exact hmigpos
    linarith [q.mu_nonneg]
  exact deployedPPV_lt_of_deployedR2_lt L q p V_E prevalence hπ hπ1 (le_of_lt hE) hq hp
    (ScoreMoments.deployedR2_anti_in_demes p q V_E hE hNe hmu hmig hV hmigpos hlt)

/-- **More demes, a lower negative predictive value.** -/
theorem deployedNPV_anti_in_demes (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    L.deployedNPV q V_E prevalence < L.deployedNPV p V_E prevalence := by
  have hp : 0 < p.mu + p.mig := by have := p.mu_nonneg; linarith
  have hq : 0 < q.mu + q.mig := by
    have hqm : (0:ℝ) < q.mig := by rw [← hmig]; exact hmigpos
    linarith [q.mu_nonneg]
  exact deployedNPV_lt_of_deployedR2_lt L q p V_E prevalence hπ hπ1 (le_of_lt hE) hq hp
    (ScoreMoments.deployedR2_anti_in_demes p q V_E hE hNe hmu hmig hV hmigpos hlt)

/-- **More demes, a lower net benefit.** -/
theorem deployedNetBenefit_anti_in_demes (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence t : ℝ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (ht : 0 < t) (ht1 : t < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    L.deployedNetBenefit q V_E prevalence t < L.deployedNetBenefit p V_E prevalence t := by
  have hp : 0 < p.mu + p.mig := by have := p.mu_nonneg; linarith
  have hq : 0 < q.mu + q.mig := by
    have hqm : (0:ℝ) < q.mig := by rw [← hmig]; exact hmigpos
    linarith [q.mu_nonneg]
  exact deployedNetBenefit_lt_of_deployedR2_lt L q p V_E prevalence t hπ hπ1 ht ht1
    (le_of_lt hE) hq hp
    (ScoreMoments.deployedR2_anti_in_demes p q V_E hE hNe hmu hmig hV hmigpos hlt)

/-- **More demes, a lower recall.** -/
theorem deployedRecall_anti_in_demes (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    L.deployedRecall q V_E < L.deployedRecall p V_E := by
  have hp : 0 < p.mu + p.mig := by have := p.mu_nonneg; linarith
  have hq : 0 < q.mu + q.mig := by
    have hqm : (0:ℝ) < q.mig := by rw [← hmig]; exact hmigpos
    linarith [q.mu_nonneg]
  exact deployedRecall_lt_of_deployedR2_lt L q p V_E (le_of_lt hE) hq hp
    (ScoreMoments.deployedR2_anti_in_demes p q V_E hE hNe hmu hmig hV hmigpos hlt)

/-! ### The clinical report reads five fields and no others

`Core.Moments.deployedR2_congr` proves the deployed `R²` is a function of `Ne`, `mu`,
`mig`, `nDemes` and `V_A` alone. Everything in this file factors through that `R²`, so the
same is true of the whole clinical report -- and saying it explicitly is what makes the
rejection of a locus count and a sample size from `PopGenParameters` a fact rather than a
preference. Neither `t_div` nor `recomb` reaches a patient. -/

/-- **The deployed predictive value reads five fields.** -/
theorem deployedPPV_congr (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) :
    L.deployedPPV p V_E prevalence = L.deployedPPV q V_E prevalence := by
  unfold deployedPPV
  rw [ScoreMoments.deployedR2_congr p q V_E hNe hmu hmig hd hV]

/-- **And so does the deployed negative predictive value.** -/
theorem deployedNPV_congr (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence : ℝ) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) :
    L.deployedNPV p V_E prevalence = L.deployedNPV q V_E prevalence := by
  unfold deployedNPV
  rw [ScoreMoments.deployedR2_congr p q V_E hNe hmu hmig hd hV]

/-- **And the deployed net benefit.** -/
theorem deployedNetBenefit_congr (L : OperatingPointLaw) (p q : PopGenParameters)
    (V_E prevalence t : ℝ) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) :
    L.deployedNetBenefit p V_E prevalence t = L.deployedNetBenefit q V_E prevalence t := by
  unfold deployedNetBenefit
  rw [ScoreMoments.deployedR2_congr p q V_E hNe hmu hmig hd hV]

/-- **And the deployed reclassification index.** -/
theorem deployedNRI_congr (L : OperatingPointLaw) (p q : PopGenParameters) (V_E : ℝ)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) :
    L.deployedNRI p V_E = L.deployedNRI q V_E := by
  unfold deployedNRI
  rw [ScoreMoments.deployedR2_congr p q V_E hNe hmu hmig hd hV, hV]

/-! ### Bounds and boundaries -/

/-- **The deployed predictive value lies in the unit interval at every history**, away
from the degenerate denominator. -/
theorem deployedPPV_mem_unit (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig)
    (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1)
    (hpos : 0 < (L.point (ScoreMoments.deployedR2 p V_E)).sensitivity * prevalence
      + (1 - (L.point (ScoreMoments.deployedR2 p V_E)).specificity) * (1 - prevalence)) :
    0 ≤ L.deployedPPV p V_E prevalence ∧ L.deployedPPV p V_E prevalence ≤ 1 :=
  OperatingPoint.positivePredictiveValue_mem_unit _ prevalence
    (L.point_admissible _ (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).1
      (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).2) hπ0 hπ1 hpos

/-- **And so does the deployed negative predictive value.** -/
theorem deployedNPV_mem_unit (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig)
    (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1)
    (hpos : 0 < (L.point (ScoreMoments.deployedR2 p V_E)).specificity * (1 - prevalence)
      + (1 - (L.point (ScoreMoments.deployedR2 p V_E)).sensitivity) * prevalence) :
    0 ≤ L.deployedNPV p V_E prevalence ∧ L.deployedNPV p V_E prevalence ≤ 1 :=
  OperatingPoint.negativePredictiveValue_mem_unit _ prevalence
    (L.point_admissible _ (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).1
      (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).2) hπ0 hπ1 hpos

/-- **No history's net benefit exceeds the prevalence.** The ceiling, in the demographic
coordinates: no demography makes deploying a score worth more than finding every case for
free. -/
theorem deployedNetBenefit_le_prevalence (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig)
    (hπ0 : 0 ≤ prevalence) (hπ1 : prevalence ≤ 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    L.deployedNetBenefit p V_E prevalence t ≤ prevalence :=
  OperatingPoint.netBenefit_le_prevalence _ prevalence t
    (L.point_admissible _ (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).1
      (ScoreMoments.deployedR2_mem_unit p V_E hE hflow).2) hπ0 hπ1 ht ht1

/-! ### The threshold and the prevalence, at a fixed history

The three demographic parameters and the deme count move the report by moving `R²`. Two
more axes move it without touching the demography at all: the decision threshold, which
is a clinical choice, and the prevalence of the population deployed into, which is neither
a property of the score nor of the demography that produced it.

They are here rather than in the operating-point section because at a fixed history the
deployed point is pinned, and the strictness these need -- a sensitivity strictly above
zero, a specificity strictly below one -- is available only once the history has pinned
the `R²` strictly inside the unit interval. Those two facts come first. -/

/-- **The deployed `R²` is strictly positive at every history with flow.** -/
theorem deployedR2_pos (p : PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) : 0 < ScoreMoments.deployedR2 p V_E := by
  have hlt := p.fstEquilibrium_lt_one hflow
  have hge := p.fstEquilibrium_mem_unit.1
  have hV := p.V_A_pos
  have hr : 0 < retainedFraction p.fstEquilibrium p.V_A := by
    unfold retainedFraction; nlinarith
  rw [ScoreMoments.deployedR2_eq p V_E hE hflow]
  unfold share
  exact div_pos hr (by linarith)

/-- **And strictly below one**, on a trait with environmental variance. -/
theorem deployedR2_lt_one (p : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hflow : 0 < p.mu + p.mig) : ScoreMoments.deployedR2 p V_E < 1 := by
  unfold ScoreMoments.deployedR2
  exact r2_momentsUnderDrift_lt_one p.V_A V_E p.fstEquilibrium p.V_A_pos hE
    (p.fstEquilibrium_lt_one hflow)

/-- **A deployed score calls some cases.** Strictly positive sensitivity at every history
with flow, because the law is strictly increasing and the deployed `R²` is strictly above
zero. -/
theorem deployedPoint_sensitivity_pos (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    0 < (L.point (ScoreMoments.deployedR2 p V_E)).sensitivity := by
  have hpos := deployedR2_pos p V_E (le_of_lt hE) hflow
  have hle := (ScoreMoments.deployedR2_mem_unit p V_E (le_of_lt hE) hflow).2
  have h0 := (L.point_admissible 0 le_rfl zero_le_one).sensitivity_nonneg
  have := L.sensitivity_strictMono 0 (ScoreMoments.deployedR2 p V_E) le_rfl hpos hle
  linarith

/-- **And it makes some false positives.** Strictly sub-unit specificity, because the
deployed `R²` is strictly below one and the law is strictly increasing up to it. This is
what makes the threshold matter: a rule with no false positives is worth using at every
threshold, and no deployed score is that rule. -/
theorem deployedPoint_specificity_lt_one (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    (L.point (ScoreMoments.deployedR2 p V_E)).specificity < 1 := by
  have hlt := deployedR2_lt_one p V_E hE hflow
  have h0 := (ScoreMoments.deployedR2_mem_unit p V_E (le_of_lt hE) hflow).1
  have h1 := (L.point_admissible 1 zero_le_one le_rfl).specificity_le_one
  have := L.specificity_strictMono (ScoreMoments.deployedR2 p V_E) 1 h0 hlt le_rfl
  linarith

/-- **A higher decision threshold is a lower deployed net benefit.**

The decision curve of a deployed score, sloping down, at a fixed demographic history. The
history enters only through the guarantee that the score makes false positives at all --
which `deployedPoint_specificity_lt_one` supplies and which no deployed score escapes. -/
theorem deployedNetBenefit_anti_in_threshold (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t₁ t₂ : ℝ) (hπ1 : prevalence < 1) (hE : 0 < V_E)
    (hflow : 0 < p.mu + p.mig) (h0 : 0 ≤ t₁) (h : t₁ < t₂) (h1 : t₂ < 1) :
    L.deployedNetBenefit p V_E prevalence t₂ < L.deployedNetBenefit p V_E prevalence t₁ :=
  OperatingPoint.netBenefit_lt_of_threshold_lt _ prevalence t₁ t₂ hπ1
    (deployedPoint_specificity_lt_one L p V_E hE hflow) h0 h h1

/-- **A commoner disease raises the deployed predictive value at the same history.**

The prevalence axis, and the reason a deployed predictive value is not transportable even
between two populations with the SAME demographic relationship to the training set. Two
clinics differing only in how common the disease is report different numbers from the same
score at the same threshold, and nothing has gone wrong. -/
theorem deployedPPV_mono_in_prevalence (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E π₁ π₂ : ℝ) (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig)
    (h0 : 0 < π₁) (h : π₁ < π₂) (h1 : π₂ ≤ 1) :
    L.deployedPPV p V_E π₁ < L.deployedPPV p V_E π₂ :=
  OperatingPoint.positivePredictiveValue_lt_of_prevalence_lt _ π₁ π₂
    (deployedPoint_sensitivity_pos L p V_E hE hflow)
    (deployedPoint_specificity_lt_one L p V_E hE hflow) h0 h h1

/-- **And LOWERS the deployed negative predictive value**, at the same history and the same
threshold. The two run opposite ways, so a deployment cannot be defended on both by
choosing where to deploy -- which is the sharpest form of the warning, because the
demographic results above might otherwise be read as saying the deployment population is
the free parameter. -/
theorem deployedNPV_anti_in_prevalence (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E π₁ π₂ : ℝ) (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig)
    (h0 : 0 < π₁) (h : π₁ < π₂) (h1 : π₂ < 1) :
    L.deployedNPV p V_E π₂ < L.deployedNPV p V_E π₁ := by
  have hq : 0 < (L.point (ScoreMoments.deployedR2 p V_E)).specificity := by
    have hpos := deployedR2_pos p V_E (le_of_lt hE) hflow
    have hle := (ScoreMoments.deployedR2_mem_unit p V_E (le_of_lt hE) hflow).2
    have h0' := (L.point_admissible 0 le_rfl zero_le_one).specificity_nonneg
    have := L.specificity_strictMono 0 (ScoreMoments.deployedR2 p V_E) le_rfl hpos hle
    linarith
  have hs : (L.point (ScoreMoments.deployedR2 p V_E)).sensitivity < 1 := by
    have hlt := deployedR2_lt_one p V_E hE hflow
    have h0' := (ScoreMoments.deployedR2_mem_unit p V_E (le_of_lt hE) hflow).1
    have h1' := (L.point_admissible 1 zero_le_one le_rfl).sensitivity_le_one
    have := L.sensitivity_strictMono (ScoreMoments.deployedR2 p V_E) 1 h0' hlt le_rfl
    linarith
  exact OperatingPoint.negativePredictiveValue_lt_of_prevalence_lt _ π₁ π₂ hq hs h0 h h1

/-- **Exactly when a deployed score is not worth using**, as a function of the demographic
history, the threshold and the prevalence.

The decision-analytic bottom line. A polygenic score deployed across a differentiation is
worse than treating everyone precisely when the cases its lost discrimination causes it to
miss outweigh the unnecessary treatments it still avoids, at the exchange rate the
clinician's threshold declares. Every quantity in the condition is reachable from
`(Nₑ, m, μ, d)`, which is what the rest of this file was for. -/
theorem deployedNetBenefit_lt_treatAll_iff (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) :
    L.deployedNetBenefit p V_E prevalence t
        < OperatingPoint.treatAll.netBenefit prevalence t ↔
      (1 - prevalence) * (L.point (ScoreMoments.deployedR2 p V_E)).specificity
          * OperatingPoint.thresholdOdds t
        < prevalence * (1 - (L.point (ScoreMoments.deployedR2 p V_E)).sensitivity) :=
  OperatingPoint.netBenefit_lt_treatAll_iff _ prevalence t

/-- **Deploying across a differentiation reclassifies patients the wrong way.**

The sign of the reclassification index, from the demography alone. Any history with some
flow and some differentiation gives a strictly negative index: the deployed rule finds
fewer cases and clears fewer non-cases than the rule the source population's own score
reaches, and neither half offsets the other.

This is the clinically decisive statement the corpus could not previously make. Every
existing NRI result in the corpus takes the reclassification counts as free reals; this
one takes a demographic history.

**And it holds at EVERY history**, which is a stronger claim than it first reads. The
hypothesis is only that there is some flow -- there is no hypothesis that the populations
are appreciably differentiated, because by `fstEquilibrium_pos` there is no history at
which they are not. `1/(1 + x)` is strictly positive at every finite flow, so a
non-negative deployed index is not a case this model admits and then rules out; it is a
case the model has none of. An earlier version of this section stated a
`deployedNRI_at_source` anchor under the hypothesis `p.fstEquilibrium = 0`, which no
record satisfies -- a true, vacuous theorem asserting nothing, and it is deleted rather
than kept for symmetry. -/
theorem deployedNRI_neg (L : OperatingPointLaw) (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    L.deployedNRI p V_E < 0 := by
  have hf1 := p.fstEquilibrium_lt_one hflow
  have hlt : ScoreMoments.deployedR2 p V_E
      < (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 :=
    ScoreMoments.r2_momentsUnderDrift_anti p.V_A V_E 0 p.fstEquilibrium p.V_A_pos hE
      (fstEquilibrium_pos p) hf1
  have hsrc1 : (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 ≤ 1 :=
    le_of_lt (r2_momentsUnderDrift_lt_one p.V_A V_E 0 p.V_A_pos hE (by norm_num))
  have hdep0 : 0 ≤ ScoreMoments.deployedR2 p V_E :=
    (ScoreMoments.deployedR2_mem_unit p V_E (le_of_lt hE) hflow).1
  exact L.nri_neg_of_r2_lt _ _ hdep0 hlt hsrc1

/-- **No demographic history deploys for free.**

The contrapositive form, and the one a reader should take away: there is no setting of the
effective size, the migration rate, the mutation rate and the deme count at which the
deployed reclassification index is zero or positive. Deployment across ANY equilibrium
costs, and the cost is strict. -/
theorem deployedNRI_ne_zero (L : OperatingPointLaw) (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hflow : 0 < p.mu + p.mig) :
    L.deployedNRI p V_E ≠ 0 :=
  ne_of_lt (deployedNRI_neg L p V_E hE hflow)

/-- **A history with no flow tells every patient the prevalence and nothing more.**

At zero migration and zero mutation the equilibrium is complete differentiation, the
deployed `R²` is zero, and the operating point is whatever the law gives no
discrimination. Stated as the conjunction because that is the claim: the worst demographic
history there is drives `R²` to zero and the whole clinical report with it. -/
theorem deployedReport_at_no_flow (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) (hmu : p.mu = 0) (hmig : p.mig = 0) (hE : 0 < V_E) :
    ScoreMoments.deployedR2 p V_E = 0 ∧
    L.deployedPPV p V_E prevalence
      = (L.point 0).positivePredictiveValue prevalence ∧
    L.deployedNPV p V_E prevalence
      = (L.point 0).negativePredictiveValue prevalence ∧
    L.deployedNetBenefit p V_E prevalence t = (L.point 0).netBenefit prevalence t := by
  have hz := ScoreMoments.deployedR2_at_no_flow p V_E hmu hmig hE
  refine ⟨hz, ?_, ?_, ?_⟩ <;>
    simp only [deployedPPV, deployedNPV, deployedNetBenefit, hz]

end OperatingPointLaw

/-! ### The split coordinate is strictly monotone

These two lemmas were extracted HERE, with a note reading "`Core.Moments` does it four
times, with the same four lines. Once, here." The extraction was right and the location
could not work: this file is DOWNSTREAM of `Core.Moments`, so the consumer the note names
could not reach them and went on repeating the four lines, which is how the duplication
guard still found the block three times over. They now sit in `Core.Fst`, beside the
`fstFromTau` and `saturation` they are about and above everything that needs them. -/

/-! ### The clinical family along a clean split

The second route into the metric that `Core.Moments` already carries: a divergence time
rather than a migration-mutation balance. The whole clinical family composes with it by
the same four theorems, because the moment tuple sees a differentiation and nothing about
where it came from. -/

namespace OperatingPointLaw

/-- **The predictive value after a clean split**, from the scaled coalescence time.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedPPVFromTau (L : OperatingPointLaw)
    (V_A V_E : ℝ) (τ : Tau) (prevalence : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2FromTau V_A V_E τ)).positivePredictiveValue prevalence

/-- **The negative predictive value after a clean split.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNPVFromTau (L : OperatingPointLaw)
    (V_A V_E : ℝ) (τ : Tau) (prevalence : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2FromTau V_A V_E τ)).negativePredictiveValue prevalence

/-- **The net benefit after a clean split.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNetBenefitFromTau (L : OperatingPointLaw)
    (V_A V_E : ℝ) (τ : Tau) (prevalence t : ℝ) : ℝ :=
  (L.point (ScoreMoments.deployedR2FromTau V_A V_E τ)).netBenefit prevalence t

/-- **The split-route `R²` is non-negative.** -/
theorem deployedR2FromTau_nonneg (V_A V_E : ℝ) (τ : Tau) (hV : 0 < V_A) (hE : 0 < V_E)
    (h : 0 ≤ τ.value) : 0 ≤ ScoreMoments.deployedR2FromTau V_A V_E τ := by
  unfold ScoreMoments.deployedR2FromTau
  exact r2_momentsUnderDrift_nonneg V_A V_E (fstFromTau τ) hV hE (fstFromTau_lt_one τ h)

/-- **And at most one.** -/
theorem deployedR2FromTau_le_one (V_A V_E : ℝ) (τ : Tau) (hV : 0 < V_A) (hE : 0 < V_E)
    (h : 0 ≤ τ.value) : ScoreMoments.deployedR2FromTau V_A V_E τ ≤ 1 := by
  unfold ScoreMoments.deployedR2FromTau
  exact le_of_lt
    (r2_momentsUnderDrift_lt_one V_A V_E (fstFromTau τ) hV hE (fstFromTau_lt_one τ h))

/-- **A longer split, a lower predictive value.** The divergence-time route into the
coordinate a patient is told, so a result stated in divergence time and one stated in
migration rate reach the same place. -/
theorem deployedPPVFromTau_anti (L : OperatingPointLaw) (V_A V_E : ℝ) (t₁ t₂ : Tau)
    (prevalence : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    L.deployedPPVFromTau V_A V_E t₂ prevalence < L.deployedPPVFromTau V_A V_E t₁ prevalence :=
  L.positivePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (deployedR2FromTau_nonneg V_A V_E t₂ hV hE (by linarith))
    (ScoreMoments.deployedR2FromTau_anti V_A V_E t₁ t₂ hV hE h0 hlt)
    (deployedR2FromTau_le_one V_A V_E t₁ hV hE h0)

/-- **A longer split, a lower negative predictive value.** -/
theorem deployedNPVFromTau_anti (L : OperatingPointLaw) (V_A V_E : ℝ) (t₁ t₂ : Tau)
    (prevalence : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    L.deployedNPVFromTau V_A V_E t₂ prevalence < L.deployedNPVFromTau V_A V_E t₁ prevalence :=
  L.negativePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (deployedR2FromTau_nonneg V_A V_E t₂ hV hE (by linarith))
    (ScoreMoments.deployedR2FromTau_anti V_A V_E t₁ t₂ hV hE h0 hlt)
    (deployedR2FromTau_le_one V_A V_E t₁ hV hE h0)

/-- **A longer split, a lower net benefit.** The decision curve of a score deployed
across a divergence, as a function of the divergence. -/
theorem deployedNetBenefitFromTau_anti (L : OperatingPointLaw)
    (V_A V_E : ℝ) (t₁ t₂ : Tau) (prevalence t : ℝ)
    (hπ : 0 < prevalence) (hπ1 : prevalence < 1) (ht : 0 < t) (ht1 : t < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    L.deployedNetBenefitFromTau V_A V_E t₂ prevalence t
      < L.deployedNetBenefitFromTau V_A V_E t₁ prevalence t :=
  L.netBenefit_lt_of_r2_lt prevalence t _ _ hπ hπ1 ht ht1
    (deployedR2FromTau_nonneg V_A V_E t₂ hV hE (by linarith))
    (ScoreMoments.deployedR2FromTau_anti V_A V_E t₁ t₂ hV hE h0 hlt)
    (deployedR2FromTau_le_one V_A V_E t₁ hV hE h0)

/-- **The whole clinical report is route-agnostic.**

`Core.Moments.deployedR2_eq_deployedR2FromTau` says the equilibrium route and the split
route give the same `R²` when they give the same `F_ST`. This says the same of every
clinical metric downstream, and it is the reason the rest of this file never has to be
proved twice: a metric that read anything about WHERE the differentiation came from would
fail here. -/
theorem clinicalReport_route_agnostic (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) (τ : Tau) (h : p.fstEquilibrium = fstFromTau τ) :
    L.deployedPPV p V_E prevalence = L.deployedPPVFromTau p.V_A V_E τ prevalence ∧
    L.deployedNPV p V_E prevalence = L.deployedNPVFromTau p.V_A V_E τ prevalence ∧
    L.deployedNetBenefit p V_E prevalence t
      = L.deployedNetBenefitFromTau p.V_A V_E τ prevalence t := by
  have hr2 : ScoreMoments.deployedR2 p V_E = ScoreMoments.deployedR2FromTau p.V_A V_E τ :=
    ScoreMoments.deployedR2_eq_deployedR2FromTau p V_E τ h
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [deployedPPV, deployedNPV, deployedNetBenefit, deployedPPVFromTau,
      deployedNPVFromTau, deployedNetBenefitFromTau, hr2]

end OperatingPointLaw

/-! ### The transient route, and what it does and does not establish

`Core.Moments` reaches the metric through two coordinates: `fstEquilibrium`, the LEVEL a
migration-mutation balance settles at, and `fstFromTau`, the split law read at a scaled
coalescence time. Neither is indexed by generations, so neither can say when a population
gets where it is going.

The corpus's approach-to-equilibrium coordinate is
`Descent.Core.PopGenParameters.fstTransientAt`. Despite living in this record's namespace
it is NOT in `Core`: it is declared with `_root_.` from
`Descent/Portability/PortabilityDrift/Generational.lean` at depth thirty, and its body
calls `PopGen.fstTransientDecayFromScaled`. `Core` cannot import it and cannot redefine
it, so no theorem in this layer can mention it. That is a real gap in the layering and
not a gap this file can close: the repair is to move `fstTransientAt` and `tauAt` DOWN,
which is a thirty-module edit.

What is reachable is the generation-indexed reading of the split law, below. It is a
different quantity from `fstTransientAt` and the difference is the whole point of this
section: an isolated split keeps differentiating without bound, while a
migration-mutation balance plateaus. So the two coordinates CROSS -- they agree at exactly
one generation, which the record's own parameters determine, and after it the split law
strictly exceeds the equilibrium level. Both facts are theorems here.

A reader who wanted "the transient approaches the equilibrium from below and converges to
it" will not find it, because for THIS coordinate it is false, and the coordinate for
which it is true is out of reach. -/

namespace PopGenParameters

/-- **Differentiation after `t` generations of isolation**, `τ/(1+τ)` at `τ = t/(2Nₑ)`.

The clean-split law in generations rather than in scaled coalescent time. `t/(2Nₑ)` is the
corpus's scaled time -- the same conversion
`Descent.Core.PopGenParameters.tauAt` carries in `Portability/PortabilityDrift/
Generational.lean`, whose docstring records the measurement that pins the two: the
composition `exp(-θτ)` is checked at six cells where `Nₑ` runs over a factor of eight and
cancels, and halving or doubling this factor is excluded by hundreds of sems. That
declaration is above `Core` and cannot be called from here; when it moves down, this body
should call it rather than repeat it.

**This is a HUDSON `F_ST`, by the corpus's standing rule and not by choice**: it is
`Core.fstFromTau` of a scaled time, and every `F_ST` written in `τ/(1+τ)` coordinates in
this corpus is Hudson. Nei's `G_ST` is falsified at up to 18.59 sems against this same
split law where Hudson's matches at 0.03, and the ratio between them moves with the data,
so there is no factor converting a value computed here into a Nei one.

**Regime: ISOLATION.** This is the law for two populations exchanging nothing. With
migration the differentiation plateaus rather than saturating, and substituting one for
the other is an error the corpus has already paid for.
`fstEquilibrium_lt_fstAtGeneration_of_late` below is the machine-checked form of that
warning, and it is where the measurement which bears on the substitution is cited -- not
here. The run in question falsifies a DIFFERENT body, `Generational.fstTransientAt`'s
superseded decay base, and a battery named in this docstring would say that a run bore on
THIS one, which is the reading `Meta.Linters.coreStatusDenied` exists to catch and did.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def fstAtGeneration (p : PopGenParameters) (t : ℕ) : ℝ :=
  fstFromTau (Tau.ofGenerations (t : ℝ) p.Ne)

/-- **At the split nothing has differentiated.** -/
@[simp] theorem fstAtGeneration_zero (p : PopGenParameters) : p.fstAtGeneration 0 = 0 := by
  unfold fstAtGeneration fstFromTau saturation
  rw [Tau.value_ofGenerations]
  norm_num

/-- **The scaled time is non-negative**, which every bound below rests on.

Stated on `Tau.ofGenerations`'s own value rather than on `t/(2 Nₑ)` written out, so that
the `2` in it is `ploidy` and the same `ploidy` every other scaling in the corpus carries.
Writing the quotient out instead is how a corpus ends up with `t/(2 Nₑ)` in one file and
`t/(4 Nₑ)` in another. -/
theorem scaledTime_nonneg (p : PopGenParameters) (t : ℕ) :
    (0:ℝ) ≤ (Tau.ofGenerations (t : ℝ) p.Ne).value := by
  have hNe := p.Ne_pos
  rw [Tau.value_ofGenerations]
  exact div_nonneg (Nat.cast_nonneg t) (by linarith)

/-- **Transient differentiation is non-negative.** -/
theorem fstAtGeneration_nonneg (p : PopGenParameters) (t : ℕ) :
    0 ≤ p.fstAtGeneration t :=
  (fstFromTau_mem_unit _ (p.scaledTime_nonneg t)).1

/-- **And strictly below one at every finite generation.** Complete differentiation is a
limit and not a value the split law takes: two populations separated for any finite time
still share allele frequencies. -/
theorem fstAtGeneration_lt_one (p : PopGenParameters) (t : ℕ) :
    p.fstAtGeneration t < 1 :=
  fstFromTau_lt_one _ (p.scaledTime_nonneg t)

/-- **Transient differentiation lies in the unit interval.** -/
theorem fstAtGeneration_mem_unit (p : PopGenParameters) (t : ℕ) :
    0 ≤ p.fstAtGeneration t ∧ p.fstAtGeneration t ≤ 1 :=
  ⟨p.fstAtGeneration_nonneg t, le_of_lt (p.fstAtGeneration_lt_one t)⟩

/-- **Longer isolation, more differentiation.** Strictly increasing in the generation
count, which is what makes this a transient rather than a level. -/
theorem fstAtGeneration_strictMono (p : PopGenParameters) (t₁ t₂ : ℕ) (h : t₁ < t₂) :
    p.fstAtGeneration t₁ < p.fstAtGeneration t₂ := by
  have hNe := p.Ne_pos
  have hcast : (t₁ : ℝ) < (t₂ : ℝ) := by exact_mod_cast h
  have hτ : (Tau.ofGenerations (t₁ : ℝ) p.Ne).value
      < (Tau.ofGenerations (t₂ : ℝ) p.Ne).value := by
    rw [Tau.value_ofGenerations, Tau.value_ofGenerations,
      div_lt_div_iff₀ (by linarith) (by linarith)]
    exact mul_lt_mul_of_pos_right hcast (by linarith)
  exact fstFromTau_lt_fstFromTau _ _ (p.scaledTime_nonneg t₁) hτ

/-- **The equilibrium level IS the split law, at scaled time `1/x`.**

`1/(1 + x)` and `τ/(1 + τ)` are the same curve read from the two ends, so the level a
migration-mutation balance settles at is the differentiation an ISOLATED pair reaches
after scaled time `1/x`, where `x` is the record's total scaled flow. That is the
conversion between the corpus's two `F_ST` coordinates, made explicit rather than left for
a reader to rediscover, and it is what makes the crossing theorems below statements about
one curve rather than two.

Written through `Core.scaledFlow` at the record's own deme count, so the deme correction
`d/(d-1)` is carried into the equilibration time as well: a lattice with more demes
differentiates to a higher level AND takes a different number of generations to get
there. -/
theorem fstEquilibrium_eq_fstFromTau_inv (p : PopGenParameters)
    (h : 0 < scaledFlow p.bigM p.theta p.nDemes) :
    p.fstEquilibrium = fstFromTau ⟨1 / scaledFlow p.bigM p.theta p.nDemes⟩ := by
  have hinv : (0:ℝ) < 1 / scaledFlow p.bigM p.theta p.nDemes := div_pos one_pos h
  have h1 : (1:ℝ) + scaledFlow p.bigM p.theta p.nDemes ≠ 0 := by
    have hpos : (0:ℝ) < 1 + scaledFlow p.bigM p.theta p.nDemes := by linarith
    exact hpos.ne'
  have h2 : (1:ℝ) + 1 / scaledFlow p.bigM p.theta p.nDemes ≠ 0 := by
    have hpos : (0:ℝ) < 1 + 1 / scaledFlow p.bigM p.theta p.nDemes := by linarith
    exact hpos.ne'
  have hx : scaledFlow p.bigM p.theta p.nDemes ≠ 0 := h.ne'
  unfold fstEquilibrium fstIslandEquilibrium fstFromFlow fstFromTau saturation
  dsimp only
  rw [div_eq_div_iff h1 h2]
  field_simp
  ring

/-- **The two routes agree at exactly one generation**, and the condition says which.

`Core.Moments.fstEquilibrium_eq_fstFromTau_iff` states this in scaled time; this is the
same statement with the generation count in it, so a reader can ask "how long until this
population is as differentiated as its own equilibrium says it will be" and get an
answer. -/
theorem fstAtGeneration_eq_fstEquilibrium_iff (p : PopGenParameters) (t : ℕ) :
    p.fstEquilibrium = p.fstAtGeneration t ↔
      1 = (Tau.ofGenerations (t : ℝ) p.Ne).value
          * scaledFlow p.bigM p.theta p.nDemes := by
  have hflow := p.scaledFlow_nonneg
  have h0 := p.scaledTime_nonneg t
  have hx : (1:ℝ) + scaledFlow p.bigM p.theta p.nDemes ≠ 0 := by
    have hpos : (0:ℝ) < 1 + scaledFlow p.bigM p.theta p.nDemes := by linarith
    exact hpos.ne'
  have ht : (1:ℝ) + (Tau.ofGenerations (t : ℝ) p.Ne).value ≠ 0 := by
    have hpos : (0:ℝ) < 1 + (Tau.ofGenerations (t : ℝ) p.Ne).value := by linarith
    exact hpos.ne'
  unfold fstAtGeneration
  exact ScoreMoments.fstEquilibrium_eq_fstFromTau_iff p (Tau.ofGenerations (t : ℝ) p.Ne) hx ht

/-- **The equilibration generation, named.** At `t = 2Nₑ/x` the isolated pair has reached
exactly the differentiation the migration-mutation balance settles at. Before that
generation the transient is below the level; after it, above -- which is the next theorem
and is why "the transient converges to the equilibrium" is false for this coordinate.

The hypothesis asks that `2Nₑ/x` IS a whole number of generations, and for most records it
is not: generations are discrete and the equilibration time is a real. So this is an exact
crossing when the arithmetic happens to land on a generation, and otherwise the crossing
is bracketed rather than attained -- `fstAtGeneration_lt_fstEquilibrium_of_early` at the
generation below and `fstEquilibrium_lt_fstAtGeneration_of_late` at the one above, which
between them locate it without needing it to be hit. Stated this way rather than by
rounding, because a rounded generation is a different number and the theorem would be
about the rounding. -/
theorem fstAtGeneration_eq_fstEquilibrium_of_equilibrationTime (p : PopGenParameters)
    (t : ℕ) (hflow : 0 < scaledFlow p.bigM p.theta p.nDemes)
    (h : (t : ℝ) = 2 * p.Ne / scaledFlow p.bigM p.theta p.nDemes) :
    p.fstEquilibrium = p.fstAtGeneration t := by
  have hNe := p.Ne_pos
  have hx : scaledFlow p.bigM p.theta p.nDemes ≠ 0 := hflow.ne'
  have h2 : (2:ℝ) * p.Ne ≠ 0 := by positivity
  rw [p.fstAtGeneration_eq_fstEquilibrium_iff t, Tau.value_ofGenerations, h]
  field_simp

/-- **Before the equilibration generation the transient is strictly below the level.**
The direction a reader expects, and it holds -- but only on this side. -/
theorem fstAtGeneration_lt_fstEquilibrium_of_early (p : PopGenParameters) (t : ℕ)
    (hflow : 0 < scaledFlow p.bigM p.theta p.nDemes)
    (hearly : (Tau.ofGenerations (t : ℝ) p.Ne).value
      < 1 / scaledFlow p.bigM p.theta p.nDemes) :
    p.fstAtGeneration t < p.fstEquilibrium := by
  rw [p.fstEquilibrium_eq_fstFromTau_inv hflow]
  exact fstFromTau_lt_fstFromTau _ _ (p.scaledTime_nonneg t) hearly

/-- **And after it the transient strictly EXCEEDS the level, without bound.**

This is the theorem that says the generation-indexed split law is not an
approach-to-equilibrium coordinate, and it is stated because assuming otherwise is a
known-expensive error. An isolated pair keeps differentiating; a pair exchanging migrants
plateaus.

**This is where the measurement on that substitution is cited, and `fstAtGeneration`'s own
docstring is where it is not.** A battery named on the DEFINITION would assert that the run
bore on that body; it did not -- it falsified the superseded within-deme decay base of
`Generational.fstTransientAt`, which is a different quantity. Naming it on this theorem
says what is true: a run measured the substitution, and this is the statement that rules it
out.

Substituting the first for the second is what
`Generational.fstTransientAt`'s docstring records as FALSIFIED at up to 2222 sems, and a
reader who took `fstAtGeneration` for a transient under migration would be making it
again.

The corpus's coordinate for the migration case is `fstTransientAt`, which this layer
cannot reach; see the section header. -/
theorem fstEquilibrium_lt_fstAtGeneration_of_late (p : PopGenParameters) (t : ℕ)
    (hflow : 0 < scaledFlow p.bigM p.theta p.nDemes)
    (hlate : 1 / scaledFlow p.bigM p.theta p.nDemes
      < (Tau.ofGenerations (t : ℝ) p.Ne).value) :
    p.fstEquilibrium < p.fstAtGeneration t := by
  have hinv : (0:ℝ) ≤ 1 / scaledFlow p.bigM p.theta p.nDemes :=
    le_of_lt (div_pos one_pos hflow)
  rw [p.fstEquilibrium_eq_fstFromTau_inv hflow]
  exact fstFromTau_lt_fstFromTau _ _ hinv hlate

/-- **A history with no flow is never reached in finite time.**

At zero migration and zero mutation the equilibrium is complete differentiation, and the
transient is strictly below one at every generation. So the one demographic history whose
equilibrium the transient can never cross is the isolated one -- which is right, and is
the boundary case the two coordinates agree about. -/
theorem fstAtGeneration_lt_fstEquilibrium_at_no_flow (p : PopGenParameters) (t : ℕ)
    (hmu : p.mu = 0) (hmig : p.mig = 0) :
    p.fstAtGeneration t < p.fstEquilibrium := by
  have hz : scaledFlow p.bigM p.theta p.nDemes = 0 := by
    rw [p.scaledFlow_eq, hmu, hmig]
    ring
  have heq : p.fstEquilibrium = 1 := by
    unfold fstEquilibrium fstIslandEquilibrium
    rw [hz]
    exact fstFromFlow_zero
  rw [heq]
  exact p.fstAtGeneration_lt_one t

/-- **The deployed `R²` after `t` generations of isolation.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedR2AtGeneration (p : PopGenParameters) (V_E : ℝ) (t : ℕ) : ℝ :=
  (ScoreMoments.momentsUnderDrift p.V_A V_E (p.fstAtGeneration t)).r2

/-- **At the split the deployed metric is the source metric.** -/
theorem deployedR2AtGeneration_at_zero (p : PopGenParameters) (V_E : ℝ) :
    p.deployedR2AtGeneration V_E 0 = (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 := by
  unfold deployedR2AtGeneration
  rw [p.fstAtGeneration_zero]

/-- **Longer isolation, less transferable score.** The transient route's monotone law, in
generations. -/
theorem deployedR2AtGeneration_anti (p : PopGenParameters) (V_E : ℝ) (t₁ t₂ : ℕ)
    (hE : 0 < V_E) (h : t₁ < t₂) :
    p.deployedR2AtGeneration V_E t₂ < p.deployedR2AtGeneration V_E t₁ :=
  ScoreMoments.r2_momentsUnderDrift_anti p.V_A V_E (p.fstAtGeneration t₁)
    (p.fstAtGeneration t₂) p.V_A_pos hE (p.fstAtGeneration_strictMono t₁ t₂ h)
    (p.fstAtGeneration_lt_one t₂)

/-- **The transient `R²` is non-negative.** -/
theorem deployedR2AtGeneration_nonneg (p : PopGenParameters) (V_E : ℝ) (t : ℕ)
    (hE : 0 < V_E) : 0 ≤ p.deployedR2AtGeneration V_E t :=
  r2_momentsUnderDrift_nonneg p.V_A V_E (p.fstAtGeneration t) p.V_A_pos hE
    (p.fstAtGeneration_lt_one t)

/-- **And at most one.** -/
theorem deployedR2AtGeneration_le_one (p : PopGenParameters) (V_E : ℝ) (t : ℕ)
    (hE : 0 < V_E) : p.deployedR2AtGeneration V_E t ≤ 1 :=
  le_of_lt (r2_momentsUnderDrift_lt_one p.V_A V_E (p.fstAtGeneration t) p.V_A_pos hE
    (p.fstAtGeneration_lt_one t))

/-- **The transient route reaches the equilibrium route's metric, at the equilibration
generation.**

The `R²` half of the agreement. Both routes feed the same `momentsUnderDrift`, so they
agree exactly when they agree on `F_ST`, and the generation at which they do is the one
`fstAtGeneration_eq_fstEquilibrium_of_equilibrationTime` names. -/
theorem deployedR2AtGeneration_eq_deployedR2 (p : PopGenParameters) (V_E : ℝ) (t : ℕ)
    (h : p.fstEquilibrium = p.fstAtGeneration t) :
    p.deployedR2AtGeneration V_E t = ScoreMoments.deployedR2 p V_E := by
  unfold deployedR2AtGeneration ScoreMoments.deployedR2
  rw [h]

end PopGenParameters

namespace OperatingPointLaw

/-- **The predictive value after `t` generations of isolation.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedPPVAtGeneration (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (t : ℕ) : ℝ :=
  (L.point (p.deployedR2AtGeneration V_E t)).positivePredictiveValue prevalence

/-- **The negative predictive value after `t` generations of isolation.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNPVAtGeneration (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (t : ℕ) : ℝ :=
  (L.point (p.deployedR2AtGeneration V_E t)).negativePredictiveValue prevalence

/-- **The net benefit after `t` generations of isolation.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNetBenefitAtGeneration (L : OperatingPointLaw)
    (p : PopGenParameters) (V_E prevalence t : ℝ) (gen : ℕ) : ℝ :=
  (L.point (p.deployedR2AtGeneration V_E gen)).netBenefit prevalence t

/-- **The reclassification index of `t` generations of isolation.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedNRIAtGeneration (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) (t : ℕ) : ℝ :=
  OperatingPoint.nriFromOperatingPoints
    (L.point (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2)
    (L.point (p.deployedR2AtGeneration V_E t))

/-- **Longer isolation, a lower predictive value.** The transient route reaching the
number a patient is told. -/
theorem deployedPPVAtGeneration_anti (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (t₁ t₂ : ℕ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hE : 0 < V_E) (h : t₁ < t₂) :
    L.deployedPPVAtGeneration p V_E prevalence t₂
      < L.deployedPPVAtGeneration p V_E prevalence t₁ :=
  L.positivePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (p.deployedR2AtGeneration_nonneg V_E t₂ hE)
    (p.deployedR2AtGeneration_anti V_E t₁ t₂ hE h)
    (p.deployedR2AtGeneration_le_one V_E t₁ hE)

/-- **Longer isolation, a lower negative predictive value.** -/
theorem deployedNPVAtGeneration_anti (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence : ℝ) (t₁ t₂ : ℕ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (hE : 0 < V_E) (h : t₁ < t₂) :
    L.deployedNPVAtGeneration p V_E prevalence t₂
      < L.deployedNPVAtGeneration p V_E prevalence t₁ :=
  L.negativePredictiveValue_lt_of_r2_lt prevalence _ _ hπ hπ1
    (p.deployedR2AtGeneration_nonneg V_E t₂ hE)
    (p.deployedR2AtGeneration_anti V_E t₁ t₂ hE h)
    (p.deployedR2AtGeneration_le_one V_E t₁ hE)

/-- **Longer isolation, a lower net benefit.** -/
theorem deployedNetBenefitAtGeneration_anti (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E prevalence t : ℝ) (g₁ g₂ : ℕ) (hπ : 0 < prevalence) (hπ1 : prevalence < 1)
    (ht : 0 < t) (ht1 : t < 1) (hE : 0 < V_E) (h : g₁ < g₂) :
    L.deployedNetBenefitAtGeneration p V_E prevalence t g₂
      < L.deployedNetBenefitAtGeneration p V_E prevalence t g₁ :=
  L.netBenefit_lt_of_r2_lt prevalence t _ _ hπ hπ1 ht ht1
    (p.deployedR2AtGeneration_nonneg V_E g₂ hE)
    (p.deployedR2AtGeneration_anti V_E g₁ g₂ hE h)
    (p.deployedR2AtGeneration_le_one V_E g₁ hE)

/-- **Isolation reclassifies patients the wrong way, at every generation past the
split.** -/
theorem deployedNRIAtGeneration_neg (L : OperatingPointLaw) (p : PopGenParameters)
    (V_E : ℝ) (t : ℕ) (hE : 0 < V_E) (ht : 0 < t) :
    L.deployedNRIAtGeneration p V_E t < 0 := by
  have h0 : p.deployedR2AtGeneration V_E 0
      = (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 :=
    p.deployedR2AtGeneration_at_zero V_E
  have hlt : p.deployedR2AtGeneration V_E t
      < (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 := by
    rw [← h0]
    exact p.deployedR2AtGeneration_anti V_E 0 t hE ht
  have hsrc : (ScoreMoments.momentsUnderDrift p.V_A V_E 0).r2 ≤ 1 := by
    rw [← h0]
    exact p.deployedR2AtGeneration_le_one V_E 0 hE
  exact L.nri_neg_of_r2_lt _ _ (p.deployedR2AtGeneration_nonneg V_E t hE) hlt hsrc

/-- **The transient and the equilibrium routes reach the SAME clinical report, at the
equilibration generation.**

This is the agreement the two routes have and the whole of it. It is not convergence: by
`fstEquilibrium_lt_fstAtGeneration_of_late` the transient overshoots afterwards. It is a
crossing, at the one generation `fstAtGeneration_eq_fstEquilibrium_of_equilibrationTime`
names, and at that generation every clinical metric agrees because all of them factor
through `R²` and `R²` factors through `F_ST`. -/
theorem clinicalReport_transient_eq_equilibrium (L : OperatingPointLaw)
    (p : PopGenParameters) (V_E prevalence t : ℝ) (gen : ℕ)
    (h : p.fstEquilibrium = p.fstAtGeneration gen) :
    L.deployedPPVAtGeneration p V_E prevalence gen = L.deployedPPV p V_E prevalence ∧
    L.deployedNPVAtGeneration p V_E prevalence gen = L.deployedNPV p V_E prevalence ∧
    L.deployedNetBenefitAtGeneration p V_E prevalence t gen
      = L.deployedNetBenefit p V_E prevalence t ∧
    L.deployedNRIAtGeneration p V_E gen = L.deployedNRI p V_E := by
  have hr2 : p.deployedR2AtGeneration V_E gen = ScoreMoments.deployedR2 p V_E :=
    p.deployedR2AtGeneration_eq_deployedR2 V_E gen h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [deployedPPVAtGeneration, deployedNPVAtGeneration,
      deployedNetBenefitAtGeneration, deployedNRIAtGeneration, deployedPPV, deployedNPV,
      deployedNetBenefit, deployedNRI, hr2]

end OperatingPointLaw

/-! ### The F1 score

Moved here from `Program/OpenQuestions.lean`. An F1 score is the harmonic mean of two
reals; it carries no programme content, and its being in the programme narrative meant that
`Portability/MetricSpecificPortability/PrecisionRecall.lean` -- which states the one theorem
about it that the corpus has -- imported the audit layer at the top of the graph to reach a
formula in two arguments. That file's own header had already written down the repair:
"the repair is to move `f1Score` down, since an F1 formula is a classifier metric and
carries no programme content." This is that move.

It belongs in this file rather than anywhere else lower: `positivePredictiveValue`,
`negativePredictiveValue`, `netBenefit` and `nriFromOperatingPoints` are here, and F1 is a
member of that family -- the harmonic mean of the precision and the recall that
`OperatingPoint` already carries. -/

/-- **F1 score**: the harmonic mean of precision and sensitivity.

    Empirical status: UNTESTED. -/
noncomputable def f1Score (precision sensitivity : ℝ) : ℝ :=
  2 * precision * sensitivity / (precision + sensitivity)

/-- **f1Score where its denominator vanishes, named.** The guard `precision + sensitivity` is zero
at `precision = 0`, `sensitivity = 0`. A classifier with neither precision nor sensitivity has
no F1 score; the value returned is indistinguishable from a classifier that fires and is always
wrong. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `precision + sensitivity ≠ 0`. -/
theorem f1Score_at_precision0sensitivity0_is_junk :
    f1Score 0 0 = 0 := by
  unfold f1Score
  norm_num

/-- **F1 score is symmetric in precision and recall.** -/
theorem f1_symmetric (p r : ℝ) : f1Score p r = f1Score r p := by
  unfold f1Score; ring

/-- **F1 score ≤ arithmetic mean of precision and recall**, the harmonic-arithmetic mean
    inequality for two positive reals.

    Do not head this "F1 score ≤ max(precision, recall)". Of the chain
    `harmonic ≤ arithmetic ≤ max`, only the first inequality is proved. The bound by the
    max is strictly weaker and no theorem here establishes it. The name states exactly
    what is proved. -/
theorem f1_le_arithmetic_mean (p r : ℝ)
    (hp : 0 < p) (hr : 0 < r) :
    f1Score p r ≤ (p + r) / 2 := by
  unfold f1Score
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [sq_nonneg (p - r)]

/-- **F1 is bounded above by one** when both precision and sensitivity lie in `(0, 1]`.
Moved here with the definition from `Portability/MetricSpecificPortability/PrecisionRecall.lean`,
which is where it was and which had to import the programme narrative to say it. -/
theorem f1_le_one (precision sens : ℝ)
    (h_p : 0 < precision) (h_r : 0 < sens)
    (h_p1 : precision ≤ 1) (h_r1 : sens ≤ 1) :
    f1Score precision sens ≤ 1 := by
  unfold f1Score
  rw [div_le_one (by linarith)]
  nlinarith [mul_nonneg (le_of_lt h_p) (by linarith : 0 ≤ 1 - sens),
             mul_nonneg (le_of_lt h_r) (by linarith : 0 ≤ 1 - precision)]

end Descent.Core
