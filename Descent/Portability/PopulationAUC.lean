/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# Population AUC in conditional-law form

A binary-outcome population is a pair of measures on the feature space -- the law of the
features given a case, and the law given a control. The AUC of a score against it is the
probability that the score ranks a case above a control, with ties split evenly.

All of this needs is those two conditional laws and a real-valued score. There is no
transport in it: one population, one score, no quantity being carried anywhere. It sits at
the bottom of the chapter for that reason, and because three separate modules state
discrimination results in these terms -- `PGSCalibrationTheory.RecalibrationMethods`,
`PGSCalibrationTheory.CalibrationVsDiscrimination` and
`MetricSpecificPortability.R2Decomposition` -- none of which is below the others.

`populationAUC_strictMono_invariant` is the theorem all three reach for. AUC sees only the
order a score induces, so any strictly increasing reparametrisation of a score -- a
logistic recalibration, an affine rescaling, a shift -- leaves it unchanged. That is the
exact sense in which calibration and discrimination are separate questions: an intervention
can move every predicted probability and move no AUC at all.
-/

universe u

/-- Binary-outcome population described by the conditional feature laws:
`Z⁺ ~ law(Z|Y=1)`, `Z⁻ ~ law(Z|Y=0)`, independent. -/
structure BinaryPopulation (Z : Type u) [MeasurableSpace Z] where
  μpos : Measure Z
  μneg : Measure Z

/-- **The two-point population**: all case mass at `zpos`, all control mass at
`zneg`.

`BinaryPopulation` had no exhibited inhabitant, so the AUC invariance result
below was quantified over a class nothing had been shown to belong to. This is
the smallest population on which an AUC is a real comparison rather than an
integral against nothing: exactly one case value and one control value, which is
the configuration the `>` and `=` terms of `populationAUC` were written to
separate. -/
noncomputable def BinaryPopulation.ofPoints {Z : Type u} [MeasurableSpace Z]
    (zpos zneg : Z) : BinaryPopulation Z where
  μpos := Measure.dirac zpos
  μneg := Measure.dirac zneg

/-- The class is inhabited whenever the sample space has a point. The side
condition is not an artefact: an AUC compares a case value with a control value,
so an empty sample space has no population for it to be about, and requiring
`Nonempty Z` says so rather than substituting a zero measure on which every AUC
term vanishes. -/
instance BinaryPopulation.instNonempty {Z : Type u} [MeasurableSpace Z] [Nonempty Z] :
    Nonempty (BinaryPopulation Z) :=
  ⟨BinaryPopulation.ofPoints (Classical.arbitrary Z) (Classical.arbitrary Z)⟩

/-- Population AUC of a score:
`P(s(Z⁺) > s(Z⁻)) + 1/2 P(s(Z⁺)=s(Z⁻))`. -/
noncomputable def populationAUC {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (s : Z → ℝ) : ENNReal :=
  (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 > s zz.2} +
    (ENNReal.ofReal (1 / 2 : ℝ)) *
      (pop.μpos.prod pop.μneg) {zz : Z × Z | s zz.1 = s zz.2}

theorem populationAUC_strictMono_invariant {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (s : Z → ℝ) (g : ℝ → ℝ) (hg : StrictMono g) :
    populationAUC pop (g ∘ s) = populationAUC pop s := by
  unfold populationAUC
  have h_gt :
      {zz : Z × Z | g (s zz.1) > g (s zz.2)} = {zz : Z × Z | s zz.1 > s zz.2} := by
    ext zz
    exact hg.lt_iff_lt
  have h_eq :
      {zz : Z × Z | g (s zz.1) = g (s zz.2)} = {zz : Z × Z | s zz.1 = s zz.2} := by
    ext zz
    constructor <;> intro h
    · exact hg.injective h
    · simpa using congrArg g h
  simp [h_gt, h_eq]

/-- A strictly increasing transform of an AUC-optimal posterior score is also AUC-optimal. -/
theorem populationAUC_optimal_of_eta_transform {Z : Type u} [MeasurableSpace Z]
    (pop : BinaryPopulation Z) (η score : Z → ℝ)
    (h_opt_eta : ∀ s : Z → ℝ, populationAUC pop s ≤ populationAUC pop η)
    (h_rep : ∃ g : ℝ → ℝ, StrictMono g ∧ score = g ∘ η) :
    ∀ s : Z → ℝ, populationAUC pop s ≤ populationAUC pop score := by
  rcases h_rep with ⟨g, hg, hscore⟩
  intro s
  have h_eq : populationAUC pop score = populationAUC pop η := by
    rw [hscore]
    exact populationAUC_strictMono_invariant pop η g hg
  calc
    populationAUC pop s ≤ populationAUC pop η := h_opt_eta s
    _ = populationAUC pop score := h_eq.symm

end Descent.Portability
