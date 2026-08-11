/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Descent.Blindness.EffectSizeSurgery

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

/-!
# Fiber surgery is an observational symmetry

`Descent.Blindness.EffectSizeSurgery` proves that moving effect mass between `+s` and `-s`
leaves every even summary of the distribution unmoved and changes every non-degenerate odd
one. That file is deliberately self-contained — it can be read without any of this
development — so the translation into the corpus's identifiability vocabulary lives here
instead of there.

The translation is exact. `Fiber.transfer` is a transformation of the parameter, the
even-summary report is an observation it preserves *at every fiber*, and the imbalance is a
target it moves. That is an `ObservationalSymmetry`, and
`ObservationalSymmetry.no_target_criterion` then says what the surgery result was always
about: no procedure reading even summaries decides the imbalance, whatever the procedure.

## Why both halves are stated

`imbalance_not_identifiedBy_evenSummaryReport` is the negative half and
`imbalance_identifiedBy_oddSummary` is the positive one, and the pair is the point. The
even class — heritability, LD-score regression, stratified heritability, moment-based
polygenicity — is blind to the imbalance as a matter of arithmetic, while a single odd
summary at a magnitude where it does not vanish pins the imbalance exactly, by division.
So this is not an experimental limit dressed up as a theorem: the information is in the
data, and the summaries in use discard it. `IdentifiedBy` is what makes that contrast
statable in one vocabulary rather than as two unrelated observations.

The observation here is the whole even class at once, not one summary at a time: the
report a fiber makes to every even summary there is. Blindness of the entire class is
therefore a single `ObservationalSymmetry`, rather than one witness per estimator.
-/

/-- **What a fiber reports to every even summary at once.** The observation whose blindness
is at issue: not one estimator's value, but the whole even class's, as one object. -/
def evenSummaryReport (F : Fiber) : {summary : ℝ → ℝ // IsEvenSummary summary} → ℝ :=
  fun summary ↦ F.contribution summary.val

/-- **Fiber surgery, as an observational symmetry.** The transformation is the transfer;
the invariance is `Fiber.even_summary_blind_to_transfer` at every fiber and every even
summary; the moved target is the imbalance, which the transfer shifts by `2δ`. -/
def fiberTransferSymmetry (shift : ℝ) (hshift : shift ≠ 0) (baseFiber : Fiber) :
    ObservationalSymmetry evenSummaryReport Fiber.imbalance where
  transform := fun fiber ↦ fiber.transfer shift
  observation_invariant := by
    intro fiber
    funext summary
    exact fiber.even_summary_blind_to_transfer summary.property shift
  moved := baseFiber
  target_moved := by
    rw [Fiber.transfer_imbalance]
    intro hcontra
    exact hshift (by linarith)

/-- **The imbalance is not identified by the even class.** Not poorly estimated by it: not
a function of it. One transfer of unit mass at one fiber is the whole refutation. -/
theorem imbalance_not_identifiedBy_evenSummaryReport :
    ¬ IdentifiedBy evenSummaryReport Fiber.imbalance :=
  not_identifiedBy_of_observationalSymmetry
    (fiberTransferSymmetry 1 one_ne_zero ⟨1, 0, 0⟩)

/-- **No procedure reading even summaries decides the imbalance.** The general law applied
to `fiberTransferSymmetry`: for any post-processing of the even-class report and any
acceptance region, the verdict is the same at a fiber and at its transfer while the
imbalance is not. -/
theorem no_evenSummary_criterion_decides_imbalance :
    ¬ ∃ decideValue : ({summary : ℝ → ℝ // IsEvenSummary summary} → ℝ) → Prop,
      ∀ fiber : Fiber, fiber.imbalance = ((⟨1, 0, 0⟩ : Fiber).transfer 1).imbalance
        ↔ decideValue (evenSummaryReport fiber) :=
  (fiberTransferSymmetry 1 one_ne_zero ⟨1, 0, 0⟩).no_target_criterion

/-- **One odd summary pins the imbalance, at a fixed magnitude.** The positive half, in the
same vocabulary: at a magnitude where the summary does not vanish, the imbalance IS a
function of what that single odd summary reports, recovered by dividing. The fixed
magnitude is not a technicality — fibers at different levels are compared by a summary that
weights them differently, and nothing pins them together. -/
theorem imbalance_identifiedBy_oddSummary {summary : ℝ → ℝ} (hsummary : IsOddSummary summary)
    (level : ℝ) (hlevel : summary level ≠ 0) :
    IdentifiedBy (fun fiber : {fiber : Fiber // fiber.level = level} ↦
        fiber.val.contribution summary)
      (fun fiber ↦ fiber.val.imbalance) := by
  intro first second hobserve
  have hreduced : first.val.contribution summary = second.val.contribution summary := hobserve
  show first.val.imbalance = second.val.imbalance
  rw [Fiber.contribution_of_odd _ hsummary, Fiber.contribution_of_odd _ hsummary,
    first.property, second.property] at hreduced
  exact mul_right_cancel₀ hlevel hreduced

/-- **The asymmetry the surgery file names, as one statement.** The same distribution datum
is unreachable from the entire even class and recoverable from one odd summary. Read
against the estimators in use, the first conjunct is a non-identifiability result for
heritability, LD-score regression, stratified heritability and moment-based polygenicity
together, and the second is why that is a choice rather than a limit. -/
theorem imbalance_blind_to_evenClass_identified_by_oddSummary
    {summary : ℝ → ℝ} (hsummary : IsOddSummary summary) (level : ℝ)
    (hlevel : summary level ≠ 0) :
    ¬ IdentifiedBy evenSummaryReport Fiber.imbalance ∧
      IdentifiedBy (fun fiber : {fiber : Fiber // fiber.level = level} ↦
          fiber.val.contribution summary)
        (fun fiber ↦ fiber.val.imbalance) :=
  ⟨imbalance_not_identifiedBy_evenSummaryReport,
    imbalance_identifiedBy_oddSummary hsummary level hlevel⟩

end Descent.Blindness
