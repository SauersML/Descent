/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ControlledCoarseGraining

assert_below Descent.Decision Descent.Program

/-!
Exact continuous-time elimination of hidden linear dynamics. Hidden initial
data produce a distinct forcing term, retained alongside the history integral.
No timescale approximation or autonomous closure is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousMemoryLaw

open ControlledCoarseGraining MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def hiddenIntegrand (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F)
    (retained : ℝ → E) (horizon time : ℝ) : F :=
  evolution hidden (horizon - time) (coupling (retained time))

omit [CompleteSpace E] in
theorem hiddenIntegrand_continuous (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F)
    (retained : ℝ → E) (hretained : Continuous retained) (horizon : ℝ) :
    Continuous (hiddenIntegrand coupling hidden retained horizon) := by
  exact ((evolution_continuous hidden).comp (continuous_const.sub continuous_id)).clm_apply
    (coupling.continuous.comp hretained)

omit [CompleteSpace E] in
private theorem propagated_hidden_derivative (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F)
    (retained : ℝ → E) (discarded : ℝ → F)
    (hdiscarded : ∀ time, HasDerivAt discarded
      (coupling (retained time) + hidden (discarded time)) time) (horizon time : ℝ) :
    HasDerivAt (fun moment ↦ evolution hidden (horizon - moment) (discarded moment))
      (hiddenIntegrand coupling hidden retained horizon time) time := by
  have he := (hasDerivAt_exp_smul_const hidden (horizon - time)).scomp time
    ((hasDerivAt_id time).const_sub horizon)
  have hd := he.clm_apply (hdiscarded time)
  convert hd using 1
  simp [hiddenIntegrand, evolution, ContinuousLinearMap.mul_def]

omit [CompleteSpace E] in
/-- Variation of constants, derived directly from the hidden differential equation. -/
theorem hidden_expansion (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F)
    (retained : ℝ → E) (discarded : ℝ → F) (hretained : Continuous retained)
    (hdiscarded : ∀ time, HasDerivAt discarded
      (coupling (retained time) + hidden (discarded time)) time) (horizon : ℝ) :
    discarded horizon = evolution hidden horizon (discarded 0) +
      ∫ time in 0..horizon, hiddenIntegrand coupling hidden retained horizon time := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ ↦
      propagated_hidden_derivative coupling hidden retained discarded hdiscarded horizon time)
    ((hiddenIntegrand_continuous coupling hidden retained hretained horizon).intervalIntegrable
      0 horizon)
  simp only [evolution, sub_self, zero_smul, NormedSpace.exp_zero,
    ContinuousLinearMap.one_apply, sub_zero] at hFTC
  rw [hFTC]
  simp only [evolution]
  abel

/-- Exact retained-state memory: both hidden initial forcing and the complete
history kernel are derived from the two block differential equations. -/
theorem retained_memory (direct : E →L[ℝ] E) (feedback : F →L[ℝ] E)
    (coupling : E →L[ℝ] F) (hidden : F →L[ℝ] F)
    (retained : ℝ → E) (discarded : ℝ → F)
    (hretained : ∀ time, HasDerivAt retained
      (direct (retained time) + feedback (discarded time)) time)
    (hdiscarded : ∀ time, HasDerivAt discarded
      (coupling (retained time) + hidden (discarded time)) time) (horizon : ℝ) :
    HasDerivAt retained
      (direct (retained horizon) + feedback (evolution hidden horizon (discarded 0)) +
        ∫ time in 0..horizon,
          feedback (hiddenIntegrand coupling hidden retained horizon time)) horizon := by
  have hcontinuous : Continuous retained :=
    continuous_iff_continuousAt.mpr fun time ↦ (hretained time).continuousAt
  have heq := hidden_expansion coupling hidden retained discarded hcontinuous hdiscarded horizon
  have hd := hretained horizon
  rw [heq, map_add] at hd
  rw [feedback.intervalIntegral_comp_comm
    ((hiddenIntegrand_continuous coupling hidden retained hcontinuous horizon).intervalIntegrable
      0 horizon)]
  simpa only [add_assoc] using hd

end Descent.Portability.ContinuousMemoryLaw
