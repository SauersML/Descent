/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PCCorrectability.Diagnostic
import Descent.Portability.PCCorrectability.Overlap
import Descent.Spectral.ProjectionShiftBounds

namespace Descent

noncomputable section

/-!
# End-to-end correctability theorems

This module connects the spectral, second-moment, and application-risk layers.  Its statements
expose exactly where the rank-one
overlap model is used and where a distribution-free discrepancy bound can be
substituted instead.
-/

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Residual susceptibility obtained by applying the modeled sample-PC
residual fraction to an ancestry axis and then coupling it to marker-axis
variance. -/
noncomputable def modeledPCResidualSusceptibility
    (markerAxisVariance ancestryVariance n markers spike : ℝ) : ℝ :=
  ancestryGradientSusceptibility markerAxisVariance
    (ancestryVariance * samplePCResidualAxisFraction n markers spike)

/-- Below the spectral edge the modeled PC removes none of the target axis,
so residual susceptibility equals uncorrected susceptibility exactly. -/
theorem modeledPCResidualSusceptibility_eq_uncorrected_of_subthreshold
    (markerAxisVariance ancestryVariance n markers spike : ℝ)
    (hsubthreshold : spike ≤ bbpProxyThreshold n markers) :
    modeledPCResidualSusceptibility markerAxisVariance ancestryVariance
        n markers spike =
      ancestryGradientSusceptibility markerAxisVariance ancestryVariance := by
  unfold modeledPCResidualSusceptibility
  rw [subthreshold_sample_pc_leaves_full_axis n markers spike hsubthreshold]
  ring_nf

/-- Above the spectral edge a finite positive spike strictly reduces, but does
not eliminate, susceptibility.  This is the precise risk-level consequence of
the Johnstone--Paul overlap curve. -/
theorem modeledPCResidualSusceptibility_pos_and_lt_uncorrected
    (markerAxisVariance ancestryVariance n markers spike : ℝ)
    (hmarkerAxis : 0 < markerAxisVariance)
    (hancestry : 0 < ancestryVariance)
    (hn : 0 < n) (hmarkers : 0 < markers)
    (hsuperthreshold : bbpProxyThreshold n markers < spike) :
    0 < modeledPCResidualSusceptibility markerAxisVariance ancestryVariance
          n markers spike ∧
      modeledPCResidualSusceptibility markerAxisVariance ancestryVariance
          n markers spike <
        ancestryGradientSusceptibility markerAxisVariance ancestryVariance := by
  have hresidual := samplePCResidualAxisFraction_pos_and_lt_one
    n markers spike hn hmarkers hsuperthreshold
  unfold modeledPCResidualSusceptibility ancestryGradientSusceptibility
  constructor
  · exact mul_pos hmarkerAxis (mul_pos hancestry hresidual.1)
  · have haxis : ancestryVariance * samplePCResidualAxisFraction n markers spike <
        ancestryVariance := by
      nlinarith [mul_lt_mul_of_pos_left hresidual.2 hancestry]
    exact mul_lt_mul_of_pos_left haxis hmarkerAxis

/-- Ascertainment amplification is nonnegative whenever its directional and
count-inflation inputs are nonnegative. -/
theorem ascertainmentAmplification_nonneg
    (directionalAmplification countInflation : ℝ)
    (hdirectional : 0 ≤ directionalAmplification)
    (hcount : 0 ≤ countInflation) :
    0 ≤ ascertainmentAmplification directionalAmplification countInflation := by
  unfold ascertainmentAmplification
  exact div_nonneg (by linarith) (Real.sqrt_nonneg _)

/-- For fixed design and nonnegative confounding, the standardized bias model
is monotone in residual susceptibility. -/
theorem standardizedResidualPGSBias_mono_susceptibility
    (expectedSNPCount Hsmall Hlarge effectSD directionalAmplification
      countInflation confounding : ℝ)
    (hH : Hsmall ≤ Hlarge)
    (heffectSD : 0 < effectSD)
    (hdirectional : 0 ≤ directionalAmplification)
    (hcount : 0 ≤ countInflation)
    (hconfounding : 0 ≤ confounding) :
    standardizedResidualPGSBias expectedSNPCount Hsmall effectSD
        directionalAmplification countInflation confounding ≤
      standardizedResidualPGSBias expectedSNPCount Hlarge effectSD
        directionalAmplification countInflation confounding := by
  have hsqrt : Real.sqrt Hsmall ≤ Real.sqrt Hlarge := Real.sqrt_le_sqrt hH
  have hamp : 0 ≤ ascertainmentAmplification directionalAmplification countInflation :=
    ascertainmentAmplification_nonneg directionalAmplification countInflation
      hdirectional hcount
  have hscale :
      0 ≤ Real.sqrt expectedSNPCount / effectSD *
        ascertainmentAmplification directionalAmplification countInflation * confounding :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt heffectSD)) hamp)
      hconfounding
  have hscaled := mul_le_mul_of_nonneg_right hsqrt hscale
  unfold standardizedResidualPGSBias pgsStratificationRiskCoefficient
  convert hscaled using 1 <;> ring

/-- Distribution-free end-to-end protection theorem.  A chi-square
distribution-shift budget times a residual-curvature budget bounds coefficient
movement; after scaling by marker-axis variance, monotonicity propagates that
bound to standardized downstream bias. -/
theorem projection_artifact_implies_standardized_bias_bound
    (P : ExpFunctional Ω) (densityRatio : Ω → ℝ)
    (X : Ω → ι → ℝ) (residual : Ω → ℝ)
    (B : Matrix ι ι ℝ) (artifact : ι → ℝ) (curvatureBound : ℝ)
    (markerAxisVariance expectedSNPCount effectSD directionalAmplification
      countInflation confounding : ℝ)
    (hmoment : B.mulVec artifact =
      weightedResidualMoment P densityRatio X residual)

    (henergy : 0 ≤ coefficientEnergy B artifact)
    (hchiSquare : 0 ≤ chiSquareBudget P densityRatio)
    (hcurvatureBound : 0 ≤ curvatureBound)
    (hcurvature : directionalResidualCurvature P X residual artifact ≤
      curvatureBound * coefficientEnergy B artifact)
    (hmarkerAxis : 0 ≤ markerAxisVariance)
    (heffectSD : 0 < effectSD)
    (hdirectional : 0 ≤ directionalAmplification)
    (hcount : 0 ≤ countInflation)
    (hconfounding : 0 ≤ confounding) :
    standardizedResidualPGSBias expectedSNPCount
        (markerAxisVariance * coefficientEnergy B artifact) effectSD
        directionalAmplification countInflation confounding ≤
      standardizedResidualPGSBias expectedSNPCount
        (markerAxisVariance *
          (chiSquareBudget P densityRatio * curvatureBound)) effectSD
        directionalAmplification countInflation confounding := by
  have hartifact := projection_artifact_energy_le_chiSquare_mul_curvature
    P densityRatio X residual B artifact curvatureBound hmoment
    henergy hchiSquare hcurvatureBound hcurvature
  apply standardizedResidualPGSBias_mono_susceptibility
  · exact mul_le_mul_of_nonneg_left hartifact hmarkerAxis
  · exact heffectSD
  · exact hdirectional
  · exact hcount
  · exact hconfounding

end

end Descent
