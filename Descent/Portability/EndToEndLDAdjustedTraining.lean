/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndDeploymentLaw

assert_below Descent.Decision Descent.Program

/-!
# LD-adjusted training with a reference panel

`EndToEndDeploymentLaw` trains a score by population ridge regression in one deme, with the LD
matrix and the marginal effects both read in that deme.  In practice the marginal effects come from
a source cohort and the LD matrix from a reference panel, which can be drawn from another deme.
This module gives the deployed accuracy of that score.

The score.  With `Σ_R` the tag covariance of a reference deme, `b_S` the tag–outcome covariances
of a source deme and a penalty `λ`, the LD-adjusted weights are `β = (Σ_R + λ I)⁻¹ b_S`
(`adjustedWeights`).  A positive penalty makes every positive semidefinite panel covariance
invertible (`isUnit_det_add_penalty`), and the weights are then the unique solution of the normal
equations (`ridgeWeights_eq_of_mulVec_eq`).  A panel enters only through its tag covariance, and a
matched panel recovers the corpus ridge weights of the source deme
(`adjustedWeights_eq_trainedWeights_of_tagCovariance_eq`, `adjustedWeights_self`).

The target accuracy.  In a target deme `T` a linear score has covariance `βᵀ c_T` with the outcome
and variance `βᵀ Σ_T β`, so its squared correlation is `(βᵀ c_T)² / (βᵀ Σ_T β · Var_T Y)`
(`r2_eq_dot`).  The squared correlation does not change when the weights are rescaled
(`r2_smul_weights`), and the determinant of `Σ_R + λ I` times the adjusted weights is the adjugate
numerator `adj(Σ_R + λ I) b_S` (`adjugateWeights`, `det_smul_adjustedWeights`).  So the target
squared correlation is the same ratio read at the adjugate numerator: a ratio of polynomials in the
entries of `Σ_R`, `λ`, `b_S`, `Σ_T`, `c_T` and `Var_T Y` (`r2_adjustedWeights_eq_adjugate`).
Along epochs, splits and pulses these entries are the expected budget-2 moments of the three
demes: the report of the adjusted score is the report of the moment matrices of `U · H₂(x₀)`
(`adjustedReport_historyEventKernel`), and histories with equal propagated budget-2 moments give
equal reports (`adjustedReport_eq_of_moments_eq`).

The panel channel.  In the source deme the adjusted score's covariance with the outcome is its
variance, plus `λ ‖β‖²`, plus the panel channel `βᵀ (Σ_R − Σ_S) β`
(`predictiveCovariance_adjustedWeights_source`).  Its calibration slope there is
`1 + (λ ‖β‖² + βᵀ (Σ_R − Σ_S) β) / Var S` (`calibrationSlope_adjustedWeights_source`).  A matched
panel closes the channel, which leaves the corpus ridge law `1 + λ ‖β‖² / Var S`.

A mismatched panel costs accuracy.  Take two tags that are the causal codings, with unit variances
and covariance `1/2` in the source deme, a unit effect at the first coding and a unit residual
variance.  Train with penalty one and deploy in the source deme.  The matched panel gives weights
`(7/15, 2/15)` and squared correlation `32/67`.  A panel deme with covariance `1/4`, half the
source LD, gives weights `(10/21, 4/21)` and the smaller squared correlation `6/13`
(`witnessMatchedWeights`, `witnessPanelWeights`, `witnessMatchedR2`, `witnessPanelR2`,
`r2_mismatchedPanel_lt_matched`).  Both panel covariances are positive semidefinite
(`witnessCovariance_nonneg`).

Scope.  Training is at the population level: the moments are expected second moments, and the query
is the ratio of expectations of NOTE2 §6.2, not the expectation of each population's metric.  The
sampling noise of an estimated panel LD matrix and of estimated marginal effects is not stated.  The
penalty matrix is `λ I`.  That a mismatched panel lowers accuracy is shown on one law only; no
general inequality between matched and mismatched panels is claimed.  The limit of a large penalty
is not stated.

## Empirical status

None.  The bodies here are matrix algebra on supplied moments, rational arithmetic on one
stipulated law, and rewriting along the history kernels, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndLDAdjustedTraining

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  EndToEndPortabilityLaw EndToEndCalibrationLaw EndToEndDeploymentLaw
open Descent.Foundations (dot)
open scoped Matrix NNReal

noncomputable section

/-! ## The adjusted weights -/

section Training

variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **LD-adjusted training with a reference panel**: the ridge weights `(Σ_R + λ I)⁻¹ b_S` from the
tag covariance `Σ_R` of a reference deme and the tag–outcome covariances `b_S` of a source deme. -/
def adjustedWeights (reference source : DemeMoments J L) (sourceArch : DemeArchitecture J L)
    (penalty : ℝ) : J → ℝ :=
  ridgeWeights reference.tagCovariance (source.tagOutcomeCovariance sourceArch) penalty

/-- **The adjugate numerator of the adjusted weights**, `adj(Σ_R + λ I) b_S`: every entry is a
polynomial in the entries of `Σ_R`, `λ` and `b_S`. -/
def adjugateWeights (reference source : DemeMoments J L) (sourceArch : DemeArchitecture J L)
    (penalty : ℝ) : J → ℝ :=
  (reference.tagCovariance + penalty • (1 : Matrix J J ℝ)).adjugate
    *ᵥ source.tagOutcomeCovariance sourceArch

/-- **Ridge weights are the unique solution of the normal equations** where the penalised
covariance is invertible.

Assumes: `IsUnit (covariance + penalty • 1).det`. -/
theorem ridgeWeights_eq_of_mulVec_eq (covariance : Matrix J J ℝ) (target : J → ℝ) (penalty : ℝ)
    (hunit : IsUnit (covariance + penalty • (1 : Matrix J J ℝ)).det) {weights : J → ℝ}
    (hnormal : (covariance + penalty • (1 : Matrix J J ℝ)) *ᵥ weights = target) :
    ridgeWeights covariance target penalty = weights := by
  rw [ridgeWeights, ← hnormal, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (h := hunit),
    Matrix.one_mulVec]

/-- **A positive penalty makes a positive semidefinite panel covariance invertible.**  A null vector
`v` of `Σ + λ I` has `vᵀ Σ v + λ vᵀ v = 0`, so `vᵀ v = 0` and `v = 0`.

Assumes: `∀ u, 0 ≤ dot u (covariance *ᵥ u)` and `0 < penalty`. -/
theorem isUnit_det_add_penalty (covariance : Matrix J J ℝ)
    (hcovariance : ∀ u : J → ℝ, 0 ≤ dot u (covariance *ᵥ u)) {penalty : ℝ}
    (hpenalty : 0 < penalty) : IsUnit (covariance + penalty • (1 : Matrix J J ℝ)).det := by
  refine isUnit_iff_ne_zero.mpr fun hdet ↦ ?_
  obtain ⟨v, hv, hnull⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsmul : dot v (penalty • v) = penalty * dot v v := by
    simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hzero : dot v ((covariance + penalty • (1 : Matrix J J ℝ)) *ᵥ v) = 0 := by
    rw [hnull]
    simp only [dot, Descent.Core.innerSum, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Foundations.dot_add_right,
    hsmul] at hzero
  have hdot : dot v v = ∑ i, v i * v i := rfl
  have hsquares : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
  rw [hdot] at hzero
  have hproduct : penalty * ∑ i, v i * v i = 0 := by
    linarith [hcovariance v, mul_nonneg hpenalty.le hsquares]
  have hnorm : ∑ i, v i * v i = 0 := (mul_eq_zero.mp hproduct).resolve_left hpenalty.ne'
  refine hv (funext fun i ↦ ?_)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_self_nonneg (v j)).mp hnorm i
    (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hentry

/-- **A panel enters only through its tag covariance**: a reference deme whose tag covariance is
the source's gives the corpus ridge weights of the source deme. -/
theorem adjustedWeights_eq_trainedWeights_of_tagCovariance_eq (reference source : DemeMoments J L)
    (sourceArch : DemeArchitecture J L) (penalty : ℝ)
    (hpanel : reference.tagCovariance = source.tagCovariance) :
    adjustedWeights reference source sourceArch penalty
      = trainedWeights source sourceArch penalty := by
  rw [adjustedWeights, hpanel, trainedWeights]

/-- **A matched panel is population ridge training**: with the source deme as its own reference
panel, LD-adjusted training gives the corpus ridge weights `trainedWeights`. -/
theorem adjustedWeights_self (source : DemeMoments J L) (sourceArch : DemeArchitecture J L)
    (penalty : ℝ) :
    adjustedWeights source source sourceArch penalty = trainedWeights source sourceArch penalty :=
  adjustedWeights_eq_trainedWeights_of_tagCovariance_eq source source sourceArch penalty rfl

/-! ## The target squared correlation -/

/-- **The squared correlation of a linear score** in a deme is `(wᵀ c)² / (wᵀ Σ w · Var Y)`, with
`c` the tag–outcome covariances and `Σ` the tag covariance of that deme. -/
theorem r2_eq_dot (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) :
    m.r2 a w
      = dot w (m.tagOutcomeCovariance a) ^ 2
        / (dot w (m.tagCovariance *ᵥ w) * m.outcomeVariance a) := by
  show m.predictiveCovariance a w ^ 2 / (m.scoreVariance w * m.outcomeVariance a) = _
  rw [DemeMoments.predictiveCovariance_eq_dot, DemeMoments.scoreVariance]

/-- **The squared correlation is scale free**: rescaling the weights by a nonzero factor leaves
the deployed `R²` unchanged. -/
theorem r2_smul_weights (m : DemeMoments J L) (a : DemeArchitecture J L) (w : J → ℝ) {c : ℝ}
    (hc : c ≠ 0) : m.r2 a (c • w) = m.r2 a w := by
  have hcovariance : m.predictiveCovariance a (c • w) = c * m.predictiveCovariance a w := by
    rw [DemeMoments.predictiveCovariance_eq_dot, DemeMoments.predictiveCovariance_eq_dot]
    simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hvariance : m.scoreVariance (c • w) = c ^ 2 * m.scoreVariance w := by
    rw [DemeMoments.scoreVariance, DemeMoments.scoreVariance, Matrix.mulVec_smul]
    simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  show m.predictiveCovariance a (c • w) ^ 2 / (m.scoreVariance (c • w) * m.outcomeVariance a)
    = m.predictiveCovariance a w ^ 2 / (m.scoreVariance w * m.outcomeVariance a)
  rw [hcovariance, hvariance, mul_pow, mul_assoc (c ^ 2),
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- **The determinant times the adjusted weights is the adjugate numerator**: `adj(A) A = det A · I`
applied to the normal equations `A β = b_S`, with `A = Σ_R + λ I`.

Assumes: `IsUnit (reference.tagCovariance + penalty • 1).det`. -/
theorem det_smul_adjustedWeights (reference source : DemeMoments J L)
    (sourceArch : DemeArchitecture J L) (penalty : ℝ)
    (hunit : IsUnit (reference.tagCovariance + penalty • (1 : Matrix J J ℝ)).det) :
    (reference.tagCovariance + penalty • (1 : Matrix J J ℝ)).det
        • adjustedWeights reference source sourceArch penalty
      = adjugateWeights reference source sourceArch penalty := by
  have hnormal : (reference.tagCovariance + penalty • (1 : Matrix J J ℝ))
        *ᵥ adjustedWeights reference source sourceArch penalty
      = source.tagOutcomeCovariance sourceArch :=
    ridgeWeights_normal reference.tagCovariance (source.tagOutcomeCovariance sourceArch) penalty
      hunit
  rw [adjugateWeights, ← hnormal, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- **The target squared correlation of LD-adjusted training is rational in the moments.**  With a
positive semidefinite panel covariance and a positive penalty, the squared correlation of the
adjusted score in a target deme is `(aᵀ c_T)² / (aᵀ Σ_T a · Var_T Y)` at the adjugate numerator
`a = adj(Σ_R + λ I) b_S`: a ratio of polynomials in the entries of the moments of the reference,
source and target demes.

Assumes: `∀ u, 0 ≤ dot u (reference.tagCovariance *ᵥ u)` and `0 < penalty`. -/
theorem r2_adjustedWeights_eq_adjugate (reference source target : DemeMoments J L)
    (sourceArch targetArch : DemeArchitecture J L) {penalty : ℝ}
    (hpanel : ∀ u : J → ℝ, 0 ≤ dot u (reference.tagCovariance *ᵥ u)) (hpenalty : 0 < penalty) :
    target.r2 targetArch (adjustedWeights reference source sourceArch penalty)
      = dot (adjugateWeights reference source sourceArch penalty)
            (target.tagOutcomeCovariance targetArch) ^ 2
        / (dot (adjugateWeights reference source sourceArch penalty)
            (target.tagCovariance *ᵥ adjugateWeights reference source sourceArch penalty)
          * target.outcomeVariance targetArch) := by
  have hunit := isUnit_det_add_penalty reference.tagCovariance hpanel hpenalty
  rw [← r2_smul_weights target targetArch (adjustedWeights reference source sourceArch penalty)
      hunit.ne_zero, det_smul_adjustedWeights reference source sourceArch penalty hunit, r2_eq_dot]

/-! ## The panel channel in the source deme -/

/-- **The panel channel.**  In the source deme an LD-adjusted score's covariance with the outcome is
its variance, plus the penalty times the squared weight norm, plus the panel channel
`βᵀ (Σ_R − Σ_S) β`.  At a matched panel the channel vanishes and this is
`predictiveCovariance_trainedWeights`.

Assumes: `IsUnit (reference.tagCovariance + penalty • 1).det`. -/
theorem predictiveCovariance_adjustedWeights_source (reference source : DemeMoments J L)
    (sourceArch : DemeArchitecture J L) (penalty : ℝ)
    (hunit : IsUnit (reference.tagCovariance + penalty • (1 : Matrix J J ℝ)).det) :
    source.predictiveCovariance sourceArch (adjustedWeights reference source sourceArch penalty)
      = source.scoreVariance (adjustedWeights reference source sourceArch penalty)
        + penalty * dot (adjustedWeights reference source sourceArch penalty)
          (adjustedWeights reference source sourceArch penalty)
        + dot (adjustedWeights reference source sourceArch penalty)
          ((reference.tagCovariance - source.tagCovariance)
            *ᵥ adjustedWeights reference source sourceArch penalty) := by
  have hdot : dot (adjustedWeights reference source sourceArch penalty)
        (source.tagOutcomeCovariance sourceArch)
      = dot (adjustedWeights reference source sourceArch penalty)
          (reference.tagCovariance *ᵥ adjustedWeights reference source sourceArch penalty)
        + penalty * dot (adjustedWeights reference source sourceArch penalty)
          (adjustedWeights reference source sourceArch penalty) :=
    dot_ridgeWeights_target reference.tagCovariance (source.tagOutcomeCovariance sourceArch)
      penalty hunit
  rw [DemeMoments.predictiveCovariance_eq_dot, DemeMoments.scoreVariance, Matrix.sub_mulVec,
    Foundations.dot_sub_right', hdot]
  ring

/-- **The calibration slope of LD-adjusted training in the source deme** is
`1 + (λ ‖β‖² + βᵀ (Σ_R − Σ_S) β) / Var S`.

Assumes: `IsUnit (reference.tagCovariance + penalty • 1).det`. -/
theorem calibrationSlope_adjustedWeights_source (reference source : DemeMoments J L)
    (sourceArch : DemeArchitecture J L) (penalty : ℝ)
    (hunit : IsUnit (reference.tagCovariance + penalty • (1 : Matrix J J ℝ)).det)
    (hvariance : source.scoreVariance (adjustedWeights reference source sourceArch penalty) ≠ 0) :
    source.calibrationSlope sourceArch (adjustedWeights reference source sourceArch penalty)
      = 1 + (penalty * dot (adjustedWeights reference source sourceArch penalty)
            (adjustedWeights reference source sourceArch penalty)
          + dot (adjustedWeights reference source sourceArch penalty)
            ((reference.tagCovariance - source.tagCovariance)
              *ᵥ adjustedWeights reference source sourceArch penalty))
        / source.scoreVariance (adjustedWeights reference source sourceArch penalty) := by
  show source.predictiveCovariance sourceArch (adjustedWeights reference source sourceArch penalty)
      / source.scoreVariance (adjustedWeights reference source sourceArch penalty) = _
  rw [predictiveCovariance_adjustedWeights_source reference source sourceArch penalty hunit,
    add_assoc, add_div (source.scoreVariance _), div_self hvariance]

end Training

/-! ## Along a history -/

section Moments

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **Panel, source and target along a history.**  Weights trained on the marginal covariances of a
source deme, adjusted with the tag covariance of a reference deme and deployed in a target deme,
have a deployment report computed from the expected deployment moments equal to the report of the
moment matrices of `U · H₂(x₀)`. -/
theorem adjustedReport_historyEventKernel (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (x0 : FrequencyState Deme Locus Allele) (reference source target : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ)
    (sourceArch targetArch : DemeArchitecture J L) (penalty : ℝ) :
    (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 target X C).report targetArch
        (adjustedWeights
          (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 reference X C)
          (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ events) x0 source X C)
          sourceArch penalty)
      = (momentDemeMoments ℓ₀ 2 target X C
            (historyEventPropagator (fun _ ↦ 2) events
              *ᵥ budgetMomentFeature (fun _ ↦ 2) x0)).report
          targetArch
          (adjustedWeights
            (momentDemeMoments ℓ₀ 2 reference X C
              (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
            (momentDemeMoments ℓ₀ 2 source X C
              (historyEventPropagator (fun _ ↦ 2) events *ᵥ budgetMomentFeature (fun _ ↦ 2) x0))
            sourceArch penalty) := by
  rw [expectedDemeMoments_historyEventKernel ℓ₀ hap₀ events le_rfl x0 target,
    expectedDemeMoments_historyEventKernel ℓ₀ hap₀ events le_rfl x0 reference,
    expectedDemeMoments_historyEventKernel ℓ₀ hap₀ events le_rfl x0 source]

/-- **Panel mismatch sees the history only through finitely many moments.**  Two histories whose
propagated budget-2 moments agree give the same report for every reference, source and target
deme, codings, architectures and penalty. -/
theorem adjustedReport_eq_of_moments_eq (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 2) first *ᵥ budgetMomentFeature (fun _ ↦ 2) x₁
      = historyEventPropagator (fun _ ↦ 2) second *ᵥ budgetMomentFeature (fun _ ↦ 2) x₂)
    (reference source target : Deme)
    (X : FullHaplotype Locus Allele → J → ℝ) (C : FullHaplotype Locus Allele → L → ℝ)
    (sourceArch targetArch : DemeArchitecture J L) (penalty : ℝ) :
    (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ target X C).report targetArch
        (adjustedWeights
          (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ reference X C)
          (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ first) x₁ source X C)
          sourceArch penalty)
      = (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ target X C).report targetArch
          (adjustedWeights
            (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ reference X C)
            (expectedDemeMoments (historyEventKernel ℓ₀ hap₀ second) x₂ source X C)
            sourceArch penalty) := by
  rw [expectedDemeMoments_eq_of_moments_eq ℓ₀ hap₀ le_rfl target hmoments X C,
    expectedDemeMoments_eq_of_moments_eq ℓ₀ hap₀ le_rfl reference hmoments X C,
    expectedDemeMoments_eq_of_moments_eq ℓ₀ hap₀ le_rfl source hmoments X C]

end Moments

/-! ## A mismatched panel lowers target accuracy -/

section Witness

/-- **The witness source deme**: two tags that are the causal codings, with unit variances and
covariance `1/2`. -/
def witnessSource : DemeMoments (Fin 2) (Fin 2) where
  tagCovariance := !![1, 1 / 2; 1 / 2, 1]
  tagCausalCovariance := !![1, 1 / 2; 1 / 2, 1]
  causalCovariance := !![1, 1 / 2; 1 / 2, 1]
  tagMean := 0
  causalMean := 0

/-- **The witness panel deme**: the same codings with covariance `1/4`, half the source LD. -/
def witnessPanel : DemeMoments (Fin 2) (Fin 2) where
  tagCovariance := !![1, 1 / 4; 1 / 4, 1]
  tagCausalCovariance := !![1, 1 / 4; 1 / 4, 1]
  causalCovariance := !![1, 1 / 4; 1 / 4, 1]
  tagMean := 0
  causalMean := 0

/-- **The witness architecture**: a unit effect at the first causal coding, a unit residual
variance and no residual covariances. -/
def witnessArchitecture : DemeArchitecture (Fin 2) (Fin 2) where
  effects := ![1, 0]
  residualVariance := 1
  residualMean := 0
  residualTagCovariance := 0
  residualCausalCovariance := 0

/-- **The witness covariances are positive semidefinite**: `!![1, ρ; ρ, 1]` reads `u` as
`(1 − ρ)(u₀² + u₁²) + ρ (u₀ + u₁)²`, which is nonnegative for `0 ≤ ρ ≤ 1`.

Assumes: `0 ≤ ρ` and `ρ ≤ 1`. -/
theorem witnessCovariance_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (u : Fin 2 → ℝ) :
    0 ≤ dot u (!![1, ρ; ρ, 1] *ᵥ u) := by
  have hform : dot u (!![1, ρ; ρ, 1] *ᵥ u)
      = (1 - ρ) * (u 0 ^ 2 + u 1 ^ 2) + ρ * (u 0 + u 1) ^ 2 := by
    simp [dot, Descent.Core.innerSum, Fin.sum_univ_two, Matrix.mulVec, dotProduct] <;> ring
  rw [hform]
  exact add_nonneg (mul_nonneg (by linarith) (by positivity)) (mul_nonneg h0 (sq_nonneg _))

/-- **The matched panel's weights**: the corpus ridge weights of the witness deme at penalty one
are `(7/15, 2/15)`. -/
theorem witnessMatchedWeights :
    adjustedWeights witnessSource witnessSource witnessArchitecture 1 = ![7 / 15, 2 / 15] := by
  have hunit :
      IsUnit (witnessSource.tagCovariance + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det :=
    isUnit_det_add_penalty _ (witnessCovariance_nonneg (ρ := 1 / 2) (by norm_num) (by norm_num))
      one_pos
  refine ridgeWeights_eq_of_mulVec_eq _ _ _ hunit ?_
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> norm_num [witnessSource, witnessArchitecture, DemeMoments.tagOutcomeCovariance,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The mismatched panel's weights**: adjusting the witness deme's marginal covariances with the
panel deme's LD at penalty one gives `(10/21, 4/21)`. -/
theorem witnessPanelWeights :
    adjustedWeights witnessPanel witnessSource witnessArchitecture 1 = ![10 / 21, 4 / 21] := by
  have hunit : IsUnit (witnessPanel.tagCovariance + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det :=
    isUnit_det_add_penalty _ (witnessCovariance_nonneg (ρ := 1 / 4) (by norm_num) (by norm_num))
      one_pos
  refine ridgeWeights_eq_of_mulVec_eq _ _ _ hunit ?_
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> norm_num [witnessPanel, witnessSource, witnessArchitecture,
    DemeMoments.tagOutcomeCovariance, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The matched panel's target squared correlation** in the witness deme is `32/67`. -/
theorem witnessMatchedR2 :
    witnessSource.r2 witnessArchitecture
      (adjustedWeights witnessSource witnessSource witnessArchitecture 1) = 32 / 67 := by
  rw [witnessMatchedWeights, r2_eq_dot]
  norm_num [witnessSource, witnessArchitecture, DemeMoments.tagOutcomeCovariance,
    DemeMoments.outcomeVariance, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- **The mismatched panel's target squared correlation** in the witness deme is `6/13`. -/
theorem witnessPanelR2 :
    witnessSource.r2 witnessArchitecture
      (adjustedWeights witnessPanel witnessSource witnessArchitecture 1) = 6 / 13 := by
  rw [witnessPanelWeights, r2_eq_dot]
  norm_num [witnessSource, witnessArchitecture, DemeMoments.tagOutcomeCovariance,
    DemeMoments.outcomeVariance, dot, Descent.Core.innerSum, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- **A panel from another deme lowers target accuracy.**  Training on the witness deme and
deploying there, adjusting with the panel deme's LD gives a strictly smaller squared correlation
than the matched panel, `6/13 < 32/67`. -/
theorem r2_mismatchedPanel_lt_matched :
    witnessSource.r2 witnessArchitecture
        (adjustedWeights witnessPanel witnessSource witnessArchitecture 1)
      < witnessSource.r2 witnessArchitecture
        (adjustedWeights witnessSource witnessSource witnessArchitecture 1) := by
  rw [witnessPanelR2, witnessMatchedR2]
  norm_num

end Witness

end

end Descent.Portability.EndToEndLDAdjustedTraining
