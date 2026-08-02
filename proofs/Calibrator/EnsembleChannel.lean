import Mathlib

namespace Calibrator

/-!
# The ensemble channel for order-erased target panels

An order-erased target panel is not the same experiment as a one-locus marginal.  Even
after genomic positions are discarded, fluctuations of its empirical measure depend on
linkage.  The variance of the sample mean exposes a Fejér-weighted autocovariance sum.

The first two theorems record that useful channel exactly for three loci.  The next witness
is the guardrail: the Fejér number is not sufficient for the unordered sample law.  Two
positive trigonometric symbols can have the same sample-mean channel while a symmetric
fourth-order Gaussian statistic differs.  Thus ensemble PGS deployment may learn some LD
from order-erased target panels, but it must not compress all target dependence to one
"long-run variance" without an additional model.

The final theorem is the exact finite-sample geometry behind compound deployment.  Moving
from the source score to the ensemble centroid improves squared spectral loss by precisely
the between-target predictable component; residual within-fibre variation is the price of
blindness.  Statistical identification of that centroid is a separate experiment, not an
algebraic consequence of the decomposition.
-/

open scoped BigOperators

/-- For a stationary three-locus covariance profile `(γ₀, γ₁, γ₂)`, this is
`3 * Var(mean)`: the zero-frequency Fejér evaluation. -/
noncomputable def fejerChannel3 (γ₀ γ₁ γ₂ : ℝ) : ℝ :=
  γ₀ + (4 / 3 : ℝ) * γ₁ + (2 / 3 : ℝ) * γ₂

/-- Direct covariance counting: three diagonal terms, four ordered lag-one terms, and two
ordered lag-two terms. -/
theorem three_mul_sampleMeanVariance3 (γ₀ γ₁ γ₂ : ℝ) :
    3 * ((3 * γ₀ + 4 * γ₁ + 2 * γ₂) / 9) = fejerChannel3 γ₀ γ₁ γ₂ := by
  unfold fejerChannel3
  ring

/-- A symmetric Gaussian fourth-order channel. By Isserlis' identity,
`E[∑_{i<j} Xᵢ²Xⱼ²] = 3γ₀² + 4γ₁² + 2γ₂²`; unlike the sample-mean channel it sees squared
lag covariances. -/
noncomputable def gaussianPairSquareChannel3 (γ₀ γ₁ γ₂ : ℝ) : ℝ :=
  3 * γ₀ ^ 2 + 4 * γ₁ ^ 2 + 2 * γ₂ ^ 2

/-- The flat covariance profile and a dependent profile have exactly the same Fejér
sample-mean channel. -/
theorem equal_fejer_channel_witness :
    fejerChannel3 1 0 0 = fejerChannel3 1 (1 / 10) (-1 / 5) := by
  norm_num [fejerChannel3]

/-- The same two profiles are separated by a symmetric fourth-order statistic. Therefore
the Fejér/sample-mean channel is not sufficient for the unordered Gaussian sample law. -/
theorem unequal_symmetric_fourth_channel_witness :
    gaussianPairSquareChannel3 1 0 0 ≠
      gaussianPairSquareChannel3 1 (1 / 10) (-1 / 5) := by
  norm_num [gaussianPairSquareChannel3]

/-- The dependent witness has a strictly positive trigonometric spectral polynomial on
`[-1,1]`, where `x = cos s`. This is the positivity check needed before interpreting its
first two Fourier coefficients as a stationary covariance profile. -/
theorem dependent_channel_symbol_positive {x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    (2 / 5 : ℝ) ≤ 7 / 5 + x / 5 - (4 / 5) * x ^ 2 := by
  have hsq : x ^ 2 ≤ 1 := by
    have hxplus : 0 ≤ 1 + x := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₁) hxplus]
  nlinarith

/-- Total squared deployment loss for a scalar spectral coordinate across a finite target
ensemble. The vector-valued/bandwise identity follows by summing this theorem by band. -/
noncomputable def ensembleSquaredLoss {ι : Type*} [Fintype ι]
    (target : ι → ℝ) (deployment : ℝ) : ℝ :=
  ∑ i, (target i - deployment) ^ 2

/-- Squared loss of a target-specific predictor across a finite ensemble. -/
noncomputable def ensemblePredictorSquaredLoss {ι : Type*} [Fintype ι]
    (target predictor : ι → ℝ) : ℝ :=
  ∑ i, (target i - predictor i) ^ 2

/-- **Conditional-predictor Pythagorean identity.** If the prediction residual is
orthogonal to the displacement from the source deployment, then source deployment loss is
residual loss plus the squared recoverable displacement. For a conditional expectation,
the orthogonality premise is the defining projection property.

The recoverable term is `∑ᵢ (predictor i - source)²`. It is not generally the variance of
the predictor: it also contains the squared displacement between the source and the target
ensemble mean. This distinction matters when a PGS is transported into cohorts whose
average genetic architecture has shifted from the training population. -/
theorem ensemblePredictorSquaredLoss_decomposition {ι : Type*} [Fintype ι]
    (target predictor : ι → ℝ) (source : ℝ)
    (horthogonal : ∑ i, (target i - predictor i) * (predictor i - source) = 0) :
    ensembleSquaredLoss target source =
      ensemblePredictorSquaredLoss target predictor + ∑ i, (predictor i - source) ^ 2 := by
  unfold ensembleSquaredLoss ensemblePredictorSquaredLoss
  calc
    ∑ i, (target i - source) ^ 2 =
        ∑ i, ((target i - predictor i) ^ 2 + (predictor i - source) ^ 2 +
          2 * ((target i - predictor i) * (predictor i - source))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (target i - predictor i) ^ 2) +
        (∑ i, (predictor i - source) ^ 2) +
          2 * ∑ i, (target i - predictor i) * (predictor i - source) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, (target i - predictor i) ^ 2) +
        ∑ i, (predictor i - source) ^ 2 := by
      rw [horthogonal]
      ring

/-- **Compound deployment Pythagorean identity.** If `center` is an ensemble centroid,
loss from deploying the source decomposes into irreducible within-ensemble loss plus the
recoverable displacement of the centroid from the source. -/
theorem ensembleSquaredLoss_decomposition {ι : Type*} [Fintype ι]
    (target : ι → ℝ) (source center : ℝ)
    (hcenter : ∑ i, (target i - center) = 0) :
    ensembleSquaredLoss target source =
      ensembleSquaredLoss target center + Fintype.card ι * (center - source) ^ 2 := by
  unfold ensembleSquaredLoss
  calc
    ∑ i, (target i - source) ^ 2 =
        ∑ i, ((target i - center) ^ 2 +
          2 * (center - source) * (target i - center) + (center - source) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (target i - center) ^ 2) +
        2 * (center - source) * (∑ i, (target i - center)) +
          ∑ _i : ι, (center - source) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, (target i - center) ^ 2) +
        Fintype.card ι * (center - source) ^ 2 := by
      rw [hcenter]
      simp

end Calibrator
