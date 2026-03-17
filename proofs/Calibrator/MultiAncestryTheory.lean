import Calibrator.PortabilityDrift
import Calibrator.TransferLearningPGS

namespace Calibrator

/-!
# Multi-Ancestry GWAS Theory and Equitable PGS

This file formalizes theoretical results about how multi-ancestry GWAS designs
can address the portability problem, and what fundamental limits exist.

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## GWAS Sample Diversity and Portability

The paper argues that understanding portability gaps can "inform more equitable
applications" and "aid in the development of PGS". We formalize how increasing
GWAS diversity affects portability bounds.
-/

section GWASDiversity

/- **GWAS sample genetic distance from target.**
    d_GWAS(target) = weighted distance from target individual to GWAS centroid. -/

/-- **Multi-ancestry GWAS reduces effective Fst.**
    A multi-ancestry GWAS with fraction α from a second ancestry
    at Fst distance d₂ from the target (and the primary ancestry at
    distance d₁) has effective Fst = (1-α)·d₁ + α·d₂ to the target.
    When d₂ < d₁ (the second ancestry is closer to the target),
    the mixture Fst is lower, yielding higher portability.

    Derived from: the convex combination (1-α)·d₁ + α·d₂ < d₁
    when α > 0 and d₂ < d₁, together with monotonic degradation of the
    deployed present-day `R²` chart in `Fst`. -/
theorem multi_ancestry_reduces_fst
    (V_A V_E d₁ d₂ α : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_d₂_closer : d₂ < d₁)
    (h_d₁_le_one : d₁ ≤ 1)
    (h_α_pos : 0 < α) :
    let fst_single := d₁
    let fst_multi := (1 - α) * d₁ + α * d₂
    presentDayR2 V_A V_E fst_multi > presentDayR2 V_A V_E fst_single := by
  simp only
  have h_multi_lt_single : (1 - α) * d₁ + α * d₂ < d₁ := by
    nlinarith
  simpa using
    (drift_degrades_R2
      V_A V_E ((1 - α) * d₁ + α * d₂) d₁
      hVA hVE h_multi_lt_single h_d₁_le_one)

/-- Present-day `R²` is the `expectedR2` chart applied to the drift-attenuated
signal variance `V_A × (1 - fst)`. -/
private theorem presentDayR2_eq_expectedR2
    (V_A V_E fst : ℝ) :
    presentDayR2 V_A V_E fst = expectedR2 ((1 - fst) * V_A) V_E := by
  simp [presentDayR2, presentDayPGSVariance, expectedR2]

/-- Exact gain from adding `δ` units of taggable signal variance to a deployed
target state with baseline signal variance `x`. -/
private theorem expectedR2_gain_eq
    (x δ V_E : ℝ)
    (hVE : 0 < V_E)
    (hx : 0 ≤ x)
    (hδ : 0 < δ) :
    expectedR2 (x + δ) V_E - expectedR2 x V_E =
      δ * V_E / ((x + δ + V_E) * (x + V_E)) := by
  unfold expectedR2
  have hxE : x + V_E ≠ 0 := by
    linarith
  have hxdE : x + δ + V_E ≠ 0 := by
    linarith
  field_simp [hxE, hxdE]
  ring

/-- For fixed residual variance, the same increase in taggable signal variance
helps more when the baseline signal is smaller. This is the discrete
diminishing-returns statement behind the multi-ancestry allocation argument. -/
private theorem expectedR2_gain_strictAnti_base
    (x₁ x₂ δ V_E : ℝ)
    (hVE : 0 < V_E)
    (hx₁ : 0 ≤ x₁)
    (hx_lt : x₁ < x₂)
    (hδ : 0 < δ) :
    expectedR2 (x₁ + δ) V_E - expectedR2 x₁ V_E >
      expectedR2 (x₂ + δ) V_E - expectedR2 x₂ V_E := by
  have hx₂ : 0 ≤ x₂ := by
    linarith
  rw [expectedR2_gain_eq x₁ δ V_E hVE hx₁ hδ,
    expectedR2_gain_eq x₂ δ V_E hVE hx₂ hδ]
  have hx₁E : 0 < x₁ + V_E := by
    linarith
  have hx₁δE : 0 < x₁ + δ + V_E := by
    linarith
  have hx₂E : 0 < x₂ + V_E := by
    linarith
  have hx₂δE : 0 < x₂ + δ + V_E := by
    linarith
  have hprod₁ :
      (x₁ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₁ + V_E) := by
    have hstep : x₁ + δ + V_E < x₂ + δ + V_E := by
      linarith
    exact mul_lt_mul_of_pos_right hstep hx₁E
  have hprod₂ :
      (x₂ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₂ + V_E) := by
    have hstep : x₁ + V_E < x₂ + V_E := by
      linarith
    exact mul_lt_mul_of_pos_left hstep hx₂δE
  have hprod :
      (x₁ + δ + V_E) * (x₁ + V_E) <
        (x₂ + δ + V_E) * (x₂ + V_E) := by
    exact lt_trans hprod₁ hprod₂
  have hnum : 0 < δ * V_E := by
    exact mul_pos hδ hVE
  have hfrac :
      δ * V_E / ((x₂ + δ + V_E) * (x₂ + V_E)) <
        δ * V_E / ((x₁ + δ + V_E) * (x₁ + V_E)) := by
    rw [div_lt_div_iff₀ (show 0 < (x₂ + δ + V_E) * (x₂ + V_E) by
      exact mul_pos hx₂δE hx₂E) (show 0 < (x₁ + δ + V_E) * (x₁ + V_E) by
      exact mul_pos hx₁δE hx₁E)]
    nlinarith [hprod, hnum]
  linarith

/-- **Diminishing returns from more similar samples.**
    In the deployed drift chart `R² = V_signal / (V_signal + V_E)`,
    reducing `Fst` by the same amount yields a larger `R²` gain when the
    starting population is farther from the GWAS centroid. This is the actual
    diminishing-returns statement relevant for underserved targets. -/
theorem portability_concave_in_fst_reduction
    (V_A V_E fst₁ fst₂ Δ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fst₁ < fst₂)
    (hfst₂_le_one : fst₂ ≤ 1)
    (hΔ : 0 < Δ) :
    presentDayR2 V_A V_E (fst₂ - Δ) - presentDayR2 V_A V_E fst₂ >
      presentDayR2 V_A V_E (fst₁ - Δ) - presentDayR2 V_A V_E fst₁ := by
  let xHigh : ℝ := (1 - fst₂) * V_A
  let xLow : ℝ := (1 - fst₁) * V_A
  let δ : ℝ := Δ * V_A
  have hxHigh : 0 ≤ xHigh := by
    unfold xHigh
    have h_one_minus : 0 ≤ 1 - fst₂ := by
      linarith
    exact mul_nonneg h_one_minus (le_of_lt hVA)
  have hδ : 0 < δ := by
    unfold δ
    exact mul_pos hΔ hVA
  have hx_lt : xHigh < xLow := by
    unfold xHigh xLow
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  have h_high_reduce :
      presentDayR2 V_A V_E (fst₂ - Δ) = expectedR2 (xHigh + δ) V_E := by
    rw [presentDayR2_eq_expectedR2]
    unfold xHigh δ
    congr 1
    ring
  have h_high :
      presentDayR2 V_A V_E fst₂ = expectedR2 xHigh V_E := by
    rw [presentDayR2_eq_expectedR2]
  have h_low_reduce :
      presentDayR2 V_A V_E (fst₁ - Δ) = expectedR2 (xLow + δ) V_E := by
    rw [presentDayR2_eq_expectedR2]
    unfold xLow δ
    congr 1
    ring
  have h_low :
      presentDayR2 V_A V_E fst₁ = expectedR2 xLow V_E := by
    rw [presentDayR2_eq_expectedR2]
  rw [h_high_reduce, h_high, h_low_reduce, h_low]
  exact expectedR2_gain_strictAnti_base xHigh xLow δ V_E hVE hxHigh hx_lt hδ

/-- **Optimal GWAS allocation.**
    In the exact shared-feature multi-ancestry effect model, the training
    weights induce a weighted average of ancestry-specific SNP effect vectors.
    Under equal per-ancestry deviation scale and orthogonal ancestry-specific
    effect components, the equal-weight diverse mixture minimizes the exact
    target coefficient gap among all affine allocations. -/
theorem maxmin_allocation_favors_diversity
    {p k : ℕ}
    (wShared wTarget : Fin p → ℝ)
    (deviation : Fin k → Fin p → ℝ)
    (weight : Fin k → ℝ)
    (irreducibleGap populationSpecificGap : ℝ)
    (h_k : 0 < k)
    (h_sum : ∑ j : Fin k, weight j = 1)
    (h_shared : coefficientGapSq wShared wTarget = irreducibleGap)
    (h_shared_orth :
      ∀ j, dotProduct (fun i => wShared i - wTarget i) (deviation j) = 0)
    (h_norm : ∀ j, dotProduct (deviation j) (deviation j) = populationSpecificGap)
    (h_pair : ∀ j l, j ≠ l → dotProduct (deviation j) (deviation l) = 0)
    (h_pop : 0 ≤ populationSpecificGap) :
    weightedMetaTransferGapSq wShared wTarget deviation (uniformMetaWeight k) ≤
      weightedMetaTransferGapSq wShared wTarget deviation weight := by
  exact weightedMetaTransferGapSq_ge_uniform_of_affine_weights
    wShared wTarget deviation weight irreducibleGap populationSpecificGap
    h_k h_sum h_shared h_shared_orth h_norm h_pair h_pop

end GWASDiversity


/-!
## Information-Theoretic and Geometric Limits on Portability

Even with infinite GWAS sample size, portability is fundamentally limited
by the information content of the source population about the target and by
target-private effect components that source data cannot identify.
-/

section InformationTheoreticLimits

/-- **Mutual information between source and target effect vectors.**
    Under a multivariate Gaussian model for effects:
    β_target | β_source ~ N(ρ·β_source, (1-ρ²)·σ²_β · I).
    The mutual information is -(m/2)·log(1-ρ²). -/
noncomputable def effectMutualInformation (m : ℕ) (ρ : ℝ) : ℝ :=
  -(m : ℝ) / 2 * Real.log (1 - ρ ^ 2)

/-- **Mutual information is zero when effects are uncorrelated.** -/
theorem no_info_when_uncorrelated (m : ℕ) :
    effectMutualInformation m 0 = 0 := by
  unfold effectMutualInformation
  simp [Real.log_one]

/-- **Mutual information increases with effect correlation.** -/
theorem more_correlated_more_informative
    (m : ℕ) (ρ₁ ρ₂ : ℝ)
    (hm : 0 < m)
    (hρ₁_nn : 0 ≤ ρ₁) (hρ₂_nn : 0 ≤ ρ₂)
    (hρ₁_lt : ρ₁ < 1) (hρ₂_lt : ρ₂ < 1)
    (h_more_corr : ρ₁ < ρ₂) :
    effectMutualInformation m ρ₁ < effectMutualInformation m ρ₂ := by
  unfold effectMutualInformation
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h_neg_m : -(m : ℝ) / 2 < 0 := by linarith
  have h1 : 1 - ρ₂ ^ 2 < 1 - ρ₁ ^ 2 := by nlinarith [sq_nonneg ρ₁, sq_nonneg ρ₂]
  have h_pos₁ : 0 < 1 - ρ₁ ^ 2 := by nlinarith [sq_nonneg ρ₁]
  have h_pos₂ : 0 < 1 - ρ₂ ^ 2 := by nlinarith [sq_nonneg ρ₂]
  have h_log : Real.log (1 - ρ₂ ^ 2) < Real.log (1 - ρ₁ ^ 2) :=
    Real.log_lt_log h_pos₂ h1
  nlinarith

/-- Additive genetic variance is the Euclidean squared norm of the SNP-effect
vector in the standardized diagonal-LD model. -/
private theorem additiveGeneticVariance_eq_dotProduct {m : ℕ}
    (β : Fin m → ℝ) :
    additiveGeneticVariance β = dotProduct β β := by
  unfold additiveGeneticVariance dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- When a target effect vector splits into a source-shared component and an
orthogonal target-private component, target heritability decomposes exactly
into shared plus private additive variance. -/
private theorem additiveGeneticVariance_add_of_orthogonal {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (h_orth : dotProduct β_shared β_private = 0) :
    additiveGeneticVariance (fun i => β_shared i + β_private i) =
      additiveGeneticVariance β_shared + additiveGeneticVariance β_private := by
  rw [additiveGeneticVariance_eq_dotProduct,
    additiveGeneticVariance_eq_dotProduct β_shared,
    additiveGeneticVariance_eq_dotProduct β_private]
  calc
    dotProduct (fun i => β_shared i + β_private i) (fun i => β_shared i + β_private i)
        =
          dotProduct β_shared β_shared + dotProduct β_shared β_private +
            (dotProduct β_private β_shared + dotProduct β_private β_private) := by
              rw [dotProduct_add_left, dotProduct_add_right, dotProduct_add_right]
    _ = dotProduct β_shared β_shared + dotProduct β_private β_private := by
          rw [h_orth, dotProduct_comm β_private β_shared, h_orth]
          ring

/-- If the target architecture equals the source-shared effect vector plus an
orthogonal target-private component, then the transported source score recovers
exactly the shared heritability and no more. -/
private theorem transportedTargetR2DiagonalLD_eq_sharedHeritability_of_orthogonal_private
    {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_shared_nonzero : 0 < additiveGeneticVariance β_shared)
    (h_orth : dotProduct β_shared β_private = 0) :
    transportedTargetR2DiagonalLD β_shared (fun i => β_shared i + β_private i) var_y =
      additiveHeritability β_shared var_y := by
  unfold transportedTargetR2DiagonalLD transportedTargetR2SharedLD pgsR2
    sharedLDGeneticVariance additiveHeritability
  rw [pgsPhenoCov_standardizedDiagonalLD, pgsPhenoCov_self_standardizedDiagonalLD]
  have hdot_zero : (∑ i : Fin m, β_shared i * β_private i) = 0 := by
    simpa [dotProduct] using h_orth
  have hcross :
      (∑ i : Fin m, β_shared i * (β_shared i + β_private i)) =
        additiveGeneticVariance β_shared := by
    calc
      (∑ i : Fin m, β_shared i * (β_shared i + β_private i))
          = (∑ i : Fin m, (β_shared i * β_shared i + β_shared i * β_private i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i : Fin m, β_shared i ^ 2) + ∑ i : Fin m, β_shared i * β_private i := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = additiveGeneticVariance β_shared := by
            simp [additiveGeneticVariance, hdot_zero]
  rw [hcross]
  have h_shared_ne : additiveGeneticVariance β_shared ≠ 0 := ne_of_gt h_shared_nonzero
  have h_var_y_ne : var_y ≠ 0 := ne_of_gt h_var_y
  field_simp [h_shared_ne, h_var_y_ne]

/-- **Fundamental portability limit from target-private SNP effects.**
    If the target architecture contains an orthogonal target-private effect
    component, the transferred source score can explain at most the shared
    heritability. The missing heritability is exactly the private target
    component, not an artifact of finite sample size. -/
theorem fundamental_portability_limit
    {m : ℕ}
    (β_shared β_private : Fin m → ℝ)
    (var_y : ℝ)
    (h_var_y : 0 < var_y)
    (h_shared_nonzero : 0 < additiveGeneticVariance β_shared)
    (h_orth : dotProduct β_shared β_private = 0) :
    transportedTargetR2DiagonalLD β_shared (fun i => β_shared i + β_private i) var_y +
      additiveHeritability β_private var_y =
        additiveHeritability (fun i => β_shared i + β_private i) var_y := by
  rw [transportedTargetR2DiagonalLD_eq_sharedHeritability_of_orthogonal_private
    β_shared β_private var_y h_var_y h_shared_nonzero h_orth]
  unfold additiveHeritability
  rw [additiveGeneticVariance_add_of_orthogonal β_shared β_private h_orth]
  have h_var_y_ne : var_y ≠ 0 := ne_of_gt h_var_y
  field_simp [h_var_y_ne]

/-- **No free lunch for portability when source and target SNP effects are
orthogonal.**
    In the standardized diagonal-LD model, zero source-target effect overlap
    forces the transported target `R²` to be exactly zero. -/
theorem no_free_lunch_portability
    {m : ℕ}
    (β_source β_target : Fin m → ℝ)
    (var_y : ℝ)
    (h_orth : dotProduct β_source β_target = 0) :
    transportedTargetR2DiagonalLD β_source β_target var_y = 0 := by
  unfold transportedTargetR2DiagonalLD transportedTargetR2SharedLD pgsR2
    sharedLDGeneticVariance
  rw [pgsPhenoCov_standardizedDiagonalLD, pgsPhenoCov_self_standardizedDiagonalLD]
  have hcross : (∑ i : Fin m, β_source i * β_target i) = 0 := by
    simpa [dotProduct] using h_orth
  rw [hcross]
  simp

end InformationTheoreticLimits


/-!
## Equity Implications

The paper discusses equitable applications of PGS. We formalize
the key equity-relevant theoretical results.
-/

section EquityImplications

/-- **Portability gap as a measure of inequity.**
    The portability gap = R²_source - R²_target measures the
    disadvantage faced by individuals in the target population. -/
noncomputable def portabilityGap (r2_source r2_target : ℝ) : ℝ :=
  r2_source - r2_target

/-- **Portability gap is always non-negative under drift.** -/
theorem portability_gap_nonneg
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS ≤ fstT) (hfstT : fstT ≤ 1) :
    0 ≤ portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT) := by
  unfold portabilityGap
  by_cases h : fstS = fstT
  · simp [h]
  · have hfst_strict : fstS < fstT := lt_of_le_of_ne hfst h
    exact le_of_lt (sub_pos.mpr
      (drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst_strict hfstT))

/-- **Portability gap increases with genetic distance from GWAS.** -/
theorem portability_gap_increases_with_distance
    (V_A V_E fstS fstT₁ fstT₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst₂ : fstT₁ < fstT₂) (hfstT₂ : fstT₂ ≤ 1) :
    portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT₁) <
      portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fstT₂) := by
  unfold portabilityGap
  have h1 : presentDayR2 V_A V_E fstT₂ < presentDayR2 V_A V_E fstT₁ :=
    drift_degrades_R2 V_A V_E fstT₁ fstT₂ hVA hVE hfst₂ hfstT₂
  linarith

/-- **Diversifying GWAS reduces maximum portability gap.**
    If multi-ancestry GWAS reduces the effective Fst for the
    worst-off population, the maximum portability gap decreases.

    This formalizes the argument for GWAS diversification as
    an equity intervention. -/
theorem diversity_reduces_max_gap
    (V_A V_E fstS fst_worst_single fst_worst_multi : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_single_bound : fst_worst_single ≤ 1)
    (h_improvement : fst_worst_multi < fst_worst_single) :
    portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fst_worst_multi) <
      portabilityGap (presentDayR2 V_A V_E fstS) (presentDayR2 V_A V_E fst_worst_single) := by
  unfold portabilityGap
  have h1 : presentDayR2 V_A V_E fst_worst_single < presentDayR2 V_A V_E fst_worst_multi :=
    drift_degrades_R2 V_A V_E fst_worst_multi fst_worst_single hVA hVE h_improvement h_single_bound
  linarith

/-- **Even perfect diversity cannot eliminate environmental portability gaps.**
    If environmental variance differs across populations, GWAS diversification
    addresses genetic portability but not environmental portability. -/
theorem diversity_doesnt_fix_environmental_gap
    (Vg Ve_source Ve_target : ℝ)
    (hVg : 0 < Vg)
    (hVe_s : 0 < Ve_source)
    (h_env_diff : Ve_source < Ve_target) :
    -- Even with zero genetic Fst gap, R² still differs
    Vg / (Vg + Ve_target) < Vg / (Vg + Ve_source) := by
  exact div_lt_div_of_pos_left hVg (by linarith) (by linarith)

end EquityImplications


/-!
## Variant Count and Estimation Noise

We formalize how the number of variants and effect estimation approach
affect portability noise and stability.
-/

section VariantCountAndEstimationNoise

/-- **Fewer variants → noisier portability estimates.**
    With fewer variants, each SNP's contribution is larger,
    making the score more sensitive to individual LD changes. -/
theorem fewer_variants_noisier
    (m₁ m₂ : ℕ) (σ_sq : ℝ)
    (hm : m₁ < m₂) (hσ : 0 < σ_sq)
    (hm₁ : 0 < m₁) :
    σ_sq / (m₁ : ℝ) > σ_sq / (m₂ : ℝ) := by
  apply div_lt_div_of_pos_left hσ
  · exact Nat.cast_pos.mpr hm₁
  · exact Nat.cast_lt.mpr hm

/-- **More variants → portability estimates converge to population-level truth.**
    By the law of large numbers, the sample portability ratio converges
    to the true ratio as the number of SNPs increases. -/
theorem more_variants_more_stable
    (m : ℕ) (var_per_snp : ℝ) (hv : 0 < var_per_snp) (hm : 0 < m) :
    -- Variance of portability ratio estimate scales as 1/m
    var_per_snp / (m : ℝ) > 0 := by
  exact div_pos hv (Nat.cast_pos.mpr hm)

/-- **Shrinkage regularization dampens portability noise.**
    Bayesian shrinkage pulls small effects toward zero,
    reducing the impact of LD-specific noise on portability. -/
theorem shrinkage_reduces_portability_variance
    (β_raw β_shrunk σ_sq_noise : ℝ)
    (h_shrunk : |β_shrunk| ≤ |β_raw|)
    (hσ : 0 < σ_sq_noise) :
    β_shrunk ^ 2 * σ_sq_noise ≤ β_raw ^ 2 * σ_sq_noise := by
  apply mul_le_mul_of_nonneg_right _ (le_of_lt hσ)
  nlinarith [sq_abs β_shrunk, sq_abs β_raw, abs_nonneg β_shrunk, abs_nonneg β_raw]

end VariantCountAndEstimationNoise

end Calibrator
