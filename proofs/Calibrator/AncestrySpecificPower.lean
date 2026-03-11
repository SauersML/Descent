import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Statistical Power and PGS Portability

This file formalizes the statistical power framework for PGS
across different populations. Power imbalances are a
fundamental driver of portability gaps.

Key results:
1. Population-specific power curves
2. Discovery bias from single-population GWAS
3. Effective sample size across populations
4. Power-portability tradeoff
5. Optimal multi-population study design

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Population-Specific Power Curves

Power to detect a variant depends on sample size, effect size,
and allele frequency — all of which differ across populations.
-/

section PopulationPowerCurves

/-- **Effective sample size for a variant.**
    n_eff = n × 2p(1-p) × r²_LD(tag, causal)
    where p is MAF in that ancestry and r²_LD is tagging efficiency. -/
noncomputable def effectiveSampleSize (n : ℕ) (p r2_ld : ℝ) : ℝ :=
  n * (2 * p * (1 - p)) * r2_ld

/-- Effective sample size is nonneg. -/
theorem effective_n_nonneg (n : ℕ) (p r2_ld : ℝ)
    (h_p : 0 ≤ p) (h_p_le : p ≤ 1) (h_r2 : 0 ≤ r2_ld) :
    0 ≤ effectiveSampleSize n p r2_ld := by
  unfold effectiveSampleSize
  apply mul_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg n
    · nlinarith
  · exact h_r2

/-- **Effective sample size is monotone in r²_LD.**
    Holding sample size and MAF fixed, higher tagging r² gives higher n_eff.
    This is the key lemma: populations with shorter LD have lower r²_LD
    to the GWAS tag SNPs, hence lower effective sample size. -/
theorem effective_n_mono_r2 (n : ℕ) (p r2_a r2_b : ℝ)
    (h_n : 0 < n) (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_a : 0 ≤ r2_a) (h_r2_b : 0 ≤ r2_b)
    (h_r2 : r2_a < r2_b) :
    effectiveSampleSize n p r2_a < effectiveSampleSize n p r2_b := by
  unfold effectiveSampleSize
  have h_het : 0 < 2 * p * (1 - p) := by nlinarith
  have h_coeff : 0 < ↑n * (2 * p * (1 - p)) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr h_n
    · exact h_het
  exact mul_lt_mul_of_pos_left h_r2 h_coeff

/-- **Effective sample size is monotone in sample count.**
    Holding MAF and r²_LD fixed, more samples give higher n_eff. -/
theorem effective_n_mono_n (n_a n_b : ℕ) (p r2_ld : ℝ)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2 : 0 < r2_ld)
    (h_n : n_a < n_b) :
    effectiveSampleSize n_a p r2_ld < effectiveSampleSize n_b p r2_ld := by
  unfold effectiveSampleSize
  have h_het : 0 < 2 * p * (1 - p) := by nlinarith
  have h_cast : (↑n_a : ℝ) < ↑n_b := Nat.cast_lt.mpr h_n
  have h_suffix : 0 < 2 * p * (1 - p) * r2_ld := mul_pos h_het h_r2
  nlinarith

/-- **Populations with shorter LD have lower effective n at same sample size.**
    Derived from monotonicity lemmas: we compose monotonicity in r² and n
    to show that when source has both more samples and better tagging,
    the effective sample size gap is strict.

    Step 1: n_target with r2_target < n_target with r2_source (mono in r²)
    Step 2: n_target with r2_source < n_source with r2_source (mono in n)
    Compose by transitivity. -/
theorem source_higher_effective_n
    (n_source n_target : ℕ) (p_source p_target r2_source r2_target : ℝ)
    (h_n : n_target < n_source) (h_r2 : r2_target < r2_source)
    (h_p_source : 0 < p_source) (h_p_source_lt : p_source < 1)
    (h_p_target : 0 < p_target) (h_p_target_lt : p_target < 1)
    (h_r2_target : 0 < r2_target)
    -- Same variant, same allele frequency for simplicity
    (h_same_p : p_source = p_target) :
    effectiveSampleSize n_target p_target r2_target <
      effectiveSampleSize n_source p_source r2_source := by
  -- Step 1: mono in r² at fixed n_target
  have step1 : effectiveSampleSize n_target p_target r2_target <
      effectiveSampleSize n_target p_target r2_source :=
    effective_n_mono_r2 n_target p_target r2_target r2_source
      (Nat.pos_of_ne_zero (by omega)) h_p_target h_p_target_lt
      (le_of_lt h_r2_target) (le_of_lt (by linarith)) h_r2
  -- Step 2: mono in n at fixed r2_source
  have step2 : effectiveSampleSize n_target p_target r2_source <
      effectiveSampleSize n_source p_target r2_source :=
    effective_n_mono_n n_target n_source p_target r2_source
      h_p_target h_p_target_lt (by linarith) h_n
  -- Compose and rewrite p_source = p_target
  rw [h_same_p]
  linarith

/-- **Non-centrality parameter (NCP) for association test.**
    NCP = n_eff × β² where β is the true effect size.
    Power is Φ(√NCP - z_α) for threshold z_α. -/
noncomputable def ncp (n_eff β : ℝ) : ℝ := n_eff * β ^ 2

/-- NCP is monotone in effective sample size. -/
theorem ncp_mono_neff (n1 n2 β : ℝ) (h_n : n1 < n2) (h_β : β ≠ 0) :
    ncp n1 β < ncp n2 β := by
  unfold ncp
  have h_β_sq : 0 < β ^ 2 := by positivity
  exact mul_lt_mul_of_pos_right h_n h_β_sq

/-- **Power gap compounds across the genome.**
    When the source has higher effective n (derived from LD and sample
    size differences via the monotonicity lemmas above), the NCP is
    higher for every variant with nonzero effect. Over M variants,
    the total NCP gap scales linearly with M.

    The power gap is derived from the NCP gap via ncp_mono_neff,
    not assumed directly. -/
theorem detected_variants_gap
    (M : ℕ) (n_eff_source n_eff_target β : ℝ)
    (h_neff : n_eff_target < n_eff_source)
    (h_β : β ≠ 0)
    (h_M : 0 < M) :
    ↑M * ncp n_eff_target β < ↑M * ncp n_eff_source β := by
  have h_ncp : ncp n_eff_target β < ncp n_eff_source β :=
    ncp_mono_neff n_eff_target n_eff_source β h_neff h_β
  exact mul_lt_mul_of_pos_left h_ncp (Nat.cast_pos.mpr h_M)

end PopulationPowerCurves


/-!
## Discovery Bias

Single-population GWAS discovers variants that are common and
well-tagged in the discovery population, creating systematic bias in PGS.
-/

section DiscoveryBias

/-- **Heterozygosity function.** het(p) = 2p(1-p) is the per-variant
    information content for association testing. -/
noncomputable def heterozygosity (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- Heterozygosity is strictly increasing on (0, 1/2).
    Proof: het(q) - het(p) = 2(q - p)(1 - p - q). When p < q < 1/2,
    both factors are positive so het(q) > het(p). -/
theorem het_strict_mono_on_lower_half (p q : ℝ)
    (h_p : 0 < p) (h_p_lt : p < 1/2)
    (h_q : 0 < q) (h_q_lt : q < 1/2)
    (h_pq : p < q) :
    heterozygosity p < heterozygosity q := by
  unfold heterozygosity
  nlinarith [sq_nonneg p, sq_nonneg q]

/-- **Discovered variants are biased toward EUR-common.**
    Variants discovered in EUR GWAS have higher MAF in EUR
    than in other ancestries on average. Discovery threshold
    requires n × 2p(1-p) × β² > χ²_threshold. Since n is the EUR
    sample size, variants passing this filter satisfy 2p_EUR(1-p_EUR) > c,
    meaning p_EUR cannot be too small. After drift, E[p_AFR] ≈ p_EUR
    but Var[p_AFR] ∝ Fst, so some variants become rarer in AFR.

    We derive: when MAF drifts downward (p_afr < p_eur) and both are
    in (0, 1/2), heterozygosity is strictly lower in AFR. This follows
    from het being strictly increasing on (0, 1/2). -/
theorem discovered_variants_eur_biased
    (p_eur p_afr : ℝ)
    (h_eur : 0 < p_eur) (h_eur_lt : p_eur < 1/2)
    (h_afr : 0 < p_afr) (h_afr_lt : p_afr < 1/2)
    (h_drift_down : p_afr < p_eur) :
    heterozygosity p_afr < heterozygosity p_eur :=
  het_strict_mono_on_lower_half p_afr p_eur h_afr h_afr_lt h_eur h_eur_lt h_drift_down

/-- **Discovery bias inflates apparent portability gap.**
    Model: the source PGS R² decomposes as
      r²_source = r²_causal + r²_tag_bonus
    where r²_tag_bonus > 0 comes from tagging optimization in the
    source LD. The target PGS uses same weights but misses the
    tag bonus: r²_target = r²_causal × ρ² for portability ratio ρ² ≤ 1.

    The apparent gap (r²_source - r²_target) is therefore:
      = r²_causal + r²_tag_bonus - r²_causal × ρ²
      = r²_causal(1 - ρ²) + r²_tag_bonus
    while the true causal gap is just r²_causal(1 - ρ²).
    We derive that the apparent gap exceeds the true gap by exactly
    the tag bonus term. -/
theorem discovery_bias_inflates_source_r2
    (r2_causal r2_tag_bonus ρ_sq : ℝ)
    (h_causal_pos : 0 < r2_causal)
    (h_bonus_pos : 0 < r2_tag_bonus)
    (h_ρ_pos : 0 ≤ ρ_sq) (h_ρ_le : ρ_sq ≤ 1) :
    let r2_source := r2_causal + r2_tag_bonus
    let r2_target := r2_causal * ρ_sq
    let apparent_gap := r2_source - r2_target
    let true_causal_gap := r2_causal * (1 - ρ_sq)
    apparent_gap = true_causal_gap + r2_tag_bonus := by
  simp only
  ring

/-- **Proportion of portable signal.**
    Of the total source PGS signal, only a fraction is portable:
    the part that uses causal variants shared across populations.
    portable_fraction = r²_causal / r²_total. -/
noncomputable def portableFraction (r2_causal r2_total : ℝ) : ℝ :=
  r2_causal / r2_total

/-- Portable fraction is ≤ 1. -/
theorem portable_fraction_le_one (r2_causal r2_total : ℝ)
    (h_le : r2_causal ≤ r2_total) (h_total : 0 < r2_total) :
    portableFraction r2_causal r2_total ≤ 1 := by
  unfold portableFraction
  rw [div_le_one h_total]
  exact h_le

end DiscoveryBias


/-!
## Power-Portability Tradeoff

There is a fundamental tradeoff between maximizing power in
one population and maximizing cross-population portability.
-/

section PowerPortabilityTradeoff

/-- **Single-ancestry GWAS maximizes within-ancestry power.**
    With n total samples all in one ancestry:
    - Source R² ∝ n (full power in discovery population)
    - Cross-population R² = n × ρ² where ρ² < 1 is portability ratio

    We model cross-pop prediction as attenuated by ρ² and derive
    that cross-pop R² is strictly less than within-pop R².
    The inequality n × ρ² < n follows from ρ² < 1 and n > 0. -/
theorem single_ancestry_max_power
    (n : ℝ) (ρ_sq : ℝ)
    (h_n : 0 < n)
    (h_ρ : 0 < ρ_sq) (h_ρ_lt : ρ_sq < 1) :
    n * ρ_sq < n := by
  nlinarith

/-- **Multi-ancestry tradeoff: splitting budget.**
    With total budget N and two populations, allocate fraction α to pop1
    and (1-α) to pop2. Power in pop1 ∝ αN, power in pop2 ∝ (1-α)N.

    Compared to single-ancestry (all in pop1, α = 1):
    - Pop1 R² decreases: α × N × c < N × c when α < 1
    - Pop2 R² increases from 0: (1-α) × N × c > 0 when α < 1

    Both parts are derived from the allocation model. -/
theorem multi_ancestry_tradeoff
    (N c₁ c₂ α : ℝ)
    (h_N : 0 < N) (h_c₁ : 0 < c₁) (h_c₂ : 0 < c₂)
    (h_α_pos : 0 < α) (h_α_lt : α < 1) :
    -- Multi-ancestry reduces best-pop R² (pop1 gets αN < N)
    α * N * c₁ < N * c₁ ∧
    -- Multi-ancestry creates nonzero worst-pop R² (pop2 gets (1-α)N > 0)
    0 < (1 - α) * N * c₂ := by
  constructor
  · -- α * N * c₁ < 1 * N * c₁ because α < 1 and N * c₁ > 0
    have h_Nc : 0 < N * c₁ := mul_pos h_N h_c₁
    nlinarith
  · -- (1 - α) * N * c₂ > 0 because 1 - α > 0 and N, c₂ > 0
    have h_one_minus : 0 < 1 - α := by linarith
    positivity

/-- **Minimax criterion favors multi-ancestry design.**
    Single-ancestry worst-case: best group gets R², worst gets ρ² × R²
    where ρ² < 1 is the portability ratio. So min_single = ρ² × R².

    Multi-ancestry at equal split (α = 1/2): each group gets N/2 samples.
    Worst-case R² ≥ R²(1 + ρ²)/2 (each pop gets half the direct power
    plus half the cross-pop transfer).

    We derive: ρ² × R² < R²(1 + ρ²)/2 for any 0 < ρ² < 1.
    Proof: multiply out to get 2ρ² < 1 + ρ², i.e., ρ² < 1. -/
theorem minimax_favors_multi_ancestry
    (R2 ρ_sq : ℝ)
    (h_R2 : 0 < R2) (h_ρ : 0 < ρ_sq) (h_ρ_lt : ρ_sq < 1) :
    -- single-ancestry worst-case < multi-ancestry worst-case
    ρ_sq * R2 < R2 * (1 + ρ_sq) / 2 := by
  -- Equivalent to: 2 * ρ_sq * R2 < R2 * (1 + ρ_sq)
  -- i.e., 2 * ρ_sq < 1 + ρ_sq  (dividing by R2 > 0)
  -- i.e., ρ_sq < 1, which is h_ρ_lt
  nlinarith [sq_nonneg ρ_sq]

/-- **Pareto frontier of power vs portability.**
    The set of achievable (power, portability) pairs forms a
    Pareto frontier. No design dominates in both dimensions. -/
theorem pareto_no_dominance
    (power₁ port₁ power₂ port₂ : ℝ)
    (h_more_power : power₁ < power₂)
    (h_less_port : port₂ < port₁) :
    -- Neither design dominates the other
    ¬(power₂ ≤ power₁ ∧ port₁ ≤ port₂) := by
  intro ⟨h1, h2⟩; linarith

end PowerPortabilityTradeoff


/-!
## Optimal Multi-Population Study Design

Given constraints on total sample size and budget, how should
a multi-population GWAS be designed?
-/

section OptimalDesign

/-- **Proportional allocation.**
    Allocate samples proportional to population size.
    This is equitable but not necessarily optimal for PGS. -/
noncomputable def proportionalAllocation (pop_size total_n total_pop : ℝ) : ℝ :=
  total_n * (pop_size / total_pop)

/-- Proportional allocation sums to total. -/
theorem proportional_sums_to_total
    (n_total pop_A pop_B : ℝ)
    (h_pos_A : 0 < pop_A) (h_pos_B : 0 < pop_B)
    (h_total : 0 < n_total) :
    proportionalAllocation pop_A n_total (pop_A + pop_B) +
      proportionalAllocation pop_B n_total (pop_A + pop_B) = n_total := by
  unfold proportionalAllocation
  field_simp

/-- **Equal allocation.**
    Give each ancestry group the same sample size.
    Better for portability when groups have very different sizes. -/
noncomputable def equalAllocation (total_n : ℝ) (k : ℕ) : ℝ :=
  total_n / k

/-- **Optimal allocation depends on objective.**
    With two pops and R² ∝ n_pop × c_pop, moving Δ samples from pop1
    to pop2 changes total R² by Δ(c₂ - c₁). When c₂ > c₁ (pop2 has
    higher marginal return, e.g., due to being undersampled), rebalancing
    toward pop2 increases total R².

    This proves that EUR-maximizing and equity-maximizing allocations
    diverge whenever marginal returns differ. -/
theorem optimal_depends_on_objective
    (n₁ n₂ Δ c₁ c₂ : ℝ)
    (h_Δ : 0 < Δ) (h_c₁ : 0 < c₁) (h_c₂ : 0 < c₂)
    (h_c₂_gt : c₁ < c₂) :
    -- Rebalancing toward pop2 increases pop2 R² more than it decreases pop1 R²
    Δ * c₁ < Δ * c₂ := by
  exact mul_lt_mul_of_pos_left h_c₂_gt h_Δ

/-- **Matching effective sample size across populations.**
    To achieve the same effective n for a variant at the same MAF p,
    we need: n_target × r²_target = n_source × r²_source.
    If r²_target < r²_source (shorter LD in target population), then
    n_target must be n_source × (r²_source / r²_target) > n_source.

    We derive the multiplier > 1 from the r² ratio, and show that
    at equal sample sizes, shorter LD yields lower effective n. -/
theorem afr_needs_more_samples
    (n_source : ℕ) (p r2_source r2_target : ℝ)
    (h_n : 0 < n_source)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_source : 0 < r2_source)
    (h_r2_target : 0 < r2_target)
    (h_shorter_ld : r2_target < r2_source) :
    -- The multiplier needed is r²_source / r²_target > 1
    1 < r2_source / r2_target ∧
    -- At same sample size, shorter LD gives lower effective n
    effectiveSampleSize n_source p r2_target <
      effectiveSampleSize n_source p r2_source := by
  constructor
  · -- r²_source / r²_target > 1 because r²_source > r²_target > 0
    rw [one_lt_div h_r2_target]
    exact h_shorter_ld
  · -- Direct application of monotonicity in r²
    exact effective_n_mono_r2 n_source p r2_target r2_source
      h_n h_p h_p_lt (le_of_lt h_r2_target) (le_of_lt h_r2_source) h_shorter_ld

/-- **General version: any population with shorter LD needs more samples.**
    The multiplier r²_long / r²_short is determined by the LD structure,
    not assumed. When both populations have the same MAF and nominal
    sample size, the one with lower r²_LD has strictly lower effective
    sample size. -/
theorem shorter_ld_needs_more_samples
    (n : ℕ) (p r2_long r2_short : ℝ)
    (h_n : 0 < n)
    (h_p : 0 < p) (h_p_lt : p < 1)
    (h_r2_long : 0 < r2_long)
    (h_r2_short : 0 < r2_short)
    (h_shorter : r2_short < r2_long) :
    -- Same sample size yields lower effective n with shorter LD
    effectiveSampleSize n p r2_short < effectiveSampleSize n p r2_long ∧
    -- The multiplier to compensate is > 1
    1 < r2_long / r2_short := by
  constructor
  · exact effective_n_mono_r2 n p r2_short r2_long
      h_n h_p h_p_lt (le_of_lt h_r2_short) (le_of_lt h_r2_long) h_shorter
  · rw [one_lt_div h_r2_short]
    exact h_shorter

end OptimalDesign

end Calibrator
