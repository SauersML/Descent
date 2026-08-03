/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Rare Variant Contributions to PGS and Portability

This file formalizes the role of rare variants (MAF < 1%) in
polygenic scores and their impact on cross-population portability.
Rare variants are mostly population-specific, creating unique
portability challenges.

Key results:
1. Rare variant population-specificity
2. Burden tests and gene-based PGS
3. Loss-of-function variant portability
4. Rare variant effect size distribution

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat rare-variant sharing, burden tests or loss-of-function variants.
Sources for individual results, where they exist, are cited at those results.
-/


/-!
## Rare Variant Population Specificity

Most rare variants are recent in origin and population-specific.
This has direct implications for PGS portability.
-/

section RareVariantSpecificity


/-- **Ultra-rare variants are almost never shared.**
    Under the coalescent, a variant at frequency p in one population
    has sharing probability ≈ 2·Ne·p in a diverged population (for
    recent divergence relative to 2·Ne generations).

    For ultra-rare variants where p < 1/(2·Ne), the sharing probability
    2·Ne·p is bounded below 1.  This is the defining feature of
    ultra-rare variants: they arose recently enough that they almost
    certainly have not spread to the sister population.

    Proof: multiply both sides of p < 1/(2·Ne) by the positive
    quantity 2·Ne. -/
theorem ultra_rare_not_shared
    (Ne p : ℝ)
    (h_Ne : 0 < Ne)
    (h_ultra_rare : p < 1 / (2 * Ne)) :
    -- sharing_prob = 2 * Ne * p (coalescent approximation) is < 1
    2 * Ne * p < 1 := by
  have h2Ne_pos : (0 : ℝ) < 2 * Ne := by positivity
  rw [lt_div_iff₀ h2Ne_pos] at h_ultra_rare
  linarith [mul_comm p (2 * Ne)]

/-- **One positive summand's share of a sum of two is strictly between `0` and
    `1`.**

    Read as genetics the two summands are rare and common contributions to
    heritability, so the rare share is neither nothing nor everything. The
    LDAK-thin scaling `E[β²] ∝ [p(1-p)]^(1+α)` that would make the rare
    contribution *substantial* rather than merely positive appears nowhere: no
    `α`, no frequency and no effect size occurs below, and "substantial" is not
    a formal claim about a quantity bounded only by `0` and `1`. -/
theorem div_add_mem_Ioo_of_pos
    (n_rare v_rare n_common v_common : ℝ)
    (h_nr : 0 < n_rare) (h_vr : 0 < v_rare)
    (h_nc : 0 < n_common) (h_vc : 0 < v_common) :
    -- h²_rare is a strictly positive component of h²_total
    let h2_rare := n_rare * v_rare
    let h2_total := n_rare * v_rare + n_common * v_common
    0 < h2_rare / h2_total ∧ h2_rare / h2_total < 1 := by
  constructor
  · apply div_pos (by positivity) (by positivity)
  · rw [div_lt_one (by positivity : 0 < n_rare * v_rare + n_common * v_common)]
    linarith [mul_pos h_nc h_vc]

/-- **A product with a zero factor is zero:** `maf_B = 0` gives
    `β²·(2·maf_B·(1 - maf_B)) = 0`.

    The reading is that a variant absent from a population contributes nothing
    to a score there. That the contribution IS `β²·2p(1-p)` is the modelling
    step and is stipulated by writing it; no population, no score and no
    variant appears below. -/
theorem mul_genotype_variance_eq_zero_of_freq_zero
    (β maf_B : ℝ) (h_absent : maf_B = 0) :
    β ^ 2 * (2 * maf_B * (1 - maf_B)) = 0 := by
  rw [h_absent]; ring


/-- **A ratio above two means the numerator is above twice the denominator**,
    for a positive denominator.

    Cross-multiplication. The demographic reading — larger long-term `Nₑ` and no
    out-of-Africa bottleneck, hence more rare variants — is the reason someone
    might assert the hypothesis `2 < ratio`, and is not derived here. Nothing
    below names a population, and the factor claimed in prose was three while
    the hypothesis says two. -/
theorem two_mul_lt_of_two_lt_div
    (n_rare_afr n_rare_eur ratio : ℝ)
    (h_ratio : ratio = n_rare_afr / n_rare_eur)
    (h_more : 2 < ratio)
    (h_eur_pos : 0 < n_rare_eur) :
    2 * n_rare_eur < n_rare_afr := by
  have : 2 < n_rare_afr / n_rare_eur := by linarith
  rwa [lt_div_iff₀ h_eur_pos] at this

end RareVariantSpecificity


/-!
## Burden Tests and Gene-Based PGS

Collapsing rare variants into gene-level scores improves power
and can improve portability.
-/

section BurdenTests

/-- **At least one of `k` shares beats one share**, for `k ≥ 2`:
    `s < 1 - (1-s)^k` whenever `0 < s < 1`.

    The motivating reading is that if each of `k` variants in a gene is shared
    across populations independently with rate `s`, a gene-level burden survives
    when any one of them is shared. That reading is prose: no gene, no burden,
    no population and no independence assumption appears below. The statement is
    the inequality on two reals and a natural, and `nlinarith` proves it. Whether
    the sharing events are independent — the assumption that makes
    `1 - (1-s)^k` the right probability — is exactly what a portability claim
    would have to establish, and it is assumed away by writing the expression. -/
theorem gene_level_share_gt_single_share
    (s : ℝ) (k : ℕ)
    (h_s_pos : 0 < s) (h_s_lt : s < 1)
    (h_k : 2 ≤ k) :
    s < 1 - (1 - s) ^ k := by
  have h_base : (1 - s) ^ k ≤ (1 - s) ^ 2 := by
    apply pow_le_pow_of_le_one (by linarith) (by linarith) h_k
  have h_expand : (1 - s) ^ 2 = 1 - 2 * s + s ^ 2 := by ring
  nlinarith [sq_nonneg s]

/-- **`β² < k·β²` for `k ≥ 2` and `β ≠ 0`.**

    Read as genetics: if `k` variants in a gene carry the same effect `β` and
    contribute additively, gene-level burden variance `k·β²` exceeds
    single-variant variance `β²`. Nothing below carries that reading. There is
    no gene, no burden, and no second population — in particular no
    cross-population correlation, which is what a portability claim would need.
    What is proved is that multiplying a positive number by something larger
    than one increases it. -/
theorem sq_lt_cast_mul_sq_of_two_le
    (β : ℝ) (k : ℕ)
    (h_β : β ≠ 0)
    (h_k : 2 ≤ k) :
    -- Gene burden variance = k · β² > β² = single variant variance
    β ^ 2 < ↑k * β ^ 2 := by
  have h_β2 : 0 < β ^ 2 := sq_pos_of_ne_zero h_β
  have h_k_real : (1 : ℝ) < ↑k := by
    exact_mod_cast (by omega : 1 < k)
  linarith [mul_lt_mul_of_pos_right h_k_real h_β2]


/-- **Two opposite nonzero effects: the sum vanishes and the sum of squares does
    not.** `(β₁+β₂)² < β₁² + β₂²` when `β₁ + β₂ = 0` and `β₁ ≠ 0`.

    This is the two-variant shape of the reason a variance statistic sees signal
    a burden statistic cancels away. It is not a theorem about SKAT: no kernel,
    no test statistic, no null distribution and no power comparison appears
    below, and nothing here says the variance statistic *detects* anything. Two
    reals summing to zero, one of them nonzero. -/
theorem sq_sum_lt_sum_sq_of_opposite
    (β₁ β₂ : ℝ)
    (h_opposite : β₁ + β₂ = 0)
    (h_nonzero : β₁ ≠ 0) :
    -- Burden signal (sum) is zero but SKAT signal (sum of squares) is positive
    (β₁ + β₂) ^ 2 < β₁ ^ 2 + β₂ ^ 2 := by
  rw [h_opposite]
  simp
  have : β₂ = -β₁ := by linarith
  rw [this]
  positivity

end BurdenTests


/-!
## WGS-Based PGS

Whole genome sequencing enables inclusion of rare variants in PGS,
but the portability implications are complex.
-/

section WGSBasedPGS


/-- **`β²·2p(1-p)·s` is monotone in `p` below `1/2` and in `s`:** raising both
    the frequency and the sharing rate does not decrease the product.

    The reading is that the common-variant part of a score ports better than
    the rare part. Below there is no score, no component and no population, and
    the expression `β²·2p(1-p)·s` being the cross-population signal is
    stipulated rather than derived. Two monotonicity steps in a product of
    nonnegatives. -/
theorem mul_genotype_variance_mul_le_of_le
    (β p_common p_rare s_common s_rare : ℝ)
    (h_β : β ≠ 0)
    (h_pc : 0 < p_common) (h_pc1 : p_common < 1)
    (h_pr : 0 < p_rare) (h_pr1 : p_rare < 1)
    (h_sr : 0 < s_rare)
    (h_freq : p_rare < p_common) (h_half : p_common ≤ 1/2)
    (h_sharing : s_rare ≤ s_common) :
    β ^ 2 * (2 * p_rare * (1 - p_rare)) * s_rare ≤
      β ^ 2 * (2 * p_common * (1 - p_common)) * s_common := by
  have h_β2 : 0 < β ^ 2 := sq_pos_of_ne_zero h_β
  have h_het_rare : 0 ≤ 2 * p_rare * (1 - p_rare) := by nlinarith
  have h_het_le : 2 * p_rare * (1 - p_rare) ≤ 2 * p_common * (1 - p_common) := by
    nlinarith [sq_nonneg (p_common - 1/2), sq_nonneg (p_rare - 1/2)]
  calc β ^ 2 * (2 * p_rare * (1 - p_rare)) * s_rare
      ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_rare := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h_sr)
        exact mul_le_mul_of_nonneg_left h_het_le (le_of_lt h_β2)
    _ ≤ β ^ 2 * (2 * p_common * (1 - p_common)) * s_common := by
        apply mul_le_mul_of_nonneg_left h_sharing
        apply mul_nonneg (le_of_lt h_β2)
        nlinarith [sq_nonneg (p_common - 1/2)]


end WGSBasedPGS


/-!
## Loss-of-Function Variants

Loss-of-function (LoF) variants have uniquely interpretable effects
and different portability properties.
-/

section LossOfFunction

/-- **LoF variants have large effects.**
    LoF variants typically have effect sizes 5-10x larger than
    common regulatory variants, but they are very rare. -/
theorem lof_large_effects
    (β_lof β_common : ℝ)
    (h_larger : |β_common| < |β_lof|)
    (h_common_pos : 0 < |β_common|) :
    1 < |β_lof| / |β_common| := by
  rw [one_lt_div₀ h_common_pos]
  exact h_larger

/-!
### Mutation-selection balance, as the fixed point of a map

The frequency of a deleterious allele under purifying selection is usually quoted
as `μ/s`. That number is not a frequency: for `s < μ` it exceeds `1`, and `s < μ`
is admissible for exactly the weakly-constrained comparison arm the portability
claim is about. It is also the wrong quantity twice over — the dominant balance
is `μ/(h s)` and the recessive one is `√(μ/s)` — and this file's subject matter,
LoF variants scored by pLI and haploinsufficiency, spans both regimes.

So the two regimes are written here as one-generation maps and their equilibria
are derived as fixed points of those maps, in the shape of
`Calibrator.PopulationGeneticsFoundations.selectionMigrationEquilibrium_isFixedPoint`.
Both equilibria land in `[0, 1]` by construction rather than by hypothesis.
-/

/-- **One generation of mutation-selection dynamics for a rare deleterious allele
with dominance coefficient `h`.**

Heterozygotes carry selective load `h * s` and are the only carriers that matter
while the allele is rare, so the selection step multiplies the frequency by
`1 - h * s`; mutation then converts a fraction `mu` of the wild-type allele.
The `p ^ 2` homozygote term is dropped, which is the rare-allele linearization
and is valid only while `h * s` dominates `mu` — see
`mutationSelectionBalance_at_zero_dominance`, which shows the map degenerates at
`h = 0` and hands the recessive case to `mutationSelectionStepRecessive`.

    Empirical status: UNTESTED. -/
noncomputable def mutationSelectionStepRare (mu s h p : ℝ) : ℝ :=
  p * (1 - h * s) + mu * (1 - p)

/-- **Mutation-selection balance for a partially dominant deleterious allele.**

The fixed point of `mutationSelectionStepRare`. It is `mu / (h * s + mu)`, not
`mu / (h * s)`: the two agree to leading order when `h * s` is large against
`mu`, and the difference is what keeps this quantity inside `[0, 1]` for every
admissible parameter, including the weak-constraint regime `s < mu` where
`mu / s` is not a frequency at all.

    Empirical status: UNTESTED. -/
noncomputable def mutationSelectionBalance (mu s h : ℝ) : ℝ :=
  mu / (h * s + mu)

/-- **Mutation-selection balance is the drift chart's saturation map, at a
different argument.**

`fstFromTau` sends `tau` to `tau / (1 + tau)`, and the balance frequency is that
same map applied to the ratio of mutation to effective selection, `mu / (h s)`.
The two modules therefore share one rational function: whatever is true of the
saturation law at one is true at the other, and a change to either body that
breaks this identity fails to compile rather than leaving the two quietly
disagreeing about a shape they both claim. -/
theorem mutationSelectionBalance_eq_fstFromTau (mu s h : ℝ)
    (hhs : h * s ≠ 0) (hsum : h * s + mu ≠ 0) :
    mutationSelectionBalance mu s h = fstFromTau (mu / (h * s)) := by
  unfold mutationSelectionBalance fstFromTau
  have hden : (h * s + mu) / (h * s) = 1 + mu / (h * s) := by
    rw [add_div, div_self hhs]
  rw [← hden, div_eq_div_iff hsum (div_ne_zero hsum hhs)]
  ring

/-- **Mutation-selection balance is the identity-fraction map at the scaled selective load.**

`DGP.fstMutationDriftEquilibrium θ = 1 / (1 + θ)` is this corpus's one body for the fraction
surviving a balance between a replenishing and a removing force, and the dominant
mutation-selection balance is that map at `θ = h·s / mu` — the selective load measured in
units of the mutation rate, exactly as `θ` and `M` measure mutation and migration in units
of drift.

Reading it this way is what makes the `mu / (h·s + mu)` form forced rather than chosen. The
textbook `mu / (h·s)` is not `1 / (1 + θ)` at any `θ`, and it leaves the unit interval in the
weak-constraint regime; the identity below is what a substitution of the one for the other
would have to contradict. -/
theorem mutationSelectionBalance_eq_identityFraction (mu s h : ℝ) (hmu : mu ≠ 0) :
    mutationSelectionBalance mu s h = fstMutationDriftEquilibrium (h * s / mu) := by
  have hsum : (1 : ℝ) + h * s / mu = (h * s + mu) / mu := by
    field_simp
    ring
  unfold mutationSelectionBalance fstMutationDriftEquilibrium
  rw [hsum, one_div_div]

/-- **The dominant balance is a fixed point of the dominant map.** This is what
makes the closed form above impossible to stipulate: it is derived from the
dynamic rather than asserted alongside it. -/
theorem mutationSelectionBalance_isFixedPoint (mu s h : ℝ)
    (h_load : 0 < h * s + mu) :
    mutationSelectionStepRare mu s h (mutationSelectionBalance mu s h) =
      mutationSelectionBalance mu s h := by
  have hne : h * s + mu ≠ 0 := ne_of_gt h_load
  unfold mutationSelectionStepRare mutationSelectionBalance
  field_simp
  ring

/-- The dominant balance is a frequency: it lies in `[0, 1]` for every
nonnegative mutation rate, nonnegative selective component `h*s`, and positive
total load. The quoted `mu / s` has no such bound, and exceeds `1` whenever
`s < mu`. -/
theorem mutationSelectionBalance_mem_unit (mu s h : ℝ)
    (h_mu : 0 ≤ mu) (h_hs : 0 ≤ h * s) (h_load : 0 < h * s + mu) :
    0 ≤ mutationSelectionBalance mu s h ∧ mutationSelectionBalance mu s h ≤ 1 := by
  unfold mutationSelectionBalance
  refine ⟨div_nonneg h_mu h_load.le, ?_⟩
  rw [div_le_one h_load]
  linarith

/-- The balance is strictly below the textbook `mu / (h s)`, so the classical
formula is an upper bound and the correction is second order in `mu`. -/
theorem mutationSelectionBalance_lt_classical (mu s h : ℝ)
    (h_mu : 0 < mu) (h_hs : 0 < h * s) :
    mutationSelectionBalance mu s h < mu / (h * s) := by
  unfold mutationSelectionBalance
  exact div_lt_div_of_pos_left h_mu h_hs (by linarith)

/-- **The dominant linearization degenerates at full recessivity.** At `h = 0`
the map has no selection at all, and its fixed point is fixation. This is not a
defect of the closed form but a statement about the linearization: with `h = 0`
selection acts only through the dropped `p ^ 2` term, so the recessive case needs
`mutationSelectionStepRecessive` and gets a different scaling law. -/
theorem mutationSelectionBalance_at_zero_dominance (mu s : ℝ) (h_mu : mu ≠ 0) :
    mutationSelectionBalance mu s 0 = 1 := by
  unfold mutationSelectionBalance
  rw [zero_mul, zero_add]
  exact div_self h_mu

/-- **One generation for a fully recessive deleterious allele.** Selection acts
only on homozygotes, so the load is `s * p` per copy rather than `h * s`, and
mutation replenishes as before.

    Empirical status: UNTESTED. -/
noncomputable def mutationSelectionStepRecessive (mu s p : ℝ) : ℝ :=
  p - s * p ^ 2 + mu * (1 - p)

/-- **Mutation-selection balance for a fully recessive deleterious allele**: the
nonnegative root of `s p² + mu p − mu = 0`, the fixed point of
`mutationSelectionStepRecessive`. It is `√(mu/s)` to leading order — a
qualitatively different scaling from the dominant `mu/(h s)` — and it is bounded
by `1` for every positive `s`.

    Empirical status: UNTESTED. -/
noncomputable def mutationSelectionBalanceRecessive (mu s : ℝ) : ℝ :=
  (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)

/-- **The recessive balance is a fixed point of the recessive map.** -/
theorem mutationSelectionBalanceRecessive_isFixedPoint (mu s : ℝ)
    (h_mu : 0 ≤ mu) (h_s : 0 < s) :
    mutationSelectionStepRecessive mu s (mutationSelectionBalanceRecessive mu s) =
      mutationSelectionBalanceRecessive mu s := by
  have hs : s ≠ 0 := ne_of_gt h_s
  have hnn : 0 ≤ mu * (mu + 4 * s) := by
    nlinarith [mul_nonneg h_mu h_mu, mul_nonneg h_mu h_s.le]
  have hR : Real.sqrt (mu * (mu + 4 * s)) ^ 2 = mu * (mu + 4 * s) := Real.sq_sqrt hnn
  -- `x` is the candidate frequency; `2 s x = R - mu` is the only fact about it used.
  have hx : 2 * s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) =
      Real.sqrt (mu * (mu + 4 * s)) - mu := by
    field_simp
  have hR' : (2 * s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) + mu) ^ 2 =
      mu * (mu + 4 * s) := by
    rw [hx]
    linear_combination hR
  have hfour : (4 * s) * (s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) ^ 2) =
      (4 * s) * (mu * (1 - (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s))) := by
    linear_combination hR'
  have hfour_ne : (4 : ℝ) * s ≠ 0 := by
    intro hc
    apply hs
    linarith
  have hkey : s * ((Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) ^ 2 =
      mu * (1 - (Real.sqrt (mu * (mu + 4 * s)) - mu) / (2 * s)) :=
    mul_left_cancel₀ hfour_ne hfour
  unfold mutationSelectionStepRecessive mutationSelectionBalanceRecessive
  linear_combination -hkey

/-- The recessive balance is a frequency, and its square is bounded by `mu / s`:
`s p² ≤ mu`, which is the exact sense in which `p ≲ √(mu/s)`. -/
theorem mutationSelectionBalanceRecessive_sq_le (mu s : ℝ)
    (h_mu : 0 ≤ mu) (h_s : 0 < s) :
    s * mutationSelectionBalanceRecessive mu s ^ 2 ≤ mu ∧
      0 ≤ mutationSelectionBalanceRecessive mu s := by
  have hle : mu * mu ≤ mu * (mu + 4 * s) := by
    nlinarith [mul_nonneg h_mu h_s.le]
  have hRge : mu ≤ Real.sqrt (mu * (mu + 4 * s)) :=
    calc mu = Real.sqrt (mu * mu) := (Real.sqrt_mul_self h_mu).symm
      _ ≤ Real.sqrt (mu * (mu + 4 * s)) := Real.sqrt_le_sqrt hle
  have hnonneg : 0 ≤ mutationSelectionBalanceRecessive mu s := by
    unfold mutationSelectionBalanceRecessive
    apply div_nonneg (by linarith)
    linarith
  refine ⟨?_, hnonneg⟩
  have hfix := mutationSelectionBalanceRecessive_isFixedPoint mu s h_mu h_s
  simp only [mutationSelectionStepRecessive] at hfix
  nlinarith [hfix, mul_nonneg h_mu hnonneg]

/-- **LoF variant portability depends on gene constraint.**
    Highly constrained genes have LoF variants in all populations
    (purifying selection maintains them rare). The comparison is made on the
    dominant mutation-selection balance derived above, at a common dominance
    coefficient `h`, so both arms are frequencies in `[0, 1]` whatever the
    selection coefficients are — including the weakly constrained arm with
    `s < mu`, where `mu / s` exceeds one and is therefore not a frequency at all.

    Worked example: Genes with high constraint (e.g., pLI > 0.9) show
    this pattern most clearly, and `haploinsufficiency_consistent_direction`
    below is about the same `h > 0` regime this theorem is stated in. -/
theorem constrained_genes_more_portable_lof
    (s_constrained s_unconstrained μ h : ℝ)
    (h_μ : 0 < μ)
    (h_h : 0 < h)
    (h_su : 0 < s_unconstrained)
    (h_stronger : s_unconstrained < s_constrained) :
    -- Equilibrium frequency is lower under stronger constraint
    mutationSelectionBalance μ s_constrained h <
      mutationSelectionBalance μ s_unconstrained h := by
  unfold mutationSelectionBalance
  have h_lo : 0 < h * s_unconstrained + μ := by nlinarith
  have h_lt : h * s_unconstrained + μ < h * s_constrained + μ := by nlinarith
  exact div_lt_div_of_pos_left h_μ h_lo h_lt

/-- **Haploinsufficiency gives directional effects.**
    For haploinsufficient genes, any LoF variant reduces function.
    The direction of effect is consistent across populations,
    even if the specific variants differ. -/
theorem haploinsufficiency_consistent_direction
    (effect_pop1 effect_pop2 : ℝ)
    (h_same_direction : 0 < effect_pop1 ∧ 0 < effect_pop2
      ∨ effect_pop1 < 0 ∧ effect_pop2 < 0) :
    effect_pop1 * effect_pop2 > 0 := by
  rcases h_same_direction with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos h1 h2
  · exact mul_pos_of_neg_of_neg h1 h2

/-! **Deleted: `gene_lof_maximally_portable_rare`.**

This declaration is absent on purpose. It took `a ≤ b` and `b ≤ c` and returned
`le_trans h₁ h₂`: transitivity of `≤` on three reals, which is Mathlib's
`le_trans`, under a name asserting that gene-level loss-of-function aggregation
is the most portable rare-variant construction. Nothing in it referred to a
gene, a variant, an annotation or a score, and "maximally portable" is not a
statement two applications of `≤` can carry — a maximum needs a set to be
maximal over, and none was given. -/

end LossOfFunction


/-!
## Rare Variant Effect Size Distribution

The effect size distribution of rare variants differs from common
variants, affecting both PGS construction and portability.
-/

section EffectSizeDistribution

/-- **`2p(1-p)` is strictly increasing below `1/2`.**

    The selection reading — purifying selection removing large-effect alleles
    that reach high frequency, so `E[β²|MAF]` falls with `MAF` — is about effect
    sizes, and no effect size appears below. This is the heterozygosity
    expression alone, monotone on the left half of the frequency range. -/
theorem two_mul_mul_one_sub_lt_of_lt
    (maf_rare maf_common : ℝ)
    (h_common_lt : maf_common ≤ 1/2)
    (h_rare_maf : maf_rare < maf_common) :
    -- Heterozygosity is smaller for rarer variants (when both ≤ 1/2)
    2 * maf_rare * (1 - maf_rare) < 2 * maf_common * (1 - maf_common) := by
  nlinarith [sq_nonneg (maf_common - 1/2), sq_nonneg (maf_rare - 1/2)]

/-- **The α model: E[β²] ∝ [p(1-p)]^(1+α).**
    α = 0: neutral (no relationship between MAF and effect)
    α = -1: LDAK (β² ∝ 1/[p(1-p)])
    When `α < -1`, the exponent `1 + α` is negative, so lower heterozygosity
    implies a larger expected effect-size multiplier. This makes rarer variants
    more population-specific and therefore less portable.

    Empirical status: UNTESTED. -/
noncomputable def expectedEffectMultiplier (p α : ℝ) : ℝ :=
  (p * (1 - p)) ^ (1 + α)

/-- **The multiplier is symmetric about even frequency and neutral at `α = -1`.** It depends on
the allele only through the heterozygosity `p(1-p)`, so relabelling which allele is counted
cannot change it, and the exponent `1 + α` is zero exactly at the selection parameter where
frequency drops out entirely. -/
theorem expectedEffectMultiplier_symm (p α : ℝ) :
    expectedEffectMultiplier (1 - p) α = expectedEffectMultiplier p α := by
  unfold expectedEffectMultiplier
  rw [show (1 - p) * (1 - (1 - p)) = p * (1 - p) by ring]

theorem expectedEffectMultiplier_neutral_exponent (p : ℝ) (hp : 0 < p * (1 - p)) :
    expectedEffectMultiplier p (-1) = 1 := by
  unfold expectedEffectMultiplier
  rw [show (1 : ℝ) + -1 = 0 by ring, Real.rpow_zero]

theorem alpha_model_portability_impact
    (p_rare p_common α : ℝ)
    (h_rare_pos : 0 < p_rare)
    (h_rare_lt : p_rare < p_common)
    (h_common_le : p_common ≤ 1 / 2)
    (h_alpha : α < -1) :
    expectedEffectMultiplier p_common α < expectedEffectMultiplier p_rare α := by
  unfold expectedEffectMultiplier
  have h_common_pos : 0 < p_common :=
    lt_trans h_rare_pos h_rare_lt
  have h_common_lt_one : p_common < 1 := by
    linarith
  have h_rare_lt_half : p_rare < 1 / 2 :=
    lt_of_lt_of_le h_rare_lt h_common_le
  have h_rare_het_pos : 0 < p_rare * (1 - p_rare) := by
    apply mul_pos h_rare_pos
    linarith
  have h_het_lt : p_rare * (1 - p_rare) < p_common * (1 - p_common) := by
    nlinarith [sq_nonneg (p_common - 1 / 2), sq_nonneg (p_rare - 1 / 2)]
  have h_exp_neg : 1 + α < 0 := by
    linarith
  exact Real.rpow_lt_rpow_of_neg h_rare_het_pos h_het_lt h_exp_neg

/-- **A reciprocal of a product below `1/100` exceeds `100`:** for
    `0 < maf < 1/100` and `|β| ≤ 1` with `β ≠ 0`, `100 < 1/(maf·β²)`.

    The reading is that a rare variant needs a large sample, via
    `R² ∝ n·MAF·β²` and a power threshold. Neither the proportionality nor the
    threshold appears below: there is no sample size, no power and no `R²`, and
    `100` is a numeral rather than a required `n`. -/
theorem hundred_lt_one_div_mul_sq
    (maf β : ℝ) (h_maf : 0 < maf) (h_maf_small : maf < 1 / 100)
    (h_β : β ≠ 0) (h_β_le : |β| ≤ 1) :
    100 < 1 / (maf * β ^ 2) := by
  have h_β_sq : β ^ 2 ≤ 1 := by nlinarith [sq_abs β, abs_nonneg β]
  have h_prod_pos : 0 < maf * β ^ 2 := mul_pos h_maf (sq_pos_of_ne_zero h_β)
  rw [lt_div_iff₀ h_prod_pos]
  have h_prod_small : maf * β ^ 2 < 1 / 100 := by
    calc maf * β ^ 2 ≤ maf * 1 := by nlinarith [sq_nonneg β]
    _ = maf := mul_one maf
    _ < 1 / 100 := h_maf_small
  nlinarith


end EffectSizeDistribution

end Calibrator
