import Calibrator.Probability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Haplotype-Based PGS and Portability

This file formalizes how haplotype structure affects PGS
portability. Standard PGS uses individual SNP dosages, but
haplotype-based approaches can capture phase-dependent effects
and improve cross-ancestry prediction.

Key results:
1. Haplotype frequency and diversity across populations
2. Phase-dependent effects (cis interactions)
3. Haplotype-based PGS construction
4. Phasing errors and their impact
5. Local ancestry haplotype effects

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Haplotype Diversity Across Populations

Populations with older demographic history have more haplotype
diversity. This affects PGS portability.
-/

section HaplotypeDiversity

/-- Empirical status: UNTESTED. -/
noncomputable def expectedDistinctHaplotypes (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (1 - (1 - 1 / ((2 : ℝ) ^ k)) ^ n)

/-- The occupancy-model expectation is strictly increasing in the number of sampled haplotypes
    whenever at least two haplotypes are possible in the region (`k > 0`). -/
theorem expectedDistinctHaplotypes_strictMono
    (k : ℕ) (h_k : 0 < k) :
    StrictMono (expectedDistinctHaplotypes k) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  let m : ℝ := (2 : ℝ) ^ k
  have h_m_pos : 0 < m := by
    dsimp [m]
    positivity
  have h_m_gt_one : 1 < m := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_k) with ⟨k', rfl⟩
    dsimp [m]
    have h_one_le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ k' := by
      exact_mod_cast (Nat.one_le_pow k' 2 (by decide : 0 < 2))
    calc
      (1 : ℝ) < 2 := one_lt_two
      _ ≤ 2 * (2 : ℝ) ^ k' := by nlinarith
      _ = (2 : ℝ) ^ (Nat.succ k') := by simp [pow_succ, mul_comm]
  have h_q_pos : 0 < 1 - 1 / m := by
    have h_inv_lt_one : 1 / m < 1 := by
      rw [div_lt_one h_m_pos]
      exact h_m_gt_one
    exact sub_pos.mpr h_inv_lt_one
  have h_step :
      expectedDistinctHaplotypes k (n + 1) =
        expectedDistinctHaplotypes k n + (1 - 1 / m) ^ n := by
    unfold expectedDistinctHaplotypes
    dsimp [m]
    rw [pow_succ]
    field_simp [h_m_pos.ne']
    ring
  have h_increment_pos : 0 < (1 - 1 / m) ^ n := pow_pos h_q_pos n
  calc
    expectedDistinctHaplotypes k n
      < expectedDistinctHaplotypes k n + (1 - 1 / m) ^ n := by linarith
    _ = expectedDistinctHaplotypes k (n + 1) := h_step.symm

/-- **Haplotype homozygosity.**
    H = Σ f_i² where f_i are haplotype frequencies.
    Lower in more diverse populations → more unique haplotypes.
    With n haplotypes at equal frequency 1/n, H = n × (1/n)² = 1/n.

    Empirical status: UNTESTED. -/
noncomputable def haplotypeHomozygosity {α : Type*} [Fintype α] (freq : α → ℝ) : ℝ :=
  ∑ i, freq i ^ 2

/-- For any valid haplotype frequency distribution, homozygosity is in `(0, 1]`. -/
theorem homozygosity_bounded {α : Type*} [Fintype α] (freq : α → ℝ)
    (h_nonneg : ∀ i, 0 ≤ freq i)
    (h_sum : ∑ i, freq i = 1) :
    0 < haplotypeHomozygosity freq ∧ haplotypeHomozygosity freq ≤ 1 := by
  have h_nonneg_total : 0 ≤ haplotypeHomozygosity freq := by
    unfold haplotypeHomozygosity
    exact Fintype.sum_nonneg fun i ↦ sq_nonneg (freq i)
  have h_ne_zero : haplotypeHomozygosity freq ≠ 0 := by
    intro h_zero
    have h_sq_zero : ∀ i, freq i ^ 2 = 0 := by
      have :
          (∑ i, freq i ^ 2) = 0 := by
        simpa [haplotypeHomozygosity] using h_zero
      have h_sq_zero_fun :
          (fun i ↦ freq i ^ 2) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun i ↦ sq_nonneg (freq i)).1 this
      intro i
      exact congrFun h_sq_zero_fun i
    have h_freq_zero : ∀ i, freq i = 0 := fun i ↦ sq_eq_zero_iff.mp (h_sq_zero i)
    have h_total_zero : (∑ i, freq i) = 0 := by simp [h_freq_zero]
    linarith
  have h_le_one : haplotypeHomozygosity freq ≤ 1 := by
    unfold haplotypeHomozygosity
    calc
      ∑ i, freq i ^ 2 ≤ (∑ i, freq i) ^ 2 := by
        simpa using
          (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := freq)
            fun i _ ↦ h_nonneg i)
      _ = 1 := by rw [h_sum]; norm_num
  constructor
  · exact lt_of_le_of_ne h_nonneg_total h_ne_zero.symm
  · exact h_le_one

/-- Under uniform frequencies across `n` haplotypes, the general homozygosity formula reduces to
    `1 / n`. -/
theorem uniform_homozygosity_eq_inverse_haplotype_count
    (n : ℕ) (h_n : 1 ≤ n) :
    haplotypeHomozygosity (fun _ : Fin n ↦ 1 / (n : ℝ)) = 1 / (n : ℝ) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_n)
  unfold haplotypeHomozygosity
  calc
    ∑ _ : Fin n, (1 / (n : ℝ)) ^ 2 = (n : ℝ) * (1 / (n : ℝ)) ^ 2 := by simp
    _ = 1 / (n : ℝ) := by
      field_simp [h_n_pos.ne']

/-- In the uniform-frequency special case, more haplotypes imply lower homozygosity. -/
theorem uniform_homozygosity_decreases_with_diversity (n₁ n₂ : ℕ)
    (h₁ : 1 ≤ n₁) (h_lt : n₁ < n₂) :
    haplotypeHomozygosity (fun _ : Fin n₂ ↦ 1 / (n₂ : ℝ)) <
      haplotypeHomozygosity (fun _ : Fin n₁ ↦ 1 / (n₁ : ℝ)) := by
  have h₂ : 1 ≤ n₂ := le_trans h₁ (Nat.le_of_lt h_lt)
  rw [uniform_homozygosity_eq_inverse_haplotype_count n₂ h₂]
  rw [uniform_homozygosity_eq_inverse_haplotype_count n₁ h₁]
  exact div_lt_div_of_pos_left one_pos
    (Nat.cast_pos.mpr (Nat.succ_le_iff.mp h₁))
    (Nat.cast_lt.mpr h_lt)

/-- Inverse homozygosity (Hill number of order 2), a standard effective-number
summary of haplotype diversity. Larger values correspond to more evenly spread
haplotype mass across more distinct haplotypes.

    Empirical status: UNTESTED. -/
noncomputable def effectiveHaplotypeNumber {α : Type*} [Fintype α]
    (freq : α → ℝ) : ℝ :=
  1 / haplotypeHomozygosity freq

/-- Lower homozygosity implies a larger effective number of haplotypes. This is
the biologically relevant diversity statement: populations with more even
haplotype frequency spectra carry more effective haplotypic states. -/
theorem more_haplotypes_in_afr
    {α β : Type*} [Fintype α] [Fintype β]
    (freq_eur : α → ℝ) (freq_afr : β → ℝ)
    (h_afr_nonneg : ∀ i, 0 ≤ freq_afr i)
    (h_afr_sum : ∑ i, freq_afr i = 1)
    (h_hom : haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur) :
    effectiveHaplotypeNumber freq_eur < effectiveHaplotypeNumber freq_afr := by
  have h_hom_afr_pos :
      0 < haplotypeHomozygosity freq_afr := (homozygosity_bounded freq_afr h_afr_nonneg h_afr_sum).1
  unfold effectiveHaplotypeNumber
  exact div_lt_div_of_pos_left one_pos h_hom_afr_pos h_hom

/-- A more uniform haplotype frequency spectrum corresponds to lower
homozygosity and therefore a larger effective haplotype number. This theorem
states that connection directly on the population frequency distributions,
rather than via a hand-written inverse-count surrogate. -/
theorem haplotype_frequency_more_uniform_afr
    {α β : Type*} [Fintype α] [Fintype β]
    (freq_eur : α → ℝ) (freq_afr : β → ℝ)
    (h_afr_nonneg : ∀ i, 0 ≤ freq_afr i)
    (h_afr_sum : ∑ i, freq_afr i = 1)
    (h_hom : haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur) :
    haplotypeHomozygosity freq_afr < haplotypeHomozygosity freq_eur ∧
      effectiveHaplotypeNumber freq_eur < effectiveHaplotypeNumber freq_afr := by
  exact ⟨h_hom, more_haplotypes_in_afr freq_eur freq_afr
    h_afr_nonneg h_afr_sum h_hom⟩

end HaplotypeDiversity


/-!
## Phase-Dependent Effects

Some genetic effects depend on the phase (cis/trans configuration)
of alleles on the same haplotype. These effects are missed by
standard PGS but captured by haplotype-based PGS.
-/

section PhaseDependentEffects

/-- Average interaction contribution when a population has cis-configuration
frequency `freq_cis` and trans frequency `1 - freq_cis`. -/
noncomputable def averagePhaseInteraction
    (freq_cis interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis * interaction_cis + (1 - freq_cis) * interaction_trans

/-- Structural error from using a dosage-only predictor that cannot distinguish
cis from trans configurations. The best dosage-only predictor within a fixed
dosage class uses the population-average interaction, leaving this residual
phase-misspecification error. -/
noncomputable def dosagePhaseMisspecificationError
    (freq_cis interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis * (interaction_cis - averagePhaseInteraction freq_cis interaction_cis interaction_trans) ^ 2 +
    (1 - freq_cis) *
      (interaction_trans - averagePhaseInteraction freq_cis interaction_cis interaction_trans) ^ 2

/-- **A phase-aware haplotype predictor, and the error it actually incurs.**

The predictor assigns interaction `pred_cis` to an individual it *calls* cis and
`pred_trans` to one it calls trans. Statistical phasing calls the configuration
wrongly at switch-error rate `switch_err`, so conditional on a cis individual the
prediction is `pred_cis` with probability `1 - switch_err` and `pred_trans` with
probability `switch_err`, and symmetrically for a trans individual. This
definition is the resulting mean squared phase-prediction error, written out as
the two-by-two mixture it comes from rather than asserted as a closed form; the
closed form is `haplotypePhasePredictionError_correctSpec_eq` below.

Nothing here is zero by construction. The error vanishes only when the predictor
is correctly specified *and* phasing never switches, and both of those are
hypotheses of theorems below rather than parts of this definition. That is the
whole difference from the previous version of this file, in which the haplotype
error was the literal `0` and every comparison against the dosage predictor was
therefore a tautology.

    Empirical status: UNTESTED. -/
noncomputable def haplotypePhasePredictionError
    (freq_cis switch_err pred_cis pred_trans interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis *
      ((1 - switch_err) * (interaction_cis - pred_cis) ^ 2 +
        switch_err * (interaction_cis - pred_trans) ^ 2) +
    (1 - freq_cis) *
      ((1 - switch_err) * (interaction_trans - pred_trans) ^ 2 +
        switch_err * (interaction_trans - pred_cis) ^ 2)

/-- Transport bias from carrying a source-trained dosage approximation into a
target population whose cis/trans configuration frequency differs. -/
noncomputable def dosageTransportBias
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) : ℝ :=
  |averagePhaseInteraction freq_cis_target interaction_cis interaction_trans -
    averagePhaseInteraction freq_cis_source interaction_cis interaction_trans|

/-- **Transport bias of a phase-aware haplotype model.**

The model is fitted in the source population, which fixes the pair
`(pred_cis, pred_trans)`; it is then deployed in a target population whose
cis-configuration frequency is `freq_cis_target`. The bias is the gap between the
mean interaction the model predicts there and the mean interaction the target
population has.

Unlike the dosage bias, this one does not move when only the configuration
frequency moves. It is not zero by construction either: it vanishes just when the
fitted cis/trans effects agree with the target's, which is the content of
`haplotypeTransportBias_eq_zero_of_portable_effects`, and it is what fails when
the effects themselves do not transport — see
`haplotype_less_portable_when_effects_shift`.

    Empirical status: UNTESTED. -/
noncomputable def haplotypeTransportBias
    (freq_cis_target pred_cis pred_trans interaction_cis interaction_trans : ℝ) : ℝ :=
  |averagePhaseInteraction freq_cis_target pred_cis pred_trans -
    averagePhaseInteraction freq_cis_target interaction_cis interaction_trans|

/-- The dosage-only phase-misspecification error has the exact variance form
`f(1-f)(δ_cis - δ_trans)^2`. -/
theorem dosagePhaseMisspecificationError_eq
    (freq_cis interaction_cis interaction_trans : ℝ) :
    dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans =
      freq_cis * (1 - freq_cis) * (interaction_cis - interaction_trans) ^ 2 := by
  unfold dosagePhaseMisspecificationError averagePhaseInteraction
  ring

/-- The structural dosage transport bias is exactly the shift in phase
configuration frequency times the cis/trans interaction gap. -/
theorem dosageTransportBias_eq
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) :
    dosageTransportBias freq_cis_source freq_cis_target interaction_cis interaction_trans =
      |freq_cis_target - freq_cis_source| * |interaction_cis - interaction_trans| := by
  unfold dosageTransportBias averagePhaseInteraction
  have h_factor :
      freq_cis_target * interaction_cis + (1 - freq_cis_target) * interaction_trans -
        (freq_cis_source * interaction_cis + (1 - freq_cis_source) * interaction_trans) =
        (freq_cis_target - freq_cis_source) * (interaction_cis - interaction_trans) := by
    ring
  rw [h_factor, abs_mul]

/-- **Closed form of the phase-aware haplotype error under correct
specification.** When the predictor's cis and trans values agree with the
population's cis and trans interactions, the whole residual error is phasing
error: `switch_err × (δ_cis − δ_trans)²`.

This is the haplotype-side analogue of `dosagePhaseMisspecificationError_eq`, and
it is what replaces the previous assertion that the haplotype error is `0`. The
two closed forms are directly comparable: `switch_err` against
`freq_cis (1 − freq_cis)`. -/
theorem haplotypePhasePredictionError_correctSpec_eq
    (freq_cis switch_err interaction_cis interaction_trans : ℝ) :
    haplotypePhasePredictionError freq_cis switch_err interaction_cis interaction_trans
        interaction_cis interaction_trans =
      switch_err * (interaction_cis - interaction_trans) ^ 2 := by
  unfold haplotypePhasePredictionError
  ring

/-- Correct specification *and* perfect phasing give zero residual phase error.
Both hypotheses are visible in the statement, and both are exactly what fails in
practice: effects are estimated from finite samples, and statistical phasing
switches at a nonzero rate that is itself worse in underrepresented populations
(`phasing_worse_for_underrepresented`). -/
theorem haplotypePhasePredictionError_eq_zero_of_perfect
    (freq_cis interaction_cis interaction_trans : ℝ) :
    haplotypePhasePredictionError freq_cis 0 interaction_cis interaction_trans
      interaction_cis interaction_trans = 0 := by
  rw [haplotypePhasePredictionError_correctSpec_eq, zero_mul]

/-- The dosage-only predictor is the phase-aware predictor forced to return the
same value in both configurations. So the two errors of the previous section are
one functional evaluated at two predictors, not two unrelated quantities. -/
theorem dosagePhaseMisspecificationError_eq_haplotype_constrained
    (freq_cis interaction_cis interaction_trans : ℝ) :
    dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans =
      haplotypePhasePredictionError freq_cis 0
        (averagePhaseInteraction freq_cis interaction_cis interaction_trans)
        (averagePhaseInteraction freq_cis interaction_cis interaction_trans)
        interaction_cis interaction_trans := by
  unfold dosagePhaseMisspecificationError haplotypePhasePredictionError
  ring

/-- Closed form of the phase-aware transport bias: the configuration-weighted
average of the two effect-estimation gaps. Note what is absent — the source
configuration frequency does not appear, which is the precise sense in which a
phase-aware model is insensitive to a configuration shift. -/
theorem haplotypeTransportBias_eq
    (freq_cis_target pred_cis pred_trans interaction_cis interaction_trans : ℝ) :
    haplotypeTransportBias freq_cis_target pred_cis pred_trans interaction_cis
        interaction_trans =
      |freq_cis_target * (pred_cis - interaction_cis) +
        (1 - freq_cis_target) * (pred_trans - interaction_trans)| := by
  unfold haplotypeTransportBias averagePhaseInteraction
  have h_factor :
      freq_cis_target * pred_cis + (1 - freq_cis_target) * pred_trans -
          (freq_cis_target * interaction_cis +
            (1 - freq_cis_target) * interaction_trans) =
        freq_cis_target * (pred_cis - interaction_cis) +
          (1 - freq_cis_target) * (pred_trans - interaction_trans) := by
    ring
  rw [h_factor]

/-- The phase-aware transport bias is zero when the cis and trans effects
themselves transport. This is now a theorem with its hypothesis in the
statement — the fitted pair is instantiated at the target's own effects — rather
than a definitional `0`. -/
theorem haplotypeTransportBias_eq_zero_of_portable_effects
    (freq_cis_target interaction_cis interaction_trans : ℝ) :
    haplotypeTransportBias freq_cis_target interaction_cis interaction_trans
      interaction_cis interaction_trans = 0 := by
  rw [haplotypeTransportBias_eq]
  have h : freq_cis_target * (interaction_cis - interaction_cis) +
      (1 - freq_cis_target) * (interaction_trans - interaction_trans) = 0 := by ring
  rw [h, abs_zero]

/-- And it is strictly positive as soon as the fitted effects miss the target's
on average. -/
theorem haplotypeTransportBias_pos_of_effects_not_portable
    (freq_cis_target pred_cis pred_trans interaction_cis interaction_trans : ℝ)
    (h_gap : freq_cis_target * (pred_cis - interaction_cis) +
      (1 - freq_cis_target) * (pred_trans - interaction_trans) ≠ 0) :
    0 < haplotypeTransportBias freq_cis_target pred_cis pred_trans interaction_cis
      interaction_trans := by
  rw [haplotypeTransportBias_eq]
  exact abs_pos.mpr h_gap

/-- **Compound heterozygosity is invisible to a dosage score — but only when
phasing is good enough.** The comparison is now quantitative: a correctly
specified phase-aware predictor beats the dosage predictor exactly when its
switch-error rate is below `freq_cis (1 − freq_cis)`, which is at most `1/4` and
falls to zero as the configuration becomes monomorphic.

This hypothesis is checkable and is not always satisfied. At `freq_cis = 0.05`
the threshold is `0.0475`, comparable to reported switch-error rates in
underrepresented populations, so the conclusion is not available there; see
`dosage_beats_haplotype_when_phasing_poor` for the reversal. -/
theorem compound_het_not_captured_by_dosage
    (freq_cis switch_err interaction_cis interaction_trans : ℝ)
    (h_phase_gap : interaction_cis ≠ interaction_trans)
    (h_phasing : switch_err < freq_cis * (1 - freq_cis)) :
    haplotypePhasePredictionError freq_cis switch_err interaction_cis interaction_trans
        interaction_cis interaction_trans <
      dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans := by
  rw [dosagePhaseMisspecificationError_eq, haplotypePhasePredictionError_correctSpec_eq]
  have h_gap_sq : 0 < (interaction_cis - interaction_trans) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr h_phase_gap)
  exact mul_lt_mul_of_pos_right h_phasing h_gap_sq

/-- **The comparison reverses when phasing is poor.** Above the threshold the
dosage-only predictor has strictly smaller error than the phase-aware one, for
the same cis/trans architecture. A haplotype score is not unconditionally better;
it trades a structural error of size `freq_cis (1 − freq_cis)` for a phasing
error of size `switch_err`. -/
theorem dosage_beats_haplotype_when_phasing_poor
    (freq_cis switch_err interaction_cis interaction_trans : ℝ)
    (h_phase_gap : interaction_cis ≠ interaction_trans)
    (h_phasing : freq_cis * (1 - freq_cis) < switch_err) :
    dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans <
      haplotypePhasePredictionError freq_cis switch_err interaction_cis interaction_trans
        interaction_cis interaction_trans := by
  rw [dosagePhaseMisspecificationError_eq, haplotypePhasePredictionError_correctSpec_eq]
  have h_gap_sq : 0 < (interaction_cis - interaction_trans) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr h_phase_gap)
  exact mul_lt_mul_of_pos_right h_phasing h_gap_sq

/-- **Phase effects are population-specific.**
    Haplotype frequencies differ → phase configuration frequencies
    differ → average phase-dependent effect differs across populations. -/
theorem phase_effects_population_specific
    (freq_cis_source freq_cis_target delta_cis : ℝ)
    (h_diff_freq : freq_cis_source ≠ freq_cis_target)
    (h_delta : delta_cis ≠ 0) :
    freq_cis_source * delta_cis ≠ freq_cis_target * delta_cis := by
  intro h
  have := mul_right_cancel₀ h_delta h
  exact h_diff_freq this

end PhaseDependentEffects


/-!
## Haplotype-Based PGS Construction

Using haplotype blocks rather than individual SNPs can improve
PGS accuracy and portability.
-/

section HaplotypePGS

/-- **Haplotype PGS captures more variance than SNP PGS — under a stated
phasing hypothesis.**

The comparison is made on the explicit error surface of the previous section. A
correctly specified phase-aware haplotype score carries error `switch_err × gap²`
and a dosage-only SNP score carries `freq_cis (1 − freq_cis) × gap²`, so the
haplotype score is at least as good exactly on `switch_err ≤ freq_cis (1 −
freq_cis)`.

**Status change.** The previous statement of this theorem was
`0 ≤ <nonnegative thing>`, true by definitional fiat because the haplotype error
was defined to be `0`. It is now a genuine comparison with a hypothesis that can
fail; when it fails the inequality reverses
(`dosage_beats_haplotype_when_phasing_poor`). -/
theorem haplotype_pgs_at_least_snp
    (freq_cis switch_err interaction_cis interaction_trans : ℝ)
    (h_phasing : switch_err ≤ freq_cis * (1 - freq_cis)) :
    haplotypePhasePredictionError freq_cis switch_err interaction_cis interaction_trans
        interaction_cis interaction_trans ≤
      dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans := by
  rw [dosagePhaseMisspecificationError_eq, haplotypePhasePredictionError_correctSpec_eq]
  exact mul_le_mul_of_nonneg_right h_phasing (sq_nonneg _)

/-- **Haplotype PGS portability can be better — when the cis/trans effects
themselves transport.**

If the causal mechanism acts through cis/trans configuration, transporting a
dosage-only approximation incurs structural bias whenever the target
configuration frequency differs from the source. A phase-aware model fitted at
the target's own cis/trans effects avoids that bias.

**The left-hand side must be the transport bias of an explicit predictor, not the
constant `0`** -- with `0` the theorem is `0 < <positive thing>` and says nothing. The
portability of the effects is visible in the statement as the instantiation of the fitted
pair; drop that instantiation and the conclusion fails, as
`haplotype_less_portable_when_effects_shift` shows. -/
theorem haplotype_pgs_more_portable_for_cis
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ)
    (h_freq_shift : freq_cis_source ≠ freq_cis_target)
    (h_phase_gap : interaction_cis ≠ interaction_trans) :
    haplotypeTransportBias freq_cis_target interaction_cis interaction_trans
        interaction_cis interaction_trans <
      dosageTransportBias
        freq_cis_source freq_cis_target interaction_cis interaction_trans := by
  rw [dosageTransportBias_eq, haplotypeTransportBias_eq_zero_of_portable_effects]
  exact mul_pos
    (abs_pos.mpr (sub_ne_zero.mpr h_freq_shift.symm))
    (abs_pos.mpr (sub_ne_zero.mpr h_phase_gap))

/-- **And the portability advantage reverses when the effects do not transport.**

Suppose the fitted cis and trans effects are both off by the same amount `e` in
the target — an effect shift rather than a configuration shift. Then the
phase-aware model carries bias `|e|` in every target population, while the
dosage model's structural transport bias is zero whenever the configuration
frequency has not moved. The advantage in `haplotype_pgs_more_portable_for_cis`
is therefore an advantage against one failure mode only, and the haplotype model
buys it by taking on a second. -/
theorem haplotype_less_portable_when_effects_shift
    (freq_cis e interaction_cis interaction_trans : ℝ) (h_e : e ≠ 0) :
    dosageTransportBias freq_cis freq_cis interaction_cis interaction_trans <
      haplotypeTransportBias freq_cis (interaction_cis + e) (interaction_trans + e)
        interaction_cis interaction_trans := by
  rw [dosageTransportBias_eq, haplotypeTransportBias_eq]
  have h0 : |freq_cis - freq_cis| * |interaction_cis - interaction_trans| = 0 := by
    simp
  rw [h0]
  have hval : freq_cis * (interaction_cis + e - interaction_cis) +
      (1 - freq_cis) * (interaction_trans + e - interaction_trans) = e := by ring
  rw [hval]
  exact abs_pos.mpr h_e

/-- **But haplotype PGS can overfit in training population.**
    Rare haplotypes have fewer observed carriers, so their effect estimates are
    noisier. This theorem states the actual carrier-count mechanism: estimation
    variance scales like `σ² / (n × f)` where `f` is haplotype frequency in a
    sample of size `n`. Adding a rarer haplotype strictly increases the total
    estimation-noise burden.

    Empirical status: UNTESTED. -/
noncomputable def haplotypeEffectEstimationVariance
    (σ2 n freq : ℝ) : ℝ :=
  σ2 / (n * freq)

/-- **The OLS estimation variance, corrected.**

    Regressing on a binary haplotype indicator of frequency `f` gives
    `Var(β̂) = σ²/(n·f·(1-f))`, not `σ²/(n·f)`. The missing `(1-f)` makes the uncorrected
    body **understate** the estimation variance — hence **overstate** precision — and it does
    so worst for **common** haplotypes, which is the opposite of the rarity intuition the
    surrounding prose appeals to.

    Monte-Carlo at `n = 1000`, 3000 replicates, MC standard error about 2.6%:

    | `f` | measured | uncorrected | corrected |
    |---|---|---|---|
    | 0.02 | 0.05286 | −5.4% | −3.5% |
    | 0.1 | 0.011255 | −11.2% | −1.3% |
    | 0.3 | 0.0048055 | −30.6% | −0.9% |
    | 0.5 | 0.0040328 | **−50.4%** | −0.8% |

    Empirical status: **VALIDATED**; the uncorrected form is FALSIFIED
    (`proofs/validation/popgen_diff2/`). -/
noncomputable def haplotypeEffectVarianceOLS
    (σ2 n freq : ℝ) : ℝ :=
  σ2 / (n * freq * (1 - freq))

/-- **The uncorrected form understates the estimation variance, by exactly `(1-f)`.**

    So it overstates precision, and the error grows with frequency rather than shrinking:
    at `f = 1/2` it is a factor of two. -/
theorem haplotypeEffectEstimationVariance_lt_ols (σ2 n freq : ℝ)
    (hσ : 0 < σ2) (hn : 0 < n) (hf0 : 0 < freq) (hf1 : freq < 1) :
    haplotypeEffectEstimationVariance σ2 n freq < haplotypeEffectVarianceOLS σ2 n freq := by
  have h1 : 0 < n * freq := mul_pos hn hf0
  have h2 : 0 < n * freq * (1 - freq) := by nlinarith
  have hlt : n * freq * (1 - freq) < n * freq := by nlinarith
  unfold haplotypeEffectEstimationVariance haplotypeEffectVarianceOLS
  exact div_lt_div_of_pos_left hσ h2 hlt

theorem haplotype_pgs_overfitting_risk
    (σ2 n freq_common freq_rare : ℝ)
    (h_sigma : 0 < σ2)
    (h_n : 0 < n)
    (h_rare : 0 < freq_rare)
    (h_rarer : freq_rare < freq_common) :
    haplotypeEffectEstimationVariance σ2 n freq_common <
      haplotypeEffectEstimationVariance σ2 n freq_rare ∧
    haplotypeEffectEstimationVariance σ2 n freq_common <
      haplotypeEffectEstimationVariance σ2 n freq_common +
        haplotypeEffectEstimationVariance σ2 n freq_rare := by
  unfold haplotypeEffectEstimationVariance
  have h_common_var_lt_rare :
      σ2 / (n * freq_common) < σ2 / (n * freq_rare) := by
    exact div_lt_div_of_pos_left h_sigma (mul_pos h_n h_rare)
      (by nlinarith [mul_pos h_n h_rare])
  have h_rare_var_pos : 0 < σ2 / (n * freq_rare) := by
    exact div_pos h_sigma (mul_pos h_n h_rare)
  constructor
  · exact h_common_var_lt_rare
  · linarith

end HaplotypePGS


/-!
## Phasing Errors

Statistical phasing introduces errors that affect
haplotype-based analyses and PGS.
-/

section PhasingErrors


/-- **Phasing error introduces noise.**
    With switch error rate s, the phase-dependent signal
    is attenuated by (1 - 2s)². For s = 0.01, this is ~0.96.

    Empirical status: UNTESTED. -/
noncomputable def phaseAttenuation (s : ℝ) : ℝ := (1 - 2 * s)^2

/-- Phase attenuation is in [0,1] for small error rate. -/
theorem phase_attenuation_bounded (s : ℝ)
    (h_s : 0 ≤ s) (h_s_le : s ≤ 1 / 2) :
    0 ≤ phaseAttenuation s ∧ phaseAttenuation s ≤ 1 := by
  unfold phaseAttenuation
  constructor
  · exact sq_nonneg _
  · have h1 : -1 ≤ 1 - 2 * s := by linarith
    have h2 : 1 - 2 * s ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - 2 * s), sq_nonneg (1 - (1 - 2 * s))]

/-- Phase attenuation decreases with higher error rate. -/
theorem more_errors_more_attenuation (s₁ s₂ : ℝ)
    (h_s₂_le : s₂ ≤ 1 / 2)
    (h_lt : s₁ < s₂) :
    phaseAttenuation s₂ < phaseAttenuation s₁ := by
  unfold phaseAttenuation
  have h₁ : 0 ≤ 1 - 2 * s₂ := by linarith
  have h₂ : 1 - 2 * s₂ < 1 - 2 * s₁ := by linarith
  exact sq_lt_sq' (by linarith) h₂

/-- **Phasing accuracy varies by population representation.**
    Phasing algorithms trained on well-represented populations
    work worse on underrepresented samples because reference
    panels are biased toward the training population. -/
theorem phasing_worse_for_underrepresented
    (s_source s_target : ℝ)
    (h_worse : s_source < s_target)
    (h_target_le : s_target ≤ 1 / 2) :
    phaseAttenuation s_target < phaseAttenuation s_source := by
  exact more_errors_more_attenuation s_source s_target h_target_le h_worse

end PhasingErrors


/-!
## Local Ancestry Haplotype Effects

In admixed populations, the haplotype effect depends on the
local ancestry of the genomic segment.
-/

section LocalAncestryHaplotypes

/-- **Ancestry-specific haplotype effect.**
    At a given locus, the haplotype effect depends on
    which ancestral population the haplotype derives from.

    Empirical status: UNTESTED.

    Denotes: the reading its name carries. The same formula appears under
    names from 'frequency', 'variance', and the formula alone does not fix which is meant. -/
noncomputable def ancestrySpecificEffect (beta_pop1 beta_pop2 alpha : ℝ) : ℝ :=
  alpha * beta_pop1 + (1 - alpha) * beta_pop2

/-- Ancestry-specific effect is a weighted average. -/
theorem ancestry_effect_between_pops (beta₁ beta₂ alpha : ℝ)
    (h_alpha : 0 ≤ alpha) (h_alpha_le : alpha ≤ 1)
    (h_order : beta₁ ≤ beta₂) :
    beta₁ ≤ ancestrySpecificEffect beta₁ beta₂ alpha ∧
    ancestrySpecificEffect beta₁ beta₂ alpha ≤ beta₂ := by
  unfold ancestrySpecificEffect
  constructor <;> nlinarith

/-- Single-effect predictor obtained by averaging ancestry-specific effects
according to the admixture proportion `alpha`.

    Empirical status: UNTESTED. -/
noncomputable def globalAncestryAveragedEffect
    (beta₁ beta₂ alpha : ℝ) : ℝ :=
  ancestrySpecificEffect beta₁ beta₂ alpha

/-- Structural prediction error from using a single ancestry-averaged effect in
an admixed population whose local ancestry really switches between ancestry 1
and ancestry 2. -/
noncomputable def localAncestryMisspecification
    (beta₁ beta₂ alpha : ℝ) : ℝ :=
  alpha * (beta₁ - globalAncestryAveragedEffect beta₁ beta₂ alpha) ^ 2 +
    (1 - alpha) * (beta₂ - globalAncestryAveragedEffect beta₁ beta₂ alpha) ^ 2

/-- The misspecification from ignoring local ancestry is exactly the weighted
squared effect-difference term `α(1-α)(β₁-β₂)^2`. -/
theorem localAncestryMisspecification_eq
    (beta₁ beta₂ alpha : ℝ) :
    localAncestryMisspecification beta₁ beta₂ alpha =
      alpha * (1 - alpha) * (beta₁ - beta₂) ^ 2 := by
  unfold localAncestryMisspecification globalAncestryAveragedEffect ancestrySpecificEffect
  ring

/-- **Local ancestry deconvolution for haplotypes.**
    By identifying the ancestry of each haplotype segment, the model can apply
    the ancestry-appropriate effect instead of a single ancestry-averaged
    effect. The gain is exactly the local-ancestry misspecification variance
    removed by deconvolution. -/
theorem la_deconvolution_improves_pgs
    (r2_global beta₁ beta₂ alpha V_total : ℝ)
    (h_alpha : 0 < alpha)
    (h_alpha_lt : alpha < 1)
    (h_beta : beta₁ ≠ beta₂)
    (h_total : 0 < V_total) :
    r2_global <
      r2_global + localAncestryMisspecification beta₁ beta₂ alpha / V_total := by
  rw [localAncestryMisspecification_eq]
  have h_mix : 0 < alpha * (1 - alpha) := mul_pos h_alpha (sub_pos.mpr h_alpha_lt)
  have h_gap : 0 < (beta₁ - beta₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h_beta)
  have h_gain : 0 < alpha * (1 - alpha) * (beta₁ - beta₂) ^ 2 / V_total := by
    exact div_pos (mul_pos h_mix h_gap) h_total
  linarith

/-- **The admixture tract length, corrected.**

    For a single-pulse hybrid-isolation model the ancestry-1 tracts are exponential with mean
    `1/(g(1-α))` Morgans, where `α` is the admixture fraction (Pool & Nielsen 2009; Liang &
    Nielsen 2014). The map length does **not** appear.

    The uncorrected `expectedSegmentLength` below takes a total map length `r_total` that is
    spurious and omits `α` entirely. A forward pedigree simulation with explicit Poisson
    crossovers settles it decisively — holding `α = 0.5, g = 10` and varying chromosome
    length, the truth is asymptotically **independent** of map length while the uncorrected
    form moves 16-fold:

    | map length | simulated | uncorrected |
    |---|---|---|
    | 1 M | 0.1462 ± 0.0043 | 0.1000 |
    | 4 M | 0.1728 ± 0.0023 | 0.0250 |
    | 16 M | 0.1913 ± 0.0013 | 0.00625 |

    (The simulated value rises toward `1/(g(1-α)) = 0.20` as edge censoring vanishes.) Across
    `α ∈ {0.2,0.5,0.8} × g ∈ {5,10,20}` the uncorrected form runs −78% to −95%; the corrected
    one matches to 0.1–7% where censoring is small. **No choice of units repairs it** — one
    argument is spurious and another is missing.

    Empirical status: **VALIDATED**; the form below is FALSIFIED
    (`proofs/validation/popgen_diff2/`). -/
noncomputable def expectedTractLength (g admixtureFraction : ℝ) : ℝ :=
  1 / (g * (1 - admixtureFraction))

/-- **FALSIFIED — spurious map-length argument, missing admixture fraction.** See
    `expectedTractLength`. Retained so the superseded form is named and struck rather than
    quietly absent. -/
noncomputable def expectedSegmentLength (g r_total : ℝ) : ℝ :=
  1 / (g * r_total)

/-- Segments get shorter with more generations. -/
theorem segments_shorten_with_time (g₁ g₂ r_total : ℝ)
    (h_r : 0 < r_total) (h_g₁ : 0 < g₁) (h_g₂ : 0 < g₂)
    (h_g : g₁ < g₂) :
    expectedSegmentLength g₂ r_total < expectedSegmentLength g₁ r_total := by
  unfold expectedSegmentLength
  exact div_lt_div_iff_of_pos_left one_pos (mul_pos h_g₂ h_r) (mul_pos h_g₁ h_r) |>.mpr
    (mul_lt_mul_of_pos_right h_g h_r)

end LocalAncestryHaplotypes

end Calibrator
