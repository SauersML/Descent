/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Descent.Program.OpenQuestions
import Descent.Core.Fst

namespace Descent.PopGen

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

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat haplotype structure, phasing or phase-dependent effects. Sources
for individual results, where they exist, are cited at those results.
-/


/-!
## Haplotype Diversity Across Populations

Populations with older demographic history have more haplotype
diversity. This affects PGS portability.
-/

section HaplotypeDiversity

/-- **Expected distinct haplotypes under UNIFORM occupancy**: `k` sites give `2^k` possible
haplotypes, each equally frequent, and `n` chromosomes are drawn independently.

    The name carries the assumption because the formula cannot carry the alternative. The
    observable "expected number of distinct haplotypes in a `k`-SNP window from `n` sampled
    chromosomes" depends on the haplotype frequency spectrum, hence on effective size,
    recombination and demographic history, and this signature takes none of them: it is
    demography-free by construction. So it cannot support the section's opening remark that
    populations with older demographic history carry more haplotype diversity — that statement
    is about a dependence this function does not have. `haplotypeHomozygosity` below takes the
    frequency vector and shows what the required input looks like.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk2.py`,
    `test_haplotype_occupancy`). Exact Monte Carlo over 40000 replicate draws:

      k    n      this def   simulated              sems
      4    10      7.60863   7.60513±0.00527        0.67
      4    40     14.78948   14.79735±0.00470       1.67
      6    50     34.87883   34.86908±0.01163       0.84
      8   200    138.97383   138.98490±0.02325      0.48

    Power: the prediction spans 7.6 to 139.0, a factor of eighteen. -/
noncomputable def uniformOccupancyDistinctHaplotypes (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (1 - (1 - 1 / ((2 : ℝ) ^ k)) ^ n)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem uniformOccupancyDistinctHaplotypes_at_reference_point :
    uniformOccupancyDistinctHaplotypes 1 1 = 1 := by
  norm_num [uniformOccupancyDistinctHaplotypes]


/-- **A sample cannot show more distinct haplotypes than the window admits.** With `k` sites
there are `2^k` possible haplotypes, and the occupancy expectation stays below that ceiling
however many chromosomes are drawn. -/
theorem uniformOccupancyDistinctHaplotypes_le (k n : ℕ) :
    uniformOccupancyDistinctHaplotypes k n ≤ (2 : ℝ) ^ k := by
  unfold uniformOccupancyDistinctHaplotypes
  have hm : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hq : (0 : ℝ) ≤ (1 - 1 / (2 : ℝ) ^ k) ^ n := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one hm]
    exact one_le_pow₀ (by norm_num)
  nlinarith

/-- The occupancy-model expectation is strictly increasing in the number of sampled haplotypes
    whenever at least two haplotypes are possible in the region (`k > 0`). -/
theorem uniformOccupancyDistinctHaplotypes_strictMono
    (k : ℕ) (h_k : 0 < k) :
    StrictMono (uniformOccupancyDistinctHaplotypes k) := by
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
      uniformOccupancyDistinctHaplotypes k (n + 1) =
        uniformOccupancyDistinctHaplotypes k n + (1 - 1 / m) ^ n := by
    unfold uniformOccupancyDistinctHaplotypes
    dsimp [m]
    rw [pow_succ]
    field_simp [h_m_pos.ne']
    ring
  have h_increment_pos : 0 < (1 - 1 / m) ^ n := pow_pos h_q_pos n
  calc
    uniformOccupancyDistinctHaplotypes k n
      < uniformOccupancyDistinctHaplotypes k n + (1 - 1 / m) ^ n := by linarith
    _ = uniformOccupancyDistinctHaplotypes k (n + 1) := h_step.symm

/-- **Haplotype homozygosity.**
    H = Σ f_i² where f_i are haplotype frequencies.
    Lower in more diverse populations → more unique haplotypes.
    With n haplotypes at equal frequency 1/n, H = n × (1/n)² = 1/n.

    Regime: haplotypes drawn independently, so this is the identity-by-state
    match probability and not an identity-by-descent one.

    Empirical status: **VALIDATED** (`simcov/battery_bulk41.py`, `group_c`). The displayed
    formula follows algebraically from independence -- the probability that two draws match
    is the sum, over haplotypes, of the product of their two marginal probabilities -- and
    the design measures the LEFT-hand side of that statement without evaluating the right:
    a frequency vector is drawn from a Dirichlet, then 8×10⁶ independent PAIRS of haplotypes
    are drawn from it and the observable is the realised fraction of pairs that MATCH.

      k    conc   this body   realised match rate   sems
       4    0.4    0.49446         0.49454          0.42
       6    1.0    0.30011         0.29983          1.72
      10    0.3    0.22531         0.22542          0.77
       3    3.0    0.45615         0.45590          1.44

    Counting matches is an independent route to the sum of squares, which is what makes this
    a measurement rather than the same expression twice. The identity gate: the uniform
    reading `1/k` misses by up to 1383 sems, the complement `1 - ∑f²` by 3718, and `(∑f²)/k`
    by 2098. The positive control -- a UNIFORM frequency vector, where the match rate must
    be `1/k` -- passes at 1.19 sems. -/
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

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk2.py`,
    `test_haplotype_occupancy`). Against the inverse probability that two
    independent draws match, four million pairs per cell:

      frequencies       this def   simulated            sems
      uniform over 8     8.00000   8.00363±0.01059     0.34
      skewed             2.90909   2.90686±0.00201     1.11
      very skewed        1.22880   1.22869±0.00029     0.39

    Power: the prediction spans 1.229 to 8.000, and the skewed cells are what
    separate an inverse-Simpson reading from a plain type count. -/
noncomputable def effectiveHaplotypeNumber {α : Type*} [Fintype α]
    (freq : α → ℝ) : ℝ :=
  1 / haplotypeHomozygosity freq

/-- **effectiveHaplotypeNumber over an empty index, named.** With no haplotypes the homozygosity
is an empty sum, so its reciprocal divides by zero. Lean returns `0`: fewer than one effective
haplotype, a value the quantity cannot take, since an effective number is at least one whenever
any haplotype exists. Consumers must require a nonempty index. -/
theorem effectiveHaplotypeNumber_empty_panel_is_junk (freq : Fin 0 → ℝ) :
    effectiveHaplotypeNumber freq = 0 := by
  unfold effectiveHaplotypeNumber haplotypeHomozygosity
  simp

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
  Descent.Core.convexCombination freq_cis interaction_cis interaction_trans

/-! `averagePhaseInteraction` -- **Empirical status: VALIDATED**
(`simcov/battery_bulk43.py`, `group_c`). 3×10⁶ individuals, a fraction
`freq_cis` of them in cis; the observable is the realised mean interaction
across the population, which is exact and needs no modelling. Worst cell 1.41
sems at 0.05% relative.

Power: the UNWEIGHTED mean `(i_cis + i_trans)/2` rides on the same draws and is
FALSIFIED at 1299 sems (75% relative). The two coincide only at
`freq_cis = 1/2`, so the design sweeps across it -- 0.2, 0.35, 0.5, 0.8 -- and
one cell gives the two interactions OPPOSITE signs, where an unweighted average
lands on the wrong side of zero. Control: the realised cis fraction recovers
`freq_cis` on the same draws.

`haplotypeTransportBias`, the absolute gap between the predicted and true phase
averages, is measured on those same draws at worst 1.41 sems. Its relative
error reaches 100% in one cell, which is not a defect: that cell's true gap is
near zero, and a relative error against a vanishing denominator carries no
information. The absolute agreement is what the sems report. -/

/-- **A population entirely in cis carries the cis interaction.**

The weights sum to one by construction, so the average is an interpolation and the two endpoints
are what identify which. At `freq_cis = 1` the trans term drops out entirely; a body that
weighted the two configurations by anything other than their frequencies would still be an affine
combination and would fail here. This is also the reference the transport-bias definitions below
are differences of, so fixing it fixes what those differences measure. -/
theorem averagePhaseInteraction_all_cis (interaction_cis interaction_trans : ℝ) :
    averagePhaseInteraction 1 interaction_cis interaction_trans = interaction_cis := by
  unfold averagePhaseInteraction Descent.Core.convexCombination
  ring

/-- Structural error from using a dosage-only predictor that cannot distinguish
cis from trans configurations. The best dosage-only predictor within a fixed
dosage class uses the population-average interaction, leaving this residual
phase-misspecification error. -/
noncomputable def dosagePhaseMisspecificationError
    (freq_cis interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis *
      (interaction_cis - averagePhaseInteraction freq_cis interaction_cis interaction_trans) ^ 2 +
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
hypotheses of theorems below rather than parts of this definition. Defining the
haplotype error as the literal `0` instead would make every comparison against
the dosage predictor a tautology.

    Empirical status: **VALIDATED**
(`simcov/battery_bulk50.py`, `group_a`). 4×10⁶ individuals: true phase drawn at
rate `freq_cis`, a switch error drawn independently at rate `switch_err` that
flips which prediction is APPLIED, and the observable the realised mean squared
error. Worst cell 1.51 sems at 0.14% relative, with `switch_err` swept 0 to 0.25
and one design giving the two interactions opposite signs, where misreading
phase costs most.

Power, and the two confusions this shape invites, both rejected on the same
cells: dropping the switch channel entirely -- computing the error as if phase
were always read correctly -- misses by 1152 sems (83% relative); applying the
switch rate to the phase FREQUENCY rather than to the READ misses by 1174 sems
(85%). The second is the subtler error, because it produces a number of the
right magnitude that moves in the right direction with `switch_err`, and only
the two-sign design separates it cleanly.

The switch error acts on the READ, not on the truth: an individual in cis whose
phase is misread still HAS the cis interaction, and merely receives the trans
prediction. That is why the body pairs `interaction_cis` with `pred_trans` in
its switched branch rather than swapping both. Control: with no switch error
the counted cis fraction recovers `freq_cis`.

REBUILT AND RE-RUN, and the numbers above are superseded by these. The
battery this cites had never been committed: the verdict was real when it
was produced and no reader could check it, which is the same standing as no
verdict. `simcov/battery_bulk50.py` is now in the repository, was run against
the design described above, and its results are committed beside it (group_a).
MATCH at worst 1.49 sems (0.18% relative); dropping the switch channel and applying the
switch rate to the phase FREQUENCY are both FALSIFIED at 912 sems.
-/
noncomputable def haplotypePhasePredictionError
    (freq_cis switch_err pred_cis pred_trans interaction_cis interaction_trans : ℝ) : ℝ :=
  freq_cis *
      ((1 - switch_err) * (interaction_cis - pred_cis) ^ 2 +
        switch_err * (interaction_cis - pred_trans) ^ 2) +
    (1 - freq_cis) *
      ((1 - switch_err) * (interaction_trans - pred_trans) ^ 2 +
        switch_err * (interaction_trans - pred_cis) ^ 2)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem haplotypePhasePredictionError_at_reference_point :
    haplotypePhasePredictionError (1 / 3) (1 / 4) 0 1 2 3 = 55 / 12 := by
  norm_num [haplotypePhasePredictionError]


/-- Transport bias from carrying a source-trained dosage approximation into a
target population whose cis/trans configuration frequency differs. -/
noncomputable def dosageTransportBias
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) : ℝ :=
  |averagePhaseInteraction freq_cis_target interaction_cis interaction_trans -
    averagePhaseInteraction freq_cis_source interaction_cis interaction_trans|

/-- **The bias is bounded by the two phase interactions it compares.** The closed form below
holds for every positive multiple of this distance; the triangle bound does not, so it is what
fixes the multiple at one. -/
theorem dosageTransportBias_le_add_abs
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) :
    dosageTransportBias freq_cis_source freq_cis_target interaction_cis interaction_trans
      ≤ |averagePhaseInteraction freq_cis_target interaction_cis interaction_trans|
        + |averagePhaseInteraction freq_cis_source interaction_cis interaction_trans| := by
  unfold dosageTransportBias
  exact abs_sub _ _

/-- **Transport bias of a phase-aware haplotype model.**

The model is fitted in the source population, which fixes the pair
`(pred_cis, pred_trans)`; it is then deployed in a target population whose
cis-configuration frequency is `freq_cis_target`. The bias is the gap between the
mean interaction the model predicts there and the mean interaction the target
population has.

Unlike the dosage bias, this one does not move when only the configuration
frequency moves. It is not zero by construction either: it vanishes just when the
fitted cis/trans effects agree with the target's, which is the content of
`haplotypeTransportBias_of_matched_predictor`, and it is what fails when
the effects themselves do not transport — see
`haplotype_less_portable_when_effects_shift`.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body is the absolute gap between two
    evaluations of `averagePhaseInteraction` at the SAME configuration frequency, which is
    the DEFINITION of "the bias the fitted cis/trans pair carries into the target". No
    population can make that distance a different number once the four inputs are fixed.
    What is empirical is whether real cis and trans interaction effects transport -- a claim
    about the INPUTS `interaction_cis` and `interaction_trans` relative to `pred_cis` and
    `pred_trans` -- and `haplotypeTransportBias_of_matched_predictor` is the corpus saying
    exactly when this vanishes, which is algebra on that input rather than a measurement. -/
noncomputable def haplotypeTransportBias
    (freq_cis_target pred_cis pred_trans interaction_cis interaction_trans : ℝ) : ℝ :=
  |averagePhaseInteraction freq_cis_target pred_cis pred_trans -
    averagePhaseInteraction freq_cis_target interaction_cis interaction_trans|

/-- **A predictor that matches the interaction transports without bias.**

This is an identity about the bias, and it was named `_at_reference_point`, which
it is not: it states zero, so a competitor scaled by any `c` satisfies it too and
it pins no coefficient. Renamed rather than moved, because the fact is real and
worth having -- it is the zero of the bias, and the zero is where the definition
is anchored. What it is not is a reference evaluation, and
`haplotypeTransportBias_at_reference_point` below now supplies one. -/
theorem haplotypeTransportBias_of_matched_predictor
    (freq_cis_target interaction_cis interaction_trans : ℝ) :
    haplotypeTransportBias freq_cis_target interaction_cis interaction_trans
      interaction_cis interaction_trans = 0 := by
  unfold haplotypeTransportBias
  simp

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem haplotypeTransportBias_at_reference_point :
    haplotypeTransportBias (1 / 2) 1 1 0 0 = 1 := by
  unfold haplotypeTransportBias averagePhaseInteraction Descent.Core.convexCombination
  norm_num


-- **Predicting the true interaction leaves no transport bias** is stated once
-- by `haplotypeTransportBias_of_matched_predictor` above.

/-- The dosage-only phase-misspecification error has the exact variance form
`f(1-f)(δ_cis - δ_trans)^2`. -/
theorem dosagePhaseMisspecificationError_eq
    (freq_cis interaction_cis interaction_trans : ℝ) :
    dosagePhaseMisspecificationError freq_cis interaction_cis interaction_trans =
      freq_cis * (1 - freq_cis) * (interaction_cis - interaction_trans) ^ 2 := by
  unfold dosagePhaseMisspecificationError averagePhaseInteraction Descent.Core.convexCombination
  ring

/-- The structural dosage transport bias is exactly the shift in phase
configuration frequency times the cis/trans interaction gap. -/
theorem dosageTransportBias_eq
    (freq_cis_source freq_cis_target interaction_cis interaction_trans : ℝ) :
    dosageTransportBias freq_cis_source freq_cis_target interaction_cis interaction_trans =
      |freq_cis_target - freq_cis_source| * |interaction_cis - interaction_trans| := by
  unfold dosageTransportBias averagePhaseInteraction Descent.Core.convexCombination
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
  unfold haplotypeTransportBias averagePhaseInteraction Descent.Core.convexCombination
  have h_factor :
      freq_cis_target * pred_cis + (1 - freq_cis_target) * pred_trans -
          (freq_cis_target * interaction_cis +
            (1 - freq_cis_target) * interaction_trans) =
        freq_cis_target * (pred_cis - interaction_cis) +
          (1 - freq_cis_target) * (pred_trans - interaction_trans) := by
    ring
  rw [h_factor]

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

/-- Both error comparisons below reduce to this: the two closed forms differ only in a
leading coefficient, and the shared factor `(δ_cis - δ_trans) ^ 2` is positive exactly when
the two effects differ.  The comparison is therefore the coefficient comparison, in either
direction, and the argument is written once here rather than once per direction. -/
theorem mul_sq_sub_lt_of_lt_of_ne
    {coeffSmall coeffLarge effectCis effectTrans : ℝ}
    (h_coeff : coeffSmall < coeffLarge) (h_gap : effectCis ≠ effectTrans) :
    coeffSmall * (effectCis - effectTrans) ^ 2 <
      coeffLarge * (effectCis - effectTrans) ^ 2 :=
  mul_lt_mul_of_pos_right h_coeff (sq_pos_of_ne_zero (sub_ne_zero.mpr h_gap))

/-- **Compound heterozygosity is invisible to a dosage score — but only when
phasing is good enough.** The comparison is now quantitative: a correctly
specified phase-aware predictor beats the dosage predictor whenever its
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
  exact mul_sq_sub_lt_of_lt_of_ne h_phasing h_phase_gap

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
  exact mul_sq_sub_lt_of_lt_of_ne h_phasing h_phase_gap

/-- **Phase effects are population-specific.**
    Haplotype frequencies differ → phase configuration frequencies
    differ → average phase-dependent effect differs across populations. -/
theorem mul_ne_mul_right_of_ne_of_ne_zero
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
  rw [dosageTransportBias_eq, haplotypeTransportBias_of_matched_predictor]
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

/-! **Deleted: `haplotypeEffectEstimationVariance σ2 n freq = σ2 / (n * freq)`, together with
`haplotypeEffectEstimationVariance_lt_ols`.**

This definition is absent on purpose. Regressing on a binary haplotype indicator of
frequency `f` gives `Var(β̂) = σ²/(n·f·(1-f))`, not `σ²/(n·f)`. Dropping the `(1-f)`
**understates** the estimation variance and so **overstates** precision, worst of all for
**common** haplotypes, which is the opposite of the rarity intuition the surrounding prose
appeals to. Monte-Carlo at `n = 1000`, 3000 replicates, MC standard error about 2.6%:

| `f` | measured | `σ²/(n·f)` | `haplotypeEffectVarianceOLS` |
|---|---|---|---|
| 0.02 | 0.05286 | −5.4% | −3.5% |
| 0.1 | 0.011255 | −11.2% | −1.3% |
| 0.3 | 0.0048055 | −30.6% | −0.9% |
| 0.5 | 0.0040328 | **−50.4%** | −0.8% |

Measured in `validation/empirical/popgen_diff2/`. -/

/-- **The OLS estimation variance for a binary haplotype indicator.**

    `Var(β̂) = σ²/(n·f·(1-f))`. Monte-Carlo at `n = 1000`, 3000 replicates: within 0.8–3.5% of
    the measured variance across `f ∈ {0.02, 0.1, 0.3, 0.5}`, where `σ²/(n·f)`
    runs −5% to −50%.

    Note the shape is **U-shaped in `f`**, not monotone: the variance is largest at the two
    extremes and smallest at `f = 1/2`. The rarity intuition holds only below `f = 1/2`.

    Empirical status: **VALIDATED** (`validation/empirical/popgen_diff2/`). -/
noncomputable def haplotypeEffectVarianceOLS
    (σ2 n freq : ℝ) : ℝ :=
  σ2 / (n * freq * (1 - freq))

/-- **haplotypeEffectVarianceOLS at zero n, named.** The same failure at zero sample size, and
again in the direction that certifies rather than warns: no data yields zero estimation variance.
Consumers must require `n ≠ 0`. -/
theorem haplotypeEffectVarianceOLS_zero_n_is_junk (σ2 : ℝ) (freq : ℝ) :
    haplotypeEffectVarianceOLS σ2 0 freq = 0 := by
  unfold haplotypeEffectVarianceOLS
  simp

/-- **But haplotype PGS can overfit in training population.**

    Rare haplotypes have fewer observed carriers, so their effect estimates are noisier, and
    adding a rarer haplotype strictly increases the total estimation-noise burden. The
    hypothesis `freq_common ≤ 1/2` is load-bearing rather than cosmetic: `f(1-f)` is U-shaped,
    so above one half the *commoner* haplotype is the noisier one and the conclusion reverses.
    A body of the form `σ²/(n·f)` is monotone everywhere and cannot express that
    reversal. -/
theorem haplotype_pgs_overfitting_risk
    (σ2 n freq_common freq_rare : ℝ)
    (h_sigma : 0 < σ2)
    (h_n : 0 < n)
    (h_rare : 0 < freq_rare)
    (h_rarer : freq_rare < freq_common)
    (h_common_le_half : freq_common ≤ 1 / 2) :
    haplotypeEffectVarianceOLS σ2 n freq_common <
      haplotypeEffectVarianceOLS σ2 n freq_rare ∧
    haplotypeEffectVarianceOLS σ2 n freq_common <
      haplotypeEffectVarianceOLS σ2 n freq_common +
        haplotypeEffectVarianceOLS σ2 n freq_rare := by
  have h_rare_lt_half : freq_rare < 1 / 2 := lt_of_lt_of_le h_rarer h_common_le_half
  have h_rare_den : 0 < n * freq_rare * (1 - freq_rare) :=
    mul_pos (mul_pos h_n h_rare) (by linarith)
  have h_gap : 0 < n * ((freq_common - freq_rare) * (1 - freq_common - freq_rare)) :=
    mul_pos h_n (mul_pos (by linarith) (by linarith))
  have h_expand : n * freq_common * (1 - freq_common) - n * freq_rare * (1 - freq_rare) =
      n * ((freq_common - freq_rare) * (1 - freq_common - freq_rare)) := by ring
  have h_den_lt : n * freq_rare * (1 - freq_rare) < n * freq_common * (1 - freq_common) := by
    linarith
  unfold haplotypeEffectVarianceOLS
  have h_common_var_lt_rare :
      σ2 / (n * freq_common * (1 - freq_common)) < σ2 / (n * freq_rare * (1 - freq_rare)) :=
    div_lt_div_of_pos_left h_sigma h_rare_den h_den_lt
  have h_rare_var_pos : 0 < σ2 / (n * freq_rare * (1 - freq_rare)) :=
    div_pos h_sigma h_rare_den
  exact ⟨h_common_var_lt_rare, by linarith⟩

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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem phaseAttenuation_at_reference_point :
    phaseAttenuation 1 = 1 := by
  unfold phaseAttenuation
  norm_num

/-- **Random phasing destroys the signal entirely.**

At a switch error rate of one half the phase carries no information and the attenuation is exactly
zero. Membership in `[0,1]`, recorded below, holds for every squared affine map of `s` into that
interval and leaves the zero unlocated; this fixes it at the point where phase becomes a coin
flip, which is the only rate at which the attenuation *should* vanish. A body vanishing anywhere
else would still be bounded and still be decreasing on the relevant range. -/
theorem phaseAttenuation_random_phase : phaseAttenuation (1 / 2) = 0 := by
  unfold phaseAttenuation
  norm_num

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

/-- **Phasing error costs more attenuation in the target than in the source.**

    This is `more_errors_more_attenuation` read with source and target labels: the content is
    that attenuation is decreasing in the switch-error rate, and the biology is entirely in the
    hypothesis `s_source < s_target`. That reference panels are biased toward the training
    population is the reason someone would assert that hypothesis; no panel, no representation
    and no bias mechanism appears below, and none is derived. -/
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

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk4.py`,
    `test_ancestry_averaged_effect`). Two million simulated individuals carrying
    an ancestry label, with the true effect depending on ancestry; the oracle is
    the pooled least-squares slope of phenotype on genotype, which the mixture
    produces and this formula predicts:

      alpha   b1     b2      this def   pooled slope         sems
      0.3     1.0    0.2      0.44000   0.43970±0.00035      0.85
      0.5     0.8   -0.4      0.20000   0.19970±0.00046      0.65
      0.8     0.5    0.5      0.50000   0.50000±0.00025      0.00

    The third cell is the check that the weighting cannot manufacture a
    difference that is not there.

    Power: the prediction spans 0.20000 to 0.50000 across the design.

    Denotes: the reading its name carries. The same formula appears under
    names from 'frequency', 'variance', and the formula alone does not fix which is meant. -/
noncomputable def ancestrySpecificEffect (beta_pop1 beta_pop2 alpha : ℝ) : ℝ :=
  Descent.Core.convexCombination alpha beta_pop1 beta_pop2

/-- With the same effect in both ancestries the average is that effect, at every mixing
fraction: the ancestry weighting cannot manufacture a difference that is not there. -/
theorem ancestrySpecificEffect_const (b alpha : ℝ) :
    ancestrySpecificEffect b b alpha = b := by
  unfold ancestrySpecificEffect Descent.Core.convexCombination; ring

/-- **The ancestry-averaged effect is a convex combination.** At the two pure ancestries it
returns the corresponding effect, and swapping the two populations together with the ancestry
fraction leaves it unchanged. A body not affine in the fraction fails the endpoints. -/
theorem ancestrySpecificEffect_endpoints (b₁ b₂ : ℝ) :
    ancestrySpecificEffect b₁ b₂ 1 = b₁ ∧ ancestrySpecificEffect b₁ b₂ 0 = b₂ := by
  constructor <;> unfold ancestrySpecificEffect Descent.Core.convexCombination <;> ring

theorem ancestrySpecificEffect_relabel (b₁ b₂ alpha : ℝ) :
    ancestrySpecificEffect b₂ b₁ (1 - alpha) = ancestrySpecificEffect b₁ b₂ alpha := by
  unfold ancestrySpecificEffect Descent.Core.convexCombination; ring

/-- Ancestry-specific effect is a weighted average. -/
theorem ancestry_effect_between_pops (beta₁ beta₂ alpha : ℝ)
    (h_alpha : 0 ≤ alpha) (h_alpha_le : alpha ≤ 1)
    (h_order : beta₁ ≤ beta₂) :
    beta₁ ≤ ancestrySpecificEffect beta₁ beta₂ alpha ∧
    ancestrySpecificEffect beta₁ beta₂ alpha ≤ beta₂ := by
  unfold ancestrySpecificEffect Descent.Core.convexCombination
  constructor <;> nlinarith

/-- Single-effect predictor obtained by averaging ancestry-specific effects
according to the admixture proportion `alpha`.

    Empirical status: **VALIDATED** (`simcov/battery_bulk43.py`, `group_b`).
    2×10⁶ individuals, a fraction `alpha` carrying the first ancestry's effect
    and the rest the second; the observable is the realised MARGINAL OLS effect
    of the variant across the whole admixed sample -- exactly what a GWAS
    ignoring local ancestry would estimate. Worst cell 0.59 sems at 0.26%
    relative.

    Power: the weights SWAPPED, `(1-alpha)·β₁ + alpha·β₂`, is FALSIFIED at 294
    sems and 805% relative. That is the error the name invites -- which
    ancestry `alpha` counts -- and the two readings coincide only at
    `alpha = 1/2`, so the design sweeps 0.2, 0.3, 0.5, 0.8 across it. One cell
    gives the two ancestries effects of OPPOSITE SIGN, where the swap lands the
    average on the wrong side of zero. Control: the realised ancestry-1
    fraction recovers `alpha` on the same draws.

    This measures `ancestrySpecificEffect` too, since this body is that
    function applied to the same three arguments.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk43.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_b).
    MATCH at worst 1.48 sems; the swapped weights are FALSIFIED at 560 sems. The same
    cells measure `ancestrySpecificEffect`, which is now recorded under its own name
    rather than left implicit.
    -/
noncomputable def globalAncestryAveragedEffect
    (beta₁ beta₂ alpha : ℝ) : ℝ :=
  ancestrySpecificEffect beta₁ beta₂ alpha

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem globalAncestryAveragedEffect_at_reference_point :
    globalAncestryAveragedEffect 1 1 1 = 1 := by
  norm_num [globalAncestryAveragedEffect, ancestrySpecificEffect, Descent.Core.convexCombination]



/-- Structural prediction error from using a single ancestry-averaged effect in
an admixed population whose local ancestry really switches between ancestry 1
and ancestry 2.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk4.py`,
    `test_ancestry_averaged_effect`). Measured as the mean squared deviation of
    the true ancestry-specific effect from the single averaged effect, over the
    same two million individuals -- the loss the definition names, not its
    algebra:

      alpha   b1     b2      this def   measured loss        sems
      0.3     1.0    0.2      0.13440   0.13432±0.00008      0.91
      0.5     0.8   -0.4      0.36000   0.36000±0.00000      0.00
      0.8     0.5    0.5      0.00000   0.00000±0.00000      0.00

    Power: the prediction spans 0.00000 to 0.36000, the full range the quantity
    admits, and the vanishing cell is the one that would expose a spurious
    constant. -/
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
  unfold localAncestryMisspecification globalAncestryAveragedEffect ancestrySpecificEffect Descent.Core.convexCombination
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

/-- **The admixture tract length.**

    For a single-pulse hybrid-isolation model the ancestry-1 tracts are exponential with mean
    `1/(g(1-α))` Morgans, where `α` is the admixture fraction (Pool & Nielsen 2009; Liang &
    Nielsen 2014). The map length does **not** appear.

    **The admixture fraction is mandatory and the map length does not enter.** The form
    `1/(g·r_total)` takes a total map length `r_total` that is spurious and omits `α`
    entirely. A forward pedigree simulation with explicit Poisson crossovers settles that
    decisively: holding `α = 0.5, g = 10` and varying chromosome length, the truth is
    asymptotically **independent** of map length while `1/(g·r_total)` moves 16-fold.

    | map length | simulated | `1/(g·r_total)` |
    |---|---|---|
    | 1 M | 0.1462 ± 0.0043 | 0.1000 |
    | 4 M | 0.1728 ± 0.0023 | 0.0250 |
    | 16 M | 0.1913 ± 0.0013 | 0.00625 |

    (The simulated value rises toward `1/(g(1-α)) = 0.20` as edge censoring vanishes.) Across
    `α ∈ {0.2,0.5,0.8} × g ∈ {5,10,20}` the map-length form runs −78% to −95%, while this
    body matches to 0.1–7% where censoring is small. **No choice of units repairs it:** one
    argument is spurious and another is missing.

    Empirical status: **VALIDATED**; the form below is FALSIFIED
    (`validation/empirical/popgen_diff2/`). -/
noncomputable def expectedTractLength (g admixtureFraction : ℝ) : ℝ :=
  1 / (g * (1 - admixtureFraction))

/-- **The expected tract length at unit admixture fraction, named.** An admixture fraction of one
means every lineage comes from the same source, so ancestry never switches and tracts are
unbounded. The divisor `g * (1 - admixtureFraction)` is zero and Lean returns `0`: tracts of zero
length, the shortest possible, for the population with no ancestry breakpoints at all. Tract
length is what dates an admixture event, so this branch dates an unadmixed population as
infinitely old rather than reporting that the question does not apply. Consumers must require
`admixtureFraction ≠ 1`. -/
theorem expectedTractLength_unit_admixture_is_junk (g : ℝ) :
    expectedTractLength g 1 = 0 := by
  unfold expectedTractLength
  simp

/-- Tracts get shorter with more generations, at fixed admixture fraction. -/
theorem tract_length_shortens_with_time (g₁ g₂ admixtureFraction : ℝ)
    (h_α : admixtureFraction < 1) (h_g₁ : 0 < g₁) (h_g₂ : 0 < g₂)
    (h_g : g₁ < g₂) :
    expectedTractLength g₂ admixtureFraction < expectedTractLength g₁ admixtureFraction := by
  have h_a : 0 < 1 - admixtureFraction := by linarith
  unfold expectedTractLength
  exact div_lt_div_iff_of_pos_left one_pos (mul_pos h_g₂ h_a) (mul_pos h_g₁ h_a) |>.mpr
    (mul_lt_mul_of_pos_right h_g h_a)

end LocalAncestryHaplotypes

end Descent.PopGen
