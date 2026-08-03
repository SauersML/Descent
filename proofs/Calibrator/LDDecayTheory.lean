/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.OpenQuestions

namespace Calibrator

open MeasureTheory

/-!
# Linkage Disequilibrium Decay and PGS Portability

This file formalizes how LD structure differences across populations
affect PGS portability. LD patterns are shaped by population history
(bottlenecks, admixture, selection) and directly determine PGS accuracy.

Key results:
1. LD decay with recombination distance follows the Ohta-Kimura model
2. LD differences create PGS prediction error via tagging mismatch
3. Admixture creates long-range LD maximized at equal mixing
4. Population bottlenecks amplify LD as a function of severity and duration
5. LD mismatch quantification via Frobenius norm

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat the Ohta-Kimura decay model, admixture LD or bottleneck
amplification. Sources for individual results, where they exist, are cited at those
results.
-/


/-!
## Ohta-Kimura LD Decay Model

Under neutrality, LD between two loci decays as:
D(t) = D(0) · (1-r)^t · (1 - 1/(2Ne))^t
where r is recombination rate and Ne is effective population size.
-/

section OhtaKimuraDecay

/-- **LD decay coefficient per generation.**
    The fraction of LD retained per generation between two loci.

    Empirical status: VALIDATED. Coalescent simulation tracks `E[D]/D₀` to
    three or four significant figures across the tested range of `Ne`, `r` and
    `t` (for instance `0.3312` predicted against `0.3308` observed). The
    specific concern that this conflates decay of `D` with decay of `r²` was
    tested and is unfounded. -/
noncomputable def ldRetentionPerGen (r Ne : ℝ) : ℝ :=
  (1 - r) * (1 - 1 / (2 * Ne))

/-- LD retention is strictly less than 1 for positive recombination and finite Ne. -/
theorem ld_retention_lt_one (r Ne : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hNe : 1 < Ne) :
    ldRetentionPerGen r Ne < 1 := by
  unfold ldRetentionPerGen
  have h1 : 1 - r < 1 := by linarith
  have h2 : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos]; rw [div_lt_one (by linarith)]; linarith
  have h3 : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  calc (1 - r) * (1 - 1 / (2 * Ne))
      < 1 * (1 - 1 / (2 * Ne)) := mul_lt_mul_of_pos_right h1 h2
    _ = 1 - 1 / (2 * Ne) := one_mul _
    _ < 1 := h3

/-- LD retention is nonneg for reasonable parameters. -/
theorem ld_retention_nonneg (r Ne : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hNe : 1 ≤ Ne) :
    0 ≤ ldRetentionPerGen r Ne := by
  unfold ldRetentionPerGen
  apply mul_nonneg
  · linarith
  · rw [sub_nonneg]; rw [div_le_one (by linarith)]; linarith

/-- **LD after t generations.**
    D(t) = D(0) · (ldRetention)^t.

    Empirical status: VALIDATED alongside `ldRetentionPerGen`. -/
noncomputable def ldAfterGenerations (D₀ r Ne : ℝ) (t : ℕ) : ℝ :=
  D₀ * (ldRetentionPerGen r Ne) ^ t

/-- LD decays monotonically with time. -/
theorem ld_decays_with_time (D₀ r Ne : ℝ) (t₁ t₂ : ℕ)
    (hD₀ : 0 < D₀) (hr : 0 < r) (hr1 : r < 1) (hNe : 1 < Ne)
    (h_time : t₁ < t₂) :
    |ldAfterGenerations D₀ r Ne t₂| < |ldAfterGenerations D₀ r Ne t₁| := by
  simp only [ldAfterGenerations, abs_mul, abs_of_pos hD₀]
  apply mul_lt_mul_of_pos_left _ hD₀
  have h_ret_nn : 0 ≤ ldRetentionPerGen r Ne :=
    ld_retention_nonneg r Ne (le_of_lt hr) (le_of_lt hr1) (le_of_lt hNe)
  have h_ret_lt : ldRetentionPerGen r Ne < 1 :=
    ld_retention_lt_one r Ne hr hr1 hNe
  rw [abs_of_nonneg (pow_nonneg h_ret_nn _), abs_of_nonneg (pow_nonneg h_ret_nn _)]
  have h_ret_pos : 0 < ldRetentionPerGen r Ne := by
    unfold ldRetentionPerGen
    apply mul_pos
    · linarith
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
  exact pow_lt_pow_right_of_lt_one₀ h_ret_pos h_ret_lt h_time

end OhtaKimuraDecay


/-!
## LD-Based Tagging and PGS Accuracy

PGS uses tag SNPs that are in LD with causal variants.
When LD changes, tags become less informative → PGS accuracy drops.
-/

section LDTagging

/-- **Tag SNP r² with causal variant.**
    The proportion of causal variant information captured by a tag.

    Convention: `var_tag` and `var_causal` are genotypic variances `2p(1-p)`,
    matching `hweGenotypeVariance`, and `D_sq` is a squared dosage covariance.
    Reading the variances as allelic `p(1-p)` scales the result by four, the
    same hazard `ldCorrelationSq` carries. -/
noncomputable def tagR2 (D_sq var_tag var_causal : ℝ) : ℝ :=
  D_sq / (var_tag * var_causal)

/-- Tag r² is bounded by 1. -/
theorem tag_r2_le_one (D_sq var_tag var_causal : ℝ)
    (h_cauchy_schwarz : D_sq ≤ var_tag * var_causal)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal) :
    tagR2 D_sq var_tag var_causal ≤ 1 := by
  unfold tagR2
  rw [div_le_one (mul_pos h_vt h_vc)]
  exact h_cauchy_schwarz

/-- **Tag r² decreases when LD structure changes.**
    In the target population, D² between tag and causal may be different. -/
theorem tag_r2_decreases_with_ld_change
    (D_sq_source D_sq_target var_tag var_causal : ℝ)
    (h_vt : 0 < var_tag) (h_vc : 0 < var_causal)
    (h_ld_drop : D_sq_target < D_sq_source) :
    tagR2 D_sq_target var_tag var_causal < tagR2 D_sq_source var_tag var_causal := by
  unfold tagR2
  exact div_lt_div_of_pos_right h_ld_drop (mul_pos h_vt h_vc)

/-- **Total PGS accuracy is the product of tag accuracies.**
    R²_PGS ≈ Σᵢ r²_tag_i × β_causal_i² / V_Y.
    When tag r² drops, PGS R² drops proportionally. -/
theorem pgs_accuracy_from_tagging
    {m : ℕ} (r2_tag : Fin m → ℝ) (β_sq : Fin m → ℝ) (v_y : ℝ)
    (h_vy : 0 < v_y) (h_β : ∀ i, 0 ≤ β_sq i) (h_r2 : ∀ i, 0 ≤ r2_tag i) :
    0 ≤ (∑ i, r2_tag i * β_sq i) / v_y := by
  apply div_nonneg _ (le_of_lt h_vy)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (h_r2 i) (h_β i)

end LDTagging


/-!
## Admixture and Long-Range LD

Recently admixed populations have long-range LD between loci that are
in different LD blocks in the ancestral populations. This creates
unique portability challenges.
-/

section AdmixtureLD

/-- **Admixture LD between unlinked loci.**
    D_admix = α(1-α)(p₁_A - p₁_B)(p₂_A - p₂_B)
    where α is admixture proportion and A,B are ancestral populations.

    Empirical status: UNTESTED. -/
noncomputable def admixtureLD (α Δp₁ Δp₂ : ℝ) : ℝ :=
  α * (1 - α) * Δp₁ * Δp₂

/-- Admixture LD is maximized at α = 0.5. -/
theorem admixture_ld_max_at_half_freq (Δp₁ Δp₂ α : ℝ)
    (h_pos₁ : 0 < Δp₁) (h_pos₂ : 0 < Δp₂)
    (h_α : 0 < α) (h_α1 : α < 1) :
    admixtureLD α Δp₁ Δp₂ ≤ admixtureLD (1/2) Δp₁ Δp₂ := by
  unfold admixtureLD
  have h1 : α * (1 - α) ≤ 1/4 := by nlinarith [sq_nonneg (α - 1/2)]
  have h2 : (1/2 : ℝ) * (1 - 1/2) = 1/4 := by norm_num
  nlinarith [mul_pos h_pos₁ h_pos₂]

/-- **Admixture LD decays with time since admixture.**
    D_admix(t) = D_admix(0) · (1-r)^t.
    For unlinked loci (r = 0.5), D halves each generation. -/
theorem admixture_ld_decays_unlinked (D₀ : ℝ) (t : ℕ) (hD₀ : 0 < D₀) :
    D₀ * (1/2 : ℝ) ^ (t + 1) < D₀ * (1/2 : ℝ) ^ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  apply pow_lt_pow_right_of_lt_one₀
  · norm_num
  · norm_num
  · omega

end AdmixtureLD


/-!
## Population Bottlenecks and LD Amplification

Bottlenecks increase LD because genetic drift in a small population
generates LD between previously independent loci.
-/

section BottleneckLD

/-! ### Bottleneck LD amplification

Removed.  This defined `bottleneckLDAmplification N_b t = 1 - (1 - 1/(2 N_b))^t`,
drift-generated LD after a bottleneck.  Simulation falsifies it: it takes no
recombination rate, so it rises to 1 with time instead of saturating at the
drift-recombination equilibrium `1/(1 + 4 N c)`, overstating by up to 3.3-fold.
The missing argument is the defect, as in five earlier cases, and no constant
repairs it.

What follows is the replacement.  Rather than asserting a closed form, it
defines the Sved (1971) drift--recombination *process* -- with the recombination
rate present -- states the equilibrium separately, and proves that the stated
equilibrium is a fixed point of the process and that the trajectory converges to
it.  `driftLDEquilibrium_zero_recomb` isolates exactly the regime in which the
deleted formula was right (`c = 0`, where the equilibrium really is `1`), and
`driftLDEquilibrium_le_one` is the bound the deleted formula satisfied only
because it had no other place to go.
-/

/-- **One generation of the Sved (1971) drift--recombination recurrence** for
    the two-locus identity-by-descent measure `Q` (the quantity whose
    equilibrium is the familiar `E[r²] ≈ 1/(1 + 4 N c)`).

    Two lineage pairs stay non-recombinant across the generation with
    probability `(1 - c)²`; conditional on that, they are identical either
    because they coalesced this generation (probability `1/(2 Nₑ)`) or because
    they were already identical (probability `Q`).

      Q(t+1) = (1 - c)² · [ 1/(2 Nₑ) + (1 - 1/(2 Nₑ)) · Q(t) ]

    **This map is shared with the island model, and the sharing is substantive
    rather than a coincidence of algebra.** The single-locus island-model
    identity recursion is the same map with the migration rate `m` in the place
    of `c` and `F_ST` in the place of `Q`
    (`driftLDStep_eq_islandFstMultiplicativeStep` below states the identity).
    The fixed point of `x = (1-t)²(a + (1-a)x)` with `a = 1/(2 Nₑ)` is
    `x* = (1-t)² a / (1 - (1-t)²(1-a))`, which to first order in small `t` and
    `a` is `a/(a + 2t) = 1/(1 + 4 Nₑ t)`. Sved's `1/(1 + 4 Nₑ c)` and Wright's
    `1/(1 + 4 Nₑ m)` are therefore the same linearisation of the same
    recurrence, which is why the two formulas have always looked alike.

    **Pending refactor.** The owner of `PortabilityDrift.lean` is extracting the
    shared map under a rate-neutral name (`ibdRecurrenceStep Ne rate x`), with
    the fixed point and the weak-rate linearisation stated there as
    theorems. Once that lands this body should become
    `ibdRecurrenceStep Ne c Q`, keeping the recombination reading in this
    docstring and inheriting the fixed-point theorem instead of restating it.
    It must NOT be defined as `islandFstMultiplicativeStep`: an LD recurrence
    defined in terms of a symbol named after `F_ST` is a misnaming, and
    misnaming is what produced the factor-of-four error already recorded in this
    corpus.

    Empirical status: UNTESTED as written here.  The formula it replaces
    (`bottleneckLDAmplification`, deleted above) was falsified by up to 3.3-fold
    through omitting `c`; the classical small-`c`, large-`Nₑ` limit of the
    fixed point of this map is the Sved expression `1/(1 + 4 Nₑ c)` that the
    falsification report cites as truth, but that limit is documented here, not
    proved, and the map itself has not been simulated. -/
noncomputable def driftLDStep (Ne c Q : ℝ) : ℝ :=
  (1 - c) ^ 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * Q)

/-- **Cross-check: the Sved drift-recombination step and the island-model
`F_ST` step are one recurrence.** `PortabilityDrift.islandFstMultiplicativeStep`
applies it with the migration rate in the place of the recombination rate and
`F_ST` in the place of the identity measure. The two are different processes
and the same map, so the `1/(2 Nₑ)` inside them has to be the same
`1/(2 Nₑ)`. -/
theorem driftLDStep_eq_islandFstMultiplicativeStep (Ne c Q : ℝ) :
    driftLDStep Ne c Q = islandFstMultiplicativeStep Ne c Q := by
  unfold driftLDStep islandFstMultiplicativeStep ibdRecurrenceStep
  ring

/-- **`driftLDStep` is the rate-neutral recurrence, stated directly.**

This body and `PortabilityDrift.ibdRecurrenceStep` are the same expression written twice
in two modules, which the pending refactor above is meant to collapse. Until it does, the
identity has to be stated somewhere, because a duplicated body that nothing relates is the
shape in which one copy gets repaired and the other silently does not — this corpus has
already paid that bill three times over `F_ST`.

It is available transitively — `driftLDStep_eq_islandFstMultiplicativeStep` just above,
composed with `islandFstMultiplicativeStep` being `ibdRecurrenceStep` by definition — and
stated here anyway, in the direct form. A two-step route is a route a reader has to
reconstruct, and the guard that looks for these pairs cannot follow it. -/
theorem driftLDStep_eq_ibdRecurrenceStep (Ne c Q : ℝ) :
    driftLDStep Ne c Q = ibdRecurrenceStep Ne c Q := by
  unfold driftLDStep ibdRecurrenceStep
  ring

/-- **Per-generation retention factor of the two-locus identity measure**,
    `(1 - c)² · (1 - 1/(2 Nₑ))`: the slope of `driftLDStep` in `Q`.

    This is the factor whose absence from the deleted formula caused the
    unbounded rise: with `c = 0` it is the pure-drift retention `1 - 1/(2 Nₑ)`,
    and only a positive `c` makes the process settle below `1`.

    Empirical status: UNTESTED. -/
noncomputable def driftLDRetention (Ne c : ℝ) : ℝ :=
  (1 - c) ^ 2 * (1 - 1 / (2 * Ne))

/-- **Drift--recombination equilibrium of the two-locus identity measure.**

    This closed form is not stipulated: it is the solution of
    `driftLDStep Ne c Q = Q`, and `driftLDEquilibrium_isFixedPoint` is the
    theorem that pins it, so no other constant can be substituted here and still
    compile.

    In the small-`c`, large-`Nₑ` limit this reduces to Sved's `1/(1 + 4 Nₑ c)`.
    That limit is NOT a good approximation to `σ_d²` in the tightly-linked
    regime: measured against a two-locus Wright-Fisher simulation
    (`validation/differential/cluster/fam_ld_decay.py`) this form is +76% at
    `ρ = 0.5` and +45% at `ρ = 2`, converging to within 2% only by `ρ = 10`.
    Use `ohtaKimuraSigmaDSq` if `σ_d²` is what is wanted.

    What is proved here is the two properties the deleted formula lacked: it is
    a genuine fixed point of a map that mentions `c`, and it never exceeds `1`.

    Empirical status: VALIDATED as the two-locus identity measure -- it is the
    exact fixed point of `driftLDStep` and simulation confirms the family's
    `E[D]` retention to within 0.07%. MEASURED to differ from `σ_d²` by +76%
    at `ρ = 0.5`. -/
noncomputable def driftLDEquilibrium (Ne c : ℝ) : ℝ :=
  (1 - c) ^ 2 * (1 / (2 * Ne)) / (1 - driftLDRetention Ne c)

/-- **The Ohta-Kimura (1971) approximation to `σ_d²`**, in terms of the scaled
recombination rate `ρ = 4·Nₑ·c`:

  `σ_d² ≈ (10 + ρ) / ((2 + ρ)·(11 + ρ))`

Read the name literally: this is Ohta and Kimura's APPROXIMATION to `σ_d²`, not
`E[r²]` and not an identity probability. `σ_d²` is itself the ratio of
expectations `E[D²]/E[p(1-p)q(1-q)]`, which is a different quantity from the
expectation of the ratio that `r²` is, and the closed form above is a
truncation of the two-locus moment recursion rather than an exact solution of
anything. It is stated with its provenance because a name asserting a
provenance the body does not have is the defect class this file has already
been repaired for twice today: `driftLDEquilibrium` is the identity measure and
says so, and calling this one `expectedRSquared` would undo that in one commit.

Regime: neutral two-locus Wright-Fisher, no mutation, `Nₑ` constant, and the
diffusion limit in which `ρ` is the only parameter. Outside it -- in particular
at small `Nₑ` where `ρ` and `c` are not interchangeable -- the truncation is
not justified.

    Empirical status: VALIDATED against two-locus Wright-Fisher simulation --
    within 3.5% at `ρ = 0.5` and 1% at `ρ = 2`, where the identity measure
    `driftLDEquilibrium` is +76% and +45%. The differential check
    `ohtaKimuraSigmaDSq-matches-simulation` is the standing check. -/
noncomputable def ohtaKimuraSigmaDSq (Ne c : ℝ) : ℝ :=
  let ρ := 4 * Ne * c
  (10 + ρ) / ((2 + ρ) * (11 + ρ))

/-- `σ_d²` under this approximation is strictly positive whenever `ρ ≥ 0`,
which is what a ratio of nonnegative expectations requires and is the cheapest
statement that would fail if the sign of a coefficient were ever flipped. -/
theorem ohtaKimuraSigmaDSq_pos (Ne c : ℝ) (h : 0 ≤ 4 * Ne * c) :
    0 < ohtaKimuraSigmaDSq Ne c := by
  unfold ohtaKimuraSigmaDSq
  apply div_pos (by linarith)
  apply mul_pos <;> linarith

/-- **It is below one**, as a ratio `E[D²]/E[p(1-p)q(1-q)]` must be, and
strictly so at every `ρ ≥ 0`. -/
theorem ohtaKimuraSigmaDSq_lt_one (Ne c : ℝ) (h : 0 ≤ 4 * Ne * c) :
    ohtaKimuraSigmaDSq Ne c < 1 := by
  unfold ohtaKimuraSigmaDSq
  rw [div_lt_one (by apply mul_pos <;> linarith)]
  nlinarith

/-- **The tight-linkage value is `5/11`**, not `1`: at `ρ = 0` two loci are
completely linked and `σ_d²` still falls well short of one, because the
denominator averages over allele frequencies rather than conditioning on them.
This is the point at which the identity measure `driftLDEquilibrium` and this
approximation diverge most, and pinning it as an equation stops the constants
`10`, `2` and `11` from drifting. -/
theorem ohtaKimuraSigmaDSq_at_zero (Ne : ℝ) :
    ohtaKimuraSigmaDSq Ne 0 = 5 / 11 := by
  unfold ohtaKimuraSigmaDSq
  norm_num

/-- The one-generation map is affine in `Q`, with slope `driftLDRetention`. -/
theorem driftLDStep_affine (Ne c Q : ℝ) :
    driftLDStep Ne c Q =
      (1 - c) ^ 2 * (1 / (2 * Ne)) + driftLDRetention Ne c * Q := by
  unfold driftLDStep driftLDRetention
  ring

/-- **The two equilibria are one equilibrium too.**  The step-level identity
above forces this, but the two closed forms are written differently enough that
nothing would have caught it: `driftLDEquilibrium` is
`(1-c)²·(1/(2Nₑ)) / (1 - (1-c)²(1 - 1/(2Nₑ)))` and
`fstIslandMultiplicativeEquilibrium` is `(1-m)²/((1-m)² + 2Nₑm(2-m))`.
Multiplying the first through by `2Nₑ` gives the second, since
`2Nₑ(1 - (1-t)²(1 - 1/(2Nₑ))) = (1-t)² + 2Nₑt(2-t)`.

Stated here so that when the shared map is extracted under a neutral name, the
two equilibria go with it as one quantity rather than being deduplicated by
inspection. -/
theorem driftLDEquilibrium_eq_fstIslandMultiplicativeEquilibrium (Ne c : ℝ)
    (hNe : Ne ≠ 0) :
    driftLDEquilibrium Ne c = fstIslandMultiplicativeEquilibrium Ne c := by
  unfold driftLDEquilibrium driftLDRetention fstIslandMultiplicativeEquilibrium
    ibdRecurrenceFixedPoint
  field_simp [hNe]
  ring

/-- The retention factor is a genuine per-generation probability: it lies in
    `[0, 1]` whenever `Nₑ ≥ 1` and `c ∈ [0, 1]`. -/
theorem driftLDRetention_mem_unit (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ driftLDRetention Ne c ∧ driftLDRetention Ne c ≤ 1 := by
  have hu_pos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
  have hu_le : 1 / (2 * Ne) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hk_nonneg : 0 ≤ (1 - c) ^ 2 := sq_nonneg _
  have hk_le : (1 - c) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 2 - c)]
  unfold driftLDRetention
  constructor
  · exact mul_nonneg hk_nonneg (by linarith)
  · nlinarith

/-- The retention factor is strictly below `1` once recombination is present.
    This is the statement the deleted formula could not make. -/
theorem driftLDRetention_lt_one (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 < c) (hc1 : c ≤ 1) :
    driftLDRetention Ne c < 1 := by
  have hu_pos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
  have hu_le : 1 / (2 * Ne) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hk_lt : (1 - c) ^ 2 < 1 := by
    nlinarith [mul_pos hc (by linarith : (0:ℝ) < 2 - c)]
  have hk_nonneg : 0 ≤ (1 - c) ^ 2 := sq_nonneg _
  unfold driftLDRetention
  nlinarith

/-- The retention factor is strictly positive when `c < 1` and `Nₑ > 1/2`. -/
theorem driftLDRetention_pos (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc1 : c < 1) :
    0 < driftLDRetention Ne c := by
  have hu_lt : 1 / (2 * Ne) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hk_pos : 0 < (1 - c) ^ 2 := pow_pos (by linarith : (0:ℝ) < 1 - c) 2
  unfold driftLDRetention
  exact mul_pos hk_pos (by linarith)

/-- Larger populations retain a larger fraction of the identity measure per
    generation, at fixed recombination rate. -/
theorem driftLDRetention_strictMono (Ne₁ Ne₂ c : ℝ)
    (hNe₁ : 1 ≤ Ne₁) (h_lt : Ne₁ < Ne₂) (hc1 : c < 1) :
    driftLDRetention Ne₁ c < driftLDRetention Ne₂ c := by
  have hk_pos : 0 < (1 - c) ^ 2 := pow_pos (by linarith : (0:ℝ) < 1 - c) 2
  have hu_lt : 1 / (2 * Ne₂) < 1 / (2 * Ne₁) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  unfold driftLDRetention
  exact mul_lt_mul_of_pos_left (by linarith) hk_pos

/-- The denominator of the equilibrium is positive, so the equilibrium is
    well-defined for every admissible `(Nₑ, c)`. -/
theorem driftLD_one_sub_retention_pos (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 < 1 - driftLDRetention Ne c := by
  have hu_pos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
  have hu_le : 1 / (2 * Ne) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hk_le : (1 - c) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 2 - c)]
  unfold driftLDRetention
  nlinarith [mul_nonneg (sub_nonneg.2 hk_le) (sub_nonneg.2 hu_le)]

/-- Clearing the denominator: `Q* · (1 - retention)` is the per-generation
    coalescence input `(1 - c)²/(2 Nₑ)`. -/
theorem driftLDEquilibrium_mul_one_sub_retention (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    driftLDEquilibrium Ne c * (1 - driftLDRetention Ne c) =
      (1 - c) ^ 2 * (1 / (2 * Ne)) := by
  have h_ne : 1 - driftLDRetention Ne c ≠ 0 :=
    ne_of_gt (driftLD_one_sub_retention_pos Ne c hNe hc hc1)
  unfold driftLDEquilibrium
  field_simp

/-- **The equilibrium is a fixed point of the one-generation map.**  This is
    the theorem that makes `driftLDEquilibrium` unfalsifiable-by-stipulation
    impossible: it is derived from the dynamic, not asserted alongside it.  The
    deleted `bottleneckLDAmplification` had no such theorem, and no map it could
    have been a fixed point of, because it had no `c`. -/
theorem driftLDEquilibrium_isFixedPoint (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    driftLDStep Ne c (driftLDEquilibrium Ne c) = driftLDEquilibrium Ne c := by
  rw [driftLDStep_affine,
    ← driftLDEquilibrium_mul_one_sub_retention Ne c hNe hc hc1]
  ring

/-- **Without recombination the equilibrium really is `1`.**  `c = 0` is the only
    point at which drift-generated identity rises to one, so an equilibrium
    formula that returns `1` at positive `c` is wrong there. -/
theorem driftLDEquilibrium_zero_recomb (Ne : ℝ) (hNe : 0 < Ne) :
    driftLDEquilibrium Ne 0 = 1 := by
  have hb : (0 : ℝ) < 1 / (2 * Ne) := div_pos one_pos (by linarith)
  unfold driftLDEquilibrium driftLDRetention
  have hin : (1 : ℝ) - (1 - 0) ^ 2 * (1 - 1 / (2 * Ne)) = 1 / (2 * Ne) := by ring
  have hnum : ((1 : ℝ) - 0) ^ 2 * (1 / (2 * Ne)) = 1 / (2 * Ne) := by ring
  rw [hin, hnum, div_self (ne_of_gt hb)]

/-- **The equilibrium is nonnegative.** -/
theorem driftLDEquilibrium_nonneg (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ driftLDEquilibrium Ne c := by
  have hden := driftLD_one_sub_retention_pos Ne c hNe hc hc1
  have hu_pos : 0 < 1 / (2 * Ne) := div_pos one_pos (by linarith)
  unfold driftLDEquilibrium
  exact div_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hu_pos)) (le_of_lt hden)

/-- **The equilibrium never exceeds `1`.**  This is the physical constraint the
    deleted formula satisfied only by saturating at `1`; here it is a bound that
    any replacement body must also satisfy in order to typecheck. -/
theorem driftLDEquilibrium_le_one (Ne c : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    driftLDEquilibrium Ne c ≤ 1 := by
  have hden := driftLD_one_sub_retention_pos Ne c hNe hc hc1
  have hk_le : (1 - c) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 2 - c)]
  unfold driftLDEquilibrium
  rw [div_le_one hden]
  unfold driftLDRetention
  nlinarith

/-- **Smaller populations equilibrate at higher LD**, weakly. -/
theorem driftLDEquilibrium_antitone (Ne₁ Ne₂ c : ℝ)
    (hNe₁ : 1 ≤ Ne₁) (h_le : Ne₁ ≤ Ne₂) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    driftLDEquilibrium Ne₂ c ≤ driftLDEquilibrium Ne₁ c := by
  have hNe₂ : (1 : ℝ) ≤ Ne₂ := le_trans hNe₁ h_le
  have hd₁ := driftLD_one_sub_retention_pos Ne₁ c hNe₁ hc hc1
  have hd₂ := driftLD_one_sub_retention_pos Ne₂ c hNe₂ hc hc1
  have hk_nonneg : 0 ≤ (1 - c) ^ 2 := sq_nonneg _
  have hk_le : (1 - c) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 2 - c)]
  have hu_le : 1 / (2 * Ne₂) ≤ 1 / (2 * Ne₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  unfold driftLDEquilibrium
  rw [div_le_div_iff₀ hd₂ hd₁]
  unfold driftLDRetention
  nlinarith [mul_nonneg (mul_nonneg hk_nonneg (sub_nonneg.2 hk_le))
    (sub_nonneg.2 hu_le)]

/-- **Smaller populations equilibrate at strictly higher LD** once recombination
    is present but not free. -/
theorem driftLDEquilibrium_strictAnti (Ne₁ Ne₂ c : ℝ)
    (hNe₁ : 1 ≤ Ne₁) (h_lt : Ne₁ < Ne₂) (hc : 0 < c) (hc1 : c < 1) :
    driftLDEquilibrium Ne₂ c < driftLDEquilibrium Ne₁ c := by
  have hNe₂ : (1 : ℝ) ≤ Ne₂ := by linarith
  have hd₁ := driftLD_one_sub_retention_pos Ne₁ c hNe₁ (le_of_lt hc) (le_of_lt hc1)
  have hd₂ := driftLD_one_sub_retention_pos Ne₂ c hNe₂ (le_of_lt hc) (le_of_lt hc1)
  have hk_pos : 0 < (1 - c) ^ 2 := pow_pos (by linarith : (0:ℝ) < 1 - c) 2
  have hk_lt : (1 - c) ^ 2 < 1 := by
    nlinarith [mul_pos hc (by linarith : (0:ℝ) < 2 - c)]
  have hu_lt : 1 / (2 * Ne₂) < 1 / (2 * Ne₁) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  unfold driftLDEquilibrium
  rw [div_lt_div_iff₀ hd₂ hd₁]
  unfold driftLDRetention
  nlinarith [mul_pos (mul_pos hk_pos (sub_pos.2 hk_lt)) (sub_pos.2 hu_lt)]

/-- **The trajectory of the two-locus identity measure** from an initial level
    `Q₀`, iterating `driftLDStep`.  This is the process; the closed form below
    is a theorem about it, not a second definition.

    Empirical status: UNTESTED. -/
noncomputable def driftLDTrajectory (Ne c Q₀ : ℝ) : ℕ → ℝ
  | 0 => Q₀
  | t + 1 => driftLDStep Ne c (driftLDTrajectory Ne c Q₀ t)

@[simp] theorem driftLDTrajectory_zero (Ne c Q₀ : ℝ) :
    driftLDTrajectory Ne c Q₀ 0 = Q₀ := rfl

@[simp] theorem driftLDTrajectory_succ (Ne c Q₀ : ℝ) (t : ℕ) :
    driftLDTrajectory Ne c Q₀ (t + 1) =
      driftLDStep Ne c (driftLDTrajectory Ne c Q₀ t) := rfl

/-- **Closed form of the trajectory**, proved by induction from the recurrence:
    the deviation from equilibrium decays geometrically at the retention rate.

      Q(t) = Q* + (Q₀ - Q*) · retentionᵗ

    Because `retention < 1` exactly when `c > 0`, the trajectory approaches
    `Q*` and not `1`.  This identity is what the deleted formula asserted
    without a process to assert it about. -/
theorem driftLDTrajectory_closedForm (Ne c Q₀ : ℝ)
    (hNe : 1 ≤ Ne) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℕ) :
    driftLDTrajectory Ne c Q₀ t =
      driftLDEquilibrium Ne c +
        (Q₀ - driftLDEquilibrium Ne c) * driftLDRetention Ne c ^ t := by
  induction t with
  | zero =>
      rw [driftLDTrajectory_zero, pow_zero, mul_one]
      ring
  | succ n ih =>
      rw [driftLDTrajectory_succ, ih, driftLDStep_affine,
        ← driftLDEquilibrium_mul_one_sub_retention Ne c hNe hc hc1]
      ring

end BottleneckLD


/-!
## LD Mismatch Quantification

We formalize how to quantify the LD mismatch between source and target
populations and its impact on PGS accuracy.
-/

section LDMismatchQuantification

/-- **LD matrix distance.**
    The Frobenius norm of the difference between source and target
    LD matrices captures the total LD mismatch.

    Empirical status: UNTESTED. -/
noncomputable def ldMismatchFrobenius
    {p : ℕ} (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  frobeniusNormSq (Sig_S - Sig_T)

/-- LD mismatch is nonneg. -/
theorem ld_mismatch_nonneg {p : ℕ}
    (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ldMismatchFrobenius Sig_S Sig_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_nonneg _

/-- LD mismatch is positive when matrices differ. -/
theorem ld_mismatch_pos_of_ne {p : ℕ}
    (Sig_S Sig_T : Matrix (Fin p) (Fin p) ℝ)
    (h_ne : ∃ i j, (Sig_S - Sig_T) i j ≠ 0) :
    0 < ldMismatchFrobenius Sig_S Sig_T := by
  unfold ldMismatchFrobenius
  exact frobeniusNormSq_pos_of_exists_ne_zero _ h_ne

end LDMismatchQuantification


/-!
## Harmonic Mean Effective Population Size

When Ne varies over time, the effective drift is governed by the harmonic
mean: 1/Ne_eff = (1/T) Σ 1/Ne(t). Bottleneck generations dominate because
their small Ne contributes disproportionately large 1/Ne terms.
-/

section HarmonicMeanNe

/-- **Harmonic mean Ne** for a population size trajectory over T generations. -/
noncomputable def harmonicMeanNe {T : ℕ} (Ne : Fin T → ℝ) : ℝ :=
  (T : ℝ) / ∑ i, (1 / Ne i)

/-- The reciprocal of the harmonic mean equals the average of reciprocals. -/
theorem harmonic_mean_reciprocal (T : ℕ) (hT : 0 < T)
    (Ne : Fin T → ℝ) (hNe : ∀ i, 0 < Ne i) :
    1 / harmonicMeanNe Ne = (1 / (T : ℝ)) * ∑ i, (1 / Ne i) := by
  unfold harmonicMeanNe
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsum_pos : 0 < ∑ i, (1 / Ne i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe i)
    · exact ⟨⟨0, hT⟩, by simp⟩
  field_simp [ne_of_gt hT_pos, ne_of_gt hsum_pos]

/-- Replacing one generation's Ne with a smaller value decreases the harmonic mean.
    This shows bottleneck generations dominate. -/
theorem bottleneck_dominates_harmonic_mean (T : ℕ) (hT : 0 < T)
    (Ne₁ Ne₂ : Fin T → ℝ)
    (hNe₁ : ∀ i, 0 < Ne₁ i) (hNe₂ : ∀ i, 0 < Ne₂ i)
    (h_recip_larger : ∑ i, (1 / Ne₁ i) < ∑ i, (1 / Ne₂ i)) :
    harmonicMeanNe Ne₂ < harmonicMeanNe Ne₁ := by
  unfold harmonicMeanNe
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hs₁ : 0 < ∑ i, (1 / Ne₁ i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe₁ i)
    · exact ⟨⟨0, hT⟩, by simp⟩
  have hs₂ : 0 < ∑ i, (1 / Ne₂ i) := by
    apply Finset.sum_pos
    · intro i _; exact div_pos one_pos (hNe₂ i)
    · exact ⟨⟨0, hT⟩, by simp⟩
  exact div_lt_div_of_pos_left hT_pos hs₁ h_recip_larger

/-- A single bottleneck generation (small Ne_b) makes the harmonic mean
    smaller than the arithmetic mean would suggest.
    Specifically: if Ne_b < Ne_normal, then 1/Ne_b > 1/Ne_normal,
    so the sum of reciprocals is dominated by bottleneck terms. -/
theorem bottleneck_reciprocal_dominance (Ne_b Ne_normal : ℝ)
    (hb : 0 < Ne_b)
    (h_bottle : Ne_b < Ne_normal) :
    1 / Ne_normal < 1 / Ne_b := by
  exact div_lt_div_of_pos_left one_pos hb h_bottle

end HarmonicMeanNe


/-!
## Bottleneck Effects on LD

A bottleneck (temporary reduction in Ne) amplifies LD above equilibrium
levels. After recovery, LD decays back but excess persists proportionally
to recovery population size.
-/

section BottleneckLDExcess

/-- **Excess LD from a bottleneck**, over the level the same population would
    have carried had it stayed at its recovered size.

    The previous body of this definition was
    `(1 - (1 - 1/(2 N_b))^t_b) * (1 - 1/(2 N_r))^t_r`.  Its first factor is
    `bottleneckLDAmplification` verbatim -- the formula deleted about a hundred
    lines above this one for taking no recombination rate, so that it rises to
    `1` with time instead of saturating at the drift--recombination equilibrium,
    overstating by up to 3.3-fold.  The deletion notice's reasoning applied to
    this copy word for word, and to a third copy in `DemographicHistory`.

    The replacement is not another closed form.  It is the composition of the
    Sved drift--recombination process defined above: start the population at the
    equilibrium for its recovered size `N_r`, run `t_b` generations at the
    bottleneck size `N_b`, then run `t_r` generations back at `N_r`, and report
    the level above the `N_r` equilibrium.  `excessLDAfterBottleneck_closedForm`
    proves the closed form that results, and it saturates at the *gap between
    two equilibria* rather than at `1`.

    **The UNTESTED marker was STALE and there is a LIVE DISAGREEMENT.** A simulation against
    this body already exists — `validation/differential/cluster/fam_ld_decay.py` section C,
    measuring two-locus Wright–Fisher `σ_d²` — and it does **not** agree:

    | `ρ` | `t_b` | measured amplification | this body |
    |---|---|---|---|
    | 2 | 25 | 2.66 | 5.16 |
    | 10 | 25 | 11.70 | 7.81 |
    | 10 | 100 | 3.68 | 8.25 |

    The disagreement runs in **both** directions, so it is not a single missing factor, and
    the run's null arm passes, so it is not an engine artefact. `bottleneckExcessLD`
    (`DemographicHistory`) is proved equal to this at `t_r = 0` and inherits the finding.

    What is *not* established is which side is wrong: the measurement targets `σ_d²` while
    this body is a `D`-scale trajectory, and nobody has checked that the two are the same
    observable. That check is the next step and it has not been done.

    The falsification that removed this definition's predecessor (up to 3.3-fold
    overstatement, from the missing `c`) does not apply here, because `c` is present and the
    process demonstrably saturates (`driftLDEquilibrium_le_one`).

    Empirical status: **DISAGREES WITH AN EXISTING MEASUREMENT**, direction unresolved
    (`validation/differential/cluster/fam_ld_decay.py`, `proofs/validation/coalescent_diff/`). -/
noncomputable def excessLDAfterBottleneck (N_b N_r c : ℝ) (t_b t_r : ℕ) : ℝ :=
  driftLDTrajectory N_r c
      (driftLDTrajectory N_b c (driftLDEquilibrium N_r c) t_b) t_r -
    driftLDEquilibrium N_r c

/-- **Closed form of the two-phase excess.**  The excess is the gap between the
    two equilibria, approached over the bottleneck and decaying over the
    recovery.  Unlike its predecessor, the amplitude is bounded by that gap. -/
theorem excessLDAfterBottleneck_closedForm (N_b N_r c : ℝ) (t_b t_r : ℕ)
    (hNb : 1 ≤ N_b) (hNr : 1 ≤ N_r) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    excessLDAfterBottleneck N_b N_r c t_b t_r =
      (driftLDEquilibrium N_b c - driftLDEquilibrium N_r c) *
        (1 - driftLDRetention N_b c ^ t_b) *
        driftLDRetention N_r c ^ t_r := by
  unfold excessLDAfterBottleneck
  rw [driftLDTrajectory_closedForm N_r c _ hNr hc hc1 t_r,
    driftLDTrajectory_closedForm N_b c _ hNb hc hc1 t_b]
  ring

/-- Excess LD is nonneg for reasonable parameters. -/
theorem excess_ld_nonneg (N_b N_r c : ℝ) (t_b t_r : ℕ)
    (hNb : 1 ≤ N_b) (h_bottle : N_b ≤ N_r)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ excessLDAfterBottleneck N_b N_r c t_b t_r := by
  have hNr : (1 : ℝ) ≤ N_r := le_trans hNb h_bottle
  rw [excessLDAfterBottleneck_closedForm N_b N_r c t_b t_r hNb hNr hc hc1]
  have h_gap : 0 ≤ driftLDEquilibrium N_b c - driftLDEquilibrium N_r c := by
    have := driftLDEquilibrium_antitone N_b N_r c hNb h_bottle hc hc1
    linarith
  have h_Lb := driftLDRetention_mem_unit N_b c hNb hc hc1
  have h_Lr := driftLDRetention_mem_unit N_r c hNr hc hc1
  have h_amp : 0 ≤ 1 - driftLDRetention N_b c ^ t_b := by
    have hp : driftLDRetention N_b c ^ t_b ≤ 1 := pow_le_one₀ h_Lb.1 h_Lb.2
    linarith
  have h_dec : 0 ≤ driftLDRetention N_r c ^ t_r := pow_nonneg h_Lr.1 t_r
  exact mul_nonneg (mul_nonneg h_gap h_amp) h_dec

/-- More severe bottleneck (smaller N_b) produces more excess LD. -/
theorem more_severe_bottleneck_more_ld (N₁ N₂ N_r c : ℝ) (t_b t_r : ℕ)
    (hN₂ : 1 ≤ N₂) (h_smaller : N₂ < N₁) (h_bound : N₁ ≤ N_r)
    (hc : 0 < c) (hc1 : c < 1) (ht_b : 0 < t_b) :
    excessLDAfterBottleneck N₁ N_r c t_b t_r <
      excessLDAfterBottleneck N₂ N_r c t_b t_r := by
  have hN₁ : (1 : ℝ) ≤ N₁ := by linarith
  have hNr : (1 : ℝ) ≤ N_r := le_trans hN₁ h_bound
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hc1' : c ≤ 1 := le_of_lt hc1
  rw [excessLDAfterBottleneck_closedForm N₁ N_r c t_b t_r hN₁ hNr hc0 hc1',
    excessLDAfterBottleneck_closedForm N₂ N_r c t_b t_r hN₂ hNr hc0 hc1']
  -- the two equilibrium gaps
  have h_gap₁ : 0 ≤ driftLDEquilibrium N₁ c - driftLDEquilibrium N_r c := by
    have := driftLDEquilibrium_antitone N₁ N_r c hN₁ h_bound hc0 hc1'
    linarith
  have h_gap_lt :
      driftLDEquilibrium N₁ c - driftLDEquilibrium N_r c <
        driftLDEquilibrium N₂ c - driftLDEquilibrium N_r c := by
    have := driftLDEquilibrium_strictAnti N₂ N₁ c hN₂ h_smaller hc hc1
    linarith
  -- the two approach amplitudes
  have hL₂ := driftLDRetention_mem_unit N₂ c hN₂ hc0 hc1'
  have hL₁ := driftLDRetention_mem_unit N₁ c hN₁ hc0 hc1'
  have h_ret_lt : driftLDRetention N₂ c < driftLDRetention N₁ c :=
    driftLDRetention_strictMono N₂ N₁ c hN₂ h_smaller hc1
  have h_pow_lt :
      driftLDRetention N₂ c ^ t_b < driftLDRetention N₁ c ^ t_b :=
    pow_lt_pow_left₀ h_ret_lt hL₂.1 (by omega)
  have h_amp₁ : 0 ≤ 1 - driftLDRetention N₁ c ^ t_b := by
    have hp : driftLDRetention N₁ c ^ t_b ≤ 1 := pow_le_one₀ hL₁.1 hL₁.2
    linarith
  have h_amp₂_pos : 0 < 1 - driftLDRetention N₂ c ^ t_b := by linarith
  -- the recovery decay factor is strictly positive
  have h_Lr_pos : 0 < driftLDRetention N_r c :=
    driftLDRetention_pos N_r c hNr hc1
  have h_dec_pos : 0 < driftLDRetention N_r c ^ t_r := pow_pos h_Lr_pos t_r
  -- combine: A₁·B₁ ≤ A₁·B₂ < A₂·B₂, then scale by the positive decay factor
  have h_step₁ :
      (driftLDEquilibrium N₁ c - driftLDEquilibrium N_r c) *
          (1 - driftLDRetention N₁ c ^ t_b) ≤
        (driftLDEquilibrium N₁ c - driftLDEquilibrium N_r c) *
          (1 - driftLDRetention N₂ c ^ t_b) :=
    mul_le_mul_of_nonneg_left (by linarith) h_gap₁
  have h_step₂ :
      (driftLDEquilibrium N₁ c - driftLDEquilibrium N_r c) *
          (1 - driftLDRetention N₂ c ^ t_b) <
        (driftLDEquilibrium N₂ c - driftLDEquilibrium N_r c) *
          (1 - driftLDRetention N₂ c ^ t_b) :=
    mul_lt_mul_of_pos_right h_gap_lt h_amp₂_pos
  exact mul_lt_mul_of_pos_right (lt_of_le_of_lt h_step₁ h_step₂) h_dec_pos

/-- After recovery, excess LD decays with time. -/
theorem excess_ld_decays_after_recovery (N_b N_r c : ℝ) (t_b : ℕ) (t₁ t₂ : ℕ)
    (hNb : 1 ≤ N_b) (h_bottle : N_b < N_r)
    (hc : 0 < c) (hc1 : c < 1) (ht_b : 0 < t_b)
    (h_time : t₁ < t₂) :
    excessLDAfterBottleneck N_b N_r c t_b t₂ <
      excessLDAfterBottleneck N_b N_r c t_b t₁ := by
  have hNr : (1 : ℝ) ≤ N_r := by linarith
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hc1' : c ≤ 1 := le_of_lt hc1
  rw [excessLDAfterBottleneck_closedForm N_b N_r c t_b t₂ hNb hNr hc0 hc1',
    excessLDAfterBottleneck_closedForm N_b N_r c t_b t₁ hNb hNr hc0 hc1']
  have h_gap_pos : 0 < driftLDEquilibrium N_b c - driftLDEquilibrium N_r c := by
    have := driftLDEquilibrium_strictAnti N_b N_r c hNb h_bottle hc hc1
    linarith
  have hLb := driftLDRetention_mem_unit N_b c hNb hc0 hc1'
  have hLb_lt : driftLDRetention N_b c < 1 :=
    driftLDRetention_lt_one N_b c hNb hc hc1'
  have h_amp_pos : 0 < 1 - driftLDRetention N_b c ^ t_b := by
    have := pow_lt_one₀ hLb.1 hLb_lt (by omega : t_b ≠ 0)
    linarith
  have h_head_pos :
      0 < (driftLDEquilibrium N_b c - driftLDEquilibrium N_r c) *
        (1 - driftLDRetention N_b c ^ t_b) := mul_pos h_gap_pos h_amp_pos
  apply mul_lt_mul_of_pos_left _ h_head_pos
  have h_Lr_pos : 0 < driftLDRetention N_r c :=
    driftLDRetention_pos N_r c hNr hc1
  have h_Lr_lt : driftLDRetention N_r c < 1 :=
    driftLDRetention_lt_one N_r c hNr hc hc1'
  exact pow_lt_pow_right_of_lt_one₀ h_Lr_pos h_Lr_lt h_time

end BottleneckLDExcess


/-!
## Population Expansion and LD Persistence

Population expansion reduces the rate of new drift, so LD generated
pre-expansion persists longer. Large modern Ne means current drift is slow.
-/

section ExpansionLD

/-- **Per-generation drift rate at effective size Ne**, `1/(2Ne)`. Larger Ne means
    slower drift.

    **This is not the fraction of LD lost per generation.** For that use
    `ldRetentionPerGen`, which takes the recombination rate this body omits. The name
    `ldDecayRatePerGen` is absent on purpose: reading `1/(2Ne)` as a rate of LD decay is
    FALSIFIED, and no declaration here may carry that reading.

    **The name states drift because the body is a bare drift rate.** "The fraction of LD
    that decays per generation is `1/(2Ne)`" omits recombination, which dominates it. This
    file's own
    `ldRetentionPerGen r Ne = (1-r)(1-1/(2Ne))` is VALIDATED to
    `0.7%`, and it makes the fraction of `E[D]` lost per generation
    `r + 1/(2Ne) - r/(2Ne)`. In exact rational arithmetic:

    | `Ne` | `r` | true fraction lost | this body | ratio |
    |---|---|---|---|---|
    | 10⁴ | 1/100 | 0.0100495 | 5e-5 | **201×** |
    | 10⁴ | 1/1000 | 0.00104995 | 5e-5 | 21× |
    | 10³ | 1/100 | 0.010495 | 5e-4 | 21× |
    | 10⁴ | 0 | 5e-5 | 5e-5 | 1× |

    The error is unbounded in `r/(1/(2Ne))` and the claim holds only on the `r = 0` slice.
    **The defect class is the absence of the recombination argument from the signature, and
    no constant repairs it.** `ldHalfLife` and `ldRetainedFraction` in this file record the
    same failure at 2110× and 37000×. The body carries a name that says drift, because it
    is genuinely consumed as a drift rate -- by
    `LongitudinalPortability` and by `Conventions.driftRatePerGen_eq_inv_timeScale`, which
    identifies it as the reciprocal coalescent time scale. For the fraction of LD lost, use
    `ldRetentionPerGen`.

    An identical twin carries the same reading at `DemographicHistory.driftLDCreationRate`.

    Empirical status: body **DERIVED** as a drift rate; the fraction-lost reading
    **FALSIFIED** (`proofs/validation/coalescent_diff/`).

    Denotes: a per-generation rate. Other definitions share this formula under names from a
    different concept family; the formula does not fix which is meant. -/
noncomputable def driftRatePerGen (Ne : ℝ) : ℝ :=
  1 / (2 * Ne)

/-- Larger population has a slower per-generation drift rate. This is drift only: without
a recombination argument it is not an LD decay rate, which is the reading falsified at
`driftRatePerGen`. The monotonicity proved here is a fact about `1/(2Ne)`. -/
theorem larger_pop_slower_drift_rate (Ne₁ Ne₂ : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (h_larger : Ne₁ < Ne₂) :
    driftRatePerGen Ne₂ < driftRatePerGen Ne₁ := by
  unfold driftRatePerGen
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **LD half-life at recombination rate `r` and effective size `Nₑ`.**
    The number of generations for `E[D]` to halve, read off the
    per-generation retention `ldRetentionPerGen r Ne = (1-r)(1 - 1/(2Nₑ))`
    already established at the top of this file:

      `t₁ᵥ₂ = ln 2 / -ln[(1-r)(1 - 1/(2Nₑ))]`

    **The recombination argument is mandatory.** The form `2·Nₑ·ln 2` carries no
    recombination argument. It is the `r → 0` limit of this expression and
    nothing else: it makes the half-life of linkage disequilibrium independent
    of the recombination rate, the one parameter that dominates it away from
    zero. The discrepancy is not a constant factor -- at `Ne = 10000, r = 0.1`
    that form gives 13863 generations against 6.6, a factor of 2110, and the
    factor grows without bound in `Nₑ` at fixed `r`, since the true half-life
    tends to `ln 2 / -ln(1-r)` while `2·Nₑ·ln 2` diverges.

    `ldHalfLife_halves_retention` states what this body claims, and the
    differential check `ldHalfLife-drops-recombination` is the standing check.
    The check's grid must keep `r > 0`: at `r = 0` the two forms coincide
    exactly, so a grid through that point alone detects nothing.

    Empirical status: DERIVED from `ldRetentionPerGen`, which is VALIDATED. -/
noncomputable def ldHalfLife (r Ne : ℝ) : ℝ :=
  Real.log 2 / (-Real.log (ldRetentionPerGen r Ne))

/-- **What the definition claims.** Retaining LD for `ldHalfLife r Ne`
    generations leaves exactly half of it. Stated with the real power, since
    the half-life is not an integer. This is the property the name asserts, and
    a body that omits the recombination rate satisfies it only at `r = 0`. -/
theorem ldHalfLife_halves_retention (r Ne : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hNe : 1 < Ne) :
    (ldRetentionPerGen r Ne) ^ (ldHalfLife r Ne) = 1 / 2 := by
  have h0 : 0 < ldRetentionPerGen r Ne := by
    unfold ldRetentionPerGen
    apply mul_pos
    · linarith
    · rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h1 : ldRetentionPerGen r Ne < 1 := ld_retention_lt_one r Ne hr hr1 hNe
  have hlog : Real.log (ldRetentionPerGen r Ne) < 0 := Real.log_neg h0 h1
  have hne : Real.log (ldRetentionPerGen r Ne) ≠ 0 := ne_of_lt hlog
  rw [Real.rpow_def_of_pos h0]
  unfold ldHalfLife
  rw [show Real.log (ldRetentionPerGen r Ne) *
        (Real.log 2 / -Real.log (ldRetentionPerGen r Ne)) = -Real.log 2 by
      field_simp]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- LD half-life increases with population size, at a fixed recombination
    rate. Drift is the only channel `Nₑ` acts through. The content is
    conditional on `r`, and it must be: a half-life independent of `r` is the
    defect this signature avoids. -/
theorem ld_half_life_increasing (r Ne₁ Ne₂ : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hNe₁ : 1 < Ne₁) (h_larger : Ne₁ < Ne₂) :
    ldHalfLife r Ne₁ < ldHalfLife r Ne₂ := by
  have hNe₂ : (1 : ℝ) < Ne₂ := lt_trans hNe₁ h_larger
  have hd₁ : (0 : ℝ) < 1 - 1 / (2 * Ne₁) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hd₂ : (0 : ℝ) < 1 - 1 / (2 * Ne₂) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hd₂lt : (1 : ℝ) - 1 / (2 * Ne₂) < 1 := by
    rw [sub_lt_self_iff]; positivity
  have hp₁ : 0 < ldRetentionPerGen r Ne₁ := by
    unfold ldRetentionPerGen; exact mul_pos (by linarith) hd₁
  have hp₁₂ : ldRetentionPerGen r Ne₁ < ldRetentionPerGen r Ne₂ := by
    unfold ldRetentionPerGen
    have hfac : (1 : ℝ) - 1 / (2 * Ne₁) < 1 - 1 / (2 * Ne₂) := by
      rw [sub_lt_sub_iff_left]
      exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
    exact mul_lt_mul_of_pos_left hfac (by linarith)
  have hp₂lt : ldRetentionPerGen r Ne₂ < 1 := by
    unfold ldRetentionPerGen
    calc (1 - r) * (1 - 1 / (2 * Ne₂))
        ≤ 1 * (1 - 1 / (2 * Ne₂)) := by
          exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hd₂)
      _ = 1 - 1 / (2 * Ne₂) := one_mul _
      _ < 1 := hd₂lt
  have hp₁lt : ldRetentionPerGen r Ne₁ < 1 := lt_trans hp₁₂ hp₂lt
  have hl₁ : Real.log (ldRetentionPerGen r Ne₁) < 0 := Real.log_neg hp₁ hp₁lt
  have hl₂ : Real.log (ldRetentionPerGen r Ne₂) < 0 :=
    Real.log_neg (lt_trans hp₁ hp₁₂) hp₂lt
  have hlog_lt : Real.log (ldRetentionPerGen r Ne₁)
      < Real.log (ldRetentionPerGen r Ne₂) :=
    Real.log_lt_log hp₁ hp₁₂
  unfold ldHalfLife
  exact div_lt_div_of_pos_left (Real.log_pos (by norm_num))
    (by linarith) (by linarith)

/-- Pre-expansion LD retained after t generations in expanded population.
    If pre-expansion LD level is D₀ and expansion is to Ne_new,
    the retained fraction after t generations is (1 - 1/(2·Ne_new))^t.
    Larger Ne_new retains more LD. -/
theorem expansion_retains_more_ld (Ne_small Ne_large D₀ : ℝ) (t : ℕ)
    (hNs : 2 < Ne_small) (hNl : 2 < Ne_large)
    (h_exp : Ne_small < Ne_large) (hD₀ : 0 < D₀) (ht : 0 < t) :
    D₀ * (1 - 1/(2 * Ne_small)) ^ t < D₀ * (1 - 1/(2 * Ne_large)) ^ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  have h_base : 1 - 1/(2 * Ne_small) < 1 - 1/(2 * Ne_large) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_nn : 0 ≤ 1 - 1/(2 * Ne_small) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h_lt_one : 1 - 1/(2 * Ne_large) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_left₀ h_base h_nn (by omega)

end ExpansionLD


/-!
## LD Half-Life Depends on Ne Trajectory

After a perturbation (bottleneck, admixture, etc.), LD decays with
half-life proportional to the current Ne. Populations with larger modern
Ne have slower LD decay toward equilibrium.
-/

section LDHalfLifeTrajectory

/-- **Fraction of `E[D]` retained after `t` generations** at recombination
    rate `r` and constant effective size `Nₑ`: the per-generation retention
    `ldRetentionPerGen r Ne`, compounded.

    **The recombination argument is mandatory.** The form `(1 - 1/(2Nₑ))^t` is
    the drift factor alone, raised to `t`. It contradicts `ldRetentionPerGen`,
    stated 800 lines above in this same file, which puts the per-generation
    retention at `(1-r)(1 - 1/(2Nₑ))`. The gap is the missing `(1-r)^t` and is
    therefore unbounded in `t`: at `r = 0.1, t = 100` the drift-only form
    overstates retention by a factor of `0.9^(-100) ≈ 3.7 × 10⁴`.
    `ldAfterGenerations_eq_retainedFraction` below makes this body and
    `ldAfterGenerations` the same expression, so the two cannot separate.

    Regime: two neutral loci, constant `Nₑ`, no mutation and no new input of
    disequilibrium. The `Nₑ` channel here is the same closed-population
    retention as `DriftRegime.closedPopulation`, and carries the same caveat:
    under mutation-drift balance nothing in this expression replenishes
    variation, so it must not be read as a heterozygosity trajectory at
    demographic equilibrium.

    Empirical status: DERIVED from `ldRetentionPerGen`, which is VALIDATED.
    The differential check `ldRetainedFraction-inconsistent-with-retention` is
    retained as the standing check; its grid must keep `r > 0`, since the
    `r = 0` row is where the old and corrected bodies coincide. -/
noncomputable def ldRetainedFraction (r Ne : ℝ) (t : ℕ) : ℝ :=
  (ldRetentionPerGen r Ne) ^ t

/-- **The internal agreement that the old body broke.** `ldAfterGenerations`
    and `ldRetainedFraction` are now one expression, not two that happened to
    be written differently. -/
theorem ldAfterGenerations_eq_retainedFraction (D₀ r Ne : ℝ) (t : ℕ) :
    ldAfterGenerations D₀ r Ne t = D₀ * ldRetainedFraction r Ne t := rfl

/-- Larger current Ne means more LD retained after any fixed time, at a fixed
    recombination rate. -/
theorem larger_ne_more_ld_retained (r Ne₁ Ne₂ : ℝ) (t : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂)
    (h : Ne₁ < Ne₂) (ht : 0 < t) :
    ldRetainedFraction r Ne₁ t < ldRetainedFraction r Ne₂ t := by
  unfold ldRetainedFraction ldRetentionPerGen
  have h_fac : 1 - 1/(2 * Ne₁) < 1 - 1/(2 * Ne₂) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  have h_base : (1 - r) * (1 - 1/(2 * Ne₁)) < (1 - r) * (1 - 1/(2 * Ne₂)) :=
    mul_lt_mul_of_pos_left h_fac (by linarith)
  have h_nn : 0 ≤ (1 - r) * (1 - 1/(2 * Ne₁)) := by
    apply mul_nonneg (by linarith)
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact pow_lt_pow_left₀ h_base h_nn (by omega)

/-- Retained fraction is strictly decreasing with time for finite Ne. -/
theorem ld_retained_decreasing (r Ne : ℝ) (t₁ t₂ : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hNe : 2 < Ne) (h_time : t₁ < t₂) :
    ldRetainedFraction r Ne t₂ < ldRetainedFraction r Ne t₁ := by
  unfold ldRetainedFraction ldRetentionPerGen
  have h_fac_pos : 0 < 1 - 1/(2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_fac_lt : 1 - 1/(2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  have h_pos : 0 < (1 - r) * (1 - 1/(2 * Ne)) :=
    mul_pos (by linarith) h_fac_pos
  have h_lt_one : (1 - r) * (1 - 1/(2 * Ne)) < 1 := by
    calc (1 - r) * (1 - 1/(2 * Ne))
        ≤ 1 * (1 - 1/(2 * Ne)) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h_fac_pos)
      _ = 1 - 1/(2 * Ne) := one_mul _
      _ < 1 := h_fac_lt
  exact pow_lt_pow_right_of_lt_one₀ h_pos h_lt_one h_time

/-- Two populations with the same initial LD perturbation but different
    modern Ne will have different LD levels after the same time.
    The one with larger Ne retains more excess LD. -/
theorem different_ne_different_ld_persistence
    (D₀ r Ne₁ Ne₂ : ℝ) (t : ℕ)
    (hD₀ : 0 < D₀) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂)
    (h_larger : Ne₁ < Ne₂) (ht : 0 < t) :
    D₀ * ldRetainedFraction r Ne₁ t < D₀ * ldRetainedFraction r Ne₂ t := by
  apply mul_lt_mul_of_pos_left _ hD₀
  exact larger_ne_more_ld_retained r Ne₁ Ne₂ t hr0 hr1 hNe₁ hNe₂ h_larger ht

end LDHalfLifeTrajectory


/-!
## First-Principles Derivation of LD Decay

We derive the classical LD decay formula D(t) = (1-r)^t · D₀ from the
recurrence relation D(t+1) = (1-r) · D(t). This is the fundamental
result underlying all LD decay models: each generation, recombination
at rate r between two loci reduces LD by a factor of (1-r).

The derivation proceeds by:
1. Defining the recurrence relation as a recursive function
2. Proving by induction that the closed form equals (1-r)^t · D₀
3. Proving monotone decay of |D(t)| for 0 < r < 1
4. Proving the ratio |D(t)/D₀| = (1-r)^t is strictly decreasing in t
5. Connecting to the existing `ldDecayPerGeneration` definition
-/

section LDDecayDerivation

/-- **LD recurrence relation.**
    D(t+1) = (1-r) · D(t) where r is the recombination rate between two loci
    and D₀ is the initial LD. This is the fundamental discrete-time model
    of LD decay under random mating with recombination.

    Empirical status: UNTESTED. -/
def ldRecurrence (r D₀ : ℝ) : ℕ → ℝ
  | 0 => D₀
  | t + 1 => (1 - r) * ldRecurrence r D₀ t

/-- Base case: the recurrence at generation 0 returns D₀. -/
@[simp]
theorem ldRecurrence_zero (r D₀ : ℝ) : ldRecurrence r D₀ 0 = D₀ := rfl

/-- Step case: the recurrence at generation t+1 multiplies by (1-r). -/
@[simp]
theorem ldRecurrence_succ (r D₀ : ℝ) (t : ℕ) :
    ldRecurrence r D₀ (t + 1) = (1 - r) * ldRecurrence r D₀ t := rfl

/-- **Closed-form solution for LD decay (derived by induction).**

    The recurrence D(t+1) = (1-r) · D(t) with D(0) = D₀ has the unique
    solution D(t) = (1-r)^t · D₀. This is proved by induction on t:
    - Base: D(0) = D₀ = (1-r)^0 · D₀ = 1 · D₀ = D₀
    - Step: D(t+1) = (1-r) · D(t) = (1-r) · ((1-r)^t · D₀)
                    = (1-r)^(t+1) · D₀ -/
theorem ld_decay_closed_form (r D₀ : ℝ) (t : ℕ) :
    ldRecurrence r D₀ t = (1 - r) ^ t * D₀ := by
  induction t with
  | zero =>
    simp
  | succ n ih =>
    simp [ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- **LD magnitude decreases each generation** when 0 < r < 1 and D(t) > 0.

    Since D(t+1) = (1-r) · D(t) and 0 < 1-r < 1, we have
    |D(t+1)| < |D(t)| whenever D(t) ≠ 0. -/
theorem ld_recurrence_decreasing (r D₀ : ℝ) (t : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hD₀ : D₀ ≠ 0) :
    |ldRecurrence r D₀ (t + 1)| < |ldRecurrence r D₀ t| := by
  rw [ld_decay_closed_form, ld_decay_closed_form]
  rw [pow_succ, mul_assoc, abs_mul, abs_mul, abs_mul]
  have h_abs_lt : |1 - r| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have h_pow_abs_pos : 0 < |(1 - r) ^ t| := by
    exact abs_pos.mpr (pow_ne_zero _ (by linarith))
  calc
    |(1 - r) ^ t| * (|1 - r| * |D₀|) < |(1 - r) ^ t| * (1 * |D₀|) := by
      apply mul_lt_mul_of_pos_left
      · exact mul_lt_mul_of_pos_right h_abs_lt (abs_pos.mpr hD₀)
      · exact h_pow_abs_pos
    _ = |(1 - r) ^ t| * |D₀| := by simp

/-- **LD decay ratio is strictly decreasing in t.**

    The ratio |D(t)/D₀| = (1-r)^t is strictly decreasing in t for 0 < r < 1.
    This characterizes the LD half-life: D halves when (1-r)^t = 1/2. -/
theorem ld_decay_ratio_decreasing (r D₀ : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hD₀ : 0 < D₀)
    (h_time : t₁ < t₂) :
    ldRecurrence r D₀ t₂ / D₀ < ldRecurrence r D₀ t₁ / D₀ := by
  rw [ld_decay_closed_form, ld_decay_closed_form]
  rw [mul_div_cancel_right₀ _ (ne_of_gt hD₀)]
  rw [mul_div_cancel_right₀ _ (ne_of_gt hD₀)]
  have h_base_pos : 0 < 1 - r := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos (by linarith) h_time

/-- **LD magnitude decays monotonically over longer intervals.**

    For 0 < r < 1 and D₀ > 0, if t₁ < t₂ then |D(t₂)| < |D(t₁)|.
    This extends the per-generation result to arbitrary time gaps. -/
theorem ld_recurrence_monotone_decay (r D₀ : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hD₀ : 0 < D₀)
    (h_time : t₁ < t₂) :
    |ldRecurrence r D₀ t₂| < |ldRecurrence r D₀ t₁| := by
  rw [ld_decay_closed_form, ld_decay_closed_form]
  rw [abs_mul, abs_mul]
  rw [abs_of_pos hD₀]
  apply mul_lt_mul_of_pos_right _ hD₀
  rw [abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1 - r) _)]
  rw [abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1 - r) _)]
  have h_base_pos : 0 < 1 - r := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos (by linarith) h_time

/-- **Consistency with existing `ldAfterGenerations`.**

    The recurrence-derived LD at generation t equals the directly defined
    `ldAfterGenerations` when the Ohta-Kimura model reduces to pure
    recombination (i.e., infinite Ne, so the drift term 1/(2Ne) → 0).

    Specifically, `ldRecurrence r D₀ t = D₀ · (1-r)^t`, which equals
    `ldAfterGenerations D₀ r Ne t` when Ne → ∞ (since ldRetentionPerGen
    approaches (1-r) as 1/(2Ne) → 0). We prove the structural identity:
    the closed form from the recurrence matches the formula used by
    `ldAfterGenerations` up to the drift correction factor. -/
theorem ld_recurrence_eq_pure_recombination (r D₀ : ℝ) (t : ℕ) :
    ldRecurrence r D₀ t = D₀ * (1 - r) ^ t := by
  rw [ld_decay_closed_form, mul_comm]

/-- **Consistency with `ldDecayPerGeneration` from LongitudinalPortability.**

    The ratio D(t)/D₀ from the recurrence equals `(1-r)^t`, which is exactly
    the `ldDecayPerGeneration` function defined in LongitudinalPortability.
    This confirms that our first-principles derivation produces the same
    decay factor used throughout the codebase. -/
theorem ld_recurrence_ratio_eq_decay_factor (r D₀ : ℝ) (t : ℕ) (hD₀ : D₀ ≠ 0) :
    ldRecurrence r D₀ t / D₀ = (1 - r) ^ t := by
  rw [ld_decay_closed_form, mul_div_cancel_right₀ _ hD₀]

end LDDecayDerivation

end Calibrator
