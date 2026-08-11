/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.SelectionArchitecture
import Descent.PopGen.DriftRegime
import Descent.Portability.PortabilityBounds
import Descent.Portability.PortabilityDrift.PresentDayMoments
import Descent.Portability.PortabilityDrift.MutationDrift
import Descent.Portability.PortabilityDrift.MigrationDrift

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open PopGen.TransportedMetrics (r2FromSignalVariance)

/-!
# Phenome-Wide Portability and Trait-Specific Patterns

This file formalizes why portability varies across traits (Open Question 2)
in greater depth, connecting to phenome-wide association studies (PheWAS)
and the biological mechanisms underlying trait-specific portability.

Key results:
1. Metabolic trait portability and dietary adaptation
2. Anthropometric trait portability
3. Phenome-wide portability correlation structure

Reference: Wang et al. (2026), Nature Communications 17:942.
-/

/-!
## Trait Classification by Portability Pattern

Traits can be classified by how their portability relates to
genetic distance. This classification reflects underlying biology.
-/

section TraitClassification

/-- **Neutral scalar transport baseline.**
    Under pure neutral drift with no selection or GxE, this file uses the
    coarse transport summary `(1 - Fst_additional) * ld_factor`.

    This is a trait-level scalar baseline for downstream comparisons, not a
    literal theorem that the deployed `R²` ratio equals this product.

    Empirical status: **VALIDATED AS TO FORM**, with a residual
    (`simcov/battery_bulk48.py`, `group_ratio`). 2000 variants and 400000
    individuals, with the target differing from the source in TWO independent
    ways: a fraction `fst_additional` of variants stop being shared, and the
    score's tagging is scaled by `ld_factor`. The observable is the realised
    ratio of predictive covariance.

      fst_add  ld_factor   this body   realised ratio
        0.0      1.0        1.00000     1.00312 ± 0.00382
        0.2      1.0        0.80000     0.80511 ± 0.00338
        0.0      0.6        0.60000     0.60166 ± 0.00293
        0.3      0.5        0.35000     0.35990 ± 0.00239
        0.1      0.8        0.72000     0.72373 ± 0.00320

    That the two penalties MULTIPLY is what the design establishes: adding them,
    `(1 - fst_additional) + ld_factor - 1`, is FALSIFIED at 67 sems and 44%
    relative, and the two readings separate only when BOTH penalties bite --
    which is why they are swept independently rather than one at a time.

    The residual is a systematic 2.75% at the worst cell, just over the
    two-percent floor. It sits at the finite-panel scale: `1/√m` is 2.2% at
    `m = 2000`, and the shared-variant fraction is itself a finite draw. It is
    recorded as a residual rather than a falsification because its size tracks
    the panel, not the parameters; a larger panel is the test that would settle
    it.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk48.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_ratio).
    MATCH at worst 1.41 sems; the ADDITIVE reading is FALSIFIED at 41 sems, so the
    product is what the design establishes.
    -/
noncomputable def neutralPortabilityRatioLD (fst_additional ld_factor : ℝ) : ℝ :=
  Descent.Core.retainedFraction fst_additional ld_factor

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem neutralPortabilityRatioLD_at_reference_point :
    neutralPortabilityRatioLD (1 / 2) (1 / 2) = 1 / 4 := by
  unfold neutralPortabilityRatioLD Descent.Core.retainedFraction
  norm_num

/-- **Cross-check: the neutral transport summary and the post-drift score
variance are one map.** `PortabilityDrift.presentDayPGSVariance` attenuates an
ancestral variance by `1 - F_ST`; this attenuates an LD factor by
`1 - F_ST_additional`. Different quantities, one attenuation, and the argument
order is the only thing that differs. -/
theorem neutralPortabilityRatioLD_eq_presentDayPGSVariance
    (fst_additional ld_factor : ℝ) :
    neutralPortabilityRatioLD fst_additional ld_factor =
      presentDayPGSVariance ld_factor fst_additional := by
  unfold neutralPortabilityRatioLD presentDayPGSVariance pgsVarianceFromHet Descent.Core.product
    Descent.Core.retainedFraction; ring

/-- Neutral ratio is in [0, 1] under valid parameters. -/
theorem neutral_ratio_in_unit (fst ld : ℝ)
    (h_fst : 0 ≤ fst) (h_fst1 : fst ≤ 1)
    (h_ld : 0 ≤ ld) (h_ld1 : ld ≤ 1) :
    0 ≤ neutralPortabilityRatioLD fst ld ∧
      neutralPortabilityRatioLD fst ld ≤ 1 := by
  unfold neutralPortabilityRatioLD Descent.Core.retainedFraction
  constructor
  · exact mul_nonneg (by linarith) h_ld
  · calc (1 - fst) * ld ≤ 1 * 1 := by
          apply mul_le_mul (by linarith) h_ld1 h_ld (by linarith)
      _ = 1 := by ring

/-!
### Derivation: Stabilizing Selection Reduces Fst at Causal Loci

Under the Wright-Fisher model, neutral allele frequency drift gives
  Fst_neutral = 1 - (1 - 1/(2*Ne))^t

where Ne is the effective population size and t is the number of generations.
The factor (1 - 1/(2*Ne))^t is the probability that two lineages have NOT
coalesced by generation t -- i.e., the fraction of heterozygosity remaining.

Under stabilizing selection with coefficient s > 0, alleles at causal loci
experience selection pressure that constrains frequency changes. The effective
drift rate is reduced: instead of losing heterozygosity at rate 1/(2*Ne) per
generation, the per-generation loss is 1/(2*Ne) - s_correction, where
s_correction > 0 captures selection maintaining polymorphism.

Concretely, define:
  neutralDriftFactor(Ne, t)      = (1 - 1/(2*Ne))^t
  selectedDriftFactor(Ne, t, s)  = (1 - 1/(2*Ne) + s_correction)^t

where 0 < s_correction < 1/(2*Ne), so the selected drift factor per
generation is strictly larger (closer to 1) than the neutral one but still at
most 1. Both halves of that range are load-bearing and both are now hypotheses
of every theorem below: the lower bound gives the strict inequality, the upper
bound is what keeps `fstFromDriftFactor` from returning a negative F_ST.

Since heterozygosity_selected = H_0 * selectedDriftFactor > H_0 * neutralDriftFactor =
heterozygosity_neutral,
and Fst = 1 - H_between / H_total = 1 - driftFactor (in the island model),
we get:

  Fst_selected = 1 - selectedDriftFactor < 1 - neutralDriftFactor = Fst_neutral

This is the formal justification for the hypothesis fst_causal < fst_neutral
used in the portability theorem below.
-/

/-- **Neutral drift factor per generation.**
    Under Wright-Fisher, the probability of NOT coalescing in one generation
    is (1 - 1/(2*Ne)), and that quantity raised to the t-th power is the
    fraction of ancestral heterozygosity remaining after t generations *in a
    closed population with no mutation*.

    Regime: closed population, no mutation. The qualifier is not decoration: the
    unqualified claim that the retained fraction *is* this power is what measurement
    rejects. Under
    mutation-drift balance heterozygosity is stationary: simulation at
    `Ne = 1000`, `t = 4000` measures the retention as `1.025 ± 0.020` where this
    formula gives `0.135`. `Descent.PopGen.DriftRegime` exhibits the two regimes and
    proves they disagree at every positive time.

    This body is the retention of `closedPopulation`, the regime object that
    carries the falsification. `closedPopulation_het_eq_neutralDriftFactor`
    below ties the two together, so neither copy can carry an empirical status
    the other lacks.

    Empirical status: CONDITIONALLY VALID -- measured inside the closed
    population with no mutation that it declares, and known to fail at
    demographic equilibrium; see `closedPopulation`, which carries both legs of
    the measurement and whose retention this body is. In-regime: forward
    Wright-Fisher at `Ne = 1000` gives 0.90445 ± 0.00094, 0.60311 ± 0.00372 and
    0.13699 ± 0.00272 at `t = 200`, `1000`, `4000` against this formula's
    0.90481, 0.60645 and 0.13527, worst 0.90 sems, with `(1 - 1/(4 Ne))^t`
    excluded at 84.90 sems and `(1 - 1/Ne)^t` at 91.51. The theorems below are
    conditional on that regime holding rather than false. -/
noncomputable def neutralDriftFactor (Ne : ℝ) (t : ℕ) : ℝ :=
  (1 - 1 / (2 * Ne)) ^ t

/-- **neutralDriftFactor at its junk point, named.** An empty population loses all heterozygosity
immediately. The per-generation factor is junk-one and the retention is `1` at every generation
count, so the error does not attenuate with `t` -- it is the multiplicative identity and
persists exactly. Consumers must guard the argument that makes the divisor vanish. -/
theorem neutralDriftFactor_empty_population_is_junk (t : ℕ) :
    neutralDriftFactor 0 t = 1 := by
  unfold neutralDriftFactor
  simp

/-- **This factor is the closed-population regime's retention.**

The tie is to the regime *object*, not to another copy of the formula. That
distinction is the point. A free-standing `driftRetention` used to hold the
same body in `DriftRegime`, and it was removed — correctly — as a copy of a
regime's content that could not record which regime it came from. Had this
identity been stated against that copy it would have died with it; stated
against `closedPopulation` it survives, and it makes the regime and its
falsification reachable from this file by a proof rather than by a comment. -/
theorem closedPopulation_het_eq_neutralDriftFactor (Ne H₀ : ℝ) (hH : 0 < H₀) (t : ℕ) :
    (PopGen.closedPopulation Ne H₀ hH).het t = neutralDriftFactor Ne t * H₀ := by
  simp [PopGen.closedPopulation, neutralDriftFactor]

/-- **Selected drift factor per generation.**
    Under stabilizing selection with correction s_correction, the
    per-generation heterozygosity retention is higher:
    (1 - 1/(2*Ne) + s_correction)^t.
    The s_correction term reflects selection maintaining polymorphism
    at causal loci, reducing the effective drift rate.

    **Admissible range.** `s_correction` must satisfy
    `0 < s_correction < 1/(2*Ne)`. The prose above this definition always said
    so; the definition and every theorem about it used to hypothesize only
    `0 < s_correction`, and above the upper bound the base exceeds `1`, the
    factor grows without bound in `t`, and `fstFromDriftFactor` returns a
    negative `F_ST` that then flows into `causalPortabilityFromLocalFst` and
    `better_than_neutral_implies_stabilizing_selection`. The bound is now in the
    hypotheses of every theorem here, and `selectedDriftFactor_mem_unit` /
    `fst_from_selectedDriftFactor_mem_unit` state the ranges so a replacement
    body that escapes them cannot typecheck.

    **`s_correction` is a free knob, not a derived quantity.** Nothing in this
    file or the corpus defines it in terms of a selection coefficient, a fitness
    function, or a stabilizing-selection model; it is a parameter whose sign and
    magnitude are assumed, and the theorems below establish only what follows
    from those assumptions. Deriving it from a stabilizing-selection model --
    which would fix its dependence on the selection strength, the number of
    loci, and `Ne` -- has not been done, and until it is, the results here are
    conditional on the assumption rather than evidence for it.

    Empirical status: **MIXED** -- VALIDATED at `s_correction = 0` (the
    Wright-Fisher measurement recorded at the end of this docstring), and NOT
    MEASURABLE for general `s_correction`. Both halves are stated below and
    neither supersedes the other; they are joined here because a reader, and
    every scanner, takes the FIRST marker in a docstring as the verdict, and
    either half alone misreports this definition -- `UNTESTED` hides a
    measurement that exists, `VALIDATED` hides that it covers one slice.

    Why the general form is not measurable. The
    paragraph above is the reason: `s_correction` has no operational definition,
    so a simulation cannot set it without inventing one, and whatever the
    simulation then measures is a property of the invention rather than of this
    definition.

    That is not a conjecture about the difficulty. It was attempted
    (`validation/empirical/simcov/battery_bulk7.py`,
    `test_selected_drift_factor`) with a per-generation restoring term standing
    in for `s_correction`, and the result carries the signature of a design
    testing itself: the `s_correction = 0` cell agreed at 0.02 sems, while the
    two cells where the invented term actually bit disagreed at 9.5 and 8.1.
    The verdict gates returned LEAD rather than FALSIFIED, correctly, because no
    positive control had been declared.

    A measurement becomes possible only once the derivation the paragraph
    above says is missing is supplied -- fixing the dependence of `s_correction`
    on selection strength, locus count and `Ne`. Until then this definition is
    counted among the unmeasured, which it is, and no simulation should be built
    against it. A corpus-wide scan
    (`validation/empirical/simcov/unmeasurable_scan.py`) finds this is
    the ONLY definition still marked UNTESTED whose docstring admits its own
    parameter is unpinned, so the category is one definition rather than the
    class it first appeared to be.

    The validated half, in full. **VALIDATED at `s_correction = 0`**
    (`simcov/battery_bulk47.py`, `group_a`). An explicit Wright-Fisher forward
    simulation over 3000 replicate populations and 400 loci; the observable is
    the realised heterozygosity ratio `H_t/H_0`, which IS the drift factor.
    Over `Nₑ` = 50, 100, 200 and `t` = 30, 40, 80, 120 swept independently, the
    body predicts 0.81832, 0.81853, 0.54799 and 0.73970 against measured
    0.81828 ± 0.00003, 0.81855 ± 0.00006, 0.54785 ± 0.00020 and 0.73975 ±
    0.00012 -- worst cell 1.69 sems at 0.01% relative.

    Power: the HAPLOID slip `(1 - 1/Nₑ + s)ᵗ`, which is this law with the
    diploid factor of two dropped, is FALSIFIED at 5848 sems. The two `Nₑ = 100`
    cells at `t = 40` and `t = 120` pin the exponent, and the `(Nₑ, t)` pairs
    (100, 40) and (200, 80) reach nearly the same factor by different routes, so
    a body depending on them separately would separate there.

    The `s_correction` parameter is NOT pinned by this run: it was held at zero
    throughout, which is exactly the gap the paragraph above already records.
    What is established is the drift half of the law.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk47.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_a).
    MATCH at worst 1.42 sems (0.06% relative) at s_correction = 0; the haploid slip is
    FALSIFIED at 532 sems. `s_correction` is still held at zero and is still
    unmeasurable for the reason the paragraphs above give.
    -/
noncomputable def selectedDriftFactor (Ne : ℝ) (t : ℕ) (s_correction : ℝ) : ℝ :=
  (1 - 1 / (2 * Ne) + s_correction) ^ t

/-- **selectedDriftFactor at its junk point, named.** The drift term `1 / (2 * Ne)` is junk-zero at
`Ne = 0`, so the factor reduces to selection alone and an empty population is reported as one in
which drift does nothing. As with `neutralDriftFactor` the error compounds with the generation
count rather than attenuating. Consumers must exclude the argument that makes the guard vanish. -/
theorem selectedDriftFactor_empty_population_is_junk (t : ℕ) (s_correction : ℝ) :
    selectedDriftFactor 0 t s_correction = (1 + s_correction) ^ t := by
  unfold selectedDriftFactor
  simp

/-- **Fst from a drift factor.**
    In the island/drift model, Fst = 1 - driftFactor, where driftFactor
    is the fraction of ancestral heterozygosity retained.

    This map returns a valid `F_ST` only for `driftFactor ∈ (0, 1]`. It has no
    clamp of its own, deliberately: the constraint belongs on the factor it is
    fed, and `fstFromDriftFactor_mem_unit` below states which inputs are
    admissible. Feeding it a factor above `1` -- which `selectedDriftFactor`
    used to permit -- returns a negative `F_ST`.

    **Inherited falsification.** This body, `1 - driftFactor`, is innocent: it
    is an involution on the unit interval and carries no regime of its own. But
    an innocent body fed a falsified input yields a falsified result, and the
    input this file supplies is `neutralDriftFactor`, which is falsified at
    demographic equilibrium. So every value computed here through that route
    inherits the closed-population, no-mutation regime, and nothing in this
    definition's signature or body records that. It is written down here because
    an inheritance of that kind is invisible otherwise: a reader checking this
    definition alone finds nothing wrong with it, which is the whole difficulty.

    Denotes: the reading its name carries. The same formula appears under
    names from 'factor', 'frequency', 'fst', and the formula alone does not fix which is meant.

    Empirical status: **VALIDATED** (`simcov/battery_bulk47.py`, `group_a`), on
    the same Wright-Fisher runs that measure `selectedDriftFactor`. The
    observable is `1 - H_t/H_0`, the realised fraction of ancestral
    heterozygosity lost, against `1 - driftFactor`; worst cell 1.69 sems at
    0.02% relative.

    Which `F` this is, since the docstring above warns the formula does not fix
    it: the PER-BRANCH drift coefficient, Wright's `F` measured against the
    ancestor within ONE lineage. It is not the pairwise Hudson `F_ST` of
    `PortabilityDrift.fstFromTau`, which is `τ/(1+τ)` and which this corpus
    proves is strictly smaller at every positive `τ`. The simulation measures a
    single population losing heterozygosity, so it measures the per-branch
    reading and nothing else.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_bulk47.py` is now in the repository, was run against
    the design described above, and its results are committed beside it (group_a).
    MATCH at worst 1.42 sems (0.29% relative) read as the LOSS on the same runs; the
    haploid drift factor is FALSIFIED at 532 sems.
    -/
noncomputable def fstFromDriftFactor (driftFactor : ℝ) : ℝ :=
  Descent.Core.complement driftFactor

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem fstFromDriftFactor_at_reference_point :
    fstFromDriftFactor (1 / 2) = 1 / 2 := by
  unfold fstFromDriftFactor Descent.Core.complement
  norm_num

/-- **Cross-check: `1 - F_ST` read forwards and backwards.**
`PortabilityDrift.covarianceRetentionFactorFromFst` sends `F_ST` to the retained
frequency correlation; `fstFromDriftFactor` sends the retained drift factor
back to `F_ST`. They are the same involution, and stating it keeps the two
directions from acquiring different conventions. -/
theorem fstFromDriftFactor_eq_covarianceRetentionFactorFromFst (driftFactor : ℝ) :
    fstFromDriftFactor driftFactor = covarianceRetentionFactorFromFst driftFactor := by
  unfold fstFromDriftFactor covarianceRetentionFactorFromFst Descent.Core.complement; ring

/-- **The third spelling of the same involution.**

`DriftRegime.lossOfRetention` sends a closed-population retention to the heterozygosity
lost with it. It is `1 - ·` again, so it agrees numerically with the two `F_ST` readings
above. The three readings stay separate on purpose — a within-population loss, a
between-population `F_ST`, and a retained frequency correlation are different quantities,
and `DriftRegime` records what substituting one for another cost — but the map they share
is written down here, so a convention change in any one of them contradicts this. This
module is where all three are visible at once. -/
theorem lossOfRetention_eq_fstFromDriftFactor_eq_covarianceRetentionFactorFromFst (r : ℝ) :
    PopGen.lossOfRetention r = fstFromDriftFactor r ∧
      PopGen.lossOfRetention r = covarianceRetentionFactorFromFst r :=
  ⟨rfl, rfl⟩

/-- **`F_ST` from an admissible drift factor lies in `[0, 1)`.**
    The range constraint, stated so that a replacement body producing values
    outside it does not typecheck as this definition. -/
theorem fstFromDriftFactor_mem_unit (driftFactor : ℝ)
    (h_pos : 0 < driftFactor) (h_le : driftFactor ≤ 1) :
    0 ≤ fstFromDriftFactor driftFactor ∧ fstFromDriftFactor driftFactor < 1 := by
  unfold fstFromDriftFactor Descent.Core.complement
  exact ⟨by linarith, by linarith⟩

/-- **The neutral drift factor is an admissible input**: it lies in `(0, 1]`. -/
theorem neutralDriftFactor_mem_unit (Ne : ℝ) (t : ℕ)
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) (h_base_le : 1 - 1 / (2 * Ne) ≤ 1) :
    0 < neutralDriftFactor Ne t ∧ neutralDriftFactor Ne t ≤ 1 := by
  unfold neutralDriftFactor
  exact ⟨pow_pos h_base_pos t, pow_le_one₀ (le_of_lt h_base_pos) h_base_le⟩

/-- **The selected drift factor is an admissible input**, but only inside the
    stated range for `s_correction`. Above `1/(2*Ne)` the per-generation base
    exceeds `1` and this fails -- which is how a negative `F_ST` used to reach
    the portability results. -/
theorem selectedDriftFactor_mem_unit (Ne : ℝ) (t : ℕ) (s_correction : ℝ)
    (h_s_pos : 0 < s_correction)
    (h_s_lt : s_correction < 1 / (2 * Ne))
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) :
    0 < selectedDriftFactor Ne t s_correction ∧
      selectedDriftFactor Ne t s_correction ≤ 1 := by
  unfold selectedDriftFactor
  have h_pos : 0 < 1 - 1 / (2 * Ne) + s_correction := by linarith
  have h_le : 1 - 1 / (2 * Ne) + s_correction ≤ 1 := by linarith
  exact ⟨pow_pos h_pos t, pow_le_one₀ (le_of_lt h_pos) h_le⟩

/-- **`F_ST` at selected loci stays in `[0, 1)`.** This is the bound the old
    hypotheses did not enforce: with only `0 < s_correction`, this quantity went
    negative and fed `causalPortabilityFromLocalFst` and
    `better_than_neutral_implies_stabilizing_selection` unchecked. -/
theorem fst_from_selectedDriftFactor_mem_unit (Ne : ℝ) (t : ℕ) (s_correction : ℝ)
    (h_s_pos : 0 < s_correction)
    (h_s_lt : s_correction < 1 / (2 * Ne))
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) :
    0 ≤ fstFromDriftFactor (selectedDriftFactor Ne t s_correction) ∧
      fstFromDriftFactor (selectedDriftFactor Ne t s_correction) < 1 := by
  obtain ⟨hp, hle⟩ :=
    selectedDriftFactor_mem_unit Ne t s_correction h_s_pos h_s_lt h_base_pos
  exact fstFromDriftFactor_mem_unit _ hp hle

/-- **Selected drift factor exceeds neutral drift factor.**
    Since s_correction > 0, the per-generation retention rate is strictly
    higher for selected loci, and raising to the t-th power preserves
    the strict inequality (for t ≥ 1). -/
theorem selected_drift_factor_gt_neutral (Ne : ℝ) (t : ℕ) (s_correction : ℝ)
    (h_s_pos : 0 < s_correction)
    (h_t_pos : 1 ≤ t)
    -- the neutral per-generation factor is positive
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) :
    neutralDriftFactor Ne t < selectedDriftFactor Ne t s_correction := by
  unfold neutralDriftFactor selectedDriftFactor
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 - 1 / (2 * Ne) + s_correction := by
    linarith
  exact pow_lt_pow_left₀ h_base_lt (le_of_lt h_base_pos) (by omega)

/-- **Stabilizing selection reduces Fst at causal loci.**
    From the drift factor inequality, we derive:
    Fst_selected = 1 - selectedDriftFactor < 1 - neutralDriftFactor = Fst_neutral.

    This is the key population genetics result: stabilizing selection
    maintains shared polymorphism across populations, reducing divergence
    at causal loci relative to neutral sites. -/
theorem stabilizing_selection_reduces_fst (Ne : ℝ) (t : ℕ) (s_correction : ℝ)
    (h_s_pos : 0 < s_correction)
    (h_s_lt : s_correction < 1 / (2 * Ne))
    (h_t_pos : 1 ≤ t)
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) :
    0 ≤ fstFromDriftFactor (selectedDriftFactor Ne t s_correction) ∧
      fstFromDriftFactor (selectedDriftFactor Ne t s_correction) <
        fstFromDriftFactor (neutralDriftFactor Ne t) := by
  constructor
  · exact (fst_from_selectedDriftFactor_mem_unit Ne t s_correction
      h_s_pos h_s_lt h_base_pos).1
  · unfold fstFromDriftFactor Descent.Core.complement
    linarith [selected_drift_factor_gt_neutral Ne t s_correction
      h_s_pos h_t_pos h_base_pos]

/-- **Corollary: Fst at causal loci is strictly less than Fst at neutral loci.**
    This is the exact condition needed by the portability theorem below.
    We phrase it in terms of raw real-valued Fst parameters to connect
    the Wright-Fisher derivation to the portability framework. -/
theorem fst_causal_lt_fst_neutral_of_stabilizing_selection
    (Ne : ℝ) (t : ℕ) (s_correction : ℝ)
    (h_s_pos : 0 < s_correction)
    (h_s_lt : s_correction < 1 / (2 * Ne))
    (h_t_pos : 1 ≤ t)
    (h_base_pos : 0 < 1 - 1 / (2 * Ne)) :
    fstFromDriftFactor (selectedDriftFactor Ne t s_correction) <
      fstFromDriftFactor (neutralDriftFactor Ne t) := by
  exact (stabilizing_selection_reduces_fst Ne t s_correction
    h_s_pos h_s_lt h_t_pos h_base_pos).2

/-- Effect-size-weighted retained causal portability from a locus-specific
causal-`F_ST` profile, resolved per locus rather than as a trait-wide scalar.

    Empirical status: **VALIDATED** (`simcov/battery_gap01.py`,
    `group_turnover`), with one thing the design does NOT separate, stated
    below.

    The independent test the paragraph after this one asks for has been run. 800
    causal loci are drifted by explicit Wright-Fisher for `t` generations at
    census `Nₑ`, so the per-locus `F_ST` profile is REALISED rather than drawn;
    the observable is the ratio of realised predictive covariance in the drifted
    population to that in the source -- the retained causal signal -- and the
    body is evaluated at the realised drift indices. Worst cell 1.10 sems at
    0.70% relative over `(Nₑ, t)` = (200, 40), (100, 60), (400, 40).

    Power: the PAIRWISE reading, effect-mass-weighted `1 - 2·F`, is FALSIFIED at
    22.3 sems and 30% relative. NOT separated: the UNWEIGHTED mean of `1 - F`
    matches at 2.58 sems. Effect sizes and drift indices are independent in this
    design, so the weighting has nothing to bite on; a design correlating `β²`
    with `F` -- which is what selection would produce -- is what would separate
    them, and this run does not claim to have.

    Two details that were faults in earlier attempts and are now design
    decisions. Both populations are scaled by the SOURCE heterozygosity, because
    a transported score carries the weights it was fitted with on the scale it
    was fitted on; restandardising the target divides out exactly the
    heterozygosity loss `1 - fstCausal` is a claim about, and the measured ratio
    then returns 1 whatever the drift was. And the realised `F` is NOT clipped
    to `[0, 1]`: drift raises heterozygosity at some loci, and clipping those to
    zero feeds the body a profile the simulation did not realise -- worth 15
    sems on its own.

    THE EARLIER NON-TEST, kept so it is not repeated
    (`validation/empirical/simcov/battery_bulk6.py`). That battery built
    the oracle by evaluating this same effect-mass-weighted average over drawn
    per-locus drift indices, so the oracle WAS the formula: it agreed to machine
    precision in every cell and the harness returns SELF-TEST. -/
noncomputable def causalPortabilityFromLocalFst {m : ℕ}
    (sourceSquaredEffect fstCausal : Fin m → ℝ) : ℝ :=
  (∑ i, sourceSquaredEffect i * (1 - fstCausal i)) /
    (∑ i, sourceSquaredEffect i)

/-- **causalPortabilityFromLocalFst at empty index, named.** With no causal variants both the
retained and the total effect mass are empty sums. Lean returns `0`: no portability at all, which
is what a score whose every effect fails to transfer also gives. A missing panel and a completely
non-portable one are reported identically. Consumers must exclude it by hypothesis. -/
theorem causalPortabilityFromLocalFst_empty_panel_is_junk
    (sourceSquaredEffect fstCausal : Fin 0 → ℝ) :
    causalPortabilityFromLocalFst sourceSquaredEffect fstCausal = 0 := by
  unfold causalPortabilityFromLocalFst
  simp

/-- The locus-level causal portability chart is exactly one minus the
effect-size-weighted average causal `F_ST`. -/
private theorem causalPortabilityFromLocalFst_eq_one_sub_weightedLocalFst {m : ℕ}
    (sourceSquaredEffect fstCausal : Fin m → ℝ)
    (h_weight_pos : 0 < ∑ i, sourceSquaredEffect i) :
    causalPortabilityFromLocalFst sourceSquaredEffect fstCausal =
      1 - (∑ i, sourceSquaredEffect i * fstCausal i) /
        (∑ i, sourceSquaredEffect i) := by
  unfold causalPortabilityFromLocalFst
  have hW_ne : (∑ i, sourceSquaredEffect i) ≠ 0 := ne_of_gt h_weight_pos
  calc
    (∑ i, sourceSquaredEffect i * (1 - fstCausal i)) /
        (∑ i, sourceSquaredEffect i)
        =
          ((∑ i, sourceSquaredEffect i) -
            ∑ i, sourceSquaredEffect i * fstCausal i) /
            (∑ i, sourceSquaredEffect i) := by
              congr 1
              calc
                ∑ i, sourceSquaredEffect i * (1 - fstCausal i)
                    = ∑ i, (sourceSquaredEffect i - sourceSquaredEffect i * fstCausal i) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                _ = (∑ i, sourceSquaredEffect i) -
                      ∑ i, sourceSquaredEffect i * fstCausal i := by
                        rw [Finset.sum_sub_distrib]
    _ = 1 - (∑ i, sourceSquaredEffect i * fstCausal i) /
          (∑ i, sourceSquaredEffect i) := by
          field_simp [hW_ne]

/-- If no effect-bearing causal locus is less differentiated than the neutral
background, then the locus-level causal portability chart cannot exceed the
neutral expectation. -/
private theorem causalPortabilityFromLocalFst_le_neutral_of_no_subneutral_effect_locus
    {m : ℕ}
    (sourceSquaredEffect fstCausal : Fin m → ℝ)
    (fst_neutral : ℝ)
    (h_nonneg : ∀ i, 0 ≤ sourceSquaredEffect i)
    (h_weight_pos : 0 < ∑ i, sourceSquaredEffect i)
    (h_no_subneutral : ∀ i, 0 < sourceSquaredEffect i → fst_neutral ≤ fstCausal i) :
    causalPortabilityFromLocalFst sourceSquaredEffect fstCausal ≤ 1 - fst_neutral := by
  have hsum :
      fst_neutral * (∑ i, sourceSquaredEffect i) ≤
        ∑ i, sourceSquaredEffect i * fstCausal i := by
    calc
      fst_neutral * (∑ i, sourceSquaredEffect i)
          = ∑ i, sourceSquaredEffect i * fst_neutral := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ ≤ ∑ i, sourceSquaredEffect i * fstCausal i := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hpos : 0 < sourceSquaredEffect i
            · exact mul_le_mul_of_nonneg_left (h_no_subneutral i hpos) (le_of_lt hpos)
            · have hzero : sourceSquaredEffect i = 0 := by
                have hnn := h_nonneg i
                linarith
              simp [hzero]
  have hweighted :
      fst_neutral ≤
        (∑ i, sourceSquaredEffect i * fstCausal i) /
          (∑ i, sourceSquaredEffect i) := by
    exact (le_div_iff₀ h_weight_pos).2 hsum
  rw [causalPortabilityFromLocalFst_eq_one_sub_weightedLocalFst
    sourceSquaredEffect fstCausal h_weight_pos]
  linarith

/-- **Above-neutral portability forces a stabilizing-like causal locus signature.**
    If the observed portability for a trait exceeds the neutral expectation on
    the exact locus-level causal-`F_ST` chart, then some effect-bearing causal
    locus must have lower-than-neutral divergence. This connects the phenome-
    wide "better than neutral" pattern to a concrete SNP-level signature. -/
theorem better_than_neutral_implies_stabilizing_selection
    {m : ℕ}
    (sourceSquaredEffect fstCausal : Fin m → ℝ)
    (fst_neutral : ℝ)
    (h_nonneg : ∀ i, 0 ≤ sourceSquaredEffect i)
    (h_weight_pos : 0 < ∑ i, sourceSquaredEffect i)
    (h_better :
      1 - fst_neutral < causalPortabilityFromLocalFst sourceSquaredEffect fstCausal) :
    ∃ i : Fin m, 0 < sourceSquaredEffect i ∧ fstCausal i < fst_neutral := by
  by_contra h_no
  push_neg at h_no
  have h_le :
      causalPortabilityFromLocalFst sourceSquaredEffect fstCausal ≤ 1 - fst_neutral := by
    exact causalPortabilityFromLocalFst_le_neutral_of_no_subneutral_effect_locus
      sourceSquaredEffect fstCausal fst_neutral h_nonneg h_weight_pos h_no
  linarith

/-- **Below-neutral portability plus selected-variance excess is matched by a
fluctuating/diversifying selection regime.**
    A subunit observed cross-population effect correlation by itself is not yet
    a regime label. But if the same trait also has selected-architecture
    variance above the stabilizing mutation-selection baseline, then the
    observed summary is matched exactly by a fluctuating-selection regime. For
    fixed drift coordinates, that same observed effect correlation forces the
    portability ratio below the neutral drift baseline.

    A MATCH, not an identification: excluding a stabilizing regime on the
    correlation coordinate would need a law for the cross-population effect
    correlation a stabilizing regime produces, and the corpus carries none. -/
theorem worse_than_neutral_matched_by_fluctuating_regime
    (v_mutation s t rho_obs v_selected_obs V_A V_E fstS fstT : ℝ)
    (h_t : 0 < t)
    (h_rho : 0 < rho_obs) (h_rho_lt : rho_obs < 1)
    (h_var_gap : PopGen.stabilizingSelectedArchitectureVariance v_mutation s < v_selected_obs)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1) :
    let tau_hat := PopGen.tauFromObservedEffectCorrelation t rho_obs
    let sigma_hat :=
      PopGen.sigmaThetaFromObservedSelectedVariance v_selected_obs v_mutation s t rho_obs
    let observed_ratio :=
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rho_obs) V_E /
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E
    let neutral_ratio :=
      PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E
    (0 < tau_hat ∧
      0 < sigma_hat ∧
      PopGen.fluctuatingEffectCorrelation t tau_hat = rho_obs ∧
      PopGen.fluctuatingSelectedArchitectureVariance v_mutation s sigma_hat tau_hat =
        v_selected_obs) ∧
      observed_ratio < neutral_ratio := by
  dsimp
  have h_match :
      0 < PopGen.tauFromObservedEffectCorrelation t rho_obs ∧
        0 <
          PopGen.sigmaThetaFromObservedSelectedVariance
            v_selected_obs v_mutation s t rho_obs ∧
        PopGen.fluctuatingEffectCorrelation t
            (PopGen.tauFromObservedEffectCorrelation t rho_obs) = rho_obs ∧
        PopGen.fluctuatingSelectedArchitectureVariance v_mutation s
            (PopGen.sigmaThetaFromObservedSelectedVariance
              v_selected_obs v_mutation s t rho_obs)
            (PopGen.tauFromObservedEffectCorrelation t rho_obs) = v_selected_obs := by
    exact PopGen.observedSummary_matched_by_fluctuating_regime
      v_mutation s t rho_obs v_selected_obs h_t h_rho h_rho_lt h_var_gap
  have h_port :
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rho_obs) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    simpa [realWorldPGSVariance, presentDayPGSVariance, pgsVarianceFromHet, Descent.Core.product,
      mul_comm] using
      portability_ratio_with_ld_decay V_A V_E fstS fstT 1 rho_obs
        hVA hVE hfst hfstT_lt_one rfl ⟨h_rho, h_rho_lt⟩
  exact ⟨h_match, h_port⟩

/-- **Scalar three-factor portability upper bound.**
    This is only the coarse scalar inequality
    `r2_source × (1 - fst) × ρ² × ld_factor ≤ r2_source`
    under unit-bounded factors. It is not the file's mechanistic SNP-level
    portability law. -/
theorem scalar_three_factor_portability_upper_bound
    (r2_source fst rho ld_factor : ℝ)
    (h_r2 : 0 ≤ r2_source)
    (h_fst : 0 ≤ fst)
    (h_rho : 0 ≤ rho) (h_rho_le : rho ≤ 1)
    (h_ld : 0 ≤ ld_factor) (h_ld_le : ld_factor ≤ 1) :
    r2_source * (1 - fst) * rho ^ 2 * ld_factor ≤ r2_source := by
  have h_rho_sq_le : rho ^ 2 ≤ 1 := pow_le_one₀ h_rho h_rho_le
  have h_rho_ld_le : rho ^ 2 * ld_factor ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h_rho_sq_le) (sub_nonneg.mpr h_ld_le)]
  have h_factor_le : (1 - fst) * rho ^ 2 * ld_factor ≤ 1 := by
    nlinarith [mul_nonneg (mul_nonneg h_fst (sq_nonneg rho)) h_ld]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_factor_le h_r2

end TraitClassification

/-!
## Immune Trait Portability

Immune-related traits consistently show worse portability than
neutral expectation, reflecting pathogen-driven divergent selection.
-/

section ImmuneTraits

end ImmuneTraits

/-!
## Metabolic Trait Portability

Metabolic traits show intermediate portability, reflecting
dietary adaptation across populations.
-/

section MetabolicTraits

/-- **GxE reduces cross-population effect correlation.**
    Model: In pop1, effect of variant i is β_i.
    In pop2, effect is β_i + δ_i where δ_i is the GxE perturbation.

    Without GxE (δ = 0): cross-pop correlation of effects = 1.
    With GxE (δ ≠ 0): correlation < 1 because δ adds uncorrelated noise.

    Formally, if σ²_β is the variance of true effects and σ²_δ is the
    GxE perturbation variance (uncorrelated with β), then:
      ρ_with_gxe = σ²_β / √(σ²_β * (σ²_β + σ²_δ))
                  = √(σ²_β / (σ²_β + σ²_δ))

    Since σ²_δ > 0, the denominator exceeds the numerator. -/
theorem gxe_reduces_effect_correlation
    (sigma2_beta sigma2_delta : ℝ)
    (h_beta_pos : 0 < sigma2_beta) (h_delta_pos : 0 < sigma2_delta) :
    let rho_genetics_only := (1 : ℝ)  -- no GxE means perfect correlation
    let rho_with_gxe := Real.sqrt (sigma2_beta / (sigma2_beta + sigma2_delta))
    rho_with_gxe < rho_genetics_only := by
  simp only
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_one (by linarith)]
  linarith

/-- **Larger GxE variance lowers the scalar portability fraction.**
    In the scalar chart `port(delta) = σ²_β / (σ²_β + delta)`, a larger
    environmental perturbation variance yields a smaller portability fraction.
    This theorem proves the extreme comparison `port_trig < port_ldl` from that
    denominator ordering. -/
theorem larger_gxe_variance_lowers_scalar_portability_fraction
    (sigma2_beta sigma2_delta_ldl sigma2_delta_hdl sigma2_delta_trig : ℝ)
    (h_beta_pos : 0 < sigma2_beta)
    (h_ldl_nn : 0 ≤ sigma2_delta_ldl)
    -- GxE increases from LDL → HDL → Triglycerides
    (h_ldl_lt_hdl : sigma2_delta_ldl < sigma2_delta_hdl)
    (h_hdl_lt_trig : sigma2_delta_hdl < sigma2_delta_trig) :
    let port (delta : ℝ) := sigma2_beta / (sigma2_beta + delta)
    port sigma2_delta_trig < port sigma2_delta_ldl := by
  simp only
  apply div_lt_div_of_pos_left h_beta_pos (by linarith) (by linarith)

end MetabolicTraits

/-!
## Anthropometric Trait Portability

Height and body proportions show relatively good portability,
suggesting largely neutral genetic architecture for the common
variants captured by GWAS.
-/

section AnthropometricTraits

/-- **`1 - (1 - c/n)² < 2c/n`.**

    Renamed from `near_neutral_portability_highly_polygenic`, which claimed a
    population-genetic result the statement does not contain. What is proved is the
    algebraic fact that expanding `1 - (1 - δ)²` leaves `2δ - δ²`, strictly below `2δ`
    whenever `δ ≠ 0`. It holds for every real `c` and every `n ≥ 2`; nothing in it is
    specific to portability, and nothing in it degrades as `n` grows.

    The former docstring supplied the missing half as prose: that under the infinitesimal
    model with a per-locus selection coefficient `s` across `n` loci, the cross-population
    effect correlation is `ρ = 1 - c/n`, so that `1 - ρ²` is the portability gap. That
    identification is the entire scientific claim and it is **assumed, not derived** —
    there is no `s` in the statement, no locus count beyond a bare `n : ℕ`, no effect
    correlation, and no derivation anywhere in this corpus fixing `ρ` to that form. The
    unused `c ≤ 1` was the only thing tying `c` to a correlation scale, and dropping it
    costs the theorem nothing, which is the measure of how little the model was doing.

    Read as an inequality it is correct and cheap. Read as "highly polygenic traits are
    near-neutrally portable" it was an unproved population-genetic assertion resting on an
    `O(1/n)` scaling argument that appears in no statement. -/
theorem one_sub_sq_one_sub_div_lt_two_mul_div
    (c : ℝ) (n : ℕ)
    (h_c_pos : 0 < c)
    (h_n_large : 1 < n) :
    1 - (1 - c / n) ^ 2 < 2 * c / n := by
  have h_n_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  -- gap = 1 - (1 - c/n)² = 2c/n - (c/n)²
  have h_expand : 1 - (1 - c / ↑n) ^ 2 = 2 * c / ↑n - (c / ↑n) ^ 2 := by ring
  rw [h_expand]
  -- Need: 2c/n - (c/n)² < 2c/n, i.e., 0 < (c/n)²
  have : 0 < (c / ↑n) ^ 2 := by positivity
  linarith

/-- **Per-locus variance share is bounded by locus count in the equal-effect
chart.**
    If total variance is `n_loci * per_locus_var`, then each locus contributes
    exactly `1 / n_loci` of the total, hence strictly less than `1 / n_threshold`
    whenever `n_threshold < n_loci`. This is a counting identity, not by itself
    a mechanistic portability theorem. -/
theorem equal_share_lt_one_div_of_lt
    (n_loci n_threshold : ℕ) (per_locus_var total_var : ℝ)
    (h_many : n_threshold < n_loci) (h_thresh_pos : 0 < n_threshold)
    (h_total : total_var = n_loci * per_locus_var)
    (h_var_pos : 0 < per_locus_var) :
    -- Each locus contributes < 1/n_threshold of total variance
    per_locus_var / total_var < 1 / n_threshold := by
  rw [h_total]
  rw [show per_locus_var / (↑n_loci * per_locus_var) = 1 / ↑n_loci from by
    field_simp]
  have h_n_pos : (0 : ℝ) < ↑n_loci := Nat.cast_pos.mpr (by omega)
  have h_t_pos : (0 : ℝ) < ↑n_threshold := Nat.cast_pos.mpr h_thresh_pos
  rw [div_lt_div_iff₀ h_n_pos h_t_pos]
  have : (n_threshold : ℝ) < (n_loci : ℝ) := by exact_mod_cast h_many
  linarith

/-- **An `α < 1` upper bound forces portability below the reference trait.**
    If `port_selected < α * port_reference` with `0 < α < 1`, then the selected
    trait's portability is strictly below the reference portability. -/
theorem lt_of_lt_mul_of_lt_one
    (port_reference port_selected α : ℝ)
    (h_much_worse : port_selected < α * port_reference)
    (h_ref_pos : 0 < port_reference) (h_α_lt : α < 1) (h_α_pos : 0 < α) :
    port_selected < port_reference := by nlinarith

end AnthropometricTraits

/-!
## Phenome-Wide Portability Correlation Structure

Portability across traits is correlated: traits with similar
genetic architecture show similar portability patterns.
-/

section PhenomeWideStructure

/-- **Pearson `R²` is strictly below `1` under additive prediction noise.**
    For the scalar model `Y = aX + ε` with `σ²_ε > 0`, the induced
    `pearson_r2 = (aσ_X)^2 / ((aσ_X)^2 + σ²_ε)` is strictly below `1`.
    This file does not prove a separate rank-correlation theorem here; it only
    proves the Pearson bound. -/
theorem pearson_r2_below_one_under_additive_noise
    (a sigma_x sigma_eps : ℝ) (h_se_pos : 0 < sigma_eps) :
    -- Pearson r² for Y = aX + ε is a²σ²_X / (a²σ²_X + σ²_ε) < 1
    let pearson_r2 := (a * sigma_x) ^ 2 / ((a * sigma_x) ^ 2 + sigma_eps ^ 2)
    pearson_r2 < 1 := by
  simp only
  rw [div_lt_one (by positivity)]
  have : 0 < sigma_eps ^ 2 := by positivity
  linarith

end PhenomeWideStructure

theorem neutralDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) :
    Portability.neutralDriftFactor Ne t = (1 - 1 / Descent.Core.coalescentTimeScale Ne) ^ t := by
  unfold Portability.neutralDriftFactor; rw [Descent.Core.coalescentTimeScale_eq]

theorem selectedDriftFactor_uses_timeScale (Ne : ℝ) (t : ℕ) (s_correction : ℝ) :
    Portability.selectedDriftFactor Ne t s_correction
      = (1 - 1 / Descent.Core.coalescentTimeScale Ne + s_correction) ^ t := by
  unfold Portability.selectedDriftFactor; rw [Descent.Core.coalescentTimeScale_eq]

theorem heterozygosityLossFromDrift_eq_closedPopulation_measuredLoss
    (t : ℕ) (Ne H₀ : ℝ) (hH : 0 < H₀) :
    PopGen.heterozygosityLossFromDrift t Ne = (PopGen.closedPopulation Ne H₀ hH).measuredLoss t
      := by
  rw [PopGen.measuredLoss_closedPopulation]
  unfold PopGen.heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement
    Descent.Core.geometricDecay
  rfl

/-!
## The composed clean-split transport prediction

A CLEAN TWO-BRANCH SPLIT is the simplest demographic history a portability law can be asked
about: one ancestral population, two closed descendant branches, no migration between them
and no mutation regime. Everything the corpus needs for an end-to-end prediction under that
history is here — `neutralDriftFactor` for the retention in each branch, `fstFromDriftFactor`
for the drift index it implies, `neutralPortability` for the `R²` a given index transports,
the multiplicative LD penalty of `neutralPortabilityRatioLD`, and
`liabilityThresholdAUCFromExplainedR2` for the conversion to discrimination — so that a
battery has a single name to aim at instead of a chain a reader has to assemble by hand.

THE TWO BRANCHES ARE NOT INTERCHANGEABLE, and that is the correction this section carries.
A composition that summed the two per-branch indices and fed the sum to `neutralPortability`
was FALSIFIED by `simcov/battery_clean01.py` at 66.51 sems, 56% low at the deepest cell, with
a miss growing monotonically in the argument — a wrong functional form and not a wrong
constant. The TARGET branch's drift attenuates a signal the score still carries, which is what
`neutralPortability` charts. The SOURCE branch's drift does something the chart has no slot
for: it FIXES variants, and a variant fixed in the source leaves the score altogether while
its variance stays in the target phenotype as unexplained heritable variance. A single index
cannot stand for both operations, so `cleanSplitTargetR2'` charts the target branch alone and
gives the source branch a factor of its own.

THE ANCESTRAL SPECTRUM IS A NECESSARY ARGUMENT and not a decoration. Holding the source's
effective size and the split time fixed — hence holding its own drift index fixed — and
varying only the ancestral allele-frequency spectrum moves the lost signal fraction by a
factor of 51 at `t = 100` and 1.9 at `t = 1100`. The source branch's contribution is a
functional of the spectrum, not a function of its drift index, which is why no rescaling
repairs a summed-index body and why the signatures below carry per-variant weights and
frequencies rather than one number.

THE SUMMATION CONVENTION IN `cleanSplitFst` SURVIVES ALL OF THAT, because what the run
rejected is not the sum. `fstFromDriftFactor` returns the PER-BRANCH drift coefficient —
Wright's `F` measured against the ancestor within ONE lineage — and its own docstring says so,
distinguishing it from the pairwise Hudson `F_ST`. Per-branch indices ADD over independent
branches, which is the convention `expectedSqMeanPGSDiff_pureSplit` feeds `Var_Delta_Mu` and
which that definition's docstring records as adjudicated after a two-branch design fed a
pairwise value produced a factor-of-four false falsification TWICE. `cleanSplitFst` therefore
sums, and a battery that fed it a pairwise value would be repeating an error the corpus has
already paid for twice. What the run rejected is that sum in a portability chart's `fst` slot.

THE SUM IS NOT CONFINED TO THE UNIT INTERVAL. Each branch index lies in `[0,1)`, so their sum
reaches toward `2`, and `cleanSplitFst_lt_one_iff` below says when it does not: precisely when
the two retentions sum above one. That is a fact about the sum, no longer an admissibility
condition on a composition, since no composition here reads it.
-/

section CleanSplit

/-- The drift index a clean two-branch split accumulates, as the SUM of the two per-branch
    coefficients.

    Empirical status: **VALIDATED** (`validation/empirical/simcov/battery_clean01.py`).
    Forward Wright-Fisher on allele frequencies, 20000 loci from a neutral `1/p` spectrum,
    `NeS = 2000` and `NeT = 500` closed, no mutation and no migration, 10 independent blocks.
    The oracle is the realised PER-BRANCH heterozygosity loss `1 - H_branch/H_ancestor` summed
    over the two lineages, which is the reading `fstFromDriftFactor` was validated at:

      t      this body   summed per-branch F   pairwise Hudson F_ST
      100    0.11990     0.11944 ± 0.00063     0.0598
      250    0.28189     0.28158 ± 0.00148     0.1416
      500    0.51114     0.51420 ± 0.00158     0.2572
      800    0.73214     0.73279 ± 0.00173     0.3671
      1100   0.90777     0.90748 ± 0.00191     0.4559

    Worst cell 1.94 sems, 0.60% relative. Every cell stays inside
    `cleanSplitFst_lt_one_iff`'s admissible range, which the battery asserts rather than
    assumes. Power: the prediction spans 0.120 to 0.908, a factor of 7.6.

    THE SUMMATION CONVENTION IS WHAT WAS MEASURED, and the third column is why the warning
    below is kept rather than retired. The pairwise Hudson reading of the same two branches,
    carried as a competitor on the same replicates, is FALSIFIED at 459 sems and 99%
    relative — it runs almost exactly half the summed index, which is the factor-of-two-per-
    branch shape `Var_Delta_Mu`'s docstring records as having produced a factor-of-four false
    falsification twice. So the convention is now measured and not merely asserted: this is
    the sum of two PER-BRANCH Wright `F` values and NOT a pairwise Hudson `F_ST`, and a
    consumer feeding a pairwise value gets a number the design has separated from this one.

    argument_source: model. `Ne` and `t` are the simulation's own parameters, never estimated
    from the replicates the heterozygosity loss is measured on. The control is one branch's
    realised retention against `neutralDriftFactor`, a separately measured body, on the same
    resampling path: predicted 0.759546, measured 0.759042 ± 0.001733.

    WHAT THIS DOES NOT CARRY, AND IT IS WHY THE COMPOSITION BELOW DOES NOT READ IT. This index
    describes the TOTAL differentiation the split has accumulated between the two branches. It
    is NOT the argument a portability chart takes, and the same run that validated it rejected
    it in that role at 66.51 sems and 56% low at the deepest cell.

    THE LINE IS CHART ARGUMENT VERSUS DRIFT-VARIANCE ARGUMENT, and NOT transported `R²` versus
    anything else. A consumer feeding a portability CHART wants `cleanSplitTargetR2'`, which
    charts the target branch alone. A consumer wanting the DRIFT VARIANCE BETWEEN THE BRANCHES
    — the moment `Var(p_T | p_S) = F · p_S · (1 - p_S)`, whose `F` accumulates along BOTH
    branches from their common ancestor — wants this body, summed, for exactly the reason the
    convention paragraph above gives, and `causalVarianceRatio` below is that consumer.
    A transported `R²` that has been decomposed into factors
    can carry one factor of each kind, so a reader deriving such a factor should not read the
    paragraph above as putting this body out of reach: what is rejected is this index in a
    chart's `fst` slot, not this index. -/
noncomputable def cleanSplitFst (NeS NeT : ℝ) (t : ℕ) : ℝ :=
  fstFromDriftFactor (neutralDriftFactor NeS t) +
    fstFromDriftFactor (neutralDriftFactor NeT t)

/-- **When the summed index stays below one, exactly.** The sum of two per-branch coefficients
    is not confined to the unit interval — each reaches toward one, so the sum reaches toward
    two — and this says when it does not: precisely when the two retentions sum above one.
    A consumer reading the sum as though it were one population's `F` against an ancestor
    needs that condition. The composed prediction below does not, because it never puts this
    sum in a chart's `fst` slot. -/
theorem cleanSplitFst_lt_one_iff (NeS NeT : ℝ) (t : ℕ) :
    cleanSplitFst NeS NeT t < 1 ↔
      1 < neutralDriftFactor NeS t + neutralDriftFactor NeT t := by
  unfold cleanSplitFst fstFromDriftFactor Descent.Core.complement
  constructor <;> intro h <;> linarith

/-- **No time, no differentiation.** Both branches retain everything at generation zero, so the
    split has accumulated no drift index. -/
@[simp] theorem cleanSplitFst_at_zero_time (NeS NeT : ℝ) :
    cleanSplitFst NeS NeT 0 = 0 := by
  unfold cleanSplitFst neutralDriftFactor fstFromDriftFactor Descent.Core.complement
  norm_num

/-- **The causal variance ratio across a split**, `1/(1 - F)`, taking the SUMMED per-branch
    drift index — which is what `cleanSplitFst` computes and is the reason that body survives.

    WHERE IT COMES FROM. Conditioning on the source frequency, the target's expected
    heterozygosity is `E[h_T | p_S] = h_S · (1 - F)`, the same cancellation family that makes
    `sourcePolymorphicSignalFraction` independent of the target's effective size. The causal
    genetic variance therefore rises across the split by the reciprocal of the retained
    fraction, and `F` here accumulates along BOTH branches from their common ancestor, which is
    why the index is summed rather than pairwise.

    **A HUDSON-DERIVED STAND-IN IS NOT ADMISSIBLE AS THE INPUT, and that refusal is measured.**
    Reading the argument as `2 · F_hudson` fits at 1.6%, 3.1% and 1.7% where `F_hudson` alone
    runs 5.6% to 35%, so the convention is decided rather than conventional. But the factor
    relating the two is specific to a symmetric split and is not a law: it was MEASURED at
    2.23 to 2.40, not the folkloric 2. Substituting a doubled Hudson value flatters the fit at
    depth in one direction, so a caller must supply a genuine summed per-branch index.

    Empirical status: **CONDITIONALLY VALID**, and the regime has two independent edges.

    INSIDE THE REGIME the relation is a clean-split identity and was confirmed against
    ancient-sample per-branch `F` at `t = 200` to 0.0004 relative, with zero fitted parameters.

    THE FIRST EDGE IS DEPTH. Beyond `F ≈ 0.2` the agreement degrades one-signed, reaching a
    ratio of 0.665 by `F = 0.79`. So this is a first-order law in the drift index and the
    correction at depth is OWED, not merely unmeasured.

    THE SECOND EDGE IS CAUSAL ASCERTAINMENT, and it is a fired pre-registration rather than a
    caveat added afterwards. Drawing causal variants from all segregating sites rather than
    common ones returned a measured ratio of 0.943 at the nearest separation — BELOW ONE. This
    body is `≥ 1` by construction on `F ∈ [0,1)`, as `causalVarianceRatio_one_le` states, so
    that regime lies outside its scope entirely and no choice of argument reaches it. The
    reading is not yet settled: 0.943 carries no error bar, and a jackknife sem is owed before
    it can be called below one. The candidate mechanism — ascertaining causals on being
    polymorphic in the SOURCE enriches for source-rare variants and depresses the source
    variance, while the target carries no matching condition — is flagged and NOT adopted.

    ON A STEPPING-STONE CHAIN the relation is approximate with a known sign: the target
    regresses toward the ancestral mean, so the truth sits BELOW this body. The sign is
    reported rather than predicted, because the chain approximation has no derivation here and
    retrofitting a sign argument to a one-signed residual is how a finding becomes an excuse.

    NO `record()` NAMES THIS BODY. The numbers above come from the derivation's own runs, which
    are not in this repository, so a reader cannot check them; a battery under this name is
    owed and is what would move the head.

    argument_source: model. -/
noncomputable def causalVarianceRatio (fstSummed : ℝ) : ℝ := 1 / (1 - fstSummed)

/-- **No differentiation, no inflation.** At the split itself the causal variance is the
    ancestral one, which is the control cell any battery for this body is gated on. -/
@[simp] theorem causalVarianceRatio_at_zero : causalVarianceRatio 0 = 1 := by
  unfold causalVarianceRatio
  norm_num

/-- **The ratio is at least one on the admissible range**, and this is the statement that puts
    the observed sub-one regime outside the body rather than merely far from it: no argument in
    `[0,1)` produces a value below one, so a measurement below one refutes the SCOPE and not
    the constant. -/
theorem causalVarianceRatio_one_le (fstSummed : ℝ)
    (h0 : 0 ≤ fstSummed) (h1 : fstSummed < 1) :
    1 ≤ causalVarianceRatio fstSummed := by
  unfold causalVarianceRatio
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Deeper splits inflate the causal variance further.** Monotone in the summed index across
    the admissible range. -/
theorem causalVarianceRatio_monotone (f₁ f₂ : ℝ)
    (h₁₂ : f₁ ≤ f₂) (h1 : f₂ < 1) :
    causalVarianceRatio f₁ ≤ causalVarianceRatio f₂ := by
  unfold causalVarianceRatio
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- **causalVarianceRatio at complete differentiation, named.** The denominator vanishes at
    `F = 1`, where no ancestral variation is retained and the ratio is unbounded. Lean returns
    `0` there — the smallest possible inflation for a split that has retained nothing — and no
    type error marks the point. Consumers must exclude it. -/
theorem causalVarianceRatio_at_one_is_junk : causalVarianceRatio 1 = 0 := by
  unfold causalVarianceRatio
  norm_num

/-- **The per-generation retention is an admissible base** whenever the effective size is at
    least one. Both halves are needed downstream: nonnegativity to raise it to a power at all,
    and the upper bound to make the power antitone in the generation count. -/
theorem neutralDriftFactor_base_mem_unit (Ne : ℝ) (hNe : 1 ≤ Ne) :
    0 ≤ 1 - 1 / (2 * Ne) ∧ 1 - 1 / (2 * Ne) ≤ 1 := by
  have hpos : (0 : ℝ) < 2 * Ne := by linarith
  have hhalf : 1 / (2 * Ne) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hnn : (0 : ℝ) ≤ 1 / (2 * Ne) := by positivity
  exact ⟨by linarith, by linarith⟩

/-- **Drift retention falls with the generation count**, for any effective size of at least
    one. This is the monotone step the composed prediction rests on. -/
theorem neutralDriftFactor_antitone_time (Ne : ℝ) (t₁ t₂ : ℕ)
    (hNe : 1 ≤ Ne) (ht : t₁ ≤ t₂) :
    neutralDriftFactor Ne t₂ ≤ neutralDriftFactor Ne t₁ := by
  obtain ⟨h0, h1⟩ := neutralDriftFactor_base_mem_unit Ne hNe
  unfold neutralDriftFactor
  exact pow_le_pow_of_le_one h0 h1 ht

/-- **The split's drift index grows with time.** Retention falls in each branch, so the
    per-branch indices rise and so does their sum. -/
theorem cleanSplitFst_monotone_time (NeS NeT : ℝ) (t₁ t₂ : ℕ)
    (hS : 1 ≤ NeS) (hT : 1 ≤ NeT) (ht : t₁ ≤ t₂) :
    cleanSplitFst NeS NeT t₁ ≤ cleanSplitFst NeS NeT t₂ := by
  have hdS := neutralDriftFactor_antitone_time NeS t₁ t₂ hS ht
  have hdT := neutralDriftFactor_antitone_time NeT t₁ t₂ hT ht
  unfold cleanSplitFst fstFromDriftFactor Descent.Core.complement
  linarith

/-!
### The source branch enters as a fraction, and it needs the ancestral spectrum

What follows is the corrected composition. The target branch keeps the chart; the source
branch gets a factor built from the probability that each ancestral variant is still
segregating in it, which is a functional of the ancestral frequencies and cannot be
compressed into a drift index.
-/

/-- **Gegenbauer polynomials at `α = 3/2`, by the standard three-term recurrence**
    `(k+2)·C_{k+2}(z) = 2·(k + 5/2)·z·C_{k+1}(z) − (k+3)·C_k(z)`. That recurrence is the
    definition here rather than a theorem about one, because Mathlib carries neither Gegenbauer
    nor Legendre polynomials.

    THEY APPEAR FOR ONE REASON. `p(1-p)·C_{n-1}^{3/2}(1-2p)` is an eigenfunction of the
    Wright-Fisher backward operator `L u = p(1-p)·u''/(4·Ne)`, with eigenvalue
    `-n(n+1)/(4·Ne)`, and it vanishes at both absorbing boundaries. That is what lets
    `stillSegregatingProb` below be a closed form in its own arguments instead of an iteration
    of a transition matrix — the difference between a law this corpus can state and a
    computation it can only run.

    Empirical status: NOT AN EMPIRICAL CLAIM. A polynomial recurrence describes no population.
    What can be measured is the segregation probability built out of it. -/
noncomputable def gegenbauerC32 : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, z => 3 * z
  | (k + 2), z =>
      (2 * ((k : ℝ) + 5 / 2) * z * gegenbauerC32 (k + 1) z
        - ((k : ℝ) + 3) * gegenbauerC32 k z) / ((k : ℝ) + 2)

/-- **Even-degree Gegenbauer polynomials are even functions and odd-degree ones are odd.**
    Carried in pairs, because the recurrence makes each value depend on the two below it, so a
    single-step induction cannot state a strong enough hypothesis. This is what makes
    `stillSegregatingProb_symm` a corollary of the expansion's coefficients rather than a
    separate assumption about drift. -/
theorem gegenbauerC32_neg (n : ℕ) (z : ℝ) :
    gegenbauerC32 n (-z) = (-1) ^ n * gegenbauerC32 n z := by
  have key : ∀ m : ℕ, gegenbauerC32 m (-z) = (-1) ^ m * gegenbauerC32 m z ∧
      gegenbauerC32 (m + 1) (-z) = (-1) ^ (m + 1) * gegenbauerC32 (m + 1) z := by
    intro m
    induction m with
    | zero => exact ⟨by simp [gegenbauerC32], by simp [gegenbauerC32]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show gegenbauerC32 (k + 2) (-z) = (-1) ^ (k + 2) * gegenbauerC32 (k + 2) z
      simp only [gegenbauerC32]
      rw [ih.1, ih.2]
      ring
  exact (key n).1

/-- **An even-degree Gegenbauer polynomial takes the same value at `z` and `-z`.** The form the
    segregation probability's symmetry actually uses. -/
theorem gegenbauerC32_even_neg (k : ℕ) (z : ℝ) :
    gegenbauerC32 (2 * k) (-z) = gegenbauerC32 (2 * k) z := by
  rw [gegenbauerC32_neg, pow_mul]
  norm_num

/-- **The probability that a neutral allele at frequency `p` is still SEGREGATING** — neither
    lost nor fixed — after `t` generations in a closed population of effective size `Ne`.

    Kimura's eigenfunction solution of the Wright-Fisher diffusion, with the coefficients
    computed rather than quoted. Expanding the constant initial condition against the
    eigenfunctions under the weight `1/(p(1-p))` gives `⟨1, u_n⟩ = ½·(P_n(1) − P_n(-1))`,
    which is `1` for odd `n` and `0` for even `n`; only odd `n` survives, so the sum is
    reindexed `n = 2k+1` and only EVEN-degree Gegenbauer polynomials appear. The symmetry
    between `p` and `1-p` follows from that and is `stillSegregatingProb_symm`.

    ONE TERM IS NOT ENOUGH, which is why this is a series and not a single exponential. At the
    deepest cell the corpus has measured — `t = 1100` generations at `Ne = 2000` — the `n = 3`
    term still carries `e^(-1.65) = 0.19`, so truncating at the leading eigenvalue discards a
    fifth of the answer.

    `t = 0` IS GUARDED AND THE GUARD IS LOAD-BEARING. For `t ≥ 1` the exponential beats the
    polynomial growth of the Gegenbauer factor and the series converges absolutely. At `t = 0`
    the expansion of the constant function converges only conditionally, so `Summable` fails
    and `∑'` returns its junk value `0`; the reading `stillSegregatingProb Ne p 0 = 1` would be
    FALSE as written rather than merely unproved. The `if` supplies the value the series is
    expanding, which is what the `t = 0` control cell every battery group is gated on has to
    see.

    SUMMABILITY FOR `t ≥ 1` IS AN OBLIGATION THIS FILE HAS NOT DISCHARGED. It wants a
    polynomial bound on `C_{2k}^{3/2}` over `[-1, 1]`. Until that is proved, the theorems below
    take the range and the time-monotonicity of this body as HYPOTHESES rather than deriving
    them, and a consumer has to discharge them — numerically, as the derivation did — instead
    of assuming them silently.

    Empirical status: UNTESTED. No `record()` in the harness names this body. Behind it stand
    two other computations of the same quantity that agree with it — a backward iteration of
    the discrete Wright-Fisher transition matrix, which is the battery's own engine with no
    diffusion limit taken, and a direct forward Wright-Fisher simulation agreeing at worst 0.73
    sems — but those scripts are not in this repository, so a reader cannot check them and they
    do not amount to a verdict. What measured standing this body has arrives through
    `sourcePolymorphicSignalFraction`, which is compared against committed cells. -/
noncomputable def stillSegregatingProb (Ne p : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 1 else
    ∑' k : ℕ,
      4 * (4 * (k : ℝ) + 3) / (((2 : ℝ) * k + 1) * (2 * k + 2))
        * (p * (1 - p)) * gegenbauerC32 (2 * k) (1 - 2 * p)
        * Real.exp (-(((2 : ℝ) * k + 1) * (2 * k + 2)) * t / (4 * Ne))

/-- **A variant and its complement have the same fate.** An allele at frequency `p` and one at
    `1-p` are equally likely to be still segregating, because the two are the same variant read
    from the other allele. This is not assumed: it falls out of `gegenbauerC32_even_neg`,
    which is to say out of the coefficients vanishing on the even eigenfunctions. A consumer
    integrating against a spectrum symmetric about one half may therefore weight the
    probability flatly, which is what makes the battery's `1/p` spectrum tractable. -/
theorem stillSegregatingProb_symm (Ne p : ℝ) (t : ℕ) :
    stillSegregatingProb Ne (1 - p) t = stillSegregatingProb Ne p t := by
  unfold stillSegregatingProb
  by_cases ht : t = 0
  · simp [ht]
  · simp only [if_neg ht]
    refine tsum_congr fun k ↦ ?_
    have hz : 1 - 2 * (1 - p) = -(1 - 2 * p) := by ring
    have hp : (1 - p) * (1 - (1 - p)) = p * (1 - p) := by ring
    rw [hz, hp, gegenbauerC32_even_neg]

/-- **No time, no absorption.** Every variant is still segregating at the generation the
    branches parted, which is the guarded value rather than the series' junk point. -/
@[simp] theorem stillSegregatingProb_at_zero_time (Ne p : ℝ) :
    stillSegregatingProb Ne p 0 = 1 := by
  unfold stillSegregatingProb
  simp

/-- **The fraction of the TARGET's genetic signal that is still POLYMORPHIC IN THE SOURCE.**
    A weighted average of `stillSegregatingProb` over the causal variants: `w j` is variant
    `j`'s contribution to the genetic variance — `β_j² · 2·p_j·(1-p_j)` at the battery's
    instantiation — and `p j` is its ANCESTRAL frequency, the state both branches departed
    from.

    THE TARGET BRANCH CANCELS OUT OF THIS, AND THAT CANCELLATION IS THE POINT. Conditioning on
    the ancestral frequency, the target's expected heterozygosity at a variant is the ancestral
    heterozygosity times that branch's drift factor — one constant, shared across variants,
    which divides out of numerator and denominator alike. So this quantity depends on the
    SOURCE's effective size and on the ancestral spectrum, and on the TARGET's effective size
    not at all. That is a structural claim the battery's own decomposition row could not make,
    because both of its factors were measured on the same replicates;
    `cleanSplitTargetR2'_NeT_enters_only_through_chart` states it at the composed level and it
    is UNTESTED, since the committed design carries a single `(NeS, NeT)` pair and no stored
    cell can separate them.

    WHY THE SPECTRUM IS AN ARGUMENT AND A DRIFT INDEX WOULD NOT DO. Holding `NeS` and `t` fixed
    — hence holding the source's own `F` fixed — and varying only the ancestral spectrum moves
    the lost fraction by a factor of 51 at `t = 100` and 1.9 at `t = 1100`. The source's
    contribution is a functional of the spectrum, so a body taking one number where this takes
    `w` and `p` cannot be repaired by rescaling that number.

    Empirical status: **VALIDATED** (`simcov/battery_clean01.py`). Evaluated at the battery's
    own instantiation — 20000 loci from a neutral `1/p` spectrum on `[0.01, 0.99]`,
    `NeS = 2000` closed, no mutation and no migration, 10 independent blocks — against the
    realised fraction of the target's signal carried by variants still polymorphic in the
    source, which `clean01.log` prints per cell as "of the target's signal":

      t      this body   realised fraction   relative
      100    0.98882     0.98740             +0.144%
      250    0.95561     0.95470             +0.095%
      500    0.89892     0.89940             -0.053%
      800    0.83442     0.83490             -0.057%
      1100   0.77431     0.77300             +0.169%

    Worst cell 0.169% relative, residuals of mixed sign. Zero fitted constants: every argument
    is a simulation parameter, and nothing is estimated from the replicates the fraction is
    measured on.

    Power: the prediction spans 0.989 to 0.774 across the design, and the composition it feeds
    separated three rival readings of the same slot on these very cells — the summed index
    FALSIFIED at 66.51 sems, the target-branch-only reading at 47.30, the superseded linear
    retention at 229.

    A `record()` NOW NAMES THIS BODY and it is a MATCH (`simcov/battery_clean02.py`): 14
    cells, worst 2.86 sems and 0.69% relative, residuals of mixed sign, zero fitted
    constants, error bars MEASUREMENT-ONLY rather than paired. Two spectra at five depths
    each — `1/p` truncated at `[0.01,0.99]` and at `[0.05,0.95]` — plus four target sizes at
    fixed `(NeS, t)`. The prediction spans 0.775 to 0.9996 across the design.

    THE FOUR `NeT` CELLS ARE THE INFORMATIVE ONES, and they are not a restatement of the
    argument list. This body has no `NeT` argument, but its ORACLE — the realised fraction of
    the target's signal carried by variants still polymorphic in the source — weights by the
    TARGET's realised heterozygosity, which does drift with `NeT`. One prediction, 0.899305,
    against measurements 0.897812, 0.896364, 0.898253, 0.898404 at `NeT` = 250, 500, 1000,
    2000: a 0.2% spread with every cell inside one sem.

    The source-off cells (`NeS = 200000`) are deliberately NOT among the 14. No locus fixes
    there, so the prediction and every replicate of the measurement are 1 alike: the cell
    cannot fail, and its replicates being identical drive the sem to zero. Including them
    reported a MATCH whose worst cell read "1888130 sems off". A cell that can only agree
    buys no evidence and destroys the error bar it is scored against.

    argument_source: model. `NeS`, `t` and the ancestral frequencies are the simulation's own
    parameters; the weights are its constructed effect sizes and ancestral heterozygosities. -/
noncomputable def sourcePolymorphicSignalFraction {M : ℕ} (w p : Fin M → ℝ)
    (NeS : ℝ) (t : ℕ) : ℝ :=
  (∑ j, w j * stillSegregatingProb NeS (p j) t) / ∑ j, w j

/-- **At the split itself the whole signal is still shared.** Every variant is segregating in
    the source, so the weighted average is one whatever the weights are, provided they do not
    sum to zero. This is the control cell every battery group in the clean-split design is
    gated on. -/
theorem sourcePolymorphicSignalFraction_at_zero_time {M : ℕ} (w p : Fin M → ℝ) (NeS : ℝ)
    (hw : ∑ j, w j ≠ 0) :
    sourcePolymorphicSignalFraction w p NeS 0 = 1 := by
  unfold sourcePolymorphicSignalFraction
  simp [div_self hw]

/-- **The fraction is a genuine fraction**, between none of the signal and all of it.

    Assumes: the weights are nonnegative and do not sum to zero, and the segregation
    probability lies in `[0,1]` at each ancestral frequency. The last of those is a property of
    `stillSegregatingProb` that this file has not proved — it needs the summability obligation
    that body's docstring records — so it is carried as a hypothesis rather than smuggled in.
    What is proved here is the part that is about the AVERAGING: a weighted mean of quantities
    in `[0,1]` with nonnegative weights lands in `[0,1]`, whatever the spectrum. -/
theorem sourcePolymorphicSignalFraction_mem_Icc {M : ℕ} (w p : Fin M → ℝ) (NeS : ℝ) (t : ℕ)
    (hw : ∀ j, 0 ≤ w j) (hpos : 0 < ∑ j, w j)
    (hP0 : ∀ j, 0 ≤ stillSegregatingProb NeS (p j) t)
    (hP1 : ∀ j, stillSegregatingProb NeS (p j) t ≤ 1) :
    0 ≤ sourcePolymorphicSignalFraction w p NeS t ∧
      sourcePolymorphicSignalFraction w p NeS t ≤ 1 := by
  unfold sourcePolymorphicSignalFraction
  have hnum : 0 ≤ ∑ j, w j * stillSegregatingProb NeS (p j) t :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (hP0 j)
  have hle : ∑ j, w j * stillSegregatingProb NeS (p j) t ≤ ∑ j, w j := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    calc w j * stillSegregatingProb NeS (p j) t
        ≤ w j * 1 := mul_le_mul_of_nonneg_left (hP1 j) (hw j)
      _ = w j := mul_one _
  exact ⟨div_nonneg hnum hpos.le, (div_le_one hpos).2 hle⟩

/-- **Signal leaves the score and does not come back.** As the split deepens more of the
    target's causal variants have been absorbed in the source, so the shared fraction falls.

    Assumes: the segregation probability is itself antitone in time at each frequency, which is
    true of the Wright-Fisher diffusion and is not proved here — the eigenfunction coefficients
    alternate in sign, so a termwise argument does not give it. Stated this way the theorem
    says what it is for: the averaging cannot reverse a decline that holds variant by variant,
    however the weights are distributed. -/
theorem sourcePolymorphicSignalFraction_antitone_time {M : ℕ} (w p : Fin M → ℝ) (NeS : ℝ)
    (t₁ t₂ : ℕ) (hw : ∀ j, 0 ≤ w j) (hpos : 0 < ∑ j, w j)
    (hP : ∀ j, stillSegregatingProb NeS (p j) t₂ ≤ stillSegregatingProb NeS (p j) t₁) :
    sourcePolymorphicSignalFraction w p NeS t₂ ≤ sourcePolymorphicSignalFraction w p NeS t₁ := by
  unfold sourcePolymorphicSignalFraction
  have h : ∑ j, w j * stillSegregatingProb NeS (p j) t₂ ≤
      ∑ j, w j * stillSegregatingProb NeS (p j) t₁ :=
    Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hP j) (hw j)
  rw [div_le_div_iff₀ hpos hpos]
  nlinarith [h, hpos]

/-- **The composed target `R²` for a clean two-branch split, with the branches separated.**
    The TARGET branch's drift index through the neutral portability chart, times the fraction
    of the target's signal still polymorphic in the SOURCE, times the LD factor.

    THE PRODUCT IS DERIVED AND NOT AN ANSATZ. With the score `s = Σ_{j polymorphic in S} β_j
    g_j` over target genotypes and the phenotype `y = Σ_j β_j g_j + e`, the frequency engine
    carrying no linkage, `cov(s,y) = Var(s) = Σ_{poly} β_j² h_T,j`, so
    `R² = [V_A^poly/V_A^T] · [V_A^T/(V_A^T + V_E)]`. The second bracket is
    `neutralPortability r2_0 F_T` after substituting `V_E/V_A = (1-r2_0)/r2_0`, and the first
    is the source-polymorphic fraction. The factorisation is a consequence of the score's
    construction; only the TARGET branch's index belongs in the chart's `fst` slot, and the
    source branch enters through the fraction and nowhere else.

    THE PRIME IS NOT DECORATION. The unprimed name belonged to the summed-index composition
    that this design FALSIFIED at 66.51 sems, and the harness's ledger still carries that
    verdict under it; a repair reusing the name would have inherited a record about a different
    formula.

    Empirical status: **VALIDATED** (`simcov/battery_clean01.py`). Same replicates as
    `cleanSplitFst`, 40000 target individuals per block, TRUE causal effects so no
    GWAS-inefficiency confound is present, `r2_0 = V_A/(V_A + V_E) = 0.5` realised in every
    block, `ldFactor = 1`, `NeS = 2000` and `NeT = 500`. The observable is the realised squared
    correlation between the source-built PER-ALLELE score and the target phenotype:

      t      F_T       fraction   this body   measured             sems   relative
      100    0.09521   0.98882    0.46970     0.47082 ± 0.00061    1.84   -0.238%
      250    0.22130   0.95561    0.41836     0.41995 ± 0.00110    1.45   -0.379%
      500    0.39362   0.89892    0.33933     0.33817 ± 0.00181   -0.64   +0.342%
      800    0.55085   0.83442    0.25862     0.25826 ± 0.00115   -0.31   +0.139%
      1100   0.66731   0.77431    0.19330     0.19400 ± 0.00139    0.51   -0.362%

    Worst cell 1.84 sems, 0.38% relative, residuals of mixed sign, with ZERO fitted constants —
    every argument is a model parameter and none is estimated from the replicates. It also
    beats the battery's own decomposition row, which used the MEASURED fraction and lands at
    2.66 sems: the computed fraction is noise-free, so supplying it improves the fit rather
    than degrading it.

    THE ERROR BARS ARE THE BATTERY'S PAIRED SEMS, which subtract the block-to-block scatter
    shared by a prediction that tracks each block's realised `F`. This prediction is
    deterministic and so deserves the measurement-only sem, which is at or above the paired
    one. The sems quoted are therefore an upper bound on the discrepancy.

    Power: the prediction spans 0.470 to 0.193 across the design, a factor of 2.4, and the two
    other readings of the `fst` slot that could be meant sit at 0.085 and 0.250 at the far
    cell — the summed index FALSIFIED at 66.51 sems and 56% low, the target-branch-only reading
    at 47.30 sems and 20% high. The design separates them by a factor of three and could not
    have validated all three.

    THERE IS NO SHALLOW-SPLIT REDUCTION TO THE SUMMED BODY, and a reader should not look for
    one. The ratio of the two is non-monotone in `t` with a crossing near `t = 250`. The summed
    body survived at `t = 100` because it charges `(1-r2_0)·F_S` for the source branch where
    the truth charges `1 - S`, and on THIS spectrum at `r2_0 = 0.5` those happen to be 0.0124
    and 0.0116; on a `[0.05, 0.95]` spectrum at the identical `F_S` they are 0.0124 and
    0.00045, a factor of 27 apart. Two unrelated errors cancelled at one cell. The genuine
    reduction is at `t = 0`, and it is `cleanSplitTargetR2'_at_zero_time`.

    A `record()` NOW NAMES THIS BODY and it is a MATCH (`simcov/battery_clean02.py`), which
    also closes the `NeT` question. 19 cells, worst 1.97 sems and 0.33% relative, residuals
    of mixed sign, ZERO fitted constants, and MEASUREMENT-ONLY error bars rather than the
    paired ones the table above carries. The design spans two spectra at five depths each,
    four target sizes at fixed `(NeS, t)`, and a source-off limit at `NeS = 200000` where
    `Φ = 1` and the composition reduces to its chart — which is what separates the two
    factors instead of fitting them jointly, and is the thing a single `(NeS, NeT)` pair
    could never do.

    BOTH RIVALS FAIL ON THE SAME CELLS. The superseded summed-index body is FALSIFIED at
    74.38 sems and 60% relative, the chart alone with `Φ` forced to 1 at 36.67 sems and 20%
    relative. The positive control — `t = 0`, where the measured target `R²` must be the
    constructed `V_A/(V_A + V_E)` and no formula under test is involved — passes at 0.73
    sems.

    THE `t = 100` COINCIDENCE IS NOW MEASURED RATHER THAN ARGUED. On `[0.01,0.99]` the two
    source-branch charges are `1 - Φ = 0.01103` against `(1-r2_0)·F_S = 0.01251`, a ratio of
    1.1, which is why the summed body survived that cell. On `[0.05,0.95]` at the same `F_S`
    they are 0.00044 and 0.01233, a ratio of 28.1 — the paragraph above predicted 27 from
    the derivation alone, before the second spectrum was run.

    SCOPE, AND IT IS NARROWER THAN THE NAME. Derived for the PER-ALLELE score, which is what a
    deployed PGS is. It does NOT describe the SOURCE-STANDARDISED score, whose `√(h_S/h_T)`
    weights make a different observable — that construction is measured in the same battery and
    needs a derivation of its own. The regime is inherited whole from `neutralDriftFactor`:
    closed populations, no mutation, no migration, no linkage within the drift stage, and true
    causal effects.

    argument_source: model. The control is the `t = 0` cell, where no drift has happened and
    the measured target `R²` must be the constructed `V_A/(V_A + V_E)`: predicted 0.500000,
    measured 0.501181 ± 0.001110. -/
noncomputable def cleanSplitTargetR2' (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ) : ℝ :=
  neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t))
    * sourcePolymorphicSignalFraction w p NeS t * ldFactor

/-- **The composition recovers the ancestral `R²` at the root.** At the generation the branches
    parted, with no LD loss, the target `R²` IS the source `R²`: the target branch has
    accumulated no drift index and the source branch has absorbed no variants, so neither
    penalty is active. A body failing this would be predicting a drop with no elapsed time.

    This is the reduction the corrected composition genuinely has. It is NOT a shallow-split
    agreement with the summed-index body, which does not exist — see this file's account of the
    `t = 100` coincidence. -/
theorem cleanSplitTargetR2'_at_zero_time (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ) (NeS NeT : ℝ)
    (hw : ∑ j, w j ≠ 0) :
    cleanSplitTargetR2' r2_0 w p NeS NeT 0 1 = r2_0 := by
  unfold cleanSplitTargetR2'
  rw [sourcePolymorphicSignalFraction_at_zero_time w p NeS hw]
  unfold neutralPortability fstFromDriftFactor neutralDriftFactor Descent.Core.complement
  norm_num

/-- **The corrected prediction sits below the target-branch-only reading.** The source branch
    can only remove signal, so charting the target branch alone and stopping there is an upper
    bound. The design measured both: the target-branch-only reading is 20% HIGH at the deepest
    cell and the summed-index reading 56% LOW, and the corrected law lies between them, which
    is the shape this inequality fixes in the corpus. -/
theorem cleanSplitTargetR2'_le_targetBranchOnly (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ) (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1)
    (hfst : fstFromDriftFactor (neutralDriftFactor NeT t) ≤ 1)
    (hfrac1 : sourcePolymorphicSignalFraction w p NeS t ≤ 1) (hld : 0 ≤ ldFactor) :
    cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor ≤
      neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) * ldFactor := by
  unfold cleanSplitTargetR2'
  have hchart : 0 ≤ neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) :=
    neutralPortability_nonneg _ _ hr2 hr2' hfst
  nlinarith [mul_le_mul_of_nonneg_left hfrac1 hchart, hld]

/-- **The target's effective size moves the prediction only through the chart.** Cross-
    multiplied so that the claim is an identity rather than a statement about a quotient: the
    source-branch factor and the LD factor are the same at two target effective sizes, so all
    the `NeT`-dependence is in `neutralPortability`.

    THIS WAS THE SHARPEST UNTESTED CONSEQUENCE OF THE CORRECTION, and it is why the
    correction is a change of shape rather than of constant: the summed-index body made the
    source and target branches enter symmetrically, and here the source branch's factor does
    not know `NeT` exists. It is now TESTED AND MATCHED (`simcov/battery_clean02.py`), by the
    sweep in `NeT` at fixed `NeS` the claim needed and no stored cell could supply:
    `NeT` = 250, 500, 1000, 2000 at `NeS = 2000`, `t = 500`.
    `sourcePolymorphicSignalFraction` returns ONE prediction, 0.899305, against measurements
    spanning 0.2%, while the composed prediction moves 0.242 to 0.422 across the same four
    cells — a factor of 1.74, carried entirely by `neutralPortability` — and matches at 0.57,
    1.26, 0.89 and 0.97 sems. -/
theorem cleanSplitTargetR2'_NeT_enters_only_through_chart (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT NeT' : ℝ) (t : ℕ) (ldFactor : ℝ) :
    cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor *
        neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT' t)) =
      cleanSplitTargetR2' r2_0 w p NeS NeT' t ldFactor *
        neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) := by
  unfold cleanSplitTargetR2'
  ring

/-- **The prediction is a genuine `R²`**: nonnegative, and never above the ancestral value.
    Both penalties are retentions, so the composition can only lose. -/
theorem cleanSplitTargetR2'_mem_Icc (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ) (NeS NeT : ℝ) (t : ℕ)
    (ldFactor : ℝ) (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1)
    (hfst0 : 0 ≤ fstFromDriftFactor (neutralDriftFactor NeT t))
    (hfst1 : fstFromDriftFactor (neutralDriftFactor NeT t) < 1)
    (hfrac0 : 0 ≤ sourcePolymorphicSignalFraction w p NeS t)
    (hfrac1 : sourcePolymorphicSignalFraction w p NeS t ≤ 1)
    (hld0 : 0 ≤ ldFactor) (hld1 : ldFactor ≤ 1) :
    0 ≤ cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor ∧
      cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor ≤ r2_0 := by
  have hchart : 0 ≤ neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) :=
    neutralPortability_nonneg _ _ hr2 hr2' hfst1.le
  have hle : neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) ≤ r2_0 :=
    neutralPortability_le_r2_0 _ _ hr2 hr2' hfst0 hfst1
  unfold cleanSplitTargetR2'
  refine ⟨mul_nonneg (mul_nonneg hchart hfrac0) hld0, ?_⟩
  nlinarith [mul_nonneg hchart hfrac0, mul_nonneg hchart hld0]

/-- **The composed prediction decays with the age of the split.** More generations means a
    larger target drift index, which the chart carries downward, and a smaller shared fraction,
    which multiplies it down again. The two penalties move the same way, so no cancellation
    between them can hide a decline.

    The LD factor is held fixed, which is the honest statement: this is about the drift half of
    the composition, and a target whose tagging has also decayed falls further. The
    admissibility hypothesis is on the LATER time only, since the index is monotone in time and
    requiring it at both would be redundant. The fraction's own monotonicity is a hypothesis
    for the reason `sourcePolymorphicSignalFraction_antitone_time` records. -/
theorem cleanSplitTargetR2'_antitone_time (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ) (NeS NeT : ℝ)
    (t₁ t₂ : ℕ) (ldFactor : ℝ) (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hT : 1 ≤ NeT) (ht : t₁ ≤ t₂)
    (hfst0 : 0 ≤ fstFromDriftFactor (neutralDriftFactor NeT t₁))
    (hfst1 : fstFromDriftFactor (neutralDriftFactor NeT t₂) < 1)
    (hfrac : sourcePolymorphicSignalFraction w p NeS t₂ ≤
      sourcePolymorphicSignalFraction w p NeS t₁)
    (hfrac0 : 0 ≤ sourcePolymorphicSignalFraction w p NeS t₂) (hld : 0 ≤ ldFactor) :
    cleanSplitTargetR2' r2_0 w p NeS NeT t₂ ldFactor ≤
      cleanSplitTargetR2' r2_0 w p NeS NeT t₁ ldFactor := by
  have hd := neutralDriftFactor_antitone_time NeT t₁ t₂ hT ht
  have hmono : fstFromDriftFactor (neutralDriftFactor NeT t₁) ≤
      fstFromDriftFactor (neutralDriftFactor NeT t₂) := by
    unfold fstFromDriftFactor Descent.Core.complement
    linarith
  have hchart := neutralPortability_antitone_fst r2_0
    (fstFromDriftFactor (neutralDriftFactor NeT t₁))
    (fstFromDriftFactor (neutralDriftFactor NeT t₂)) hr2 hr2' hfst0 hmono hfst1
  have hchart2 : 0 ≤ neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t₂)) :=
    neutralPortability_nonneg _ _ hr2 hr2' hfst1.le
  unfold cleanSplitTargetR2'
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hchart hfrac hfrac0 (le_trans hchart2 hchart)) hld

/-- **The LD penalty enters as the validated multiplicative factor.** `neutralPortabilityRatioLD`
    is the measured combination `(1 - fst_additional)·ld_factor`; read at zero additional
    `F_ST` it is the bare LD factor, which is what this composition multiplies in. The point of
    stating it is the zero: the drift penalty is carried ONCE, by `neutralPortability`, and is
    not applied a second time inside the LD stage. -/
theorem cleanSplitTargetR2'_eq_ratioLD_scaling (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ) :
    cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor =
      neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t)) *
        sourcePolymorphicSignalFraction w p NeS t * neutralPortabilityRatioLD 0 ldFactor := by
  unfold cleanSplitTargetR2' neutralPortabilityRatioLD Descent.Core.retainedFraction
  ring

/-- **The composed target AUC for a clean two-branch split**, at a required prevalence.

    Empirical status: **VALIDATED, inherited** (`simcov/battery_clean01.py`). The chart this
    wraps is `liabilityThresholdAUCFromExplainedR2`, separately VALIDATED against 400 simulated
    PGS studies at pooled RMSE 0.0121 against a 0.0120 noise floor; what this body adds is the
    `R²` it is given. Carrying the corrected `R²` through it, on the same replicates with cases
    the upper 5% of the realised target liability and the Mann-Whitney AUC as the observable:

      t      predicted R²   predicted AUC   measured AUC         sems
      100    0.46970        0.88738         0.89017 ± 0.00081    3.45
      250    0.41836        0.86960         0.87126 ± 0.00152    1.09
      500    0.33933        0.83812         0.83801 ± 0.00141   -0.08
      800    0.25862        0.79955         0.80029 ± 0.00124    0.59
      1100   0.19330        0.76183         0.76220 ± 0.00255    0.15

    Worst cell 3.45 sems, against 33.79 for the summed-index composition on these same cells.
    THE REMAINING RESIDUAL IS THE CHART'S, NOT THE `R²`'s: the `t = 100` miss is +0.0028
    absolute, and the battery's own `t = 0` control — where no drift has happened and the chart
    is read at the constructed `r2_0` — shows +0.0031 by itself, predicted 0.897003 against
    0.900097 ± 0.001305. So it is the chart's small high-`R²` bias, four times smaller than the
    pooled RMSE the chart is validated at, and not something the corrected `R²` introduces.

    Power: the prediction spans 0.887 to 0.762 across the design, and the superseded linear
    retention carried through the same chart is FALSIFIED at 235 sems on the same cells, so the
    design's power to reject a wrong `R²` through this conversion is demonstrated rather than
    assumed.

    Prevalence stays a required argument for the reason
    `targetLiabilityAUCFromNeutralAFBenchmark` gives at length: converting a drift-induced `R²`
    drop to AUC through a prevalence-free chart is the fault that carried a `-0.068` bias, and
    making `K` mandatory is what prevents it.

    NO `record()` NAMES THIS BODY YET; the table is arithmetic against committed cells. This
    is no longer the standing of `cleanSplitTargetR2'`, which `simcov/battery_clean02.py`
    now records as a MATCH — that battery scopes itself to the per-allele `R²` and does not
    measure the AUC, so the `R²` it feeds is validated while this composition with
    `liabilityThresholdAUCFromExplainedR2` is not. -/
noncomputable def cleanSplitTargetAUC' (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT : ℝ) (t : ℕ) (ldFactor K : ℝ) : ℝ :=
  liabilityThresholdAUCFromExplainedR2 (cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor) K

/-- The AUC prediction is the `R²` prediction put through the liability chart, and nothing
    else. Stated so the two cannot drift apart under later edits. -/
theorem cleanSplitTargetAUC'_eq (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ) (NeS NeT : ℝ) (t : ℕ)
    (ldFactor K : ℝ) :
    cleanSplitTargetAUC' r2_0 w p NeS NeT t ldFactor K =
      liabilityThresholdAUCFromExplainedR2
        (cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor) K :=
  rfl

/-!
### Two metrics the simulations report, given laws

`cleanSplitTargetR2'` predicts an `R²`. The simulation harness reports two other numbers
alongside it — an odds ratio per standard deviation of score, and a squared correlation with
the truth — and neither had a law here to be compared against. The declarations below supply
them. Both are UNTESTED and both name honestly what they do NOT cover.
-/

/-- **Risk at a given score, under the liability-threshold model.** A liability
    `√r2 · z + √(1-r2) · e` with `e` standard normal crosses the threshold
    `liabilityThreshold K` with probability `Φ((√r2·z - T)/√(1-r2))`, and no other.

    THE SIGN IS THE CORPUS'S AND IT IS NOT FREE. `liabilityThreshold K` is
    `Φ⁻¹(1 - K)`, the UPPER-tail quantile — positive for a rare trait — because the model
    puts cases ABOVE the threshold. So the threshold enters this index with a MINUS, and at
    `r2 = 0` the risk is `Φ(-T)`, which is the prevalence. Writing `+T` instead inverts the
    trait: it would report a 95% risk at average score for a 5%-prevalence disease. That is
    the same sign slip `liabilityThreshold`'s own docstring records as FALSIFIED at 3390 sems
    and 200% relative, and it is indistinguishable from the correct reading only at
    `K = 1/2`.

    THE PREVALENCE CHECK IS NOW A THEOREM, and it is the sign convention's warrant.
    `liabilityRiskAtScore_at_zero_r2_eq_prevalence` below proves
    `liabilityRiskAtScore 0 K z = K` for `0 < K < 1`: with no explained variance the model
    must return the population prevalence at every score, and this body does. That check
    needs `Φ (liabilityThreshold K) = 1 - K` — that is, that `Φ` is onto `(0,1)`, so that
    `Function.invFun` returns a genuine preimage — which `PresentDayMoments` recorded as a
    gap where it deletes `LiabilityThresholdRegime`. `Foundations.Phi_surjOn_Ioo` supplies
    it (continuity plus the limits at `±∞` plus the intermediate value theorem) and
    `Foundations.Phi_neg` carries `Φ(-T)` back to `1 - Φ(T)`. Under the `+T` reading the
    same computation returns `1 - K`, so the check separates the two conventions at every
    prevalence but `K = 1/2`.

    Empirical status: **VALIDATED** (`validation/empirical/simcov/battery_liab01.py`). Direct
    liability-threshold simulation, `liability = √r2·z + √(1-r2)·e` with `e` an independent
    standard normal and a case a liability above `liabilityThreshold K`, 20 million
    individuals per block at each score and 8 independent blocks, across `r2 ∈ {0.10, 0.30,
    0.60}` and `K ∈ {0.05, 0.10, 0.20}` at `z = 0` and `z = 1`. Worst cell 2.97 sems and 0.29%
    relative over all 18 cells. Power: the predicted risk spans 0.0047 to 0.4578, a factor
    of 97.

    THE SCORE IS HELD AT EXACTLY `z` rather than binned near it, and that is what the body
    claims — the risk AT a score, not the risk averaged over a neighbourhood of it. An earlier
    version of the design binned at half-width 0.05 and carried the bin's curvature smear,
    0.42% relative, which is inside the harness's 2% floor but showed at 5.7 sems. A floor
    covering for a known estimator bias is not a design that is right, so the estimator was
    replaced rather than the tolerance widened.

    THE SIGN IS MEASURED AND NOT ASSUMED. The `+T` reading, carried as a competitor in the same
    cells, is FALSIFIED at 222024 sems — at `r2 = 0.60, K = 0.05` it returns 0.9999 where the
    simulation gives 0.0047. The two readings coincide at `K = 1/2` and at no other prevalence,
    so a design that never ran it could not have said which one it had confirmed.

    argument_source: model. `r2` and `K` are the simulation's own parameters. The control is
    the marginal prevalence at `r2 = 0.30, K = 0.05`, which must be `K` itself and is
    independent of every body in the file: predicted 0.050000, measured 0.049997 ± 0.000023.
    The `r2 = 0` case, `liabilityRiskAtScore_at_zero_r2_eq_prevalence` below, is measured
    beside it at 0.049982 ± 0.000015 and is reported as a diagnostic rather than as a second
    gate, since taking whichever of two controls looks worse is a worst-of-N selection. -/
noncomputable def liabilityRiskAtScore (r2 K z : ℝ) : ℝ :=
  Foundations.Phi ((Real.sqrt r2 * z - liabilityThreshold K) / Real.sqrt (1 - r2))

/-- **Odds ratio per standard deviation of score**, under the liability-threshold model: the
    odds of disease at a score one SD above the mean, divided by the odds at the mean. This
    is the law-side counterpart of the simulations' `or_per_sd` metric, which until now had
    no declaration to be compared against.

    The quantity is a RATIO OF ODDS, not of risks: the risk ratio and the odds ratio agree
    only in the rare-disease limit, and a battery reading one against the other would be
    measuring the gap between them rather than this body.

    Empirical status: **VALIDATED** (`validation/empirical/simcov/battery_liab01.py`), and the
    join it was written to test holds. Same design as `liabilityRiskAtScore` above and the same
    replicates:

      r2     K      this body   measured odds ratio    sems
      0.10   0.05    2.02833     2.02848 ± 0.00065      0.2
      0.10   0.20    1.76869     1.76806 ± 0.00050      1.3
      0.30   0.05    4.14736     4.14601 ± 0.00328      0.4
      0.30   0.20    3.05054     3.05139 ± 0.00096      0.9
      0.60   0.05   19.72958    19.78990 ± 0.01813      3.3
      0.60   0.20    8.36928     8.36576 ± 0.00179      2.0

    Worst cell 3.33 sems and 0.30% relative over all nine. Power: the prediction spans 1.77 to
    19.73, a factor of 11.

    THE ODDS RATIO IS THE FIRST STANDARD DEVIATION'S, AND THE MEASUREMENT RESPECTS THAT. The
    caveat below is now measured rather than expected: a logistic regression fitted over the
    WHOLE score range, carried as a competitor on the same replicates, disagrees at 279 sems
    and 83% relative — at `r2 = 0.60, K = 0.05` it returns 10.75 against this body's 19.73. So
    a battery reading a wide-range logistic slope against this declaration would be measuring
    the probit-versus-logistic gap and not this body, exactly as the note says.

    THE RISK RATIO IS NOT THIS QUANTITY, and the design decides it rather than assuming it.
    `risk(1)/risk(0)` measured on the same draws agrees with its own prediction at 3.30 sems,
    and it is a different number: 18.15 against this body's 19.73 at `r2 = 0.60, K = 0.05`,
    converging on it only as prevalence falls. The prevalence sweep runs 0.05 to 0.20 and
    stops there deliberately — below 0.05 the odds ratio's denominator is the case rate at
    `z = 0`, which at `K = 0.01, r2 = 0.60` is 1.2e-4 and cannot be measured to inside the
    harness's 2% relative floor by any affordable sample, so a rarer cell could contribute a
    spurious falsification and nothing else.

    The `+T` sign slip carried through the same odds ratio is FALSIFIED at 5889 sems.

    argument_source: model. Control as for `liabilityRiskAtScore`: the marginal prevalence at
    `r2 = 0.30, K = 0.05`, predicted 0.050000 and measured 0.049997 ± 0.000023.

    The model is probit and the metric is logistic: an odds ratio is constant per SD only under
    a logistic link, and under this probit model it is not, so this is the odds ratio for the
    FIRST standard deviation specifically and not a slope that may be extrapolated. -/
noncomputable def orPerSDFromLiability (r2 K : ℝ) : ℝ :=
  (liabilityRiskAtScore r2 K 1 / (1 - liabilityRiskAtScore r2 K 1)) /
    (liabilityRiskAtScore r2 K 0 / (1 - liabilityRiskAtScore r2 K 0))

/-- **At no explained variance the risk is flat at `Φ(-T)`**, the same at every score. This
    form holds for every real `K`, including the degenerate prevalences where
    `liabilityThreshold` is a junk `Function.invFun` value; the identification of `Φ(-T)`
    with `K` itself needs `0 < K < 1` and is the theorem below. -/
theorem liabilityRiskAtScore_at_zero_r2 (K z : ℝ) :
    liabilityRiskAtScore 0 K z = Foundations.Phi (-liabilityThreshold K) := by
  unfold liabilityRiskAtScore
  norm_num

/-- **At no explained variance the risk is the prevalence**: `liabilityRiskAtScore 0 K z = K`
    for every score `z`, whenever `0 < K < 1`.

    This is the sanity check the definition's docstring long recorded as unprovable here, and
    what made it provable is `Foundations.Phi_surjOn_Ioo`: `liabilityThreshold K` is
    `Function.invFun Φ (1 - K)`, an opaque value until `Φ` is known to hit `1 - K`, and
    surjectivity on `(0,1)` — the interval that `0 < K < 1` places `1 - K` inside —
    turns it into a genuine preimage. `Foundations.Phi_neg` then carries `Φ(-T)` to
    `1 - Φ(T) = 1 - (1 - K) = K`.

    It is also the sign test. Under the `+T` reading of `liabilityRiskAtScore` this same
    computation returns `Φ(T) = 1 - K`: a 95% risk at average score for a 5%-prevalence
    disease, which is the slip `liabilityThreshold`'s docstring records as FALSIFIED at 3390
    sems. The two readings agree only at `K = 1/2`.

    Empirical status: UNTESTED as a joint claim, and it needs no battery to be believed —
    it is a closed derivation from `Phi_surjOn_Ioo` and `Phi_neg`, both of which are proved
    from Mathlib's Gaussian. What a battery would measure is `liabilityRiskAtScore` at
    nonzero `r2`, where the body is not pinned by this boundary case. -/
theorem liabilityRiskAtScore_at_zero_r2_eq_prevalence (K z : ℝ) (hK0 : 0 < K) (hK1 : K < 1) :
    liabilityRiskAtScore 0 K z = K := by
  have hthr : Foundations.Phi (liabilityThreshold K) = 1 - K := by
    unfold liabilityThreshold
    exact Foundations.Phi_invFun_eq (1 - K) (by linarith) (by linarith)
  rw [liabilityRiskAtScore_at_zero_r2, Foundations.Phi_neg, hthr]
  ring

/-- **The risk is strictly increasing in the score** whenever the score explains anything.
    A body that failed this would have a higher polygenic score lowering risk. -/
theorem liabilityRiskAtScore_strictMono_score (r2 K z₁ z₂ : ℝ)
    (h0 : 0 < r2) (h1 : r2 < 1) (hz : z₁ < z₂) :
    liabilityRiskAtScore r2 K z₁ < liabilityRiskAtScore r2 K z₂ := by
  have hs : 0 < Real.sqrt (1 - r2) := Real.sqrt_pos.mpr (by linarith)
  have hr : 0 < Real.sqrt r2 := Real.sqrt_pos.mpr h0
  unfold liabilityRiskAtScore
  refine Foundations.strictMono_Phi ?_
  rw [div_lt_div_iff_of_pos_right hs]
  nlinarith [mul_lt_mul_of_pos_left hz hr]

/-- **No explained variance, no odds ratio.** With a flat risk curve the odds at one SD equal
    the odds at the mean, so the ratio is exactly one. `Foundations.Phi_pos` and
    `Foundations.Phi_lt_one` are what make this a real `1` rather than Lean's junk `0 / 0`:
    the odds are a genuine positive number, so they cancel. -/
theorem orPerSDFromLiability_at_zero_r2 (K : ℝ) : orPerSDFromLiability 0 K = 1 := by
  have hpos := Foundations.Phi_pos (-liabilityThreshold K)
  have hlt := Foundations.Phi_lt_one (-liabilityThreshold K)
  unfold orPerSDFromLiability
  rw [liabilityRiskAtScore_at_zero_r2, liabilityRiskAtScore_at_zero_r2]
  exact div_self (div_pos hpos (by linarith)).ne'

/-- **A score that explains anything raises the odds.** For any explained-variance fraction
    strictly between zero and one, the odds ratio per standard deviation is strictly above
    one. The mechanism is two strict monotonicities composed: the probit index is increasing
    in the score, `Φ` is strictly monotone (`Foundations.strictMono_Phi`), and `p ↦ p/(1-p)`
    is strictly increasing on `(0,1)`, where `Foundations.Phi_pos` and `Phi_lt_one` put both
    risks.

    THE PREVALENCE IS UNCONSTRAINED, which is worth stating because it looks like an
    omission. `K` enters only through the threshold `T`, and the argument shifts BOTH indices
    by the same `T`; the comparison survives any real threshold. So no `0 < K < 1` hypothesis
    is needed for the direction, and adding one would suggest the bound depends on a
    prevalence range when it does not. -/
theorem one_lt_orPerSDFromLiability (r2 K : ℝ) (h0 : 0 < r2) (h1 : r2 < 1) :
    1 < orPerSDFromLiability r2 K := by
  have hlt := liabilityRiskAtScore_strictMono_score r2 K 0 1 h0 h1 (by norm_num)
  set p0 := liabilityRiskAtScore r2 K 0 with hp0
  set p1 := liabilityRiskAtScore r2 K 1 with hp1
  have h0pos : 0 < p0 := Foundations.Phi_pos _
  have h0lt : p0 < 1 := Foundations.Phi_lt_one _
  have h1lt : p1 < 1 := Foundations.Phi_lt_one _
  have hodds0 : 0 < p0 / (1 - p0) := div_pos h0pos (by linarith)
  have hoddsmono : p0 / (1 - p0) < p1 / (1 - p1) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  unfold orPerSDFromLiability
  rw [← hp0, ← hp1]
  exact (one_lt_div hodds0).mpr hoddsmono

/-- **Squared correlation between the score-driven probit index and the true-liability index**,
    from the score's retention `rho` and the scale `s` of the independent noise the score
    carries.

    THE PROJECTION IDENTITY. Write the true-liability index as `a + b·z` and the score index as
    `a + b·ẑ` with `ẑ = rho·z + s·ε` and `ε` independent of `z`, both standardised. Then
    `Cov = b²·rho` and the variances are `b²·(rho² + s²)` and `b²`, so the squared
    correlation is `rho²/(rho² + s²)`: the intercept `a` cancels from a covariance and `b`
    cancels between numerator and denominator. Neither appears in this body, which is the
    content — the index-scale fidelity is a property of the score alone and not of the risk
    model wrapped around it. `indexScaleTrueIndexR2_slope_invariant` states the cancellation.

    ON THE STANDARDISED SCORE `s² = 1 - rho²` this reduces to `rho²`, the retained fraction —
    `indexScaleTrueIndexR2_of_standardized` — which is what makes it compose with
    `cleanSplitTargetR2'`.

    **THIS BODY CLAIMS THE INDEX SCALE ONLY, and the simulations do not measure that scale.**
    The harness's `r2_true` is a squared correlation between RISKS — probabilities, after the
    `Φ` warp — and `Φ` is not affine, so the two are not the same number and no closed form
    carries one to the other. The gap is smallest where the risk curve is closest to linear,
    which is the middle of the index range, and largest in the tails where a rare trait
    actually lives. So a battery comparing this body to a risk-scale `r2_true` would be
    measuring the warp, not this identity. Testing THIS declaration means correlating the
    indices, which a simulation can do because it knows the latent liability it drew.

    Empirical status: **VALIDATED** on the index scale
    (`validation/empirical/simcov/battery_liab01.py`). Standard normal `z` and independent
    standard normal `ε`, `ẑ = rho·z + s·ε`, the true-liability index `a + b·z` and the score
    index `a + b·ẑ`, 5 million draws per block and 8 blocks. Worst cell 2.81 sems and 0.03%
    relative. Power: the prediction spans 0.160 to 0.719, a factor of 4.5.

    HALF THE CELLS CARRY `s² ≠ 1 - rho²` AND A NONZERO INTERCEPT WITH A SLOPE OTHER THAN ONE,
    which is the whole reason the design decides anything. A run confined to standardised
    scores would have validated all three candidates at once:

      cell                              this body   measured   rho² alone   rho/(rho+s)
      rho=0.4, s=0.917, standardised      0.16000    0.15998     0.16000       0.30383
      rho=0.4, s=0.500, a=-1.64, b=0.65   0.39024    0.39017     0.16000       0.44444
      rho=0.6, s=0.500, a=-1.64, b=0.65   0.59016    0.59031     0.36000       0.54545
      rho=0.8, s=0.500, a=-1.64, b=0.65   0.71910    0.71900     0.64000       0.61538

    `rho²` alone — the standardised-score special case mistaken for the general body — is
    FALSIFIED at 2541 sems, and the unsquared reading `rho/(rho+s)` at 1938 sems. The affine
    cells are also what make `indexScaleTrueIndexR2_slope_invariant` a measured claim rather
    than a tautology: the intercept and slope are carried through the simulation and cancel.

    THE WARNING ABOVE IS NOW MEASURED. The risk-scale reading — correlating `Φ` of the two
    indices, which is what a simulation reports most easily — is FALSIFIED against this body
    at 497.81 sems and 11.2% relative, running 0.530 where the index scale gives 0.590. So the
    gap between the two scales is real and this body is the index-scale one; a design reaching
    for the risk scale would have measured the `Φ` warp.

    WHAT THIS DOES NOT ESTABLISH. The projection identity is a closed derivation, so agreement
    on the ratio itself is close to a construction check and is not claimed as more. What the
    run decides is carried by the three rivals and by the affine cells.

    argument_source: model. The control is the variance decomposition
    `Var(rho·z + s·ε) = rho² + s²`, which is not this body's ratio and fails on a draw slip,
    designated a priori as the design's largest-variance cell: predicted 1.000000, measured
    0.999602 ± 0.000219. It is designated rather than selected as the worst of the six because
    an earlier version took the worst and declared a failure at exactly 3.0 sems, voiding all
    three rivals — the worst-of-N false positive, arrived at in the control rather than in
    the cells. -/
noncomputable def indexScaleTrueIndexR2 (rho s : ℝ) : ℝ :=
  rho ^ 2 / (rho ^ 2 + s ^ 2)

/-- **The affine wrapper cancels.** Building the two indices with any nonzero slope `b`
    returns the same squared correlation, which is why the body carries neither slope nor
    intercept. The left-hand side is `Cov²/(Var·Var)` written out in the moments the
    projection gives. -/
theorem indexScaleTrueIndexR2_slope_invariant (b rho s : ℝ) (hb : b ≠ 0)
    (hden : rho ^ 2 + s ^ 2 ≠ 0) :
    (b ^ 2 * rho) ^ 2 / ((b ^ 2 * (rho ^ 2 + s ^ 2)) * b ^ 2) = indexScaleTrueIndexR2 rho s := by
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  unfold indexScaleTrueIndexR2
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hb2 hden) hb2) hden]
  ring

/-- **On a standardised score the index-scale fidelity IS the retained fraction.** This is the
    identity that lets the clean-split law's output be read directly as an index-scale `R²`
    without a further conversion. -/
theorem indexScaleTrueIndexR2_of_standardized (rho s : ℝ) (hs : s ^ 2 = 1 - rho ^ 2) :
    indexScaleTrueIndexR2 rho s = rho ^ 2 := by
  unfold indexScaleTrueIndexR2
  rw [hs]
  have : rho ^ 2 + (1 - rho ^ 2) = 1 := by ring
  rw [this, div_one]

/-- **The composition.** A score whose retained squared correlation is the clean-split law's
    predicted target `R²` has, on the probit-index scale, exactly that `R²` against the true
    liability index. The clean-split prediction therefore needs no conversion to be read as
    index-scale fidelity — and, by the definition's docstring, does need one to be read as the
    risk-scale number a simulation reports most easily. -/
theorem cleanSplitTargetR2'_eq_indexScaleTrueIndexR2 (r2_0 : ℝ) {M : ℕ} (w p : Fin M → ℝ)
    (NeS NeT : ℝ) (t : ℕ) (ldFactor rho s : ℝ)
    (hretain : rho ^ 2 = cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor)
    (hs : s ^ 2 = 1 - rho ^ 2) :
    indexScaleTrueIndexR2 rho s = cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor := by
  rw [indexScaleTrueIndexR2_of_standardized rho s hs, hretain]

end CleanSplit

/-!
## The migration-connected chain: a bracket, not a law

The clean split above is the easy demography — two closed branches, nothing crossing between
them — and the corpus can write a single composed number for it. A MIGRATION-CONNECTED CHAIN
cannot be written that way, and the reason is a measurement rather than a gap in effort.

Two effects run in opposite directions along such a chain. Drift and limited migration push
`F_ST` up with distance, which `steppingStoneFstGeneral` describes and which costs transported `R²`.
Ongoing gene flow also RESTORES shared linkage disequilibrium between demes, which recovers
some of what the LD stage takes away. The first effect has a validated body. The second does
not: `DGP.migrationLDBoost` is the corpus's only candidate and `simcov/battery_bulk55.py`
FALSIFIES it in magnitude at worst 15.6 sems and 62% relative, while rejecting no restoration
at all at 8.3 sems. So restoration is real and no formula for it survives.

That is what forces a bracket. The UPPER end applies the drift-and-migration penalty and no LD
penalty at all, which is the limit of complete restoration. The LOWER end multiplies the upper
by the LD retention a model with no restoration would predict. Any multiplicative-LD model
whose restoration lies between none and full lies between the two, which
`steppingStonePortability_mem_bracket` states.

TWO SEPARATE DEFECTS, and they should not be run together. The WIDTH is open because no
surviving formula picks the point inside it, and until one exists the width is the honest
report where a point prediction would not be. The LOWER END is a second matter: it is built
from ancestral `D` surviving recombination and carries none of the LD that drift regenerates
after the split, and the isolation arm recorded at `steppingStonePortability` measures the
truth exceeding it by a margin that GROWS with separation. An open width leaves the bracket
uninformative; a lower end the truth rises above leaves it unsound. The first was always the
report, the second is a repair owed to the floor.

`effectiveDriftGenerations` is the other half of instantiating such a chain. A stepping-stone
`F_ST` is a differentiation index, and a drift law wants a generation count; this inverts the
per-branch drift law to supply one.
-/

section MigrationChainBracket

/-- **The generation count a per-branch drift index implies.** Inverting
    `neutralDriftFactor`: the retention after `t` generations is `(1 - 1/(2·Ne))^t`, so the
    `t` at which the accumulated per-branch index reaches `F` is `log(1-F) / log(1-1/(2·Ne))`.
    Both logarithms are negative on the admissible range and the quotient is positive.

    THE ARGUMENT IS A PER-BRANCH INDEX, not a pairwise `F_ST`, and the two differ by the
    factor this corpus has paid for twice. `F` is the slot `fstFromDriftFactor` returns into —
    Wright's `F` for ONE lineage measured against the ancestor — because the law being
    inverted, `neutralDriftFactor`, is a single-branch retention. Feeding a pairwise Hudson
    value returns a generation count for a history that is not the one measured.

    JUNK VALUES, both from Lean's total division and total logarithm rather than from any
    modelling choice. At `F = 1` no finite generation count is implied, and this returns `0`
    because `log 0` is `0`; `effectiveDriftGenerations_at_full_index_is_junk` names it. At
    `Ne = 1/2` the per-generation retention is `0`, its logarithm is `0`, and the whole
    quotient is `0` at every `F`; `effectiveDriftGenerations_at_half_Ne_is_junk` names that.
    Below `Ne = 1/2` the retention goes negative and the logarithm is junk again. Consumers
    must require `1/2 < Ne` and `F < 1`.

    Empirical status: UNTESTED. It inherits its regime whole from `neutralDriftFactor` —
    closed population, no mutation — which is CONDITIONALLY VALID inside that regime and
    known to fail at demographic equilibrium, so an inverted generation count read off a
    population at mutation-drift balance is wrong for that reason and not for any reason
    about the inversion. A battery is owed and none has been run. -/
noncomputable def effectiveDriftGenerations (Ne F : ℝ) : ℝ :=
  Real.log (1 - F) / Real.log (1 - 1 / (2 * Ne))

/-- **The two in `2·Ne` is the corpus's ploidy, not a free constant.** A population of `Ne`
    diploids carries `ploidy · Ne` gene copies and drift acts at rate `1/(ploidy · Ne)`, so a
    haploid reading of this same inversion would return generation counts off by a factor of
    two in the drift rate — and off in the same direction at every index, which no range check
    would catch. Stated beside the definition so the numeral in the body is tied to the
    convention primitive wherever the definition is in scope. -/
theorem effectiveDriftGenerations_uses_ploidy (Ne F : ℝ) :
    effectiveDriftGenerations Ne F
      = Real.log (1 - F) / Real.log (1 - 1 / (Descent.Core.ploidy * Ne)) := by
  unfold effectiveDriftGenerations
  rw [Descent.Core.ploidy_at_reference_point]

/-- **No differentiation, no elapsed time.** The anchor of the inversion: an index of zero is
    reached at generation zero, for every population size. -/
theorem effectiveDriftGenerations_at_zero_index (Ne : ℝ) :
    effectiveDriftGenerations Ne 0 = 0 := by
  unfold effectiveDriftGenerations
  norm_num

/-- **effectiveDriftGenerations at complete differentiation, named.** A per-branch index of
    one is reached only in the limit, so the true value is unbounded. `Real.log 0` is `0` and
    the quotient is `0` — the value the function also takes at `F = 0`, which is the opposite
    end of the range. The two are indistinguishable in the output, so a consumer that reads a
    returned `0` as "no time has passed" is reading complete fixation the same way. -/
theorem effectiveDriftGenerations_at_full_index_is_junk (Ne : ℝ) :
    effectiveDriftGenerations Ne 1 = 0 := by
  unfold effectiveDriftGenerations
  norm_num

/-- **effectiveDriftGenerations at the smallest diploid population, named.** At `Ne = 1/2`
    there is one gene copy, the per-generation retention `1 - 1/(2·Ne)` is `0`, and `log 0`
    is Lean's `0`, so the divisor vanishes and every index returns generation `0`. The true
    reading is that all differentiation happens in one generation. Consumers must require
    `1/2 < Ne`. -/
theorem effectiveDriftGenerations_at_half_Ne_is_junk (F : ℝ) :
    effectiveDriftGenerations (1 / 2) F = 0 := by
  unfold effectiveDriftGenerations
  norm_num

/-- **More differentiation means more elapsed generations.** Strictly monotone in the index
    across `[0, 1)` whenever the population is large enough for the per-generation retention
    to be a probability.

    The sign bookkeeping is the whole content and it cancels twice. `log(1-F)` is negative and
    falls as `F` rises; the divisor `log(1-1/(2·Ne))` is negative and fixed; so the quotient
    rises. Writing the inversion with either logarithm's sign flipped produces a generation
    count that DECREASES with differentiation, which is monotone in the wrong direction and
    would not be caught by any range check. -/
theorem effectiveDriftGenerations_strictMono_index (Ne F₁ F₂ : ℝ)
    (hNe : 1 / 2 < Ne) (h0 : 0 ≤ F₁) (hlt : F₁ < F₂) (h1 : F₂ < 1) :
    effectiveDriftGenerations Ne F₁ < effectiveDriftGenerations Ne F₂ := by
  have hNe0 : 0 < 2 * Ne := by linarith
  have hfrac : 1 / (2 * Ne) < 1 := (div_lt_one hNe0).mpr (by linarith)
  have hfracpos : 0 < 1 / (2 * Ne) := div_pos one_pos hNe0
  have hL : Real.log (1 - 1 / (2 * Ne)) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  have hnum : Real.log (1 - F₂) < Real.log (1 - F₁) :=
    Real.log_lt_log (by linarith) (by linarith)
  have hkey : 0 < (Real.log (1 - F₂) - Real.log (1 - F₁)) / Real.log (1 - 1 / (2 * Ne)) :=
    div_pos_of_neg_of_neg (by linarith) hL
  have hsplit : (Real.log (1 - F₂) - Real.log (1 - F₁)) / Real.log (1 - 1 / (2 * Ne))
      = effectiveDriftGenerations Ne F₂ - effectiveDriftGenerations Ne F₁ := by
    unfold effectiveDriftGenerations
    ring
  rw [hsplit] at hkey
  linarith

/-- **The drift-and-migration UPPER bound on transported `R²` along a stepping-stone chain.**
    The stepping-stone `F_ST` at separation `d` put through the neutral portability chart, and
    nothing else — no LD penalty at all. That omission is what makes it an upper bound rather
    than a prediction: it is the transported `R²` a chain would retain if ongoing migration
    restored every bit of the linkage disequilibrium that divergence costs.

    The LOWER end of the bracket is this quantity times an LD retention, and this file does
    NOT define the retention. `DGP.migrationLDBoost` is the corpus's only candidate for how
    much migration restores and `simcov/battery_bulk55.py` falsifies it in magnitude, so
    there is no body to compose here. Writing one anyway — a placeholder factor with a
    plausible shape — would be the laundering this corpus guards against: a number a reader
    could take for a measured restoration when none survives measurement.

    Empirical status: UNTESTED. The stages carry their own verdicts and the join does not.
    `steppingStoneFstGeneral`'s saturating body is VALIDATED head to head at worst 1.87 sems with a
    free parameter withheld, the linear form FALSIFIED at 10.38 sems; `neutralPortability` is
    VALIDATED at worst 1.70 sems with the linear `1 - 2·fst` form FALSIFIED at 101 sems on the
    same cells. What is untested is that a stepping-stone `F_ST` is the argument
    `neutralPortability`'s `fst` slot wants, and the clean-split design settled the analogous
    question the other way: a summed two-branch index in that slot was FALSIFIED at 66.51 sems
    while a single branch's index passed. So this join is a live question here, not a
    formality.

    INFORMAL SUPPORT, WHICH IS NOT A VERDICT. An exploratory run at `Ne = 3000`, `m = 1e-3`, a
    ten-deme chain, 250 kb clumps and recombination `1.1e-8` had all ten deme means of the
    ancestry-calibration study inside the bracket this body's upper end defines. That run is
    not committed and no reader can check it, which is the standing the corpus assigns to no
    verdict at all; it is recorded as the reason a battery is being commissioned and not as
    evidence. A bracket is also a weak thing to pass: an interval wide enough to hold every
    plausible model is not confirmed by holding the data, and the battery owed here must
    measure the WIDTH against the restoration gap, not merely report containment.

    THE WIDTH MEASUREMENT IS NOW DELIVERED, and it is about the bracket's LOWER end
    (`validation/empirical/simcov/battery_ldwidth01.py`). Two demes of `Nₑ = 1000` split 250
    generations ago, 20 Mb, 200 diploids each, 30 replicates; the observable is
    `battery_bulk55`'s split-half cross-deme correlation of signed `r`, so no `E[noise²]`
    term survives. Pairs binned by map distance, and an ISOLATION arm where — there being no
    migration — the floor is the whole prediction rather than a bound:

      separation        floor   unascertained   MAF-only   score SNPs
      25-80 kb         0.6024   0.8188          0.8396     0.8968
      80-320 kb        0.3073   0.4972          0.5321     0.6510
      320-1000 kb      0.0471   0.0978          0.1119     0.1500

    THE ASCERTAINMENT FACTOR IS 1.1-1.5x AND NOT 1.8-5.9x, which is the finding. The
    derivation that corrected this floor modelled `MAF > 0.05` and NOT the clumping and
    p-thresholding a score applies, and it quantified that gap as needing a factor between
    1.8x and 5.9x for the corpus's inferred `λ` to be an LD quantity at all. Measured on the
    same replicates, the p-thresholded-and-clumped SNPs a per-allele score actually carries
    give 1.10x, 1.31x and 1.53x against unascertained pairs, and 1.07x, 1.22x and 1.34x
    against MAF-only. Every one of those is BELOW the band, so score ascertainment alone does
    not close it and the remaining mis-attribution is elsewhere. This ratio is the robust
    part of the run: it is taken across ascertainments ON THE SAME PAIRS, so any attenuation
    common to the estimator cancels out of it.

    THE FLOOR IS EXCEEDED EVEN UNASCERTAINED, by 1.36x, 1.63x and 2.09x, AND THE EXCESS
    GROWS WITH SEPARATION. That gradient is the finding, and an earlier version of this
    paragraph got it wrong by charging the whole gap to the `r`-versus-`D` normalisation.
    The correction is due to a reading of what the normalisation can do: `r` divides `D` by
    allele-frequency terms at the two loci, and those depend on drift and on the frequency
    spectrum but NOT on the recombination distance BETWEEN the loci. A change of
    normalisation can therefore move the level by a factor, uniformly — it cannot
    manufacture a factor that grows in `c`. So only the smallest-separation cell is covered:
    1.36x against the uniform 1.28x the drift term already predicts leaves about 6% for
    normalisation, which is plausible. The 1.63x and 2.09x are not covered by any
    normalisation and stand as measurement.

    WHAT THE GRADIENT IS. The corrected floor tracks only the ANCESTRAL `D` surviving
    recombination on both branches, and LD is continuously REGENERATED by drift after the
    split, with the two demes sharing the regenerated component to the extent they share
    recent ancestry. At small `c` the surviving ancestral term dominates and the floor is
    nearly right; as `c` grows the ancestral term dies exponentially while the regenerated
    one does not, so the floor underpredicts by more and more. This is the same functional
    error, seen from the opposite side, that sank the full-coalescent PGF derivation of the
    restoration law: `E[(1-c)^{2T}]` is the right functional for a GIVEN ancestral `D` and
    the wrong one for an LD CORRELATION. On that reading these three numbers are a direct
    measurement of the regeneration term, and a `D`-based rerun on the same replicates is
    still worth doing — not to settle the caveat, which is settled above, but to isolate the
    level shift so the gradient can be read cleanly. The prediction it would test is that the
    gradient SURVIVES the change of normalisation.

    A CONSEQUENCE FOR THE BRACKET ITSELF: a lower end that ignores regeneration is not a
    lower bound at large separation, so the interior positions computed against it — the
    pooled 0.546 among them — should not be quoted until they are redone against a floor
    that carries the regenerated share.

    What the isolation arm settles without any caveat is the drift term: the superseded floor
    `(1-c)^(2t)`, carried as a competitor, is a uniform 1.28x above the corrected one —
    which is `exp(t/Nₑ) = exp(0.25) = 1.2840`, recovered to three digits and uniform in
    separation as a constant factor must be — and is FALSIFIED at 13.63 sems. Omitting drift
    from the lower end was a real error of a size now measured rather than asserted.

    The control is a split at `t = 1`, one population, where the cross-deme LD correlation
    must be 1: measured 0.995290 ± 0.002158. -/
noncomputable def steppingStonePortability (r2_0 f1 : ℝ) (d : ℕ) : ℝ :=
  neutralPortability r2_0 (steppingStoneFst f1 d)

/-- **At zero separation the chain transports the source `R²` whole.** The deme compared with
    itself has no differentiation, and `neutralPortability` at index zero is the identity, so
    the composed law reduces to its own input with no hypotheses at all. A body that returned
    anything else here would be charging a transport penalty for not transporting. -/
theorem steppingStonePortability_at_zero_distance (r2_0 f1 : ℝ) :
    steppingStonePortability r2_0 f1 0 = r2_0 := by
  unfold steppingStonePortability neutralPortability steppingStoneFst
  rw [steppingStoneFstGeneral_at_zero]
  have hden : (1 - (0 : ℝ)) * r2_0 + (1 - r2_0) = 1 := by ring
  rw [hden, div_one]
  ring

/-- **The upper bound is a nonnegative `R²`.** Needed before anything may be multiplied into
    it: the bracket's lower end is this quantity scaled down, and scaling down is only a lower
    bound when what is scaled is nonnegative. -/
theorem steppingStonePortability_nonneg (r2_0 f1 : ℝ) (d : ℕ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hf : 0 < f1) (hf' : f1 < 1) :
    0 ≤ steppingStonePortability r2_0 f1 d := by
  unfold steppingStonePortability steppingStoneFst
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · rw [steppingStoneFstGeneral_at_zero]
    exact neutralPortability_nonneg r2_0 0 hr2 hr2' (by norm_num)
  · exact neutralPortability_nonneg r2_0 _ hr2 hr2'
      (steppingStoneFstGeneral_le_one f1 1 d hf hf'.le zero_le_one hpos)

/-- **Portability falls off along the chain.** Two monotonicities composed:
    `steppingStoneFst` rises with separation and `neutralPortability` falls with the index it
    is given. Stated
    from separation zero rather than one, so the source deme itself is inside the range and
    the fall-off is anchored at `steppingStonePortability_at_zero_distance`. -/
theorem steppingStonePortability_antitone_distance (r2_0 f1 : ℝ) (d₁ d₂ : ℕ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hf : 0 < f1) (hf' : f1 < 1)
    (hd : d₁ ≤ d₂) :
    steppingStonePortability r2_0 f1 d₂ ≤ steppingStonePortability r2_0 f1 d₁ := by
  unfold steppingStonePortability steppingStoneFst
  rcases Nat.eq_zero_or_pos d₂ with rfl | hpos
  · rw [Nat.le_zero.mp hd]
  · have hlt1 : steppingStoneFstGeneral f1 1 d₂ < 1 :=
      steppingStoneFstGeneral_lt_one f1 1 d₂ hf hf' one_pos hpos
    have hnn : 0 ≤ steppingStoneFstGeneral f1 1 d₁ := by
      rcases Nat.eq_zero_or_pos d₁ with rfl | hpos₁
      · exact (steppingStoneFstGeneral_at_zero f1 1).ge
      · exact steppingStoneFstGeneral_nonneg f1 1 d₁ hf hf'.le zero_le_one hpos₁
    have hmono : steppingStoneFstGeneral f1 1 d₁ ≤ steppingStoneFstGeneral f1 1 d₂ := by
      rcases eq_or_lt_of_le hd with rfl | h
      · exact le_rfl
      · exact (steppingStoneFstGeneral_increases_with_distance f1 1 d₁ d₂ hf hf' one_pos h).le
    exact neutralPortability_antitone_fst r2_0 _ _ hr2 hr2' hnn hmono hlt1

/-- **The bracket contains every intermediate restoration.** If the true multiplicative LD
    retention `ldFactor` lies anywhere between the no-restoration retention `ldLoss` and one —
    which is what "restoration between none and full" means — then the transported `R²` it
    predicts lies between the bracket's two ends.

    This is the theorem that makes the bracket a claim rather than two unrelated numbers. It
    does not say where inside the interval the truth is, and nothing in this corpus does:
    supplying the point is the outstanding empirical derivation, and the hypothesis
    `ldLoss ≤ ldFactor ≤ 1` is the whole of what may be assumed about it without one.

    **THE HYPOTHESIS IS NOT CURRENTLY DISCHARGED AT LARGE SEPARATION, AND THAT IS A FACT
    ABOUT THE FLOOR AND NOT ABOUT THIS THEOREM.** The implication below is algebra and holds
    whatever the two ends are. What is measured, on the isolation arm recorded at
    `steppingStonePortability`, is that a floor built from ancestral `D` surviving
    recombination is EXCEEDED by an excess that grows with separation, because LD is
    continuously regenerated by drift after the split and the floor carries none of it. A
    quantity the truth exceeds is not a lower bound, so `ldLoss ≤ ldFactor` is a hypothesis a
    caller must not assume from the no-restoration construction at large `c`.

    Two consequences for consumers. Interior positions computed against that floor are not
    quotable until it carries the regenerated share -- the pooled figure among them
    especially. And the width being open is not the same defect as the floor being wrong:
    the width was always open, whereas the lower end failing to bound is new, and only the
    second one makes the bracket unsound rather than uninformative. -/
theorem steppingStonePortability_mem_bracket (r2_0 f1 : ℝ) (d : ℕ) (ldLoss ldFactor : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hf : 0 < f1) (hf' : f1 < 1)
    (hlow : ldLoss ≤ ldFactor) (hhigh : ldFactor ≤ 1) :
    steppingStonePortability r2_0 f1 d * ldLoss
        ≤ steppingStonePortability r2_0 f1 d * ldFactor ∧
      steppingStonePortability r2_0 f1 d * ldFactor
        ≤ steppingStonePortability r2_0 f1 d := by
  have hnn := steppingStonePortability_nonneg r2_0 f1 d hr2 hr2' hf hf'
  exact ⟨mul_le_mul_of_nonneg_left hlow hnn, mul_le_of_le_one_right hnn hhigh⟩

/-- **The bracket is a nonempty interval of nonnegative `R²`.** The lower end is at or above
    zero and at or below the upper end, for any LD retention in `[0, 1]`. Stated separately
    from the membership theorem because a consumer plotting the band needs the endpoints to be
    ordered and in range before it needs to know what lies between them.

    Ordered and in range is all this says. Whether the lower end is where the truth actually
    sits above is the separate question `steppingStonePortability_mem_bracket`'s caveat
    answers, and at large separation the answer is currently no. -/
theorem steppingStonePortability_bracket (r2_0 f1 : ℝ) (d : ℕ) (ldLoss : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1) (hf : 0 < f1) (hf' : f1 < 1)
    (hld0 : 0 ≤ ldLoss) (hld1 : ldLoss ≤ 1) :
    0 ≤ steppingStonePortability r2_0 f1 d * ldLoss ∧
      steppingStonePortability r2_0 f1 d * ldLoss
        ≤ steppingStonePortability r2_0 f1 d := by
  have hnn := steppingStonePortability_nonneg r2_0 f1 d hr2 hr2' hf hf'
  exact ⟨mul_nonneg hnn hld0, mul_le_of_le_one_right hnn hld1⟩

end MigrationChainBracket

end Descent.Portability
