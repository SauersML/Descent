/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.SelectionArchitecture
import Descent.PopGen.DriftRegime
import Descent.Portability.PortabilityBounds
import Descent.Portability.PortabilityDrift.PresentDayMoments
import Descent.Portability.PortabilityDrift.MutationDrift

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

/-- **Below-neutral portability plus selected-variance excess identifies a
fluctuating/diversifying selection regime.**
    A subunit observed cross-population effect correlation by itself is not yet
    a regime label. But if the same trait also has selected-architecture
    variance above the stabilizing mutation-selection baseline, then the
    observed summary is matched by a fluctuating-selection regime and by no
    stabilizing regime. For fixed drift coordinates, that same observed effect
    correlation forces the portability ratio below the neutral drift baseline. -/
theorem worse_than_neutral_implies_fluctuating_regime
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
      observed_ratio < neutral_ratio ∧
      ¬ ∃ Ns,
        PopGen.effectCorrelationStabilizing Ns = rho_obs ∧
          PopGen.stabilizingSelectedArchitectureVariance v_mutation s = v_selected_obs := by
  dsimp
  have h_selection :
      (0 < PopGen.tauFromObservedEffectCorrelation t rho_obs ∧
        0 <
          PopGen.sigmaThetaFromObservedSelectedVariance
            v_selected_obs v_mutation s t rho_obs ∧
        PopGen.fluctuatingEffectCorrelation t
            (PopGen.tauFromObservedEffectCorrelation t rho_obs) = rho_obs ∧
        PopGen.fluctuatingSelectedArchitectureVariance v_mutation s
            (PopGen.sigmaThetaFromObservedSelectedVariance
              v_selected_obs v_mutation s t rho_obs)
            (PopGen.tauFromObservedEffectCorrelation t rho_obs) = v_selected_obs) ∧
      ¬ ∃ Ns,
        PopGen.effectCorrelationStabilizing Ns = rho_obs ∧
          PopGen.stabilizingSelectedArchitectureVariance v_mutation s = v_selected_obs := by
    exact PopGen.observedSummary_identifies_fluctuating_not_stabilizing
      v_mutation s t rho_obs v_selected_obs h_t h_rho h_rho_lt h_var_gap
  rcases h_selection with ⟨h_match, h_not_stab⟩
  have h_port :
      PopGen.TransportedMetrics.r2FromSignalVariance (realWorldPGSVariance V_A fstT rho_obs) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E <
        PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
          PopGen.TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    simpa [realWorldPGSVariance, presentDayPGSVariance, pgsVarianceFromHet, Descent.Core.product,
      mul_comm] using
      portability_ratio_with_ld_decay V_A V_E fstS fstT 1 rho_obs
        hVA hVE hfst hfstT_lt_one rfl ⟨h_rho, h_rho_lt⟩
  exact ⟨h_match, h_port, h_not_stab⟩

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
history is already here and separately measured — `neutralDriftFactor` for the retention in
each branch, `fstFromDriftFactor` for the drift index it implies, `neutralPortability` for
the `R²` a given index transports, the multiplicative LD penalty of
`neutralPortabilityRatioLD`, and `liabilityThresholdAUCFromExplainedR2` for the conversion to
discrimination. The definitions below compose them and nothing else, so that a battery has a
single name to aim at instead of a chain a reader has to assemble by hand.

THE SUMMATION CONVENTION IS THE LOAD-BEARING CHOICE and it is not free. `fstFromDriftFactor`
returns the PER-BRANCH drift coefficient — Wright's `F` measured against the ancestor within
ONE lineage — and its own docstring says so, distinguishing it from the pairwise Hudson
`F_ST`. Per-branch indices ADD over independent branches, which is the convention
`expectedSqMeanPGSDiff_pureSplit` feeds `Var_Delta_Mu` and which that definition's docstring
records as adjudicated after a two-branch design fed a pairwise value produced a
factor-of-four false falsification TWICE. `cleanSplitFst` therefore sums, and a battery that
fed it a pairwise value would be repeating the error the corpus has already paid for twice.

THE SUM IS NOT CONFINED TO THE UNIT INTERVAL, and this is a genuine restriction rather than
a technicality. Each branch index lies in `[0,1)`, so their sum reaches toward `2`, while
`neutralPortability` has a pole at `fst = 1`. `cleanSplitFst_lt_one_iff` below says exactly
when the composition is admissible: the two retentions must sum above one. Deep splits leave
that range, and there the composed prediction is not defined rather than merely inaccurate.
-/

section CleanSplit

/-- The drift index a clean two-branch split accumulates, as the SUM of the two per-branch
    coefficients.

    Empirical status: UNTESTED. A battery is being commissioned against this name and the two
    that compose it. What the battery must respect is the convention rather than the
    arithmetic: this is the sum of two PER-BRANCH Wright `F` values, the reading
    `fstFromDriftFactor` is validated at, and NOT a pairwise Hudson `F_ST`. Feeding a pairwise
    value here is the error `Var_Delta_Mu`'s docstring records as having produced a
    factor-of-four false falsification twice. The components carry their own measurements:
    `neutralDriftFactor` is CONDITIONALLY VALID inside the closed-population, no-mutation
    regime this definition also assumes, and `fstFromDriftFactor` is VALIDATED at worst 1.42
    sems on the same Wright-Fisher runs. -/
noncomputable def cleanSplitFst (NeS NeT : ℝ) (t : ℕ) : ℝ :=
  fstFromDriftFactor (neutralDriftFactor NeS t) +
    fstFromDriftFactor (neutralDriftFactor NeT t)

/-- **The composed target `R²` for a clean two-branch split.** The drift index of the split
    transported through the neutral portability chart, then scaled by the LD factor.

    Empirical status: UNTESTED, and a battery is being commissioned against this name.
    The composition is what is untested; every stage carries a measurement of its own.
    `neutralPortability` is VALIDATED at worst 1.70 sems with the superseded linear
    `1 - 2·fst` form FALSIFIED at 101 sems on the same cells. That the drift penalty and the
    LD penalty MULTIPLY rather than add is the validated content of
    `neutralPortabilityRatioLD`, where the additive reading is FALSIFIED at 41 sems, and
    `cleanSplitTargetR2_eq_ratioLD_scaling` below states that this body uses that combination
    and does not double-count the drift penalty inside it.

    WHAT A BATTERY MUST NOT INHERIT AS SETTLED. The join is the claim: that a summed
    per-branch drift index is the argument `neutralPortability`'s `fst` slot wants, and that
    an LD retention measured on tagging may multiply an `R²` measured on transport. Neither
    battery behind the two stages feeds the other's output, which is the same gap
    `targetLiabilityAUCFromNeutralAFBenchmark` records for its own composition. The regime is
    inherited whole from `neutralDriftFactor`: closed populations, no mutation, no migration.
    At demographic equilibrium the retention is stationary and this prediction is wrong for
    that reason and not for any reason about transport. -/
noncomputable def cleanSplitTargetR2 (r2_0 NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ) : ℝ :=
  neutralPortability r2_0 (cleanSplitFst NeS NeT t) * ldFactor

/-- **The composed target AUC for a clean two-branch split**, at a required prevalence.

    Empirical status: UNTESTED, with the same battery commissioned against it. Prevalence is a
    required argument for the reason `targetLiabilityAUCFromNeutralAFBenchmark` gives at
    length: converting a drift-induced `R²` drop to AUC through a prevalence-free chart is the
    fault that carried a `-0.068` bias, and making `K` mandatory is what prevents it.
    `liabilityThresholdAUCFromExplainedR2` is VALIDATED against 400 simulated PGS studies at
    pooled RMSE 0.0121 against a 0.0120 noise floor, with its prevalence axis swept; what is
    untested here is that the `R²` this file computes is the explained-variance fraction that
    chart's argument expects. -/
noncomputable def cleanSplitTargetAUC (r2_0 NeS NeT : ℝ) (t : ℕ) (ldFactor K : ℝ) : ℝ :=
  liabilityThresholdAUCFromExplainedR2 (cleanSplitTargetR2 r2_0 NeS NeT t ldFactor) K

/-- The AUC prediction is the `R²` prediction put through the liability chart, and nothing
    else. Stated so the two cannot drift apart under later edits. -/
theorem cleanSplitTargetAUC_eq (r2_0 NeS NeT : ℝ) (t : ℕ) (ldFactor K : ℝ) :
    cleanSplitTargetAUC r2_0 NeS NeT t ldFactor K =
      liabilityThresholdAUCFromExplainedR2 (cleanSplitTargetR2 r2_0 NeS NeT t ldFactor) K :=
  rfl

/-- **The LD penalty enters as the validated multiplicative factor.** `neutralPortabilityRatioLD`
    is the measured combination `(1 - fst_additional)·ld_factor`; read at zero additional `F_ST`
    it is the bare LD factor, which is what this composition multiplies in. The point of
    stating it is the zero: the drift penalty is carried ONCE, by `neutralPortability`, and is
    not applied a second time inside the LD stage. -/
theorem cleanSplitTargetR2_eq_ratioLD_scaling (r2_0 NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ) :
    cleanSplitTargetR2 r2_0 NeS NeT t ldFactor =
      neutralPortability r2_0 (cleanSplitFst NeS NeT t) *
        neutralPortabilityRatioLD 0 ldFactor := by
  unfold cleanSplitTargetR2 neutralPortabilityRatioLD Descent.Core.retainedFraction
  ring

/-- **The admissible range, exactly.** The composition is defined where the summed per-branch
    index stays below `neutralPortability`'s pole, and that is precisely where the two
    retentions sum above one. Beyond it the split is deep enough that the chart has no value,
    which a consumer must exclude rather than read. -/
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

/-- **The composition recovers the ancestral `R²` at the root.** At generation zero with no LD
    loss the target `R²` IS the source `R²`: the two penalties are the whole content of the
    prediction, and with neither of them active nothing is lost. A body that failed this would
    be predicting a drop with no elapsed time and no decayed tagging. -/
theorem cleanSplitTargetR2_at_zero_time (r2_0 NeS NeT : ℝ) :
    cleanSplitTargetR2 r2_0 NeS NeT 0 1 = r2_0 := by
  unfold cleanSplitTargetR2 neutralPortability
  rw [cleanSplitFst_at_zero_time]
  norm_num

/-- **The prediction is a genuine `R²`**: nonnegative, and never above the ancestral value.
    Both bounds need the admissible range, and the upper one needs the LD factor to be a
    retention rather than an amplification. -/
theorem cleanSplitTargetR2_mem_Icc (r2_0 NeS NeT : ℝ) (t : ℕ) (ldFactor : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1)
    (hfst0 : 0 ≤ cleanSplitFst NeS NeT t) (hfst1 : cleanSplitFst NeS NeT t < 1)
    (hld0 : 0 ≤ ldFactor) (hld1 : ldFactor ≤ 1) :
    0 ≤ cleanSplitTargetR2 r2_0 NeS NeT t ldFactor ∧
      cleanSplitTargetR2 r2_0 NeS NeT t ldFactor ≤ r2_0 := by
  have hnn := neutralPortability_nonneg r2_0 (cleanSplitFst NeS NeT t) hr2 hr2' hfst1.le
  have hle := neutralPortability_le_r2_0 r2_0 (cleanSplitFst NeS NeT t) hr2 hr2' hfst0 hfst1
  unfold cleanSplitTargetR2
  refine ⟨mul_nonneg hnn hld0, ?_⟩
  calc neutralPortability r2_0 (cleanSplitFst NeS NeT t) * ldFactor
      ≤ neutralPortability r2_0 (cleanSplitFst NeS NeT t) * 1 :=
        mul_le_mul_of_nonneg_left hld1 hnn
    _ = neutralPortability r2_0 (cleanSplitFst NeS NeT t) := mul_one _
    _ ≤ r2_0 := hle

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

/-- **The composed prediction decays with the age of the split.** More generations since the
    split means a larger summed drift index, and `neutralPortability` is decreasing in that
    index, so the transported `R²` can only fall. The LD factor is held fixed, which is the
    honest statement: this theorem is about the drift half of the composition, and a target
    whose tagging has also decayed falls further.

    The admissibility hypothesis is on the LATER time only. That is not a convenience — the
    index is monotone in time, so keeping the older split inside the pole automatically keeps
    the younger one there, and requiring it at both times would be redundant. -/
theorem cleanSplitTargetR2_antitone_time (r2_0 NeS NeT : ℝ) (t₁ t₂ : ℕ) (ldFactor : ℝ)
    (hr2 : 0 ≤ r2_0) (hr2' : r2_0 ≤ 1)
    (hS : 1 ≤ NeS) (hT : 1 ≤ NeT) (ht : t₁ ≤ t₂)
    (hfst0 : 0 ≤ cleanSplitFst NeS NeT t₁) (hfst1 : cleanSplitFst NeS NeT t₂ < 1)
    (hld : 0 ≤ ldFactor) :
    cleanSplitTargetR2 r2_0 NeS NeT t₂ ldFactor ≤
      cleanSplitTargetR2 r2_0 NeS NeT t₁ ldFactor := by
  have hmono := cleanSplitFst_monotone_time NeS NeT t₁ t₂ hS hT ht
  have hanti :=
    neutralPortability_antitone_fst r2_0 (cleanSplitFst NeS NeT t₁) (cleanSplitFst NeS NeT t₂)
      hr2 hr2' hfst0 hmono hfst1
  unfold cleanSplitTargetR2
  exact mul_le_mul_of_nonneg_right hanti hld

/-!
### Two metrics the simulations report, given laws

`cleanSplitTargetR2` predicts an `R²`. The simulation harness reports two other numbers
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

    Empirical status: UNTESTED. A battery is being commissioned against this name and against
    `orPerSDFromLiability`, which is built from it. -/
noncomputable def liabilityRiskAtScore (r2 K z : ℝ) : ℝ :=
  Foundations.Phi ((Real.sqrt r2 * z - liabilityThreshold K) / Real.sqrt (1 - r2))

/-- **Odds ratio per standard deviation of score**, under the liability-threshold model: the
    odds of disease at a score one SD above the mean, divided by the odds at the mean. This
    is the law-side counterpart of the simulations' `or_per_sd` metric, which until now had
    no declaration to be compared against.

    The quantity is a RATIO OF ODDS, not of risks: the risk ratio and the odds ratio agree
    only in the rare-disease limit, and a battery reading one against the other would be
    measuring the gap between them rather than this body.

    Empirical status: UNTESTED, and a battery is being commissioned against this name. The
    components are in different states and the composition is what is untested.
    `liabilityThreshold` is VALIDATED at worst 0.91 sems with the sign slip `Φ⁻¹(K)`
    FALSIFIED at 3390 sems, so the threshold convention this body inherits is measured. What
    is not measured is that the odds ratio a fitted logistic reports on simulated data is
    this function of the explained-variance fraction — which is the join, and joins are where
    this corpus has hidden errors before. Note also that the model is probit and the metric
    is logistic: an odds ratio is constant per SD only under a logistic link, and
    under this probit model it is not, so `orPerSDFromLiability` is the odds ratio for the
    FIRST standard deviation specifically and not a slope that may be extrapolated. A battery
    fitting a logistic regression over a wide score range will recover something between this
    and the odds ratio at other points. -/
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
    `cleanSplitTargetR2`.

    **THIS BODY CLAIMS THE INDEX SCALE ONLY, and the simulations do not measure that scale.**
    The harness's `r2_true` is a squared correlation between RISKS — probabilities, after the
    `Φ` warp — and `Φ` is not affine, so the two are not the same number and no closed form
    carries one to the other. The gap is smallest where the risk curve is closest to linear,
    which is the middle of the index range, and largest in the tails where a rare trait
    actually lives. So a battery comparing this body to a risk-scale `r2_true` would be
    measuring the warp, not this identity. Testing THIS declaration means correlating the
    indices, which a simulation can do because it knows the latent liability it drew.

    Empirical status: UNTESTED on the index scale. NOT TESTED BY THE DESIGN THAT LOOKED LIKE
    IT WAS would be the wrong head, since no design has been pointed at this body yet; the
    paragraph above is a warning about the design a battery would reach for first, not a
    record of one that ran. -/
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
theorem cleanSplitTargetR2_eq_indexScaleTrueIndexR2 (r2_0 NeS NeT : ℝ) (t : ℕ)
    (ldFactor rho s : ℝ)
    (hretain : rho ^ 2 = cleanSplitTargetR2 r2_0 NeS NeT t ldFactor)
    (hs : s ^ 2 = 1 - rho ^ 2) :
    indexScaleTrueIndexR2 rho s = cleanSplitTargetR2 r2_0 NeS NeT t ldFactor := by
  rw [indexScaleTrueIndexR2_of_standardized rho s hs, hretain]

end CleanSplit

end Descent.Portability
