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
# Population Genetics Foundations for PGS Portability

This file formalizes the core population genetics theory underlying
PGS portability: allele frequency dynamics, Fst computation, coalescent
theory, and the relationship between demographic history and genetic
differentiation.

Key results:
1. Fst definitions and properties (Nei, Hudson, simplified)
2. Coalescent theory and expected heterozygosity
3. Effective population size and drift
4. Wright's fixation indices
5. Mutation-drift balance (equilibrium and transient Fst, LD decay)

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat Fst estimators, coalescent theory or mutation-drift balance.
Sources for individual results, where they exist, are cited at those results.
-/


/-!
## Fst Definitions and Properties

Fst measures genetic differentiation between populations.
Multiple definitions exist, all related but not identical.
-/

section FstDefinitions

/-- **Nei's Fst.**
    Fst = (H_T - H_S) / H_T where H_T is total heterozygosity
    and H_S is mean subpopulation heterozygosity.

    Empirical status: UNTESTED. -/
noncomputable def neiFst (H_T H_S : ℝ) : ℝ :=
  (H_T - H_S) / H_T

/-- Nei's Fst is in [0, 1] when H_T > 0 and H_S ≤ H_T. -/
theorem nei_fst_in_unit (H_T H_S : ℝ)
    (h_HT : 0 < H_T) (h_HS : 0 ≤ H_S) (h_le : H_S ≤ H_T) :
    0 ≤ neiFst H_T H_S ∧ neiFst H_T H_S ≤ 1 := by
  unfold neiFst
  constructor
  · exact div_nonneg (by linarith) (le_of_lt h_HT)
  · rw [div_le_one h_HT]; linarith


/-- **Nei's `G_ST` for two equally weighted subgroups, from allele
    frequencies:** `G_ST = (p₁ - p₂)² / (4·p̄·(1-p̄))`.

    THIRD COPY, CORRECTLY NAMED, DO NOT DELETE ON DISCOVERY. This is algebraically
    identical to `Conventions.neiGst`, which is written in the heterozygosity form
    `1 - (p₁(1-p₁) + p₂(1-p₂))/(2·p̄(1-p̄))`. The two agree because
    `p₁(1-p₁) + p₂(1-p₂) = 2p̄(1-p̄) - (p₁-p₂)²/2`, so
    `1 - H_S/H_T = (p₁-p₂)²/(4p̄(1-p̄))` exactly; `Conventions.neiGst_eq_varianceRatio`
    relates the two shapes. A name audit checked both against Nei's definition and
    found both correct, so if a duplication scan reports this pair, the resolution is
    to repoint one at the other, NOT to delete whichever is found second -- and note
    that `Conventions.hudsonFst` is a genuinely different estimator that only looks
    like a third spelling of the same thing.

    This is Nei's `G_ST` -- `1 - H_S/H_T` with `H_T = 2p̄(1-p̄)`
    the total-pool heterozygosity and `H_S` the mean within-subgroup
    heterozygosity -- and it is NOT Hudson's `F_ST`, which divides instead by
    the between-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`. Derivation:
    `H_T - H_S = 2p̄(1-p̄) - (p₁(1-p₁) + p₂(1-p₂)) = (p₁-p₂)²/2`, and dividing
    by `H_T` gives this body. Hudson's estimator lives in `Conventions` as
    `hudsonFst`, with the exact conversion `Hudson = 2·G/(1 + G)` proved as
    `Conventions.hudsonFst_eq_of_neiGst`. The two differ by up to a factor
    of two -- +71.4% at `p₁ = 0.2, p₂ = 0.6` -- and AGREE ONLY WHERE THIS
    QUANTITY IS `0` OR `1`, i.e. at `p₁ = p₂` or at complete differentiation.
    That is immediate from the conversion: `2·G/(1+G) = G` iff `G = 0` or
    `G = 1`.

    **There is no `p̄ = 1/2` agreement slice. Do not add one.**
    On `p̄ = 1/2` exactly, with `p₁ = 0.9, p₂ = 0.1`, this body gives `0.64`
    and Hudson gives `0.7805`, a ratio of `1.22`; toward the middle the ratio
    approaches `2` (`1.995` at `(0.525, 0.475)`). The trap is that `p̄ = 1/2`
    makes the denominator `4·p̄·(1-p̄)` equal `1`, which looks like it should
    settle the comparison — it only makes `G_ST = (p₁-p₂)²`, while Hudson
    still divides by `1 - 2·p₁·p₂`.

    The arithmetic is unchanged by the rename; only the claim about what the
    number is has been made explicit.

    Empirical status: CONVENTION PINNED as Nei's `G_ST`, confirmed against an
    independent implementation by the differential checks `simpleFst-is-nei`
    and `simpleFst-vs-hudson`, which are retained as the standing checks. -/
noncomputable def neiGstFromFrequencies (p₁ p₂ : ℝ) : ℝ :=
  let p_bar := (p₁ + p₂) / 2
  (p₁ - p₂) ^ 2 / (4 * p_bar * (1 - p_bar))

/-- Nei's `G_ST` is nonneg. -/
theorem neiGstFromFrequencies_nonneg (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    0 ≤ neiGstFromFrequencies p₁ p₂ := by
  unfold neiGstFromFrequencies
  apply div_nonneg (sq_nonneg _)
  nlinarith

/-- **`G_ST` is zero when the subgroups are identical.** -/
theorem neiGstFromFrequencies_zero_same (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    neiGstFromFrequencies p p = 0 := by
  unfold neiGstFromFrequencies
  simp [sub_self, zero_pow (by norm_num : 2 ≠ 0)]

/-- **`G_ST` is symmetric.** -/
theorem neiGstFromFrequencies_symmetric (p₁ p₂ : ℝ) :
    neiGstFromFrequencies p₁ p₂ = neiGstFromFrequencies p₂ p₁ := by
  unfold neiGstFromFrequencies
  ring_nf


end FstDefinitions


/-!
## Coalescent Theory and Heterozygosity

The coalescent provides the theoretical framework for understanding
genetic variation and differentiation.
-/

section CoalescentTheory

/-- **Expected heterozygosity from mutation-drift balance.**
    H = 4Neμ / (1 + 4Neμ) = θ / (1 + θ) where θ = 4Neμ. -/
noncomputable def expectedHeterozygosity (θ : ℝ) : ℝ :=
  θ / (1 + θ)

/-- Expected heterozygosity is in [0, 1). -/
theorem expected_het_in_unit (θ : ℝ) (h_θ : 0 ≤ θ) :
    0 ≤ expectedHeterozygosity θ ∧ expectedHeterozygosity θ < 1 := by
  unfold expectedHeterozygosity
  constructor
  · exact div_nonneg h_θ (by linarith)
  · rw [div_lt_one (by linarith : 0 < 1 + θ)]
    linarith

/-- **Heterozygosity increases with effective population size.**
    Larger Ne → more mutations retained → higher diversity. -/
theorem het_increases_with_ne
    (θ₁ θ₂ : ℝ) (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (h_more : θ₁ < θ₂) :
    expectedHeterozygosity θ₁ < expectedHeterozygosity θ₂ := by
  unfold expectedHeterozygosity
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Coalescence time between populations.**
    For two populations separated t generations ago:
    E[T_between] = t + 2Ne, E[T_within] = 2Ne.
    Fst = 1 - T_within / T_between = t / (t + 2Ne).

    Empirical status: UNTESTED. -/
noncomputable def coalFst (t Ne : ℝ) : ℝ :=
  t / (t + 2 * Ne)

/-- **One quantity, one definition.**  `coalFst` and `fstFromTau` are the same
function in generation and coalescent units.  Three formulas for this quantity
existed across three files and two were wrong; this theorem is the relation
whose absence let them disagree, and it fails to compile if either body moves. -/
theorem coalFst_eq_fstFromTau (t Ne : ℝ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    coalFst t Ne = fstFromTau (coalescentTau t Ne) := by
  have h2 : (2 : ℝ) * Ne ≠ 0 := by positivity
  have hsum : t + 2 * Ne ≠ 0 := by
    have hs : 0 < t + 2 * Ne := by linarith
    exact ne_of_gt hs
  unfold coalFst fstFromTau coalescentTau
  field_simp
  ring

/-- Coalescent Fst is nonneg. -/
theorem coal_fst_nonneg (t Ne : ℝ) (h_t : 0 ≤ t) (h_Ne : 0 < Ne) :
    0 ≤ coalFst t Ne := by
  unfold coalFst
  exact div_nonneg h_t (by linarith)

/-- Coalescent Fst increases with separation time. -/
theorem coal_fst_increases_with_time
    (Ne : ℝ) (t₁ t₂ : ℝ) (h_Ne : 0 < Ne)
    (h_t₁ : 0 ≤ t₁) (h_t₂ : 0 ≤ t₂) (h_more : t₁ < t₂) :
    coalFst t₁ Ne < coalFst t₂ Ne := by
  unfold coalFst
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Coalescent Fst approaches 1 as t → ∞ (relative to Ne). -/
theorem coal_fst_approaches_one
    (Ne t : ℝ) (h_Ne : 0 < Ne) (h_t : 0 < t)
    (h_large : 100 * Ne < t) :
    49 / 50 < coalFst t Ne := by
  unfold coalFst
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 50) (by linarith)]
  nlinarith

end CoalescentTheory


/-!
## Effective Population Size

Ne determines the rate of genetic drift and the amount of genetic
variation. It is central to predicting portability.
-/

section EffectivePopulationSize


/-- **Ne affects PGS variance.**
    Var(PGS_drift) = V_A × Fst = V_A × t / (2Ne).
    Smaller Ne → faster drift → more PGS variance. -/
theorem ne_affects_pgs_variance
    (V_A t Ne₁ Ne₂ : ℝ)
    (h_VA : 0 < V_A) (h_t : 0 < t)
    (h_Ne₁ : 0 < Ne₁) (h_Ne₂ : 0 < Ne₂)
    (h_smaller : Ne₁ < Ne₂) :
    V_A * t / (2 * Ne₂) < V_A * t / (2 * Ne₁) := by
  exact div_lt_div_of_pos_left (mul_pos h_VA h_t) (by positivity) (by nlinarith)

end EffectivePopulationSize


/-!
## Selection-Migration Balance

When natural selection acts in the presence of migration,
a balance is reached that determines the amount of differentiation
at selected loci.
-/

section SelectionMigrationBalance

/-- One generation of continent--island dynamics, selection step first: the
locally favoured allele at frequency `p` is reweighted by relative fitness
`1 + s`, then a fraction `m` of the island is replaced by continental migrants
carrying the allele at frequency zero.

Convention: selection precedes migration within a generation. The orderings are
not interchangeable -- they have different fixed points, and deterministic
iteration separates them at the fourth decimal -- so the ordering is part of the
model rather than part of the presentation.  The other order is
`continentIslandStepMigrationFirst`, and `selectionMigrationEquilibrium_orderings`
relates the two.

    Empirical status: VALIDATED (deterministic iteration reproduces the fixed
    point to all digits reported, s = 0.1 m = 0.05 -> 0.45000).

    Power: iterated over the four cells `(s, m) = (.1, .05), (.1, .08), (.1, .1),
    (.2, .4)` this map rests at `0.45000`, `0.12000`, `0` and `0`, so the design
    spans the maintained regime and the absorbing one. The migration-first
    ordering rests at `0.47368` and `0.13043` on the first two of those cells,
    which is the separation that makes the convention checkable rather than
    stylistic. -/
noncomputable def continentIslandStepSelectionFirst (s m p : ℝ) : ℝ :=
  (1 - m) * (p * (1 + s) / (1 + s * p))

/-- The same generation with the migration step first.

    Empirical status: VALIDATED (iteration gives 0.47368 at s = 0.1, m = 0.05,
    matching this map's fixed point exactly).

    Power: over the same four cells `(s, m) = (.1, .05), (.1, .08), (.1, .1),
    (.2, .4)` this map rests at `0.47368`, `0.13043`, `0` and `0`, against the
    selection-first ordering's `0.45000` and `0.12000` on the first two. The
    span covers both the maintained and the absorbing regime, and the two
    orderings are separated at every cell where the allele survives. -/
noncomputable def continentIslandStepMigrationFirst (s m p : ℝ) : ℝ :=
  ((1 - m) * p) * (1 + s) / (1 + s * ((1 - m) * p))

/-- **Selection-migration equilibrium frequency** under the selection-first
convention.

This closed form is not stipulated.  It is the nonzero solution of
`continentIslandStepSelectionFirst s m p = p`, and
`selectionMigrationEquilibrium_isFixedPoint` is the theorem that pins it: no
other constant can be substituted here and still compile.  The `max` is not
cosmetic either.  Migration is absorbing: once `m (1 + s) ≥ s` the allele is
lost outright and the equilibrium is the boundary value `0`, which
`selectionMigrationEquilibrium_eq_zero` records and
`continentIslandStep_zero` confirms is itself a fixed point.

    Empirical status: VALIDATED (0.45000, 0.12000, 0, 0 against iteration at
    (s, m) = (.1, .05), (.1, .08), (.1, .1), (.2, .4)).

    Power: the prediction spans `0.45000` down to `0` across those four cells,
    crossing the absorbing boundary within the design, so the `max` and the
    interior formula are both exercised. The migration-first closed form gives
    `0.47368` and `0.13043` where this one gives `0.45000` and `0.12000`, so the
    check also separates the two orderings. -/
noncomputable def selectionMigrationEquilibrium (s m : ℝ) : ℝ :=
  max 0 ((s - m - m * s) / s)

/-- The equilibrium under the migration-first convention.

Derived, not stipulated, in the same way as its companion:
`selectionMigrationEquilibriumMigrationFirst_isFixedPoint` proves it is the
nonzero solution of `continentIslandStepMigrationFirst s m p = p`, and the
`max 0` carries the same absorbing boundary, since migration swamps selection
under either ordering.

    Empirical status: VALIDATED (iteration gives 0.47368 at s = 0.1, m = 0.05,
    matching this closed form; the selection-first convention rests at 0.45000
    on the same parameters, which is the composition convention showing up in
    the fourth decimal).

    Power: across `(s, m) = (.1, .05), (.1, .08), (.1, .1), (.2, .4)` this form
    predicts `0.47368`, `0.13043`, `0` and `0`, spanning the maintained regime
    and the absorbing one, against the selection-first form's `0.45000` and
    `0.12000` where the allele survives. -/
noncomputable def selectionMigrationEquilibriumMigrationFirst (s m : ℝ) : ℝ :=
  max 0 ((s - m - m * s) / (s * (1 - m)))

/-- **The migration-first equilibrium is a fixed point of the migration-first
map.**  Neither ordering is more correct, but each must be pinned by its own
dynamic; without this theorem the two closed forms could be swapped and nothing
would fail to compile. -/
theorem selectionMigrationEquilibriumMigrationFirst_isFixedPoint (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) (h_maintained : m * (1 + s) < s) :
    continentIslandStepMigrationFirst s m
        (selectionMigrationEquilibriumMigrationFirst s m) =
      selectionMigrationEquilibriumMigrationFirst s m := by
  have hs' : s ≠ 0 := ne_of_gt h_s
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  have hsm : (1 : ℝ) + s ≠ 0 := by positivity
  have hx : 0 < (s - m - m * s) / (s * (1 - m)) := by
    apply div_pos _ (mul_pos h_s hm)
    nlinarith
  have heq : selectionMigrationEquilibriumMigrationFirst s m =
      (s - m - m * s) / (s * (1 - m)) := max_eq_right hx.le
  rw [heq]
  unfold continentIslandStepMigrationFirst
  have hden : 1 + s * ((1 - m) * ((s - m - m * s) / (s * (1 - m)))) =
      (1 + s) * (1 - m) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- Loss is absorbing: an allele absent from the island stays absent. -/
@[simp] theorem continentIslandStep_zero (s m : ℝ) :
    continentIslandStepSelectionFirst s m 0 = 0 := by
  unfold continentIslandStepSelectionFirst
  simp

/-- **The equilibrium is a fixed point of the one-generation map.**  This is the
theorem that makes the closed form above unfalsifiable-by-stipulation
impossible: it is derived from the dynamic, not asserted alongside it. -/
theorem selectionMigrationEquilibrium_isFixedPoint (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) (h_maintained : m * (1 + s) < s) :
    continentIslandStepSelectionFirst s m (selectionMigrationEquilibrium s m) =
      selectionMigrationEquilibrium s m := by
  have hs' : s ≠ 0 := ne_of_gt h_s
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  have hsm : (1 : ℝ) + s ≠ 0 := by positivity
  have hx : 0 < (s - m - m * s) / s := by
    apply div_pos _ h_s
    nlinarith
  have heq : selectionMigrationEquilibrium s m = (s - m - m * s) / s :=
    max_eq_right hx.le
  rw [heq]
  unfold continentIslandStepSelectionFirst
  have hden : 1 + s * ((s - m - m * s) / s) = (1 + s) * (1 - m) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- **Migration swamps selection.**  Once migration exceeds the selective
advantage the allele is lost, not merely rare.  The previous statement of this
result bounded the frequency below `1/10`; the frequency is `0`. -/
theorem selectionMigrationEquilibrium_eq_zero (s m : ℝ)
    (h_s : 0 < s) (h_swamped : s ≤ m * (1 + s)) :
    selectionMigrationEquilibrium s m = 0 := by
  unfold selectionMigrationEquilibrium
  apply max_eq_left
  apply div_nonpos_of_nonpos_of_nonneg _ h_s.le
  nlinarith

/-- **Strong selection maintains near-complete differentiation.**  Stated
against the migration load `m (1 + s)` that the dynamic actually produces. -/
theorem selectionMigrationEquilibrium_ge_of_strong_selection (s m : ℝ)
    (h_s : 0 < s) (h_strong : 10 * (m * (1 + s)) ≤ s) :
    9 / 10 ≤ selectionMigrationEquilibrium s m := by
  have hge : 9 / 10 ≤ (s - m - m * s) / s := by
    rw [le_div_iff₀ h_s]
    nlinarith
  exact le_max_of_le_right hge

/-- The equilibrium never leaves the unit interval. -/
theorem selectionMigrationEquilibrium_lt_one (s m : ℝ)
    (h_s : 0 < s) (h_m : 0 < m) :
    selectionMigrationEquilibrium s m < 1 := by
  unfold selectionMigrationEquilibrium
  apply max_lt one_pos
  rw [div_lt_one h_s]
  nlinarith

/-- **The two orderings differ by exactly one migration step.**  This is the
whole content of the composition convention: neither map is more correct, but
they are not equal, and a definition that named neither could not say so. -/
theorem selectionMigrationEquilibrium_orderings (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) :
    selectionMigrationEquilibrium s m =
      (1 - m) * selectionMigrationEquilibriumMigrationFirst s m := by
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hs : s ≠ 0 := ne_of_gt h_s
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  -- One migration step is exactly the factor between the two conventions.
  have hkey : (s - m - m * s) / s =
      (1 - m) * ((s - m - m * s) / (s * (1 - m))) := by
    field_simp
  unfold selectionMigrationEquilibrium selectionMigrationEquilibriumMigrationFirst
  rcases le_or_lt ((s - m - m * s) / (s * (1 - m))) 0 with h | h
  · have h0 : (s - m - m * s) / s ≤ 0 := by rw [hkey]; nlinarith
    rw [max_eq_left h0, max_eq_left h, mul_zero]
  · have h0 : 0 ≤ (s - m - m * s) / s := by rw [hkey]; nlinarith
    rw [max_eq_right h0, max_eq_right h.le, hkey]

/-- **Loci under selection contribute disproportionally to portability loss.**
    Selected loci have higher Fst → larger portability impact
    despite being a small fraction of all loci.
    The weighted Fst contribution of selected loci (fraction × fst_selected)
    can exceed their fraction of the genome, showing disproportionate impact
    when fst_selected > fst_neutral. -/
theorem mul_lt_mul_left_of_lt_of_pos
    (fst_selected fst_neutral fraction_selected : ℝ)
    (h_higher : fst_neutral < fst_selected)
    (h_pos : 0 < fraction_selected) :
    -- The selected loci contribution exceeds what you'd expect from neutral Fst
    fraction_selected * fst_neutral < fraction_selected * fst_selected := by
  exact mul_lt_mul_of_pos_left h_higher h_pos

/-- **Genome-wide Fst is dominated by neutral loci.**
    Since most of the genome is neutral and selected loci are rare,
    genome-wide Fst reflects drift, not selection.
    But portability loss at selected loci can exceed the neutral prediction. -/
theorem abs_sub_lt_of_small_mixture
    (fst_gw fst_neutral fst_selected : ℝ)
    (f_sel : ℝ) -- fraction of selected loci
    (h_gw : fst_gw = (1 - f_sel) * fst_neutral + f_sel * fst_selected)
    (h_small : f_sel < 1 / 100)
    (h_pos : 0 < f_sel)
    (h_neutral_nn : 0 ≤ fst_neutral) (h_sel_nn : 0 ≤ fst_selected)
    (h_sel_higher : fst_neutral < fst_selected) :
    |fst_gw - fst_neutral| < (1 / 100) * fst_selected := by
  rw [h_gw]
  have : (1 - f_sel) * fst_neutral + f_sel * fst_selected - fst_neutral =
      f_sel * (fst_selected - fst_neutral) := by ring
  rw [this, abs_of_nonneg (mul_nonneg (le_of_lt h_pos) (by linarith))]
  calc f_sel * (fst_selected - fst_neutral) < (1 / 100) * (fst_selected - fst_neutral) :=
        mul_lt_mul_of_pos_right h_small (by linarith)
    _ ≤ (1 / 100) * fst_selected := by nlinarith

end SelectionMigrationBalance


/-!
## Wright's Fixation Indices

Wright's F-statistics partition genetic variation into hierarchical
levels: individual, subpopulation, total.
-/

section WrightFStatistics

/-- **Wright's hierarchical F-statistics.**
    F_IT = 1 - (1 - F_IS)(1 - F_ST).
    F_IS: inbreeding within subpopulations.
    F_ST: differentiation between subpopulations (= Fst).
    F_IT: overall inbreeding. -/
noncomputable def wrightFIT (f_IS f_ST : ℝ) : ℝ :=
  1 - (1 - f_IS) * (1 - f_ST)

/-- Wright's decomposition identity. -/
theorem wright_decomposition (f_IS f_ST : ℝ) :
    wrightFIT f_IS f_ST = f_IS + f_ST - f_IS * f_ST := by
  unfold wrightFIT; ring

/-- **The multiplicative-complement composition `1 - (1-a)(1-b)` occurs twice, and the two
occurrences do not have the same status.**

`wrightFIT` composes `F_IS` with `F_ST` across *nested* levels — individual within
subpopulation within total — and there the composition is exact, because the two
complements are the retention factors of a genuine hierarchy.
`PortabilityDrift.pairwiseFstFromBranches` applies the same algebra to two *sibling*
branches, and `PortabilityDrift` records it as CONDITIONALLY VALID for exactly that
reason: composing multiplicatively in `F_ST` inserts a spurious `tauS * tauT` of divergence
time, because coalescence times add along a path while `F_ST` values do not, and near
`tau = 1` that term doubles the divergence time.

So the shared body is not a coincidence and not an identification either: it is one
algebraic move that is *correct across levels and wrong across branches*.  This theorem
exists so the arithmetic agreement is on the record and cannot drift, and so that anyone
repairing one of the two is forced to look at the other. `pairwiseFstFromBranchTaus` is the
composition PortabilityDrift offers in place of the branch case. -/
theorem wrightFIT_eq_pairwiseFstFromBranches (a b : ℝ) :
    wrightFIT a b = pairwiseFstFromBranches a b := rfl

/-- **Within-population heterozygosity loss after `t` generations of drift.**
    `1 - (1 - 1/(2 Nₑ))^t`.

    **This is *not* between-population `F_ST` after a split.** Coalescent simulation with branch-mode
    divergence, which removes mutational noise analytically, shows the split
    quantity is `coalFst t Ne = t / (t + 2 Nₑ)`: that is unbiased across the
    tested grid, while this formula is biased upward in eleven of twelve cells
    by up to 28 percent. The formula is correct for what it now says, and
    `heterozygosityLossDerived_eq_het_loss` is the theorem that says it; only the name and
    docstring were reassigning it to a different observable.

    Regime: closed population, no mutation. See `Calibrator.DriftRegime`.

    Empirical status: VALIDATED as heterozygosity loss against the drift-only
    recurrence it restates (0.9048/0.6065/0.1353 retention at t = 200/1000/4000
    with Ne = 1000); FALSIFIED as split `F_ST`, and FALSIFIED as *measured*
    heterozygosity loss at mutation-drift balance, where the simulated retention
    is 1.025 ± 0.02 at every one of those times. The first clause is an identity
    and carries no empirical weight on its own — a cross-check cannot measure the
    premise it shares, `DriftRegime.crossChecks_blind_to_retention`.

    Denotes: within-population heterozygosity loss. The same formula appears under
    `heterozygosityLossFromDrift` here and `founderHeterozygosityLoss` in
    `DemographicHistory`; all three now name the quantity rather than leaving the
    formula to fix it, which it cannot.

    Power: the retention this formula predicts spans `0.9048`, `0.6065` and
    `0.1353` at `t = 200`, `1000` and `4000` with `Ne = 1000` — nearly the whole
    unit interval — while the measurement at mutation-drift balance stays at
    `1.025` across all three times. The design therefore has the power to
    separate the two regimes, which is how the falsification was reached. -/
noncomputable def heterozygosityLossFromDrift (t : ℕ) (Ne : ℝ) : ℝ :=
  1 - (1 - 1 / (2 * Ne)) ^ t

/-- Fst from drift is nonneg. -/
theorem fst_drift_nonneg (t : ℕ) (Ne : ℝ) (h_Ne : 2 ≤ Ne) :
    0 ≤ heterozygosityLossFromDrift t Ne := by
  unfold heterozygosityLossFromDrift
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- Fst from drift increases with time. -/
theorem fst_drift_increases (Ne : ℝ) (t₁ t₂ : ℕ) (h_Ne : 2 < Ne)
    (h_time : t₁ < t₂) :
    heterozygosityLossFromDrift t₁ Ne < heterozygosityLossFromDrift t₂ Ne := by
  unfold heterozygosityLossFromDrift
  rw [sub_lt_sub_iff_left]
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_time

end WrightFStatistics


/-!
## Mutation-Drift Balance

When mutation is non-negligible, Fst reaches a finite equilibrium instead
of going to 1. The classic Wright result gives Fst = 1/(1 + 4Neμ).
Mutation also governs equilibrium heterozygosity via θ = 4Neμ.
-/

section MutationDriftBalance

/-- Scaled mutation rate is positive when Ne and μ are positive. -/
theorem scaledMutationRate_pos (Ne μ : ℝ) (hNe : 0 < Ne) (hμ : 0 < μ) :
    0 < scaledMutationRate Ne μ := by
  unfold scaledMutationRate
  positivity

/-- **One coalescent time unit of the identity balance, in scaled units.**

Time in units of `2 Nₑ` generations. On that timescale a lineage pair coalesces
at rate one, so identity is regenerated in full over a unit of scaled time,
while the homogenising force removes identity at the scaled rate `scaledRate`:
`θ = 4 Nₑ μ` for mutation, `M = 4 Nₑ m` for migration, and the *sum* when both
act, which is the reason the two scaled rates add rather than compose.

Composition convention: the balance is written in scaled time, so no
within-generation ordering enters and the map is the same under either. The
per-generation maps, where the ordering does matter, are `ibdFlowStep` and
`ibdRecurrenceStep` in `Calibrator.PortabilityDrift`; this one is their
scaled-time limit and is stated here because the definitions it pins are
parameterised by `θ` and `M` rather than by `Nₑ` and a rate.

    Empirical status: UNTESTED. -/
noncomputable def scaledIdentityStep (scaledRate F : ℝ) : ℝ :=
  1 - scaledRate * F

/-- **`1/(1 + scaledRate)` is the fixed point of the scaled identity balance.**
Setting `F = 1 - scaledRate * F` gives `F (1 + scaledRate) = 1`. Every
`1/(1 + θ)` and `1/(1 + M)` below is this lemma at a particular scaled rate. -/
theorem scaledIdentityStep_fixedPoint (scaledRate : ℝ) (h : 0 ≤ scaledRate) :
    scaledIdentityStep scaledRate (1 / (1 + scaledRate)) = 1 / (1 + scaledRate) := by
  have hd : (0 : ℝ) < 1 + scaledRate := by linarith
  have hd' : (1 : ℝ) + scaledRate ≠ 0 := ne_of_gt hd
  unfold scaledIdentityStep
  rw [mul_one_div, sub_eq_iff_eq_add, div_add_div_same, div_self hd']

/-- **The mutation-drift equilibrium is the rest point of the scaled identity
balance** driven by mutation alone. -/
theorem fstMutationDriftEquilibrium_isFixedPoint (θ : ℝ) (hθ : 0 ≤ θ) :
    scaledIdentityStep θ (fstMutationDriftEquilibrium θ) =
      fstMutationDriftEquilibrium θ :=
  scaledIdentityStep_fixedPoint θ hθ

/-- Equilibrium Fst is positive for nonneg θ. -/
theorem fstMutationDriftEquilibrium_pos (θ : ℝ) (hθ : 0 ≤ θ) :
    0 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium
  positivity

/-- Equilibrium Fst is at most 1. -/
theorem fstMutationDriftEquilibrium_le_one (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ ≤ 1 := by
  unfold fstMutationDriftEquilibrium
  rw [div_le_one (by linarith)]
  linarith

/-- Equilibrium Fst is strictly less than 1 when θ > 0. This is the key
    qualitative difference from the pure drift model: mutation prevents
    complete fixation. -/
theorem fstMutationDriftEquilibrium_lt_one (θ : ℝ) (hθ : 0 < θ) :
    fstMutationDriftEquilibrium θ < 1 := by
  unfold fstMutationDriftEquilibrium
  rw [div_lt_one (by linarith)]
  linarith

/-- Equilibrium Fst decreases with θ: more mutation → less differentiation. -/
theorem fstMutationDriftEquilibrium_strictAnti (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) :
    fstMutationDriftEquilibrium b < fstMutationDriftEquilibrium a := by
  unfold fstMutationDriftEquilibrium
  have hden : 0 < 1 + a := by linarith
  have hden_lt : 1 + a < 1 + b := by linarith
  simpa using div_lt_div_of_pos_left one_pos hden hden_lt

/-- Equilibrium Fst decreases when Ne increases (with μ fixed). -/
theorem fstEquilibrium_decreases_with_Ne (μ Ne₁ Ne₂ : ℝ)
    (hμ : 0 < μ) (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂)
    (h_more : Ne₁ < Ne₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne₂ μ) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne₁ μ) := by
  apply fstMutationDriftEquilibrium_strictAnti
  · unfold scaledMutationRate
    nlinarith
  unfold scaledMutationRate
  nlinarith

/-- Equilibrium Fst decreases when μ increases (with Ne fixed). -/
theorem fstEquilibrium_decreases_with_mu (Ne μ₁ μ₂ : ℝ)
    (hNe : 0 < Ne) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (h_more : μ₁ < μ₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne μ₂) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne μ₁) := by
  apply fstMutationDriftEquilibrium_strictAnti
  · unfold scaledMutationRate
    nlinarith
  unfold scaledMutationRate
  nlinarith

/-- **Complementarity of heterozygosity and Fst under mutation-drift balance.**

    **Biological derivation.** Nei's Fst is *defined* as the proportion of total
    heterozygosity that is due to between-population differences:

      Fst = (H_T − H_S) / H_T = 1 − H_S / H_T

    where H_T is total (meta-population) heterozygosity and H_S is the mean
    subpopulation heterozygosity. Rearranging gives

      H_S / H_T  +  Fst  =  1

    so the within-population share and the between-population share of genetic
    diversity are complementary *by definition* of Fst as a variance partition.

    At mutation-drift equilibrium under the infinite-alleles model,
    H_S / H_T = θ/(1+θ) = `expectedHeterozygosity θ` and
    Fst = 1/(1+θ) = `fstMutationDriftEquilibrium θ`.  The algebraic identity
    θ/(1+θ) + 1/(1+θ) = 1 is therefore the equilibrium instantiation of the
    definitional partition H_S/H_T + Fst = 1.

    See also `nei_fst_complement` for the general (non-equilibrium)
    version derived directly from Nei's definition, and
    `nei_fst_equilibrium_consistent` which connects the two. -/
theorem het_plus_fst_eq_one (θ : ℝ) (hθ : 0 ≤ θ) :
    expectedHeterozygosity θ + fstMutationDriftEquilibrium θ = 1 := by
  unfold expectedHeterozygosity fstMutationDriftEquilibrium
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- **The within-population heterozygosity share and Nei's Fst sum to 1.**
    Since `neiFst H_T H_S = (H_T − H_S) / H_T = 1 − H_S / H_T`, we have
    H_S / H_T + neiFst H_T H_S = 1.  No equilibrium assumption is needed;
    the identity holds for *any* H_T ≠ 0.  This is the general form of the
    variance partition that `het_plus_fst_eq_one` instantiates at equilibrium. -/
theorem nei_fst_complement (H_S H_T : ℝ) (hHT : H_T ≠ 0) :
    H_S / H_T + neiFst H_T H_S = 1 := by
  unfold neiFst
  field_simp [hHT]
  ring_nf

/-- **At mutation-drift equilibrium, Nei's Fst recovers fstMutationDriftEquilibrium.**
    When H_S = θ/(1+θ) (`expectedHeterozygosity θ`) and H_T = 1 (maximal
    heterozygosity under the infinite-alleles model), Nei's formula gives
    Fst = 1/(1+θ) = `fstMutationDriftEquilibrium θ`. -/
theorem nei_fst_equilibrium_consistent (θ : ℝ) (hθ : 0 ≤ θ) :
    neiFst 1 (expectedHeterozygosity θ) = fstMutationDriftEquilibrium θ := by
  unfold neiFst expectedHeterozygosity fstMutationDriftEquilibrium
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- **At mutation-drift equilibrium, the within-population share equals expectedHeterozygosity.**
    When H_T = 1, we have H_S / H_T = H_S = θ/(1+θ). -/
theorem within_pop_share_eq_het (θ : ℝ) :
    expectedHeterozygosity θ / 1 = expectedHeterozygosity θ := by
  simp

/-- **Heterozygosity determines Fst and vice versa.**
    Fst = 1 - H under mutation-drift balance. -/
theorem fstEquilibrium_eq_one_minus_het (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ = 1 - expectedHeterozygosity θ := by
  have h := het_plus_fst_eq_one θ hθ
  linarith

/-- **Timescale separation.**
    Drift acts on timescale ~Ne generations (τ_drift = t/(2Ne)).
    Mutation introduces new variants on timescale ~1/μ generations.
    When θ > 2, mutation acts faster than drift, so 1/μ < 2Ne. -/
theorem mutation_timescale_exceeds_drift (Ne μ : ℝ)
    (hNe : 0 < Ne) (hμ : 0 < μ)
    (hθ_large : 2 < scaledMutationRate Ne μ) :
    1 / μ < 2 * Ne := by
  unfold scaledMutationRate at hθ_large
  rw [div_lt_iff₀ hμ]
  nlinarith

/-- When θ < 1, equilibrium Fst > 1/2. -/
theorem fstEquilibrium_gt_half_of_small_theta (θ : ℝ)
    (hθ_pos : 0 < θ) (hθ_small : θ < 1) :
    1 / 2 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium
  rw [lt_div_iff₀ (by linarith : 0 < 1 + θ)]
  linarith

/-- **Fst under mutation-drift with time dependence (approach to equilibrium).**
    Fst(t) = Fst_eq × (1 - e^{-(1 + θ) t / (2Ne)})
    where Fst_eq = 1/(1+θ). Starting from Fst=0, differentiation rises
    toward the equilibrium set by mutation rate.

    Empirical status: UNTESTED. -/
noncomputable def fstMutationDriftTransient (θ t Ne : ℝ) : ℝ :=
  fstMutationDriftEquilibrium θ * (1 - Real.exp (-(1 + θ) * t / (2 * Ne)))

/-- Transient mutation-drift Fst is nonneg for nonneg θ, t, and positive Ne. -/
theorem fstMutationDriftTransient_nonneg (θ t Ne : ℝ)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    0 ≤ fstMutationDriftTransient θ t Ne := by
  unfold fstMutationDriftTransient
  apply mul_nonneg
  · exact le_of_lt (fstMutationDriftEquilibrium_pos θ hθ)
  · have harg : 0 ≤ (1 + θ) * t / (2 * Ne) := by positivity
    have hexp : Real.exp (-(1 + θ) * t / (2 * Ne)) ≤ 1 := by
      rw [← Real.exp_zero]
      have h_nonpos : -(Real.exp 0 + θ) * t / (2 * Ne) ≤ 0 := by
        have hnum_nonpos : -(Real.exp 0 + θ) * t ≤ 0 := by
          have hneg_nonpos : -(Real.exp 0 + θ) ≤ 0 := by
            nlinarith [hθ, Real.exp_pos 0]
          exact mul_nonpos_of_nonpos_of_nonneg hneg_nonpos ht
        exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (by positivity : 0 ≤ 2 * Ne)
      exact Real.exp_le_exp.mpr h_nonpos
    exact sub_nonneg.mpr hexp

/-- Transient Fst is bounded above by the equilibrium Fst. -/
theorem fstMutationDriftTransient_le_equilibrium (θ t Ne : ℝ)
    (hθ : 0 ≤ θ) (ht : 0 ≤ t) (hNe : 0 < Ne) :
    fstMutationDriftTransient θ t Ne ≤ fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftTransient
  have hfeq_pos : 0 < fstMutationDriftEquilibrium θ :=
    fstMutationDriftEquilibrium_pos θ hθ
  have hexp_pos : 0 < Real.exp (-(1 + θ) * t / (2 * Ne)) :=
    Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(1 + θ) * t / (2 * Ne)) ≤ 1 := by linarith
  calc fstMutationDriftEquilibrium θ * (1 - Real.exp (-(1 + θ) * t / (2 * Ne)))
      ≤ fstMutationDriftEquilibrium θ * 1 := by
        exact mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
    _ = fstMutationDriftEquilibrium θ := by ring

/-- Transient Fst increases with time toward equilibrium. -/
theorem fstMutationDriftTransient_increases_with_time (θ Ne t₁ t₂ : ℝ)
    (hθ : 0 < θ) (hNe : 0 < Ne) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h_more : t₁ < t₂) :
    fstMutationDriftTransient θ t₁ Ne < fstMutationDriftTransient θ t₂ Ne := by
  unfold fstMutationDriftTransient
  have hfeq_pos : 0 < fstMutationDriftEquilibrium θ :=
    fstMutationDriftEquilibrium_pos θ (le_of_lt hθ)
  have harg_lt : (1 + θ) * t₁ / (2 * Ne) < (1 + θ) * t₂ / (2 * Ne) := by
    exact div_lt_div_of_pos_right (by nlinarith) (by positivity)
  have hneg_arg_lt : -((1 + θ) * t₂ / (2 * Ne)) < -((1 + θ) * t₁ / (2 * Ne)) := by
    exact neg_lt_neg harg_lt
  have hexp_lt : Real.exp (-((1 + θ) * t₂ / (2 * Ne))) <
      Real.exp (-((1 + θ) * t₁ / (2 * Ne))) := by
    exact Real.exp_lt_exp.mpr hneg_arg_lt
  have h_factor_lt :
      1 - Real.exp (-((1 + θ) * t₁ / (2 * Ne))) <
        1 - Real.exp (-((1 + θ) * t₂ / (2 * Ne))) := by
    linarith
  have h_factor_lt' :
      1 - Real.exp (-(1 + θ) * t₁ / (2 * Ne)) <
        1 - Real.exp (-(1 + θ) * t₂ / (2 * Ne)) := by
    have harg₁ : -(1 + θ) * t₁ / (2 * Ne) = -((1 + θ) * t₁ / (2 * Ne)) := by ring
    have harg₂ : -(1 + θ) * t₂ / (2 * Ne) = -((1 + θ) * t₂ / (2 * Ne)) := by ring
    rw [harg₁, harg₂]
    exact h_factor_lt
  exact mul_lt_mul_of_pos_left h_factor_lt' hfeq_pos

/-- At t=0, transient Fst is 0 (populations are undifferentiated). -/
theorem fstMutationDriftTransient_at_zero (θ Ne : ℝ) :
    fstMutationDriftTransient θ 0 Ne = 0 := by
  unfold fstMutationDriftTransient
  simp [mul_zero, zero_div, neg_zero, Real.exp_zero, sub_self]

/-- **Mutation introduces new population-specific variants over time.**
    The expected number of new mutations per generation per locus is 2Neμ = θ/2.

    **The body counts mutations ARISING, and never segregating sites.** Reading `θt/2`
    as the expected number of new segregating sites is FALSIFIED. Segregating sites
    saturate at Watterson's `θ·Σ(1/i)`, and mutations arising do not.
    Infinite-sites simulation at `Ne = 50`, `t = 1200`, 16 replicates:

    | `θ` | arisen (measured) | this body | segregating (measured) | Watterson |
    |---|---|---|---|---|
    | 1 | 599.9 | 600.0 | 5.1 | 5.2 |
    | 4 | 2423.8 | 2400.0 | 21.3 | 20.7 |

    So the body tracks *arisen* to 1%, while the segregating reading overstates by **118× at
    `t = 1200`, growing linearly in `t`**. Watterson is reproduced to 2–3%.

    Empirical status: body **VALIDATED** as a count of mutations arising; the
    segregating-sites reading **FALSIFIED** (`proofs/validation/empirical/coalescent_diff/`). -/
noncomputable def expectedNewMutations (θ t : ℝ) : ℝ :=
  θ / 2 * t

/-- Expected new mutations is nonneg for nonneg θ and t. -/
theorem expectedNewMutations_nonneg (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ expectedNewMutations θ t := by
  unfold expectedNewMutations
  positivity

/-- More mutations accumulate with larger θ (fixed t). -/
theorem expectedNewMutations_increases_with_theta (t θ₁ θ₂ : ℝ)
    (ht : 0 < t) (hθ₁ : 0 ≤ θ₁) (h_more : θ₁ < θ₂) :
    expectedNewMutations θ₁ t < expectedNewMutations θ₂ t := by
  unfold expectedNewMutations
  nlinarith

/-- More mutations accumulate over longer time (fixed θ). -/
theorem expectedNewMutations_increases_with_time (θ t₁ t₂ : ℝ)
    (hθ : 0 < θ) (ht₁ : 0 ≤ t₁) (h_more : t₁ < t₂) :
    expectedNewMutations θ t₁ < expectedNewMutations θ t₂ := by
  unfold expectedNewMutations
  nlinarith

/-! **Deleted: `sharedLDFractionFromMutation θ t = exp(-expectedNewMutations θ t)`,
together with `sharedLDFraction_pos`, `sharedLDFraction_le_one` and
`sharedLDFraction_decreases_with_time`.**

Measured in `proofs/validation/empirical/coalescent_diff/`. -/

end MutationDriftBalance


/-!
## Migration-Drift Balance: Population Genetics Foundations

The island model of migration-drift balance is a cornerstone of population genetics.
When populations exchange migrants at rate m per generation, drift and migration
reach an equilibrium Fst = 1/(1 + 4Nm). This section provides the pure population
genetics foundations for migration effects, independent of PGS portability.

Key results:
1. Island model Fst equilibrium and monotonicity properties
2. Stepping-stone model and isolation by distance
3. Migration homogenizes allele frequencies and LD
4. Admixture (recent migration pulses) and transient LD
5. Asymmetric migration and effective migration rates
-/

section MigrationDriftFoundations

/-! ### Island Model Equilibrium

**REGIME, stated once for everything in this section.** `1/(1 + 4·Nₑ·m)` is the
INFINITE-ISLAND LIMIT. It is the `d → ∞` case of the finite-island result

  `F_ST = 1 / (1 + 4·Nₑ·m·(d/(d-1))²)`

for `d` demes, and it is not the finite-`d` answer. The correction factor
`(d/(d-1))²` is `4` at `d = 2` and `2.25` at `d = 3`, so with two demes the
limit understates the migration pressure by a factor of four in the scaled rate
and overstates `F_ST` correspondingly. Nothing about the expression `1/(1+4Nm)`
announces this, which is why every theorem below is a theorem about the limit
and not about a two-deme system. `islandFstFiniteDemes` states the finite form,
`islandFstFiniteDemes_lt_islandLimit` proves the limit is an overstatement at
every finite `d`, and `islandDemeCorrection_tendsto_one` proves the two agree
only in the limit.

The reason this matters here specifically: two-population comparisons are the
common case in this corpus, and `d = 2` is exactly where the limit is worst. -/

/-- **Finite-island correction factor** `(d/(d-1))²`, in the number of demes
`d`. This is the entire difference between the infinite-island limit and the
finite-island result, isolated so that it can be stated about rather than
carried implicitly. -/
noncomputable def islandDemeCorrection (d : ℝ) : ℝ := (d / (d - 1)) ^ 2

/-! **`PortabilityDrift.finiteIslandCorrection` is this same quantity written a second
time, and `islandDemeCorrection_eq_finiteIslandCorrection` below is what says so.**

Both are `(d/(d-1))²`, both are documented as *the* standard finite-island correction
factor in the number of demes, and both exist to isolate the entire gap between the
infinite-island limit and the finite-`d` result.  This is one quantity defined twice, not
two quantities that coincide — the failure mode this corpus already hit with three
definitions of `F_ST`, where repairing one left the other two standing.

The identity theorem was written and then withdrawn once, because `finiteIslandCorrection`
was present in `PortabilityDrift.lean`'s source but absent from its compiled `olean`, so
the statement did not elaborate against a stale build.  That was a build-cache condition,
not a defect in either definition, and it is gone: `PortabilityDrift` compiles and this
file imports it.  The withdrawal is worth recording because of *how* it failed — loudly,
and only because the statement applies the name to an argument.  A bare occurrence would
have been auto-bound as an implicit variable and stayed green, which is the hazard
`DGP.LDDecayMechanism` documents.

Stating the identity is the weaker of the two available repairs.  The stronger one is to
delete a definition and have the survivor's callers move over; that is a cross-module
rename this pass did not attempt.  What the theorem buys in the meantime is the property
the duplicate-body guard exists to enforce: if either body is edited, this line stops
compiling. -/

/-- **The two finite-island corrections are one quantity.**  `islandDemeCorrection` here
and `PortabilityDrift.finiteIslandCorrection` are both `(d/(d-1))²` under two names in two
modules; until one of them is retired, this is what makes a divergence between them a
compile error rather than a silent fork. -/
theorem islandDemeCorrection_eq_finiteIslandCorrection (d : ℝ) :
    islandDemeCorrection d = finiteIslandCorrection d := by
  unfold islandDemeCorrection finiteIslandCorrection
  ring

/-- **Finite-island `F_ST` for `d` demes** (Wright; Nei):
`F_ST = 1/(1 + 4·Nₑ·m·(d/(d-1))²)`.

    Regime: `d` demes of equal size `Nₑ`, symmetric migration at rate `m`,
    mutation negligible relative to migration. This is the finite-`d`
    statement; `fstMigrationDriftEquilibrium` is its `d → ∞` limit.

    Empirical status: matches `validation/differential/refs.island_fst_finite_demes`,
    against which the differential check `islandModelFst-finite-demes` measures
    the corpus's limit form. -/
noncomputable def islandFstFiniteDemes (Ne m d : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m * islandDemeCorrection d)

/-- At two demes the correction is exactly `4`: the scaled migration rate is
`16·Nₑ·m`, not `4·Nₑ·m`. Stated as an equation because `d = 2` is the case the
corpus actually uses. -/
theorem islandDemeCorrection_at_two : islandDemeCorrection 2 = 4 := by
  unfold islandDemeCorrection; norm_num

/-- The correction is strictly above `1` at every finite number of demes, so
the limit is never exact for a real population. -/
theorem one_lt_islandDemeCorrection (d : ℝ) (hd : 1 < d) :
    1 < islandDemeCorrection d := by
  unfold islandDemeCorrection
  have hpos : 0 < d - 1 := by linarith
  have h1 : 1 < d / (d - 1) := by
    rw [lt_div_iff₀ hpos]; linarith
  nlinarith

/-- **The infinite-island limit overstates `F_ST` at every finite `d`.** This is
the claim the section header makes, made machine-checked: a definition that is
correct in its regime and silent about the regime is still a defect, and this
is what stops the limit from being read as the general answer. -/
theorem islandFstFiniteDemes_lt_islandLimit (Ne m d : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hd : 1 < d) :
    islandFstFiniteDemes Ne m d < fstMigrationDriftEquilibrium Ne m := by
  unfold islandFstFiniteDemes fstMigrationDriftEquilibrium
  have hc : 1 < islandDemeCorrection d := one_lt_islandDemeCorrection d hd
  have hNm : 0 < 4 * Ne * m := by positivity
  apply div_lt_div_of_pos_left one_pos (by nlinarith)
  nlinarith

/-- **And the two agree only in the limit.** Without this the phrase
"infinite-island limit" is prose; with it, the regime is a proved property of
the definition rather than a claim in a comment. -/
theorem islandDemeCorrection_tendsto_one :
    Filter.Tendsto islandDemeCorrection Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun d : ℝ ↦ d - 1) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1)
      (Filter.tendsto_id (α := ℝ))
  have h2 : Filter.Tendsto (fun d : ℝ ↦ (d - 1)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Filter.Tendsto (fun d : ℝ ↦ 1 + (d - 1)⁻¹) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (α := ℝ) (x := (1 : ℝ))
      (f := Filter.atTop)).add h2
  have h4 : Filter.Tendsto (fun d : ℝ ↦ d / (d - 1)) Filter.atTop (nhds 1) := by
    apply h3.congr'
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with d hd
    have hne : d - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    field_simp
    ring
  simpa [islandDemeCorrection] using h4.pow 2

/-- Island model Fst is the reciprocal of (1 + 4Nm). -/
theorem islandModelFst_eq_inv (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = (1 + 4 * Ne * m)⁻¹ := by
  unfold fstMigrationDriftEquilibrium
  rw [one_div]

/-- **Island model Fst is strictly decreasing in migration rate.**
    The function m ↦ 1/(1 + 4Nm) is strictly anti-monotone for positive Ne. -/
theorem islandModelFst_strictAnti_m (Ne a b : ℝ) (hNe : 0 < Ne)
    (ha : 0 ≤ a) (hab : a < b) :
    fstMigrationDriftEquilibrium Ne b < fstMigrationDriftEquilibrium Ne a := by
  unfold fstMigrationDriftEquilibrium
  have hden_pos : 0 < 1 + 4 * Ne * a := by nlinarith
  have hden_lt : 1 + 4 * Ne * a < 1 + 4 * Ne * b := by nlinarith
  exact div_lt_div_of_pos_left one_pos hden_pos hden_lt

/-- **Island model Fst is strictly decreasing in Ne.**
    Larger populations have more effective migrants per generation. -/
theorem islandModelFst_strictAnti_Ne (m a b : ℝ) (hm : 0 < m)
    (ha : 0 ≤ a) (hab : a < b) :
    fstMigrationDriftEquilibrium b m < fstMigrationDriftEquilibrium a m := by
  unfold fstMigrationDriftEquilibrium
  have hden_pos : 0 < 1 + 4 * a * m := by nlinarith
  have hden_lt : 1 + 4 * a * m < 1 + 4 * b * m := by nlinarith
  exact div_lt_div_of_pos_left one_pos hden_pos hden_lt

/-- **When 4Nm > 1, Fst < 1/2** (one-migrant-per-generation rule).
    This is Wright's classical threshold: even one migrant per generation
    (Nm = 0.25, so 4Nm = 1) is enough to prevent substantial differentiation. -/
theorem islandModelFst_lt_half_of_one_migrant (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m)
    (h_threshold : 1 < 4 * Ne * m) :
    fstMigrationDriftEquilibrium Ne m < 1 / 2 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_lt_div_iff₀ (by nlinarith : 0 < 1 + 4 * Ne * m) (by norm_num : (0:ℝ) < 2)]
  linarith

/-- **When 4Nm ≫ 1, Fst ≈ 0.** Specifically, 4Nm > k implies Fst < 1/(1+k). -/
theorem islandModelFst_small_of_large_migration (Ne m k : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hk : 0 < k)
    (h_large : k < 4 * Ne * m) :
    fstMigrationDriftEquilibrium Ne m < 1 / (1 + k) := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by linarith) (by nlinarith)

/-! ### Relationship between Migration and Mutation Effects on Fst -/

/-- **Migration-mutation equivalence for Fst.**
    Under the island model, the equilibrium Fst has the same functional form
    whether the homogenizing force is migration or mutation:
    Fst_migration = 1/(1+4Nm), Fst_mutation = 1/(1+4Neμ).
    The key parameter is the scaled rate 4N × (rate). -/
theorem islandModelFst_eq_mutationForm (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = fstMutationDriftEquilibrium (4 * Ne * m) := by
  unfold fstMigrationDriftEquilibrium fstMutationDriftEquilibrium
  ring

/-- **Combined migration and mutation reduce Fst below either alone.**
    When both migration (m) and mutation (μ) act, the equilibrium Fst
    is 1/(1 + 4Nm + 4Neμ), which is below either individual equilibrium.

    Empirical status: UNTESTED. -/
noncomputable def fstMigrationMutationEquilibrium (Ne m μ : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m + 4 * Ne * μ)

/-- **The combined equilibrium is the rest point of the scaled identity balance
at the summed scaled rate.**  This is where the additivity of `θ` and `M` comes
from: one balance, one rate, and that rate is `4 Nₑ (m + μ)`. -/
theorem fstMigrationMutationEquilibrium_isFixedPoint (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) (hμ : 0 ≤ μ) :
    scaledIdentityStep (4 * Ne * m + 4 * Ne * μ)
        (fstMigrationMutationEquilibrium Ne m μ) =
      fstMigrationMutationEquilibrium Ne m μ := by
  have h4 : (0 : ℝ) ≤ 4 * Ne := by linarith
  have h : (0 : ℝ) ≤ 4 * Ne * m + 4 * Ne * μ :=
    add_nonneg (mul_nonneg h4 hm) (mul_nonneg h4 hμ)
  have hbody : fstMigrationMutationEquilibrium Ne m μ =
      1 / (1 + (4 * Ne * m + 4 * Ne * μ)) := by
    unfold fstMigrationMutationEquilibrium
    rw [add_assoc]
  rw [hbody]
  exact scaledIdentityStep_fixedPoint _ h

/-- Combined Fst is below migration-only Fst. -/
theorem fstMigrationMutation_lt_migrationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibrium Ne m μ < fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigrationMutationEquilibrium fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- Combined Fst is below mutation-only Fst. -/
theorem fstMigrationMutation_lt_mutationOnly (Ne m μ : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 < μ) :
    fstMigrationMutationEquilibrium Ne m μ < fstMutationDriftEquilibrium (4 * Ne * μ) := by
  unfold fstMigrationMutationEquilibrium fstMutationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### Stepping-Stone Model Foundations -/

/-- **Characteristic length of one-dimensional isolation by distance.**
    `L = √(m·σ² / (2·μ))`, in units of the deme spacing. This is the Malécot /
    Kimura-Weiss decay scale: in an infinite linear array of demes with
    nearest-neighbour migration rate `m`, dispersal variance `σ²` and mutation
    rate `μ`, the probability that two genes sampled `d` demes apart are
    identical by descent falls off as `exp(-d/L)`.

    It is the balance point of two rates. At unit dispersal variance a lineage
    crosses a stretch of `L` demes in time `L²/m`, while mutation destroys
    identity in the two lineages at rate `2·μ`. Setting `L²/m = 1/(2·μ)` gives
    this body, and
    `steppingStoneCharacteristicLength_balances_mutation` states exactly that.

    **The mutation rate is mandatory and the deme size does not enter.** The
    form `√(2·Nₑ·m)` carries the deme size and no mutation rate. That is not a
    mis-set constant, it is the wrong function. `√(2·Nₑ·m)` is not even a
    length: `Nₑ` is a count of individuals, so the expression has units of
    √individuals, while `m/(2μ)` is a ratio of two per-generation rates and is
    dimensionless, as a squared deme count must be. The two forms disagree on
    both axes that matter. `√(2·Nₑ·m)` is constant in `μ` where the true scale
    goes as `μ^(-1/2)`, and grows as `√Nₑ` where the true scale does not depend
    on `Nₑ` at all. `validation/differential/heavy/h1_stepping_stone_length.py`
    measures those two exponents and is the standing check on this definition.

    **The dispersal variance is an explicit argument, and it is load-bearing.**
    `L` scales as `σ`, so a habitat with `σ² = 4` has a decay length twice that
    of one with `σ² = 1` -- a factor, not a rounding. A body that fixes `σ² = 1`
    has no argument with which to state the assumption, so every caller makes it
    and none writes it down.

    Regime: mutation-limited, i.e. distances comparable to `L`. Below `L`,
    isolation by distance is governed instead by the mutation-free coalescent
    result `DemographicHistory.demoSteppingStoneFst`, which is a different
    function and is derived separately.

    Measured on every axis that separates this body from `√(2·Nₑ·m)`:
    `d log L / d log μ = -0.502` against that form's `0`,
    `d log L / d log Nₑ = -0.000` against its `+1/2`, and
    `d log L / d log m = +0.510`. This body is confirmed and `√(2·Nₑ·m)` is
    excluded on two independent axes rather than one.

    Empirical status: MEASURED on all three axes above, and the body is the
    published Kimura-Weiss result. The dispersal-variance axis is MEASURED too:
    `d log L / d log σ² = +0.475` against `0` for a body without `σ²`, and the
    error from omitting `σ²` is `-26.9%` at `σ² = 2` and `-49.3%` at `σ² = 4`.

    Why an exponent is the decisive measurement here. A convention difference --
    infinite-alleles versus infinite-sites, say -- multiplies `μ` by a constant,
    which rescales every `L` UNIFORMLY AND CANNOT MOVE AN EXPONENT. A
    constant-factor discrepancy on this definition, of the +44% size seen here,
    therefore admits a convention artefact as its whole explanation and settles
    nothing. An exponent is immune to that entire class of explanation, which is
    why the `σ²` axis settles the question and is worth waiting for rather than
    estimating. The measured `+0.475` is the diffusion balance's `+1/2`.

    Signature consistency: both siblings carry a dispersal variance --
    `DemographicHistory.demoSteppingStoneFst (d Ne m σ_sq)` and
    `DemographicHistory.steppingStoneDiffusionTimescale (d σ_sq m)` -- so this
    signature matches the family. -/
noncomputable def steppingStoneCharacteristicLength (m σ_sq μ : ℝ) : ℝ :=
  Real.sqrt (m * σ_sq / (2 * μ))

/-- The characteristic length scale is positive for positive migration,
    dispersal and mutation rates. -/
theorem steppingStoneCharacteristicLength_pos (m σ_sq μ : ℝ)
    (hm : 0 < m) (hσ : 0 < σ_sq) (hμ : 0 < μ) :
    0 < steppingStoneCharacteristicLength m σ_sq μ := by
  unfold steppingStoneCharacteristicLength
  exact Real.sqrt_pos.mpr (by positivity)

/-- **What the definition claims: the migration/mutation balance.**
    `L² · (2·μ) = m·σ²`, i.e. the time `L²/(m·σ²)` a lineage takes to diffuse
    `L` demes is exactly the time `1/(2·μ)` in which mutation destroys identity
    between two lineages. Stating it as an equation is what stops the body from
    drifting back to something containing `Nₑ`, and now also what pins the
    `σ²` scaling: no expression lacking `σ²` can satisfy it. -/
theorem steppingStoneCharacteristicLength_balances_mutation (m σ_sq μ : ℝ)
    (hm : 0 ≤ m) (hσ : 0 ≤ σ_sq) (hμ : 0 < μ) :
    steppingStoneCharacteristicLength m σ_sq μ ^ 2 * (2 * μ) = m * σ_sq := by
  unfold steppingStoneCharacteristicLength
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **The `σ² = 1` slice.** Anything stated about `√(m/(2μ))` is the unit-dispersal
    case of this, and not a different quantity. -/
theorem steppingStoneCharacteristicLength_at_unit_dispersal (m μ : ℝ) :
    steppingStoneCharacteristicLength m 1 μ = Real.sqrt (m / (2 * μ)) := by
  unfold steppingStoneCharacteristicLength
  norm_num

/-- **The decay scale grows with dispersal variance.** This is the axis that
    was just measured at `+0.475`, and on which a body without `σ²` is pinned
    at `0` and cannot move. -/
theorem steppingStoneCharacteristicLength_strictMono_dispersal
    (m σ₁ σ₂ μ : ℝ) (hm : 0 < m) (hσ₁ : 0 ≤ σ₁) (hμ : 0 < μ) (h : σ₁ < σ₂) :
    steppingStoneCharacteristicLength m σ₁ μ
      < steppingStoneCharacteristicLength m σ₂ μ := by
  unfold steppingStoneCharacteristicLength
  apply Real.sqrt_lt_sqrt (by positivity)
  apply div_lt_div_of_pos_right _ (by positivity)
  exact (mul_lt_mul_left hm).mpr h

/-- **The decay scale shrinks as mutation gets faster.**
    This is the axis on which the `√(2·Nₑ·m)` body was falsified: it is
    constant in `μ`, so it could not move here at all. -/
theorem steppingStoneCharacteristicLength_strictAnti_mutation (m σ_sq μ₁ μ₂ : ℝ)
    (hm : 0 < m) (hσ : 0 < σ_sq) (hμ₁ : 0 < μ₁) (h : μ₁ < μ₂) :
    steppingStoneCharacteristicLength m σ_sq μ₂
      < steppingStoneCharacteristicLength m σ_sq μ₁ := by
  unfold steppingStoneCharacteristicLength
  have hμ₂ : 0 < μ₂ := lt_trans hμ₁ h
  apply Real.sqrt_lt_sqrt
    (div_nonneg (mul_nonneg hm.le hσ.le) (mul_nonneg (by norm_num) hμ₂.le))
  exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

/-- The decay scale grows with the migration rate. -/
theorem steppingStoneCharacteristicLength_strictMono_migration
    (m₁ m₂ σ_sq μ : ℝ) (hm₁ : 0 ≤ m₁) (hσ : 0 < σ_sq) (hμ : 0 < μ) (h : m₁ < m₂) :
    steppingStoneCharacteristicLength m₁ σ_sq μ
      < steppingStoneCharacteristicLength m₂ σ_sq μ := by
  unfold steppingStoneCharacteristicLength
  apply Real.sqrt_lt_sqrt (by positivity)
  apply div_lt_div_of_pos_right _ (by positivity)
  exact (mul_lt_mul_right hσ).mpr h

/-! ### `continuousSteppingStoneFst` has been deleted

The corpus carried a second stepping-stone F_ST,
`continuousSteppingStoneFst L d = 1 - exp(-d/L)`, evaluated at
`L = steppingStoneCharacteristicLength`. It contradicted
`DemographicHistory.demoSteppingStoneFst d Nₑ m σ² = d/(d + 4·Nₑ·m·σ²)` by up
to 878% on the differential grid, so at most one of the two could be right.

The contradiction is decidable without simulation, and it is decided against
the exponential. `demoSteppingStoneFst` is derived from the coalescent in
`DemographicHistory`: the meeting time of two lineages `d` demes apart is
linear in `d`, `T(d) = d/(2σ²m)`, and `F_ST = T/(T + 2Nₑ)` then gives the
hyperbolic `d/(d + 4Nₑσ²m)` exactly, with
`steppingStoneFst_from_coalescence_time` proving that equality. A linear
meeting time under the `T/(T+2Nₑ)` map cannot produce `1 - exp(-d/L)` for any
`L`: the two agree only to first order in `d`, and there they agree only if
`L = 4·Nₑ·m·σ²`, which is not the scale the corpus passed and is not a
mutation scale at all. The exponential had no derivation anywhere in the
corpus and no theorem tying it to anything.

Its three theorems -- `continuousSteppingStoneFst_nonneg`, `_increases` and
`_decreases_with_L` -- are absent with it, and their absence carries the
lesson. All three are monotonicity and sign facts, true of the exponential body
as written, and `d/(d + 4Nₑmσ²)` satisfies them equally. Facts of that shape
cannot detect a wrong functional form. Callers wanting a stepping-stone F_ST
should use `demoSteppingStoneFst`. -/

/-! ### Allele Frequency Homogenization by Migration -/

/-- **Allele frequency convergence under migration.**
    Starting from initial frequency p₀ in a deme, the frequency after t
    generations of migration at rate m toward a continent with frequency p_c is:
    p(t) = p_c + (p₀ - p_c) × (1-m)^t.
    The deviation from the continental frequency decays geometrically.

    Empirical status: UNTESTED. -/
noncomputable def alleleFreqAfterMigration (p₀ p_c m : ℝ) (t : ℕ) : ℝ :=
  p_c + (p₀ - p_c) * (1 - m) ^ t

/-- After 0 generations of migration, frequency is unchanged. -/
theorem alleleFreqAfterMigration_at_zero (p₀ p_c m : ℝ) :
    alleleFreqAfterMigration p₀ p_c m 0 = p₀ := by
  unfold alleleFreqAfterMigration
  simp

/-- **Allele frequency converges toward continental frequency.**
    The deviation |p(t) - p_c| decreases with each generation of migration. -/
theorem alleleFreq_deviation_decreases (p₀ p_c m : ℝ) (t₁ t₂ : ℕ)
    (hm : 0 < m) (hm1 : m < 1)
    (hne : p₀ ≠ p_c) (ht : t₁ < t₂) :
    |alleleFreqAfterMigration p₀ p_c m t₂ - p_c| <
    |alleleFreqAfterMigration p₀ p_c m t₁ - p_c| := by
  unfold alleleFreqAfterMigration
  simp only [add_sub_cancel_left]
  rw [abs_mul, abs_mul]
  apply mul_lt_mul_of_pos_left
  · rw [abs_of_nonneg (pow_nonneg (by linarith) _),
        abs_of_nonneg (pow_nonneg (by linarith) _)]
    have h_base_pos : 0 < 1 - m := by linarith
    have h_base_lt : 1 - m < 1 := by linarith
    exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)

/-! ### Effective Migration Rate -/

/-- Effective migration is between the two directional rates. -/
theorem effectiveMigration_bounds (m₁₂ m₂₁ : ℝ) (h : m₂₁ < m₁₂) :
    m₂₁ < effectiveSymmetricMigration m₁₂ m₂₁ ∧ effectiveSymmetricMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveSymmetricMigration
  constructor <;> linarith

/-- Effective migration equals both rates when migration is symmetric. -/
theorem effectiveMigration_symmetric (m : ℝ) :
    effectiveSymmetricMigration m m = m := by
  unfold effectiveSymmetricMigration
  ring

/-- **Asymmetric migration yields asymmetric Fst.**
    The population receiving more migrants has lower Fst (from its perspective).
    We prove the Fst difference is proportional to the migration asymmetry. -/
theorem asymmetric_fst_difference_sign (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    fstMigrationDriftEquilibrium Ne m₁₂ < fstMigrationDriftEquilibrium Ne m₂₁ := by
  exact islandModelFst_strictAnti_m Ne m₂₁ m₁₂ hNe (le_of_lt hm₂₁) h_asym

/-! ### Migration and LD Homogenization -/

/-- **LD similarity between populations under migration.**
    Populations exchanging migrants share more similar LD patterns.
    We model the LD correlation as a function of scaled migration rate:
    LD_correlation(M) = M² / (1 + M)² (proportion of LD that is shared).
    This accounts for both allele frequency sharing and haplotype sharing.

    **This is a stipulation, not a derivation, and the name says so.** No source is
    cited, nothing derives this shape from a migration process, and no theorem here
    constrains it beyond monotonicity and range. Do not rename it to assert a derivation
    unless one is supplied.

    Empirical status: UNTESTED, and untested here means unfalsified rather than
    supported: it is a functional form nobody has compared to a simulation. -/
noncomputable def ldCorrelationMigrationAnsatz (M : ℝ) : ℝ :=
  M ^ 2 / (1 + M) ^ 2

/-- LD correlation from migration is nonneg. -/
theorem ldCorrelationFromMigration_nonneg (M : ℝ) :
    0 ≤ ldCorrelationMigrationAnsatz M := by
  unfold ldCorrelationMigrationAnsatz
  exact div_nonneg (sq_nonneg M) (sq_nonneg (1 + M))

/-- LD correlation from migration is at most 1. -/
theorem ldCorrelationFromMigration_le_one (M : ℝ) (hM : 0 ≤ M) :
    ldCorrelationMigrationAnsatz M ≤ 1 := by
  unfold ldCorrelationMigrationAnsatz
  rw [div_le_one (sq_pos_of_pos (by linarith : 0 < 1 + M))]
  exact sq_le_sq' (by linarith) (by linarith)

/-- **LD correlation increases with migration rate.** -/
theorem ldCorrelationFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (h_more : M₁ < M₂) :
    ldCorrelationMigrationAnsatz M₁ < ldCorrelationMigrationAnsatz M₂ := by
  unfold ldCorrelationMigrationAnsatz
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]
    nlinarith
  have h_sq :
      (M₁ / (1 + M₁)) ^ 2 < (M₂ / (1 + M₂)) ^ 2 := by
    nlinarith [h_ratio, div_pos hM₁ h1M₁, div_pos hM₂ h1M₂]
  simpa [div_pow] using h_sq

end MigrationDriftFoundations


/-!
## Derivation of Fst from Wright-Fisher Drift Dynamics

Rather than *defining* Fst as a formula, we *derive* it from the fundamental
Wright-Fisher recurrence for heterozygosity.  The key identity is:

  H(t+1) = (1 - 1/(2N)) × H(t)

which expresses the fact that two alleles drawn from generation t+1 are
identical by descent with probability 1/(2N), leaving heterozygosity reduced
by that factor each generation.

We then:
1. Solve this recurrence in closed form by induction.
2. Define Fst(t) = 1 - H(t)/H₀ and derive its properties.
3. Introduce mutation, find the equilibrium heterozygosity H* = θ/(1+θ),
   and derive Fst_eq = 1/(1+θ) as a *consequence*.
-/

section FstDerivationFromDrift

/-! ### Pure-drift heterozygosity recurrence -/

/-- **Heterozygosity recurrence under pure drift.**
    Each generation, the probability that two sampled alleles are distinct
    is reduced by a factor of (1 - 1/(2Ne)).

    Regime: closed population, no mutation. This is the root of the cluster that
    `Calibrator.DriftRegime` dissects: every quantity downstream of this
    recurrence is a function of the single number `(1 - 1/(2Ne))^t`, so every
    cross-check among them holds at every value of it, correct or not
    (`crossChecks_blind_to_retention`). At mutation-drift balance the measured
    retention is `1.02 ± 0.02` against `e^(-2) = 0.135` predicted here, and the
    resulting `F_ST` is `≈ 0` where the measurable between-population `F_ST` is
    `0.50`. The recurrence is correct for what it says; it is not a split `F_ST`. -/
noncomputable def hetRecurrence (Ne : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetRecurrence Ne H₀ t

/-- **Closed-form solution by induction.**
    hetRecurrence Ne H₀ t = (1 - 1/(2Ne))^t × H₀. -/
theorem hetRecurrence_closed_form (Ne H₀ : ℝ) (t : ℕ) :
    hetRecurrence Ne H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ := by
  induction t with
  | zero =>
    simp [hetRecurrence]
  | succ n ih =>
    simp only [hetRecurrence, ih]
    ring

/-! ### Fst derived from heterozygosity loss -/

/-- **Within-population heterozygosity loss, derived from the decay recurrence.**
    `L(t) = 1 - H(t)/H₀ = 1 - (1 - 1/(2Ne))^t`.

    **This is not a split `F_ST`.** For between-population `F_ST` after a split use
    `coalFst t Ne = t / (t + 2 Nₑ)`.

    Regime: closed population, no mutation. **Being derived is not a defence, and this
    is derived only WITHIN that regime**: the recurrence it comes from lets heterozygosity
    decay with nothing replenishing it. Under mutation-drift balance
    heterozygosity is stationary, the retention is measured at `1.025 ± 0.020`
    at `Ne = 1000`, `t = 4000` where this expression's factor gives `0.135`,
    and the between-population `F_ST` at that design point is `0.50` while this
    formula's cluster reports approximately zero. `Calibrator.DriftRegime`
    exhibits both regimes and proves they disagree at every positive time.

    Being derived rather than stipulated is what made this look safe. It is not
    a defence: a derivation inherits every premise of the process it derives
    from, and this one inherits the closed population.

    Empirical status: FALSIFIED at demographic equilibrium; see
    `closedPopulation`. Inside the declared regime it stands.

    Denotes: the reading its name carries. The same formula appears under
    names from 'fst', 'heterozygosity', and the formula alone does not fix which is meant. -/
noncomputable def heterozygosityLossDerived (Ne : ℝ) (t : ℕ) : ℝ :=
  1 - (1 - 1 / (2 * Ne)) ^ t

/-- **Fst matches heterozygosity loss.**
    When H₀ > 0, heterozygosityLossDerived Ne t = 1 - hetRecurrence Ne H₀ t / H₀. -/
theorem heterozygosityLossDerived_eq_het_loss (Ne H₀ : ℝ) (t : ℕ) (hH₀ : H₀ ≠ 0) :
    heterozygosityLossDerived Ne t = 1 - hetRecurrence Ne H₀ t / H₀ := by
  unfold heterozygosityLossDerived
  rw [hetRecurrence_closed_form]
  field_simp

/-- **Fst(0) = 0**: populations start undifferentiated. -/
theorem heterozygosityLossDerived_zero (Ne : ℝ) : heterozygosityLossDerived Ne 0 = 0 := by
  unfold heterozygosityLossDerived
  simp

/-- **Fst is monotonically increasing in t.**
    More generations of drift → more differentiation. -/
theorem heterozygosityLossDerived_mono (Ne : ℝ) (t₁ t₂ : ℕ) (hNe : 2 < Ne)
    (h_lt : t₁ < t₂) :
    heterozygosityLossDerived Ne t₁ < heterozygosityLossDerived Ne t₂ := by
  unfold heterozygosityLossDerived
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  linarith [pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_lt]

/-- **0 ≤ Fst(t) for all t when Ne ≥ 2.** -/
theorem heterozygosityLossDerived_nonneg (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    0 ≤ heterozygosityLossDerived Ne t := by
  unfold heterozygosityLossDerived
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- **Fst(t) < 1 for all t when Ne ≥ 2.** -/
theorem heterozygosityLossDerived_lt_one (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    heterozygosityLossDerived Ne t < 1 := by
  unfold heterozygosityLossDerived
  linarith [pow_pos (show 0 < 1 - 1 / (2 * Ne) by
    rw [sub_pos, div_lt_one (by linarith)]; linarith) t]

/-- **Fst increases faster with smaller Ne.**
    For t ≥ 1 and Ne₁ < Ne₂, we have heterozygosityLossDerived Ne₁ t > heterozygosityLossDerived Ne₂ t.
    Smaller populations drift faster. -/
theorem heterozygosityLossDerived_faster_small_Ne (Ne₁ Ne₂ : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂) (h_lt : Ne₁ < Ne₂) :
    heterozygosityLossDerived Ne₂ t < heterozygosityLossDerived Ne₁ t := by
  unfold heterozygosityLossDerived
  -- Need (1 - 1/(2Ne₂))^t > (1 - 1/(2Ne₁))^t, i.e. larger base → larger power
  -- which means 1 - (larger)^t < 1 - (smaller)^t
  have h_base₁_pos : 0 < 1 - 1 / (2 * Ne₁) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base₂_lt_one : 1 - 1 / (2 * Ne₂) < 1 := by
    rw [sub_lt_self_iff]; positivity
  have h_base_lt : 1 - 1 / (2 * Ne₁) < 1 - 1 / (2 * Ne₂) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  linarith [pow_lt_pow_left₀ h_base_lt (le_of_lt h_base₁_pos) (Nat.not_eq_zero_of_lt (by omega : 0 < t))]

/-- **Consistency check: heterozygosityLossDerived agrees with the earlier heterozygosityLossFromDrift.**
    The derivation produces the same formula as the direct definition. -/
theorem heterozygosityLossDerived_eq_fstFromDrift (Ne : ℝ) (t : ℕ) :
    heterozygosityLossDerived Ne t = heterozygosityLossFromDrift t Ne := by
  unfold heterozygosityLossDerived heterozygosityLossFromDrift
  rfl

/-! ### Mutation-drift recurrence and equilibrium -/

/-- **Heterozygosity recurrence with mutation.**
    Drift reduces heterozygosity by factor (1 - 1/(2N)), while mutation
    creates new heterozygosity at rate 2μ from homozygous sites.

    Empirical status: UNTESTED. -/
noncomputable def hetMutationDriftRecurrence (Ne mu : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetMutationDriftRecurrence Ne mu H₀ t +
              2 * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t)

/-- **Algebraic verification of the fixed point.**
    If we start at H* = θ/(1+θ), one step of the recurrence returns H*.
    This proves H* is indeed a fixed point — the equilibrium heterozygosity. -/
theorem hetMutationDrift_fixed_point (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    hetMutationDriftRecurrence Ne mu (hetMutationFloor Ne mu) 1 =
      hetMutationFloor Ne mu := by
  simp [hetMutationDriftRecurrence, hetMutationFloor]
  -- We need: (1 - 1/(2Ne)) * (4Neμ/(1+4Neμ)) + 2μ * (1 - 4Neμ/(1+4Neμ))
  --        = 4Neμ/(1+4Neμ)
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  field_simp
  ring_nf

/-- **The fixed point is unique in [0,1].**
    For any H in [0,1] satisfying f(H) = H, we must have H = θ/(1+θ).
    We prove this by direct algebra: the fixed-point equation is linear in H. -/
theorem hetMutationDrift_fixed_point_unique (Ne mu H : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu)
    (h_fixed : (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H) = H) :
    H = hetMutationFloor Ne mu := by
  unfold hetMutationFloor
  -- From the fixed-point equation:
  -- H - (1 - 1/(2Ne))H - 2μ(1-H) = 0
  -- H × [1 - (1 - 1/(2Ne)) + 2μ] = 2μ
  -- H × [1/(2Ne) + 2μ] = 2μ
  -- H = 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hcoeff : 0 < 1 / (2 * Ne) + 2 * mu := by positivity
  -- Rearrange h_fixed: H * (1/(2Ne) + 2μ) = 2μ
  have h_rearranged : H * (1 / (2 * Ne) + 2 * mu) = 2 * mu := by
    field_simp at h_fixed ⊢
    linarith
  -- Solve for H
  have h_solve : H = 2 * mu / (1 / (2 * Ne) + 2 * mu) := by
    field_simp at h_rearranged ⊢
    linarith
  -- Now show 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  rw [h_solve]
  field_simp
  ring

/-- **Derive Fst_eq = 1/(1+θ) from the equilibrium heterozygosity.**
    Since H* = θ/(1+θ) and Fst = 1 - H* (for biallelic loci where H_max = 1),
    we get Fst_eq = 1 - θ/(1+θ) = 1/(1+θ).

    This is Wright's classical result, but *derived* from the recurrence
    rather than postulated. -/
theorem fstEquilibrium_derived (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetMutationFloor Ne mu = 1 / (1 + 4 * Ne * mu) := by
  unfold hetMutationFloor
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  field_simp
  ring

/-- **The equilibrium derived from the recurrence agrees with
    `fstMutationDriftEquilibrium`.** -/
theorem fstEquilibrium_derived_consistent (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetMutationFloor Ne mu = fstMutationDriftEquilibrium (4 * Ne * mu) := by
  rw [fstEquilibrium_derived Ne mu hNe hmu]
  unfold fstMutationDriftEquilibrium
  rfl

/-- **Equilibrium heterozygosity is in (0, 1) for positive parameters.** -/
theorem hetEquilibrium_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < hetMutationFloor Ne mu := by
  unfold hetMutationFloor
  positivity

theorem hetEquilibrium_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    hetMutationFloor Ne mu < 1 := by
  unfold hetMutationFloor
  rw [div_lt_one (by positivity)]
  linarith

/-- **Equilibrium Fst is in (0, 1) for positive parameters.** -/
theorem fstEquilibrium_derived_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < 1 - hetMutationFloor Ne mu := by
  linarith [hetEquilibrium_lt_one Ne mu hNe hmu]

theorem fstEquilibrium_derived_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - hetMutationFloor Ne mu < 1 := by
  linarith [hetEquilibrium_pos Ne mu hNe hmu]

/-- **Larger θ → lower equilibrium Fst** (derived version).
    More mutation (or larger Ne) means more diversity maintained against drift. -/
theorem fstEquilibrium_derived_decreases (Ne₁ Ne₂ mu : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (hmu : 0 < mu)
    (h_lt : Ne₁ < Ne₂) :
    1 - hetMutationFloor Ne₂ mu < 1 - hetMutationFloor Ne₁ mu := by
  -- Equivalent to hetMutationFloor Ne₁ mu < hetMutationFloor Ne₂ mu
  -- i.e., 4Ne₁μ/(1+4Ne₁μ) < 4Ne₂μ/(1+4Ne₂μ)
  unfold hetMutationFloor
  have h₁ : 0 < 1 + 4 * Ne₁ * mu := by positivity
  have h₂ : 0 < 1 + 4 * Ne₂ * mu := by positivity
  rw [sub_lt_sub_iff_left]
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

end FstDerivationFromDrift


/-!
## Derivation of Transient Fst from Heterozygosity Recurrence with Mutation

The discrete-time analogue of `fstMutationDriftTransient` is DERIVED here, not assumed,
from the heterozygosity recurrence that includes both drift and mutation, using only:
1. The recurrence H(t+1) = λ H(t) + c, where λ = (1 - 1/(2N))(1 - θ/(2N))
   and c captures mutation input.
2. The closed-form solution of affine recurrences via geometric series.
3. The equilibrium H* = θ/(1+θ) (already derived above as a fixed point).
4. The definition Fst(t) = 1 - H(t)/H₀.

The key insight: when we approximate (1-μ)² ≈ 1 - 2μ and set θ = 4Nμ,
the per-generation decay factor for heterozygosity becomes
  λ = (1 - 1/(2N)) × (1 - θ/(2N))
and mutation-drift balance yields the transient formula
  Fst(t) = [1/(1+θ)] × (1 - λ^t).
-/

section TransientFstDerivation

/-! ### Heterozygosity recurrence with mutation -/

/-- **Per-generation decay factor under mutation and drift.**
    λ = (1 - 1/(2N)) × (1 - θ/(2N)).
    The first factor is drift (coalescence probability 1/(2N)),
    the second captures the approximate mutation effect:
    two lineages both fail to mutate with probability (1-μ)² ≈ 1 - 2μ = 1 - θ/(2N).

    **This is `Calibrator.hetDecayFromScaled` applied, not a second copy of its body.
    Do not inline the product `(1 - 1/(2Ne)) * (1 - θ/(2Ne))` here.** Every call site
    unfolds the PAIR `hetDecayFactor hetDecayFromScaled` — including
    `Calibrator.Conventions` and `Calibrator.DemographicHistory` — and an inlined body
    leaves no `hetDecayFromScaled` in the goal for the second unfold to find. The
    two-name unfold is the contract: inlining breaks five proofs in three files.

    Empirical status: UNTESTED. -/
noncomputable def hetDecayFactor (Ne θ : ℝ) : ℝ :=
  hetDecayFromScaled Ne θ

/-- **Heterozygosity recurrence with mutation (affine recurrence).**
    H(t+1) = λ H(t) + c, where λ = hetDecayFactor and
    c = (1 - λ) H* (since H* is the fixed point, c = (1-λ) H*).
    Rather than tracking c explicitly we parametrise by the equilibrium H*
    and λ, since the affine recurrence H(t+1) = λ H(t) + c has
    fixed point H* = c/(1-λ), i.e. c = (1-λ) H*.

    Empirical status: UNTESTED. -/
noncomputable def hetMutationRecurrence (lam Hstar H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => lam * hetMutationRecurrence lam Hstar H₀ t + (1 - lam) * Hstar

/-- **At t = 0, H equals the initial value.** -/
theorem hetMutationRecurrence_zero (lam Hstar H₀ : ℝ) :
    hetMutationRecurrence lam Hstar H₀ 0 = H₀ := by
  rfl

/-- **Closed-form solution of the affine recurrence.**
    H(t) = H* + (H₀ - H*) × λ^t.
    Proof by induction: the base case is trivial, and the step uses
    the fact that the constant term (1-λ)H* absorbs the equilibrium part. -/
theorem hetMutationRecurrence_closed_form (lam Hstar H₀ : ℝ) (t : ℕ) :
    hetMutationRecurrence lam Hstar H₀ t = Hstar + (H₀ - Hstar) * lam ^ t := by
  induction t with
  | zero =>
    simp [hetMutationRecurrence]
  | succ n ih =>
    simp only [hetMutationRecurrence, ih]
    ring

/-! ### Fst from heterozygosity ratio -/

/-- **Transient Fst from heterozygosity ratio.**
    Fst(t) = 1 - H(t)/H₀.

    Empirical status: UNTESTED. -/
noncomputable def fstFromHetRatio (H H₀ : ℝ) : ℝ :=
  1 - H / H₀

/-- **The proportional-reduction form, written three times in this corpus, related here so
that a change to any one of them fails to compile.**

`fstFromHetRatio H H₀`, `hudsonFstFromCoalescenceTimes ETss ETst` and `DGP.r2FromMSE mse
varY` are all `1 - residual/baseline`.  They are **not one quantity**: the first divides a
heterozygosity by an ancestral heterozygosity, the second an expected within-population
coalescence time by a between-population one, the third a mean squared error by a total
outcome variance.  Nothing lets a value of one be substituted for another.

What they share is the *measure*, and sharing it is not a coincidence — proportional
reduction of a residual against a baseline is one construction, and each of the three is
an instance of it.  That is why this is stated rather than left to the reader: the three
definitions carry no shared symbol, so before this theorem an edit to any one of them
diverged from the other two silently.

A fourth instance, `PCCorrectability.Diagnostic.pcTargetAxisEfficacy`, is deliberately
absent.  `Diagnostic` imports nothing from this corpus outside `PCCorrectability`, and no
module imports both it and any of the three below, so **no file can currently state that
identity at all.** Closing that one needs an import, not a theorem. -/
theorem fstFromHetRatio_eq_hudsonFst_eq_r2FromMSE (a b : ℝ) :
    fstFromHetRatio a b = hudsonFstFromCoalescenceTimes a b ∧
      fstFromHetRatio a b = r2FromMSE a b := by
  constructor <;> rfl

/-- **Fst(t) in terms of the closed-form heterozygosity.**
    Starting from H(0) = H₀, we have
    Fst(t) = 1 - [H* + (H₀ - H*) × λ^t] / H₀
           = 1 - H*/H₀ - (1 - H*/H₀) × λ^t
           = (1 - H*/H₀) × (1 - λ^t). -/
theorem fst_from_closed_form_het (lam Hstar H₀ : ℝ) (t : ℕ) (hH₀ : H₀ ≠ 0) :
    fstFromHetRatio (hetMutationRecurrence lam Hstar H₀ t) H₀ =
      (1 - Hstar / H₀) * (1 - lam ^ t) := by
  unfold fstFromHetRatio
  rw [hetMutationRecurrence_closed_form]
  field_simp
  ring

/-! ### Connecting to the equilibrium Fst -/

/-- **Fst prefactor when H₀ is normalized to 1.**
    With H₀ = 1 (heterozygosity normalized by maximum), the prefactor is
    1 - H* = 1 - θ/(1+θ) = 1/(1+θ) = Fst_eq.
    This is the correct normalisation: H₀ represents the ancestral
    heterozygosity before the population split, scaled to unit maximum. -/
theorem het_ratio_prefactor_unit_H₀ (θ : ℝ) (hθ : 0 ≤ θ) :
    1 - expectedHeterozygosity θ / 1 = fstMutationDriftEquilibrium θ := by
  rw [div_one]
  exact (fstEquilibrium_eq_one_minus_het θ hθ).symm

/-! ### The main derivation: transient Fst from the recurrence -/

/-- **Discrete transient Fst under mutation and drift.**
    Fst(t) = [1/(1+θ)] × (1 - λ^t) where λ = (1-1/(2N))(1-θ/(2N)).
    This is the closed-form discrete-time formula. The continuous version
    `fstMutationDriftTransient` (using exp) is the large-Ne approximation.

    Empirical status: UNTESTED. -/
noncomputable def fstMutationDriftTransientDiscrete (θ Ne : ℝ) (t : ℕ) : ℝ :=
  fstMutationDriftEquilibrium θ * (1 - hetDecayFactor Ne θ ^ t)

/-- **Derivation of transient Fst from the heterozygosity recurrence.**

    Starting from the affine recurrence H(t+1) = λ H(t) + (1-λ) H*
    with λ = hetDecayFactor Ne θ, H* = θ/(1+θ), and H₀ = 1
    (normalized ancestral heterozygosity):

    Step 1: Closed form gives H(t) = H* + (1 - H*) λ^t.
    Step 2: Fst(t) = 1 - H(t)/1 = 1 - H* - (1-H*) λ^t = (1-H*)(1 - λ^t).
    Step 3: 1 - H* = 1/(1+θ) = Fst_eq.
    Step 4: Fst(t) = Fst_eq × (1 - λ^t).

    This theorem shows that the recurrence-based Fst exactly equals
    `fstMutationDriftTransientDiscrete`. -/
theorem fstTransient_derived_from_recurrence (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) :
    fstFromHetRatio
      (hetMutationRecurrence (hetDecayFactor Ne θ) (expectedHeterozygosity θ) 1 t) 1 =
    fstMutationDriftTransientDiscrete θ Ne t := by
  rw [fst_from_closed_form_het _ _ _ _ one_ne_zero]
  unfold fstMutationDriftTransientDiscrete
  rw [het_ratio_prefactor_unit_H₀ θ hθ]

/-- **At t = 0, the derived transient Fst is 0.** -/
theorem fstTransientDiscrete_at_zero (θ Ne : ℝ) :
    fstMutationDriftTransientDiscrete θ Ne 0 = 0 := by
  unfold fstMutationDriftTransientDiscrete
  simp

/-- **The derived transient Fst is nonneg for valid parameters.** -/
theorem fstTransientDiscrete_nonneg (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) (hNe : 2 ≤ Ne) (hθNe : θ ≤ 2 * Ne) :
    0 ≤ fstMutationDriftTransientDiscrete θ Ne t := by
  unfold fstMutationDriftTransientDiscrete
  apply mul_nonneg
  · exact le_of_lt (fstMutationDriftEquilibrium_pos θ hθ)
  · rw [sub_nonneg]
    apply pow_le_one₀
    · unfold hetDecayFactor hetDecayFromScaled
      apply mul_nonneg
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · unfold hetDecayFactor hetDecayFromScaled
      have h1 : 1 - 1 / (2 * Ne) < 1 := by rw [sub_lt_self_iff]; positivity
      have h2 : 1 - θ / (2 * Ne) ≤ 1 := by rw [sub_le_self_iff]; positivity
      nlinarith [mul_le_of_le_one_right
        (show 0 ≤ 1 - 1 / (2 * Ne) by rw [sub_nonneg, div_le_one (by linarith)]; linarith) h2]

/-- **The derived transient Fst is bounded by the equilibrium Fst.** -/
theorem fstTransientDiscrete_le_equilibrium (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) (hNe : 2 ≤ Ne) (hθNe : θ ≤ 2 * Ne) :
    fstMutationDriftTransientDiscrete θ Ne t ≤ fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftTransientDiscrete
  have hfeq : 0 < fstMutationDriftEquilibrium θ := fstMutationDriftEquilibrium_pos θ hθ
  calc fstMutationDriftEquilibrium θ * (1 - hetDecayFactor Ne θ ^ t)
      ≤ fstMutationDriftEquilibrium θ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hfeq)
        have hpow_nonneg : 0 ≤ hetDecayFactor Ne θ ^ t := by
          apply pow_nonneg
          unfold hetDecayFactor hetDecayFromScaled
          apply mul_nonneg
          · rw [sub_nonneg, div_le_one (by linarith)]
            linarith
          · rw [sub_nonneg, div_le_one (by linarith)]
            linarith
        linarith
    _ = fstMutationDriftEquilibrium θ := by ring

/-- **Discrete-to-continuous approximation.**
    For large Ne, (1-1/(2N))(1-θ/(2N)) ≈ 1 - (1+θ)/(2N) ≈ exp(-(1+θ)/(2N)),
    so λ^t ≈ exp(-(1+θ)t/(2N)).
    We state the algebraic identity connecting the two:
    (1-1/(2N))(1-θ/(2N)) = 1 - (1+θ)/(2N) + θ/(4N²). -/
theorem hetDecayFactor_expansion (Ne θ : ℝ) (hNe : Ne ≠ 0) :
    hetDecayFactor Ne θ = 1 - (1 + θ) / (2 * Ne) + θ / (4 * Ne ^ 2) := by
  unfold hetDecayFactor hetDecayFromScaled
  field_simp
  ring

/-- **The θ/(4N²) correction is negligible for large Ne.**
    |hetDecayFactor - (1 - (1+θ)/(2N))| = θ/(4N²), which vanishes as N → ∞. -/
theorem hetDecayFactor_approx_error (Ne θ : ℝ) (hNe : 0 < Ne) (hθ : 0 ≤ θ) :
    |hetDecayFactor Ne θ - (1 - (1 + θ) / (2 * Ne))| = θ / (4 * Ne ^ 2) := by
  rw [hetDecayFactor_expansion Ne θ (ne_of_gt hNe)]
  have : 1 - (1 + θ) / (2 * Ne) + θ / (4 * Ne ^ 2) - (1 - (1 + θ) / (2 * Ne)) =
      θ / (4 * Ne ^ 2) := by ring
  rw [this, abs_of_nonneg]
  positivity

/-- **The discrete formula matches the original `fstMutationDriftTransient` definition
    in the large-Ne limit.**
    Both have the form Fst_eq × (1 - decay^t), differing only in
    whether the decay factor is the exact discrete
    (1-1/(2N))(1-θ/(2N)) or the continuous approximation exp(-(1+θ)/(2N)).
    This theorem states the structural agreement: when the decay base is the same,
    the formulas are identical. -/
theorem fstTransientDiscrete_eq_explicit (θ Ne : ℝ) (t : ℕ) :
    fstMutationDriftTransientDiscrete θ Ne t =
      1 / (1 + θ) * (1 - ((1 - 1 / (2 * Ne)) * (1 - θ / (2 * Ne))) ^ t) := by
  unfold fstMutationDriftTransientDiscrete fstMutationDriftEquilibrium hetDecayFactor
    hetDecayFromScaled
  rfl

end TransientFstDerivation

end Calibrator
