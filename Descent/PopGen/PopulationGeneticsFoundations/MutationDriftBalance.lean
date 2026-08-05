/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.WrightFStatistics

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.MutationDriftBalance`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



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
  unfold scaledMutationRate Descent.Core.scaledMutationRate Descent.Core.ploidy
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
`ibdRecurrenceStep` in `Descent.Portability.PortabilityDrift`; this one is their
scaled-time limit and is stated here because the definitions it pins are
parameterised by `θ` and `M` rather than by `Nₑ` and a rate.

    Empirical status: UNTESTED. -/
noncomputable def scaledIdentityStep (scaledRate F : ℝ) : ℝ :=
  1 - scaledRate * F

/-- **The identity-by-descent step's coefficient, pinned.** `scaledIdentityStep_fixedPoint` is a
fixed-point statement, and the equilibrium of a rescaled body is a fixed point of the rescaled
recurrence for the same reason -- the coefficient appears on both sides and cancels. A unit
scaled rate acting on an identity of one half returns one half. -/
theorem scaledIdentityStep_unit_rate :
    scaledIdentityStep 1 (1 / 2) = 1 / 2 := by
  unfold scaledIdentityStep
  norm_num

/-- **`1/(1 + scaledRate)` is the fixed point of the scaled identity balance.**
Setting `F = 1 - scaledRate * F` gives `F (1 + scaledRate) = 1`. Every
`1/(1 + θ)` and `1/(1 + M)` below is this lemma at a particular scaled rate. -/
theorem scaledIdentityStep_fixedPoint (scaledRate : ℝ) (h : 0 ≤ scaledRate) :
    scaledIdentityStep scaledRate (1 / (1 + scaledRate)) = 1 / (1 + scaledRate) := by
  have hd : (0 : ℝ) < 1 + scaledRate := by linarith
  have hd' : (1 : ℝ) + scaledRate ≠ 0 := ne_of_gt hd
  unfold scaledIdentityStep
  rw [mul_one_div, sub_eq_iff_eq_add, ← add_div, div_self hd']

/-- **The mutation-drift equilibrium is the rest point of the scaled identity
balance** driven by mutation alone. -/
theorem fstMutationDriftEquilibrium_isFixedPoint (θ : ℝ) (hθ : 0 ≤ θ) :
    scaledIdentityStep θ (fstMutationDriftEquilibrium θ) =
      fstMutationDriftEquilibrium θ :=
  scaledIdentityStep_fixedPoint θ hθ

/-- Equilibrium Fst is positive for nonneg θ. -/
theorem fstMutationDriftEquilibrium_pos (θ : ℝ) (hθ : 0 ≤ θ) :
    0 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  positivity

/-- Equilibrium Fst is at most 1. -/
theorem fstMutationDriftEquilibrium_le_one (θ : ℝ) (hθ : 0 ≤ θ) :
    fstMutationDriftEquilibrium θ ≤ 1 := by
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_le_one (by linarith)]
  linarith

/-- Equilibrium Fst is strictly less than 1 when θ > 0. This is the key
    qualitative difference from the pure drift model: mutation prevents
    complete fixation. -/
theorem fstMutationDriftEquilibrium_lt_one (θ : ℝ) (hθ : 0 < θ) :
    fstMutationDriftEquilibrium θ < 1 := by
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_lt_one (by linarith)]
  linarith

/-- Equilibrium Fst decreases with θ: more mutation → less differentiation. -/
theorem fstMutationDriftEquilibrium_strictAnti (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) :
    fstMutationDriftEquilibrium b < fstMutationDriftEquilibrium a := by
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  have hden : 0 < 1 + a := by linarith
  have hden_lt : 1 + a < 1 + b := by linarith
  simpa using div_lt_div_of_pos_left one_pos hden hden_lt

/-- **Equilibrium Fst decreases when the compound parameter `Ne * μ` increases.**

The scaled mutation rate sees `Ne` and `μ` only through their product, so raising either one
is the same move.  Both single-parameter statements below are this fact; stated separately,
each carried its own copy of the unfolding. -/
theorem fstEquilibrium_decreases_with_product (Ne₁ μ₁ Ne₂ μ₂ : ℝ)
    (h_nonneg : 0 ≤ Ne₁ * μ₁) (h_more : Ne₁ * μ₁ < Ne₂ * μ₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne₂ μ₂) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne₁ μ₁) := by
  apply fstMutationDriftEquilibrium_strictAnti <;>
    unfold scaledMutationRate Descent.Core.scaledMutationRate Descent.Core.ploidy <;>
    nlinarith

/-- Equilibrium Fst decreases when Ne increases (with μ fixed). -/
theorem fstEquilibrium_decreases_with_Ne (μ Ne₁ Ne₂ : ℝ)
    (hμ : 0 < μ) (hNe₁ : 0 < Ne₁)
    (h_more : Ne₁ < Ne₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne₂ μ) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne₁ μ) :=
  fstEquilibrium_decreases_with_product Ne₁ μ Ne₂ μ (by nlinarith) (by nlinarith)

/-- Equilibrium Fst decreases when μ increases (with Ne fixed). -/
theorem fstEquilibrium_decreases_with_mu (Ne μ₁ μ₂ : ℝ)
    (hNe : 0 < Ne) (hμ₁ : 0 < μ₁)
    (h_more : μ₁ < μ₂) :
    fstMutationDriftEquilibrium (scaledMutationRate Ne μ₂) <
      fstMutationDriftEquilibrium (scaledMutationRate Ne μ₁) :=
  fstEquilibrium_decreases_with_product Ne μ₁ Ne μ₂ (by nlinarith) (by nlinarith)

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
  unfold expectedHeterozygosity fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  have hden : (1 + θ) ≠ 0 := by linarith
  field_simp [hden]
  ring

/-- **The within-population heterozygosity share and Nei's Fst sum to 1.**
    Since `neiFst H_T H_S = (H_T − H_S) / H_T = 1 − H_S / H_T`, we have
    H_S / H_T + neiFst H_T H_S = 1.  No equilibrium assumption is needed;
    the identity holds for *any* H_T ≠ 0.  This is the general form of the
    variance partition that `het_plus_fst_eq_one` instantiates at equilibrium. -/
theorem nei_fst_complement (H_S H_T : ℝ) (hHT : H_T ≠ 0) :
    H_S / H_T + (neiFst H_T H_S).value = 1 := by
  simp only [neiFst_value]
  field_simp [hHT]
  ring_nf

/-- **At mutation-drift equilibrium, Nei's Fst recovers fstMutationDriftEquilibrium.**
    When H_S = θ/(1+θ) (`expectedHeterozygosity θ`) and H_T = 1 (maximal
    heterozygosity under the infinite-alleles model), Nei's formula gives
    Fst = 1/(1+θ) = `fstMutationDriftEquilibrium θ`. -/
theorem nei_fst_equilibrium_consistent (θ : ℝ) (hθ : 0 ≤ θ) :
    (neiFst 1 (expectedHeterozygosity θ)).value = fstMutationDriftEquilibrium θ := by
  simp only [neiFst_value]
  unfold expectedHeterozygosity fstMutationDriftEquilibrium Descent.Core.fstFromFlow
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
    (hμ : 0 < μ)
    (hθ_large : 2 < scaledMutationRate Ne μ) :
    1 / μ < 2 * Ne := by
  unfold scaledMutationRate Descent.Core.scaledMutationRate Descent.Core.ploidy at hθ_large
  rw [div_lt_iff₀ hμ]
  nlinarith

/-- When θ < 1, equilibrium Fst > 1/2. -/
theorem fstEquilibrium_gt_half_of_small_theta (θ : ℝ)
    (hθ_pos : 0 < θ) (hθ_small : θ < 1) :
    1 / 2 < fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rw [lt_div_iff₀ (by linarith : 0 < 1 + θ)]
  linarith

/-- **Fst under mutation-drift with time dependence (approach to equilibrium).**
    Fst(t) = Fst_eq × (1 - e^{-(1 + θ) t / (2Ne)})
    where Fst_eq = 1/(1+θ). Starting from Fst=0, differentiation rises
    toward the equilibrium set by mutation rate.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk16.py`). Infinite-alleles
    Wright-Fisher started ALL-DISTINCT -- every chromosome carrying its own
    allele -- so identity by descent starts at zero, which is the initial
    condition this formula assumes. 200 replicate populations, identity measured
    without replacement within the deme, at five times per parameter set
    spanning `t/Ne` from 0.25 to 4:

      Ne     theta    worst cell of five     rel err
      50     1.00     2.24 sems              6.4%
      100    0.80     under 2 sems           under 6%
      200    0.80     under 2 sems           under 6%

    Positive control: the plateau reproduces the independently validated
    `1/(1 + theta)`.

    Not separated from `fstMutationDriftTransientDiscrete`, and the docstring
    there says why: the two agree to O(1/Ne), the design reaches down to
    `Ne = 50` where the gap is about one percent, and the replicate noise here
    is six percent. So this validates the SHAPE of the approach -- the rate
    constant `(1 + theta)/(2 Ne)` and the equilibrium it approaches -- and does
    not discriminate continuous from discrete time. That limit is stated rather
    than papered over.

    Power: the prediction rises from a quarter of the plateau to within 2% of
    it across the time points, so a wrong rate constant would separate. -/
noncomputable def fstMutationDriftTransient (θ t Ne : ℝ) : ℝ :=
  fstMutationDriftEquilibrium θ * (1 - Real.exp (-(1 + θ) * t / (2 * Ne)))

/-- A zero effective size sends the scaled time to Mathlib's junk `0`, hence the exponential to
one and the transient to zero: the body reports no divergence at all where the true reading is
immediate saturation at the equilibrium value. -/
theorem fstMutationDriftTransient_at_zero_size_is_junk (θ t : ℝ) :
    fstMutationDriftTransient θ t 0 = 0 := by
  unfold fstMutationDriftTransient
  simp


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
    (hθ : 0 ≤ θ) :
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
    (hθ : 0 < θ) (hNe : 0 < Ne)
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
  simp [mul_zero, zero_div, Real.exp_zero, sub_self]

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

    Empirical status: MIXED -- body **VALIDATED** as a count of mutations arising; the
    segregating-sites reading **FALSIFIED** (`validation/empirical/coalescent_diff/`). -/
noncomputable def expectedNewMutations (θ t : ℝ) : ℝ :=
  θ / 2 * t

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem expectedNewMutations_at_reference_point :
    expectedNewMutations 1 1 = 1 / 2 := by
  norm_num [expectedNewMutations]


/-- Expected new mutations is nonneg for nonneg θ and t. -/
theorem expectedNewMutations_nonneg (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ expectedNewMutations θ t := by
  unfold expectedNewMutations
  positivity

/-- More mutations accumulate with larger θ (fixed t). -/
theorem expectedNewMutations_increases_with_theta (t θ₁ θ₂ : ℝ)
    (ht : 0 < t) (h_more : θ₁ < θ₂) :
    expectedNewMutations θ₁ t < expectedNewMutations θ₂ t := by
  unfold expectedNewMutations
  nlinarith

/-- More mutations accumulate over longer time (fixed θ). -/
theorem expectedNewMutations_increases_with_time (θ t₁ t₂ : ℝ)
    (hθ : 0 < θ) (h_more : t₁ < t₂) :
    expectedNewMutations θ t₁ < expectedNewMutations θ t₂ := by
  unfold expectedNewMutations
  nlinarith

/-! **Deleted: `sharedLDFractionFromMutation θ t = exp(-expectedNewMutations θ t)`,
together with `sharedLDFraction_pos`, `sharedLDFraction_le_one` and
`sharedLDFraction_decreases_with_time`.**

Measured in `validation/empirical/coalescent_diff/`. -/

end MutationDriftBalance

end Descent.PopGen
