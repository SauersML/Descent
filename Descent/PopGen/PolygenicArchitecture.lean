/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.HaplotypeTheory

assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

namespace Descent.PopGen

open MeasureTheory

/-!
# Polygenic Architecture and PGS Portability

This file formalizes how the underlying genetic architecture of
complex traits — the distribution of effect sizes, the number of
causal variants, and their genomic distribution — affects PGS
portability across populations.

Key results:
1. Effect size distribution models (exponential, spike-and-slab)
2. Polygenicity and its relationship to portability
3. Genetic architecture parameters from GWAS
4. Architecture-dependent portability predictions
5. Heritability partitioning by functional category

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat effect-size distribution models or the minimax and
certificate-modulus material below. Sources for individual results, where they exist,
are cited at those results.
-/


/-!
## Effect Size Distribution

The distribution of per-variant effect sizes determines
how PGS portability scales with sample size and ancestry.
-/

section EffectSizeDistribution

/-- **Exponential distribution of squared effects.**
    Under the infinitesimal model: β² ~ Exponential(1/σ²)
    where σ² = h²/M (heritability divided by number of variants).

    Empirical status: NOT AN EMPIRICAL CLAIM, and the two MATCHes on record for it are
    worthless. `battery_bulk18.py` and `battery_ldsc.py` both "validated" this body by
    drawing effects with variance `h2/M` and measuring their mean square, which tests the
    random number generator: agreement is guaranteed by construction and the residual is
    sampling noise. That is the GENERATIVE SELF-TEST shape `simcov/verdict.py` now refuses,
    and neither battery declared it, so the harness scored both MATCH.

    The body is the same map as `SelectionArchitecture.equalPerLocusHeritability` --
    heritability spread equally over M loci -- so it DEFINES the equal-allocation
    architecture rather than predicting one. The testable claim in its neighbourhood is that
    real squared effects are exponentially distributed with this mean, which is a claim
    about the effect-size DISTRIBUTION and is the one `spikeAndSlabVariance` below says the
    corpus does not make. -/
noncomputable def expectedSquaredEffect (h2 M : ℝ) : ℝ :=
  Descent.Core.ratio h2 M

/-- **expectedSquaredEffect at zero M, named.** With no causal variants the heritability has
nowhere to sit and the per-variant squared effect diverges. Lean returns `0`, the infinitely
polygenic limit. Consumers must require `M ≠ 0`. -/
theorem expectedSquaredEffect_zero_m_is_junk (h2 : ℝ) :
    expectedSquaredEffect h2 0 = 0 := by
  unfold expectedSquaredEffect Descent.Core.ratio
  simp

/-- Per-variant heritability decreases with polygenicity. -/
theorem per_variant_h2_decreases_with_M (h2 M₁ M₂ : ℝ)
    (h_h2 : 0 < h2) (h_M₁ : 0 < M₁) (h_M₂ : 0 < M₂)
    (h_M : M₁ < M₂) :
    expectedSquaredEffect h2 M₂ < expectedSquaredEffect h2 M₁ := by
  unfold expectedSquaredEffect Descent.Core.ratio
  exact div_lt_div_iff_of_pos_left h_h2 h_M₂ h_M₁ |>.mpr h_M

/-- **The `M` variants carry the whole heritability between them.**

Monotonicity in `M` is satisfied by every body that falls as variants are added -- `h²/M²`
and `h²/(1 + M)` both do -- so it leaves the scale free, and the scale is what a per-variant
effect is for.  Multiplying the per-variant share back by the count returns the heritability
exactly, with no coefficient: that is what makes this an ALLOCATION of `h²` rather than a
quantity merely decreasing in polygenicity, and it is the statement a stray factor of two
in the body would break. -/
theorem expectedSquaredEffect_mul_count (h2 M : ℝ) (hM : M ≠ 0) :
    Descent.Core.product (expectedSquaredEffect h2 M) M = h2 := by
  unfold expectedSquaredEffect Descent.Core.product Descent.Core.ratio
  field_simp

/-- **Spike-and-slab model.**
    π proportion of variants have effect ~ N(0, σ²_large),
    (1-π) proportion have effect = 0 (or ~ N(0, σ²_small)).
    π is the polygenicity parameter.

    Empirical status: **NOT AN EMPIRICAL CLAIM.** The body is the law of total
    variance for a two-component zero-mean mixture, which is arithmetic: given
    components of variance `σ²_large` and `σ²_small` mixed at `π`, the marginal
    second moment IS `π σ²_large + (1 - π) σ²_small`, and no population can
    disagree. The marker previously read NOT EMPIRICALLY TESTABLE BY SIMULATION,
    which says there is observable content no design can reach; the sharper
    reading is that there is none, and the paragraph below is why the two are
    easy to confuse here. The only simulation that would bear on it
    draws effects from the very mixture whose variance this states, and then
    measures their variance -- so the agreement is guaranteed by construction and
    the residual is the random number generator's sampling noise.
    `battery_ldsc.py` ran exactly that and reported FALSIFIED at 10.6 sems at
    `π = 0.01`, which was noise judged against a Gaussian error bar: a
    spike-and-slab at `π = 0.01` has enormous kurtosis, so `Var · sqrt(2/M)`
    understates its own scatter badly. `battery_dis1.py` reruns it declaring the
    oracle non-independent and the harness returns GENERATIVE SELF-TEST.

    What could be tested is a claim this definition does not make: that the
    two-component mixture describes real effect-size distributions. That is a
    claim about data, not about arithmetic.

    Denotes: a variance. Other definitions share this formula under names from a
    different concept family; the formula does not fix which is meant. -/
noncomputable def spikeAndSlabVariance (pi sigma_sq_large sigma_sq_small : ℝ) : ℝ :=
  Descent.Core.convexCombination pi sigma_sq_large sigma_sq_small

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem spikeAndSlabVariance_at_reference_point :
    spikeAndSlabVariance (1 / 2) (1 / 2) (1 / 2) = 1 / 2 := by
  unfold spikeAndSlabVariance Descent.Core.convexCombination
  norm_num

/-! ### The mixture map, shared with `HaplotypeTheory`

The spike-and-slab variance, the average phase interaction and the
ancestry-specific effect are three different quantities — a variance, an
interaction contribution and an effect size — that are all the same convex
combination of two values at a mixing weight. `Core.convexCombination` names
that map; these two theorems record the coincidence in one of the two files
each pair lives in, so that a change to the mixture convention in either file
fails to compile rather than quietly disagreeing. -/

theorem spikeAndSlabVariance_eq_averagePhaseInteraction (pi a b : ℝ) :
    spikeAndSlabVariance pi a b = averagePhaseInteraction pi a b := by
  unfold spikeAndSlabVariance averagePhaseInteraction Descent.Core.convexCombination; ring

theorem spikeAndSlabVariance_eq_ancestrySpecificEffect (pi a b : ℝ) :
    spikeAndSlabVariance pi a b = ancestrySpecificEffect a b pi := by
  unfold spikeAndSlabVariance ancestrySpecificEffect Descent.Core.convexCombination; ring

/-- **The spike-and-slab formula is a variance only on `0 ≤ pi ≤ 1`.**

    Outside that interval `pi * σ²_large + (1 - pi) * σ²_small` is a signed
    extrapolation of a mixture, not a mixture, and it goes negative: at `pi = 2`
    with a zero slab variance it returns `-σ²_small`. Nothing in the definition
    prevents this, and `sas_variance_monotone_in_pi` below imposes no bounds at
    all, so the bound is recorded here as a theorem with the interval hypothesis
    visible.

    This is the mixture-interval statement: on `[0, 1]` the value is a convex
    combination and therefore lies between the two component variances, hence is
    nonnegative whenever they are. -/
theorem spikeAndSlabVariance_mem_interval
    (pi sigma_sq_large sigma_sq_small : ℝ)
    (h_pi_nonneg : 0 ≤ pi) (h_pi_le : pi ≤ 1)
    (h_order : sigma_sq_small ≤ sigma_sq_large) :
    sigma_sq_small ≤ spikeAndSlabVariance pi sigma_sq_large sigma_sq_small ∧
      spikeAndSlabVariance pi sigma_sq_large sigma_sq_small ≤ sigma_sq_large := by
  unfold spikeAndSlabVariance Descent.Core.convexCombination
  constructor <;> nlinarith

/-- On the mixture interval, and only there, the spike-and-slab variance is
nonnegative when its components are. -/
theorem spikeAndSlabVariance_nonneg
    (pi sigma_sq_large sigma_sq_small : ℝ)
    (h_pi_nonneg : 0 ≤ pi) (h_pi_le : pi ≤ 1)
    (h_large : 0 ≤ sigma_sq_large) (h_small : 0 ≤ sigma_sq_small) :
    0 ≤ spikeAndSlabVariance pi sigma_sq_large sigma_sq_small := by
  unfold spikeAndSlabVariance Descent.Core.convexCombination
  have h_one_minus : 0 ≤ 1 - pi := by linarith
  nlinarith

/-- **And it is negative off the interval**, which is what the missing bound
costs. At `pi = 2` with a zero slab variance the formula returns `-σ²_small`, a
negative variance. The witness is exhibited so that the failure is recorded
rather than assumed away. -/
theorem spikeAndSlabVariance_neg_off_interval
    (sigma_sq_small : ℝ) (h_small : 0 < sigma_sq_small) :
    spikeAndSlabVariance 2 0 sigma_sq_small < 0 := by
  unfold spikeAndSlabVariance Descent.Core.convexCombination
  linarith

/-- Spike-and-slab variance increases with polygenicity
    when the slab dominates. Note that this holds for every real `pi`, including
    values outside `[0, 1]` at which the quantity is not a variance; see
    `spikeAndSlabVariance_mem_interval` for the interval on which the conclusion
    is about a mixture. -/
theorem sas_variance_monotone_in_pi
    (pi₁ pi₂ sigma_sq_large sigma_sq_small : ℝ)
    (h_large : sigma_sq_small < sigma_sq_large)
    (h_pi : pi₁ < pi₂) :
    spikeAndSlabVariance pi₁ sigma_sq_large sigma_sq_small <
      spikeAndSlabVariance pi₂ sigma_sq_large sigma_sq_small := by
  unfold spikeAndSlabVariance Descent.Core.convexCombination; nlinarith

/-- **BayesR mixture components.**
    BayesR uses a 4-component mixture:
    β ~ π₀δ₀ + π₁N(0, 0.01σ²) + π₂N(0, 0.1σ²) + π₃N(0, σ²)
    where Σπ_i = 1 and σ² = h²/M. -/
theorem mixture_weights_sum_to_one
    (pi0 pi1 pi2 pi3 : ℝ)
    (h_sum : pi0 + pi1 + pi2 + pi3 = 1)
    (h_nn₀ : 0 ≤ pi0) (h_nn₁ : 0 ≤ pi1) (h_nn₂ : 0 ≤ pi2) (h_nn₃ : 0 ≤ pi3) :
    0 ≤ pi0 ∧ pi0 ≤ 1 := by
  constructor
  · exact h_nn₀
  · linarith

end EffectSizeDistribution


/-!
## Polygenicity and Portability

More polygenic traits tend to have better portability because
each variant contributes less, making the PGS less sensitive
to per-variant LD changes.
-/

section PolygenicityAndPortability

/-- **Polygenicity definition.**
    M_eff = effective number of causal variants
    = (Σ β²_j)² / Σ β⁴_j (inverse kurtosis measure).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk6.py`,
    `test_effective_polygenicity`). Its operational meaning is the inverse
    probability that two draws from the effect-mass distribution land on the
    same locus, and that is a sampling experiment independent of the algebra --
    the same oracle that settled `HaplotypeTheory.effectiveHaplotypeNumber`:

      effect vector       this def   inverse match rate      sems
      400 equal          400.00000   407.83034±4.11298       1.90
      gaussian, m=400    147.46342   146.35396±0.88224       1.26
      one dominant         1.12856   1.12850±0.00020         0.32
      mixture             11.25069   11.26237±0.01804        0.65

    Power: the prediction spans 1.129 to 400.0, a factor of 350, and the
    one-dominant cell is what separates a participation ratio from a locus
    count. -/
noncomputable def effectivePolygenicity (sum_beta_sq sum_beta_fourth : ℝ) : ℝ :=
  sum_beta_sq^2 / sum_beta_fourth

/-- **The participation ratio's junk branch, named.** With no effects the fourth-moment sum
vanishes and Lean returns `0`, reporting an effective polygenicity of zero where the ratio is
undefined — and where every theorem below claims it is at least one. Consumers must require
`sum_beta_fourth ≠ 0`, which is exactly "some variant has a nonzero effect". -/
theorem effectivePolygenicity_no_effects_is_junk (sum_beta_sq : ℝ) :
    effectivePolygenicity sum_beta_sq 0 = 0 := by
  unfold effectivePolygenicity; simp

/-- Effective polygenicity ≥ 1.

    The hypothesis `h_cs` is not free: on a genuine effect vector it is a
    theorem, not an assumption. See `effectivePolygenicityOfEffects_mem_Icc`
    below, which removes it and adds the matching upper bound. This form is
    kept for callers holding only the two moment sums. -/
theorem effective_polygenicity_ge_one
    (sum_sq sum_fourth : ℝ)
    (h_fourth : 0 < sum_fourth)
    (h_cs : sum_fourth ≤ sum_sq^2) :
    1 ≤ effectivePolygenicity sum_sq sum_fourth := by
  unfold effectivePolygenicity
  rw [le_div_iff₀ h_fourth]
  linarith

/-- **Effective polygenicity of an explicit effect vector.**

    The same inverse-kurtosis measure, but fed the two moment sums of a named
    effect vector rather than two unrelated reals. Stating it this way is what
    lets the Cauchy–Schwarz hypothesis of `effective_polygenicity_ge_one` be
    discharged instead of assumed, and lets the matching upper bound be stated
    at all: `M_eff` cannot exceed the number of variants, which no formulation
    over two free reals can express.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a summary statistic of the
    effect vector, whose value is fixed by `beta` alone. There is no measurement
    that could agree or disagree with it, and two attempts to build one
    (`simcov/battery_bulk28.py` and `battery_bulk29.py`) returned algebra in
    both directions rather than evidence:

      * against EQUAL-MAGNITUDE effects at `k` loci the participation ratio is
        exactly `k`, so comparing it to the count of nonzero effects agreed to
        machine precision and the harness reported SELF-TEST;
      * against GAUSSIAN effects at `k` loci it is `k/3`, because
        `E[b⁴] = 3σ⁴`, so the same comparison missed by 281 sems -- a fact about
        the fourth moment of the normal distribution, not about this body.

    Both outcomes are determined before any simulation runs. What COULD carry
    empirical content is the modelling claim that the participation ratio is the
    right summary of an architecture -- that it predicts something about
    discovery, transfer or power. That is a claim about a downstream use, and it
    belongs at the definition that makes it. -/
noncomputable def effectivePolygenicityOfEffects {q : ℕ} (beta : Fin q → ℝ) : ℝ :=
  effectivePolygenicity (∑ j, beta j ^ 2) (∑ j, beta j ^ 4)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem effectivePolygenicityOfEffects_at_reference_point :
    effectivePolygenicityOfEffects (![1, 3] : Fin 2 → ℝ) = 50 / 41 := by
  norm_num [effectivePolygenicityOfEffects, effectivePolygenicity, Fin.sum_univ_two]


/-- `∑ β⁴ ≤ (∑ β²)²`: the lower half of the polygenicity range, as a theorem
about an effect vector rather than a hypothesis about two reals. It is the
statement that a sum of nonnegative numbers dominates the sum of their
squares. -/
theorem sum_fourth_le_sq_sum_sq {q : ℕ} (beta : Fin q → ℝ) :
    ∑ j, beta j ^ 4 ≤ (∑ j, beta j ^ 2) ^ 2 := by
  have h : ∑ j : Fin q, (beta j ^ 2) ^ 2 ≤ (∑ j : Fin q, beta j ^ 2) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ ↦ sq_nonneg (beta j))
  have hrw : ∑ j : Fin q, (beta j ^ 2) ^ 2 = ∑ j, beta j ^ 4 :=
    Finset.sum_congr rfl (fun j _ ↦ by ring)
  rw [hrw] at h
  exact h

/-- `(∑ β²)² ≤ q · ∑ β⁴`: the upper half, by Cauchy–Schwarz against the
constant vector. This is the direction the two-free-reals formulation could not
state, because the variant count does not appear in its signature. -/
theorem sq_sum_sq_le_card_mul_sum_fourth {q : ℕ} (beta : Fin q → ℝ) :
    (∑ j, beta j ^ 2) ^ 2 ≤ (q : ℝ) * ∑ j, beta j ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    (fun _ ↦ (1 : ℝ)) (fun j ↦ beta j ^ 2)
  have h3 : ∑ j : Fin q, (beta j ^ 2) ^ 2 = ∑ j, beta j ^ 4 :=
    Finset.sum_congr rfl (fun j _ ↦ by ring)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [h3] at h
  exact h

/-- **Effective polygenicity lies between one and the number of variants.**

    Two strengthenings of `effective_polygenicity_ge_one` at once. The
    Cauchy–Schwarz hypothesis is discharged rather than assumed, and the
    one-sided bound becomes two-sided: `1 ≤ M_eff ≤ q`, with the lower end
    approached by a single large effect and the upper end by `q` equal ones.
    Only the positivity of the fourth moment remains, and that is not a
    modelling assumption but the condition for the quotient to exist. -/
theorem effectivePolygenicityOfEffects_mem_Icc {q : ℕ} (beta : Fin q → ℝ)
    (h_pos : 0 < ∑ j, beta j ^ 4) :
    1 ≤ effectivePolygenicityOfEffects beta ∧
      effectivePolygenicityOfEffects beta ≤ (q : ℝ) := by
  unfold effectivePolygenicityOfEffects effectivePolygenicity
  constructor
  · rw [le_div_iff₀ h_pos, one_mul]
    exact sum_fourth_le_sq_sum_sq beta
  · rw [div_le_iff₀ h_pos]
    exact sq_sum_sq_le_card_mul_sum_fourth beta

/-- Explicit SNP-level portability model.

Each causal SNP contributes a source squared-effect mass
`sourceSquaredEffect j = β_source,j²`, and the target retains some portion of
that mass after LD mismatch, allele-frequency drift, effect-size drift, and
other transport losses. The retained mass is modeled directly at each SNP,
rather than through a single `√M` ansatz. -/
structure SNPArchitecturePortabilityModel (q : ℕ) where
  sourceSquaredEffect : Fin q → ℝ
  targetRetainedSquaredEffect : Fin q → ℝ
  sourceSquaredEffect_nonneg : ∀ j, 0 ≤ sourceSquaredEffect j
  targetRetained_nonneg : ∀ j, 0 ≤ targetRetainedSquaredEffect j
  targetRetained_le_source : ∀ j, targetRetainedSquaredEffect j ≤ sourceSquaredEffect j

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SNPArchitecturePortabilityModel.witness
    (q : ℕ) : SNPArchitecturePortabilityModel q where
  sourceSquaredEffect := fun _ ↦ 1
  targetRetainedSquaredEffect := fun _ ↦ 1 / 2
  sourceSquaredEffect_nonneg := fun _ ↦ by norm_num
  targetRetained_nonneg := fun _ ↦ by norm_num
  targetRetained_le_source := fun _ ↦ by norm_num

namespace SNPArchitecturePortabilityModel

/-- Total causal signal mass in the source architecture.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body sums a FIELD of the structure over
    its index set. Given the model the sum is fixed, so nothing measurable can disagree
    with it; what is empirical is what the per-SNP squared effects are, and that is an
    input. The corresponding claim about a real architecture -- that a sum of squared
    effects is the additive variance under linkage equilibrium -- is
    `TransferLearningPGS.additiveGeneticVariance`, which IS measured. -/
noncomputable def sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.sourceSquaredEffect j

/-- Total causal signal mass still retained in the target architecture.

    Empirical status: NOT AN EMPIRICAL CLAIM, for the same reason as
    `sourceEffectMass`: it sums a declared field of the model. -/
noncomputable def targetRetainedEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  ∑ j, model.targetRetainedSquaredEffect j

/-- Reference evaluation: a model retaining no squared effect has no retained mass. -/
theorem targetRetainedEffectMass_at_zero {q : ℕ} (model : SNPArchitecturePortabilityModel q)
    (hzero : ∀ j, model.targetRetainedSquaredEffect j = 0) :
    targetRetainedEffectMass model = 0 := by
  unfold targetRetainedEffectMass
  simp [hzero]


/-- Total signal mass lost across SNPs when transporting to the target.

    Empirical status: NOT AN EMPIRICAL CLAIM. A difference of two sums over the same
    declared fields: the accounting identity "lost = source minus retained" is what the
    body says, and an identity has no free coefficient for data to correct. -/
noncomputable def lostEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.sourceEffectMass - model.targetRetainedEffectMass

/-- **Nothing is lost when the target retains the whole source mass.**

An identity under its own hypothesis, not a reference evaluation. It states zero, so a
competitor scaled by any factor satisfies it too and it pins no coefficient. Renamed
rather than moved: the fact IS the accounting identity the definition exists to express,
and choosing a different `model` to make the value nonzero would have thrown it away to
satisfy a checker. -/
theorem lostEffectMass_of_full_retention_eq_zero {q : ℕ} (model : SNPArchitecturePortabilityModel q)
    (hfull : model.targetRetainedEffectMass = model.sourceEffectMass) :
    lostEffectMass model = 0 := by
  unfold lostEffectMass
  rw [hfull, sub_self]


/-- Relative portability loss: lost causal signal mass as a fraction of the
source causal signal mass. -/
noncomputable def relativePortabilityLoss {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.lostEffectMass / model.sourceEffectMass

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem relativePortabilityLoss_at_zero_denominator_is_junk {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (hzero : model.sourceEffectMass = 0) :
    relativePortabilityLoss model = 0 := by
  unfold relativePortabilityLoss
  rw [hzero, div_zero]


/-- Retained portability score: retained target causal signal mass as a
fraction of the source causal signal mass. -/
noncomputable def portabilityScore {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.targetRetainedEffectMass / model.sourceEffectMass

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem portabilityScore_at_zero_denominator_is_junk {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (hzero : model.sourceEffectMass = 0) :
    portabilityScore model = 0 := by
  unfold portabilityScore
  rw [hzero, div_zero]


theorem sourceEffectMass_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    0 ≤ model.sourceEffectMass := by
  unfold sourceEffectMass
  exact Fintype.sum_nonneg fun j ↦ model.sourceSquaredEffect_nonneg j

theorem targetRetainedEffectMass_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    0 ≤ model.targetRetainedEffectMass := by
  unfold targetRetainedEffectMass
  exact Fintype.sum_nonneg fun j ↦ model.targetRetained_nonneg j

theorem targetRetainedEffectMass_le_sourceEffectMass {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    model.targetRetainedEffectMass ≤ model.sourceEffectMass := by
  unfold targetRetainedEffectMass sourceEffectMass
  exact Finset.sum_le_sum fun j _ ↦ model.targetRetained_le_source j

/-- The relative portability loss is exactly the locuswise lost-effect mass
fraction. -/
theorem relativePortabilityLoss_eq_locuswise_loss_fraction {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    model.relativePortabilityLoss =
      (∑ j, (model.sourceSquaredEffect j - model.targetRetainedSquaredEffect j)) /
        model.sourceEffectMass := by
  unfold relativePortabilityLoss lostEffectMass sourceEffectMass targetRetainedEffectMass
  congr 1
  rw [← Finset.sum_sub_distrib]

@[simp] theorem portabilityScore_eq_one_sub_relativePortabilityLoss {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    model.portabilityScore = 1 - model.relativePortabilityLoss := by
  unfold portabilityScore relativePortabilityLoss lostEffectMass
  field_simp [ne_of_gt h_source]
  ring

theorem relativePortabilityLoss_nonneg {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    0 ≤ model.relativePortabilityLoss := by
  rw [relativePortabilityLoss_eq_locuswise_loss_fraction model]
  apply div_nonneg
  · exact Fintype.sum_nonneg fun j ↦ sub_nonneg.mpr (model.targetRetained_le_source j)
  · exact le_of_lt h_source

theorem portabilityScore_le_one {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    model.portabilityScore ≤ 1 := by
  rw [portabilityScore_eq_one_sub_relativePortabilityLoss model h_source]
  have h_loss_nn := relativePortabilityLoss_nonneg model h_source
  linarith

end SNPArchitecturePortabilityModel

/-- Equal-effect portability score under a catastrophic-mismatch architecture:
all `M` causal SNPs have equal source squared effect, and SNPs in the explicit
set `mismatched` retain zero target signal. The retained fraction is therefore
the surviving SNP fraction. -/
noncomputable def uniformCatastrophicPortabilityScore
    (M : ℕ) (mismatched : Finset (Fin M)) : ℝ :=
  1 - (mismatched.card : ℝ) / (M : ℝ)

/-- **uniformCatastrophicPortabilityScore at its junk point, named.** An empty variant panel has
no portability to score. The divisor is zero, the mismatch fraction is junk-zero, and the score
is `1`: PERFECT portability, awarded to a panel with no variants in it. Consumers must exclude
the argument that makes the guard vanish. -/
theorem uniformCatastrophicPortabilityScore_empty_panel_is_junk (mismatched : Finset (Fin 0)) :
    uniformCatastrophicPortabilityScore 0 mismatched = 1 := by
  unfold uniformCatastrophicPortabilityScore
  simp

/-- **More polygenic architectures are more robust to the same number of badly
mismatched causal SNPs.**

This theorem is now stated on an explicit causal-SNP architecture: both traits
have equal per-SNP source effect mass, and both lose the same number of causal
SNPs in the target. The trait with more causal SNPs loses a smaller fraction of
its total causal signal mass. -/
theorem more_polygenic_more_portable
    {M₁ M₂ : ℕ}
    (mismatched₁ : Finset (Fin M₁))
    (mismatched₂ : Finset (Fin M₂))
    (h_M : M₁ < M₂)
    (h_same_card : mismatched₁.card = mismatched₂.card)
    (h_loss : 0 < mismatched₁.card) :
    uniformCatastrophicPortabilityScore M₁ mismatched₁ <
      uniformCatastrophicPortabilityScore M₂ mismatched₂ := by
  unfold uniformCatastrophicPortabilityScore
  have h_k_pos : 0 < (mismatched₁.card : ℝ) := Nat.cast_pos.mpr h_loss
  have h_M₁_pos_nat : 0 < M₁ := lt_of_lt_of_le h_loss (by
    simpa [Fintype.card_fin] using mismatched₁.card_le_univ)
  have h_M₂_pos_nat : 0 < M₂ := lt_trans h_M₁_pos_nat h_M
  have h_M₁_pos : 0 < (M₁ : ℝ) := Nat.cast_pos.mpr h_M₁_pos_nat
  have h_M₂_pos : 0 < (M₂ : ℝ) := Nat.cast_pos.mpr h_M₂_pos_nat
  have h_div :
      (mismatched₁.card : ℝ) / (M₂ : ℝ) <
        (mismatched₁.card : ℝ) / (M₁ : ℝ) :=
    (div_lt_div_iff_of_pos_left h_k_pos h_M₂_pos h_M₁_pos).2 (by exact_mod_cast h_M)
  have h_same_card_cast : (mismatched₂.card : ℝ) = (mismatched₁.card : ℝ) := by
    exact_mod_cast h_same_card.symm
  rw [h_same_card_cast]
  linarith

/-- Height-like traits can be more portable than BMI-like traits when the same
number of causal SNPs are catastrophically mismatched, because a larger set of
causal SNPs dilutes the lost fraction. -/
theorem height_polygenic_good_portability
    {M_height M_bmi : ℕ}
    (mismatchedHeight : Finset (Fin M_height))
    (mismatchedBMI : Finset (Fin M_bmi))
    (h_M : M_bmi < M_height)
    (h_same_card : mismatchedBMI.card = mismatchedHeight.card)
    (h_loss : 0 < mismatchedBMI.card) :
    uniformCatastrophicPortabilityScore M_bmi mismatchedBMI <
      uniformCatastrophicPortabilityScore M_height mismatchedHeight :=
  more_polygenic_more_portable mismatchedBMI mismatchedHeight h_M h_same_card h_loss

/-- **Selection can outweigh a polygenicity advantage.**

Even if the selected trait has more causal SNPs, it can still have worse
portability when the fraction of causal SNPs that lose target signal is larger. -/
theorem selection_overrides_polygenicity
    {M_neutral M_selected : ℕ}
    (neutralMismatch : Finset (Fin M_neutral))
    (selectedMismatch : Finset (Fin M_selected))
    (h_more_polygenic : M_neutral < M_selected)
    (h_selected_worse_fraction :
      (neutralMismatch.card : ℝ) / (M_neutral : ℝ) <
        (selectedMismatch.card : ℝ) / (M_selected : ℝ)) :
    M_neutral < M_selected ∧
      uniformCatastrophicPortabilityScore M_selected selectedMismatch <
        uniformCatastrophicPortabilityScore M_neutral neutralMismatch := by
  unfold uniformCatastrophicPortabilityScore
  constructor
  · exact h_more_polygenic
  · linarith

end PolygenicityAndPortability




/-!
## Heritability Partitioning

Partitioning heritability by functional category reveals
which genomic features drive PGS signal and portability.
-/

section HeritabilityPartitioning

/-- **Heritability enrichment.**
    Enrichment of category c = (h²_c / M_c) / (h²_total / M_total).
    High enrichment means the category harbors more causal signal
    per variant.

    Regime: a partition of variants into a category and its complement, with heritability read as a
    sum of squared effects. The PER-VARIANT
    normalisation is the whole content -- a category holding half the
    heritability is enriched only relative to how many variants it holds.

    Empirical status: **VALIDATED** (`simcov/battery_bulk28.py`, `group_c`).
    Effects are drawn so a category of `M_cat` variants carries a set share of
    the heritability, and the oracle is the REALISED ratio of per-variant
    heritability inside the category to the genome-wide per-variant
    heritability, computed from the drawn effects. Over category sizes 100 to
    1000 out of 4000 and shares 0.25 to 0.5, the body predicts 10.0, 2.5, 2.0
    and 12.0 against measured 9.34 ± 0.93, 2.45 ± 0.17, 2.00 ± 0.09 and 12.02 ±
    1.70 -- worst cell 0.70 sems, over a prediction spanning 83%.

    Power: the bare share `h2_cat / h2_total`, which omits the per-variant
    normalisation, is carried on the same cells and is FALSIFIED at up to 16.76
    sems (75% relative). The two agree only when a category holds exactly its
    proportional share of variants, so the design deliberately puts the
    category far from proportional -- that is the only regime in which the
    normalisation is visible at all. Control: the realised total heritability
    recovers the 0.5 it was drawn at, passing at 0.53 sems. -/
noncomputable def heritabilityEnrichment (h2_cat M_cat h2_total M_total : ℝ) : ℝ :=
  (h2_cat / M_cat) / (h2_total / M_total)

/-- **heritabilityEnrichment where its denominator vanishes, named.** The guard `h2_total / M_total`
is zero at `h2_total = 0`, `M_total = 1`. Lean returns `0` there rather than the value the
modelled quantity takes, and no type error marks the point. Consumers must require `h2_total /
M_total ≠ 0`. -/
theorem heritabilityEnrichment_at_h2total0mtotal1_is_junk (h2_cat : ℝ) (M_cat : ℝ) :
    heritabilityEnrichment h2_cat M_cat 0 1 = 0 := by
  unfold heritabilityEnrichment
  norm_num

/-- Enrichment > 1 means more heritability per variant. -/
theorem enrichment_interpretation (h2_c M_c h2_t M_t : ℝ)
    (h_ht : 0 < h2_t) (h_Mt : 0 < M_t)
    (h_enriched : h2_c / M_c > h2_t / M_t) :
    1 < heritabilityEnrichment h2_c M_c h2_t M_t := by
  unfold heritabilityEnrichment
  rw [one_lt_div₀ (div_pos h_ht h_Mt)]
  exact h_enriched

/-- **Genomic regions can be enriched for heritability.**
    When a region contains a fraction f_snp of variants but a fraction
    f_h2 of heritability, and f_h2 > f_snp, the enrichment f_h2/f_snp > 1.
    More precisely, if f_snp < α and f_h2 > β, enrichment > β/α.

    Worked example: Coding regions contain ~1.5% of variants (< 1/50)
    but ~10-20% of heritability (> 1/10), giving enrichment > 5×. -/
theorem region_heritability_enrichment
    (h2_region h2_total M_region M_total α β : ℝ)
    (h_prop_variants : M_region / M_total < α)
    (h_prop_h2 : β < h2_region / h2_total)
    (h_all_pos : 0 < h2_region ∧ 0 < h2_total ∧ 0 < M_region ∧ 0 < M_total)
    (h_α_pos : 0 < α) :
    β / α < heritabilityEnrichment h2_region M_region h2_total M_total := by
  obtain ⟨h_hc, h_ht, h_mc, h_mt⟩ := h_all_pos
  have hv : M_region < α * M_total := by rwa [div_lt_iff₀ h_mt] at h_prop_variants
  have hh : β * h2_total < h2_region := by rwa [lt_div_iff₀ h_ht] at h_prop_h2
  have hsimpl : heritabilityEnrichment h2_region M_region h2_total M_total =
    h2_region * M_total / (M_region * h2_total) := by
    unfold heritabilityEnrichment; field_simp
  rw [hsimpl, div_lt_div_iff₀ h_α_pos (mul_pos h_mc h_ht)]
  nlinarith

/-- **Squaring is strictly monotone on the nonnegatives:** `0 ≤ a`, `0 ≤ b`,
    `b < a` give `b² < a²`.

    **Both halves of the genetics are hypotheses.** The reading is that coding
    regions are under stronger purifying selection, hence effect sizes there are
    more correlated across populations (`rg_coding > rg_regulatory`), hence —
    since portability goes as `rg²` — coding variants port better. The first
    implication is assumed outright as `h_coding_higher`, and the second is
    assumed by choosing to square. No selection, no region annotation, and no
    portability measure appears below. What remains is `x ↦ x²` monotone on
    `[0, ∞)`. -/
theorem sq_lt_sq_of_nonneg_of_lt
    (rg_coding rg_regulatory : ℝ)
    (h_coding_nn : 0 ≤ rg_coding) (h_reg_nn : 0 ≤ rg_regulatory)
    (h_coding_higher : rg_regulatory < rg_coding) :
    rg_regulatory ^ 2 < rg_coding ^ 2 := by
  -- x² is strictly monotone on [0, ∞): if 0 ≤ a < b then a² < b²
  have h_sum_nonneg : 0 ≤ rg_coding + rg_regulatory := add_nonneg h_coding_nn h_reg_nn
  nlinarith

end HeritabilityPartitioning


/-!
## Architecture-Dependent Portability Predictions

Given estimated genetic architecture parameters, we can predict
expected portability for a trait across ancestries.
-/

section ArchitecturePredictions

open SNPArchitecturePortabilityModel

/-- **Portability prediction from explicit causal-SNP architecture.**

The predicted portability is the fraction of source causal squared-effect mass
that remains transportable in the target after aggregating over causal SNPs.
This keeps the prediction surface at the SNP architecture level rather than
collapsing it into a single trait-wide `r_g² × (1 - FST)` product. -/
noncomputable def predictedPortability {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) : ℝ :=
  model.portabilityScore

/-- Reference evaluation: the predicted portability is the model's recorded score. -/
theorem predictedPortability_at_reference_point {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) :
    predictedPortability model = model.portabilityScore := rfl


/-- Predicted portability is at most the full source causal signal mass. -/
theorem predicted_le_source {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (h_source : 0 < model.sourceEffectMass) :
    predictedPortability model ≤ 1 := by
  simpa [predictedPortability] using portabilityScore_le_one model h_source

/-- Source-effect-weighted average of per-SNP retention upper envelopes.

Each `retentionUpper j` is an explicit SNP-level upper bound on the fraction of
source squared-effect mass that can survive in the target at causal SNP `j`. -/
noncomputable def weightedRetentionUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ) : ℝ :=
  (∑ j, retentionUpper j * model.sourceSquaredEffect j) /
    model.sourceEffectMass

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem weightedRetentionUpperBound_at_zero_denominator_is_junk {q : ℕ}
    (model : SNPArchitecturePortabilityModel q) (retentionUpper : Fin q → ℝ)
    (hzero : model.sourceEffectMass = 0) :
    weightedRetentionUpperBound model retentionUpper = 0 := by
  unfold weightedRetentionUpperBound
  rw [hzero, div_zero]


/-- Any locuswise retention upper envelope induces a global portability upper
bound after weighting by source causal effect mass. -/
theorem predicted_le_weightedRetentionUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_bound : ∀ j,
      model.targetRetainedSquaredEffect j ≤
        retentionUpper j * model.sourceSquaredEffect j) :
    predictedPortability model ≤ weightedRetentionUpperBound model retentionUpper := by
  unfold predictedPortability weightedRetentionUpperBound portabilityScore
  have h_sum :
      model.targetRetainedEffectMass ≤
        ∑ j, retentionUpper j * model.sourceSquaredEffect j := by
    unfold targetRetainedEffectMass
    exact Finset.sum_le_sum fun j _ ↦ h_bound j
  exact (div_le_div_iff_of_pos_right h_source).2 h_sum

/-- **The slack in the retention envelope, as an identity rather than a
bound.**

The one-sided statement `predicted_le_weightedRetentionUpperBound` says only
that the envelope is above the truth. What is above it by is the
source-effect-weighted average of the locuswise slacks, and that is an equality
with no hypotheses on the envelope at all — not even that it is an upper bound.
The inequality and the attainment condition are both corollaries. -/
theorem weightedRetentionUpperBound_sub_predicted {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ) :
    weightedRetentionUpperBound model retentionUpper - predictedPortability model =
      (∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j)) / model.sourceEffectMass := by
  unfold weightedRetentionUpperBound predictedPortability portabilityScore
    targetRetainedEffectMass
  rw [div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]

/-- **Threshold equals capacity when the locuswise constraint is active.**

If the envelope is attained at every causal SNP, the global portability equals
the global bound. No symmetry of the architecture is needed and no condition on
the effect distribution: activity of the constraint at each locus is the whole
hypothesis. -/
theorem predicted_eq_weightedRetentionUpperBound_of_active {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_active : ∀ j, model.targetRetainedSquaredEffect j =
      retentionUpper j * model.sourceSquaredEffect j) :
    predictedPortability model = weightedRetentionUpperBound model retentionUpper := by
  have h_sum : model.targetRetainedEffectMass =
      ∑ j, retentionUpper j * model.sourceSquaredEffect j := by
    unfold targetRetainedEffectMass
    exact Finset.sum_congr rfl (fun j _ ↦ h_active j)
  unfold predictedPortability weightedRetentionUpperBound portabilityScore
  rw [h_sum]

/-- **The bound is attained if and only if every locuswise constraint is
active.**

The two-sided form: under the locuswise envelope, global portability meets the
global bound exactly when no causal SNP has slack. One slack locus with positive
source mass is enough to make the bound strict, and no amount of activity
elsewhere compensates. -/
theorem weightedRetentionUpperBound_eq_predicted_iff_active {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (retentionUpper : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_bound : ∀ j, model.targetRetainedSquaredEffect j ≤
      retentionUpper j * model.sourceSquaredEffect j) :
    weightedRetentionUpperBound model retentionUpper = predictedPortability model ↔
      ∀ j, model.targetRetainedSquaredEffect j =
        retentionUpper j * model.sourceSquaredEffect j := by
  have hid := weightedRetentionUpperBound_sub_predicted model retentionUpper
  constructor
  · intro h
    have hz : (∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j)) / model.sourceEffectMass = 0 := by
      rw [← hid, h, sub_self]
    have hz' : ∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j) = 0 := by
      rcases div_eq_zero_iff.mp hz with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt h_source)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sub_nonneg.mpr (h_bound j))).mp hz'
    intro j
    have hj := hall j (Finset.mem_univ j)
    linarith [hj]
  · intro h
    have hz : ∑ j, (retentionUpper j * model.sourceSquaredEffect j -
        model.targetRetainedSquaredEffect j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [h j]
      ring
    rw [← sub_eq_zero, hid, hz, zero_div]

/-- **Architecture-based trait classification.**

Traits are ranked by their explicit causal-SNP loss fractions, not by a bare
scalar portability label. A trait with a smaller fraction of lost causal signal
has a larger retained portability score. -/
theorem architecture_classification
    {q_high q_moderate q_oligo : ℕ}
    (highPoly : SNPArchitecturePortabilityModel q_high)
    (moderate : SNPArchitecturePortabilityModel q_moderate)
    (oligo : SNPArchitecturePortabilityModel q_oligo)
    (h_high_source : 0 < highPoly.sourceEffectMass)
    (h_moderate_source : 0 < moderate.sourceEffectMass)
    (h_oligo_source : 0 < oligo.sourceEffectMass)
    (h_loss_order :
      highPoly.relativePortabilityLoss < moderate.relativePortabilityLoss ∧
        moderate.relativePortabilityLoss < oligo.relativePortabilityLoss) :
    predictedPortability oligo < predictedPortability moderate ∧
      predictedPortability moderate < predictedPortability highPoly := by
  rcases h_loss_order with ⟨h_high_moderate, h_moderate_oligo⟩
  constructor
  · rw [predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss oligo h_oligo_source,
      predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss moderate h_moderate_source]
    linarith
  · rw [predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss moderate h_moderate_source,
      predictedPortability,
      portabilityScore_eq_one_sub_relativePortabilityLoss highPoly h_high_source]
    linarith

/-- Locuswise `r_g² × (1 - FST)` upper envelope for retained causal signal.

This is not a single trait-wide multiplicative law. Instead, each causal SNP
gets its own upper envelope from a locus-specific effect-correlation bound
`rgUpper j` and a locus-specific divergence lower bound `fstLower j`, and the
global portability bound is their source-effect-weighted average.

    Empirical status: NOT AN EMPIRICAL CLAIM. `rgUpper` and `fstLower` are free
    functions supplied by the caller and the weights are fields of the model, so
    the body averages numbers the caller chose: no assignment of them is
    refutable. The substantive claim -- that a causal SNP retains at most
    `rgUpper j ^ 2 * (1 - fstLower j)` of its source squared effect -- is not
    made here. It is the HYPOTHESIS `h_locuswise_bound` of
    `portability_upper_bound_from_rg_fst` below, which is where a measurement of
    the envelope's FORM belongs, and where a design would first have to fix what
    "retained squared effect" means operationally -- this structure leaves it a
    declared field. What this definition does fix is how per-locus envelopes are
    aggregated: a source-squared-effect-weighted average rather than a
    trait-wide product. -/
noncomputable def rgFstWeightedUpperBound {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (rgUpper fstLower : Fin q → ℝ) : ℝ :=
  weightedRetentionUpperBound model
    (fun j ↦ (rgUpper j) ^ 2 * (1 - fstLower j))

/-- **Explicit SNP-level portability upper bound from locuswise effect
correlation and causal divergence.**

If each causal SNP retains at most `rgUpper(j)^2 * (1 - fstLower(j))` of its
source squared-effect mass in the target, then total portability is bounded by
the source-effect-weighted average of those locuswise envelopes. -/
theorem portability_upper_bound_from_rg_fst
    {q : ℕ}
    (model : SNPArchitecturePortabilityModel q)
    (rgUpper fstLower : Fin q → ℝ)
    (h_source : 0 < model.sourceEffectMass)
    (h_locuswise_bound : ∀ j,
      model.targetRetainedSquaredEffect j ≤
        (rgUpper j) ^ 2 * (1 - fstLower j) * model.sourceSquaredEffect j) :
    predictedPortability model ≤ rgFstWeightedUpperBound model rgUpper fstLower := by
  unfold rgFstWeightedUpperBound
  exact predicted_le_weightedRetentionUpperBound model
    (fun j ↦ (rgUpper j) ^ 2 * (1 - fstLower j))
    h_source h_locuswise_bound

end ArchitecturePredictions

end Descent.PopGen
