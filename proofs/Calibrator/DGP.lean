/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Calibrator.TransportIdentities
-- Step 4b below needs `FiniteSpectralModel.degradation_eq_zero_iff`, which supplies a
-- positivity certificate for excess target risk that does not read an F_ST difference.
-- See the discussion above `excess_target_risk_pos_of_bandwise_readout_mismatch`.
import Calibrator.SpectralDegradation

namespace Calibrator

/-! ### The ploidy-scaled rates, and the identity fraction they feed

`θ = 4 Nₑ μ` and `M = 4 Nₑ m` are the same scaling applied to a mutation rate and to a
migration rate, and `1 / (1 + θ)` is the identity fraction at either. Six accessors across
five structures — `SplitMigrationModel`, `GenerationalPopGenParameters`,
`MutationDriftModelAssumptions`, `EvolutionaryParameters` and `PGSEvolutionaryModel` —
used to spell out their own `4 * Ne * _`, and two more wrote out the quotient. That is
eight independent chances to write a different four.

They sit at the top of this module because that is the lowest point every user can see.
The copies existed for a structural reason rather than by oversight: `scaledMutationRate`
and `fstMutationDriftEquilibrium` lived in `PopulationGeneticsFoundations` and
`scaledMigrationRate` in `PortabilityDrift`, each of which *imports* the modules whose
definitions were computing them. A definition that cannot reach the function it is
computing will be written out again, so placing these correctly is what removes the
duplication rather than merely forbidding it.

Moving definitions like these has now broken this module three times, never in the
mathematics and always in sites that *name* a definition without *applying* it —
`unfold` lists and docstrings. Search this file for "Note for anyone editing the Fst
cluster" for the two failure shapes and the rule they share, recorded next to
`fstEquilibrium` where they landed. -/

/-- **Scaled mutation rate** `θ = 4 Nₑ μ`, the fundamental parameter of neutral theory.

    Empirical status: UNTESTED. -/
noncomputable def scaledMutationRate (Ne μ : ℝ) : ℝ :=
  4 * Ne * μ

/-- **The scaling factor is four times the effective size.** Positivity is shared by every
positive multiple of this product; dividing by the mutation rate exhibits the factor, which is
the whole content of the scaling convention. -/
theorem scaledMutationRate_div_mu (Ne μ : ℝ) (h : μ ≠ 0) :
    scaledMutationRate Ne μ / μ = 4 * Ne := by
  unfold scaledMutationRate
  field_simp

/-- **Scaled migration rate** `M = 4 Nₑ m`, the same scaling applied to gene flow.

    Empirical status: UNTESTED. -/
noncomputable def scaledMigrationRate (Ne m : ℝ) : ℝ :=
  4 * Ne * m

/-- **The scaling factor is four times the effective size**, the same convention as the scaled
mutation rate. Dividing by the migration rate exhibits it, which is the whole content of the
convention and is what a body carrying any other multiple would fail while remaining positive and
increasing in both arguments. -/
theorem scaledMigrationRate_div_m (Ne m : ℝ) (h : m ≠ 0) :
    scaledMigrationRate Ne m / m = 4 * Ne := by
  unfold scaledMigrationRate
  field_simp

/-- **Identity fraction at a scaled rate**, `1 / (1 + θ)`.

Not stipulated: `PopulationGeneticsFoundations.fstMutationDriftEquilibrium_isFixedPoint`
derives it as the rest point of `scaledIdentityStep` at scaled rate `θ`. That theorem lives
in another module, so a guard looking for a fixed-point result beside the definition will
not find it.

    Empirical status: UNTESTED. -/
noncomputable def fstMutationDriftEquilibrium (θ : ℝ) : ℝ :=
  1 / (1 + θ)

/-- **The mutation-drift equilibrium `Fst`, pinned.** This definition carries no theorem of its
own. At `θ = 1` mutation and drift contribute equally and the equilibrium differentiation is one
half, which fixes the `1 + θ` denominator against `1 / (1 + 2 * θ)` and `1 / (1 + θ) ^ 2`. -/
theorem fstMutationDriftEquilibrium_at_unit_theta :
    fstMutationDriftEquilibrium 1 = 1 / 2 := by
  unfold fstMutationDriftEquilibrium
  norm_num

/-- **Per-generation heterozygosity decay** at effective size `Nₑ` and scaled mutation
rate `θ`: drift removes a fraction `1 / (2 Nₑ)` and mutation is replenishing against it.
Two accessors on two structures used to write this product out separately.

    Empirical status: UNTESTED. -/
noncomputable def hetDecayFromScaled (Ne θ : ℝ) : ℝ :=
  (1 - 1 / (2 * Ne)) * (1 - θ / (2 * Ne))

/-- **The two channels factor.** Heterozygosity decay is drift times mutation, and at zero scaled
mutation only the drift factor survives. A body that added the two channels instead of
multiplying them would fail this, and would also predict decay exceeding one for large `θ`. -/
theorem hetDecayFromScaled_no_mutation (Ne : ℝ) :
    hetDecayFromScaled Ne 0 = 1 - 1 / (2 * Ne) := by
  unfold hetDecayFromScaled; ring


open scoped InnerProductSpace
open InnerProductSpace
open MeasureTheory

/-- **Heterozygosity decay at zero effective size, named, and doubled.** Both factors divide by
`2 Ne`, so at `Ne = 0` both are junk-zero and both factors collapse to one: the decay multiplier
is `1`, reporting a population that loses no heterozygosity at all. An empty population in fact
loses everything in one generation, so this is the maximal reversal, and it is produced by two
independent junk branches in the same expression -- neither of which is visible in the value.
Consumers must require `Ne ≠ 0`. -/
theorem hetDecayFromScaled_zero_population_is_junk (θ : ℝ) :
    hetDecayFromScaled 0 θ = 1 := by
  unfold hetDecayFromScaled
  simp

section AllClaims

variable {p k : ℕ}

abbrev CausalVec (c : ℕ) := Fin c → ℝ
abbrev TagVec (t : ℕ) := Fin t → ℝ

/-! ### Discrete HWE Score DGP

This block provides a population-genetics DGP for polygenic scores built from discrete
diploid genotypes under locuswise Hardy-Weinberg equilibrium. Gaussian score formulas are
exposed only as approximation centers, together with an explicit Berry-Esseen error radius.
-/

/-- Discrete genotype-based score DGP under locuswise HWE and an external liability/AUC link. -/
structure HWEPolygenicScoreDGP (m : ℕ) where
  scoreModel : HWEScoreModel m
  berryEsseenConstant : ℝ
  berryEsseenConstant_nonneg : 0 ≤ berryEsseenConstant

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def HWEPolygenicScoreDGP.witness (m : ℕ) : HWEPolygenicScoreDGP m where
  scoreModel :=
    { alleleFreq := fun _ ↦ HardyWeinbergModel.witness
      effect := fun _ ↦ 0 }
  berryEsseenConstant := 0
  berryEsseenConstant_nonneg := le_refl 0

/-- Exact score mean under the discrete HWE architecture. -/
noncomputable def HWEPolygenicScoreDGP.scoreMean {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m) : ℝ :=
  dgp.scoreModel.scoreMean

/-- Exact score variance under the discrete HWE architecture. -/
noncomputable def HWEPolygenicScoreDGP.scoreVariance {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m) : ℝ :=
  dgp.scoreModel.scoreVariance

/-- Berry-Esseen error radius for the discrete HWE score. -/
noncomputable def HWEPolygenicScoreDGP.scoreApproximationError {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m) : ℝ :=
  dgp.scoreModel.berryEsseenErrorBound dgp.berryEsseenConstant

/-! **The two interval-membership theorems below are `Set.Icc` membership, and nothing in
them is certified.**

`scoreApproximationError` is `berryEsseenErrorBound`, which is the *formula* `C·ρ₃/σ³`
written down as a definition — no Berry-Esseen theorem is invoked from Mathlib or proved
here, and `berryEsseenConstant` is a free field of `HWEPolygenicScoreDGP` rather than a
constant any bound supplies.  Even granting the formula, a Kolmogorov bound on the
standardized *score CDF* is not a bound on AUC or on `R²`: each is a further functional of
that CDF and transferring the radius across is a separate estimate this corpus does not
have.  That transfer is exactly what enters below as the hypothesis `h`.

So what these prove is `mem_approximationInterval_of_abs_sub_le` — `|x - c| ≤ ε → x ∈
[c-ε, c+ε]` — with `ε` instantiated at a named quantity.  They are kept because the
interval interface is used downstream, and stated so that the assumed step is visible in
the hypothesis rather than implied by the word "certified".  Note also that
`approximationInterval` is used for both AUC and `R²` below; the two aliases that used to
distinguish them were the *same* function
`approximationInterval` under two names, so nothing in either statement would detect
swapping AUC for `R²`. -/

/-- Any exact AUC within `scoreApproximationError` of a Gaussian center lies in the
corresponding interval around that center.  The AUC-side error control is the hypothesis. -/
theorem HWEPolygenicScoreDGP.mem_aucApproximationInterval_of_abs_sub_le
    {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m)
    (aucExact aucGaussian : ℝ)
    (h : |aucExact - aucGaussian| ≤ dgp.scoreApproximationError) :
    aucExact ∈
      Calibrator.approximationInterval aucGaussian dgp.scoreApproximationError := by
  simpa [Calibrator.approximationInterval] using
    (mem_approximationInterval_of_abs_sub_le
    aucExact aucGaussian dgp.scoreApproximationError
    (by
      unfold HWEPolygenicScoreDGP.scoreApproximationError
      exact dgp.scoreModel.berryEsseenErrorBound_nonneg _ dgp.berryEsseenConstant_nonneg)
    h)

/-- Any exact `R²` within `scoreApproximationError` of a Gaussian center lies in the
corresponding interval around that center.  The `R²`-side error control is the hypothesis. -/
theorem HWEPolygenicScoreDGP.mem_r2ApproximationInterval_of_abs_sub_le
    {m : ℕ} [Fintype (Fin m)]
    (dgp : HWEPolygenicScoreDGP m)
    (r2Exact r2Gaussian : ℝ)
    (h : |r2Exact - r2Gaussian| ≤ dgp.scoreApproximationError) :
    r2Exact ∈
      Calibrator.approximationInterval r2Gaussian dgp.scoreApproximationError := by
  simpa [Calibrator.approximationInterval] using
    (mem_approximationInterval_of_abs_sub_le
    r2Exact r2Gaussian dgp.scoreApproximationError
    (by
      unfold HWEPolygenicScoreDGP.scoreApproximationError
      exact dgp.scoreModel.berryEsseenErrorBound_nonneg _ dgp.berryEsseenConstant_nonneg)
    h)

/-! ### Tagged DGP (Causal vs Observable Architecture)

This block explicitly separates:
- latent causal variants `X_causal`
- observed/tag variants `X_tag`

and defines LD as the causal-tag correlation matrix under a joint law on `(X_causal, X_tag)`.
-/

/-- Data-generating process with separate latent causal and observed/tag spaces. -/
structure TaggedDataGeneratingProcess (c t : ℕ) where
  trueExpectation : CausalVec c → TagVec t → ℝ
  jointMeasureCT : Measure (CausalVec c × TagVec t)

/-- Mean of causal coordinate `i` under the joint tagged law. -/
noncomputable def causalMean {c t : ℕ}
    (dgp : TaggedDataGeneratingProcess c t) (i : Fin c) : ℝ :=
  ∫ x : CausalVec c × TagVec t, x.1 i ∂dgp.jointMeasureCT

/-- Mean of tag coordinate `j` under the joint tagged law. -/
noncomputable def tagMean {c t : ℕ}
    (dgp : TaggedDataGeneratingProcess c t) (j : Fin t) : ℝ :=
  ∫ x : CausalVec c × TagVec t, x.2 j ∂dgp.jointMeasureCT

/-- Causal-tag cross-covariance entry `Cov(X_causal[i], X_tag[j])`. -/
noncomputable def crossCovEntry {c t : ℕ}
    (dgp : TaggedDataGeneratingProcess c t) (i : Fin c) (j : Fin t) : ℝ :=
  ∫ x : CausalVec c × TagVec t,
      (x.1 i - causalMean dgp i) * (x.2 j - tagMean dgp j) ∂dgp.jointMeasureCT


/-- Cross-covariance matrix `Σ_tc` between tag and causal coordinates. -/
noncomputable def sigmaTagCausal {c t : ℕ}
    (dgp : TaggedDataGeneratingProcess c t) : Matrix (Fin t) (Fin c) ℝ :=
  Matrix.of fun j i ↦ crossCovEntry dgp i j


/-- Source tagged second moments for best linear prediction from tags.

The scored-to-causal alignment is decomposed into directly observed causal
variants and proxy tagging of unscored causal variants. This makes the
causal-vs-tag distinction explicit at the moment level. -/
structure SourceTaggedMoments (c t : ℕ) where
  sigmaTagSource : Matrix (Fin t) (Fin t) ℝ
  directCausalSource : Matrix (Fin t) (Fin c) ℝ
  proxyTaggingSource : Matrix (Fin t) (Fin c) ℝ

/-- Aggregate source scored-to-causal alignment is the sum of directly scored
causal variants and proxy tagging. -/
noncomputable def SourceTaggedMoments.sigmaTagCausal {c t : ℕ}
    (mom : SourceTaggedMoments c t) : Matrix (Fin t) (Fin c) ℝ :=
  mom.directCausalSource + mom.proxyTaggingSource

/-- Closed-form source best linear predictor weights:
`w*_S = Σ_tag,S^{-1} Σ_tc,S β_c`.

    Empirical status: UNTESTED. -/
noncomputable def sourceBestLinearWeightsFromLD {c t : ℕ}
    (mom : SourceTaggedMoments c t) (betaCausal : CausalVec c) : TagVec t :=
  mom.sigmaTagSource⁻¹.mulVec (mom.sigmaTagCausal.mulVec betaCausal)

/-- Frobenius norm squared for a square covariance matrix:
`‖A‖_F² = Σᵢ Σⱼ Aᵢⱼ²`. -/
noncomputable def frobeniusNormSq {t : ℕ}
    (A : Matrix (Fin t) (Fin t) ℝ) : ℝ :=
  ∑ i : Fin t, ∑ j : Fin t, (A i j) ^ 2

theorem frobeniusNormSq_nonneg {t : ℕ}
    (A : Matrix (Fin t) (Fin t) ℝ) :
    0 ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg (A i j)))

theorem frobeniusNormSq_pos_of_exists_ne_zero {t : ℕ}
    (A : Matrix (Fin t) (Fin t) ℝ)
    (h : ∃ i j, A i j ≠ 0) :
    0 < frobeniusNormSq A := by
  rcases h with ⟨i0, j0, hne⟩
  unfold frobeniusNormSq
  have h_inner_nonneg : 0 ≤ ∑ j : Fin t, (A i0 j) ^ 2 :=
    Finset.sum_nonneg (fun j _ ↦ sq_nonneg (A i0 j))
  have h_inner_lower : (A i0 j0) ^ 2 ≤ ∑ j : Fin t, (A i0 j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (A i0 j)) (by simp)
  have h_outer_lower :
      ∑ j : Fin t, (A i0 j) ^ 2 ≤ ∑ i : Fin t, ∑ j : Fin t, (A i j) ^ 2 := by
    exact Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg (A i j)))
      (by simp)
  have hsq_pos : 0 < (A i0 j0) ^ 2 := by
    exact sq_pos_of_ne_zero hne
  exact lt_of_lt_of_le hsq_pos (le_trans h_inner_lower h_outer_lower)

/-- Source/target `R²` represented from MSE and total phenotype variance. -/
noncomputable def r2FromMSE (mse varY : ℝ) : ℝ :=
  1 - mse / varY

/-- **`R²` from mean squared error, pinned.** This definition carries no theorem of its own. A
predictor whose error variance is half the outcome variance explains half of it. -/
theorem r2FromMSE_half_variance :
    r2FromMSE 1 2 = 1 / 2 := by
  unfold r2FromMSE
  norm_num

/-- **`R²` against a constant outcome, named.** An outcome with no variance cannot be explained
or failed to be explained: `R²` is undefined. The divisor is zero, the ratio is junk-zero, and
the result is `1` -- PERFECT prediction, certified for a predictor that has done nothing, against
a target that never moved. The direction matters: a junk `R²` of zero would look like a failure
and be investigated, whereas a junk `R²` of one looks like a success. Consumers must require
`varY ≠ 0`. -/
theorem r2FromMSE_constant_outcome_is_junk (mse : ℝ) :
    r2FromMSE mse 0 = 1 := by
  unfold r2FromMSE
  simp

/-- Explained-variance fraction from score/outcome covariance, score variance,
and total outcome variance. This is the exact moment-level coordinate used for
explicit source/target transport witnesses. -/
noncomputable def explainedR2FromTransportMoments
    (scoreOutcomeCov scoreVariance outcomeVariance : ℝ) : ℝ :=
  scoreOutcomeCov ^ 2 / (scoreVariance * outcomeVariance)

/-- **explainedR2FromTransportMoments at zero scoreVariance, named.** A score with no variance
explains nothing, and the ratio is undefined rather than zero -- there is no denominator to
normalise the covariance against. Lean returns `0`, which is indistinguishable from a score that
varies and predicts nothing. Consumers must require `scoreVariance ≠ 0`. -/
theorem explainedR2FromTransportMoments_zero_scorevariance_is_junk
    (scoreOutcomeCov outcomeVariance : ℝ) :
    explainedR2FromTransportMoments scoreOutcomeCov 0 outcomeVariance = 0 := by
  unfold explainedR2FromTransportMoments
  simp

/-- **A score that is the outcome explains all of it.** When the covariance and both variances
coincide the explained fraction is exactly one, which fixes the normalisation; every positive
multiple of this ratio is a squared covariance over a variance product and would miss it. -/
theorem explainedR2FromTransportMoments_perfect (v : ℝ) (h : v ≠ 0) :
    explainedR2FromTransportMoments v v v = 1 := by
  unfold explainedR2FromTransportMoments
  field_simp

/-- **Rescaling the score leaves the explained fraction alone.** Multiplying the score by `c`
multiplies its covariance with the outcome by `c` and its variance by `c²`. This is the property
that makes the quantity a squared correlation and lets it be compared across scores reported on
different scales. -/
theorem explainedR2FromTransportMoments_scale_invariant
    (scoreOutcomeCov scoreVariance outcomeVariance c : ℝ) (hc : c ≠ 0) :
    explainedR2FromTransportMoments (c * scoreOutcomeCov) (c ^ 2 * scoreVariance) outcomeVariance
      = explainedR2FromTransportMoments scoreOutcomeCov scoreVariance outcomeVariance := by
  unfold explainedR2FromTransportMoments
  rw [mul_pow, show c ^ 2 * scoreVariance * outcomeVariance
        = c ^ 2 * (scoreVariance * outcomeVariance) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- Source tagged moments for the explicit LD witness.

    Empirical status: UNTESTED. -/
def ldWitnessSourceMoments : SourceTaggedMoments 2 2 where
  sigmaTagSource := 1
  directCausalSource := 1
  proxyTaggingSource := 0

/-- Source causal effects for the explicit LD witness.

    Empirical status: UNTESTED. -/
def ldWitnessBeta : CausalVec 2 := ![1, 1]

/-- Source-learned weights for the explicit LD witness.

    Empirical status: UNTESTED. -/
noncomputable def ldWitnessSourceWeights : TagVec 2 :=
  sourceBestLinearWeightsFromLD ldWitnessSourceMoments ldWitnessBeta

/-- Target cross-covariance witness shared across the two target LD states.

    Empirical status: UNTESTED. -/
def ldWitnessTargetCross : TagVec 2 := ![1, 1]

/-- **The witness scores the two SNPs with the causal effects themselves.**
`CausalVec 2` and `TagVec 2` are both `Fin 2 → ℝ`, so the target cross-covariance vector
and the source causal vector of this witness are literally the same vector; the two names
record which side of the transport each is read on. Changing one effect size without the
other stops this from compiling. -/
theorem ldWitnessTargetCross_eq_ldWitnessBeta :
    ldWitnessTargetCross = ldWitnessBeta := rfl

/-- Target LD witness with independent scored SNPs.

    Empirical status: UNTESTED. -/
def ldWitnessSigmaTargetIndependent : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

/-- Target LD witness with perfect correlation between the scored SNPs.

    Empirical status: UNTESTED. -/
def ldWitnessSigmaTargetCorrelated : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 1, 1]

@[simp] theorem ldWitnessSourceWeights_eq :
    ldWitnessSourceWeights = ![1, 1] := by
  ext i
  fin_cases i <;>
    simp [ldWitnessSourceWeights, sourceBestLinearWeightsFromLD, ldWitnessSourceMoments,
      SourceTaggedMoments.sigmaTagCausal, ldWitnessBeta, Matrix.mulVec, dotProduct]

/-- Concrete witness that target LD structure changes target explained variance
even when the source weights and target predictor/outcome cross-covariance are
held fixed. This is why DGP does not expose a single trait-level transport
scalar as a sufficient biological summary. -/
theorem target_ld_shift_changes_explainedR2_under_fixed_source_weights :
    explainedR2FromTransportMoments
        (dotProduct ldWitnessSourceWeights ldWitnessTargetCross)
        (dotProduct ldWitnessSourceWeights
          (ldWitnessSigmaTargetCorrelated.mulVec ldWitnessSourceWeights))
        4 <
      explainedR2FromTransportMoments
        (dotProduct ldWitnessSourceWeights ldWitnessTargetCross)
        (dotProduct ldWitnessSourceWeights
          (ldWitnessSigmaTargetIndependent.mulVec ldWitnessSourceWeights))
        4 := by
  rw [ldWitnessSourceWeights_eq]
  norm_num [explainedR2FromTransportMoments, ldWitnessTargetCross, ldWitnessSigmaTargetCorrelated,
    ldWitnessSigmaTargetIndependent, Matrix.mulVec, dotProduct]

/-- Core mismatch theorem:
if target excess MSE is lower-bounded by `λ * ‖ΣS-ΣT‖_F²` with `λ>0`
and covariance mismatch is nonzero, then target MSE is strictly larger. -/
theorem target_mse_strictly_increases_of_covariance_mismatch
    {t : ℕ}
    (mseSource mseTarget lam : ℝ)
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (h_gap_lb :
      lam * frobeniusNormSq (sigmaSource - sigmaTarget) ≤ mseTarget - mseSource)
    (hlam : 0 < lam)
    (h_mismatch : 0 < frobeniusNormSq (sigmaSource - sigmaTarget)) :
    mseSource < mseTarget := by
  have hpos : 0 < lam * frobeniusNormSq (sigmaSource - sigmaTarget) := mul_pos hlam h_mismatch
  linarith

/-- Core mismatch theorem in `R²` units:
under fixed positive total variance, strict MSE increase implies strict target `R²` drop. -/
theorem target_r2_strictly_decreases_of_covariance_mismatch
    {t : ℕ}
    (mseSource mseTarget varY lam : ℝ)
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (h_gap_lb :
      lam * frobeniusNormSq (sigmaSource - sigmaTarget) ≤ mseTarget - mseSource)
    (hlam : 0 < lam)
    (h_mismatch : 0 < frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_varY_pos : 0 < varY) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY := by
  have hmse : mseSource < mseTarget :=
    target_mse_strictly_increases_of_covariance_mismatch
      mseSource mseTarget lam sigmaSource sigmaTarget h_gap_lb hlam h_mismatch
  unfold r2FromMSE
  have h_inv_pos : 0 < (1 / varY) := one_div_pos.mpr h_varY_pos
  have hdiv : mseSource / varY < mseTarget / varY := by
      have hmul : mseSource * (1 / varY) < mseTarget * (1 / varY) :=
        mul_lt_mul_of_pos_right hmse h_inv_pos
      simpa [div_eq_mul_inv] using hmul
  have hneg : -(mseTarget / varY) < -(mseSource / varY) := neg_lt_neg hdiv
  linarith

/-! ### Step 4: Demography (`F_ST`) → Covariance Divergence (with tagging density)

This block introduces a demographic lower bound connecting divergence to covariance-matrix
mismatch in observable tag space. It includes an explicit recombination/array sparsity factor:
- if tagging is effectively perfect (`arraySparsity = 0`), bound collapses to `0`;
- for sparse arrays (`arraySparsity > 0`), mismatch grows with divergence `fstTarget - fstSource`.
-/

/-- Effective mismatch scale from recombination and array sparsity (tag density inverse). -/
noncomputable def taggingMismatchScale (recombRate arraySparsity : ℝ) : ℝ :=
  recombRate * arraySparsity

/-- **A fully dense array leaves only the recombination rate.** Sparsity one is the reference
point, and it fixes the proportionality constant that a rescaled body would change. -/
theorem taggingMismatchScale_dense (recombRate : ℝ) :
    taggingMismatchScale recombRate 1 = recombRate := by
  unfold taggingMismatchScale
  ring

/-- Demography-to-LD lower bound template used in portability theorems.

**Vacuous in the generic split, and this is measured, not suspected.** The bound is
proportional to `fstTarget - fstSource`, so it is identically zero whenever the two
populations are equally diverged from a common ancestor — which is the ordinary case and
the one ancestry-specific LD results are about. Over simulated configurations of that
kind the squared Frobenius LD mismatch it is supposed to bound ranged from 2.554 to
7.346 while the bound sat at zero.

It is also never *proved* anywhere: it appears only as a hypothesis
(`covariance_mismatch_pos_of_fst_and_sparse_array`, `target_r2_drop_of_fst_and_sparse_array`),
so those two theorems rest on a quantity that vanishes exactly where they would be
applied. Step 4b below is the non-vacuous replacement and does not read this definition. -/
noncomputable def demographicCovarianceGapLowerBound
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ) : ℝ :=
  kappa * taggingMismatchScale recombRate arraySparsity * (fstTarget - fstSource)

/-- **Equal differentiation gives a vacuous bound.** The file already records that this bound is
identically zero when the two populations share an `F_ST`, as a warning; stating it fixes the
origin, which no proportionality claim about `kappa` or the mismatch scale can. -/
theorem demographicCovarianceGapLowerBound_equal_fst
    (fst recombRate arraySparsity kappa : ℝ) :
    demographicCovarianceGapLowerBound fst fst recombRate arraySparsity kappa = 0 := by
  unfold demographicCovarianceGapLowerBound
  ring

/-- The two linked loci need two distinct indices, so the block size must be at least two.
That is carried as an ordinary explicit argument `ht : 2 ≤ t` rather than a `Fact` instance:
the bound is a premise of every statement below, and instance syntax would hide it from
their signatures. -/
private def twoLocusIdx0 {t : ℕ} (ht : 2 ≤ t) : Fin t :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) ht⟩

private def twoLocusIdx1 {t : ℕ} (ht : 2 ≤ t) : Fin t :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) ht⟩

/-- Survival of two linked loci to the MRCA under discrete recombination.

    Empirical status: UNTESTED. -/
noncomputable def discreteRecombinationSurvival (recombRate : ℝ) (tmrca : ℕ) : ℝ :=
  (1 - recombRate) ^ tmrca

/-- Two-locus covariance induced by IBD persistence up to the MRCA. -/
noncomputable def twoLocusIBDCovariance (ibdWeight recombRate : ℝ) (tmrca : ℕ) : ℝ :=
  ibdWeight * discreteRecombinationSurvival recombRate tmrca

/-- `N × N` covariance matrix generated by a single two-locus coalescent block.
The diagonal is normalized to `1`; the linked pair `(0,1)` and `(1,0)` carries
the covariance implied by the recombination-survival probability.

    Empirical status: UNTESTED. -/
noncomputable def twoLocusCoalescentCovarianceMatrix {t : ℕ} (ht : 2 ≤ t)
    (ibdWeight recombRate : ℝ) (tmrca : ℕ) : Matrix (Fin t) (Fin t) ℝ :=
  fun i j ↦
    if i = twoLocusIdx0 ht ∧ j = twoLocusIdx1 ht then
      twoLocusIBDCovariance ibdWeight recombRate tmrca
    else if i = twoLocusIdx1 ht ∧ j = twoLocusIdx0 ht then
      twoLocusIBDCovariance ibdWeight recombRate tmrca
    else if i = j then 1 else 0

private theorem twoLocusCoalescentCovarianceMatrix_diff_lower_bound
    {t : ℕ} (ht : 2 ≤ t)
    (ibdWeightS recombRateS : ℝ) (tmrcaS : ℕ)
    (ibdWeightT recombRateT : ℝ) (tmrcaT : ℕ) :
    2 *
        (twoLocusIBDCovariance ibdWeightS recombRateS tmrcaS -
          twoLocusIBDCovariance ibdWeightT recombRateT tmrcaT) ^ 2 ≤
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix ht ibdWeightS recombRateS tmrcaS -
          twoLocusCoalescentCovarianceMatrix ht ibdWeightT recombRateT tmrcaT) := by
  let i0 : Fin t := twoLocusIdx0 ht
  let i1 : Fin t := twoLocusIdx1 ht
  let A :=
    twoLocusCoalescentCovarianceMatrix ht ibdWeightS recombRateS tmrcaS -
      twoLocusCoalescentCovarianceMatrix ht ibdWeightT recombRateT tmrcaT
  have hi_ne : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1, twoLocusIdx0, twoLocusIdx1] at hval
  have h01 :
      A i0 i1 =
        twoLocusIBDCovariance ibdWeightS recombRateS tmrcaS -
          twoLocusIBDCovariance ibdWeightT recombRateT tmrcaT := by
    simp [A, i0, i1, twoLocusCoalescentCovarianceMatrix]
  have h10 :
      A i1 i0 =
        twoLocusIBDCovariance ibdWeightS recombRateS tmrcaS -
          twoLocusIBDCovariance ibdWeightT recombRateT tmrcaT := by
    simp [A, i0, i1, twoLocusCoalescentCovarianceMatrix, hi_ne, Matrix.sub_apply]
  have h_row01 :
      (A i0 i1)^2 ≤ ∑ j : Fin t, (A i0 j)^2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (A i0 j)) (by simp)
  have h_row10 :
      (A i1 i0)^2 ≤ ∑ j : Fin t, (A i1 j)^2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (A i1 j)) (by simp)
  have h_pair :
      Finset.sum ({i0, i1} : Finset (Fin t)) (fun i ↦ ∑ j : Fin t, (A i j)^2) =
        (∑ j : Fin t, (A i0 j)^2) + (∑ j : Fin t, (A i1 j)^2) := by
    rw [Finset.sum_pair hi_ne]
  have h_selected_le :
      (A i0 i1)^2 + (A i1 i0)^2 ≤
        Finset.sum ({i0, i1} : Finset (Fin t)) (fun i ↦ ∑ j : Fin t, (A i j)^2) := by
    rw [h_pair]
    exact add_le_add h_row01 h_row10
  have h_subset_le :
      Finset.sum ({i0, i1} : Finset (Fin t)) (fun i ↦ ∑ j : Fin t, (A i j)^2) ≤
        ∑ i : Fin t, (∑ j : Fin t, (A i j)^2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
      intro i _ _
      exact Finset.sum_nonneg (fun j _ ↦ sq_nonneg (A i j)))
  calc
    2 *
        (twoLocusIBDCovariance ibdWeightS recombRateS tmrcaS -
          twoLocusIBDCovariance ibdWeightT recombRateT tmrcaT) ^ 2 =
        (A i0 i1)^2 + (A i1 i0)^2 := by
      rw [h01, h10]
      ring
    _ ≤ Finset.sum ({i0, i1} : Finset (Fin t)) (fun i ↦ ∑ j : Fin t, (A i j)^2) := h_selected_le
    _ ≤ ∑ i : Fin t, (∑ j : Fin t, (A i j)^2) := h_subset_le

/-- Algebraic decomposition of the two-locus covariance gap in terms of the MRCA time gap. -/
theorem twoLocusIBDCovariance_gap_eq
    (ibdWeight recombRate : ℝ) (tSource tTarget : ℕ)
    (h_time : tSource ≤ tTarget) :
    twoLocusIBDCovariance ibdWeight recombRate tSource -
        twoLocusIBDCovariance ibdWeight recombRate tTarget =
      ibdWeight * discreteRecombinationSurvival recombRate tSource *
        (1 - discreteRecombinationSurvival recombRate (tTarget - tSource)) := by
  have h_split :
      discreteRecombinationSurvival recombRate tTarget =
        discreteRecombinationSurvival recombRate tSource *
          discreteRecombinationSurvival recombRate (tTarget - tSource) := by
    unfold discreteRecombinationSurvival
    rw [← pow_add, Nat.add_sub_of_le h_time]
  unfold twoLocusIBDCovariance
  rw [h_split]
  ring

/-- Exact covariance-gap lower bound generated by the two-locus coalescent.
The `N × N` matrix mismatch is therefore controlled by recombination and the MRCA time gap,
not by an arbitrary covariance witness. -/
theorem twoLocusCoalescent_covariance_gap_lower_bound
    {t : ℕ} (ht : 2 ≤ t)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_time : tSource ≤ tTarget) :
    2 *
        (ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 ≤
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget) := by
  have h_gap :
      twoLocusIBDCovariance ibdWeight recombRate tSource -
          twoLocusIBDCovariance ibdWeight recombRate tTarget =
        ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource)) :=
    twoLocusIBDCovariance_gap_eq ibdWeight recombRate tSource tTarget h_time
  have h_matrix :
      2 *
          (twoLocusIBDCovariance ibdWeight recombRate tSource -
            twoLocusIBDCovariance ibdWeight recombRate tTarget) ^ 2 ≤
        frobeniusNormSq
          (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource -
            twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget) := by
    simpa using
      (twoLocusCoalescentCovarianceMatrix_diff_lower_bound ht
        ibdWeight recombRate tSource
        ibdWeight recombRate tTarget)
  rw [h_gap] at h_matrix
  exact h_matrix

/-- Strict positivity of the covariance mismatch when the target population has a larger
expected MRCA time and recombination is non-degenerate. -/
theorem covariance_mismatch_pos_of_twoLocusCoalescent
    {t : ℕ} (ht : 2 ≤ t)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    0 <
      frobeniusNormSq
        (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource -
          twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget) := by
  have h_gap_lb :=
    twoLocusCoalescent_covariance_gap_lower_bound
      ht ibdWeight recombRate tSource tTarget h_time.le
  have h_base_nonneg : 0 ≤ 1 - recombRate := by linarith
  have h_base_pos : 0 < 1 - recombRate := by linarith
  have h_base_lt_one : 1 - recombRate < 1 := by linarith
  have h_delta_ne : tTarget - tSource ≠ 0 := Nat.sub_ne_zero_of_lt h_time
  have h_survival_pos : 0 < discreteRecombinationSurvival recombRate tSource := by
    unfold discreteRecombinationSurvival
    exact pow_pos h_base_pos _
  have h_decay_lt_one :
      discreteRecombinationSurvival recombRate (tTarget - tSource) < 1 := by
    unfold discreteRecombinationSurvival
    exact pow_lt_one₀ h_base_nonneg h_base_lt_one h_delta_ne
  have h_tail_pos :
      0 < 1 - discreteRecombinationSurvival recombRate (tTarget - tSource) := by
    linarith
  have h_inner_pos :
      0 <
        ibdWeight * discreteRecombinationSurvival recombRate tSource *
          (1 - discreteRecombinationSurvival recombRate (tTarget - tSource)) := by
    exact mul_pos (mul_pos h_ibd_pos h_survival_pos) h_tail_pos
  have h_lb_pos :
      0 <
        2 *
          (ibdWeight * discreteRecombinationSurvival recombRate tSource *
            (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 := by
    have h_sq_pos :
        0 <
          (ibdWeight * discreteRecombinationSurvival recombRate tSource *
            (1 - discreteRecombinationSurvival recombRate (tTarget - tSource))) ^ 2 :=
      sq_pos_of_ne_zero h_inner_pos.ne'
    nlinarith
  exact lt_of_lt_of_le h_lb_pos h_gap_lb

/-- End-to-end portability drop under a two-locus coalescent witness:
once source-trained ERM incurs target excess MSE proportional to covariance mismatch,
an increase in expected MRCA time in the target population forces `R²_target < R²_source`. -/
theorem target_r2_drop_of_twoLocusCoalescent
    {t : ℕ} (ht : 2 ≤ t)
    (mseSource mseTarget varY lam : ℝ)
    (ibdWeight recombRate : ℝ)
    (tSource tTarget : ℕ)
    (h_mse_gap_lb :
      lam *
          frobeniusNormSq
            (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource -
              twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget) ≤
        mseTarget - mseSource)
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_ibd_pos : 0 < ibdWeight)
    (h_recomb_pos : 0 < recombRate)
    (h_recomb_lt_one : recombRate < 1)
    (h_time : tSource < tTarget) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY := by
  have h_mismatch :
      0 <
        frobeniusNormSq
          (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource -
            twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget) :=
    covariance_mismatch_pos_of_twoLocusCoalescent
      ht ibdWeight recombRate tSource tTarget
      h_ibd_pos h_recomb_pos h_recomb_lt_one h_time
  exact target_r2_strictly_decreases_of_covariance_mismatch
    mseSource mseTarget varY lam
    (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tSource)
    (twoLocusCoalescentCovarianceMatrix ht ibdWeight recombRate tTarget)
    h_mse_gap_lb h_lam_pos h_mismatch h_varY_pos

/-- If the demographic lower bound is available and strictly positive, covariance mismatch is
    strict. -/
theorem covariance_mismatch_pos_of_fst_and_sparse_array
    {t : ℕ}
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    0 < frobeniusNormSq (sigmaSource - sigmaTarget) := by
  have h_scale_pos : 0 < taggingMismatchScale recombRate arraySparsity := by
    unfold taggingMismatchScale
    exact mul_pos h_recomb_pos h_sparse_pos
  have h_delta_pos : 0 < fstTarget - fstSource := sub_pos.mpr h_fst
  have h_lb_pos :
      0 < demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity
            kappa := by
    unfold demographicCovarianceGapLowerBound
    exact mul_pos (mul_pos h_kappa_pos h_scale_pos) h_delta_pos
  exact lt_of_lt_of_le h_lb_pos h_cov_lb

/-- End-to-end portability drop from any demographic covariance lower bound. -/
theorem target_r2_drop_of_fst_and_sparse_array
    {t : ℕ}
    (mseSource mseTarget varY lam : ℝ)
    (sigmaSource sigmaTarget : Matrix (Fin t) (Fin t) ℝ)
    (fstSource fstTarget recombRate arraySparsity kappa : ℝ)
    (h_mse_gap_lb :
      lam * frobeniusNormSq (sigmaSource - sigmaTarget) ≤ mseTarget - mseSource)
    (h_cov_lb :
      demographicCovarianceGapLowerBound fstSource fstTarget recombRate arraySparsity kappa
        ≤ frobeniusNormSq (sigmaSource - sigmaTarget))
    (h_lam_pos : 0 < lam)
    (h_varY_pos : 0 < varY)
    (h_fst : fstSource < fstTarget)
    (h_recomb_pos : 0 < recombRate)
    (h_sparse_pos : 0 < arraySparsity)
    (h_kappa_pos : 0 < kappa) :
    r2FromMSE mseTarget varY < r2FromMSE mseSource varY := by
  have h_mismatch : 0 < frobeniusNormSq (sigmaSource - sigmaTarget) :=
    covariance_mismatch_pos_of_fst_and_sparse_array
      sigmaSource sigmaTarget fstSource fstTarget recombRate arraySparsity kappa
      h_cov_lb h_fst h_recomb_pos h_sparse_pos h_kappa_pos
  exact target_r2_strictly_decreases_of_covariance_mismatch
    mseSource mseTarget varY lam sigmaSource sigmaTarget
    h_mse_gap_lb h_lam_pos h_mismatch h_varY_pos

/-! ### Step 4b: the same conclusion without an `F_ST` difference

**The defect in Step 4, measured rather than suspected.**
`demographicCovarianceGapLowerBound` is `kappa * recombRate * arraySparsity *
(fstTarget - fstSource)`. It reads the *difference* of two divergences. For two
populations that split from one ancestor and drifted equally — the generic split, and
exactly the configuration ancestry-specific LD results are about — `fstSource =
fstTarget`, so the bound is identically zero and the hypothesis `h_fst : fstSource <
fstTarget` of both theorems above is **false**. Over simulated configurations of that
kind the squared Frobenius LD mismatch ranged from 2.554 to 7.346 while this bound sat
at zero. The two theorems are true and inapplicable in the case that matters: they can
certify a portability drop only when one population is *more* diverged than the other,
which is not what equal drift from a shared ancestor produces.

**What replaces it.** The missing ingredient is a positivity certificate that reads the
correlation structure rather than a divergence difference.
`Calibrator.SpectralDegradation.FiniteSpectralModel.degradation_eq_zero_iff` is exactly
that: transport costs nothing **if and only if** the source and target optimal readouts
`c/sigma` agree in every frequency band. So a single band of readout disagreement forces
strictly positive excess target risk, with no reference to `F_ST`, to array sparsity, or
to any recombination scale — and in particular the certificate is available at
`fstSource = fstTarget`, where Step 4 has nothing to say.

Note precisely what has and has not been transferred. Step 4 bounds
`frobeniusNormSq (sigmaSource - sigmaTarget)`, a distance between covariance matrices,
and then converts it to risk through the *assumed* inequality `h_mse_gap_lb`. Step 4b
does not need that assumed conversion, because `degradation` is already defined as excess
target risk: `risk target (optimalReadout source) - risk target (optimalReadout target)`.
The price is that the object is a finite band model rather than a covariance matrix, so
this is not a strengthening of Step 4 in Step 4's own coordinates — it is a different and
non-vacuous route to the same biological conclusion.
-/

/-- **Excess target risk is strictly positive as soon as one band's optimal readout
disagrees** — no `F_ST` difference, no tagging scale, no sparsity.

This is the equal-divergence replacement for `covariance_mismatch_pos_of_fst_and_sparse_array`.
It is not provable in this file: its content is
`FiniteSpectralModel.degradation_eq_zero_iff`, whose proof is the bandwise sum identity
`degradation = sum_b (readout gap)^2 * targetSpectrum`, and nothing in the demographic
machinery here produces it. -/
theorem excess_target_risk_pos_of_bandwise_readout_mismatch
    {Band : Type*} [Fintype Band] (source target : FiniteSpectralModel Band) (b : Band)
    (hb : FiniteSpectralModel.optimalReadout source b ≠
      FiniteSpectralModel.optimalReadout target b) :
    0 < FiniteSpectralModel.degradation source target := by
  rcases lt_or_eq_of_le (FiniteSpectralModel.degradation_nonneg source target) with hlt | heq
  · exact hlt
  · exact absurd ((FiniteSpectralModel.degradation_eq_zero_iff source target).mp heq.symm b) hb

/-- **End-to-end `R²` drop from a single band of readout mismatch.**

The Step 4 conclusion — `R²_target < R²_source` — reached with the `F_ST`-difference
hypothesis deleted rather than assumed. The comparison is between the transported
source-optimal readout and the refitted target-optimal readout, both evaluated on the
target, which is the transfer comparison a deployment actually makes.

Deleting `Calibrator.SpectralDegradation` breaks this theorem:
`excess_target_risk_pos_of_bandwise_readout_mismatch`
is its only source of strict positivity, and that in turn is
`degradation_eq_zero_iff`. -/
theorem target_r2_drop_of_bandwise_readout_mismatch
    {Band : Type*} [Fintype Band] (source target : FiniteSpectralModel Band) (b : Band)
    (varY : ℝ)
    (hb : FiniteSpectralModel.optimalReadout source b ≠
      FiniteSpectralModel.optimalReadout target b)
    (h_varY_pos : 0 < varY) :
    r2FromMSE
        (FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout source)) varY <
      r2FromMSE
        (FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout target)) varY := by
  have hpos := excess_target_risk_pos_of_bandwise_readout_mismatch source target b hb
  unfold FiniteSpectralModel.degradation at hpos
  have hlt :
      FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout target) <
        FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout source) := by
    linarith
  unfold r2FromMSE
  have h_inv_pos : 0 < (1 / varY) := one_div_pos.mpr h_varY_pos
  have hdiv :
      FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout target) / varY <
        FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout source) / varY := by
    have hmul :
        FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout target) *
            (1 / varY) <
          FiniteSpectralModel.risk target (FiniteSpectralModel.optimalReadout source) *
            (1 / varY) :=
      mul_lt_mul_of_pos_right hlt h_inv_pos
    simpa [div_eq_mul_inv] using hmul
  linarith

/-! ### Example Scenario DGPs (Specific Instantiations)

The following are **example instantiations** of `dgpAdditiveBias` with specific β values
from simulation studies. For general proofs, use `dgpAdditiveBias` with arbitrary β. -/

/-- General interaction-bias DGP:
    phenotype = P * (1 + β_int * Σ C). -/
noncomputable def dgpInteractiveBias (k : ℕ) [Fintype (Fin k)] (β_int :
    ℝ) : DataGeneratingProcess k := {
  trueExpectation := fun p pc ↦ p * (1 + β_int * (∑ l, pc l)),
  jointMeasure := stdNormalProdMeasure k
}

/-! ### Generalized DGP and L² Projection Framework

The following definitions support a cleaner, more general proof approach:
- Instead of hardcoding constants like 0.8, we parameterize by β_env
- We view least-squares optimization as orthogonal projection in L²
- This unifies Scenario 3 (β > 0) and Scenario 4 (β < 0) -/

/-- General DGP where phenotype is P + β_env * Σ C.
    This generalizes Scenario 3 (β > 0) and Scenario 4 (β < 0).

    The key insight: the raw model (span{1, P}) cannot capture the β_env * C term,
    so the projection leaves a residual of exactly β_env * C. -/
noncomputable def dgpAdditiveBias (k : ℕ) [Fintype (Fin k)] (β_env : ℝ) : DataGeneratingProcess k :=
  {
  trueExpectation := fun p pc ↦ p + β_env * (∑ l, pc l),
  jointMeasure := stdNormalProdMeasure k
}

def hasInteraction {k : ℕ} [Fintype (Fin k)] (f : ℝ → (Fin k → ℝ) → ℝ) : Prop :=
  ∃ (p₁ p₂ : ℝ) (c₁ c₂ : Fin k → ℝ), p₁ ≠ p₂ ∧ c₁ ≠ c₂ ∧
    (f p₂ c₁ - f p₁ c₁) / (p₂ - p₁) ≠ (f p₂ c₂ - f p₁ c₂) / (p₂ - p₁)

theorem scenarios_are_distinct (k : ℕ) (hk_pos : 0 < k) :
  hasInteraction (dgpInteractiveBias k 0.1).trueExpectation ∧
  ¬ hasInteraction (dgpAdditiveBias k 0.5).trueExpectation ∧
  ¬ hasInteraction (dgpAdditiveBias k (-0.8)).trueExpectation := by
  constructor
  · -- Case 1: dgpInteractiveBias with β_int = 0.1 has interaction
    unfold hasInteraction
    -- We provide witnesses for p₁, p₂, c₁, and c₂.
    -- p₁ and p₂ are real numbers. c₁ and c₂ are functions from Fin k to ℝ.
    use 0, 1, (fun _ ↦ 0), (fun i ↦ if i = ⟨0, hk_pos⟩ then 1 else 0)
    constructor; · norm_num -- Proves p₁ ≠ p₂
    constructor
    · -- Proves c₁ ≠ c₂ for any k > 0, including k=1
      intro h_eq
      -- If the functions are equal, they must be equal at the point ⟨0, hk_pos⟩.
      -- We use `congr_fun` to apply this equality.
      have := congr_fun h_eq ⟨0, hk_pos⟩
      -- This simplifies to 0 = 1, a contradiction.
      simp at this
    · -- Proves the inequality
      unfold dgpInteractiveBias; dsimp
      have h_sum_c2 : (∑ (l : Fin k), if l = ⟨0, hk_pos⟩ then 1 else 0) = 1 := by
        -- The sum is 1 because the term is 1 only at i = ⟨0, hk_pos⟩ and 0 otherwise.
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      -- Substitute the sum and simplify the expression
      simp [Finset.sum_const_zero]; norm_num
  · constructor
    · -- Case 2: additive-bias DGP with β = 0.5 has no interaction
      intro h; rcases h with ⟨p₁, p₂, c₁, c₂, hp_neq, _, h_neq⟩
      unfold dgpAdditiveBias at h_neq
      -- The terms with c₁ and c₂ cancel out, making the slope independent of c.
      simp only [add_sub_add_right_eq_sub] at h_neq
      -- This leads to 1 ≠ 1, a contradiction.
      contradiction
    · -- Case 3: additive-bias DGP with β = -0.8 has no interaction
      intro h; rcases h with ⟨p₁, p₂, c₁, c₂, hp_neq, _, h_neq⟩
      unfold dgpAdditiveBias at h_neq
      -- Similarly, the terms with c₁ and c₂ cancel out.
      simp only [add_sub_add_right_eq_sub] at h_neq
      -- This leads to 1 ≠ 1, a contradiction.
      contradiction

theorem necessity_of_phenotype_data :
  ∃ (dgp_A dgp_B : DataGeneratingProcess 1),
    dgp_A.jointMeasure = dgp_B.jointMeasure ∧ hasInteraction dgp_A.trueExpectation ∧
      ¬ hasInteraction dgp_B.trueExpectation := by
  use dgpInteractiveBias 1 0.1, dgpAdditiveBias 1 (-0.8)
  constructor; rfl
  have h_distinct := scenarios_are_distinct 1 (by norm_num)
  exact ⟨h_distinct.left, h_distinct.right.right⟩

/-! ### Population Structure: Drift and LD Decay (Abstract Form)

These statements avoid tying the math to a specific demographic model (e.g., admixture).
They capture the two essential mechanisms:
1) drift can change genic variance across PC space
2) LD decay reduces tagging efficiency with genetic distance
-/


/-! ### Linear Noise ⇒ Nonlinear Optimal Slope

If error variance increases linearly with ancestry distance, the optimal slope
is a reciprocal (hyperbolic) function. No linear function can match it everywhere
unless the noise slope is zero. -/

noncomputable def optimalSlopeLinearNoise (sigma_g_sq base_error slope_error c : ℝ) : ℝ :=
  sigma_g_sq / (sigma_g_sq + base_error + slope_error * c)

/-- **optimalSlopeLinearNoise where its denominator vanishes, named.** The guard `sigma_g_sq +
base_error + slope_error * c` is zero at `sigma_g_sq = 0`, `base_error = 0`, `slope_error = 0`,
`c = 0`. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `sigma_g_sq + base_error + slope_error * c ≠ 0`. -/
theorem optimalSlopeLinearNoise_at_sigmagsq0baseerror0slopeer_is_junk :
    optimalSlopeLinearNoise 0 0 0 0 = 0 := by
  unfold optimalSlopeLinearNoise
  norm_num

/-- **The slope recovers the signal from the total variance.** -/
theorem optimalSlopeLinearNoise_mul_total (sigma_g_sq base_error slope_error c : ℝ)
    (h : sigma_g_sq + base_error + slope_error * c ≠ 0) :
    optimalSlopeLinearNoise sigma_g_sq base_error slope_error c
      * (sigma_g_sq + base_error + slope_error * c) = sigma_g_sq := by
  unfold optimalSlopeLinearNoise
  field_simp

theorem linear_noise_implies_nonlinear_slope
    (sigma_g_sq base_error slope_error : ℝ)
    (h_g_pos : 0 < sigma_g_sq)
    (hB_pos : 0 < sigma_g_sq + base_error)
    (hB1_pos : 0 < sigma_g_sq + base_error + slope_error)
    (hB2_pos : 0 < sigma_g_sq + base_error + 2 * slope_error)
    (h_slope_ne : slope_error ≠ 0) :
    ∀ (beta0 beta1 : ℝ),
      (fun c ↦ beta0 + beta1 * c) ≠
        (fun c ↦ optimalSlopeLinearNoise sigma_g_sq base_error slope_error c) := by
  intro beta0 beta1 h_eq
  have h0 := congr_fun h_eq 0
  have h1 := congr_fun h_eq 1
  have h2 := congr_fun h_eq 2
  dsimp [optimalSlopeLinearNoise] at h0 h1 h2

  -- Simplify the equations
  simp only [mul_zero, add_zero, zero_mul, mul_one] at h0 h1
  have h2 : beta0 + 2 * beta1 = sigma_g_sq / (sigma_g_sq + base_error + slope_error * 2) := by
    convert h2 using 1
    ring

  -- Define abbreviations to simplify algebra
  set K := sigma_g_sq
  set A := sigma_g_sq + base_error
  set S := slope_error

  -- Non-zero denominators
  have h_ne_K : K ≠ 0 := h_g_pos.ne'
  have h_ne_A : A ≠ 0 := hB_pos.ne'
  have h_ne_AS : A + S ≠ 0 := hB1_pos.ne'
  have h_ne_A2S : A + 2 * S ≠ 0 := hB2_pos.ne'

  -- Rewrite hypotheses in terms of K, A, S
  have h0' : beta0 * A = K := by
    rw [h0]
    field_simp [h_ne_A]
  have h1' : (beta0 + beta1) * (A + S) = K := by
    rw [h1]
    field_simp [h_ne_AS]

  have h_denom2 : sigma_g_sq + base_error + slope_error * 2 = A + 2 * S := by ring
  rw [h_denom2] at h2

  have h2' : (beta0 + 2 * beta1) * (A + 2 * S) = K := by
    rw [h2]
    field_simp [h_ne_A2S]

  -- Derived equations for 1/K * beta terms
  have h_inv0 : 1 / A = beta0 / K := by
    field_simp [h_ne_K, h_ne_A]
    rw [← h0']
    field_simp [h_ne_K, h_ne_A]
  have h_inv1 : 1 / (A + S) = (beta0 + beta1) / K := by
    field_simp [h_ne_K, h_ne_AS]
    rw [← h1']
    field_simp [h_ne_K, h_ne_AS]
  have h_inv2 : 1 / (A + 2 * S) = (beta0 + 2 * beta1) / K := by
    field_simp [h_ne_K, h_ne_A2S]
    rw [← h2']
    field_simp [h_ne_K, h_ne_A2S]

  -- Check the identity: 1/(A) + 1/(A+2S) = 2/(A+S)
  have h_identity : 1 / A + 1 / (A + 2 * S) = 2 / (A + S) := by
    rw [h_inv0, h_inv2, div_eq_mul_one_div 2 (A + S), h_inv1]
    ring

  have h_S_zero : S = 0 := by
    field_simp [h_ne_A, h_ne_A2S, h_ne_AS] at h_identity
    nlinarith [h_identity]

  contradiction

/-! ### Generalized Population Structure (No Admixture Assumption)

We model population structure via an ancestry-indexed LD environment Σ(C),
and decompose genetic variance into genic (diagonal) and covariance (off-diagonal)
components. This captures admixture, divergence, and drift uniformly. -/

structure GeneticArchitecture (k : ℕ) where
  /-- Genic variance (as if loci were independent). -/
  V_genic : (Fin k → ℝ) → ℝ
  /-- Structural covariance / LD contribution. -/
  V_cov : (Fin k → ℝ) → ℝ
  /-- Selection effect (positive = divergent, negative = stabilizing). -/
  selection_effect : (Fin k → ℝ) → ℝ

noncomputable def totalVariance {k : ℕ} (arch : GeneticArchitecture k) (c : Fin k → ℝ) : ℝ :=
  arch.V_genic c + arch.V_cov c

noncomputable def optimalSlopeFromVariance {k : ℕ} (arch : GeneticArchitecture k) (c : Fin k →
    ℝ) : ℝ :=
  (totalVariance arch c) / (arch.V_genic c)

theorem directionalLD_nonzero_implies_slope_ne_one {k : ℕ} [Fintype (Fin k)]
    (arch : GeneticArchitecture k) (c : Fin k → ℝ)
    (h_genic_pos : arch.V_genic c ≠ 0)
    (h_cov_ne : arch.V_cov c ≠ 0) :
    optimalSlopeFromVariance arch c ≠ 1 := by
  unfold optimalSlopeFromVariance totalVariance
  intro h
  rw [add_div, div_self h_genic_pos] at h
  have : arch.V_cov c / arch.V_genic c = 0 := by linarith
  simp [div_eq_zero_iff, h_genic_pos] at this
  contradiction

/-! ### The reciprocal optimal slope is not affine

Under the *linear noise model* `optimalSlopeLinearNoise`, and only under it, the optimal slope
is a reciprocal function of `c` and so is matched by no affine function.  The name
`ld_decay_implies_nonlinear_calibration` is absent here on purpose: it asserts LD decay as
the mechanism, and neither LD, distance nor decay appears in the statement, which is a
hypothesis-weakening
wrapper for `linear_noise_implies_nonlinear_slope` with the positivity side conditions
discharged from nonnegativity.  The LD-decay statement that *is* proved is
`Calibrator.ld_decay_implies_nonlinear_calibration_of_exp_tagging` in the corpus root, which
supplies
three explicit distances through an `LDDecayMechanism`. -/

theorem optimalSlopeLinearNoise_not_affine_of_nonneg_errors
    (sigma_g_sq base_error slope_error : ℝ)
    (h_g_pos : 0 < sigma_g_sq)
    (h_base : 0 ≤ base_error)
    (h_slope_pos : 0 ≤ slope_error)
    (h_slope_ne : slope_error ≠ 0) :
    ∀ (beta0 beta1 : ℝ),
      (fun c ↦ beta0 + beta1 * c) ≠
        (fun c ↦ optimalSlopeLinearNoise sigma_g_sq base_error slope_error c) := by
  apply linear_noise_implies_nonlinear_slope sigma_g_sq base_error slope_error
  · exact h_g_pos
  · apply add_pos_of_pos_of_nonneg h_g_pos h_base
  · apply add_pos_of_pos_of_nonneg
    · apply add_pos_of_pos_of_nonneg h_g_pos h_base
    · exact h_slope_pos
  · apply add_pos_of_pos_of_nonneg
    · apply add_pos_of_pos_of_nonneg h_g_pos h_base
    · apply mul_nonneg zero_le_two h_slope_pos
  · exact h_slope_ne

/-! ### Positive structural covariance puts the optimal slope above one

This says exactly `(a + b)/a > 1` for `a, b > 0`, read through
`optimalSlopeFromVariance`.  It was called `normalization_erases_heritability` under a
section header asserting that "normalization forces `Var(P|C) = 1`, which removes the LD
covariance term": no normalization operation, no heritability and no `Var(P|C)` constraint
occurs in the statement or anywhere else in this file, so that mechanism was prose only. -/

theorem optimalSlopeFromVariance_gt_one_of_cov_pos {k : ℕ} [Fintype (Fin k)]
    (arch : GeneticArchitecture k) (c : Fin k → ℝ)
    (h_genic_pos : arch.V_genic c > 0)
    (h_cov_pos : arch.V_cov c > 0) :
    optimalSlopeFromVariance arch c > 1 := by
  unfold optimalSlopeFromVariance totalVariance
  rw [add_div, div_self (h_genic_pos.ne')]
  rw [gt_iff_lt, lt_add_iff_pos_right]
  apply div_pos h_cov_pos h_genic_pos

/-! ### Neutral Score Drift (Artifactual Mean Shift in P)

The score drifts with ancestry while true liability does not.
The calibrator must subtract the drift term (PC main effects). -/


/-! ### Normalization-Prevalence Bias (Cross-Ancestry Calibration)

**Key Insight**: When a PGS is normalized (mean-centered across ancestries) and then
calibrated to produce risk predictions, the normalization step implicitly assumes equal
disease prevalence across ancestry groups. If prevalences actually differ, the calibrated
predictions are biased toward the prevalence of the majority training population.

**Mathematical formulation**: Consider ancestry groups indexed by c ∈ Fin k → ℝ with
ancestry-specific disease prevalence π(c). Normalization forces E[score | c] = constant
for all c, but the true conditional risk E[Y | P, C=c] depends on π(c). The residual
bias after normalization is exactly (π(c) - π̄), where π̄ is the population-average
prevalence (weighted by the training distribution).

This section formalizes the claim that normalization *cannot* recover ancestry-specific
prevalence even with perfect PGS, because the prevalence information is projected out
by the mean-centering step. -/

/-- Ancestry-specific prevalence model: the true risk depends on both the PGS
    and the ancestry-specific baseline disease prevalence. -/
structure PrevalenceDGP (k : ℕ) where
  /-- Ancestry-specific baseline prevalence (probability scale). -/
  prevalence : (Fin k → ℝ) → ℝ
  /-- PGS effect (log-odds-ratio per unit PGS, ancestry-invariant). -/
  pgs_effect : ℝ
  /-- The joint measure on (PGS, Ancestry). -/
  jointMeasure : Measure (ℝ × (Fin k → ℝ))
  is_prob : IsProbabilityMeasure jointMeasure := by infer_instance

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def PrevalenceDGP.witness (k : ℕ) : PrevalenceDGP k where
  prevalence := fun _ ↦ 0
  pgs_effect := 0
  jointMeasure := Measure.dirac 0

/-- True conditional risk under a prevalence DGP (identity link, additive form).
    E[Y | P, C] = π(C) + β · P, where π varies by ancestry and β is shared.

    Empirical status: UNTESTED. -/
noncomputable def prevalenceDGP_trueExpectation {k : ℕ} (pdgp : PrevalenceDGP k)
    (p : ℝ) (c : Fin k → ℝ) : ℝ :=
  pdgp.prevalence c + pdgp.pgs_effect * p

/-- Convert a PrevalenceDGP to a standard DataGeneratingProcess. -/
noncomputable def PrevalenceDGP.toDGP {k : ℕ} (pdgp : PrevalenceDGP
    k) : DataGeneratingProcess k where
  trueExpectation := prevalenceDGP_trueExpectation pdgp
  jointMeasure := pdgp.jointMeasure
  is_prob := pdgp.is_prob

/-- **Normalization-Prevalence Bias Theorem**:

    If the true risk is E[Y|P,C] = π(C) + β·P where π varies by ancestry, but a
    normalized predictor uses a single intercept π̄ (population-average prevalence),
    then the prediction error at ancestry C is exactly (π(C) - π̄).

    In other words, normalization "bakes in" the assumption of equal prevalence.
    The calibrated predictions will be systematically:
    - Too high for ancestry groups with π(C) < π̄ (over-prediction)
    - Too low for ancestry groups with π(C) > π̄ (under-prediction)

    This is the mathematical basis for why mean-centering PGS across ancestries
    produces biased risk estimates when disease prevalences differ.

    **Both former hypotheses are gone, and the statement is stronger for it.**
    `_h_pi_bar` pinned `π̄` to the training-distribution average of `π`; it was
    already dead (note the underscore) and the identity holds for *any* centering
    constant, which is the sharper reading — no choice of single intercept
    escapes the residual `π(C) - π̄`.  `f_norm` plus `h_norm` was a free function
    together with an equation defining it pointwise; since `h_norm` determines
    `f_norm` at every argument, quantifying over such an `f_norm` says exactly
    what naming the predictor inline says, while making the caller supply the
    definition. -/
theorem normalization_prevalence_bias {k : ℕ} [Fintype (Fin k)]
    (pdgp : PrevalenceDGP k)
    (pi_bar : ℝ) :
    ∀ p c, prevalenceDGP_trueExpectation pdgp p c -
        (pi_bar + pdgp.pgs_effect * p) =
      pdgp.prevalence c - pi_bar := by
  intro p c
  unfold prevalenceDGP_trueExpectation
  ring

/-- Corollary: The MSE of the normalized predictor decomposes into a pure
    prevalence-mismatch term. If π is constant across ancestries, normalization
    incurs zero bias. Otherwise, the bias equals Var(π(C)) under the measure.

    Stated for an arbitrary intercept `π̄` for the same reason as
    `normalization_prevalence_bias`: nothing in the proof used the assumption
    that `π̄` was the training-distribution average. -/
theorem normalization_prevalence_mse {k : ℕ} [Fintype (Fin k)]
    (pdgp : PrevalenceDGP k)
    (pi_bar : ℝ) :
    mseRisk pdgp.toDGP (fun p _ ↦ pi_bar + pdgp.pgs_effect * p) =
      ∫ pc, (pdgp.prevalence pc.2 - pi_bar)^2 ∂pdgp.jointMeasure := by
  unfold mseRisk PrevalenceDGP.toDGP
  simp only
  congr 1; ext pc
  rw [normalization_prevalence_bias pdgp pi_bar pc.1 pc.2]

/-- **No-bias condition**: If prevalence is constant across ancestries (π(c) = π₀ for all c),
    then normalization introduces zero bias. This characterizes when normalization is safe. -/
theorem normalization_no_bias_iff_constant_prevalence {k : ℕ} [Fintype (Fin k)]
    (pdgp : PrevalenceDGP k) (π₀ : ℝ)
    (h_const : ∀ c, pdgp.prevalence c = π₀) :
    ∀ p c, prevalenceDGP_trueExpectation pdgp p c - (π₀ + pdgp.pgs_effect * p) = 0 := by
  intro p c
  simp [prevalenceDGP_trueExpectation, h_const c]

/-! ### Biological → Statistical Bridges

These structures connect biological mechanisms to statistical DGPs and to the
need for nonlinear calibration. The consequence for calibration is proved in
`Calibrator.ld_decay_implies_nonlinear_calibration_of_exp_tagging`, which exhibits three
explicit distances rather than assuming non-affineness as a hypothesis.

**THIS CITATION IS LOAD-BEARING AND IT CROSSES A DIRECTORY BOUNDARY.** The consumer named
above lives in `proofs/Calibrator.lean` -- the corpus ROOT, one level *above*
`proofs/Calibrator/`. A dead-code scan that walks only `proofs/Calibrator/` cannot see it,
and on 2026-02 exactly that happened: `decaySlope` was deleted as having "no use anywhere
and no theorem about them", and `LDDecayMechanism` was then deleted as having "lost its
only consumer". Both premises were false and the second inherited the first's error.

The deletion did NOT break the build, which is the part to remember. Lean auto-binds an
undefined bare name as an implicit variable, so the consuming theorem kept elaborating --
as a vacuous statement over an arbitrary term of unknown type -- and stayed green. For
this class of name the build cannot detect the breakage at all, so **absence of a build
failure is not evidence that a deletion was safe.** Grep the prose, not just the
identifier: this paragraph named the consumer the whole time. -/

/-- Exponential LD-decay mechanism: a distance proxy and a tagging efficiency.

**DO NOT DELETE AS UNUSED.** Its consumer is
`Calibrator.ld_decay_implies_nonlinear_calibration_of_exp_tagging`, which lives in
`proofs/Calibrator.lean` — the corpus ROOT, one directory *above* `proofs/Calibrator/`.
A dead-code scan that walks only `proofs/Calibrator/` reports this and `decaySlope` as
having no consumer, because the root file is outside that directory. Deleting them does
not break the build either, because Lean **auto-binds the now-undefined names as implicit
variables**, so the consuming theorem keeps elaborating as a vacuous statement about an
arbitrary term until an application finally forces the error. Absence of a build failure
is therefore not evidence that a deletion here is safe. -/
structure LDDecayMechanism (k : ℕ) where
  /-- Genetic distance proxy (e.g., PC-distance from training centroid). -/
  distance : (Fin k → ℝ) → ℝ
  /-- Tagging efficiency ρ² decreases with distance. -/
  tagging_efficiency : ℝ → ℝ

/-- Tagging efficiency as a function of the genetic distance of `c`.

**DO NOT DELETE AS UNUSED** — see the note on `LDDecayMechanism` above. This is the
function that `ld_decay_implies_nonlinear_calibration_of_exp_tagging` shows is not affine. -/
def decaySlope {k : ℕ} (mech : LDDecayMechanism k) (c : Fin k → ℝ) : ℝ :=
  mech.tagging_efficiency (mech.distance c)

theorem optimal_slope_trace_variance {k : ℕ} [Fintype (Fin k)]
    (arch : GeneticArchitecture k) (c : Fin k → ℝ)
    (h_genic_pos : arch.V_genic c ≠ 0) :
    optimalSlopeFromVariance arch c =
      1 + (arch.V_cov c) / (arch.V_genic c) := by
  unfold optimalSlopeFromVariance totalVariance
  rw [add_div, div_self h_genic_pos]

noncomputable def var {k : ℕ} [Fintype (Fin k)] (dgp : DataGeneratingProcess k)
    (f : ℝ → (Fin k → ℝ) → ℝ) : ℝ :=
  let μ := dgp.jointMeasure
  let m : ℝ := ∫ pc, f pc.1 pc.2 ∂μ
  ∫ pc, (f pc.1 pc.2 - m) ^ 2 ∂μ

noncomputable def rsquared {k : ℕ} [Fintype (Fin k)] (dgp : DataGeneratingProcess k)
    (f g : ℝ → (Fin k → ℝ) → ℝ) : ℝ :=
  let μ := dgp.jointMeasure
  let mf : ℝ := ∫ pc, f pc.1 pc.2 ∂μ
  let mg : ℝ := ∫ pc, g pc.1 pc.2 ∂μ
  let vf : ℝ := ∫ pc, (f pc.1 pc.2 - mf) ^ 2 ∂μ
  let vg : ℝ := ∫ pc, (g pc.1 pc.2 - mg) ^ 2 ∂μ
  let cov : ℝ := ∫ pc, (f pc.1 pc.2 - mf) * (g pc.1 pc.2 - mg) ∂μ
  if vf = 0 ∨ vg = 0 then 0 else (cov ^ 2) / (vf * vg)

/-! ### Exact Measure-Level Metric Identities

This section instantiates the transport and metric algebra on an actual
probability measure. Unlike `TransportIdentities.lean`, these theorems are
proved directly with `MeasureTheory.integral` and can therefore be used inside
the concrete biological DGPs without any abstract expectation wrapper.
-/

section ExactMeasureMetricIdentities

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact mean of a real observable under a concrete probability measure. -/
noncomputable def measureMean (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  ∫ ω, Z ω ∂μ

/-- Exact variance under a concrete probability measure. -/
noncomputable def measureVariance (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  ∫ ω, (Z ω - measureMean μ Z) ^ 2 ∂μ

/-- Exact covariance under a concrete probability measure. -/
noncomputable def measureCovariance (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - measureMean μ X) * (Y ω - measureMean μ Y) ∂μ

/-- Exact mean squared prediction error under a concrete probability measure. -/
noncomputable def measureExpMSE (μ : Measure Ω) (Y S : Ω → ℝ) : ℝ :=
  ∫ ω, (Y ω - S ω) ^ 2 ∂μ

/-- Exact bias of a predictor under a concrete probability measure. -/
noncomputable def measureBias (μ : Measure Ω) (Y S : Ω → ℝ) : ℝ :=
  measureMean μ S - measureMean μ Y

end ExactMeasureMetricIdentities

/-! ### Reading a data-generating process at the second-moment level

Almost every closed form in this development is a function of three numbers: the variance
of the signal, the variance of the outcome, and their covariance. Those numbers are
*stipulated* wherever the closed forms are used — `V_A`, `V_E` and `fst` arrive as bare
reals — and nothing connects them to a probability measure. That is why an algebraic
identity between them can be proved without establishing anything about a data-generating
process.

A former `MomentReading` structure stored these equalities as fields.  That made the caller
supply the very bridge being advertised.  The quantities below are now definitions of the
process moments themselves. -/

section MomentReadings

/-- Variance of a predictor under a concrete DGP. -/
noncomputable def signalVariance {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k) (signal : Predictor k) : ℝ :=
  var dgp signal

/-- Variance of the DGP's conditional-mean outcome. -/
noncomputable def outcomeMeanVariance {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k) : ℝ :=
  var dgp dgp.trueExpectation

/-- Covariance of a predictor with the DGP's conditional-mean outcome. -/
noncomputable def signalOutcomeCovariance {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k) (signal : Predictor k) : ℝ :=
  measureCovariance dgp.jointMeasure
    (fun pc ↦ signal pc.1 pc.2) (fun pc ↦ dgp.trueExpectation pc.1 pc.2)

/-- **The statistical `R²` of a reading is the squared correlation of its three moments.**

This is what makes the reading useful: `rsquared` — an integral expression — is a rational
function of three reals, and every algebraic identity about those reals becomes a
statement about the process.

**The two nondegeneracy premises are gone, and nothing was weakened to remove them.**
They used to read `signalVariance ≠ 0` and `outcomeMeanVariance ≠ 0`, and they were
supplied by the caller as facts about quantities this file defines. They were never
needed: `rsquared` returns `0` by its own guard exactly when one of those variances
vanishes, and in that same case the right-hand side has a zero factor in its denominator,
so it is `0` too — division by zero in Lean is `0`, and here that convention makes the two
sides agree rather than papering over a gap. The identity is therefore unconditional, and
the degenerate case is not an exception to it but an instance of it. -/
theorem rsquared_eq_process_moments {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k) (signal : Predictor k) :
    rsquared dgp signal dgp.trueExpectation =
      signalOutcomeCovariance dgp signal ^ 2 /
        (signalVariance dgp signal * outcomeMeanVariance dgp) := by
  by_cases h : signalVariance dgp signal = 0 ∨ outcomeMeanVariance dgp = 0
  · have hzero : signalVariance dgp signal * outcomeMeanVariance dgp = 0 := by
      rcases h with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    unfold rsquared
    change
      (if signalVariance dgp signal = 0 ∨ outcomeMeanVariance dgp = 0 then 0
        else signalOutcomeCovariance dgp signal ^ 2 /
          (signalVariance dgp signal * outcomeMeanVariance dgp)) = _
    rw [if_pos h, hzero, div_zero]
  · unfold rsquared
    change
      (if signalVariance dgp signal = 0 ∨ outcomeMeanVariance dgp = 0 then 0
        else signalOutcomeCovariance dgp signal ^ 2 /
          (signalVariance dgp signal * outcomeMeanVariance dgp)) = _
    rw [if_neg h]

end MomentReadings

section ExactMeasureMetricIdentities

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measureVariance_eq_expect_sq_sub_sq_mean
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ)
    (hZ_int : Integrable Z μ)
    (hZsq_int : Integrable (fun ω ↦ Z ω ^ 2) μ) :
    measureVariance μ Z = (∫ ω, Z ω ^ 2 ∂μ) - (measureMean μ Z) ^ 2 := by
  unfold measureVariance measureMean
  set mZ : ℝ := ∫ ω, Z ω ∂μ
  have hlin : Integrable (fun ω ↦ (-2 * mZ) * Z ω) μ := hZ_int.const_mul (-2 * mZ)
  have hconst : Integrable (fun _ : Ω ↦ mZ ^ 2) μ := integrable_const (mZ ^ 2)
  have h_expand :
      (fun ω ↦ (Z ω - mZ) ^ 2) =
        (((fun ω ↦ Z ω ^ 2) + fun ω ↦ (-2 * mZ) * Z ω) + fun _ : Ω ↦ mZ ^ 2) := by
    funext ω
    simp
    ring_nf
  rw [h_expand]
  rw [show ∫ ω, (((fun ω ↦ Z ω ^ 2) + fun ω ↦ (-2 * mZ) * Z ω) + fun _ : Ω ↦ mZ ^ 2) ω ∂μ
        = ∫ ω, ((fun ω ↦ Z ω ^ 2) + fun ω ↦ (-2 * mZ) * Z ω) ω ∂μ
            + ∫ ω, (fun _ : Ω ↦ mZ ^ 2) ω ∂μ by
        simpa using (integral_add (hZsq_int.add hlin) hconst)]
  rw [show ∫ ω, ((fun ω ↦ Z ω ^ 2) + fun ω ↦ (-2 * mZ) * Z ω) ω ∂μ
        = ∫ ω, (fun ω ↦ Z ω ^ 2) ω ∂μ + ∫ ω, (fun ω ↦ (-2 * mZ) * Z ω) ω ∂μ by
        simpa using (integral_add hZsq_int hlin)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
  simp [mZ]
  ring

theorem measureCovariance_eq_expect_mul_sub_means
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ)
    (hX_int : Integrable X μ)
    (hY_int : Integrable Y μ)
    (hXY_int : Integrable (fun ω ↦ X ω * Y ω) μ) :
    measureCovariance μ X Y =
      (∫ ω, X ω * Y ω ∂μ) - (measureMean μ X) * (measureMean μ Y) := by
  unfold measureCovariance measureMean
  set mX : ℝ := ∫ ω, X ω ∂μ
  set mY : ℝ := ∫ ω, Y ω ∂μ
  have hXlin : Integrable (fun ω ↦ (-mY) * X ω) μ := hX_int.const_mul (-mY)
  have hYlin : Integrable (fun ω ↦ (-mX) * Y ω) μ := hY_int.const_mul (-mX)
  have hconst : Integrable (fun _ : Ω ↦ mX * mY) μ := integrable_const (mX * mY)
  have h_expand :
      (fun ω ↦ (X ω - mX) * (Y ω - mY)) =
        ((((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) +
          fun ω ↦ (-mX) * Y ω) + fun _ : Ω ↦ mX * mY) := by
    funext ω
    simp
    ring_nf
  rw [h_expand]
  rw [show ∫ ω,
        ((((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) + fun ω ↦ (-mX) * Y ω) +
          fun _ : Ω ↦ mX * mY) ω ∂μ
        =
          ∫ ω, (((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) + fun ω ↦ (-mX) * Y ω) ω ∂μ
            + ∫ ω, (fun _ : Ω ↦ mX * mY) ω ∂μ by
        simpa using (integral_add ((hXY_int.add hXlin).add hYlin) hconst)]
  rw [show ∫ ω, (((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) + fun ω ↦ (-mX) * Y ω) ω ∂μ
        = ∫ ω, ((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) ω ∂μ
            + ∫ ω, (fun ω ↦ (-mX) * Y ω) ω ∂μ by
        simpa using (integral_add (hXY_int.add hXlin) hYlin)]
  rw [show ∫ ω, ((fun ω ↦ X ω * Y ω) + fun ω ↦ (-mY) * X ω) ω ∂μ
        = ∫ ω, (fun ω ↦ X ω * Y ω) ω ∂μ + ∫ ω, (fun ω ↦ (-mY) * X ω) ω ∂μ by
        simpa using (integral_add hXY_int hXlin)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const]
  simp [mX, mY]
  ring

theorem measureExpMSE_eq_variance_add_variance_sub_two_cov_add_bias_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y S : Ω → ℝ)
    (hY_int : Integrable Y μ)
    (hS_int : Integrable S μ)
    (hYsq_int : Integrable (fun ω ↦ Y ω ^ 2) μ)
    (hSsq_int : Integrable (fun ω ↦ S ω ^ 2) μ)
    (hYS_int : Integrable (fun ω ↦ Y ω * S ω) μ) :
    measureExpMSE μ Y S =
      measureVariance μ Y + measureVariance μ S -
        2 * measureCovariance μ Y S + (measureBias μ Y S) ^ 2 := by
  rw [measureVariance_eq_expect_sq_sub_sq_mean μ Y hY_int hYsq_int]
  rw [measureVariance_eq_expect_sq_sub_sq_mean μ S hS_int hSsq_int]
  rw [measureCovariance_eq_expect_mul_sub_means μ Y S hY_int hS_int hYS_int]
  unfold measureExpMSE measureBias measureMean
  have hScaledYS : Integrable (fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) μ := hYS_int.const_mul (-2)
  have h_expand :
      (fun ω ↦ (Y ω - S ω) ^ 2) =
        (((fun ω ↦ Y ω ^ 2) + fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) + fun ω ↦ S ω ^ 2) := by
    funext ω
    simp
    ring_nf
  rw [h_expand]
  rw [show ∫ ω, (((fun ω ↦ Y ω ^ 2) + fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) + fun ω ↦ S ω ^ 2) ω ∂μ
        = ∫ ω, ((fun ω ↦ Y ω ^ 2) + fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) ω ∂μ
            + ∫ ω, (fun ω ↦ S ω ^ 2) ω ∂μ by
        simpa using (integral_add (hYsq_int.add hScaledYS) hSsq_int)]
  rw [show ∫ ω, ((fun ω ↦ Y ω ^ 2) + fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) ω ∂μ
        = ∫ ω, (fun ω ↦ Y ω ^ 2) ω ∂μ + ∫ ω, (fun ω ↦ (-2 : ℝ) * (Y ω * S ω)) ω ∂μ by
        simpa using (integral_add hYsq_int hScaledYS)]
  rw [MeasureTheory.integral_const_mul]
  ring

theorem measureLinearPredictionRisk_transport_decomposition_of_orthogonality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω)
    (X : Ω → ι → ℝ) (Y : Ω → ℝ)
    (wStar w : ι → ℝ)
    (hResidualSq_int : Integrable (fun ω ↦ (Y ω - dot wStar (X ω)) ^ 2) μ)
    (hCross_int :
      Integrable
        (fun ω ↦ (Y ω - dot wStar (X ω)) * dot (fun i ↦ w i - wStar i) (X ω)) μ)
    (hDeltaSq_int :
      Integrable (fun ω ↦ (dot (fun i ↦ w i - wStar i) (X ω)) ^ 2) μ)
    (horth :
      ∫ ω, (Y ω - dot wStar (X ω)) * dot (fun i ↦ w i - wStar i) (X ω) ∂μ = 0) :
    ∫ ω, (Y ω - dot w (X ω)) ^ 2 ∂μ =
      ∫ ω, (Y ω - dot wStar (X ω)) ^ 2 ∂μ +
        ∫ ω, (dot (fun i ↦ w i - wStar i) (X ω)) ^ 2 ∂μ := by
  let residual : Ω → ℝ := fun ω ↦ Y ω - dot wStar (X ω)
  let delta : Ω → ℝ := fun ω ↦ dot (fun i ↦ w i - wStar i) (X ω)
  have hdot :
      ∀ ω, dot w (X ω) = dot wStar (X ω) + dot (fun i ↦ w i - wStar i) (X ω) := by
    intro ω
    calc
      dot w (X ω) = ∑ i, (wStar i + (w i - wStar i)) * X ω i := by
        unfold dot
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = ∑ i, (wStar i * X ω i + (w i - wStar i) * X ω i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = dot wStar (X ω) + dot (fun i ↦ w i - wStar i) (X ω) := by
        unfold dot
        rw [Finset.sum_add_distrib]
  have h_expand :
      (fun ω ↦ (Y ω - dot w (X ω)) ^ 2) =
        (fun ω ↦ residual ω ^ 2) +
          ((-2 : ℝ) • fun ω ↦ residual ω * delta ω) +
          fun ω ↦ delta ω ^ 2 := by
    funext ω
    rw [hdot ω]
    simp [residual, delta, smul_eq_mul]
    ring
  rw [h_expand]
  rw [show ∫ ω,
        (((fun ω ↦ residual ω ^ 2) + (-2 : ℝ) • fun ω ↦ residual ω * delta ω) +
          fun ω ↦ delta ω ^ 2) ω ∂μ
        =
          ∫ ω, ((fun ω ↦ residual ω ^ 2) + (-2 : ℝ) • fun ω ↦ residual ω * delta ω) ω ∂μ
            + ∫ ω, (fun ω ↦ delta ω ^ 2) ω ∂μ by
        simpa using (integral_add (hResidualSq_int.add (hCross_int.const_mul (-2))) hDeltaSq_int)]
  rw [show ∫ ω, ((fun ω ↦ residual ω ^ 2) + (-2 : ℝ) • fun ω ↦ residual ω * delta ω) ω ∂μ
        = ∫ ω, (fun ω ↦ residual ω ^ 2) ω ∂μ
            + ∫ ω, (((-2 : ℝ) • fun ω ↦ residual ω * delta ω) ω) ∂μ by
        simpa using (integral_add hResidualSq_int (hCross_int.const_mul (-2)))]
  rw [show ∫ ω, (((-2 : ℝ) • fun ω ↦ residual ω * delta ω) ω) ∂μ
        = (-2 : ℝ) * ∫ ω, residual ω * delta ω ∂μ by
        simpa [Pi.smul_apply] using
          (MeasureTheory.integral_const_mul (-2 : ℝ) (fun ω ↦ residual ω * delta ω))]
  rw [horth]
  ring

/-- Irreducible risk in a conditional-mean DGP: exact Bayes risk under the joint law. -/
noncomputable def irreduciblePredictionRisk {k : ℕ} [Fintype (Fin k)]
    (cmdgp : ConditionalMeanDGP k) : ℝ :=
  ∫ x, (x.2.2 - cmdgp.m x.1 x.2.1) ^ 2 ∂cmdgp.μ

/-- Approximation risk of a deployed predictor relative to the exact conditional mean. -/
noncomputable def conditionalMeanApproximationRisk {k : ℕ} [Fintype (Fin k)]
    (cmdgp : ConditionalMeanDGP k) (pred : Predictor k) : ℝ :=
  ∫ x, (cmdgp.m x.1 x.2.1 - pred x.1 x.2.1) ^ 2 ∂cmdgp.μ

theorem ConditionalMeanDGP.predictionRiskY_eq_irreducible_plus_conditionalMeanApproximationRisk
    {k : ℕ} [Fintype (Fin k)]
    (cmdgp : ConditionalMeanDGP k) (pred : Predictor k)
    (hResidualSq_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.2.2 - cmdgp.m x.1 x.2.1) ^ 2) cmdgp.μ)
    (hGapSq_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (cmdgp.m x.1 x.2.1 - pred x.1 x.2.1) ^ 2) cmdgp.μ)
    (hOrth_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (x.2.2 - cmdgp.m x.1 x.2.1) * (cmdgp.m x.1 x.2.1 - pred x.1 x.2.1)) cmdgp.μ) :
    predictionRiskY cmdgp pred =
      irreduciblePredictionRisk cmdgp + conditionalMeanApproximationRisk cmdgp pred := by
  let residual : ℝ × (Fin k → ℝ) × ℝ → ℝ := fun x ↦ x.2.2 - cmdgp.m x.1 x.2.1
  let gap : ℝ × (Fin k → ℝ) × ℝ → ℝ := fun x ↦ cmdgp.m x.1 x.2.1 - pred x.1 x.2.1
  have horth : ∫ x, residual x * gap x ∂cmdgp.μ = 0 := by
    simpa [residual, gap] using cmdgp.m_spec (fun pc ↦ cmdgp.m pc.1 pc.2 - pred pc.1 pc.2) hOrth_int
  have h_expand :
      (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.2.2 - pred x.1 x.2.1) ^ 2) =
        (((fun x ↦ residual x ^ 2) +
          ((2 : ℝ) • fun x ↦ residual x * gap x)) +
          fun x ↦ gap x ^ 2) := by
    funext x
    simp [residual, gap, smul_eq_mul]
    ring
  unfold predictionRiskY irreduciblePredictionRisk conditionalMeanApproximationRisk
  rw [h_expand]
  rw [show ∫ x,
        (((fun x ↦ residual x ^ 2) + (2 : ℝ) • fun x ↦ residual x * gap x) +
          fun x ↦ gap x ^ 2) x ∂cmdgp.μ
        =
          ∫ x, ((fun x ↦ residual x ^ 2) + (2 : ℝ) • fun x ↦ residual x * gap x) x ∂cmdgp.μ
            + ∫ x, (fun x ↦ gap x ^ 2) x ∂cmdgp.μ by
        simpa using (integral_add (hResidualSq_int.add (hOrth_int.const_mul 2)) hGapSq_int)]
  rw [show ∫ x, ((fun x ↦ residual x ^ 2) + (2 : ℝ) • fun x ↦ residual x * gap x) x ∂cmdgp.μ
        = ∫ x, (fun x ↦ residual x ^ 2) x ∂cmdgp.μ
            + ∫ x, (((2 : ℝ) • fun x ↦ residual x * gap x) x) ∂cmdgp.μ by
        simpa using (integral_add hResidualSq_int (hOrth_int.const_mul 2))]
  rw [show ∫ x, (((2 : ℝ) • fun x ↦ residual x * gap x) x) ∂cmdgp.μ
        = (2 : ℝ) * ∫ x, residual x * gap x ∂cmdgp.μ by
        simpa [Pi.smul_apply] using
          (MeasureTheory.integral_const_mul (2 : ℝ) (fun x ↦ residual x * gap x))]
  rw [horth]
  ring

theorem ConditionalMeanDGP.conditionalMeanApproximationRisk_eq_mseRisk_toDGP
    {k : ℕ} [Fintype (Fin k)]
    (cmdgp : ConditionalMeanDGP k) (pred : Predictor k)
    (hGapSq_meas :
      AEStronglyMeasurable
        (fun pc : ℝ × (Fin k → ℝ) ↦ (cmdgp.m pc.1 pc.2 - pred pc.1 pc.2) ^ 2)
        cmdgp.toDGP.jointMeasure) :
    conditionalMeanApproximationRisk cmdgp pred = mseRisk cmdgp.toDGP pred := by
  unfold conditionalMeanApproximationRisk mseRisk ConditionalMeanDGP.toDGP
  simpa using
    (MeasureTheory.integral_map
      (μ := cmdgp.μ)
      (φ := fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.1, x.2.1))
      (f := fun pc : ℝ × (Fin k → ℝ) ↦ (cmdgp.m pc.1 pc.2 - pred pc.1 pc.2) ^ 2)
      (by fun_prop) hGapSq_meas).symm

theorem ConditionalMeanDGP.predictionRiskY_linear_transport_decomposition
    {k : ℕ} [Fintype (Fin k)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cmdgp : ConditionalMeanDGP k)
    (X : ℝ × (Fin k → ℝ) → ι → ℝ)
    (wStar w : ι → ℝ)
    (hm_linear : ∀ p c, cmdgp.m p c = dot wStar (X (p, c)))
    (hResidualSq_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.2.2 - cmdgp.m x.1 x.2.1) ^ 2) cmdgp.μ)
    (hOrth_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (x.2.2 - cmdgp.m x.1 x.2.1) *
          dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) cmdgp.μ)
    (hDeltaSq_int :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) ^ 2) cmdgp.μ) :
    predictionRiskY cmdgp (fun p c ↦ dot w (X (p, c))) =
      irreduciblePredictionRisk cmdgp +
        ∫ x, (dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ := by
  have horth :
      ∫ x, (x.2.2 - cmdgp.m x.1 x.2.1) *
        dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1)) ∂cmdgp.μ = 0 := by
    simpa using
      cmdgp.m_spec (fun pc ↦ dot (fun i ↦ w i - wStar i) (X pc)) hOrth_int
  have hResidualSq_int_linear :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (x.2.2 - dot wStar (X (x.1, x.2.1))) ^ 2) cmdgp.μ := by
    refine hResidualSq_int.congr ?_
    filter_upwards with x
    rw [← hm_linear x.1 x.2.1]
  have hbase :
      ∫ x, (x.2.2 - dot wStar (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ =
        irreduciblePredictionRisk cmdgp := by
    unfold irreduciblePredictionRisk
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [← hm_linear x.1 x.2.1]
  have hOrth_int_linear :
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦
        (x.2.2 - dot wStar (X (x.1, x.2.1))) *
          dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) cmdgp.μ := by
    refine hOrth_int.congr ?_
    filter_upwards with x
    rw [← hm_linear x.1 x.2.1]
  have horth_linear :
      ∫ x, (x.2.2 - dot wStar (X (x.1, x.2.1))) *
        dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1)) ∂cmdgp.μ = 0 := by
    simpa [hm_linear] using horth
  unfold predictionRiskY
  calc
    ∫ x, (x.2.2 - dot w (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ =
        ∫ x, (x.2.2 - dot wStar (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ +
          ∫ x, (dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ := by
            exact measureLinearPredictionRisk_transport_decomposition_of_orthogonality
              cmdgp.μ
              (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ X (x.1, x.2.1))
              (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ x.2.2)
              wStar w hResidualSq_int_linear hOrth_int_linear hDeltaSq_int horth_linear
    _ = irreduciblePredictionRisk cmdgp +
          ∫ x, (dot (fun i ↦ w i - wStar i) (X (x.1, x.2.1))) ^ 2 ∂cmdgp.μ := by
            rw [hbase]

end ExactMeasureMetricIdentities

/-! ### Effect Heterogeneity: R² and AUC Improvement

When PGS effect size α(c) varies across PC space, using PC-specific coefficients
improves both R² and discrimination.

**Mathematical basis**: If Y = α(c)·P + f(c), then using Ŷ = β·P (single slope) has:
- MSE(raw) = MSE(calibrated) + E[(α(c) - β)² · P²]
- The excess term is strictly positive when α varies
-/

/-- Mean squared error for a predictor. -/
noncomputable def mse {k : ℕ} [Fintype (Fin k)] (dgp : DataGeneratingProcess k)
    (pred : ℝ → (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ pc, (dgp.trueExpectation pc.1 pc.2 - pred pc.1 pc.2)^2 ∂dgp.jointMeasure

/-- DGP with PC-varying effect size: Y = α(c)·P + f₀(c) -/
structure HeterogeneousEffectDGP (k : ℕ) where
  alpha : (Fin k → ℝ) → ℝ
  baseline : (Fin k → ℝ) → ℝ
  jointMeasure : Measure (ℝ × (Fin k → ℝ))
  is_prob : IsProbabilityMeasure jointMeasure

/-- **A heterogeneous-effect DGP exists.**

The `is_prob` field is a `Prop` the caller must discharge, so without a closed
term of this type the theorems taking one are conditional on a process nobody
exhibits. A Dirac measure at the origin is a probability measure, and the two
function fields are unconstrained, so constants serve.

Degenerate deliberately: the obligation is inhabitation. Every theorem below
quantifies over all `HeterogeneousEffectDGP k`, so one witness settles that the
class is nonempty without suggesting the results turn on which one. -/
noncomputable def HeterogeneousEffectDGP.witness (k : ℕ) : HeterogeneousEffectDGP k where
  alpha := fun _ ↦ 0
  baseline := fun _ ↦ 0
  jointMeasure := Measure.dirac (0, 0)
  is_prob := inferInstance

instance {k : ℕ} : Nonempty (HeterogeneousEffectDGP k) :=
  ⟨HeterogeneousEffectDGP.witness k⟩

/-- True expectation for heterogeneous effect DGP. -/
def HeterogeneousEffectDGP.trueExp {k : ℕ} (hdgp : HeterogeneousEffectDGP k) :
    ℝ → (Fin k → ℝ) → ℝ := fun p c ↦ hdgp.alpha c * p + hdgp.baseline c

/-- Convert to standard DGP. -/
noncomputable def HeterogeneousEffectDGP.toDGP {k : ℕ} (hdgp : HeterogeneousEffectDGP k) :
    DataGeneratingProcess k :=
  { trueExpectation := hdgp.trueExp
    jointMeasure := hdgp.jointMeasure
    is_prob := hdgp.is_prob }

/-- **MSE of calibrated model is zero** (perfect prediction of conditional mean). -/
theorem mse_calibrated_zero {k : ℕ} [Fintype (Fin k)] (hdgp : HeterogeneousEffectDGP k) :
    mse hdgp.toDGP hdgp.trueExp = 0 := by
  simp only [mse, HeterogeneousEffectDGP.toDGP, HeterogeneousEffectDGP.trueExp]
  simp only [sub_self, sq, mul_zero, integral_zero]

/-- **MSE of raw model equals E[(α(c) - β)² · P²]**. -/
theorem mse_raw_formula {k : ℕ} [Fintype (Fin k)] (hdgp : HeterogeneousEffectDGP k) (β : ℝ) :
    let pred_raw := fun p c ↦ β * p + hdgp.baseline c
    mse hdgp.toDGP pred_raw = ∫ pc, (hdgp.alpha pc.2 - β)^2 * pc.1^2 ∂hdgp.jointMeasure := by
  simp only [mse, HeterogeneousEffectDGP.toDGP, HeterogeneousEffectDGP.trueExp]
  congr 1; ext pc
  ring_nf

/-- **MSE Improvement**: Raw model has positive MSE when α varies.

    The hypothesis `h_product_pos` states that E[(α(c)-β)²·P²] > 0,
    which holds when there exist points where both α(c) ≠ β and P ≠ 0
    (i.e., the supports of the effect heterogeneity and PGS overlap). -/
theorem mse_improvement {k : ℕ} [Fintype (Fin k)] (hdgp : HeterogeneousEffectDGP k) (β : ℝ)
    -- Direct hypothesis: the product integral is positive
    (h_product_pos : ∫ pc, (hdgp.alpha pc.2 - β)^2 * pc.1^2 ∂hdgp.jointMeasure > 0) :
    let pred_raw := fun p c ↦ β * p + hdgp.baseline c
    mse hdgp.toDGP pred_raw > mse hdgp.toDGP hdgp.trueExp := by
  -- Expand the let and rewrite MSE(calibrated) = 0
  simp only [mse_calibrated_zero]
  -- Show MSE(raw) > 0
  -- MSE(raw) = ∫ (α(c)·p + baseline(c) - (β·p + baseline(c)))² = ∫ (α(c) - β)² · p²
  simp only [mse, HeterogeneousEffectDGP.toDGP, HeterogeneousEffectDGP.trueExp]
  -- The integrand simplifies to (α(c) - β)² · p²
  have h_simp : ∀ pc : ℝ × (Fin k → ℝ),
      (hdgp.alpha pc.2 * pc.1 + hdgp.baseline pc.2 - (β * pc.1 + hdgp.baseline pc.2))^2 =
      (hdgp.alpha pc.2 - β)^2 * pc.1^2 := by
    intro pc; ring
  simp_rw [h_simp]
  -- The goal is exactly h_product_pos
  exact h_product_pos

/-- **R² Improvement**: Lower MSE means higher R². -/
theorem rsquared_improvement {k : ℕ} [Fintype (Fin k)] (hdgp : HeterogeneousEffectDGP k) (β : ℝ)
    (hY_var_pos : var hdgp.toDGP hdgp.trueExp > 0)
    (h_product_pos : ∫ pc, (hdgp.alpha pc.2 - β)^2 * pc.1^2 ∂hdgp.jointMeasure > 0) :
    let pred_raw := fun p c ↦ β * p + hdgp.baseline c
    let r2_raw := 1 - mse hdgp.toDGP pred_raw / var hdgp.toDGP hdgp.trueExp
    let r2_cal := 1 - mse hdgp.toDGP hdgp.trueExp / var hdgp.toDGP hdgp.trueExp
    r2_cal > r2_raw := by
  have h_mse := mse_improvement hdgp β h_product_pos
  have h_cal_zero := mse_calibrated_zero hdgp
  simp only [h_cal_zero, zero_div, sub_zero]
  -- r2_cal = 1, r2_raw = 1 - MSE(raw)/Var(Y) < 1
  have h_mse_pos : mse hdgp.toDGP (fun p c ↦ β * p + hdgp.baseline c) > 0 := by
    rw [h_cal_zero] at h_mse; exact h_mse
  have h_ratio_pos : mse hdgp.toDGP (fun p c ↦ β * p + hdgp.baseline c) /
                     var hdgp.toDGP hdgp.trueExp > 0 :=
    div_pos h_mse_pos hY_var_pos
  linarith

/-- **Within-PC Rankings Unchanged**: At fixed PC, both models rank by P. -/
theorem within_pc_rankings_preserved {k : ℕ} [Fintype (Fin k)]
    (hdgp : HeterogeneousEffectDGP k) (β : ℝ) (c : Fin k → ℝ)
    (hα_pos : hdgp.alpha c > 0) (hβ_pos : β > 0) :
    ∀ p₁ p₂ : ℝ,
      (β * p₁ + hdgp.baseline c > β * p₂ + hdgp.baseline c) ↔
      (hdgp.alpha c * p₁ + hdgp.baseline c > hdgp.alpha c * p₂ + hdgp.baseline c) := by
  intros p₁ p₂
  constructor <;> intro h <;> nlinarith

/-- **Improvement Larger for Distant PC**: Per-individual MSE reduction is larger
    where α deviates more from β. This formalizes why calibration helps
    underrepresented groups MORE. -/
theorem mse_pointwise_larger_for_distant {k : ℕ} [Fintype (Fin k)]
    (hdgp : HeterogeneousEffectDGP k) (β : ℝ)
    (c_near c_far : Fin k → ℝ) (p : ℝ)
    (h_deviation : |hdgp.alpha c_near - β| < |hdgp.alpha c_far - β|) :
    -- Pointwise squared error is larger for distant PC
    (hdgp.alpha c_far - β)^2 * p^2 ≥ (hdgp.alpha c_near - β)^2 * p^2 := by
  -- |a| < |b| implies a² < b² (since x² = |x|² and x ↦ x² is strictly monotone on [0,∞))
  have h_sq : (hdgp.alpha c_near - β)^2 < (hdgp.alpha c_far - β)^2 := by
    have h1 : (hdgp.alpha c_near - β)^2 = |hdgp.alpha c_near - β|^2 := (sq_abs _).symm
    have h2 : (hdgp.alpha c_far - β)^2 = |hdgp.alpha c_far - β|^2 := (sq_abs _).symm
    rw [h1, h2]
    have h_nonneg_near : 0 ≤ |hdgp.alpha c_near - β| := abs_nonneg _
    have h_nonneg_far : 0 ≤ |hdgp.alpha c_far - β| := abs_nonneg _
    nlinarith
  -- (a² < b²) and (p² ≥ 0) implies a²p² ≤ b²p²
  nlinarith [sq_nonneg p]

/-! ### Evolutionary Coordinate Library

This block records coarse population-genetic coordinates derived from drift,
mutation, migration, divergence time, and recombination. These coordinates are
useful as primitives, but they are **not** treated here as an independent or
multiplicatively separable transport law for PGS portability.

Biologically, LD decay, allele-frequency change, mutation history, and
migration history interact through locus-specific state. This file therefore
stops at coordinate extraction. Any mechanistic portability claim must proceed
through the explicit SNP/LD-aware state space downstream in
`PortabilityDrift`. -/

section EvolutionaryCoordinates

/-- Parameters of a coarse evolutionary coordinate model with all four forces. -/
structure EvolutionaryParameters where
  /-- Effective population size (harmonic mean over history). -/
  Ne : ℝ
  /-- Mutation rate per generation. -/
  mu : ℝ
  /-- Migration rate per generation (symmetric). -/
  mig : ℝ
  /-- Divergence time in generations. -/
  t_div : ℝ
  /-- Recombination rate between linked loci. -/
  recomb : ℝ
  /-- Additive genetic variance in ancestral population. -/
  V_A : ℝ
  Ne_pos : 0 < Ne
  mu_nonneg : 0 ≤ mu
  mig_nonneg : 0 ≤ mig
  t_div_nonneg : 0 ≤ t_div
  recomb_nonneg : 0 ≤ recomb
  recomb_le_half : recomb ≤ 1 / 2
  V_A_pos : 0 < V_A

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def EvolutionaryParameters.witness : EvolutionaryParameters where
  Ne := 1
  mu := 1
  mig := 1
  t_div := 1
  recomb := 1 / 4
  V_A := 1
  Ne_pos := by norm_num
  mu_nonneg := by norm_num
  mig_nonneg := by norm_num
  t_div_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num

/-- Scaled drift parameter: τ = t/(2Ne).

    Empirical status: UNTESTED. -/
noncomputable def EvolutionaryParameters.tau (p : EvolutionaryParameters) : ℝ :=
  p.t_div / (2 * p.Ne)

/-- Scaled mutation parameter: θ = 4Neμ. -/
noncomputable def EvolutionaryParameters.theta (p : EvolutionaryParameters) : ℝ :=
  scaledMutationRate p.Ne p.mu

/-- Scaled migration parameter: M = 4Nem. -/
noncomputable def EvolutionaryParameters.bigM (p : EvolutionaryParameters) : ℝ :=
  scaledMigrationRate p.Ne p.mig

/-- θ ≥ 0. -/
theorem EvolutionaryParameters.theta_nonneg (p : EvolutionaryParameters) :
    0 ≤ p.theta := by
  unfold theta scaledMutationRate
  have h1 : 0 < 4 * p.Ne := by linarith [p.Ne_pos]
  exact mul_nonneg (le_of_lt h1) p.mu_nonneg

/-- M ≥ 0. -/
theorem EvolutionaryParameters.bigM_nonneg (p : EvolutionaryParameters) :
    0 ≤ p.bigM := by
  unfold bigM scaledMigrationRate
  have h1 : 0 < 4 * p.Ne := by linarith [p.Ne_pos]
  exact mul_nonneg (le_of_lt h1) p.mig_nonneg

/-- τ ≥ 0. -/
theorem EvolutionaryParameters.tau_nonneg (p : EvolutionaryParameters) :
    0 ≤ p.tau := by
  unfold tau
  exact div_nonneg p.t_div_nonneg (by linarith [p.Ne_pos])


/-- **Drift-migration equilibrium Fst**: Fst = 1/(1 + M).
    Migration homogenizes populations, reducing Fst.

        Empirical status: UNTESTED. -/
noncomputable def fstDriftMigration (p : EvolutionaryParameters) : ℝ :=
  1 / (1 + p.bigM)

/-- **One generation of the identity-by-descent balance under all three
forces.**

`F` is the probability that two gene copies drawn from the same population are
identical by descent.  In one generation drift makes a pair identical with
probability `1/(2 Nₑ)` among the pairs that are not already identical, and each
of the two lineages independently leaves the local identity class at rate
`mig + mu` -- by being replaced by a migrant, or by mutating away from its
ancestral allelic state.  Migration and mutation enter through their *sum*
because, to first order, either event destroys identity and neither can undo
the other.

Composition convention: the three forces are added, not composed, so their
within-generation ordering does not matter.  This is the first-order
(weak-force, large-`Nₑ`) model; the unlinearised recursion multiplies
`(1 - mig)²(1 - mu)²` against `1 - 1/(2 Nₑ)` and has a fixed point differing at
`O(mig², mu², mig/Nₑ)`.

    Empirical status: UNTESTED. -/
noncomputable def fstDriftFlowStep (p : EvolutionaryParameters) (F : ℝ) : ℝ :=
  F + (1 - F) / (2 * p.Ne) - 2 * (p.mig + p.mu) * F

/-- **At fixation drift contributes nothing and only flow pulls back.** With `F = 1` the
`(1 - F)` drift term vanishes identically, so the step is one minus twice the total flow rate --
the reference point that separates the drift term from the flow term. -/
theorem fstDriftFlowStep_at_one (p : EvolutionaryParameters) :
    fstDriftFlowStep p 1 = 1 - 2 * (p.mig + p.mu) := by
  unfold fstDriftFlowStep
  ring

/-- **Full equilibrium Fst** under drift + mutation + migration:
    Fst = 1/(1 + θ + M). Both mutation and migration counteract drift.

    Not stipulated: `fstEquilibrium_isFixedPoint` derives it as the rest point
    of `fstDriftFlowStep`.  With `θ = 4 Nₑ μ` and `M = 4 Nₑ m`, balancing
    `(1 - F)/(2 Nₑ)` against `2(m + μ)F` gives `F (1 + 4 Nₑ (m + μ)) = 1`, and
    `4 Nₑ (m + μ) = θ + M` is why the two scaled rates add.

    Empirical status: UNTESTED. -/
noncomputable def fstEquilibrium (p : EvolutionaryParameters) : ℝ :=
  1 / (1 + p.theta + p.bigM)

/-!
### Note for anyone editing the Fst cluster below

Twice today this cluster broke as a side effect of moving or absorbing a
definition elsewhere, both times in `unfold` lists rather than in any
mathematics. Recording the shape of both, because the sweeps that follow such
moves have not been catching them.

**Stale unfold targets.** `unfold X` is an error, not a no-op, when `X` does not
occur in the goal. So when a definition stops routing through another, *every*
`unfold` list naming the inner one breaks at once. `fstEquilibrium` above is
`1 / (1 + θ + M)` and `fstDriftMigration` is `1 / (1 + M)`; neither calls
`fstMutationDriftEquilibrium`, and only `fstDriftMutation` did. One stale name
in the lists below produced seven simultaneous failures, which reads like a
change of shape in the definition itself and is not one — the definition is a
plain `def (θ : ℝ) : ℝ := 1 / (1 + θ)` throughout and unfolds fine.

**Shape-unaware repointing.** `fstDriftMutation p` was a wrapper for
`fstMutationDriftEquilibrium p.theta`, was removed as a duplicate, and its call
sites were repointed textually. That is correct at sites that *apply* it and
wrong at sites that only *name* it: inside an `unfold` list the argument glued
onto the constant, giving `fstMutationDriftEquilibrium.theta`, which is not a
constant. It was caught only because the mangling happened to be ill-formed. A
repoint that stayed well-formed would have compiled and been silent.

The general rule the two share: a textual repoint sees applications. It does not
see bare constant names in `unfold`/`simp only`/`rw` argument lists, and it does
not see docstrings — a third instance left an orphaned doc comment above the
`Step 2` section header when `migrationLDBoost` moved.

(That sentence originally quoted the doc-comment opener literally. Lean nests
block comments, so the quoted opener opened one, the closer below shut only
that, and this note left its own module unterminated — the failure
the `identifications` guard in check.py counts delimiters for. Do not write the opener
literally in prose here.)
-/

/-- **The full equilibrium Fst is the fixed point of the three-force
balance.** -/
theorem fstEquilibrium_isFixedPoint (p : EvolutionaryParameters) :
    fstDriftFlowStep p (fstEquilibrium p) = fstEquilibrium p := by
  have hNe' : p.Ne ≠ 0 := ne_of_gt p.Ne_pos
  have hd : (0 : ℝ) < 1 + p.theta + p.bigM := by
    linarith [p.theta_nonneg, p.bigM_nonneg]
  have hd' : (1 : ℝ) + p.theta + p.bigM ≠ 0 := ne_of_gt hd
  have hscaled : 1 + p.theta + p.bigM = 1 + 4 * p.Ne * (p.mig + p.mu) := by
    unfold EvolutionaryParameters.theta EvolutionaryParameters.bigM scaledMutationRate
      scaledMigrationRate
    ring
  unfold fstDriftFlowStep fstEquilibrium
  rw [hscaled] at hd' ⊢
  field_simp
  ring

/-- **Complete fixation is a boundary the closed form attains.**  With neither
mutation nor migration, `θ = M = 0` and the equilibrium is exactly `1`: drift
alone runs to fixation, and the formula reaches that value rather than
approaching it. -/
theorem fstEquilibrium_of_no_flow (p : EvolutionaryParameters)
    (hmig : p.mig = 0) (hmu : p.mu = 0) :
    fstEquilibrium p = 1 := by
  have hθ : p.theta = 0 := by
    unfold EvolutionaryParameters.theta scaledMutationRate
    rw [hmu]; ring
  have hM : p.bigM = 0 := by
    unfold EvolutionaryParameters.bigM scaledMigrationRate
    rw [hmig]; ring
  unfold fstEquilibrium
  rw [hθ, hM]
  norm_num

/-- Full equilibrium Fst is positive. -/
theorem fstEquilibrium_pos (p : EvolutionaryParameters) :
    0 < fstEquilibrium p := by
  unfold fstEquilibrium
  apply div_pos one_pos
  linarith [p.theta_nonneg, p.bigM_nonneg]

/-- **Full equilibrium Fst never exceeds one**, unconditionally.  `θ` and `M`
are nonnegative by construction, so the denominator `1 + θ + M` is at least one
and the reciprocal is at most one.  No force needs to be present: the no-flow
boundary `θ = M = 0` attains the value `1` rather than exceeding it. -/
theorem fstEquilibrium_le_one (p : EvolutionaryParameters) :
    fstEquilibrium p ≤ 1 := by
  unfold fstEquilibrium
  rw [div_le_one (by linarith [p.theta_nonneg, p.bigM_nonneg] :
    (0 : ℝ) < 1 + p.theta + p.bigM)]
  linarith [p.theta_nonneg, p.bigM_nonneg]

/-- Full equilibrium Fst < 1 when either θ > 0 or M > 0. -/
theorem fstEquilibrium_lt_one (p : EvolutionaryParameters)
    (h : 0 < p.theta + p.bigM) :
    fstEquilibrium p < 1 := by
  unfold fstEquilibrium
  rw [div_lt_one (by linarith : 0 < 1 + p.theta + p.bigM)]
  linarith

/-- Full equilibrium Fst ≤ drift-mutation Fst (migration only helps). -/
theorem fstEquilibrium_le_driftMutation (p : EvolutionaryParameters) :
    fstEquilibrium p ≤ fstMutationDriftEquilibrium p.theta := by
  unfold fstEquilibrium fstMutationDriftEquilibrium
  exact one_div_le_one_div_of_le (by linarith [p.theta_nonneg]) (by linarith [p.bigM_nonneg])

/-- Full equilibrium Fst ≤ drift-migration Fst (mutation only helps). -/
theorem fstEquilibrium_le_driftMigration (p : EvolutionaryParameters) :
    fstEquilibrium p ≤ fstDriftMigration p := by
  unfold fstEquilibrium fstDriftMigration
  apply one_div_le_one_div_of_le
  · linarith [p.bigM_nonneg]
  · linarith [p.theta_nonneg]

/-- **Key ordering**: Fst_full ≤ Fst_mutation_only ≤ Fst_drift_only (at equilibrium).
    Each additional force beyond drift reduces Fst. -/
theorem fst_ordering (p : EvolutionaryParameters) (h_theta : 0 < p.theta) :
    fstEquilibrium p ≤ fstMutationDriftEquilibrium p.theta ∧
    fstMutationDriftEquilibrium p.theta < 1 := by
  constructor
  · exact fstEquilibrium_le_driftMutation p
  · unfold fstMutationDriftEquilibrium
    rw [div_lt_one (by linarith : 0 < 1 + p.theta)]
    linarith

/-- **Shared LD retention** under recombination and divergence.
    The fraction of LD shared between populations decays as exp(-2rt)
    (factor of 2 because both lineages must avoid recombination).

    Empirical status: UNTESTED. -/
noncomputable def sharedLDRetention (p : EvolutionaryParameters) : ℝ :=
  Real.exp (-2 * p.recomb * p.t_div)

/-- Shared LD retention is positive. -/
theorem sharedLDRetention_pos (p : EvolutionaryParameters) :
    0 < sharedLDRetention p := by
  unfold sharedLDRetention; exact Real.exp_pos _

/-- Shared LD retention is ≤ 1. -/
theorem sharedLDRetention_le_one (p : EvolutionaryParameters) :
    sharedLDRetention p ≤ 1 := by
  unfold sharedLDRetention
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [p.recomb_nonneg, p.t_div_nonneg]

/-- Shared LD retention decreases with divergence time. -/
theorem sharedLDRetention_decreasing_in_time
    (p₁ p₂ : EvolutionaryParameters)
    (h_same : p₁.recomb = p₂.recomb)
    (h_r_pos : 0 < p₁.recomb)
    (h_time : p₁.t_div < p₂.t_div) :
    sharedLDRetention p₂ < sharedLDRetention p₁ := by
  unfold sharedLDRetention
  apply Real.exp_lt_exp.mpr
  rw [h_same]
  nlinarith [h_r_pos, h_time]

/-- **Mutation-induced LD erosion**: new mutations create population-specific LD
    that is not shared. The fraction of LD that remains "ancestral" (shared)
    decays exponentially with the scaled mutation rate.

    Empirical status: UNTESTED. -/
noncomputable def mutationLDErosion (p : EvolutionaryParameters) : ℝ :=
  Real.exp (-p.theta * p.tau)

/-- Mutation LD erosion is in (0, 1]. -/
theorem mutationLDErosion_pos (p : EvolutionaryParameters) :
    0 < mutationLDErosion p := by
  unfold mutationLDErosion
  exact Real.exp_pos _

theorem mutationLDErosion_le_one (p : EvolutionaryParameters) :
    mutationLDErosion p ≤ 1 := by
  unfold mutationLDErosion
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith [p.theta_nonneg, p.tau_nonneg]

/-- **Migration LD boost**: migration increases shared LD by introducing
    alleles from the other population. Models as a correction factor ≥ 1.

    Empirical status: UNTESTED. -/
noncomputable def migrationLDBoost (p : EvolutionaryParameters) : ℝ :=
  1 + p.bigM * p.tau / (1 + p.bigM)

/-- Migration LD boost ≥ 1. -/
theorem migrationLDBoost_ge_one (p : EvolutionaryParameters) :
    1 ≤ migrationLDBoost p := by
  unfold migrationLDBoost
  have h1 : 0 ≤ p.bigM * p.tau / (1 + p.bigM) := by
    apply div_nonneg
    · exact mul_nonneg p.bigM_nonneg p.tau_nonneg
    · linarith [p.bigM_nonneg]
  linarith

/-- Primitive coordinate record extracted from the coarse evolutionary block.
These coordinates are stored side by side, but this file does not assert that
they act independently, are jointly sufficient for transport, or combine into a
closed-form portability law. -/
structure EvolutionaryCoordinateSummary where
  alleleFreqCoordinate : ℝ
  sharedLDCoordinate : ℝ
  ancestralVariantCoordinate : ℝ
  migrationCoordinate : ℝ

@[ext] theorem EvolutionaryCoordinateSummary.ext
    {a b : EvolutionaryCoordinateSummary}
    (h₁ : a.alleleFreqCoordinate = b.alleleFreqCoordinate)
    (h₂ : a.sharedLDCoordinate = b.sharedLDCoordinate)
    (h₃ : a.ancestralVariantCoordinate = b.ancestralVariantCoordinate)
    (h₄ : a.migrationCoordinate = b.migrationCoordinate) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Canonical primitive evolutionary coordinate summary for the coarse model. -/
noncomputable def EvolutionaryParameters.coordinateSummary
    (p : EvolutionaryParameters) : EvolutionaryCoordinateSummary where
  alleleFreqCoordinate := 1 - fstEquilibrium p
  sharedLDCoordinate := sharedLDRetention p
  ancestralVariantCoordinate := mutationLDErosion p
  migrationCoordinate := migrationLDBoost p

@[simp] theorem EvolutionaryParameters.coordinateSummary_alleleFreqCoordinate
    (p : EvolutionaryParameters) :
    p.coordinateSummary.alleleFreqCoordinate = 1 - fstEquilibrium p := by
  rfl

@[simp] theorem EvolutionaryParameters.coordinateSummary_sharedLDCoordinate
    (p : EvolutionaryParameters) :
    p.coordinateSummary.sharedLDCoordinate = sharedLDRetention p := by
  rfl

@[simp] theorem EvolutionaryParameters.coordinateSummary_ancestralVariantCoordinate
    (p : EvolutionaryParameters) :
    p.coordinateSummary.ancestralVariantCoordinate = mutationLDErosion p := by
  rfl

@[simp] theorem EvolutionaryParameters.coordinateSummary_migrationCoordinate
    (p : EvolutionaryParameters) :
    p.coordinateSummary.migrationCoordinate = migrationLDBoost p := by
  rfl

/-- The allele-frequency coordinate is nonnegative, unconditionally.

This used to carry `0 < θ + M` and route through `fstEquilibrium_lt_one`, which
is the strict bound and needs a force present.  Nonnegativity only needs the
non-strict `fstEquilibrium_le_one`, which holds at the no-flow boundary too, so
the hypothesis was never a restriction on the statement — it was a restriction
on the proof that had been pushed onto the caller. -/
theorem EvolutionaryParameters.coordinateSummary_alleleFreqCoordinate_nonneg
    (p : EvolutionaryParameters) :
    0 ≤ p.coordinateSummary.alleleFreqCoordinate := by
  rw [EvolutionaryParameters.coordinateSummary_alleleFreqCoordinate]
  linarith [fstEquilibrium_le_one p]

/-- The shared-LD coordinate is strictly positive. -/
theorem EvolutionaryParameters.coordinateSummary_sharedLDCoordinate_pos
    (p : EvolutionaryParameters) :
    0 < p.coordinateSummary.sharedLDCoordinate := by
  rw [EvolutionaryParameters.coordinateSummary_sharedLDCoordinate]
  unfold sharedLDRetention
  exact Real.exp_pos _

/-- The ancestral-variant coordinate is strictly positive. -/
theorem EvolutionaryParameters.coordinateSummary_ancestralVariantCoordinate_pos
    (p : EvolutionaryParameters) :
    0 < p.coordinateSummary.ancestralVariantCoordinate := by
  rw [EvolutionaryParameters.coordinateSummary_ancestralVariantCoordinate]
  exact mutationLDErosion_pos p

/-- The migration coordinate is at least one. -/
theorem EvolutionaryParameters.coordinateSummary_migrationCoordinate_ge_one
    (p : EvolutionaryParameters) :
    1 ≤ p.coordinateSummary.migrationCoordinate := by
  rw [EvolutionaryParameters.coordinateSummary_migrationCoordinate]
  exact migrationLDBoost_ge_one p

/-- **Each force's marginal effect on Fst.**
    Increasing any counterbalancing force (θ or M) strictly decreases Fst. -/
theorem fstEquilibrium_decreasing_in_theta
    (Ne mu₁ mu₂ mig t_div recomb V_A : ℝ)
    (hNe : 0 < Ne) (hmu₁ : 0 ≤ mu₁) (hmu₂ : 0 ≤ mu₂) (hmig : 0 ≤ mig)
    (ht : 0 ≤ t_div) (hr : 0 ≤ recomb) (hr2 : recomb ≤ 1/2) (hV : 0 < V_A)
    (h_mu : mu₁ < mu₂) :
    let p₁ : EvolutionaryParameters :=
      ⟨Ne, mu₁, mig, t_div, recomb, V_A, hNe, hmu₁, hmig, ht, hr, hr2, hV⟩
    let p₂ : EvolutionaryParameters :=
      ⟨Ne, mu₂, mig, t_div, recomb, V_A, hNe, hmu₂, hmig, ht, hr, hr2, hV⟩
    fstEquilibrium p₂ < fstEquilibrium p₁ := by
  simp only
  unfold fstEquilibrium EvolutionaryParameters.theta EvolutionaryParameters.bigM scaledMutationRate
    scaledMigrationRate
  simp only
  rw [div_lt_div_iff₀
    (by nlinarith : 0 < 1 + 4 * Ne * mu₂ + 4 * Ne * mig)
    (by nlinarith : 0 < 1 + 4 * Ne * mu₁ + 4 * Ne * mig)]
  nlinarith

theorem fstEquilibrium_decreasing_in_migration
    (Ne mu mig₁ mig₂ t_div recomb V_A : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu) (hmig₁ : 0 ≤ mig₁) (hmig₂ : 0 ≤ mig₂)
    (ht : 0 ≤ t_div) (hr : 0 ≤ recomb) (hr2 : recomb ≤ 1/2) (hV : 0 < V_A)
    (h_mig : mig₁ < mig₂) :
    let p₁ : EvolutionaryParameters :=
      ⟨Ne, mu, mig₁, t_div, recomb, V_A, hNe, hmu, hmig₁, ht, hr, hr2, hV⟩
    let p₂ : EvolutionaryParameters :=
      ⟨Ne, mu, mig₂, t_div, recomb, V_A, hNe, hmu, hmig₂, ht, hr, hr2, hV⟩
    fstEquilibrium p₂ < fstEquilibrium p₁ := by
  simp only
  unfold fstEquilibrium EvolutionaryParameters.theta EvolutionaryParameters.bigM scaledMutationRate
    scaledMigrationRate
  simp only
  rw [div_lt_div_iff₀
    (by nlinarith : 0 < 1 + 4 * Ne * mu + 4 * Ne * mig₂)
    (by nlinarith : 0 < 1 + 4 * Ne * mu + 4 * Ne * mig₁)]
  nlinarith

/-! **Two Fst-to-covariance-gap statements were removed here, and neither mentioned a
covariance gap.**

`unified_fst_to_covariance_gap` claimed "higher Fst → larger covariance mismatch → worse
portability" and proved `0 < kappa * fstEquilibrium p` for an arbitrary positive real
`kappa` — a positivity fact, not a map, not monotone in Fst, and with no covariance
anywhere; its `0 < θ + M` hypothesis was unused.  `fstEquilibrium_pos` is the content.

`full_model_smaller_gap_than_drift` claimed the full model has a smaller gap than pure
drift and was `mul_lt_mul_of_pos_left` applied to free reals *named* `fst_full` and
`fst_drift`.  The ordering it "proved" was its own hypothesis; the two names were never
tied to `fstEquilibrium` or to `fstMutationDriftEquilibrium`.  The real comparison, proved
from the definitions, is `fstEquilibrium_le_driftMutation` and
`fstEquilibrium_le_driftMigration` above. -/

/-- **The harmonic mean of `Ne` over a bottleneck lies below the time-weighted arithmetic
mean.**  Given the harmonic-mean relation `T/Ne_h = T_b/Ne_small + (T-T_b)/Ne_large` as a
hypothesis, `Ne_h < (T_b·Ne_small + (T-T_b)·Ne_large)/T` — the two-term AM–HM inequality,
strict because `Ne_small ≠ Ne_large`.

This was `harmonic_mean_governs_drift`, documented as "Fst ≈ 1 - exp(-T/(2 Ne_h))" with
bottlenecks "disproportionately increasing Fst".  No Fst, no exponential and no drift
recurrence appears below; the inequality is about two means of `Ne` and says nothing about
how either maps to Fst. -/
theorem harmonicMeanNe_lt_timeWeightedArithmeticMeanNe
    (Ne_h Ne_large Ne_small : ℝ) (T_total T_bottleneck : ℝ)
    (h_Ne_h_pos : 0 < Ne_h)
    (h_large : 0 < Ne_large) (h_small : 0 < Ne_small)
    (h_bottleneck : Ne_small < Ne_large)
    (h_T_pos : 0 < T_total) (h_Tb_pos : 0 < T_bottleneck) (h_Tb_le : T_bottleneck < T_total)
    -- Harmonic mean: T/Ne_h = T_b/Ne_small + (T-T_b)/Ne_large
    (h_harmonic : T_total / Ne_h = T_bottleneck / Ne_small + (T_total - T_bottleneck) / Ne_large) :
    -- The harmonic mean Ne is less than the arithmetic mean (bottleneck dominates)
    Ne_h < (T_bottleneck * Ne_small + (T_total - T_bottleneck) * Ne_large) / T_total := by
  -- Strategy: HM < AM via the Cauchy-Schwarz identity
  --   P·D - T²·Ne_s·Ne_l = T_b·(T-T_b)·(Ne_l - Ne_s)² > 0
  -- where D = T_b·Ne_l + (T-T_b)·Ne_s  and  P = T_b·Ne_s + (T-T_b)·Ne_l
  rw [lt_div_iff₀ h_T_pos]
  -- Clear fractions in harmonic mean to get: Ne_h · D = T · Ne_s · Ne_l
  have hD_pos : (0:ℝ) < T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small := by
    have : 0 < T_total - T_bottleneck := by linarith
    nlinarith [mul_pos h_Tb_pos h_large, mul_pos this h_small]
  have h1 : Ne_h * (T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small) =
      T_total * Ne_small * Ne_large := by
    field_simp at h_harmonic ⊢; linarith
  -- Key algebraic identity (Cauchy-Schwarz for two terms):
  have identity :
      (T_bottleneck * Ne_small + (T_total - T_bottleneck) * Ne_large) *
      (T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small) =
      T_total * (T_total * Ne_small * Ne_large) +
      T_bottleneck * (T_total - T_bottleneck) * (Ne_large - Ne_small) ^ 2 := by ring
  -- Multiply goal by D > 0: reduces to T²·Ne_s·Ne_l < P·D
  have hmul :
      Ne_h * T_total * (T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small) <
      (T_bottleneck * Ne_small + (T_total - T_bottleneck) * Ne_large) *
      (T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small) := by
    -- LHS = T · (Ne_h · D) = T · (T · Ne_s · Ne_l) by h1
    have lhs_eq :
        Ne_h * T_total * (T_bottleneck * Ne_large + (T_total - T_bottleneck) * Ne_small) =
        T_total * (T_total * Ne_small * Ne_large) := by linear_combination T_total * h1
    rw [lhs_eq, identity]
    -- Now: T²·Ne_s·Ne_l < T²·Ne_s·Ne_l + T_b·(T-T_b)·(Ne_l - Ne_s)²
    linarith [mul_pos (mul_pos h_Tb_pos (show (0:ℝ) < T_total - T_bottleneck by linarith))
                       (sq_pos_of_pos (show (0:ℝ) < Ne_large - Ne_small by linarith))]
  exact (mul_lt_mul_iff_left₀ hD_pos).mp hmul

/-- **Equilibrium Fst lies strictly in `(0,1)` once mutation or migration is present.**
The conjunction of `fstEquilibrium_pos` and `fstEquilibrium_lt_one`.

This was `unified_portability_between_zero_and_one`, "portability at equilibrium is
strictly between 0 and 1 when all forces are present".  It bounds `fstEquilibrium`, and
Fst is not portability: no metric, predictor or transported `R²` occurs in it.  Its three
hypotheses have become the one the proof actually uses — `0 < t_div` was never used, and
`0 < θ` and `0 < M` separately are stronger than the `0 < θ + M` that
`fstEquilibrium_lt_one` needs, so "all forces present" was decoration. -/
theorem fstEquilibrium_mem_Ioo
    (p : EvolutionaryParameters) (h_forces : 0 < p.theta + p.bigM) :
    0 < fstEquilibrium p ∧ fstEquilibrium p < 1 :=
  ⟨fstEquilibrium_pos p, fstEquilibrium_lt_one p h_forces⟩

end EvolutionaryCoordinates

/-! ## End-to-End: From Population Genetics to Clinical Accuracy Metrics

This section builds the evolutionary side of the deployment pipeline from
evolutionary primitives (Ne, μ, m, r, t) to clinical accuracy coordinates
(`R²`, AUC, Brier score) once an explicit target signal variance is supplied.
Time since divergence enters through the evolutionary coordinates only.

**The chain:**
1. Evolutionary parameters expose primitive divergence/sharing coordinates
   (`Fst(t)`, LD, mutation-history, migration-history)
2. These coordinates remain a coarse record only; DGP does not assume that they
   are independent, multiplicatively separable, or jointly sufficient for a
   biological portability law
3. A separate mechanistic transport theorem supplies explicit target signal variance
4. That target signal variance maps to target `R²(t)`, AUC(t), and Brier(t)

These coarse coordinates change over time as Fst grows, LD changes, mutation
changes shared ancestral content, and migration changes sharing history. The
deployed metrics in this section are then read off from exact coordinate maps
applied to an explicit target signal variance supplied elsewhere.

### Key scope note
An `EvolutionaryParameters` structure determines only the primitive
evolutionary coordinates in this file, and an observational context adds residual
scale and disease prevalence for metric evaluation. That is enough for exact
algebra on the chosen coordinates, but it is not by itself a full SNP/LD
state-space model of transport. The mechanistic transport objects live
downstream in
`PortabilityDrift.CrossPopulationMetricModel`,
`PortabilityDrift.sourceWeightedTagScore`,
`PortabilityDrift.r2FromSourceWeights`, and
`TransferLearningPGS.transportedTargetR2_eq_ldRgSq_mul_targetH2_sharedLD`.
-/

section EndToEndMetrics

/-- Extended evolutionary parameters that include the observational context:
    residual variance and disease prevalence for metric evaluation. -/
structure PGSEvolutionaryModel extends EvolutionaryParameters where
  /-- Environmental (non-genetic) variance. -/
  V_E : ℝ
  /-- Disease prevalence (for binary trait metrics). -/
  prevalence : ℝ
  V_E_pos : 0 < V_E
  prev_pos : 0 < prevalence
  prev_lt_one : prevalence < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def PGSEvolutionaryModel.witness : PGSEvolutionaryModel where
  toEvolutionaryParameters := EvolutionaryParameters.witness
  V_E := 1
  prevalence := 1 / 2
  V_E_pos := by norm_num
  prev_pos := by norm_num
  prev_lt_one := by norm_num

/-- Access the underlying evolutionary parameters. -/
noncomputable def PGSEvolutionaryModel.toEvo (m : PGSEvolutionaryModel) :
    EvolutionaryParameters := m.toEvolutionaryParameters

/-! ### Step 1: Transient Fst as a function of time

For populations that have not yet reached equilibrium, Fst(t) grows from 0
toward the equilibrium value. We use the transient formula derived in
PopulationGeneticsFoundations from the heterozygosity recurrence with mutation.

Fst(t) = Fst_eq × (1 - λ^t) where λ = (1-1/(2N))(1-θ/(2N))

At equilibrium (t → ∞), Fst → Fst_eq = 1/(1+θ+M).
-/

/-- Per-generation heterozygosity retention factor under drift + mutation.
    λ = (1 - 1/(2Ne)) × (1 - θ/(2Ne))
    Derived from the Wright-Fisher recurrence with mutation:
    H(t+1) = (1-1/(2N)) × (1-μ)² × H(t) + mutation_input
    where (1-μ)² ≈ 1 - 2μ = 1 - θ/(2N).

    Empirical status: UNTESTED. -/
noncomputable def PGSEvolutionaryModel.hetDecayFactor (m : PGSEvolutionaryModel) : ℝ :=
  hetDecayFromScaled m.Ne m.theta

/-- **Transient Fst(t)**: Fst as a function of divergence time.
    Fst(t) = Fst_eq × (1 - λ^t)
    where Fst_eq = 1/(1+θ+M) and λ = hetDecayFactor.

    At t=0: Fst = 0 (no divergence yet).
    As t → ∞: Fst → Fst_eq (equilibrium).

    DERIVED from the heterozygosity recurrence H(t) = H* + (H₀ - H*) × λ^t
    and Fst(t) = 1 - H(t)/H₀. See PopulationGeneticsFoundations.lean.

    Empirical status: UNTESTED. -/
noncomputable def PGSEvolutionaryModel.fstTransient (m : PGSEvolutionaryModel) : ℝ :=
  fstEquilibrium m.toEvo * (1 - m.hetDecayFactor ^ (Nat.floor m.t_div))

/-! ### Step 2: Primitive evolutionary coordinate summaries

The four coarse coordinates are kept side by side:

- allele-frequency divergence/sharing coordinate
- LD-history coordinate
- mutation-history coordinate
- migration-history coordinate

This block does not multiply them into a single trait-level transport scalar,
does not treat them as independent mechanisms, does not reconstruct source
signal from source `R²`, and does not derive target deployed metrics from
source `R²` plus any global retention factor.
-/

/-! ### Scope of this deployment block

The next definitions intentionally stop short of an end-to-end portability law.
They provide:

- primitive evolutionary coordinate summaries; and
- generic metric coordinate maps once an explicit target signal variance is
  supplied.

They do **not** evolve SNP weights, tag/causal covariance matrices, or target
effect-size vectors directly. The lower-level SNP/LD-aware transport objects
live in:

- `PortabilityDrift.CrossPopulationMetricModel`, where the named drivers are
  source/target tag LD, tag-causal alignment, source/target effect vectors,
  source/target context cross-covariances, and explicit additive target-side
  residual losses for broken tagging, ancestry-specific LD distortion, and
  source-specific overfit;
- `PortabilityDrift.targetEffectHeterogeneity`, where cross-population effect
  mismatch is a locus-resolved vector `β_target - β_source`, not a scalar
  retention coordinate;
- `PortabilityDrift.taggingProjection_target_eq_source_effect_plus_effectHeterogeneity`,
  where the transported target signal is decomposed into the part induced by
  source-stable effects plus the separate projection of target-effect
  heterogeneity;
- `PortabilityDrift.betaTargetAt`, where time-varying target effects are
  generated from source effects plus an explicit generation-indexed
  heterogeneity path;
- `PortabilityDrift.sourceWeightedTagScore`, which is the explicit SNP-level
  score equation applying source-learned weights to any source or target
  tag-genotype state;
- `PortabilityDrift.r2FromSourceWeights`, where transported source weights
  are evaluated against that full explicit state through the target LD and
  target tag-to-causal covariance operators; and
- `PortabilityDrift.targetMetricProfileFromSourceWeights`, where the deployed
  `R²`/AUC/Brier profile is bundled directly from that mechanistic score
  equation; and
- `TransferLearningPGS.transportedTargetR2_eq_ldRgSq_mul_targetH2_sharedLD`,
  where transport is expressed in source/target effect vectors under a shared
  LD kernel.

Those mechanistic theorems are now the required route for any biological claim
about target `R²`, AUC, or Brier.
-/

/-! ### Canonical transported metric surface

`TransportedMetrics` is the single canonical forward map from:

- explicit target signal variance
- baseline residual variance scale
- explicit additive target-side penalty budget
- prevalence

to the deployed target metrics (`R²`, AUC, Brier). Other files should expose
specialized observable or methodological wrappers only via exact specialization
lemmas back to this namespace.
-/

namespace TransportedMetrics

/-- Closed-form conversion from signal variance to deployed `R²` at fixed residual scale.

    Empirical status: UNTESTED. -/
noncomputable def r2FromSignalVariance (vSignal vNoise : ℝ) : ℝ :=
  vSignal / (vSignal + vNoise)

/-- **r2FromSignalVariance where its denominator vanishes, named.** The guard `vSignal + vNoise` is
zero at `vSignal = 0`, `vNoise = 0`. With neither signal nor noise there is no variance to
explain. Lean returns `0` there rather than the value the modelled quantity takes, and no type
error marks the point. Consumers must require `vSignal + vNoise ≠ 0`. -/
theorem r2FromSignalVariance_at_vsignal0vnoise0_is_junk :
    r2FromSignalVariance 0 0 = 0 := by
  unfold r2FromSignalVariance
  norm_num

/-- **The explained-variance ratio really is the `R²` of a data-generating process** —
under a regime that is now written down rather than assumed.

Two hypotheses carry the whole modelling content, and both are discharged by the caller:

* `h_additive` says the outcome's conditional mean tracks the signal one for one, i.e. the
  outcome is the signal plus a residual uncorrelated with it. This is the additive-noise
  regime. Outside it the covariance is not the signal variance and the ratio below is not
  an `R²` — it is a number.
* `h_split` says the outcome variance decomposes as signal plus `V_E`, which is what makes
  `V_E` deserve the name "environmental variance" rather than being an arbitrary second
  argument.

This is the bridge the development was missing. `presentDayR2`, and with it every drift,
mutation-drift and generational `R²`, is `r2FromSignalVariance` applied to a different signal
variance, so each of them inherits this theorem instead of needing its own. Before it,
the statement "this quotient is the `R²` of the process" was not something the corpus
could express, let alone check: the quotient was a definition, and a definition cannot be
wrong. -/
theorem r2FromSignalVariance_eq_rsquared {k : ℕ} [Fintype (Fin k)]
    {dgp : DataGeneratingProcess k} {signal : Predictor k}
    (V_signal V_E : ℝ)
    (h_signal : signalVariance dgp signal = V_signal)
    (h_additive : signalOutcomeCovariance dgp signal = V_signal)
    (h_split : outcomeMeanVariance dgp = V_signal + V_E)
    (h_signal_pos : 0 < V_signal) (h_outcome_pos : 0 < V_signal + V_E) :
    r2FromSignalVariance V_signal V_E = rsquared dgp signal dgp.trueExpectation := by
  rw [rsquared_eq_process_moments dgp signal,
    h_signal, h_additive, h_split]
  unfold r2FromSignalVariance
  have hs : V_signal ≠ 0 := ne_of_gt h_signal_pos
  have ho : V_signal + V_E ≠ 0 := ne_of_gt h_outcome_pos
  field_simp


/-- **AUC of the equal-variance Gaussian model**, from signal and residual
    variances.

    **Not the liability-threshold AUC.** The docstring here used to call it
    that. The liability-threshold AUC depends on prevalence, which this
    signature cannot express, and its sibling
    `equalVarianceGaussianAUCFromSignalVariance` -- which now calls this body --
    carries the marker recording that the liability reading is falsified. Two
    copies of one formula had drifted to opposite claims about which quantity
    it is; that is why they are one definition now.

    For positive residual variance this is `Φ(√(vSignal / (2 · vNoise)))`.
    At `vNoise = 0`, positive signal is perfect prediction and therefore has
    AUC `1`; the zero-signal degenerate case is assigned `Φ 0`. This explicit
    boundary prevents total real division from silently mapping a perfect
    predictor to chance discrimination.

    Empirical status: VALIDATED for the equal-variance Gaussian model at
    positive residual variance. Measured against Monte-Carlo of the underlying
    two-Gaussian model, 200000 draws per point: predicted against simulated
    `0.760250/0.760040`, `0.921350/0.921505`, `0.999797/0.999820`,
    `1.000000/1.000000` at `vNoise = 1, 0.25, 0.04, 0.01` with `vSignal = 1`;
    largest absolute difference `2.1e-4`. Power: the prediction spans `0.760`
    to `1.000` across that design, so a wrong functional form of this shape
    would separate. The zero-noise boundary is fixed analytically by the
    perfect-discrimination value.

    Correct as it stands: this is a genuine two-Gaussian model and the
    validation above is against that model, not against a dichotomised trait.
    The binary-trait counterpart is
    `PortabilityDrift.liabilityThresholdAUCFromExplainedR2`, which takes a
    prevalence; do not substitute this one for it. -/
noncomputable def equalVarianceGaussianAUCFromSignalVariance (vSignal vNoise : ℝ) : ℝ :=
  if vNoise = 0 then if 0 < vSignal then 1 else Phi 0
  else Phi (Real.sqrt (vSignal / (2 * vNoise)))

/-- Away from zero residual variance, the AUC chart is its Gaussian closed form. -/
theorem equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise
    (vSignal vNoise : ℝ) (h_noise : vNoise ≠ 0) :
    equalVarianceGaussianAUCFromSignalVariance vSignal vNoise =
      Phi (Real.sqrt (vSignal / (2 * vNoise))) := by
  simp [equalVarianceGaussianAUCFromSignalVariance, h_noise]

/-- Positive signal with no residual noise gives perfect discrimination. -/
@[simp] theorem equalVarianceGaussianAUCFromSignalVariance_zero_noise_of_pos
    (vSignal : ℝ) (h_signal : 0 < vSignal) :
    equalVarianceGaussianAUCFromSignalVariance vSignal 0 = 1 := by
  simp [equalVarianceGaussianAUCFromSignalVariance, h_signal]

/-- With no signal, the equal-variance chart gives chance discrimination. -/
@[simp] theorem equalVarianceGaussianAUCFromSignalVariance_zero_signal
    (vNoise : ℝ) :
    equalVarianceGaussianAUCFromSignalVariance 0 vNoise = Phi 0 := by
  by_cases h_noise : vNoise = 0
  · simp [equalVarianceGaussianAUCFromSignalVariance, h_noise]
  · simp [equalVarianceGaussianAUCFromSignalVariance, h_noise]

/-! AUC is not determined by second moments.  Consequently this module exposes the
equal-variance Gaussian chart as a numerical function only; it does not offer a theorem
identifying that chart with a process AUC.  Such an identification must be proved from an
explicit liability distribution, not supplied as a record field. -/

/-- Exact calibrated Bernoulli Brier risk from prevalence and explained-risk fraction. -/
def calibratedBrier (π r2 : ℝ) : ℝ :=
  π * (1 - π) * (1 - r2)

/-- **Anchors of the calibrated Brier risk.** A perfectly explanatory score reaches zero risk;
an uninformative one falls back on the prevalence variance. The two together pin the linear
dependence on `r2`, which one anchor alone would not. -/
theorem calibratedBrier_anchors (π : ℝ) :
    calibratedBrier π 1 = 0 ∧ calibratedBrier π 0 = π * (1 - π) := by
  constructor <;> unfold calibratedBrier <;> ring

/-- The risk is symmetric under exchanging a disease for its complement at fixed explained
signal: prevalence enters only through `π(1-π)`. -/
theorem calibratedBrier_prevalence_symm (π r2 : ℝ) :
    calibratedBrier (1 - π) r2 = calibratedBrier π r2 := by
  unfold calibratedBrier; ring

/-- Exact calibrated Bernoulli Brier risk from prevalence, explained signal
variance, and residual variance.

This is the direct moment form of the calibrated Brier coordinate. It is not
defined by first constructing transported `R²`; any equality to the `R²`
chart is a derived algebraic identity.

    Denotes: the reading its name carries. The same formula appears under
    names from 'rate', 'variance', and the formula alone does not fix which is meant. -/
noncomputable def calibratedBrierFromVariances (π vSignal vResidual : ℝ) : ℝ :=
  π * (1 - π) * (1 - vSignal / (vSignal + vResidual))

/-- **A residual-free signal drives the calibrated risk to zero.** With no residual variance the
explained fraction is one and the Brier risk vanishes, which is the endpoint that pins the
`1 - r²` factor: a body missing it would leave the prevalence variance behind. -/
theorem calibratedBrierFromVariances_no_residual (π vSignal : ℝ) (hv : vSignal ≠ 0) :
    calibratedBrierFromVariances π vSignal 0 = 0 := by
  unfold calibratedBrierFromVariances
  rw [add_zero, div_self hv]
  ring

@[simp] theorem calibratedBrierFromVariances_eq_chart
    (π vSignal vResidual : ℝ) :
    calibratedBrierFromVariances π vSignal vResidual =
      calibratedBrier π (r2FromSignalVariance vSignal vResidual) := by
  rfl

/-- **The calibrated Brier closed form is the Brier risk at the process's own `R²`.**

Nothing new is assumed here beyond `r2FromSignalVariance_eq_rsquared`: the same
additive-noise regime and variance split, discharged once, carry the Brier family across
too. That is the whole reason for anchoring the quotient rather than each metric
separately - `calibratedBrierFromVariances` was already the calibrated Brier evaluated at
`r2FromSignalVariance`, so the moment the quotient became the process `R²`, so did this.

The prevalence `π` is untouched by any of it, which is the honest reading: Brier moves
with prevalence for reasons that have nothing to do with how well the score predicts. -/
theorem calibratedBrierFromVariances_eq_rsquared_form {k : ℕ} [Fintype (Fin k)]
    {dgp : DataGeneratingProcess k} {signal : Predictor k}
    (V_signal π V_E : ℝ)
    (h_signal : signalVariance dgp signal = V_signal)
    (h_additive : signalOutcomeCovariance dgp signal = V_signal)
    (h_split : outcomeMeanVariance dgp = V_signal + V_E)
    (h_signal_pos : 0 < V_signal) (h_outcome_pos : 0 < V_signal + V_E) :
    calibratedBrierFromVariances π V_signal V_E =
      calibratedBrier π (rsquared dgp signal dgp.trueExpectation) := by
  rw [calibratedBrierFromVariances_eq_chart,
    r2FromSignalVariance_eq_rsquared V_signal V_E h_signal h_additive h_split
      h_signal_pos h_outcome_pos]

/-- Explicit additive irreducible target-side residual-loss budget.
These penalties are not compressed into a single multiplicative transport
factor. They represent irreducible degradation from broken tagging,
ancestry-specific LD distortion, source-specific overfit, and target-only
phenotype variance generated by novel causal mutations that are not captured by
the transported source score. -/
structure IrreducibleTargetPenalty where
  brokenTagging : ℝ
  ancestrySpecificLD : ℝ
  sourceSpecificOverfit : ℝ
  novelUntaggablePhenotype : ℝ
  brokenTagging_nonneg : 0 ≤ brokenTagging
  ancestrySpecificLD_nonneg : 0 ≤ ancestrySpecificLD
  sourceSpecificOverfit_nonneg : 0 ≤ sourceSpecificOverfit
  novelUntaggablePhenotype_nonneg : 0 ≤ novelUntaggablePhenotype

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def IrreducibleTargetPenalty.witness : IrreducibleTargetPenalty where
  brokenTagging := 0
  ancestrySpecificLD := 0
  sourceSpecificOverfit := 0
  novelUntaggablePhenotype := 0
  brokenTagging_nonneg := le_refl 0
  ancestrySpecificLD_nonneg := le_refl 0
  sourceSpecificOverfit_nonneg := le_refl 0
  novelUntaggablePhenotype_nonneg := le_refl 0

/-- Total additive target-side residual-loss budget. -/
noncomputable def IrreducibleTargetPenalty.total
    (penalty : IrreducibleTargetPenalty) : ℝ :=
  penalty.brokenTagging +
    penalty.ancestrySpecificLD +
    penalty.sourceSpecificOverfit +
    penalty.novelUntaggablePhenotype

/-- **Removing three components leaves the fourth.** The budget is additive across its four
named sources, which is what makes attributing a share to any one of them meaningful; a body
that weighted them would satisfy the nonnegativity results and not this. -/
theorem IrreducibleTargetPenalty.total_sub_three (penalty : IrreducibleTargetPenalty) :
    penalty.total - penalty.brokenTagging - penalty.ancestrySpecificLD
      - penalty.sourceSpecificOverfit = penalty.novelUntaggablePhenotype := by
  unfold IrreducibleTargetPenalty.total
  ring

theorem IrreducibleTargetPenalty.total_nonneg
    (penalty : IrreducibleTargetPenalty) :
    0 ≤ penalty.total := by
  unfold IrreducibleTargetPenalty.total
  linarith [penalty.brokenTagging_nonneg, penalty.ancestrySpecificLD_nonneg,
    penalty.sourceSpecificOverfit_nonneg, penalty.novelUntaggablePhenotype_nonneg]

/-- Canonical bundled deployed metrics from an explicit target signal variance. -/
structure Profile where
  r2 : ℝ
  auc : ℝ
  brier : ℝ

@[ext] theorem Profile.ext {p q : Profile}
    (hr2 : p.r2 = q.r2) (hauc : p.auc = q.auc) (hbrier : p.brier = q.brier) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Canonical bundled deployed metrics from explicit target signal and residual
    variances.

    This namespace intentionally stops at coordinate maps. It does not infer a
    target signal variance from source `R²` plus any global transport scalar;
    that target signal must come from a separate mechanistic theorem, and any
    irreducible target-side loss must be supplied explicitly as an additive
    penalty budget. -/
noncomputable def profileFromSignalVariance
    (π vNoise vSignal : ℝ) : Profile where
  r2 := r2FromSignalVariance vSignal vNoise
  auc := equalVarianceGaussianAUCFromSignalVariance vSignal vNoise
  brier := calibratedBrierFromVariances π vSignal vNoise

@[simp] theorem profileFromSignalVariance_r2
    (π vNoise vSignal : ℝ) :
    (profileFromSignalVariance π vNoise vSignal).r2 =
      r2FromSignalVariance vSignal vNoise := by
  rfl

@[simp] theorem profileFromSignalVariance_auc
    (π vNoise vSignal : ℝ) :
    (profileFromSignalVariance π vNoise vSignal).auc =
      equalVarianceGaussianAUCFromSignalVariance vSignal vNoise := by
  rfl

@[simp] theorem profileFromSignalVariance_brier
    (π vNoise vSignal : ℝ) :
    (profileFromSignalVariance π vNoise vSignal).brier =
      calibratedBrierFromVariances π vSignal vNoise := by
  rfl

theorem profileFromSignalVariance_brier_eq_chart
    (π vNoise vSignal : ℝ) :
    (profileFromSignalVariance π vNoise vSignal).brier =
      calibratedBrier π (r2FromSignalVariance vSignal vNoise) := by
  rw [profileFromSignalVariance_brier, calibratedBrierFromVariances_eq_chart]

/-- Canonical bundled deployed metrics from explicit target signal variance,
baseline residual scale, and an explicit additive target-side penalty budget. -/
noncomputable def profileFromSignalVarianceWithPenalty
    (π vNoise vSignal : ℝ) (penalty : IrreducibleTargetPenalty) : Profile :=
  profileFromSignalVariance π (vNoise + penalty.total) vSignal

@[simp] theorem profileFromSignalVarianceWithPenalty_r2
    (π vNoise vSignal : ℝ) (penalty : IrreducibleTargetPenalty) :
    (profileFromSignalVarianceWithPenalty π vNoise vSignal penalty).r2 =
      r2FromSignalVariance vSignal (vNoise + penalty.total) := by
  rfl

@[simp] theorem profileFromSignalVarianceWithPenalty_auc
    (π vNoise vSignal : ℝ) (penalty : IrreducibleTargetPenalty) :
    (profileFromSignalVarianceWithPenalty π vNoise vSignal penalty).auc =
      equalVarianceGaussianAUCFromSignalVariance vSignal (vNoise + penalty.total) := by
  rfl

@[simp] theorem profileFromSignalVarianceWithPenalty_brier
    (π vNoise vSignal : ℝ) (penalty : IrreducibleTargetPenalty) :
    (profileFromSignalVarianceWithPenalty π vNoise vSignal penalty).brier =
      calibratedBrierFromVariances π vSignal (vNoise + penalty.total) := by
  rfl

theorem profileFromSignalVarianceWithPenalty_brier_eq_chart
    (π vNoise vSignal : ℝ) (penalty : IrreducibleTargetPenalty) :
    (profileFromSignalVarianceWithPenalty π vNoise vSignal penalty).brier =
      calibratedBrier π (r2FromSignalVariance vSignal (vNoise + penalty.total)) := by
  rw [profileFromSignalVarianceWithPenalty_brier, calibratedBrierFromVariances_eq_chart]

end TransportedMetrics

/-- Canonical primitive evolutionary coordinate summary for the observationally
augmented model. DGP records these coordinates separately and does not collapse
them into a single transport law. -/
noncomputable def PGSEvolutionaryModel.coordinateSummary
    (m : PGSEvolutionaryModel) : EvolutionaryCoordinateSummary where
  alleleFreqCoordinate := 1 - m.fstTransient
  sharedLDCoordinate := sharedLDRetention m.toEvo
  ancestralVariantCoordinate := mutationLDErosion m.toEvo
  migrationCoordinate := migrationLDBoost m.toEvo

@[simp] theorem PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate
    (m : PGSEvolutionaryModel) :
    m.coordinateSummary.alleleFreqCoordinate = 1 - m.fstTransient := by
  rfl

@[simp] theorem PGSEvolutionaryModel.coordinateSummary_sharedLDCoordinate
    (m : PGSEvolutionaryModel) :
    m.coordinateSummary.sharedLDCoordinate = sharedLDRetention m.toEvo := by
  rfl

@[simp] theorem PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate
    (m : PGSEvolutionaryModel) :
    m.coordinateSummary.ancestralVariantCoordinate = mutationLDErosion m.toEvo := by
  rfl

@[simp] theorem PGSEvolutionaryModel.coordinateSummary_migrationCoordinate
    (m : PGSEvolutionaryModel) :
    m.coordinateSummary.migrationCoordinate = migrationLDBoost m.toEvo := by
  rfl

/-- Fully expanded evolutionary coordinate summary. Each field is a separate
coarse coordinate, not a joint portability law. -/
theorem PGSEvolutionaryModel.coordinateSummary_explicit
    (m : PGSEvolutionaryModel) :
    m.coordinateSummary =
      { alleleFreqCoordinate :=
          1 - fstEquilibrium m.toEvo * (1 - m.hetDecayFactor ^ (Nat.floor m.t_div))
        sharedLDCoordinate := Real.exp (-2 * m.recomb * m.t_div)
        ancestralVariantCoordinate := Real.exp (-m.theta * m.tau)
        migrationCoordinate := 1 + m.bigM * m.tau / (1 + m.bigM) } := by
  ext <;>
    simp [PGSEvolutionaryModel.coordinateSummary, PGSEvolutionaryModel.fstTransient,
      PGSEvolutionaryModel.toEvo,
      sharedLDRetention, mutationLDErosion, migrationLDBoost, fstEquilibrium]

/-- Monotonicity of `Phi`, a corollary of `strictMono_Phi` in `Probability`. -/
theorem Phi_monotone : Monotone Phi := strictMono_Phi.monotone

/-! ### Step 3: Metric evaluation from explicit target signal and additive losses

The rigorous interface now stops at the component summaries above. This file
does not derive a target signal variance from source `R²`; any target metric
claim must supply:

- an explicit target signal variance from a separate mechanistic transport
  theorem; and
- an explicit additive target-side penalty budget for broken tagging,
  ancestry-specific LD distortion, and source-specific overfit. -/

/-- Canonical deployed metric profile from an explicit target signal variance
and an explicit additive target-side penalty budget. -/
noncomputable def PGSEvolutionaryModel.metricProfileFromTargetSignalWithPenalty
    (m : PGSEvolutionaryModel) (vSignalTarget : ℝ)
    (penalty : TransportedMetrics.IrreducibleTargetPenalty) :
    TransportedMetrics.Profile :=
  TransportedMetrics.profileFromSignalVarianceWithPenalty
    m.prevalence m.V_E vSignalTarget penalty

@[simp] theorem PGSEvolutionaryModel.metricProfileFromTargetSignalWithPenalty_r2
    (m : PGSEvolutionaryModel) (vSignalTarget : ℝ)
    (penalty : TransportedMetrics.IrreducibleTargetPenalty) :
    (m.metricProfileFromTargetSignalWithPenalty vSignalTarget penalty).r2 =
      TransportedMetrics.r2FromSignalVariance vSignalTarget (m.V_E + penalty.total) := by
  rfl

@[simp] theorem PGSEvolutionaryModel.metricProfileFromTargetSignalWithPenalty_auc
    (m : PGSEvolutionaryModel) (vSignalTarget : ℝ)
    (penalty : TransportedMetrics.IrreducibleTargetPenalty) :
    (m.metricProfileFromTargetSignalWithPenalty vSignalTarget penalty).auc =
      TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance vSignalTarget (m.V_E +
          penalty.total) := by
  rfl

@[simp] theorem PGSEvolutionaryModel.metricProfileFromTargetSignalWithPenalty_brier
    (m : PGSEvolutionaryModel) (vSignalTarget : ℝ)
    (penalty : TransportedMetrics.IrreducibleTargetPenalty) :
    (m.metricProfileFromTargetSignalWithPenalty vSignalTarget penalty).brier =
      TransportedMetrics.calibratedBrier m.prevalence
        (TransportedMetrics.r2FromSignalVariance vSignalTarget (m.V_E + penalty.total)) := by
  simpa [PGSEvolutionaryModel.metricProfileFromTargetSignalWithPenalty] using
    TransportedMetrics.profileFromSignalVarianceWithPenalty_brier_eq_chart
      m.prevalence m.V_E vSignalTarget penalty

/-! ### Step 4: Coordinate-Rate Summaries

The evolutionary block records per-force rate coordinates only. These rates are
useful for comparing the timescales of distinct population-genetic drivers, but
they are not added or multiplied into a single portability law. -/

/-- Allele-frequency divergence rate summary from the transient `F_ST`
coordinate.

    Empirical status: UNTESTED. -/
noncomputable def alleleFreqDivergenceRate (Ne mu m_rate : ℝ) : ℝ :=
  let theta := 4 * Ne * mu
  let bigM := 4 * Ne * m_rate
  1 / (2 * Ne * (1 + theta + bigM))

/-- **The allele-frequency divergence rate at zero effective size, named.** Drift is
instantaneous in an empty population, so the divergence rate diverges. The divisor is zero and
Lean returns `0`: no divergence at all, indistinguishable from an infinite population. Scaled
mutation and migration are themselves multiplied by `Ne`, so they vanish too and the denominator
carries no trace of the degeneracy. Consumers must require `Ne ≠ 0`. -/
theorem alleleFreqDivergenceRate_zero_population_is_junk (mu m_rate : ℝ) :
    alleleFreqDivergenceRate 0 mu m_rate = 0 := by
  unfold alleleFreqDivergenceRate
  norm_num

/-- **With neither mutation nor migration the rate is pure drift.** This is the reference point
that fixes the `2Ne`, which no scale-free property of the formula can. -/
theorem alleleFreqDivergenceRate_neutral_isolated (Ne : ℝ) :
    alleleFreqDivergenceRate Ne 0 0 = 1 / (2 * Ne) := by
  unfold alleleFreqDivergenceRate
  norm_num

/-- **A second reference point, where the scaled mutation rate is one.**

`alleleFreqDivergenceRate_neutral_isolated` fixes the outer `2 * Ne` and nothing else: at zero
mutation and zero migration every body of the form `1 / (2 Ne (1 + c1 theta + c2 bigM))` agrees,
whatever `c1` and `c2` are. Evaluating where `theta = 1` separates them, which is what a
reference point has to do to be worth stating -- it only pins what varies at that point. -/
theorem alleleFreqDivergenceRate_unit_theta (Ne : ℝ) (h : Ne ≠ 0) :
    alleleFreqDivergenceRate Ne (1 / (4 * Ne)) 0 = 1 / (4 * Ne) := by
  unfold alleleFreqDivergenceRate
  field_simp
  ring

/-- LD breakage rate from recombination.

    Empirical status: UNTESTED. -/
noncomputable def ldBreakageRate (r : ℝ) : ℝ := 2 * r


/-- LD breakage dominates the allele-frequency divergence rate when
recombination exceeds the drift timescale. This is a comparison of component
rates only, not a theorem about total portability. -/
theorem ld_breakage_dominates_alleleFreq_divergence
    (Ne mu m_rate r : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu) (hm : 0 ≤ m_rate)
    (h_ld_fast : 1 / (2 * Ne) < 2 * r) :
    alleleFreqDivergenceRate Ne mu m_rate < ldBreakageRate r := by
  unfold alleleFreqDivergenceRate ldBreakageRate
  have denom_pos : 0 < 2 * Ne * (1 + 4 * Ne * mu + 4 * Ne * m_rate) := by positivity
  calc 1 / (2 * Ne * (1 + 4 * Ne * mu + 4 * Ne * m_rate))
      ≤ 1 / (2 * Ne) := by
        apply one_div_le_one_div_of_le (by linarith)
        have : 0 ≤ 4 * Ne * mu := by positivity
        have : 0 ≤ 4 * Ne * m_rate := by positivity
        nlinarith
    _ < 2 * r := h_ld_fast

/-! ### Step 8: Coordinate comparisons inside the deployment summary

Within this block, deployed `R²` and Nagelkerke-style quantities are different
coordinates on transported signal plus any explicitly supplied calibration
factor. The theorems below are therefore coordinate facts, not a general
ranking theorem for real-world portability across distinct metrics. -/


end EndToEndMetrics

end AllClaims

end Calibrator
