/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- `Finset.sum_nonneg` and `Finset.single_le_sum` live here, not in
-- `Algebra.BigOperators.Fin`; without this import they resolve as unknown constants and
-- `degradation_nonneg` / `degradation_eq_zero_iff` fail to elaborate.
import Calibrator.GenerativePortabilityLaw
import Calibrator.TransportedMinimax

namespace Calibrator

open scoped BigOperators

/-!
# Task-relative spectral degradation

This is the finite-frequency version of the stationary readout identity.  A model supplies
the feature spectrum `σ`, feature--target cross-spectrum `c`, and target power at each
frequency bin.  Its population-optimal linear filter is `c/σ`.  Completing the square
proves that evaluating the source-optimal filter under the target model costs exactly

`∑ₛ |c_source/σ_source - c_target/σ_target|² σ_target`.

The formula is deliberately **directed** and **task weighted**.  In genetics the bins can
be LD-frequency bands: long-horizon ancestry structure loads low frequencies, whereas
short haplotype or imputation tasks can load high frequencies.  The reversal theorem at
the end shows why no single monotone scalar of population shift can rank both tasks.

No Szegő convergence rate is asserted here.  Passing from this exact finite identity to a
Toeplitz limit needs symbol regularity, a spectrum bounded away from zero, and explicit
control of boundary terms; bounded variation alone does not silently provide all three.
-/

/-- Second-order spectral data for a finite family of frequency bands. -/
structure FiniteSpectralModel (Band : Type*) where
  featureSpectrum : Band → ℝ
  crossSpectrum : Band → ℝ
  targetPower : Band → ℝ
  featureSpectrum_pos : ∀ b, 0 < featureSpectrum b

namespace FiniteSpectralModel

variable {Band : Type*} [Fintype Band]

/-- The population-optimal linear coefficient `c/σ` in each band. -/
noncomputable def optimalReadout (P : FiniteSpectralModel Band) (b : Band) : ℝ :=
  P.crossSpectrum b / P.featureSpectrum b

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem optimalReadout_at_zero_denominator_is_junk (P : FiniteSpectralModel Band) (b : Band)
    (hzero : P.featureSpectrum b = 0) :
    optimalReadout P b = 0 := by
  unfold optimalReadout
  rw [hzero, div_zero]


/-- Population quadratic risk of a bandwise linear readout. -/
-- The parentheses are load-bearing. `∑ b, x - y + z` binds the summation to `x` alone,
-- so without them the second and third terms sit outside the binder and their `b` is a
-- free variable -- which is exactly how this definition failed to elaborate.
noncomputable def risk (P : FiniteSpectralModel Band) (readout : Band → ℝ) : ℝ :=
  ∑ b, (P.featureSpectrum b * readout b ^ 2 -
    2 * P.crossSpectrum b * readout b + P.targetPower b)

/-- Directed degradation: excess target risk incurred by transporting the source-optimal
readout instead of refitting the target-optimal readout. -/
noncomputable def degradation (source target : FiniteSpectralModel Band) : ℝ :=
  risk target (optimalReadout source) - risk target (optimalReadout target)

/-- The bandwise density of degradation. This vector is the exact finite analogue of the
degradation measure in a stationary spectral model. -/
noncomputable def degradationProfile (source target : FiniteSpectralModel Band)
    (b : Band) : ℝ :=
  (optimalReadout source b - optimalReadout target b) ^ 2 * target.featureSpectrum b

/-- Degradation for an arbitrary task-specific band weighting. -/
noncomputable def taskDegradation (source target : FiniteSpectralModel Band)
    (taskWeight : Band → ℝ) : ℝ :=
  ∑ b, taskWeight b * degradationProfile source target b

omit [Fintype Band] in
theorem crossSpectrum_eq_mul_optimalReadout (P : FiniteSpectralModel Band) (b : Band) :
    P.crossSpectrum b = P.featureSpectrum b * optimalReadout P b := by
  unfold optimalReadout
  field_simp [ne_of_gt (P.featureSpectrum_pos b)]

/-- **Exact spectral degradation identity.**  No closeness hypothesis and no asymptotic
argument: this is completion of the target quadratic risk around its own optimum. -/
theorem degradation_eq_weighted_readout_distance
    (source target : FiniteSpectralModel Band) :
    degradation source target =
      ∑ b, (optimalReadout source b - optimalReadout target b) ^ 2 *
        target.featureSpectrum b := by
  unfold degradation risk
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [crossSpectrum_eq_mul_optimalReadout target b]
  ring

/-- Ordinary degradation is the total mass of the degradation profile. -/
theorem degradation_eq_sum_profile (source target : FiniteSpectralModel Band) :
    degradation source target = ∑ b, degradationProfile source target b := by
  rw [degradation_eq_weighted_readout_distance]
  rfl

/-- Transport degradation is non-negative. -/
theorem degradation_nonneg (source target : FiniteSpectralModel Band) :
    0 ≤ degradation source target := by
  rw [degradation_eq_weighted_readout_distance]
  exact Finset.sum_nonneg fun b _ ↦
    mul_nonneg (sq_nonneg _) (le_of_lt (target.featureSpectrum_pos b))

/-- On the diagonal there is no transport degradation. -/
@[simp] theorem degradation_self (P : FiniteSpectralModel Band) : degradation P P = 0 := by
  rw [degradation_eq_weighted_readout_distance]
  simp

/-! ### Genotype rescaling, and why this degradation is the scale-free residual

A residual burden attributed to a transported score must not depend on the *units* the
genotypes are carried in. The substitution `g -> c * g`, `beta -> beta / c` — the free
choice between raw dosages and standardised genotypes — leaves the phenotype, the fitted
score and every measured moment unchanged bit for bit.

A quantity built as a **dot product of covariances** fails that test: covariances carry
one factor of the genotype scale, so such a quantity moves by `c ^ 2` while the outcome
variance it is added to does not. That is a dimensional error, not a modelling choice,
and it has been measured elsewhere in this corpus: a residual burden of that shape grows
by exactly `c ^ 2` while the measured `R ^ 2` moves by `0.000e+00`.

`degradation` has the right shape by construction. It is
`sum_b (readout gap) ^ 2 * featureSpectrum`, i.e. `(covariance mismatch) ^ 2 / (feature
variance)` — two factors of the genotype scale upstairs and two downstairs. The two
theorems below prove that, and they are the statement of what the correct invariant form
of a transport residual is: **normalise the covariance mismatch by the feature variance
before adding it to an outcome variance.** -/
noncomputable def rescale (P : FiniteSpectralModel Band) (c : ℝ) (hc : c ≠ 0) :
    FiniteSpectralModel Band where
  featureSpectrum := fun b ↦ c ^ 2 * P.featureSpectrum b
  crossSpectrum := fun b ↦ c * P.crossSpectrum b
  targetPower := P.targetPower
  featureSpectrum_pos := fun b ↦ mul_pos (sq_pos_of_ne_zero hc) (P.featureSpectrum_pos b)

omit [Fintype Band] in
/-- Under `g -> c * g` the optimal readout is `beta / c`: it is scale-covariant, which is
exactly what makes the score itself invariant. -/
theorem optimalReadout_rescale (P : FiniteSpectralModel Band) (c : ℝ) (hc : c ≠ 0)
    (b : Band) :
    optimalReadout (P.rescale c hc) b = optimalReadout P b / c := by
  unfold optimalReadout rescale
  have hfp := ne_of_gt (P.featureSpectrum_pos b)
  field_simp

/-- **Degradation is invariant under a change of genotype coding.** The two factors of `c`
in the squared readout gap cancel the two in the feature spectrum. Any transport residual
that is *not* invariant here is measuring the units, and any repair of such a residual has
to reproduce this normalisation. -/
theorem degradation_rescale (source target : FiniteSpectralModel Band) (c : ℝ) (hc : c ≠ 0) :
    degradation (source.rescale c hc) (target.rescale c hc) = degradation source target := by
  rw [degradation_eq_weighted_readout_distance, degradation_eq_weighted_readout_distance]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [optimalReadout_rescale source c hc b, optimalReadout_rescale target c hc b]
  show (optimalReadout source b / c - optimalReadout target b / c) ^ 2 *
      (c ^ 2 * target.featureSpectrum b) =
    (optimalReadout source b - optimalReadout target b) ^ 2 * target.featureSpectrum b
  field_simp

/-- The same degradation restricted to a selected set of frequency bands. -/
noncomputable def bandDegradation (source target : FiniteSpectralModel Band)
    (bands : Finset Band) : ℝ :=
  ∑ b ∈ bands, (optimalReadout source b - optimalReadout target b) ^ 2 *
    target.featureSpectrum b

/-- **Exact portability criterion.** Transport costs nothing exactly when the source and
target regression ratios `c/σ` agree in every frequency band. Raw feature spectra may
differ: the invariant relevant to this linear task is the optimal readout, not a scalar
distance between populations. -/
theorem degradation_eq_zero_iff (source target : FiniteSpectralModel Band) :
    degradation source target = 0 ↔
      ∀ b, optimalReadout source b = optimalReadout target b := by
  classical
  rw [degradation_eq_weighted_readout_distance]
  constructor
  · intro hsum b
    have hnonneg : ∀ i ∈ (Finset.univ : Finset Band),
        0 ≤ (optimalReadout source i - optimalReadout target i) ^ 2 *
          target.featureSpectrum i := by
      intro i _
      exact mul_nonneg (sq_nonneg _) (le_of_lt (target.featureSpectrum_pos i))
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ b)
    rw [hsum] at hle
    have hterm_nonneg := hnonneg b (Finset.mem_univ b)
    have hterm : (optimalReadout source b - optimalReadout target b) ^ 2 *
        target.featureSpectrum b = 0 := le_antisymm hle hterm_nonneg
    rcases mul_eq_zero.mp hterm with hsquare | hspectrum
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    · exact False.elim ((ne_of_gt (target.featureSpectrum_pos b)) hspectrum)
  · intro hreadout
    apply Finset.sum_eq_zero
    intro b _
    simp [hreadout b]

/-- **Complete finite-band invariant.** Two transported pairs have identical degradation
for every band-weighted linear task exactly when their degradation profiles agree in every
band. Thus the full object is a vector (a measure in the continuum), not a scalar. -/
theorem taskDegradation_eq_forall_iff_profile_eq
    (source₁ target₁ source₂ target₂ : FiniteSpectralModel Band) :
    (∀ taskWeight, taskDegradation source₁ target₁ taskWeight =
        taskDegradation source₂ target₂ taskWeight) ↔
      ∀ b, degradationProfile source₁ target₁ b =
        degradationProfile source₂ target₂ b := by
  classical
  constructor
  · intro hall b
    simpa [taskDegradation] using hall (fun i ↦ if i = b then 1 else 0)
  · intro hprofile taskWeight
    unfold taskDegradation
    apply Finset.sum_congr rfl
    intro b _
    rw [hprofile b]

end FiniteSpectralModel

/-! ## Normalization can reverse a portability ranking -/

/-- **Exact normalization-reversal window.** Let `Dᵢ > 0` be raw degradation and
`Qᵢ > 0` the evaluation-side variance used to normalize it. Pair `1` is worse in raw
degradation but better after normalization exactly when

`1 < D₁ / D₂ < Q₁ / Q₂`.

The right side uses the actual denominators `Q₁,Q₂`. Replacing them by ratios to separate
pair-specific baselines requires an additional equality of those baselines. -/
theorem normalized_degradation_reversal_iff
    (D₁ D₂ Q₁ Q₂ : ℝ) (hD₂ : 0 < D₂)
    (hQ₁ : 0 < Q₁) (hQ₂ : 0 < Q₂) :
    (D₂ < D₁ ∧ D₁ / Q₁ < D₂ / Q₂) ↔
      (1 < D₁ / D₂ ∧ D₁ / D₂ < Q₁ / Q₂) := by
  constructor
  · rintro ⟨hraw, hnorm⟩
    constructor
    · exact (one_lt_div hD₂).2 hraw
    · rw [div_lt_div_iff₀ hD₂ hQ₂]
      rw [div_lt_div_iff₀ hQ₁ hQ₂] at hnorm
      nlinarith
  · rintro ⟨hratio, hwindow⟩
    constructor
    · exact (one_lt_div hD₂).1 hratio
    · rw [div_lt_div_iff₀ hQ₁ hQ₂]
      rw [div_lt_div_iff₀ hD₂ hQ₂] at hwindow
      nlinarith

/-! ## Scalar degradation cannot represent reversing tasks -/

/-- **No common monotone scalar under an ordering reversal.**

If pair 1 degrades more than pair 2 for one task and less for another, there are no scalar
values for the two pairs and monotone task-specific response functions reproducing both
orders.  The theorem makes no continuity or metric assumption: the obstruction is purely
ordinal. -/
theorem no_common_monotone_scalar_of_reversal
    (low₁ low₂ high₁ high₂ : ℝ) (hlow : low₂ < low₁) (hhigh : high₁ < high₂) :
    ¬ ∃ (d₁ d₂ : ℝ) (Φlow Φhigh : ℝ → ℝ),
      Monotone Φlow ∧ Monotone Φhigh ∧
      Φlow d₁ = low₁ ∧ Φlow d₂ = low₂ ∧
      Φhigh d₁ = high₁ ∧ Φhigh d₂ = high₂ := by
  rintro ⟨d₁, d₂, Φlow, Φhigh, hΦlow, hΦhigh, hl₁, hl₂, hh₁, hh₂⟩
  have hnot : ¬ d₁ ≤ d₂ := by
    intro hle
    have hout := hΦlow hle
    rw [hl₁, hl₂] at hout
    linarith
  have hd₂₁ : d₂ ≤ d₁ := le_of_lt (lt_of_not_ge hnot)
  have hout := hΦhigh hd₂₁
  rw [hh₂, hh₁] at hout
  linarith

/-! ## An exact low-band/high-band witness -/

/-- Unit feature spectrum and zero optimal readout on two bands. -/
noncomputable def twoBandBaseline : FiniteSpectralModel (Fin 2) where
  featureSpectrum := ![1, 1]
  crossSpectrum := ![0, 0]
  targetPower := ![0, 0]
  featureSpectrum_pos := by intro b; fin_cases b <;> norm_num

/-- A target shift confined to the low-frequency band. -/
noncomputable def twoBandLowShift (a : ℝ) : FiniteSpectralModel (Fin 2) where
  featureSpectrum := ![1, 1]
  crossSpectrum := ![a, 0]
  targetPower := ![a ^ 2, 0]
  featureSpectrum_pos := by intro b; fin_cases b <;> norm_num

/-- A target shift confined to the high-frequency band. -/
noncomputable def twoBandHighShift (a : ℝ) : FiniteSpectralModel (Fin 2) where
  featureSpectrum := ![1, 1]
  crossSpectrum := ![0, a]
  targetPower := ![0, a ^ 2]
  featureSpectrum_pos := by intro b; fin_cases b <;> norm_num

/-- **The reversal quadruple, computed.**  A low-band shift is visible only to the low
task, and a high-band shift only to the high task.  These are ordinary positive unit
spectra; the reversal is task localization, not a singular construction. -/
theorem twoBand_reversal_values (a : ℝ) :
    FiniteSpectralModel.bandDegradation twoBandBaseline (twoBandLowShift a) {0} = a ^ 2 ∧
    FiniteSpectralModel.bandDegradation twoBandBaseline (twoBandHighShift a) {0} = 0 ∧
    FiniteSpectralModel.bandDegradation twoBandBaseline (twoBandLowShift a) {1} = 0 ∧
    FiniteSpectralModel.bandDegradation twoBandBaseline (twoBandHighShift a) {1} = a ^ 2 := by
  -- All three models have to be unfolded: with only `twoBandBaseline` in the list the
  -- goal reduces to four claims about the *shifted* models' spectra and stalls there.
  simp [FiniteSpectralModel.bandDegradation, FiniteSpectralModel.optimalReadout,
    twoBandBaseline, twoBandLowShift, twoBandHighShift]

/-- Existence of one scalar population-shift score whose monotone task-specific charts
recover both low-band and high-band degradation for the two-band witness.

The predicate lives here, beside the witness it is about, because the theorem below and its
biological consumer in `Calibrator.MetricSpecificPortability` both need it and it was
written out in full in both places -- eight lines of `let`-bound band degradations and the
existential over the two charts, copied. -/
def HasTaskIndependentSpectralPortabilityScalar (a : ℝ) : Prop :=
  let low₁ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandLowShift a) {0}
  let low₂ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandHighShift a) {0}
  let high₁ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandLowShift a) {1}
  let high₂ := FiniteSpectralModel.bandDegradation
    twoBandBaseline (twoBandHighShift a) {1}
  ∃ (d₁ d₂ : ℝ) (Φlow Φhigh : ℝ → ℝ),
    Monotone Φlow ∧ Monotone Φhigh ∧
    Φlow d₁ = low₁ ∧ Φlow d₂ = low₂ ∧
    Φhigh d₁ = high₁ ∧ Φhigh d₂ = high₂

/-- **No task-independent scalar ranks the two genomic-band shifts.**  For any nonzero
shift, pair 1 is strictly worse on the low-frequency task and pair 2 is strictly worse on
the high-frequency task. -/
theorem twoBand_no_common_monotone_scalar (a : ℝ) (ha : a ≠ 0) :
    ¬ HasTaskIndependentSpectralPortabilityScalar a := by
  unfold HasTaskIndependentSpectralPortabilityScalar
  dsimp
  apply no_common_monotone_scalar_of_reversal
  · rw [(twoBand_reversal_values a).1, (twoBand_reversal_values a).2.1]
    exact sq_pos_of_ne_zero ha
  · rw [(twoBand_reversal_values a).2.2.1, (twoBand_reversal_values a).2.2.2]
    exact sq_pos_of_ne_zero ha

end Calibrator
