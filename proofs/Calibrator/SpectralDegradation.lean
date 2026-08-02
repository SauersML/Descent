import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
structure FiniteSpectralModel (Band : Type*) [Fintype Band] where
  featureSpectrum : Band → ℝ
  crossSpectrum : Band → ℝ
  targetPower : Band → ℝ
  featureSpectrum_pos : ∀ b, 0 < featureSpectrum b

namespace FiniteSpectralModel

variable {Band : Type*} [Fintype Band]

/-- The population-optimal linear coefficient `c/σ` in each band. -/
noncomputable def optimalReadout (P : FiniteSpectralModel Band) (b : Band) : ℝ :=
  P.crossSpectrum b / P.featureSpectrum b

/-- Population quadratic risk of a bandwise linear readout. -/
noncomputable def risk (P : FiniteSpectralModel Band) (readout : Band → ℝ) : ℝ :=
  ∑ b, P.featureSpectrum b * readout b ^ 2 -
    2 * P.crossSpectrum b * readout b + P.targetPower b

/-- Directed degradation: excess target risk incurred by transporting the source-optimal
readout instead of refitting the target-optimal readout. -/
noncomputable def degradation (source target : FiniteSpectralModel Band) : ℝ :=
  target.risk source.optimalReadout - target.risk target.optimalReadout

theorem crossSpectrum_eq_mul_optimalReadout (P : FiniteSpectralModel Band) (b : Band) :
    P.crossSpectrum b = P.featureSpectrum b * P.optimalReadout b := by
  unfold optimalReadout
  field_simp [ne_of_gt (P.featureSpectrum_pos b)]

/-- **Exact spectral degradation identity.**  No closeness hypothesis and no asymptotic
argument: this is completion of the target quadratic risk around its own optimum. -/
theorem degradation_eq_weighted_readout_distance
    (source target : FiniteSpectralModel Band) :
    source.degradation target =
      ∑ b, (source.optimalReadout b - target.optimalReadout b) ^ 2 *
        target.featureSpectrum b := by
  unfold degradation risk
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [target.crossSpectrum_eq_mul_optimalReadout b]
  ring

/-- Transport degradation is non-negative. -/
theorem degradation_nonneg (source target : FiniteSpectralModel Band) :
    0 ≤ source.degradation target := by
  rw [degradation_eq_weighted_readout_distance]
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (sq_nonneg _) (le_of_lt (target.featureSpectrum_pos b))

/-- On the diagonal there is no transport degradation. -/
@[simp] theorem degradation_self (P : FiniteSpectralModel Band) : P.degradation P = 0 := by
  rw [degradation_eq_weighted_readout_distance]
  simp

/-- The same degradation restricted to a selected set of frequency bands. -/
noncomputable def bandDegradation (source target : FiniteSpectralModel Band)
    (bands : Finset Band) : ℝ :=
  ∑ b ∈ bands, (source.optimalReadout b - target.optimalReadout b) ^ 2 *
    target.featureSpectrum b

end FiniteSpectralModel

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
  simp [FiniteSpectralModel.bandDegradation, FiniteSpectralModel.optimalReadout,
    twoBandBaseline, twoBandLowShift, twoBandHighShift]

/-- **No task-independent scalar ranks the two genomic-band shifts.**  For any nonzero
shift, pair 1 is strictly worse on the low-frequency task and pair 2 is strictly worse on
the high-frequency task. -/
theorem twoBand_no_common_monotone_scalar (a : ℝ) (ha : a ≠ 0) :
    let low₁ := FiniteSpectralModel.bandDegradation
      twoBandBaseline (twoBandLowShift a) {0}
    let low₂ := FiniteSpectralModel.bandDegradation
      twoBandBaseline (twoBandHighShift a) {0}
    let high₁ := FiniteSpectralModel.bandDegradation
      twoBandBaseline (twoBandLowShift a) {1}
    let high₂ := FiniteSpectralModel.bandDegradation
      twoBandBaseline (twoBandHighShift a) {1}
    ¬ ∃ (d₁ d₂ : ℝ) (Φlow Φhigh : ℝ → ℝ),
      Monotone Φlow ∧ Monotone Φhigh ∧
      Φlow d₁ = low₁ ∧ Φlow d₂ = low₂ ∧
      Φhigh d₁ = high₁ ∧ Φhigh d₂ = high₂ := by
  dsimp
  apply no_common_monotone_scalar_of_reversal
  · rw [(twoBand_reversal_values a).1, (twoBand_reversal_values a).2.1]
    exact sq_pos_of_ne_zero ha
  · rw [(twoBand_reversal_values a).2.2.1, (twoBand_reversal_values a).2.2.2]
    exact sq_pos_of_ne_zero ha

end Calibrator
