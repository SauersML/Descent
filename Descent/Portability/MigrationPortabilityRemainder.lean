/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MigrationPortabilityFirstOrderFactor
import Descent.Portability.LinearFundamentalMatrix

assert_below Descent.Decision Descent.Program

/-!
# The second-order remainder of the migration factor

`MigrationPortabilityFirstOrderFactor` proves that the two-locus portability ratio with symmetric
migration `m` has derivative `φ₁(T) = firstOrderMigrationFactor` at `m = 0`.  This module bounds
the remainder: `|ratio_m - e^{-ρ̄T} - m φ₁(T)| ≤ C m²` on `0 ≤ m ≤ m₀`, with an explicit `C`.

## Main results

- `norm_matrixExponential_add_smul_sub_le`: Duhamel's formula of `EndToEndSensitivityLaw` with
  `‖e^{tX}‖ ≤ e^{t ‖X‖}` of `LinearFundamentalMatrix` gives
  `‖e^{t(A + mB)} - e^{tA}‖ ≤ t |m| ‖B‖ e^{t ‖A + mB‖} e^{t ‖A‖}`.  So the histories move linearly
  in `m` (`norm_affineMigrationHistory_sub_le`), and so do both stencils
  (`abs_linkageMigrationStencil_sub_le`, `abs_heterozygosityMigrationStencil_sub_le`).
- `abs_migrationHistory_DD_sub_le`, `abs_migrationHistory_pi2_sub_le`: through the exact law of
  `MigrationPortabilityFactor`, `E_m[D_S D_T](T) = N₀ + m N₁ + O(K m²)` and
  `E_m[π_S π_T](T) = Dn₀ + m Dn₁ + O(K m²)`, with the explicit constant
  `K = migrationRemainderConstant = T² ‖B‖² ‖v‖ e^{T (‖A₀‖ + m₀ ‖B‖)} e^{T ‖A₀‖}`.
- `abs_div_sub_div_sub_mul_le`: the quotient rule with an explicit remainder.
- `abs_splitPortabilityRatio_withSymmetricMigration_sub_le`: for `0 ≤ m ≤ m₀` with
  `m |Dn₁| + K m² ≤ Dn₀/2`, `|ratio_m - e^{-ρ̄T} - m φ₁(T)| ≤ C m²`, with
  `C = migrationRatioRemainderConstant`.
- `exists_portabilityDecay_lt_splitPortabilityRatio`,
  `exists_splitPortabilityRatio_lt_portabilityDecay`,
  `firstOrderMigrationFactor_nonneg_of_raises`: for all small rates migration raises portability
  when `φ₁(T) > 0`, lowers it when `φ₁(T) < 0`, and raises it only if `φ₁(T) ≥ 0`.
- `exists_portabilityDecay_lt_splitPortabilityRatio_zeroRecombination`: without recombination, a
  little migration raises portability when `DD₀ < π₀`, `π₀ + Dz₀ > 0` and `T > 0`.

## Significance

The first-order factor of `MigrationPortabilityFirstOrderFactor` is a derivative, a statement
about the limit `m → 0`.  With an explicit constant it becomes a statement at a finite rate: its
sign decides whether a small symmetric migration raises or lowers the two-locus portability ratio.

## Scope

The constants are crude.  They use the operator norms of the generator and of the migration
direction, not their spectra, so they grow exponentially with the split time.  The smallness
condition on `m` keeps the heterozygosity product above half its value without migration, and
nothing here asks how large `m` may be beyond it.  The sign theorems say nothing when
`φ₁(T) = 0`.  Two demes, symmetric migration between them only, and no mutation.

## Empirical status

None.  The bodies are algebra, calculus and norm inequalities on corpus moment coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MigrationPortabilityRemainder

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay
  Descent.Portability.MigrationPortabilityFactor Descent.Portability.MigrationPortabilityFirstOrder
  Descent.Portability.MigrationPortabilityFirstOrderFactor
open scoped Matrix Matrix.Norms.Operator

noncomputable section

/-! ## The propagator moves linearly in the migration rate -/

/-- **A change of generator moves the propagator linearly.**  For `0 ≤ t`,
`‖e^{t(A + mB)} - e^{tA}‖ ≤ t |m| ‖B‖ e^{t ‖A + mB‖} e^{t ‖A‖}`, in the operator norm. -/
theorem norm_matrixExponential_add_smul_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (m : ℝ) {time : ℝ} (htime : 0 ≤ time) :
    ‖matrixExponential (A + m • B) time - matrixExponential A time‖
      ≤ time * (|m| * ‖B‖) * Real.exp (time * ‖A + m • B‖) * Real.exp (time * ‖A‖) := by
  have hduhamel := EndToEndSensitivityLaw.exp_smul_sub_exp_smul_eq_integral (A + m • B) A time
  rw [add_sub_cancel_left] at hduhamel
  have hnorm : ‖NormedSpace.exp ℝ (time • (A + m • B)) - NormedSpace.exp ℝ (time • A)‖
      ≤ time * (|m| * ‖B‖) * Real.exp (time * ‖A + m • B‖) * Real.exp (time * ‖A‖) := by
    refine (le_of_eq (congrArg norm hduhamel)).trans
      ((intervalIntegral.norm_integral_le_of_norm_le_const
        (C := Real.exp (time * ‖A + m • B‖) * (|m| * ‖B‖) * Real.exp (time * ‖A‖))
        fun s hs ↦ ?_).trans_eq ?_)
    · rw [Set.uIoc_of_le htime] at hs
      have hleft : ‖NormedSpace.exp ℝ (s • (A + m • B))‖ ≤ Real.exp (time * ‖A + m • B‖) := by
        refine (LinearFundamentalMatrix.norm_exp_matrix_le _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
        exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      have hright : ‖NormedSpace.exp ℝ ((time - s) • A)‖ ≤ Real.exp (time * ‖A‖) := by
        refine (LinearFundamentalMatrix.norm_exp_matrix_le _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
        exact mul_le_mul_of_nonneg_right (by linarith [hs.1]) (norm_nonneg _)
      have hmiddle : ‖m • B‖ = |m| * ‖B‖ := by rw [norm_smul, Real.norm_eq_abs]
      exact norm_mul₃_le.trans (mul_le_mul (mul_le_mul hleft hmiddle.le (norm_nonneg _)
        (Real.exp_pos _).le) hright (norm_nonneg _) (by positivity))
    · rw [sub_zero, abs_of_nonneg htime]
      ring
  rw [matrixExponential_eq_normedSpace_exp, matrixExponential_eq_normedSpace_exp]
  exact hnorm

variable {D : ℕ}

/-- **The migration histories move linearly in the rate.**  For `0 ≤ t ≤ T` and `0 ≤ θ ≤ m₀`,
`‖H_θ(t) - H_0(t)‖ ≤ T θ ‖B‖ e^{T (‖A₀‖ + m₀ ‖B‖)} e^{T ‖A₀‖} ‖v‖`, with `A₀` the generator
without migration, `B = migrationDirection` and `v` the split vector.

Assumes: `0 ≤ θ ≤ m₀` and `0 ≤ t ≤ T`. -/
theorem norm_affineMigrationHistory_sub_le (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    {θ bound time duration : ℝ} (hθ : 0 ≤ θ) (hbound : θ ≤ bound) (htime : 0 ≤ time)
    (hduration : time ≤ duration) :
    ‖affineMigrationHistory rates hne ancestral θ time
        - affineMigrationHistory rates hne ancestral 0 time‖
      ≤ duration * (θ * ‖migrationDirection rates hne‖)
          * Real.exp (duration
            * (‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
              + bound * ‖migrationDirection rates hne‖))
          * Real.exp (duration
            * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖)
          * ‖(lowOrderLDSplitTransform parent child).mulVec ancestral‖ := by
  have hduration0 : 0 ≤ duration := htime.trans hduration
  have hpropagator := norm_matrixExponential_add_smul_sub_le
    (augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl))
    (migrationDirection rates hne) θ htime
  rw [abs_of_nonneg hθ] at hpropagator
  have hnorm : ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
        + θ • migrationDirection rates hne‖
      ≤ ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
        + bound * ‖migrationDirection rates hne‖ := by
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hexpMigration : Real.exp (time
        * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)
          + θ • migrationDirection rates hne‖)
      ≤ Real.exp (duration
        * (‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
          + bound * ‖migrationDirection rates hne‖)) :=
    Real.exp_le_exp.mpr (mul_le_mul hduration hnorm (norm_nonneg _) hduration0)
  have hexpNeutral : Real.exp (time
        * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖)
      ≤ Real.exp (duration
        * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hduration (norm_nonneg _))
  simp only [affineMigrationHistory]
  rw [zero_smul, add_zero, ← Matrix.sub_mulVec]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right
    (hpropagator.trans ?_) (norm_nonneg _))
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hduration (by positivity))
    hexpMigration (Real.exp_pos _).le (by positivity)) hexpNeutral (Real.exp_pos _).le
    (by positivity)

/-- **The linkage stencil moves by at most `‖B‖` times the move of the state.**

Assumes: no mutation and `parent ≠ child`. -/
theorem abs_linkageMigrationStencil_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (first second : AffineLowOrderLDCoordinate D → ℝ) :
    |linkageMigrationStencil parent child first - linkageMigrationStencil parent child second|
      ≤ ‖migrationDirection rates hne‖ * ‖first - second‖ := by
  have hsub : linkageMigrationStencil parent child first
        - linkageMigrationStencil parent child second
      = (migrationDirection rates hne).mulVec (first - second) (some (.DD parent child)) := by
    rw [Matrix.mulVec_sub, Pi.sub_apply, migrationDirection_mulVec_DD rates hmutation hne,
      migrationDirection_mulVec_DD rates hmutation hne]
  rw [hsub, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ _).trans (Matrix.linfty_opNorm_mulVec _ _)

/-- **The heterozygosity stencil moves by at most `‖B‖` times the move of the state.**

Assumes: no mutation and `parent ≠ child`. -/
theorem abs_heterozygosityMigrationStencil_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (first second : AffineLowOrderLDCoordinate D → ℝ) :
    |heterozygosityMigrationStencil parent child first
        - heterozygosityMigrationStencil parent child second|
      ≤ ‖migrationDirection rates hne‖ * ‖first - second‖ := by
  have hsub : heterozygosityMigrationStencil parent child first
        - heterozygosityMigrationStencil parent child second
      = (migrationDirection rates hne).mulVec (first - second)
          (some (.pi2 parent parent child child)) := by
    rw [Matrix.mulVec_sub, Pi.sub_apply, migrationDirection_mulVec_pi2 rates hmutation hne,
      migrationDirection_mulVec_pi2 rates hmutation hne]
  rw [hsub, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ _).trans (Matrix.linfty_opNorm_mulVec _ _)

/-! ## The coordinates to second order -/

/-- **Two exponentially weighted integrals move by at most the move of their integrands.**  If
`|f(t) - g(t)| ≤ M` on `[0, T]` and `0 ≤ λ`, then
`|∫_0^T e^{λt} f(t) dt - ∫_0^T e^{λt} g(t) dt| ≤ e^{λT} M T`.

Assumes: `0 ≤ λ`, `0 ≤ T`, continuous integrands and the pointwise bound. -/
theorem abs_integral_exp_mul_sub_le {rate duration M : ℝ} {first second : ℝ → ℝ}
    (hrate : 0 ≤ rate) (hduration : 0 ≤ duration) (hfirst : Continuous first)
    (hsecond : Continuous second)
    (hbound : ∀ time, 0 ≤ time → time ≤ duration → |first time - second time| ≤ M) :
    |(∫ time in (0 : ℝ)..duration, Real.exp (rate * time) * first time)
        - ∫ time in (0 : ℝ)..duration, Real.exp (rate * time) * second time|
      ≤ Real.exp (rate * duration) * M * duration := by
  have hcontinuous : ∀ g : ℝ → ℝ, Continuous g →
      Continuous fun time ↦ Real.exp (rate * time) * g time :=
    fun g hg ↦ (by fun_prop : Continuous fun time : ℝ ↦ Real.exp (rate * time)).mul hg
  rw [← intervalIntegral.integral_sub ((hcontinuous _ hfirst).intervalIntegrable _ _)
    ((hcontinuous _ hsecond).intervalIntegrable _ _), ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (rate * duration) * M) fun time htime ↦ ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hduration] at htime
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime.2 hrate))
      (hbound time htime.1.le htime.2) (abs_nonneg _) (Real.exp_pos _).le
  · rw [sub_zero, abs_of_nonneg hduration]

/-- **A variation-of-constants value to second order.**  If `y(m) = e^{-λT} (y₀ + m I(m))` and
`|I(m) - I(0)| ≤ e^{λT} M T`, then `|y(m) - e^{-λT} y₀ - m e^{-λT} I(0)| ≤ m M T`.

Assumes: `0 ≤ m` and the bound on the integrals. -/
theorem abs_exp_mul_add_sub_le {rate duration value₀ integral integral₀ migration M : ℝ}
    (hmigration : 0 ≤ migration)
    (hintegral : |integral - integral₀| ≤ Real.exp (rate * duration) * M * duration) :
    |Real.exp (-rate * duration) * (value₀ + migration * integral)
        - Real.exp (-rate * duration) * value₀
        - migration * (Real.exp (-rate * duration) * integral₀)|
      ≤ migration * M * duration := by
  have hfactor : Real.exp (-rate * duration) * (value₀ + migration * integral)
        - Real.exp (-rate * duration) * value₀
        - migration * (Real.exp (-rate * duration) * integral₀)
      = migration * Real.exp (-rate * duration) * (integral - integral₀) := by
    ring
  have hcancel : Real.exp (-rate * duration) * Real.exp (rate * duration) = 1 := by
    rw [← Real.exp_add, show -rate * duration + rate * duration = 0 by ring, Real.exp_zero]
  rw [hfactor, abs_mul, abs_mul, abs_of_nonneg hmigration, abs_of_pos (Real.exp_pos _)]
  calc migration * Real.exp (-rate * duration) * |integral - integral₀|
      ≤ migration * Real.exp (-rate * duration) * (Real.exp (rate * duration) * M * duration) :=
        mul_le_mul_of_nonneg_left hintegral (mul_nonneg hmigration (Real.exp_pos _).le)
    _ = migration * M * duration * (Real.exp (-rate * duration) * Real.exp (rate * duration)) := by
        ring
    _ = migration * M * duration := by rw [hcancel, mul_one]

/-- **The linkage covariance without migration** `N₀ = e^{-λ_D T} DD₀`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A decaying ancestral moment. -/
def linkageValue (rates : ManyDemeLDRates D) (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  Real.exp (-crossLinkageDecayRate rates parent child * duration)
    * ancestral (some (.DD parent parent))

/-- **The heterozygosity product without migration** `Dn₀ = e^{-λ_π T} π₀`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A decaying ancestral moment. -/
def heterozygosityValue (rates : ManyDemeLDRates D) (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
    * ancestral (some (.pi2 parent parent parent parent))

/-- **The slope of the linkage covariance in `m` at `0`**,
`N₁ = e^{-λ_D T} ∫_0^T e^{λ_D s} μ_D(s) ds` on the history without migration.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral along a corpus history. -/
def linkageSlope (rates : ManyDemeLDRates D) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  Real.exp (-crossLinkageDecayRate rates parent child * duration)
    * ∫ time in (0 : ℝ)..duration,
      Real.exp (crossLinkageDecayRate rates parent child * time)
        * linkageMigrationStencil parent child (migrationHistory rates hne 0 le_rfl ancestral time)

/-- **The slope of the heterozygosity product in `m` at `0`**,
`Dn₁ = e^{-λ_π T} ∫_0^T e^{λ_π s} μ_π(s) ds` on the history without migration.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral along a corpus history. -/
def heterozygositySlope (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ) (duration : ℝ) : ℝ :=
  Real.exp (-crossHeterozygosityDecayRate rates parent child * duration)
    * ∫ time in (0 : ℝ)..duration,
      Real.exp (crossHeterozygosityDecayRate rates parent child * time)
        * heterozygosityMigrationStencil parent child
          (migrationHistory rates hne 0 le_rfl ancestral time)

/-- **The second-order constant of the moments**
`K = T² ‖B‖² ‖v‖ e^{T (‖A₀‖ + m₀ ‖B‖)} e^{T ‖A₀‖}`, in the operator norm, with `A₀` the generator
without migration, `B = migrationDirection`, `v` the split vector and `m₀` the largest rate.

Empirical status: NOT AN EMPIRICAL CLAIM.  A product of norms of corpus matrices and vectors. -/
def migrationRemainderConstant (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration bound : ℝ) : ℝ :=
  duration ^ 2 * ‖migrationDirection rates hne‖ ^ 2
    * ‖(lowOrderLDSplitTransform parent child).mulVec ancestral‖
    * Real.exp (duration
      * (‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
        + bound * ‖migrationDirection rates hne‖))
    * Real.exp (duration
      * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖)

/-- The second-order constant of the moments is nonnegative. -/
theorem migrationRemainderConstant_nonneg (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration bound : ℝ) : 0 ≤ migrationRemainderConstant rates hne ancestral duration bound := by
  unfold migrationRemainderConstant
  positivity

/-- **The linkage covariance to second order in `m`.**
`|E_m[D_S D_T](T) - N₀ - m N₁| ≤ K m²` for `0 ≤ m ≤ m₀`.

Assumes: no mutation, `parent ≠ child`, `0 ≤ m ≤ m₀` and `0 ≤ T`. -/
theorem abs_migrationHistory_DD_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration bound : ℝ} (hmigration : 0 ≤ migration) (hbound : migration ≤ bound)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) {duration : ℝ} (hduration : 0 ≤ duration) :
    |migrationHistory rates hne migration hmigration ancestral duration (some (.DD parent child))
        - linkageValue rates parent child ancestral duration
        - migration * linkageSlope rates hne ancestral duration|
      ≤ migrationRemainderConstant rates hne ancestral duration bound * migration ^ 2 := by
  have hrate : 0 ≤ crossLinkageDecayRate rates parent child :=
    add_nonneg (add_nonneg (rates.coalescence_pos parent).le (rates.coalescence_pos child).le)
      (div_nonneg (add_nonneg (rates.recombination_nonneg parent)
        (rates.recombination_nonneg child)) zero_le_two)
  have hmove : ∀ time, 0 ≤ time → time ≤ duration →
      |linkageMigrationStencil parent child
          (migrationHistory rates hne migration hmigration ancestral time)
        - linkageMigrationStencil parent child (migrationHistory rates hne 0 le_rfl ancestral time)|
      ≤ ‖migrationDirection rates hne‖ * (duration * (migration * ‖migrationDirection rates hne‖)
          * Real.exp (duration
            * (‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
              + bound * ‖migrationDirection rates hne‖))
          * Real.exp (duration
            * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖)
          * ‖(lowOrderLDSplitTransform parent child).mulVec ancestral‖) := by
    intro time htime htimeDuration
    rw [migrationHistory_eq_affineMigrationHistory rates hne hmigration,
      ← affineMigrationHistory_zero rates hne]
    exact (abs_linkageMigrationStencil_sub_le rates hmutation hne _ _).trans
      (mul_le_mul_of_nonneg_left (norm_affineMigrationHistory_sub_le rates hne ancestral
        hmigration hbound htime htimeDuration) (norm_nonneg _))
  have hintegral := abs_integral_exp_mul_sub_le hrate hduration
    (continuous_linkageMigrationStencil
      (continuous_migrationHistory rates hne hmigration ancestral) parent child)
    (continuous_linkageMigrationStencil
      (continuous_migrationHistory rates hne le_rfl ancestral) parent child) hmove
  have h := abs_exp_mul_add_sub_le (value₀ := ancestral (some (.DD parent parent))) hmigration
    hintegral
  rw [migrationHistory_DD rates hmutation hne hmigration, linkageValue, linkageSlope]
  refine h.trans_eq ?_
  rw [migrationRemainderConstant]
  ring

/-- **The heterozygosity product to second order in `m`.**
`|E_m[π_S π_T](T) - Dn₀ - m Dn₁| ≤ K m²` for `0 ≤ m ≤ m₀`.

Assumes: no mutation, `parent ≠ child`, `0 ≤ m ≤ m₀` and `0 ≤ T`. -/
theorem abs_migrationHistory_pi2_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {migration bound : ℝ} (hmigration : 0 ≤ migration) (hbound : migration ≤ bound)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) {duration : ℝ} (hduration : 0 ≤ duration) :
    |migrationHistory rates hne migration hmigration ancestral duration
          (some (.pi2 parent parent child child))
        - heterozygosityValue rates parent child ancestral duration
        - migration * heterozygositySlope rates hne ancestral duration|
      ≤ migrationRemainderConstant rates hne ancestral duration bound * migration ^ 2 := by
  have hrate : 0 ≤ crossHeterozygosityDecayRate rates parent child :=
    add_nonneg (rates.coalescence_pos parent).le (rates.coalescence_pos child).le
  have hmove : ∀ time, 0 ≤ time → time ≤ duration →
      |heterozygosityMigrationStencil parent child
          (migrationHistory rates hne migration hmigration ancestral time)
        - heterozygosityMigrationStencil parent child
          (migrationHistory rates hne 0 le_rfl ancestral time)|
      ≤ ‖migrationDirection rates hne‖ * (duration * (migration * ‖migrationDirection rates hne‖)
          * Real.exp (duration
            * (‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖
              + bound * ‖migrationDirection rates hne‖))
          * Real.exp (duration
            * ‖augmentedLowOrderLDGenerator (withSymmetricMigration rates hne 0 le_rfl)‖)
          * ‖(lowOrderLDSplitTransform parent child).mulVec ancestral‖) := by
    intro time htime htimeDuration
    rw [migrationHistory_eq_affineMigrationHistory rates hne hmigration,
      ← affineMigrationHistory_zero rates hne]
    exact (abs_heterozygosityMigrationStencil_sub_le rates hmutation hne _ _).trans
      (mul_le_mul_of_nonneg_left (norm_affineMigrationHistory_sub_le rates hne ancestral
        hmigration hbound htime htimeDuration) (norm_nonneg _))
  have hintegral := abs_integral_exp_mul_sub_le hrate hduration
    (continuous_heterozygosityMigrationStencil
      (continuous_migrationHistory rates hne hmigration ancestral) parent child)
    (continuous_heterozygosityMigrationStencil
      (continuous_migrationHistory rates hne le_rfl ancestral) parent child) hmove
  have h := abs_exp_mul_add_sub_le
    (value₀ := ancestral (some (.pi2 parent parent parent parent))) hmigration hintegral
  rw [migrationHistory_pi2 rates hmutation hne hmigration, heterozygosityValue,
    heterozygositySlope]
  refine h.trans_eq ?_
  rw [migrationRemainderConstant]
  ring

/-! ## The ratio to second order -/

/-- **The quotient rule with an explicit remainder.**  If `N = N₀ + m N₁ + O(K m²)` and
`Dn = Dn₀ + m Dn₁ + O(K m²)`, both denominators are at least `δ > 0`, and `0 ≤ m ≤ m₀`, then
`|N/Dn - N₀/Dn₀ - m (N₁ Dn₀ - N₀ Dn₁)/Dn₀²| ≤ C m²` with
`C = |N₁ Dn₀ - N₀ Dn₁| (|Dn₁| + K m₀)/(δ Dn₀²) + K (Dn₀ + |N₀|)/(δ Dn₀)`.

Assumes: `0 < δ ≤ Dn`, `δ ≤ Dn₀`, `0 ≤ m ≤ m₀`, `0 ≤ K` and the two second-order bounds. -/
theorem abs_div_sub_div_sub_mul_le {N N₀ N₁ Dn Dn₀ Dn₁ K δ m m₀ : ℝ} (hδ : 0 < δ)
    (hDn : δ ≤ Dn) (hDn₀ : δ ≤ Dn₀) (hm : 0 ≤ m) (hm₀ : m ≤ m₀) (hK : 0 ≤ K)
    (hN : |N - N₀ - m * N₁| ≤ K * m ^ 2) (hD : |Dn - Dn₀ - m * Dn₁| ≤ K * m ^ 2) :
    |N / Dn - N₀ / Dn₀ - m * ((N₁ * Dn₀ - N₀ * Dn₁) / Dn₀ ^ 2)|
      ≤ (|N₁ * Dn₀ - N₀ * Dn₁| * (|Dn₁| + K * m₀) / (δ * Dn₀ ^ 2)
          + K * (Dn₀ + |N₀|) / (δ * Dn₀)) * m ^ 2 := by
  have hDnpos : 0 < Dn := hδ.trans_le hDn
  have hDn₀pos : 0 < Dn₀ := hδ.trans_le hDn₀
  have hDnne := hDnpos.ne'
  have hDn₀ne := hDn₀pos.ne'
  have hm₀nonneg : 0 ≤ m₀ := hm.trans hm₀
  have hidentity : N / Dn - N₀ / Dn₀ - m * ((N₁ * Dn₀ - N₀ * Dn₁) / Dn₀ ^ 2)
      = -(m * (N₁ * Dn₀ - N₀ * Dn₁) * (Dn - Dn₀)) / (Dn * Dn₀ ^ 2)
        + ((N - N₀ - m * N₁) * Dn₀ - N₀ * (Dn - Dn₀ - m * Dn₁)) / (Dn * Dn₀) := by
    field_simp
    ring
  have hmove : |Dn - Dn₀| ≤ m * (|Dn₁| + K * m₀) := by
    have htriangle := abs_add_le (Dn - Dn₀ - m * Dn₁) (m * Dn₁)
    rw [sub_add_cancel, abs_mul, abs_of_nonneg hm] at htriangle
    have hquadratic : K * m ^ 2 ≤ m * (K * m₀) := by
      calc K * m ^ 2 = m * (K * m) := by ring
        _ ≤ m * (K * m₀) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm₀ hK) hm
    linarith
  have hfirst : |-(m * (N₁ * Dn₀ - N₀ * Dn₁) * (Dn - Dn₀)) / (Dn * Dn₀ ^ 2)|
      ≤ |N₁ * Dn₀ - N₀ * Dn₁| * (|Dn₁| + K * m₀) / (δ * Dn₀ ^ 2) * m ^ 2 := by
    have hden : δ * Dn₀ ^ 2 ≤ Dn * Dn₀ ^ 2 := mul_le_mul_of_nonneg_right hDn (sq_nonneg _)
    have hnumerator : |m * (N₁ * Dn₀ - N₀ * Dn₁) * (Dn - Dn₀)|
        ≤ m * |N₁ * Dn₀ - N₀ * Dn₁| * (m * (|Dn₁| + K * m₀)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left hmove (by positivity)
    rw [abs_div, abs_of_pos (by positivity : 0 < Dn * Dn₀ ^ 2), abs_neg]
    exact (div_le_div_of_nonneg_right hnumerator (by positivity)).trans
      ((div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans_eq (by ring))
  have hsecond : |((N - N₀ - m * N₁) * Dn₀ - N₀ * (Dn - Dn₀ - m * Dn₁)) / (Dn * Dn₀)|
      ≤ K * (Dn₀ + |N₀|) / (δ * Dn₀) * m ^ 2 := by
    have hnumerator : |(N - N₀ - m * N₁) * Dn₀ - N₀ * (Dn - Dn₀ - m * Dn₁)|
        ≤ K * m ^ 2 * Dn₀ + |N₀| * (K * m ^ 2) := by
      have htriangle := abs_add_le ((N - N₀ - m * N₁) * Dn₀) (-(N₀ * (Dn - Dn₀ - m * Dn₁)))
      rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_mul, abs_of_pos hDn₀pos] at htriangle
      exact htriangle.trans (add_le_add (mul_le_mul_of_nonneg_right hN hDn₀pos.le)
        (mul_le_mul_of_nonneg_left hD (abs_nonneg _)))
    have hden : δ * Dn₀ ≤ Dn * Dn₀ := mul_le_mul_of_nonneg_right hDn hDn₀pos.le
    rw [abs_div, abs_of_pos (mul_pos hDnpos hDn₀pos)]
    exact (div_le_div_of_nonneg_right hnumerator (mul_pos hDnpos hDn₀pos).le).trans
      ((div_le_div_of_nonneg_left (by positivity) (mul_pos hδ hDn₀pos) hden).trans_eq
        (by ring))
  rw [hidentity]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

/-- Three quotients by one denominator combine into one quotient. -/
theorem sub_div_sub_mul_div (a b c m e : ℝ) :
    a / e - b / e - m * (c / e) = (a - b - m * c) / e := by
  ring

/-- A bound `C m²` on a numerator gives `(C/σ) m²` on its quotient by `σ > 0`.

Assumes: `0 < σ` and the bound on the numerator. -/
theorem abs_div_le_div_mul {x C σ m : ℝ} (hσ : 0 < σ) (h : |x| ≤ C * m ^ 2) :
    |x / σ| ≤ C / σ * m ^ 2 := by
  rw [abs_div, abs_of_pos hσ, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h hσ.le

/-- **The decay is the ratio of the moments without migration.**  `N₀/Dn₀/σ₀ = e^{-ρ̄T}`.

Assumes: nonzero ancestral `DD` and `pi2`. -/
theorem linkageValue_div_heterozygosityValue (rates : ManyDemeLDRates D) (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) (duration : ℝ) :
    linkageValue rates parent child ancestral duration
        / heterozygosityValue rates parent child ancestral duration
        / ancestralSquaredCorrelation ancestral parent
      = portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration := by
  have hexp := (Real.exp_pos (-crossHeterozygosityDecayRate rates parent child * duration)).ne'
  rw [linkageValue, heterozygosityValue, ancestralSquaredCorrelation,
    exp_neg_crossLinkageDecayRate_mul]
  first | (field_simp; ring) | field_simp

/-- **The first-order factor is the quotient-rule slope.**
`(N₁ Dn₀ - N₀ Dn₁)/Dn₀²/σ₀ = φ₁(T)`.

Assumes: nonzero ancestral `DD` and `pi2`. -/
theorem slopes_div_eq_firstOrderMigrationFactor (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ancestral (some (.DD parent parent)) ≠ 0)
    (hheterozygosity : ancestral (some (.pi2 parent parent parent parent)) ≠ 0) (duration : ℝ) :
    (linkageSlope rates hne ancestral duration
          * heterozygosityValue rates parent child ancestral duration
        - linkageValue rates parent child ancestral duration
          * heterozygositySlope rates hne ancestral duration)
        / heterozygosityValue rates parent child ancestral duration ^ 2
        / ancestralSquaredCorrelation ancestral parent
      = firstOrderMigrationFactor rates hne ancestral duration := by
  have hexp := (Real.exp_pos (-crossHeterozygosityDecayRate rates parent child * duration)).ne'
  rw [linkageSlope, heterozygosityValue, linkageValue, heterozygositySlope,
    firstOrderMigrationFactor, linkageMigrationShare, heterozygosityMigrationShare,
    ancestralSquaredCorrelation, exp_neg_crossLinkageDecayRate_mul]
  first | (field_simp; ring) | field_simp

/-- **The second-order constant of the portability ratio**
`C = (|P| (|Dn₁| + K m₀)/(δ Dn₀²) + K (Dn₀ + |N₀|)/(δ Dn₀)) / σ₀`, with `P = N₁ Dn₀ - N₀ Dn₁`,
`δ = Dn₀/2`, `K = migrationRemainderConstant` and `σ₀` the ancestral squared correlation.

Empirical status: NOT AN EMPIRICAL CLAIM.  An algebraic combination of corpus moments. -/
def migrationRatioRemainderConstant (rates : ManyDemeLDRates D) {parent child : Fin D}
    (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (duration bound : ℝ) : ℝ :=
  (|linkageSlope rates hne ancestral duration
          * heterozygosityValue rates parent child ancestral duration
        - linkageValue rates parent child ancestral duration
          * heterozygositySlope rates hne ancestral duration|
      * (|heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration bound * bound)
      / (heterozygosityValue rates parent child ancestral duration / 2
        * heterozygosityValue rates parent child ancestral duration ^ 2)
    + migrationRemainderConstant rates hne ancestral duration bound
      * (heterozygosityValue rates parent child ancestral duration
        + |linkageValue rates parent child ancestral duration|)
      / (heterozygosityValue rates parent child ancestral duration / 2
        * heterozygosityValue rates parent child ancestral duration))
    / ancestralSquaredCorrelation ancestral parent

/-- **The portability ratio to second order in the migration rate.**  For `0 ≤ m ≤ m₀`,
`|ratio_m - e^{-ρ̄T} - m φ₁(T)| ≤ C m²` with `C = migrationRatioRemainderConstant`, provided `m` is
small enough that the heterozygosity product stays above half its value without migration.

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`,
`0 ≤ m ≤ m₀`, and `m |Dn₁| + K m² ≤ Dn₀/2`. -/
theorem abs_splitPortabilityRatio_withSymmetricMigration_sub_le (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    {migration bound : ℝ} (hmigration : 0 ≤ migration) (hbound : migration ≤ bound)
    (hsmall : migration * |heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration bound * migration ^ 2
      ≤ heterozygosityValue rates parent child ancestral duration / 2) :
    |splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration) parent child
          hduration ancestral
        - portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
          duration
        - migration * firstOrderMigrationFactor rates hne ancestral duration|
      ≤ migrationRatioRemainderConstant rates hne ancestral duration bound * migration ^ 2 := by
  have hK := migrationRemainderConstant_nonneg rates hne ancestral duration bound
  have hN := abs_migrationHistory_DD_sub_le rates hmutation hne hmigration hbound ancestral
    hduration
  have hD := abs_migrationHistory_pi2_sub_le rates hmutation hne hmigration hbound ancestral
    hduration
  have hvalue : 0 < heterozygosityValue rates parent child ancestral duration :=
    mul_pos (Real.exp_pos _) hheterozygosity
  have hlower : heterozygosityValue rates parent child ancestral duration / 2
      ≤ migrationHistory rates hne migration hmigration ancestral duration
        (some (.pi2 parent parent child child)) := by
    have hbelow := (abs_le.mp hD).1
    have hslope : migration * -|heterozygositySlope rates hne ancestral duration|
        ≤ migration * heterozygositySlope rates hne ancestral duration :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hmigration
    linarith
  have hquotient := abs_div_sub_div_sub_mul_le (half_pos hvalue) hlower (half_le_self hvalue.le)
    hmigration hbound hK hN hD
  have hσ : 0 < ancestralSquaredCorrelation ancestral parent := div_pos hlinkage hheterozygosity
  have hratio : splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration)
        parent child hduration ancestral
      = migrationHistory rates hne migration hmigration ancestral duration
          (some (.DD parent child))
        / migrationHistory rates hne migration hmigration ancestral duration
          (some (.pi2 parent parent child child))
        / ancestralSquaredCorrelation ancestral parent :=
    rfl
  rw [hratio, ← linkageValue_div_heterozygosityValue rates parent child ancestral hlinkage.ne'
      hheterozygosity.ne',
    ← slopes_div_eq_firstOrderMigrationFactor rates hne ancestral hlinkage.ne'
      hheterozygosity.ne', sub_div_sub_mul_div, migrationRatioRemainderConstant]
  exact abs_div_le_div_mul hσ hquotient

/-! ## The first-order sign decides the direction for small migration -/

/-- **The remainder is dominated by the first-order term for small migration.**  When
`φ₁(T) ≠ 0` there is a threshold below which `|ratio_m - e^{-ρ̄T} - m φ₁(T)| < m |φ₁(T)|`.

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and
`φ₁(T) ≠ 0`. -/
theorem exists_abs_splitPortabilityRatio_sub_lt (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hfactor : firstOrderMigrationFactor rates hne ancestral duration ≠ 0) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        |splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le) parent
              child hduration ancestral
            - portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
              duration
            - migration * firstOrderMigrationFactor rates hne ancestral duration|
          < migration * |firstOrderMigrationFactor rates hne ancestral duration| := by
  have hK := migrationRemainderConstant_nonneg rates hne ancestral duration 1
  have hvalue : 0 < heterozygosityValue rates parent child ancestral duration :=
    mul_pos (Real.exp_pos _) hheterozygosity
  have hσ : 0 < ancestralSquaredCorrelation ancestral parent := div_pos hlinkage hheterozygosity
  have hC : 0 ≤ migrationRatioRemainderConstant rates hne ancestral duration 1 := by
    unfold migrationRatioRemainderConstant
    positivity
  have hφ := abs_pos.mpr hfactor
  refine ⟨min 1 (min (heterozygosityValue rates parent child ancestral duration
      / (2 * (|heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration 1 + 1)))
      (|firstOrderMigrationFactor rates hne ancestral duration|
        / (migrationRatioRemainderConstant rates hne ancestral duration 1 + 1))),
    lt_min one_pos (lt_min (by positivity) (by positivity)),
    fun migration hmigration hthreshold ↦ ?_⟩
  have hone : migration ≤ 1 := hthreshold.trans (min_le_left _ _)
  have hsmallThreshold : migration ≤ heterozygosityValue rates parent child ancestral duration
      / (2 * (|heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration 1 + 1)) :=
    hthreshold.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hfactorThreshold : migration ≤ |firstOrderMigrationFactor rates hne ancestral duration|
      / (migrationRatioRemainderConstant rates hne ancestral duration 1 + 1) :=
    hthreshold.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsquare : migration ^ 2 ≤ migration := by
    rw [sq]
    exact mul_le_of_le_one_left hmigration.le hone
  have hsmall : migration * |heterozygositySlope rates hne ancestral duration|
        + migrationRemainderConstant rates hne ancestral duration 1 * migration ^ 2
      ≤ heterozygosityValue rates parent child ancestral duration / 2 := by
    have hscaled := (le_div_iff₀ (by positivity)).mp hsmallThreshold
    have hquadratic := mul_le_mul_of_nonneg_left hsquare hK
    linarith
  have hremainder := abs_splitPortabilityRatio_withSymmetricMigration_sub_le rates hmutation hne
    hduration ancestral hlinkage hheterozygosity hmigration.le hone hsmall
  have hlinear : migrationRatioRemainderConstant rates hne ancestral duration 1 * migration
      < |firstOrderMigrationFactor rates hne ancestral duration| := by
    have hscaled := (le_div_iff₀ (by positivity)).mp hfactorThreshold
    linarith
  calc |splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le) parent
            child hduration ancestral
          - portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
            duration
          - migration * firstOrderMigrationFactor rates hne ancestral duration|
        ≤ migrationRatioRemainderConstant rates hne ancestral duration 1 * migration ^ 2 :=
          hremainder
      _ = migration
          * (migrationRatioRemainderConstant rates hne ancestral duration 1 * migration) := by
          ring
      _ < migration * |firstOrderMigrationFactor rates hne ancestral duration| :=
          mul_lt_mul_of_pos_left hlinear hmigration

/-- **A positive first-order factor means a little migration raises portability.**

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and
`0 < φ₁(T)`. -/
theorem exists_portabilityDecay_lt_splitPortabilityRatio (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hfactor : 0 < firstOrderMigrationFactor rates hne ancestral duration) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
          < splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le)
            parent child hduration ancestral := by
  obtain ⟨threshold, hpositive, hclose⟩ := exists_abs_splitPortabilityRatio_sub_lt rates
    hmutation hne hduration ancestral hlinkage hheterozygosity hfactor.ne'
  refine ⟨threshold, hpositive, fun migration hmigration hthreshold ↦ ?_⟩
  have h := hclose migration hmigration hthreshold
  rw [abs_of_pos hfactor] at h
  linarith [(abs_lt.mp h).1]

/-- **A negative first-order factor means a little migration lowers portability.**

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and
`φ₁(T) < 0`. -/
theorem exists_splitPortabilityRatio_lt_portabilityDecay (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hfactor : firstOrderMigrationFactor rates hne ancestral duration < 0) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le) parent
            child hduration ancestral
          < portabilityDecay ((rates.recombination parent + rates.recombination child) / 2)
            duration := by
  obtain ⟨threshold, hpositive, hclose⟩ := exists_abs_splitPortabilityRatio_sub_lt rates
    hmutation hne hduration ancestral hlinkage hheterozygosity hfactor.ne
  refine ⟨threshold, hpositive, fun migration hmigration hthreshold ↦ ?_⟩
  have h := hclose migration hmigration hthreshold
  rw [abs_of_neg hfactor] at h
  linarith [(abs_lt.mp h).2]

/-- **If a little migration raises portability, the first-order factor is nonnegative.**
Together with `exists_portabilityDecay_lt_splitPortabilityRatio`, migration raises portability
for all small rates when `φ₁(T) > 0`, and only if `φ₁(T) ≥ 0`.

Assumes: no mutation, `parent ≠ child`, `0 ≤ T`, positive ancestral `DD` and `pi2`, and that the
ratio exceeds `e^{-ρ̄T}` at every rate in some interval `(0, threshold]`. -/
theorem firstOrderMigrationFactor_nonneg_of_raises (rates : ManyDemeLDRates D)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (hraises : ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
          < splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le)
            parent child hduration ancestral) :
    0 ≤ firstOrderMigrationFactor rates hne ancestral duration := by
  by_contra hnegative
  obtain ⟨first, hfirst, hraise⟩ := hraises
  obtain ⟨second, hsecond, hlower⟩ := exists_splitPortabilityRatio_lt_portabilityDecay rates
    hmutation hne hduration ancestral hlinkage hheterozygosity (not_le.mp hnegative)
  have hmin : 0 < min first second := lt_min hfirst hsecond
  exact lt_asymm (hraise _ hmin (min_le_left _ _)) (hlower _ hmin (min_le_right _ _))

/-- **Without recombination a little migration raises portability** when `DD₀ < π₀`,
`π₀ + Dz₀ > 0` and the split is in the past: then `φ₁(T) > 0`.

Assumes: no mutation, `parent ≠ child`, equal drift and recombination rates, `ρ = 0`, positive
ancestral `DD` and `pi2`, `DD₀ < π₀`, `0 < π₀ + Dz₀`, and `0 < T`. -/
theorem exists_portabilityDecay_lt_splitPortabilityRatio_zeroRecombination
    (rates : ManyDemeLDRates D) (hmutation : ∀ deme, rates.mutation deme = 0)
    {parent child : Fin D} (hne : parent ≠ child)
    (hcoal : rates.coalescence child = rates.coalescence parent)
    (hrec : rates.recombination child = rates.recombination parent)
    (hρ : rates.recombination parent = 0) {duration : ℝ} (hpositive : 0 < duration)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : 0 < ancestral (some (.DD parent parent)))
    (hheterozygosity : 0 < ancestral (some (.pi2 parent parent parent parent)))
    (horder : ancestral (some (.DD parent parent))
      < ancestral (some (.pi2 parent parent parent parent)))
    (hcontrast : 0 < ancestral (some (.pi2 parent parent parent parent))
      + ancestral (some (.Dz parent parent parent))) :
    ∃ threshold, 0 < threshold ∧ ∀ migration (hmigration : 0 < migration),
      migration ≤ threshold →
        portabilityDecay ((rates.recombination parent + rates.recombination child) / 2) duration
          < splitPortabilityRatio (withSymmetricMigration rates hne migration hmigration.le)
            parent child hpositive.le ancestral := by
  have hfactor : 0 < firstOrderMigrationFactor rates hne ancestral duration := by
    rw [firstOrderMigrationFactor_zeroRecombination rates hmutation hne hcoal hrec hρ ancestral
      hlinkage.ne' hheterozygosity.ne']
    have hcosh : 1 < Real.cosh (rates.coalescence parent * duration) :=
      Real.one_lt_cosh.mpr (mul_pos (rates.coalescence_pos parent) hpositive).ne'
    exact div_pos (mul_pos (mul_pos (mul_pos two_pos (sub_pos.mpr hcosh)) (sub_pos.mpr horder))
      hcontrast) (mul_pos (mul_pos (rates.coalescence_pos parent) hlinkage) hheterozygosity)
  exact exists_portabilityDecay_lt_splitPortabilityRatio rates hmutation hne hpositive.le ancestral
    hlinkage hheterozygosity hfactor

end

end Descent.Portability.MigrationPortabilityRemainder
