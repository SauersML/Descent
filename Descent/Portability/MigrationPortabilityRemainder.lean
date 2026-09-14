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
    rw [hduhamel]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := Real.exp (time * ‖A + m • B‖) * (|m| * ‖B‖) * Real.exp (time * ‖A‖))
      fun s hs ↦ ?_).trans_eq ?_
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
      refine (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (norm_mul_le _ _)
        (norm_nonneg _)).trans ?_)
      rw [hmiddle]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hleft (by positivity)) hright (norm_nonneg _)
        (by positivity)
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
