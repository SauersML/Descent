/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExposureLaplaceConstraints
import Descent.Portability.TwoLocusPortabilityDecay

assert_below Descent.Decision Descent.Program

/-!
# What a portability curve identifies: the law of the split time

`TwoLocusPortabilityDecay` fixes the split time `T` and proves that the target-to-source ratio of
the expected squared correlation of a tag-locus score is `portabilityDecay r T = e^{-rT}`, with
drift cancelling (`splitPortabilityRatio_eq`).  Here the split time is random, with a law `ν` on
`[0, ∞)`, and the question is what the curve `r ↦ ratio` says about `ν`.

## Main results

- `meanSplitPortabilityRatio_eq`: the split-law average of the per-history ratio is the
  portability curve `portabilityCurve ν r = E_ν[e^{-rT}]`, `r = (ρ_S + ρ_T)/2`.  Drift still
  cancels, because it cancels in every history.
- `portabilityDecay_natCast_mul`: at `r = k r₀` the decay is `(e^{-r₀T})^k`, so the curve at
  `k = 1, 2, 3, …` lists the moments of `e^{-r₀T} ∈ (0, 1]`.
- `splitLaw_eq_of_portabilityCurve_eq`: **identifiability.**  Two probability laws on `[0, ∞)`
  whose portability curves agree at `r₀, 2r₀, 3r₀, …`, `r₀ > 0`, are equal.
- `splitLaw_eq_of_meanSplitPortabilityRatio_eq`: end to end, two split histories with any drift
  rates whose average ratios agree at `k r₀` for `k ≥ 1` have the same split-time law.
- `pooledSplitPortabilityRatio_eq`: the ratio of split-law expectations, the convention of the
  end-to-end law F8, is `L_ν(c + r) / L_ν(c)` with `c = c_S + c_T` and `L_ν` the Laplace transform
  `ExposureLaplaceConstraints.measureLaplace`.  At a point mass it is the corpus decay again
  (`pooledSplitPortabilityRatio_dirac`).
- `pooledSplitPortabilityRatio_ne_of_drift_ne`, `pooledSplitPortabilityRatio_depends_on_drift`:
  **drift does not cancel from the pooled ratio once the split time is random.**  At the two-point
  law `(δ₀ + δ_T)/2` two drift sums `c ≠ c'` give different pooled ratios at every `r > 0`, while
  the average ratios agree.

## The mechanism

Moments determine a law carried by a compact interval.  The corpus proves this in the form needed
here, for Laplace transforms at integer scales of a measure carried by `[0, R]`
(`ExposureLaplaceConstraints.measure_eq_of_measureLaplace_natCast_eq`, Weierstrass on
`[e^{-R}, 1]`).  A split time is not bounded, so it is compressed first:
`compressedExposure r₀ T = -log((1 + e^{-r₀T})/2)` lies in `[0, log 2]`
(`compressedExposure_mem_Icc`), and its transform at the integer `k` is
`E[((1 + e^{-r₀T})/2)^k] = ∑_j C(k, j) 2^{-k} E[e^{-j r₀ T}]`
(`measureLaplace_map_compressedExposure`), a combination of curve values.  Equal curves give
equal compressed laws, and the compression has the measurable inverse `x ↦ -log(2e^{-x} - 1)/r₀`
(`map_compressedDuration_map_compressedExposure`).

## Significance

A two-locus portability curve carries the whole law of the divergence time, not one summary of
it, when each history's ratio is averaged over the split-time law.  The drift rates, and so the
population sizes, never enter that curve.  The pooled ratio of expectations behaves differently.
It is the Laplace ratio `L_ν(c + r)/L_ν(c)`, and drift moves it.  So which average the data
estimate decides whether drift is visible in a portability curve.

## Scope

Each history is the split history of `TwoLocusPortabilityDecay`: one split, then one epoch without
migration or mutation.  `PortabilitySizeBlindness` replaces the epoch by a list of epochs with
different drift rates.  Split-time laws are measures on the line carried by `[0, ∞)`.  The pooled
curve is the curve of the drift-tilted law `e^{-cT} ν(dT) / L_ν(c)`.  That reading, and what the
pooled curve identifies, are not formalized beyond the closed form.

## Empirical status

None.  The bodies here are integrals of real exponentials against stated laws and algebra on the
corpus moment system, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityCurveIdentifiability

open MeasureTheory Descent.Coalescent
open Descent.Portability.TwoLocusPortabilityDecay (portabilityDecay portabilityDecay_zero_rate
  splitHistoryState splitHistoryState_DD splitHistoryState_pi2 splitPortabilityRatio
  splitPortabilityRatio_eq ancestralSquaredCorrelation)
open Descent.Portability.ExposureLaplaceConstraints (measureLaplace measureLaplace_dirac
  measure_eq_of_measureLaplace_natCast_eq)

noncomputable section

variable {D : ℕ}

/-! ## The decay as a function of the split time -/

/-- The portability decay is positive. -/
theorem portabilityDecay_pos (rate duration : ℝ) : 0 < portabilityDecay rate duration :=
  Real.exp_pos _

/-- At a nonnegative rate and a nonnegative split time the decay is at most one.

Assumes: `0 ≤ rate` and `0 ≤ duration`. -/
theorem portabilityDecay_le_one {rate duration : ℝ} (hrate : 0 ≤ rate)
    (hduration : 0 ≤ duration) : portabilityDecay rate duration ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrate hduration))

/-- The decay is continuous in the split time. -/
theorem continuous_portabilityDecay (rate : ℝ) : Continuous (portabilityDecay rate) := by
  show Continuous fun duration ↦ Real.exp (-(rate * duration))
  fun_prop

/-- **The curve at integer multiples lists moments.**  At `k r₀` the decay is the `k`-th power of
the decay at `r₀`. -/
theorem portabilityDecay_natCast_mul (scale : ℕ) (rate duration : ℝ) :
    portabilityDecay (scale * rate) duration = portabilityDecay rate duration ^ scale := by
  rw [portabilityDecay, portabilityDecay, ← Real.exp_nat_mul]
  congr 1
  ring

/-! ## The portability curve of a split-time law -/

/-- **The portability curve of a split-time law** `ν`: `r ↦ E_ν[e^{-rT}]`.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral of a real exponential against a stated
law. -/
def portabilityCurve (splitLaw : Measure ℝ) (rate : ℝ) : ℝ :=
  ∫ duration, portabilityDecay rate duration ∂splitLaw

/-- The portability curve is the Laplace transform of the split-time law. -/
theorem portabilityCurve_eq_measureLaplace (splitLaw : Measure ℝ) (rate : ℝ) :
    portabilityCurve splitLaw rate = measureLaplace splitLaw rate :=
  rfl

/-- A finite law carried by `[0, ∞)` integrates the decay at a nonnegative rate.

Assumes: a finite measure carried by `[0, ∞)` and `0 ≤ rate`. -/
theorem integrable_portabilityDecay (splitLaw : Measure ℝ) [IsFiniteMeasure splitLaw] {rate : ℝ}
    (hrate : 0 ≤ rate) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) :
    Integrable (portabilityDecay rate) splitLaw :=
  Integrable.of_bound (continuous_portabilityDecay rate).aestronglyMeasurable 1
    (hsupport.mono fun duration hduration ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (portabilityDecay_pos rate duration)]
      exact portabilityDecay_le_one hrate hduration)

/-! ## Compressing an unbounded split time into `[0, log 2]` -/

/-- **The compressed exposure** `-log((1 + e^{-rT})/2)` of a split time `T` at rate `r`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A real function of a real exponential. -/
def compressedExposure (rate duration : ℝ) : ℝ :=
  -Real.log ((1 + portabilityDecay rate duration) / 2)

/-- The compressed exposure is measurable in the split time. -/
theorem measurable_compressedExposure (rate : ℝ) : Measurable (compressedExposure rate) := by
  have hcontinuous : Continuous fun duration : ℝ ↦ (1 + Real.exp (-(rate * duration))) / 2 := by
    fun_prop
  have h : Measurable fun duration : ℝ ↦ -Real.log ((1 + Real.exp (-(rate * duration))) / 2) :=
    (Real.measurable_log.comp hcontinuous.measurable).neg
  have hfun : compressedExposure rate
      = fun duration : ℝ ↦ -Real.log ((1 + Real.exp (-(rate * duration))) / 2) :=
    rfl
  rw [hfun]
  exact h

/-- **The compression lands in `[0, log 2]`.**  For a nonnegative rate and split time the decay
lies in `(0, 1]`, so `(1 + e^{-rT})/2` lies in `(1/2, 1]`.

Assumes: `0 ≤ rate` and `0 ≤ duration`. -/
theorem compressedExposure_mem_Icc {rate duration : ℝ} (hrate : 0 ≤ rate)
    (hduration : 0 ≤ duration) :
    compressedExposure rate duration ∈ Set.Icc 0 (Real.log 2) := by
  have hpos := portabilityDecay_pos rate duration
  have hle := portabilityDecay_le_one hrate hduration
  have hlower : 0 < (1 + portabilityDecay rate duration) / 2 := by linarith
  have hdouble : Real.log (2 * ((1 + portabilityDecay rate duration) / 2))
      = Real.log 2 + Real.log ((1 + portabilityDecay rate duration) / 2) :=
    Real.log_mul two_ne_zero hlower.ne'
  have hnonneg : 0 ≤ Real.log (2 * ((1 + portabilityDecay rate duration) / 2)) :=
    Real.log_nonneg (by linarith)
  show -Real.log ((1 + portabilityDecay rate duration) / 2) ∈ Set.Icc 0 (Real.log 2)
  exact Set.mem_Icc.mpr
    ⟨neg_nonneg.mpr (Real.log_nonpos hlower.le (by linarith)), by linarith⟩

/-- The compression reads back the decay: `e^{-x} = (1 + e^{-rT})/2` at
`x = compressedExposure r T`. -/
theorem exp_neg_compressedExposure (rate duration : ℝ) :
    Real.exp (-compressedExposure rate duration) = (1 + portabilityDecay rate duration) / 2 := by
  have hpositive : 0 < (1 + portabilityDecay rate duration) / 2 := by
    linarith [portabilityDecay_pos rate duration]
  rw [compressedExposure, neg_neg, Real.exp_log hpositive]

/-- **The transform of the compression at an integer scale is a combination of decays.**
`e^{-k x} = ((1 + e^{-rT})/2)^k = ∑_j C(k, j) 2^{-k} e^{-j r T}` at `x = compressedExposure r T`.
-/
theorem exp_neg_natCast_mul_compressedExposure (scale : ℕ) (rate duration : ℝ) :
    Real.exp (-(scale * compressedExposure rate duration))
      = ∑ index ∈ Finset.range (scale + 1),
          (scale.choose index : ℝ) / 2 ^ scale * portabilityDecay (index * rate) duration := by
  rw [show -(scale * compressedExposure rate duration) = scale * -compressedExposure rate duration
      by ring, Real.exp_nat_mul, exp_neg_compressedExposure, div_pow, add_comm (1 : ℝ), add_pow,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  rw [one_pow, mul_one, portabilityDecay_natCast_mul]
  ring

/-- **The Laplace transform of the compressed law.**  At an integer scale `k` it is
`∑_j C(k, j) 2^{-k} · portabilityCurve ν (j r)`.

Assumes: a finite measure carried by `[0, ∞)` and `0 ≤ rate`. -/
theorem measureLaplace_map_compressedExposure (splitLaw : Measure ℝ) [IsFiniteMeasure splitLaw]
    {rate : ℝ} (hrate : 0 ≤ rate) (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration)
    (scale : ℕ) :
    measureLaplace (splitLaw.map (compressedExposure rate)) scale
      = ∑ index ∈ Finset.range (scale + 1),
          (scale.choose index : ℝ) / 2 ^ scale * portabilityCurve splitLaw (index * rate) := by
  have hintegrable : ∀ index ∈ Finset.range (scale + 1),
      Integrable (fun duration ↦
        (scale.choose index : ℝ) / 2 ^ scale * portabilityDecay (index * rate) duration)
        splitLaw :=
    fun index _ ↦ (integrable_portabilityDecay splitLaw
      (mul_nonneg (Nat.cast_nonneg index) hrate) hsupport).const_mul _
  have hexponential : Continuous fun exposure : ℝ ↦ Real.exp (-(scale * exposure)) := by
    fun_prop
  unfold portabilityCurve
  rw [measureLaplace, integral_map (measurable_compressedExposure rate).aemeasurable
    hexponential.aestronglyMeasurable]
  simp only [exp_neg_natCast_mul_compressedExposure]
  rw [integral_finset_sum _ hintegrable]
  exact Finset.sum_congr rfl fun index _ ↦ integral_const_mul _ _

/-- **The compression is inverted by a measurable map**, `x ↦ r⁻¹ · (-log(2e^{-x} - 1))`,
whatever the sign of the split time.

Assumes: `rate ≠ 0`. -/
theorem map_compressedDuration_map_compressedExposure {rate : ℝ} (hrate : rate ≠ 0)
    (splitLaw : Measure ℝ) :
    (splitLaw.map (compressedExposure rate)).map
        (fun exposure ↦ rate⁻¹ * -Real.log (2 * Real.exp (-exposure) - 1)) = splitLaw := by
  have hlog : Measurable fun exposure : ℝ ↦ Real.log (2 * Real.exp (-exposure) - 1) :=
    Real.measurable_log.comp
      (by fun_prop : Continuous fun exposure : ℝ ↦ 2 * Real.exp (-exposure) - 1).measurable
  have hinverse : Measurable fun exposure : ℝ ↦
      rate⁻¹ * -Real.log (2 * Real.exp (-exposure) - 1) :=
    measurable_const.mul hlog.neg
  have hidentity : (fun exposure : ℝ ↦ rate⁻¹ * -Real.log (2 * Real.exp (-exposure) - 1))
      ∘ compressedExposure rate = id := by
    funext duration
    show rate⁻¹ * -Real.log (2 * Real.exp (-compressedExposure rate duration) - 1) = duration
    rw [exp_neg_compressedExposure, show 2 * ((1 + portabilityDecay rate duration) / 2) - 1
        = portabilityDecay rate duration by ring, portabilityDecay, Real.log_exp, neg_neg,
      inv_mul_cancel_left₀ hrate duration]
  rw [Measure.map_map hinverse (measurable_compressedExposure rate), hidentity, Measure.map_id]

/-! ## Moment determinacy for split times -/

/-- **Finite split-time laws are determined by the curve at integer multiples.**  Two finite laws
carried by `[0, ∞)` whose portability curves agree at `k r₀` for every `k = 0, 1, 2, …`, with
`r₀ > 0`, are equal.

Assumes: two finite measures carried by `[0, ∞)`, `0 < rate`, and equal curves at `k r₀`. -/
theorem measure_eq_of_portabilityCurve_natCast_eq (first second : Measure ℝ)
    [IsFiniteMeasure first] [IsFiniteMeasure second] {rate : ℝ} (hrate : 0 < rate)
    (hfirst : ∀ᵐ duration ∂first, 0 ≤ duration) (hsecond : ∀ᵐ duration ∂second, 0 ≤ duration)
    (hcurve : ∀ scale : ℕ,
      portabilityCurve first (scale * rate) = portabilityCurve second (scale * rate)) :
    first = second := by
  have hsupport : ∀ law : Measure ℝ, (∀ᵐ duration ∂law, 0 ≤ duration) →
      ∀ᵐ exposure ∂law.map (compressedExposure rate), exposure ∈ Set.Icc 0 (Real.log 2) :=
    fun law hlaw ↦ (ae_map_iff (measurable_compressedExposure rate).aemeasurable
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) (Real.log 2)))).mpr
        (hlaw.mono fun duration hduration ↦ compressedExposure_mem_Icc hrate.le hduration)
  have hcompressed : first.map (compressedExposure rate) = second.map (compressedExposure rate) :=
    measure_eq_of_measureLaplace_natCast_eq _ _ (Real.log 2) (hsupport first hfirst)
      (hsupport second hsecond) fun scale ↦ by
        rw [measureLaplace_map_compressedExposure first hrate.le hfirst,
          measureLaplace_map_compressedExposure second hrate.le hsecond]
        exact Finset.sum_congr rfl fun index _ ↦ by rw [hcurve index]
  calc first
      = (first.map (compressedExposure rate)).map
          (fun exposure ↦ rate⁻¹ * -Real.log (2 * Real.exp (-exposure) - 1)) :=
        (map_compressedDuration_map_compressedExposure hrate.ne' first).symm
    _ = (second.map (compressedExposure rate)).map
          (fun exposure ↦ rate⁻¹ * -Real.log (2 * Real.exp (-exposure) - 1)) := by
        rw [hcompressed]
    _ = second := map_compressedDuration_map_compressedExposure hrate.ne' second

/-- **F9 identifiability: the portability curve determines the split-time law.**  Two probability
laws of the split time carried by `[0, ∞)` whose portability curves agree at `r₀, 2r₀, 3r₀, …`,
`r₀ > 0`, are equal.

Assumes: two probability measures carried by `[0, ∞)`, `0 < rate`, and equal curves at `k r₀`
for `k ≥ 1`. -/
theorem splitLaw_eq_of_portabilityCurve_eq (first second : Measure ℝ)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second] {rate : ℝ} (hrate : 0 < rate)
    (hfirst : ∀ᵐ duration ∂first, 0 ≤ duration) (hsecond : ∀ᵐ duration ∂second, 0 ≤ duration)
    (hcurve : ∀ scale : ℕ, 0 < scale →
      portabilityCurve first (scale * rate) = portabilityCurve second (scale * rate)) :
    first = second := by
  refine measure_eq_of_portabilityCurve_natCast_eq first second hrate hfirst hsecond
    fun scale ↦ ?_
  rcases Nat.eq_zero_or_pos scale with hzero | hpositive
  · subst hzero
    simp only [portabilityCurve, Nat.cast_zero, zero_mul, portabilityDecay_zero_rate,
      integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
  · exact hcurve scale hpositive

/-! ## Split histories at one recombination rate -/

/-- **The neutral linkage rates of a split history at recombination rate `rate`**: the drift rates
of `drift`, no migration, no mutation, and recombination `max rate 0` in every deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A choice of rate parameters. -/
def neutralLinkageRates (drift : ManyDemeLDRates D) (rate : ℝ) : ManyDemeLDRates D where
  coalescence := drift.coalescence
  migration := fun _ _ ↦ 0
  mutation := fun _ ↦ 0
  recombination := fun _ ↦ max rate 0
  coalescence_pos := drift.coalescence_pos
  migration_nonneg := fun _ _ ↦ le_rfl
  migration_self := fun _ ↦ rfl
  mutation_nonneg := fun _ ↦ le_rfl
  recombination_nonneg := fun _ ↦ le_max_right rate 0

/-- The neutral linkage rates keep the drift rates. -/
theorem neutralLinkageRates_coalescence (drift : ManyDemeLDRates D) (rate : ℝ) (deme : Fin D) :
    (neutralLinkageRates drift rate).coalescence deme = drift.coalescence deme :=
  rfl

/-- The neutral linkage rates have no migration. -/
theorem neutralLinkageRates_migration (drift : ManyDemeLDRates D) (rate : ℝ)
    (source target : Fin D) : (neutralLinkageRates drift rate).migration source target = 0 :=
  rfl

/-- The neutral linkage rates have no mutation. -/
theorem neutralLinkageRates_mutation (drift : ManyDemeLDRates D) (rate : ℝ) (deme : Fin D) :
    (neutralLinkageRates drift rate).mutation deme = 0 :=
  rfl

/-- The neutral linkage rates recombine at `max rate 0` in every deme. -/
theorem neutralLinkageRates_recombination (drift : ManyDemeLDRates D) (rate : ℝ)
    (deme : Fin D) : (neutralLinkageRates drift rate).recombination deme = max rate 0 :=
  rfl

/-- The mean recombination rate of the neutral linkage rates is `max rate 0`. -/
theorem neutralLinkageRates_recombination_mean (drift : ManyDemeLDRates D) (rate : ℝ)
    (parent child : Fin D) :
    ((neutralLinkageRates drift rate).recombination parent
        + (neutralLinkageRates drift rate).recombination child) / 2 = max rate 0 := by
  rw [neutralLinkageRates_recombination, neutralLinkageRates_recombination]
  ring

/-- **Populations of one constant size.**  Every deme has size `N = e^{logSize}` and drifts at
rate `1/N = e^{-logSize}`; there is no migration, mutation or recombination.

Empirical status: NOT AN EMPIRICAL CLAIM.  A choice of rate parameters. -/
def constantSizeRates (D : ℕ) (logSize : ℝ) : ManyDemeLDRates D where
  coalescence := fun _ ↦ Real.exp (-logSize)
  migration := fun _ _ ↦ 0
  mutation := fun _ ↦ 0
  recombination := fun _ ↦ 0
  coalescence_pos := fun _ ↦ Real.exp_pos _
  migration_nonneg := fun _ _ ↦ le_rfl
  migration_self := fun _ ↦ rfl
  mutation_nonneg := fun _ ↦ le_rfl
  recombination_nonneg := fun _ ↦ le_rfl

/-! ## Drift cancels from the average ratio -/

/-- **The split-law average of the per-history portability ratio**, `E_ν[σ²_{S→T}(T)/σ²_D(0)]`.
A split time below zero is read as zero.

Empirical status: NOT AN EMPIRICAL CLAIM.  An integral of a ratio of moment coordinates. -/
def meanSplitPortabilityRatio (rates : ManyDemeLDRates D) (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (splitLaw : Measure ℝ) : ℝ :=
  ∫ duration, splitPortabilityRatio rates parent child (le_max_right duration 0) ancestral
    ∂splitLaw

/-- **Drift still cancels when the split time is random.**  Averaged over the split-time law, the
per-history ratio is the portability curve at `r = (ρ_S + ρ_T)/2`, whatever the drift rates.

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral correlation, and a split
law carried by `[0, ∞)`. -/
theorem meanSplitPortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) (splitLaw : Measure ℝ)
    (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) :
    meanSplitPortabilityRatio rates parent child ancestral splitLaw
      = portabilityCurve splitLaw
          ((rates.recombination parent + rates.recombination child) / 2) := by
  unfold meanSplitPortabilityRatio portabilityCurve
  refine integral_congr_ae (hsupport.mono fun duration hduration ↦ ?_)
  exact (splitPortabilityRatio_eq rates hmigration hmutation hne (le_max_right duration 0)
    ancestral hsource).trans (by rw [max_eq_left hduration])

/-- At the neutral linkage rates the average ratio is the portability curve at `max rate 0`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, and a split law carried by
`[0, ∞)`. -/
theorem meanSplitPortabilityRatio_neutralLinkageRates (drift : ManyDemeLDRates D) (rate : ℝ)
    {parent child : Fin D} (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) (splitLaw : Measure ℝ)
    (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) :
    meanSplitPortabilityRatio (neutralLinkageRates drift rate) parent child ancestral splitLaw
      = portabilityCurve splitLaw (max rate 0) := by
  rw [meanSplitPortabilityRatio_eq (neutralLinkageRates drift rate)
    (neutralLinkageRates_migration drift rate) (neutralLinkageRates_mutation drift rate) hne
    ancestral hsource splitLaw hsupport, neutralLinkageRates_recombination_mean]

/-- **The average portability curve of a split history identifies its split-time law.**  Two
split histories, with any drift rates and any ancestral states, whose average ratios agree at the
recombination rates `r₀, 2r₀, 3r₀, …` have the same split-time law.

Assumes: `parent ≠ child`, nonzero ancestral correlations, probability laws carried by `[0, ∞)`,
`0 < rate`, and equal average ratios at `k r₀` for `k ≥ 1`. -/
theorem splitLaw_eq_of_meanSplitPortabilityRatio_eq (firstDrift secondDrift : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child)
    (firstAncestral secondAncestral : AffineLowOrderLDCoordinate D → ℝ)
    (hfirstSource : ancestralSquaredCorrelation firstAncestral parent ≠ 0)
    (hsecondSource : ancestralSquaredCorrelation secondAncestral parent ≠ 0)
    (firstLaw secondLaw : Measure ℝ) [IsProbabilityMeasure firstLaw]
    [IsProbabilityMeasure secondLaw] (hfirst : ∀ᵐ duration ∂firstLaw, 0 ≤ duration)
    (hsecond : ∀ᵐ duration ∂secondLaw, 0 ≤ duration) {rate : ℝ} (hrate : 0 < rate)
    (hcurve : ∀ scale : ℕ, 0 < scale →
      meanSplitPortabilityRatio (neutralLinkageRates firstDrift (scale * rate)) parent child
          firstAncestral firstLaw
        = meanSplitPortabilityRatio (neutralLinkageRates secondDrift (scale * rate)) parent child
          secondAncestral secondLaw) :
    firstLaw = secondLaw := by
  refine splitLaw_eq_of_portabilityCurve_eq firstLaw secondLaw hrate hfirst hsecond
    fun scale hscale ↦ ?_
  have h := hcurve scale hscale
  rw [meanSplitPortabilityRatio_neutralLinkageRates firstDrift _ hne firstAncestral hfirstSource
      firstLaw hfirst,
    meanSplitPortabilityRatio_neutralLinkageRates secondDrift _ hne secondAncestral hsecondSource
      secondLaw hsecond, max_eq_left (mul_nonneg (Nat.cast_nonneg scale) hrate.le)] at h
  exact h

/-! ## The pooled ratio of expectations -/

/-- **The pooled portability ratio**: the ratio of the split-law expectations of the cross moments
`E[D_S D_T]` and `E[π^A_S π^B_T]`, relative to `σ²_D(0)`.  A split time below zero is read as
zero.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of integrals of moment coordinates. -/
def pooledSplitPortabilityRatio (rates : ManyDemeLDRates D) (parent child : Fin D)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ) (splitLaw : Measure ℝ) : ℝ :=
  ((∫ duration, splitHistoryState rates parent child (le_max_right duration 0) ancestral
        (some (.DD parent child)) ∂splitLaw)
      / ∫ duration, splitHistoryState rates parent child (le_max_right duration 0) ancestral
        (some (.pi2 parent parent child child)) ∂splitLaw)
    / ancestralSquaredCorrelation ancestral parent

/-- **The pooled ratio is a ratio of Laplace transforms.**  With `c = c_S + c_T` and
`r = (ρ_S + ρ_T)/2`, the pooled ratio is `L_ν(c + r) / L_ν(c)`.  Drift enters through `c`.

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral correlation, and a split
law carried by `[0, ∞)`. -/
theorem pooledSplitPortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) (splitLaw : Measure ℝ)
    (hsupport : ∀ᵐ duration ∂splitLaw, 0 ≤ duration) :
    pooledSplitPortabilityRatio rates parent child ancestral splitLaw
      = measureLaplace splitLaw (rates.coalescence parent + rates.coalescence child
          + (rates.recombination parent + rates.recombination child) / 2)
        / measureLaplace splitLaw (rates.coalescence parent + rates.coalescence child) := by
  have hDD : ∫ duration, splitHistoryState rates parent child (le_max_right duration 0) ancestral
        (some (.DD parent child)) ∂splitLaw
      = measureLaplace splitLaw (rates.coalescence parent + rates.coalescence child
          + (rates.recombination parent + rates.recombination child) / 2)
        * ancestral (some (.DD parent parent)) := by
    rw [measureLaplace, ← integral_mul_const]
    refine integral_congr_ae (hsupport.mono fun duration hduration ↦ ?_)
    exact (splitHistoryState_DD rates hmigration hmutation hne (le_max_right duration 0)
      ancestral).trans (by rw [max_eq_left hduration, neg_mul])
  have hpi2 : ∫ duration, splitHistoryState rates parent child (le_max_right duration 0) ancestral
        (some (.pi2 parent parent child child)) ∂splitLaw
      = measureLaplace splitLaw (rates.coalescence parent + rates.coalescence child)
        * ancestral (some (.pi2 parent parent parent parent)) := by
    rw [measureLaplace, ← integral_mul_const]
    refine integral_congr_ae (hsupport.mono fun duration hduration ↦ ?_)
    exact (splitHistoryState_pi2 rates hmigration hmutation hne (le_max_right duration 0)
      ancestral).trans (by rw [max_eq_left hduration, neg_mul])
  have hcorrelation : ancestral (some (.DD parent parent))
        / ancestral (some (.pi2 parent parent parent parent))
      = ancestralSquaredCorrelation ancestral parent :=
    rfl
  rw [pooledSplitPortabilityRatio, hDD, hpi2, ← div_mul_div_comm, hcorrelation,
    mul_div_cancel_right₀ _ hsource]

/-- **For a fixed split time the pooled ratio is the corpus decay.**  At the point mass `δ_T` the
pooled ratio equals the per-history ratio of `splitPortabilityRatio_eq`.

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral correlation, and
`0 ≤ duration`. -/
theorem pooledSplitPortabilityRatio_dirac (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) {duration : ℝ}
    (hduration : 0 ≤ duration) :
    pooledSplitPortabilityRatio rates parent child ancestral (Measure.dirac duration)
      = splitPortabilityRatio rates parent child hduration ancestral := by
  have hsupport : ∀ᵐ split ∂Measure.dirac duration, 0 ≤ split := by
    simp [hduration]
  rw [pooledSplitPortabilityRatio_eq rates hmigration hmutation hne ancestral hsource _ hsupport,
    (measureLaplace_dirac duration _).2, (measureLaplace_dirac duration _).2,
    splitPortabilityRatio_eq rates hmigration hmutation hne hduration ancestral hsource,
    portabilityDecay, ← Real.exp_sub]
  congr 1
  ring

/-! ## Drift does not cancel from the pooled ratio -/

/-- **The two-point split-time law** `(δ₀ + δ_T)/2`: no divergence, or a split `T` ago, with
probability one half each.

Empirical status: NOT AN EMPIRICAL CLAIM.  A stated law. -/
def twoPointSplitLaw (duration : ℝ) : Measure ℝ :=
  ENNReal.ofReal 2⁻¹ • Measure.dirac 0 + ENNReal.ofReal 2⁻¹ • Measure.dirac duration

/-- The two-point law is carried by `[0, ∞)`.

Assumes: `0 ≤ duration`. -/
theorem ae_twoPointSplitLaw_nonneg {duration : ℝ} (hduration : 0 ≤ duration) :
    ∀ᵐ split ∂twoPointSplitLaw duration, 0 ≤ split := by
  unfold twoPointSplitLaw
  apply ae_add_measure_iff.mpr
  constructor
  · apply Measure.ae_smul_measure
    simp
  · apply Measure.ae_smul_measure
    simp [hduration]

/-- The transform of the two-point law is `(1 + e^{-λT})/2`. -/
theorem measureLaplace_twoPointSplitLaw (duration lam : ℝ) :
    measureLaplace (twoPointSplitLaw duration) lam = 2⁻¹ * (1 + portabilityDecay lam duration) := by
  have hzero : Integrable (fun split : ℝ ↦ Real.exp (-(lam * split))) (Measure.dirac 0) :=
    integrable_dirac (by simp)
  have hlate : Integrable (fun split : ℝ ↦ Real.exp (-(lam * split))) (Measure.dirac duration) :=
    integrable_dirac (by simp)
  rw [measureLaplace, twoPointSplitLaw, integral_add_measure
      (hzero.smul_measure ENNReal.ofReal_ne_top) (hlate.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2⁻¹), smul_eq_mul,
    mul_zero, neg_zero, Real.exp_zero]
  rw [portabilityDecay]
  ring

/-- **The pooled ratio at the two-point law** is `(1 + e^{-(c + r)T}) / (1 + e^{-cT})` with
`c = c_S + c_T`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, `0 ≤ rate` and `0 ≤ duration`. -/
theorem pooledSplitPortabilityRatio_twoPointSplitLaw (drift : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) {rate duration : ℝ}
    (hrate : 0 ≤ rate) (hduration : 0 ≤ duration) :
    pooledSplitPortabilityRatio (neutralLinkageRates drift rate) parent child ancestral
        (twoPointSplitLaw duration)
      = (1 + portabilityDecay (drift.coalescence parent + drift.coalescence child + rate) duration)
        / (1 + portabilityDecay (drift.coalescence parent + drift.coalescence child) duration) := by
  rw [pooledSplitPortabilityRatio_eq (neutralLinkageRates drift rate)
      (neutralLinkageRates_migration drift rate) (neutralLinkageRates_mutation drift rate) hne
      ancestral hsource _ (ae_twoPointSplitLaw_nonneg hduration),
    neutralLinkageRates_recombination_mean, max_eq_left hrate, neutralLinkageRates_coalescence,
    neutralLinkageRates_coalescence, measureLaplace_twoPointSplitLaw,
    measureLaplace_twoPointSplitLaw, mul_div_mul_left _ _ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]

/-- **Drift does not cancel from the pooled ratio.**  At the two-point law with `T > 0` and a
positive rate, two drift sums `c ≠ c'` give different pooled ratios, because
`(1 + e^{-(c+r)T})(1 + e^{-c'T}) - (1 + e^{-(c'+r)T})(1 + e^{-cT})` equals
`(1 - e^{-rT})(e^{-c'T} - e^{-cT})`.

Assumes: `parent ≠ child`, a nonzero ancestral correlation, `0 < rate`, `0 < duration`, and
different drift sums. -/
theorem pooledSplitPortabilityRatio_ne_of_drift_ne (firstDrift secondDrift : ManyDemeLDRates D)
    {parent child : Fin D} (hne : parent ≠ child) (ancestral : AffineLowOrderLDCoordinate D → ℝ)
    (hsource : ancestralSquaredCorrelation ancestral parent ≠ 0) {rate duration : ℝ}
    (hrate : 0 < rate) (hduration : 0 < duration)
    (hdrift : firstDrift.coalescence parent + firstDrift.coalescence child
      ≠ secondDrift.coalescence parent + secondDrift.coalescence child) :
    pooledSplitPortabilityRatio (neutralLinkageRates firstDrift rate) parent child ancestral
        (twoPointSplitLaw duration)
      ≠ pooledSplitPortabilityRatio (neutralLinkageRates secondDrift rate) parent child ancestral
        (twoPointSplitLaw duration) := by
  intro hequal
  rw [pooledSplitPortabilityRatio_twoPointSplitLaw firstDrift hne ancestral hsource hrate.le
      hduration.le,
    pooledSplitPortabilityRatio_twoPointSplitLaw secondDrift hne ancestral hsource hrate.le
      hduration.le] at hequal
  have hsplit : ∀ drift : ℝ, portabilityDecay (drift + rate) duration
      = portabilityDecay drift duration * portabilityDecay rate duration := fun drift ↦ by
    rw [portabilityDecay, portabilityDecay, portabilityDecay, ← Real.exp_add]
    congr 1
    ring
  have hfirstPos := portabilityDecay_pos
    (firstDrift.coalescence parent + firstDrift.coalescence child) duration
  have hsecondPos := portabilityDecay_pos
    (secondDrift.coalescence parent + secondDrift.coalescence child) duration
  rw [hsplit, hsplit, div_eq_div_iff (add_pos one_pos hfirstPos).ne'
    (add_pos one_pos hsecondPos).ne'] at hequal
  have hfactor : (1 - portabilityDecay rate duration)
      * (portabilityDecay (secondDrift.coalescence parent + secondDrift.coalescence child) duration
        - portabilityDecay (firstDrift.coalescence parent + firstDrift.coalescence child)
          duration) = 0 := by
    linear_combination hequal
  have hlt : portabilityDecay rate duration < 1 := by
    rw [portabilityDecay, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith [mul_pos hrate hduration])
  rcases mul_eq_zero.mp hfactor with hone | hsame
  · linarith
  · have hexponent : -((secondDrift.coalescence parent + secondDrift.coalescence child) * duration)
        = -((firstDrift.coalescence parent + firstDrift.coalescence child) * duration) :=
      Real.exp_injective (sub_eq_zero.mp hsame)
    exact hdrift (mul_right_cancel₀ hduration.ne' (neg_inj.mp hexponent)).symm

/-- **The counterexample in numbers.**  Two demes split with `T = 0` or `T = 1`, each with
probability one half, at recombination rate `1`, with every ancestral moment equal to one.
Populations of size `1` (`constantSizeRates 2 0`) and of size `e` (`constantSizeRates 2 1`) give
the same average ratio and different pooled ratios. -/
theorem pooledSplitPortabilityRatio_depends_on_drift :
    meanSplitPortabilityRatio (neutralLinkageRates (constantSizeRates 2 0) 1) 0 1 (fun _ ↦ 1)
        (twoPointSplitLaw 1)
      = meanSplitPortabilityRatio (neutralLinkageRates (constantSizeRates 2 1) 1) 0 1 (fun _ ↦ 1)
        (twoPointSplitLaw 1) ∧
    pooledSplitPortabilityRatio (neutralLinkageRates (constantSizeRates 2 0) 1) 0 1 (fun _ ↦ 1)
        (twoPointSplitLaw 1)
      ≠ pooledSplitPortabilityRatio (neutralLinkageRates (constantSizeRates 2 1) 1) 0 1
        (fun _ ↦ 1) (twoPointSplitLaw 1) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hsource : ancestralSquaredCorrelation (D := 2) (fun _ ↦ 1) 0 ≠ 0 := by
    simp [ancestralSquaredCorrelation]
  have hsupport := ae_twoPointSplitLaw_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨?_, pooledSplitPortabilityRatio_ne_of_drift_ne _ _ hne _ hsource one_pos one_pos ?_⟩
  · rw [meanSplitPortabilityRatio_neutralLinkageRates _ _ hne _ hsource _ hsupport,
      meanSplitPortabilityRatio_neutralLinkageRates _ _ hne _ hsource _ hsupport]
  · have hlt : Real.exp (-1) < Real.exp (-0) := Real.exp_lt_exp.mpr (by norm_num)
    show Real.exp (-0) + Real.exp (-0) ≠ Real.exp (-1) + Real.exp (-1)
    intro hsum
    linarith

end

end Descent.Portability.PortabilityCurveIdentifiability
