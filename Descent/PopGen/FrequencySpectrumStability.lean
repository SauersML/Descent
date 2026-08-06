/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.SpectrumIdentifiability
import Mathlib.Data.Nat.Choose.Sum

assert_below Descent.Spectral Descent.Conditionals Descent.Portability Descent.Decision
assert_below Descent.Program

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Blindness`:
--   Blindness: reaches 2 module(s) -- `Descent.Blindness.MultipleMergerBlindness`, `Descent.Blindness.SpectrumIdentifiability`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.PopGen

/-!
# Fixed-epoch frequency-spectrum stability

This file formalizes the finite algebra that drives the sharp fixed-epoch inverse modulus for
population histories.  A model with at most `K` epochs is identified from `2K - 3` independent
frequency-spectrum coordinates.  The collision construction is the alternating binomial
finite difference of order `2K - 3`; its Laplace response is exactly a power of that order.

The formal results include:

* the exact sample and spectrum-coordinate counts;
* the inverse Hölder exponent and its concrete values for two, three, and four epochs;
* the exact spectrum-precision and independent-sample multipliers needed to improve history
  error by a prescribed factor;
* the exact multiplicative cost of adding one epoch;
* the alternating-binomial identity producing an order-`p` collision;
* the first-order-versus-order-`p` scaling relation that makes exponent `1 / p` sharp.

The `K`-epoch restriction is not a convenience. `SpectrumIdentifiability` shows that without a
finite-dimensional sieve there is no exponent to prove: the reciprocal Kingman rate sum
converges, so on any interval there are nonzero smooth histories the spectrum cannot see at any
sample size, and the minimax risk is bounded away from zero rather than converging slowly. The
exponent below describes the sieve, and the sieve is what makes it meaningful.

The analytic Chebyshev-system upper bound and the calendar/coalescent-time bi-Lipschitz theorem
require a developed theory of bounded piecewise-constant histories and are not asserted here.
The algebra below is unconditional and is the load-bearing sharpness mechanism those analytic
steps consume.

The last section records the intrinsic operator boundary: a linear observation identifies a
model class exactly when the class difference set meets its kernel only at zero.  The separate
`SpectrumIdentifiability` module proves the finite-dimensional null-direction theorem and the
stronger all-sample Müntz obstruction, avoiding two copies of the same rank argument here.

## Main results

- `epochLineageSampleSize_add_epochs`: two additional lineages per added epoch.
- `spectrumPrecisionMultiplier_add_epochs`: exact `factor ^ (2 * extra)` precision cost.
- `independentSampleMultiplier_add_epochs`: exact `factor ^ (4 * extra)` data cost.
- `canonicalGenomeMultiplierForEpochCoordinates_add_epochs`: exponential linear-core cost.
- `fixedEpochSampleRateExponent_strictAnti`: global worsening of statistical rates.
- `collisionSpectrumDiscrepancy_eq_distance_pow`: the sharp finite-difference collision.
- `targetIdentifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset_ker`:
  exact class-relative criterion for recoverable derived targets.
- `identifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset`: intrinsic
  nullspace criterion without a nonemptiness assumption.
-/

open scoped BigOperators

/-- Number of nonredundant spectrum coordinates needed by a `K`-epoch model. -/
def epochSpectrumCoordinateCount (K : ℕ) : ℕ :=
  2 * K - 3

/-- Smallest lineage sample size supplying `2K - 3` unfolded spectrum entries. -/
def epochLineageSampleSize (K : ℕ) : ℕ :=
  Descent.Core.pairedEpochCount K

/-- The fixed-epoch inverse Hölder exponent. -/
noncomputable def fixedEpochInverseExponent (K : ℕ) : ℝ :=
  (epochSpectrumCoordinateCount K : ℝ)⁻¹

/-- A one-epoch model has `2K - 3 = 0` spectrum coordinates in truncated subtraction, so the
inverse is Mathlib's junk `0`.  Read as an exponent that would mean no stability at all,
whereas a constant history has nothing to reconstruct.  Every result above assumes `2 ≤ K`. -/
theorem fixedEpochInverseExponent_at_one_epoch_is_junk :
    fixedEpochInverseExponent 1 = 0 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]


/-- A sample of size `2K - 2` has exactly `2K - 3` nontrivial unfolded spectrum entries. -/
theorem epochLineageSampleSize_sub_one (K : ℕ) (hK : 2 ≤ K) :
    epochLineageSampleSize K - 1 = epochSpectrumCoordinateCount K := by
  unfold epochLineageSampleSize epochSpectrumCoordinateCount Descent.Core.pairedEpochCount
  omega

/-- Adding `extra` demographic epochs requires exactly `2 * extra` additional sampled
lineages in the minimal identifying SFS design. -/
theorem epochLineageSampleSize_add_epochs (K extra : ℕ) (hK : 1 ≤ K) :
    epochLineageSampleSize (K + extra) = epochLineageSampleSize K + 2 * extra := by
  unfold epochLineageSampleSize Descent.Core.pairedEpochCount
  omega

/-- The collision order is positive for every model with at least two epochs. -/
theorem epochSpectrumCoordinateCount_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < epochSpectrumCoordinateCount K := by
  unfold epochSpectrumCoordinateCount
  omega

/-- The coordinate count vanishes exactly for the trivial zero- and one-epoch indices. -/
theorem epochSpectrumCoordinateCount_eq_zero_iff (K : ℕ) :
    epochSpectrumCoordinateCount K = 0 ↔ K ≤ 1 := by
  unfold epochSpectrumCoordinateCount
  omega

/-- The inverse exponent is positive on the fixed-epoch model domain. -/
theorem fixedEpochInverseExponent_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < fixedEpochInverseExponent K := by
  unfold fixedEpochInverseExponent
  exact inv_pos.mpr (by exact_mod_cast epochSpectrumCoordinateCount_pos K hK)

/-- The deterministic inverse exponent is zero exactly outside the nontrivial epoch domain. -/
theorem fixedEpochInverseExponent_eq_zero_iff (K : ℕ) :
    fixedEpochInverseExponent K = 0 ↔ K ≤ 1 := by
  simp only [fixedEpochInverseExponent, inv_eq_zero, Nat.cast_eq_zero]
  exact epochSpectrumCoordinateCount_eq_zero_iff K

/-- Exact positivity domain of the deterministic inverse exponent. -/
theorem fixedEpochInverseExponent_pos_iff (K : ℕ) :
    0 < fixedEpochInverseExponent K ↔ 2 ≤ K := by
  constructor
  · intro hpos
    by_contra hK
    have hsmall : K ≤ 1 := by omega
    rw [(fixedEpochInverseExponent_eq_zero_iff K).2 hsmall] at hpos
    exact lt_irrefl 0 hpos
  · exact fixedEpochInverseExponent_pos K

/-- Two-epoch inference is Lipschitz. -/
@[simp] theorem fixedEpochInverseExponent_two :
    fixedEpochInverseExponent 2 = 1 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Three epochs already have cube-root stability. -/
@[simp] theorem fixedEpochInverseExponent_three :
    fixedEpochInverseExponent 3 = 1 / 3 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Four epochs have fifth-root stability. -/
@[simp] theorem fixedEpochInverseExponent_four :
    fixedEpochInverseExponent 4 = 1 / 5 := by
  norm_num [fixedEpochInverseExponent, epochSpectrumCoordinateCount]

/-- Precision multiplier in the expected spectrum needed to improve history error by `factor`. -/
def spectrumPrecisionMultiplier (K factor : ℕ) : ℕ :=
  factor ^ epochSpectrumCoordinateCount K

/-- Independent-data multiplier under root-sample spectrum error. -/
def independentSampleMultiplier (K factor : ℕ) : ℕ :=
  factor ^ (2 * epochSpectrumCoordinateCount K)

/-- Precision budgets compose multiplicatively. -/
theorem spectrumPrecisionMultiplier_mul (K left right : ℕ) :
    spectrumPrecisionMultiplier K (left * right) =
      spectrumPrecisionMultiplier K left * spectrumPrecisionMultiplier K right := by
  simp [spectrumPrecisionMultiplier, mul_pow]

/-- Under root-sample spectrum error, the independent-data multiplier is exactly the square
of the deterministic precision multiplier. -/
theorem independentSampleMultiplier_eq_precision_sq (K factor : ℕ) :
    independentSampleMultiplier K factor = spectrumPrecisionMultiplier K factor ^ 2 := by
  -- `factor ^ (2 * c) = (factor ^ c) ^ 2` is `pow_mul` with the factors the other
  -- way round; reaching it through `Nat.mul_comm` inside the simp set left the
  -- goal on whichever orientation simp normalised to first.
  rw [independentSampleMultiplier, spectrumPrecisionMultiplier, Nat.mul_comm, pow_mul]

/-- Adding one epoch costs exactly two further powers of spectrum precision. -/
theorem spectrumPrecisionMultiplier_succ (K factor : ℕ) (hK : 2 ≤ K) :
    spectrumPrecisionMultiplier (K + 1) factor =
      spectrumPrecisionMultiplier K factor * factor ^ 2 := by
  unfold spectrumPrecisionMultiplier epochSpectrumCoordinateCount
  have hcount : 2 * (K + 1) - 3 = (2 * K - 3) + 2 := by omega
  rw [hcount, pow_add]

/-- Under root-sample spectrum error, adding one epoch costs exactly four further powers of
independent data.  For halving error this is the factor `2⁴ = 16` visible between adjacent
rows of the design table. -/
theorem independentSampleMultiplier_succ (K factor : ℕ) (hK : 2 ≤ K) :
    independentSampleMultiplier (K + 1) factor =
      independentSampleMultiplier K factor * factor ^ 4 := by
  unfold independentSampleMultiplier epochSpectrumCoordinateCount
  have hcount : 2 * (K + 1) - 3 = (2 * K - 3) + 2 := by omega
  rw [hcount, Nat.mul_add, pow_add]

/-- Adding `extra` epochs adds exactly `2 * extra` independent spectrum coordinates. -/
theorem epochSpectrumCoordinateCount_add_epochs (K extra : ℕ) (hK : 2 ≤ K) :
    epochSpectrumCoordinateCount (K + extra) =
      epochSpectrumCoordinateCount K + 2 * extra := by
  unfold epochSpectrumCoordinateCount
  omega

/-- **General complexity law for spectrum precision.** Adding `extra` epochs multiplies the
required spectrum precision by exactly `factor ^ (2 * extra)`.  This is the arbitrary-jump
form of `spectrumPrecisionMultiplier_succ`. -/
theorem spectrumPrecisionMultiplier_add_epochs (K extra factor : ℕ) (hK : 2 ≤ K) :
    spectrumPrecisionMultiplier (K + extra) factor =
      spectrumPrecisionMultiplier K factor * factor ^ (2 * extra) := by
  unfold spectrumPrecisionMultiplier
  rw [epochSpectrumCoordinateCount_add_epochs K extra hK, pow_add]

/-- **General complexity law for independent data.** Under root-sample spectrum error,
adding `extra` epochs multiplies the required independent data by exactly
`factor ^ (4 * extra)`. -/
theorem independentSampleMultiplier_add_epochs (K extra factor : ℕ) (hK : 2 ≤ K) :
    independentSampleMultiplier (K + extra) factor =
      independentSampleMultiplier K factor * factor ^ (4 * extra) := by
  unfold independentSampleMultiplier
  rw [epochSpectrumCoordinateCount_add_epochs K extra hK, Nat.mul_add, pow_add]
  congr 2
  omega

/-! ### Coupling epoch complexity to canonical Laplace conditioning -/

/-- Independent-data multiplier needed for the canonical linear Laplace core to support all
`2K - 3` coordinates of a `K`-epoch model when the per-coordinate conditioning exponent is
`kappa`. This prices the linear core only; boundary collisions still impose the separate
Hölder law formalized above.

Empirical status: NOT AN EMPIRICAL CLAIM. The body raises the supplied `factor` to
`kappa * (2K - 3)`, where `2K - 3` is `epochSpectrumCoordinateCount` -- a count read off the
model's own parametrisation -- and `kappa` is a free argument. Given both, the multiplier is
arithmetic, and no inference problem can make it a different number. The theorems below fix
how it scales with the epoch count, and that scaling is algebra on the exponent. The one
thing with observable content, the value of `kappa` for any real inference problem, is a
parameter of the statement and not a number this corpus has pinned; it is an input, so the
claim about it is a claim about consumers of this definition rather than about this body. -/
noncomputable def canonicalGenomeMultiplierForEpochCoordinates
    (kappa : ℝ) (K : ℕ) : ℝ :=
  Real.exp (kappa * epochSpectrumCoordinateCount K)

/-- The canonical multiplier buys exactly the coordinate count it was designed for. -/
theorem stableSieveDimension_canonicalGenomeMultiplierForEpochCoordinates
    (kappa : ℝ) (K : ℕ) (hkappa : kappa ≠ 0) :
    Blindness.SpectrumIdentifiability.stableSieveDimension kappa
        (canonicalGenomeMultiplierForEpochCoordinates kappa K) =
      epochSpectrumCoordinateCount K := by
  have hscaled := Blindness.SpectrumIdentifiability.stableSieveDimension_of_scaled
    kappa 1 (epochSpectrumCoordinateCount K) hkappa (by norm_num)
  simpa [canonicalGenomeMultiplierForEpochCoordinates] using hscaled

/-- **Exact fixed-epoch feasibility criterion.** At positive conditioning exponent and genome
length, a `K`-epoch model's full `2K - 3` coordinate set fits inside the stable Laplace sieve if
and only if its canonical exponential data budget is available. -/
theorem epochCoordinates_le_stableSieveDimension_iff
    (kappa L : ℝ) (K : ℕ) (hkappa : 0 < kappa) (hL : 0 < L) :
    (epochSpectrumCoordinateCount K : ℝ) ≤
        Blindness.SpectrumIdentifiability.stableSieveDimension kappa L ↔
      canonicalGenomeMultiplierForEpochCoordinates kappa K ≤ L := by
  simpa [canonicalGenomeMultiplierForEpochCoordinates] using
    Blindness.SpectrumIdentifiability.le_stableSieveDimension_iff
      kappa L (epochSpectrumCoordinateCount K) hkappa hL

/-- **Exact per-epoch price in the canonical Laplace core.** Adding `extra` epochs adds
`2 * extra` stable spectral coordinates and therefore multiplies the independent-data budget
by `exp (kappa * (2 * extra))`. In particular, one epoch costs `exp (2 * kappa)`. -/
theorem canonicalGenomeMultiplierForEpochCoordinates_add_epochs
    (kappa : ℝ) (K extra : ℕ) (hK : 2 ≤ K) :
    canonicalGenomeMultiplierForEpochCoordinates kappa (K + extra) =
      canonicalGenomeMultiplierForEpochCoordinates kappa K *
        Real.exp (kappa * (2 * extra)) := by
  rw [canonicalGenomeMultiplierForEpochCoordinates,
    canonicalGenomeMultiplierForEpochCoordinates,
    epochSpectrumCoordinateCount_add_epochs K extra hK]
  rw [show kappa * ((epochSpectrumCoordinateCount K + 2 * extra : ℕ) : ℝ) =
    kappa * epochSpectrumCoordinateCount K + kappa * (2 * extra) by push_cast; ring,
    Real.exp_add]

/-- **Exact one-epoch price at the Cauchy root.**  A new epoch contributes two spectrum
coordinates.  Since independent-data cost squares inverse singular-value cost, its exact
multiplier is the fourth power of the stationary per-direction base
`(1 + θ²) / (1 - θ²)`. -/
theorem canonicalGenomeMultiplierForEpochCoordinates_succ_at_stationary
    (θ : ℝ) (K : ℕ) (hK : 2 ≤ K) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstationary : Blindness.SpectrumIdentifiability.CauchyConditioningStationary θ) :
    canonicalGenomeMultiplierForEpochCoordinates
        (Blindness.SpectrumIdentifiability.cauchyConditioningProfile θ) (K + 1) =
      canonicalGenomeMultiplierForEpochCoordinates
          (Blindness.SpectrumIdentifiability.cauchyConditioningProfile θ) K *
        ((1 + θ ^ 2) / (1 - θ ^ 2)) ^ 4 := by
  rw [canonicalGenomeMultiplierForEpochCoordinates_add_epochs _ K 1 hK]
  have hbase :=
    Blindness.SpectrumIdentifiability.exp_half_cauchyConditioningProfile_at_stationary
      θ hθ0 hθ1 hstationary
  rw [show Blindness.SpectrumIdentifiability.cauchyConditioningProfile θ * (2 * (1 : ℕ)) =
    (4 : ℕ) * (Blindness.SpectrumIdentifiability.cauchyConditioningProfile θ / 2) by
      norm_num
      ring]
  rw [Real.exp_nat_mul, hbase]

/-- The actionable spectrum-precision table for halving history error. -/
theorem spectrumPrecisionMultiplier_halving_table :
    spectrumPrecisionMultiplier 2 2 = 2 ∧
      spectrumPrecisionMultiplier 3 2 = 8 ∧
      spectrumPrecisionMultiplier 4 2 = 32 ∧
      spectrumPrecisionMultiplier 5 2 = 128 := by
  norm_num [spectrumPrecisionMultiplier, epochSpectrumCoordinateCount]

/-- The corresponding independent-sample table when spectrum error is proportional to
`sampleSize⁻¹ᐟ²`. -/
theorem independentSampleMultiplier_halving_table :
    independentSampleMultiplier 2 2 = 4 ∧
      independentSampleMultiplier 3 2 = 64 ∧
      independentSampleMultiplier 4 2 = 1024 ∧
      independentSampleMultiplier 5 2 = 16384 := by
  norm_num [independentSampleMultiplier, epochSpectrumCoordinateCount]

/-- Statistical exponent inherited from root-sample estimation of the spectrum. -/
noncomputable def fixedEpochSampleRateExponent (K : ℕ) : ℝ :=
  (2 * epochSpectrumCoordinateCount K : ℝ)⁻¹

/-- The same boundary for the statistical exponent. -/
theorem fixedEpochSampleRateExponent_at_one_epoch_is_junk :
    fixedEpochSampleRateExponent 1 = 0 := by
  norm_num [fixedEpochSampleRateExponent, epochSpectrumCoordinateCount]


/-- Root-sample estimation halves the deterministic inverse exponent exactly. -/
theorem fixedEpochSampleRateExponent_eq_half_inverse (K : ℕ) (hK : 2 ≤ K) :
    fixedEpochSampleRateExponent K = fixedEpochInverseExponent K / 2 := by
  have hp : (epochSpectrumCoordinateCount K : ℝ) ≠ 0 := by
    exact_mod_cast (epochSpectrumCoordinateCount_pos K hK).ne'
  unfold fixedEpochSampleRateExponent fixedEpochInverseExponent
  field_simp

/-- The statistical rate exponent is positive on the model domain. -/
theorem fixedEpochSampleRateExponent_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < fixedEpochSampleRateExponent K := by
  rw [fixedEpochSampleRateExponent_eq_half_inverse K hK]
  exact div_pos (fixedEpochInverseExponent_pos K hK) (by norm_num)

/-- The root-sample exponent has the same exact zero boundary as its deterministic parent. -/
theorem fixedEpochSampleRateExponent_eq_zero_iff (K : ℕ) :
    fixedEpochSampleRateExponent K = 0 ↔ K ≤ 1 := by
  simp only [fixedEpochSampleRateExponent, inv_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or]
  exact epochSpectrumCoordinateCount_eq_zero_iff K

/-- Exact positivity domain of the root-sample exponent. -/
theorem fixedEpochSampleRateExponent_pos_iff (K : ℕ) :
    0 < fixedEpochSampleRateExponent K ↔ 2 ≤ K := by
  constructor
  · intro hpos
    by_contra hK
    have hsmall : K ≤ 1 := by omega
    rw [(fixedEpochSampleRateExponent_eq_zero_iff K).2 hsmall] at hpos
    exact lt_irrefl 0 hpos
  · exact fixedEpochSampleRateExponent_pos K

/-- **The epoch coordinate count is positive, and strictly increasing, as a real.**

Both strict-antitonicity proofs below start from exactly this comparison and each carried
its own copy of the four steps that produce it: the positivity, the natural-number
inequality, and the two casts. -/
theorem epochSpectrumCoordinateCount_lt_real {K L : ℕ} (hK : 2 ≤ K) (hKL : K < L) :
    (0 : ℝ) < epochSpectrumCoordinateCount K ∧
      (epochSpectrumCoordinateCount K : ℝ) < epochSpectrumCoordinateCount L := by
  have hcountK : 0 < epochSpectrumCoordinateCount K :=
    epochSpectrumCoordinateCount_pos K hK
  have hcount : epochSpectrumCoordinateCount K < epochSpectrumCoordinateCount L := by
    unfold epochSpectrumCoordinateCount
    omega
  exact ⟨by exact_mod_cast hcountK, by exact_mod_cast hcount⟩

/-- Statistical convergence strictly worsens throughout the fixed-epoch hierarchy: every
additional epoch lowers the root-sample inverse exponent. -/
theorem fixedEpochSampleRateExponent_strictAnti
    {K L : ℕ} (hK : 2 ≤ K) (hKL : K < L) :
    fixedEpochSampleRateExponent L < fixedEpochSampleRateExponent K := by
  unfold fixedEpochSampleRateExponent
  obtain ⟨hcountKReal, hcountReal⟩ := epochSpectrumCoordinateCount_lt_real hK hKL
  have hdenK : (0 : ℝ) < 2 * epochSpectrumCoordinateCount K := by
    nlinarith
  have hden : (2 * epochSpectrumCoordinateCount K : ℝ) <
      2 * epochSpectrumCoordinateCount L := by
    nlinarith
  exact (inv_lt_inv₀ (hdenK.trans hden) hdenK).2 hden

/-- A five-epoch history has the slow `sampleSize⁻¹ᐟ¹⁴` rate. -/
@[simp] theorem fixedEpochSampleRateExponent_five :
    fixedEpochSampleRateExponent 5 = 1 / 14 := by
  norm_num [fixedEpochSampleRateExponent, epochSpectrumCoordinateCount]

/-! ## The alternating-binomial collision -/

/-- Alternating binomial response evaluated at a geometric attenuation `x`. -/
noncomputable def alternatingBinomialResponse (order : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (order + 1), (-x) ^ j * (order.choose j : ℝ)

/-- **Exact finite-difference identity.**  The order-`p` alternating collision has response
`(1 - x)^p`. -/
theorem alternatingBinomialResponse_eq (order : ℕ) (x : ℝ) :
    alternatingBinomialResponse order x = (1 - x) ^ order := by
  have h := add_pow (-x) 1 order
  simpa [alternatingBinomialResponse, sub_eq_add_neg, add_comm] using h.symm

/-- At zero attenuation the normalized collision is fully visible. -/
@[simp] theorem alternatingBinomialResponse_zero (order : ℕ) :
    alternatingBinomialResponse order 0 = 1 := by
  rw [alternatingBinomialResponse_eq]
  simp

/-- At unit attenuation every positive-order collision is invisible. -/
@[simp] theorem alternatingBinomialResponse_one (order : ℕ) (horder : order ≠ 0) :
    alternatingBinomialResponse order 1 = 0 := by
  rw [alternatingBinomialResponse_eq]
  simp [horder]

/-- Evaluating at `1 - resolution` exposes the exact order of vanishing. -/
theorem alternatingBinomialResponse_one_sub (order : ℕ) (resolution : ℝ) :
    alternatingBinomialResponse order (1 - resolution) = resolution ^ order := by
  rw [alternatingBinomialResponse_eq]
  congr 1
  ring

/-- A normalized pair of collision histories differs at first order in `resolution`. -/
noncomputable def collisionHistoryDistance (scale resolution : ℝ) : ℝ :=
  Descent.Core.product scale resolution

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem collisionHistoryDistance_at_reference_point :
    collisionHistoryDistance 2 2 = 4 := by
  norm_num [collisionHistoryDistance,
      Descent.Core.product]


/-- Its normalized frequency-spectrum discrepancy is order `order`. -/
noncomputable def collisionSpectrumDiscrepancy
    (order : ℕ) (scale resolution : ℝ) : ℝ :=
  scale ^ order * alternatingBinomialResponse order (1 - resolution)

/-- The frequency-spectrum discrepancy is exactly the `order`-th power of history distance.
This is the algebraic sharpness statement: any inverse modulus with exponent larger than
`1 / order` fails on this collision family as the resolution tends to zero. -/
theorem collisionSpectrumDiscrepancy_eq_distance_pow
    (order : ℕ) (scale resolution : ℝ) :
    collisionSpectrumDiscrepancy order scale resolution =
      collisionHistoryDistance scale resolution ^ order := by
  rw [collisionSpectrumDiscrepancy, alternatingBinomialResponse_one_sub,
    collisionHistoryDistance, Descent.Core.product, mul_pow]

/-- Specialization to the sharp collision order of a `K`-epoch model. -/
theorem fixedEpochCollision_spectrum_eq_history_pow
    (K : ℕ) (scale resolution : ℝ) :
    collisionSpectrumDiscrepancy (epochSpectrumCoordinateCount K) scale resolution =
      collisionHistoryDistance scale resolution ^ epochSpectrumCoordinateCount K :=
  collisionSpectrumDiscrepancy_eq_distance_pow _ _ _

/-- Each additional epoch adds two independent spectrum coordinates to the collision order. -/
theorem epochSpectrumCoordinateCount_succ (K : ℕ) (hK : 2 ≤ K) :
    epochSpectrumCoordinateCount (K + 1) = epochSpectrumCoordinateCount K + 2 := by
  unfold epochSpectrumCoordinateCount
  omega

/-- Every additional epoch strictly worsens the deterministic inverse exponent. -/
theorem fixedEpochInverseExponent_succ_lt (K : ℕ) (hK : 2 ≤ K) :
    fixedEpochInverseExponent (K + 1) < fixedEpochInverseExponent K := by
  unfold fixedEpochInverseExponent
  rw [epochSpectrumCoordinateCount_succ K hK]
  push_cast
  have hp : (0 : ℝ) < epochSpectrumCoordinateCount K := by
    exact_mod_cast epochSpectrumCoordinateCount_pos K hK
  exact (inv_lt_inv₀ (by linarith) hp).2 (by linarith)

/-- The deterministic inverse exponent is strictly decreasing across the entire fixed-epoch
hierarchy, not only between adjacent epoch counts. -/
theorem fixedEpochInverseExponent_strictAnti
    {K L : ℕ} (hK : 2 ≤ K) (hKL : K < L) :
    fixedEpochInverseExponent L < fixedEpochInverseExponent K := by
  unfold fixedEpochInverseExponent
  obtain ⟨hcountKReal, hcountReal⟩ := epochSpectrumCoordinateCount_lt_real hK hKL
  exact (inv_lt_inv₀ (hcountKReal.trans hcountReal) hcountKReal).2 hcountReal

/-! ## Intrinsic nullspace boundary for unrestricted history classes -/

/-- A model class is identifiable under a linear observation when the observation is injective
on that class. -/
def IdentifiableUnderLinearObservation
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (observation : V →ₗ[R] W) (modelClass : Set V) : Prop :=
  Set.InjOn observation modelClass

/-- Restricting the admissible model class preserves identifiability. -/
theorem IdentifiableUnderLinearObservation.mono
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {observation : V →ₗ[R] W} {large small : Set V}
    (hidentifiable : IdentifiableUnderLinearObservation observation large)
    (hsubset : small ⊆ large) :
    IdentifiableUnderLinearObservation observation small := by
  intro left hleft right hright heq
  exact hidentifiable (hsubset hleft) (hsubset hright) heq

/-- **Identifiability data processing.** If a processed observation still identifies the model
class, then the original, more informative observation identifies it as well. -/
theorem IdentifiableUnderLinearObservation.of_postcomp
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (processing : W →ₗ[R] Z) (modelClass : Set V)
    (hidentifiable :
      IdentifiableUnderLinearObservation (processing.comp observation) modelClass) :
    IdentifiableUnderLinearObservation observation modelClass := by
  intro left hleft right hright heq
  apply hidentifiable hleft hright
  simp only [LinearMap.comp_apply, heq]

/-- Injective recoding of the observation space preserves identifiability exactly. -/
theorem identifiableUnderLinearObservation_postcomp_iff
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (processing : W →ₗ[R] Z) (modelClass : Set V)
    (hprocessing : Function.Injective processing) :
    IdentifiableUnderLinearObservation (processing.comp observation) modelClass ↔
      IdentifiableUnderLinearObservation observation modelClass := by
  constructor
  · exact fun h ↦ h.of_postcomp observation processing modelClass
  · intro hidentifiable left hleft right hright heq
    apply hidentifiable hleft hright
    exact hprocessing heq

/-- All coefficient differences generated by pairs of admissible models. -/
def modelDifferenceSet {V : Type*} [Sub V] (modelClass : Set V) : Set V :=
  {difference | ∃ left ∈ modelClass, ∃ right ∈ modelClass, difference = left - right}

/-- A derived target is identifiable on a model class when observation-equivalent admissible
models always have the same target value. This permits useful functionals to remain identifiable
even when the full model is not. -/
def TargetIdentifiableUnderLinearObservation
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (target : V →ₗ[R] Z) (modelClass : Set V) : Prop :=
  ∀ left ∈ modelClass, ∀ right ∈ modelClass,
    observation left = observation right → target left = target right

/-- Restricting the biological model class preserves identifiability of every target. -/
theorem TargetIdentifiableUnderLinearObservation.mono
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    {observation : V →ₗ[R] W} {target : V →ₗ[R] Z} {large small : Set V}
    (hidentifiable : TargetIdentifiableUnderLinearObservation observation target large)
    (hsubset : small ⊆ large) :
    TargetIdentifiableUnderLinearObservation observation target small := by
  intro left hleft right hright hequal
  exact hidentifiable left (hsubset hleft) right (hsubset hright) hequal

/-- Processing an observation cannot make a previously unidentified target identifiable: if
the processed observation suffices, then the original observation suffices. -/
theorem TargetIdentifiableUnderLinearObservation.of_processedObservation
    {R V W Y Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (processing : W →ₗ[R] Y) (target : V →ₗ[R] Z)
    (modelClass : Set V)
    (hidentifiable :
      TargetIdentifiableUnderLinearObservation (processing.comp observation) target modelClass) :
    TargetIdentifiableUnderLinearObservation observation target modelClass := by
  intro left hleft right hright hequal
  apply hidentifiable left hleft right hright
  simp only [LinearMap.comp_apply, hequal]

/-- Every linear summary of an identifiable target remains identifiable on the same model
class. -/
theorem TargetIdentifiableUnderLinearObservation.postcomp
    {R V W Y Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    {observation : V →ₗ[R] W} {target : V →ₗ[R] Y} {modelClass : Set V}
    (hidentifiable : TargetIdentifiableUnderLinearObservation observation target modelClass)
    (processing : Y →ₗ[R] Z) :
    TargetIdentifiableUnderLinearObservation observation (processing.comp target) modelClass := by
  intro left hleft right hright hequal
  simp only [LinearMap.comp_apply, hidentifiable left hleft right hright hequal]

/-- **Class-relative functional-identifiability criterion.** A target is recoverable on a model
class exactly when every admissible difference invisible to the observation is also invisible
to the target. -/
theorem targetIdentifiableUnderLinearObservation_iff_difference_kernel
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (target : V →ₗ[R] Z) (modelClass : Set V) :
    TargetIdentifiableUnderLinearObservation observation target modelClass ↔
      ∀ left ∈ modelClass, ∀ right ∈ modelClass,
        left - right ∈ LinearMap.ker observation →
          left - right ∈ LinearMap.ker target := by
  constructor
  · intro hdetermined left hleft right hright hkernel
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hkernel ⊢
    exact hdetermined left hleft right hright hkernel
  · intro hkernel left hleft right hright hequal
    have hdifference : left - right ∈ LinearMap.ker observation := by
      rw [LinearMap.mem_ker, map_sub, hequal, sub_self]
    have htarget := hkernel left hleft right hright hdifference
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at htarget
    exact htarget

/-- **Set-valued target criterion.** The identifiable part of a nonparametric class is exactly
the quotient by admissible observation-null directions; a target survives precisely when its
kernel contains that intersection. -/
theorem targetIdentifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset_ker
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (target : V →ₗ[R] Z) (modelClass : Set V) :
    TargetIdentifiableUnderLinearObservation observation target modelClass ↔
      modelDifferenceSet modelClass ∩ LinearMap.ker observation ⊆
        LinearMap.ker target := by
  rw [targetIdentifiableUnderLinearObservation_iff_difference_kernel]
  constructor
  · intro hkernel difference hdifference
    rcases hdifference.1 with ⟨left, hleft, right, hright, rfl⟩
    exact hkernel left hleft right hright hdifference.2
  · intro hsubset left hleft right hright hkernel
    exact hsubset ⟨⟨left, hleft, right, hright, rfl⟩, hkernel⟩

/-- Full model identifiability is target identifiability for the identity map. -/
theorem targetIdentifiableUnderLinearObservation_id_iff
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (observation : V →ₗ[R] W) (modelClass : Set V) :
    TargetIdentifiableUnderLinearObservation observation LinearMap.id modelClass ↔
      IdentifiableUnderLinearObservation observation modelClass := by
  rfl

/-- The global functional criterion in `SpectrumIdentifiability` is exactly the unrestricted
model-class specialization of the class-relative criterion. -/
theorem targetIdentifiableUnderLinearObservation_univ_iff
    {R V W Z : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (observation : V →ₗ[R] W) (target : V →ₗ[R] Z) :
    TargetIdentifiableUnderLinearObservation observation target Set.univ ↔
      Blindness.SpectrumIdentifiability.LinearTargetDeterminedByObservation observation target := by
  constructor
  · intro hdetermined left right hequal
    exact hdetermined left (Set.mem_univ left) right (Set.mem_univ right) hequal
  · intro hdetermined left _ right _ hequal
    exact hdetermined left right hequal

/-- **Intrinsic identifiability criterion.**  The data identify a class exactly when no
nonzero difference of two admissible histories belongs to the observation kernel. -/
theorem identifiableUnderLinearObservation_iff_difference_kernel
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (observation : V →ₗ[R] W) (modelClass : Set V) :
    IdentifiableUnderLinearObservation observation modelClass ↔
      ∀ left ∈ modelClass, ∀ right ∈ modelClass,
        left - right ∈ LinearMap.ker observation → left = right := by
  constructor
  · intro hinjective left hleft right hright hkernel
    apply hinjective hleft hright
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hkernel
    exact hkernel
  · intro hkernel left hleft right hright hequal
    apply hkernel left hleft right hright
    rw [LinearMap.mem_ker, map_sub, hequal, sub_self]

/-- **Set-valued intrinsic criterion.**  Identifiability is equivalent to saying that every
admissible difference killed by the observation is zero.  The subset formulation is exact
even for an empty model class, unlike the customary equality with the singleton `{0}`. -/
theorem identifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (observation : V →ₗ[R] W) (modelClass : Set V) :
    IdentifiableUnderLinearObservation observation modelClass ↔
      modelDifferenceSet modelClass ∩ LinearMap.ker observation ⊆ {0} := by
  rw [identifiableUnderLinearObservation_iff_difference_kernel]
  constructor
  · intro hkernel difference hdifference
    rcases hdifference.1 with ⟨left, hleft, right, hright, rfl⟩
    apply Set.mem_singleton_iff.mpr
    exact sub_eq_zero.mpr (hkernel left hleft right hright hdifference.2)
  · intro hsubset left hleft right hright hkernel
    have hdifference : left - right ∈
        modelDifferenceSet modelClass ∩ LinearMap.ker observation :=
      ⟨⟨left, hleft, right, hright, rfl⟩, hkernel⟩
    exact sub_eq_zero.mp (Set.mem_singleton_iff.mp (hsubset hdifference))

/-- For a nonempty class, the familiar formulation is valid literally: the admissible
difference set meets the observation kernel in exactly the zero singleton. -/
theorem identifiableUnderLinearObservation_iff_differenceSet_inter_kernel_eq
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (observation : V →ₗ[R] W) (modelClass : Set V) (hmodel : modelClass.Nonempty) :
    IdentifiableUnderLinearObservation observation modelClass ↔
      modelDifferenceSet modelClass ∩ LinearMap.ker observation = {0} := by
  rw [identifiableUnderLinearObservation_iff_differenceSet_inter_kernel_subset]
  constructor
  · intro hsubset
    apply Set.Subset.antisymm hsubset
    rintro difference (rfl : difference = 0)
    rcases hmodel with ⟨model, hmodel⟩
    exact ⟨⟨model, hmodel, model, hmodel, (sub_self model).symm⟩,
      LinearMap.mem_ker.mpr (map_zero observation)⟩
  · intro heq difference hdifference
    rw [heq] at hdifference
    exact hdifference

end Descent.PopGen
