/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.StarOrdered
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic
import Descent.Blindness.ObservationalCeiling
import Descent.Blindness.TrafficInvariantSeparation.ExponentialProfileCompactness

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.MatchedBayesBoundary`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


section MatchedBayesBoundary

/-- Primitive finite singular-value data sufficient for the standard
nuclear-norm/rank inequality.  The active set contains every nonzero singular
value, its cardinality is bounded by `rank`, and every singular value is at
most the operator bound.  No nuclear inequality is included as a field. -/
structure FiniteLowRankSingularSpectrum
    (Coordinate : Type*) [Fintype Coordinate] where
  singularValue : Coordinate → ℝ
  active : Finset Coordinate
  rank : ℕ
  operatorBound : ℝ
  operatorBound_nonnegative : 0 ≤ operatorBound
  singularValue_nonnegative : ∀ coordinate, 0 ≤ singularValue coordinate
  singularValue_le_operatorBound : ∀ coordinate,
    singularValue coordinate ≤ operatorBound
  inactive_zero : ∀ coordinate ∉ active, singularValue coordinate = 0
  active_card_le_rank : active.card ≤ rank

/-- The zero spectrum is a concrete inhabitant of the low-rank certificate
type; its support, rank, and operator bound all vanish.

Stated at an arbitrary finite coordinate type rather than at `PUnit`, because
what it is for is `finiteLowRankSingularSpectrum_nonempty` just below: every
result in this section is universally quantified over
`FiniteLowRankSingularSpectrum Coordinate`, and a universally quantified
statement about an uninhabited type is true for reasons that have nothing to do
with singular values. Pinning the witness to a one-point coordinate space would
have established non-vacuity at one dimension only, which is the dimension none
of the asymptotic results are about. -/
noncomputable def zeroFiniteLowRankSingularSpectrum
    (Coordinate : Type*) [Fintype Coordinate] :
    FiniteLowRankSingularSpectrum Coordinate where
  singularValue := fun _coordinate ↦ 0
  active := ∅
  rank := 0
  operatorBound := 0
  operatorBound_nonnegative := le_rfl
  singularValue_nonnegative := by simp
  singularValue_le_operatorBound := by simp
  inactive_zero := by simp
  active_card_le_rank := by simp

/-- **The low-rank certificate type is inhabited at every finite dimension**, so
the inequalities proved for it below are not vacuously true. -/
instance finiteLowRankSingularSpectrum_nonempty
    (Coordinate : Type*) [Fintype Coordinate] :
    Nonempty (FiniteLowRankSingularSpectrum Coordinate) :=
  ⟨zeroFiniteLowRankSingularSpectrum Coordinate⟩

/-- Raw nuclear distance represented by the sum of the certified singular
values. -/
noncomputable def FiniteLowRankSingularSpectrum.rawNuclearDistance
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  ∑ coordinate, spectrum.singularValue coordinate

/-- Dimension-normalized nuclear distance. -/
noncomputable def FiniteLowRankSingularSpectrum.normalizedNuclearDistance
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  spectrum.rawNuclearDistance / Fintype.card Coordinate

/-- Dimension-normalized rank. -/
noncomputable def FiniteLowRankSingularSpectrum.rankFraction
    {Coordinate : Type*} [Fintype Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) : ℝ :=
  spectrum.rank / Fintype.card Coordinate

/-- The primitive support and operator-bound facts imply the raw inequality
`nuclear ≤ operatorBound * rank`. -/
theorem FiniteLowRankSingularSpectrum.rawNuclearDistance_le_rank_mul_operatorBound
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate) :
    spectrum.rawNuclearDistance ≤ spectrum.operatorBound * spectrum.rank := by
  rw [FiniteLowRankSingularSpectrum.rawNuclearDistance]
  calc
    (∑ coordinate, spectrum.singularValue coordinate) =
        ∑ coordinate ∈ spectrum.active, spectrum.singularValue coordinate := by
      symm
      apply Finset.sum_subset spectrum.active.subset_univ
      intro coordinate _hcoordinate hinactive
      exact spectrum.inactive_zero coordinate hinactive
    _ ≤ ∑ _coordinate ∈ spectrum.active, spectrum.operatorBound := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact spectrum.singularValue_le_operatorBound coordinate
    _ = spectrum.active.card * spectrum.operatorBound := by simp
    _ ≤ spectrum.rank * spectrum.operatorBound := by
      exact mul_le_mul_of_nonneg_right
        (mod_cast spectrum.active_card_le_rank) spectrum.operatorBound_nonnegative
    _ = spectrum.operatorBound * spectrum.rank := by ring

/-- After division by a positive dimension, the standard normalized inequality
is exactly `normalizedNuclearDistance ≤ operatorBound * rankFraction`. -/
theorem FiniteLowRankSingularSpectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (hdimension : 0 < Fintype.card Coordinate) :
    spectrum.normalizedNuclearDistance ≤
      spectrum.operatorBound * spectrum.rankFraction := by
  have hdimensionReal : (0 : ℝ) < Fintype.card Coordinate := by exact_mod_cast hdimension
  rw [FiniteLowRankSingularSpectrum.normalizedNuclearDistance,
    FiniteLowRankSingularSpectrum.rankFraction]
  calc
    spectrum.rawNuclearDistance / Fintype.card Coordinate ≤
        (spectrum.operatorBound * spectrum.rank) / Fintype.card Coordinate :=
      div_le_div_of_nonneg_right
        spectrum.rawNuclearDistance_le_rank_mul_operatorBound hdimensionReal.le
    _ = spectrum.operatorBound *
        (spectrum.rank / Fintype.card Coordinate) := by ring

/-- The concrete singular-value spectrum of a rank-one perturbation on the
`p+1`-dimensional outlier coordinate space. -/
noncomputable def finiteRankOneSingularSpectrum
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    FiniteLowRankSingularSpectrum (FiniteOutlierCoordinate population) where
  singularValue
    | none => spikeStrength
    | some _coordinate => 0
  active := {none}
  rank := 1
  operatorBound := spikeStrength
  operatorBound_nonnegative := hspike
  singularValue_nonnegative := by
    intro coordinate
    cases coordinate <;> simp_all
  singularValue_le_operatorBound := by
    intro coordinate
    cases coordinate <;> simp_all
  inactive_zero := by
    intro coordinate hinactive
    cases coordinate with
    | none => simp at hinactive
    | some coordinate => rfl
  active_card_le_rank := by simp

/-- The rank-one spectrum has raw nuclear distance equal to its spike
strength. -/
theorem finiteRankOneSingularSpectrum_rawNuclearDistance
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rawNuclearDistance =
      spikeStrength := by
  simp [FiniteLowRankSingularSpectrum.rawNuclearDistance,
    finiteRankOneSingularSpectrum, FiniteOutlierCoordinate]

/-- **The nuclear/rank inequality is attained, so nothing in it can be
tightened.** `rawNuclearDistance_le_rank_mul_operatorBound` holds for every
certificate; the rank-one spike turns it into an equality, which is what rules
out a strictly better constant, a strictly smaller power of the rank, or an
additive slack. An inequality with no attaining model is compatible with a
sharper law that the corpus would then be understating. -/
theorem finiteRankOneSingularSpectrum_rawNuclearDistance_eq_bound
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rawNuclearDistance =
      (finiteRankOneSingularSpectrum population spikeStrength hspike).operatorBound *
        (finiteRankOneSingularSpectrum population spikeStrength hspike).rank := by
  rw [finiteRankOneSingularSpectrum_rawNuclearDistance]
  simp [finiteRankOneSingularSpectrum]

/-- Its normalized nuclear distance is exactly `spikeStrength/(p+1)`. -/
theorem finiteRankOneSingularSpectrum_normalizedNuclearDistance
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).normalizedNuclearDistance =
      spikeStrength / (population + 1 : ℕ) := by
  rw [FiniteLowRankSingularSpectrum.normalizedNuclearDistance,
    finiteRankOneSingularSpectrum_rawNuclearDistance]
  simp [FiniteOutlierCoordinate]

/-- Its normalized rank is exactly `1/(p+1)`. -/
theorem finiteRankOneSingularSpectrum_rankFraction
    (population : ℕ) (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction =
      1 / (population + 1 : ℕ) := by
  simp [FiniteLowRankSingularSpectrum.rankFraction,
    finiteRankOneSingularSpectrum, FiniteOutlierCoordinate]

/-- The normalized rank of the concrete rank-one spectrum vanishes as
dimension grows. -/
theorem finiteRankOneSingularSpectrum_rankFraction_tendsto_zero
    (spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength) :
    Filter.Tendsto
      (fun population ↦
        (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction)
      Filter.atTop (nhds 0) := by
  have hdenominator : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hinverse := hdenominator.inv_tendsto_atTop
  simpa only [finiteRankOneSingularSpectrum_rankFraction, one_div] using hinverse

/-- The exact model-side data needed to derive the matched scalar-channel
nuclear Lipschitz estimate.  `informationPath` interpolates between two channel
covariances, `tracePairing / 2` is the matrix I--MMSE directional derivative,
and `posteriorCovarianceTraceBound` is the covariance-order plus trace-duality
estimate.  Keeping these as named fields exposes the genuinely probabilistic
premises instead of assuming their final consequence. -/
structure MatchedInformationPathCertificate where
  informationPath : ℝ → ℝ
  tracePairing : ℝ → ℝ
  variance : ℝ
  nuclearDistance : ℝ
  variance_nonnegative : 0 ≤ variance
  nuclearDistance_nonnegative : 0 ≤ nuclearDistance
  immseDerivative : ∀ interpolation ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt informationPath (tracePairing interpolation / 2)
      (Set.Icc (0 : ℝ) 1) interpolation
  posteriorCovarianceTraceBound : ∀ interpolation ∈ Set.Ico (0 : ℝ) 1,
    |tracePairing interpolation| ≤ variance * nuclearDistance

/-- The constant zero path is a concrete matched-information certificate.  It
anchors the abstract certificate API in an actual model with zero variance and
zero covariance displacement. -/
noncomputable def zeroMatchedInformationPathCertificate :
    MatchedInformationPathCertificate where
  informationPath := fun _interpolation ↦ 0
  tracePairing := fun _interpolation ↦ 0
  variance := 0
  nuclearDistance := 0
  variance_nonnegative := le_rfl
  nuclearDistance_nonnegative := le_rfl
  immseDerivative := by
    intro interpolation _hinterpolation
    simpa using (hasDerivAt_const interpolation (0 : ℝ)).hasDerivWithinAt
  posteriorCovarianceTraceBound := by simp

/-- **The matched-information certificate type is inhabited**, so every bound
below is a bound on something. The premises are four nontrivial fields --- a
derivative identity holding on all of `[0,1]` and a trace bound holding on
`[0,1)` --- and a structure whose fields cannot be simultaneously satisfied
would make `matchedInformationPath_nuclear_bound` and everything downstream of
it true by having no models. -/
instance : Nonempty MatchedInformationPathCertificate :=
  ⟨zeroMatchedInformationPathCertificate⟩

/-- **The certificate that runs at the maximum rate the trace bound allows.**
The information path is linear with slope `variance · nuclearDistance / 2`, and
the trace pairing sits at the boundary of `posteriorCovarianceTraceBound`
throughout.

`zeroMatchedInformationPathCertificate` is the degenerate member of this family,
at `variance = nuclearDistance = 0`; this is the family it is degenerate in.
Its purpose is `saturatingMatchedInformationPathCertificate_attains_bound`. -/
noncomputable def saturatingMatchedInformationPathCertificate
    (variance nuclearDistance : ℝ) (hvariance : 0 ≤ variance)
    (hnuclear : 0 ≤ nuclearDistance) : MatchedInformationPathCertificate where
  informationPath := fun interpolation ↦
    variance * nuclearDistance / 2 * interpolation
  tracePairing := fun _interpolation ↦ variance * nuclearDistance
  variance := variance
  nuclearDistance := nuclearDistance
  variance_nonnegative := hvariance
  nuclearDistance_nonnegative := hnuclear
  immseDerivative := by
    intro interpolation _hinterpolation
    have hderivative :
        HasDerivAt (fun t : ℝ ↦ variance * nuclearDistance / 2 * t)
          (variance * nuclearDistance / 2) interpolation := by
      simpa using (hasDerivAt_id interpolation).const_mul
        (variance * nuclearDistance / 2)
    exact hderivative.hasDerivWithinAt
  posteriorCovarianceTraceBound := by
    intro _interpolation _hinterpolation
    exact le_of_eq (abs_of_nonneg (mul_nonneg hvariance hnuclear))

/-- **The pathwise nuclear estimate is attained, so the factor `1/2` is
optimal.** `matchedInformationPath_nuclear_bound` says the information change
along the covariance segment is at most `variance/2 · nuclearDistance`; this
exhibits, at every admissible pair of values, a certificate that changes by
exactly that much. No smaller multiplier than `1/2` is available, so the `1/2`
is the I--MMSE factor of one half and not a slack constant carried through the
calculus. -/
theorem saturatingMatchedInformationPathCertificate_attains_bound
    (variance nuclearDistance : ℝ) (hvariance : 0 ≤ variance)
    (hnuclear : 0 ≤ nuclearDistance) :
    |(saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).informationPath 1 -
      (saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).informationPath 0| =
      (saturatingMatchedInformationPathCertificate variance nuclearDistance
        hvariance hnuclear).variance / 2 *
        (saturatingMatchedInformationPathCertificate variance nuclearDistance
          hvariance hnuclear).nuclearDistance := by
  have hnonneg : 0 ≤ variance * nuclearDistance / 2 :=
    div_nonneg (mul_nonneg hvariance hnuclear) (by norm_num)
  simp only [saturatingMatchedInformationPathCertificate, mul_one, mul_zero,
    sub_zero]
  rw [abs_of_nonneg hnonneg]
  ring

/-- **Matrix-path derivation of the nuclear estimate.**  The I--MMSE
directional derivative and posterior-covariance trace bound imply that the
matched information change along the covariance segment is at most
`variance / 2` times nuclear distance. -/
theorem matchedInformationPath_nuclear_bound
    (certificate : MatchedInformationPathCertificate) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance / 2 * certificate.nuclearDistance := by
  have hderivative : ∀ interpolation ∈ Set.Ico (0 : ℝ) 1,
      ‖certificate.tracePairing interpolation / 2‖ ≤
        certificate.variance / 2 * certificate.nuclearDistance := by
    intro interpolation hinterpolation
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |certificate.tracePairing interpolation| / 2 ≤
          (certificate.variance * certificate.nuclearDistance) / 2 :=
        div_le_div_of_nonneg_right
          (certificate.posteriorCovarianceTraceBound interpolation hinterpolation)
          (by norm_num)
      _ = certificate.variance / 2 * certificate.nuclearDistance := by ring
  have hpath := norm_image_sub_le_of_norm_deriv_le_segment_01'
    certificate.immseDerivative hderivative
  simpa only [Real.norm_eq_abs] using hpath

/-- Combining the pathwise nuclear estimate with `nuclearDistance ≤ operatorBound * rankFraction` gives the normalized low-rank
bound used in the matched-Bayes obstruction. -/
theorem matchedInformationPath_lowRank_bound
    (certificate : MatchedInformationPathCertificate)
    (operatorBound rankFraction : ℝ)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance * operatorBound / 2 * rankFraction := by
  calc
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance / 2 * certificate.nuclearDistance :=
      matchedInformationPath_nuclear_bound certificate
    _ ≤ certificate.variance / 2 * (operatorBound * rankFraction) :=
      mul_le_mul_of_nonneg_left hnuclearRank
        (div_nonneg certificate.variance_nonnegative (by norm_num))
    _ = certificate.variance * operatorBound / 2 * rankFraction := by ring

/-- A uniform upper bound on prior variance is enough for the low-rank
estimate.  Exact equality of variances across a model sequence is unnecessary.
The nonnegativity needed to compare coefficients follows from the certified
nuclear-distance inequality itself. -/
theorem matchedInformationPath_lowRank_bound_of_varianceBound
    (certificate : MatchedInformationPathCertificate)
    (varianceBound operatorBound rankFraction : ℝ)
    (hvarianceBound : certificate.variance ≤ varianceBound)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      varianceBound * operatorBound / 2 * rankFraction := by
  have hproduct : 0 ≤ operatorBound * rankFraction :=
    certificate.nuclearDistance_nonnegative.trans hnuclearRank
  calc
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance * operatorBound / 2 * rankFraction :=
      matchedInformationPath_lowRank_bound certificate operatorBound rankFraction
        hnuclearRank
    _ = certificate.variance / 2 * (operatorBound * rankFraction) := by ring
    _ ≤ varianceBound / 2 * (operatorBound * rankFraction) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hvarianceBound (by norm_num)) hproduct
    _ = varianceBound * operatorBound / 2 * rankFraction := by ring

/-- **I--MMSE low-rank bound derived from singular-value data.**  Once the
path's normalized nuclear distance is identified with the sum of its certified
singular values divided by dimension, the support/rank theorem above supplies
the required nuclear inequality automatically. -/
theorem matchedInformationPath_lowRank_bound_of_singularSpectrum
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : MatchedInformationPathCertificate)
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (hdimension : 0 < Fintype.card Coordinate)
    (hnuclear : certificate.nuclearDistance =
      spectrum.normalizedNuclearDistance) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      certificate.variance * spectrum.operatorBound / 2 * spectrum.rankFraction := by
  apply matchedInformationPath_lowRank_bound certificate spectrum.operatorBound
    spectrum.rankFraction
  rw [hnuclear]
  exact spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension

/-- A uniform prior-variance ceiling gives the corresponding singular-spectrum
bound with `varianceBound` replacing the path's exact variance. -/
theorem matchedInformationPath_lowRank_bound_of_singularSpectrum_of_varianceBound
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (certificate : MatchedInformationPathCertificate)
    (spectrum : FiniteLowRankSingularSpectrum Coordinate)
    (varianceBound : ℝ) (hvarianceBound : certificate.variance ≤ varianceBound)
    (hdimension : 0 < Fintype.card Coordinate)
    (hnuclear : certificate.nuclearDistance =
      spectrum.normalizedNuclearDistance) :
    |certificate.informationPath 1 - certificate.informationPath 0| ≤
      varianceBound * spectrum.operatorBound / 2 * spectrum.rankFraction := by
  apply matchedInformationPath_lowRank_bound_of_varianceBound certificate
    varianceBound spectrum.operatorBound spectrum.rankFraction hvarianceBound
  rw [hnuclear]
  exact spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension

/-- The asymptotic zero-gap conclusion shared by low-rank path certificates. -/
def MatchedInformationPathGapTendsToZero
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate) : Prop :=
  Filter.Tendsto
    (fun index ↦ (certificate index).informationPath 1 -
      (certificate index).informationPath 0)
    regime (nhds 0)

/-- A family of certified matched-information paths with vanishing rank
fraction has vanishing information-density gap whenever its prior variances
are uniformly bounded.  Thus the asymptotic theorem needs no exact common
variance. -/
theorem matchedInformationPath_lowRank_tendsto_zero_of_varianceBound
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate := by
  have hbound : Filter.Tendsto
      (fun index ↦ varianceBound * operatorBound / 2 * rankFraction index)
      regime (nhds 0) := by
    simpa using hrankVanishing.const_mul (varianceBound * operatorBound / 2)
  have habs : Filter.Tendsto
      (fun index ↦ |(certificate index).informationPath 1 -
        (certificate index).informationPath 0|)
      regime (nhds 0) := by
    apply squeeze_zero
    · intro index
      exact abs_nonneg _
    · intro index
      exact matchedInformationPath_lowRank_bound_of_varianceBound
        (certificate index) varianceBound operatorBound (rankFraction index)
        (hvarianceBound index) (hnuclearRank index)
    · exact hbound
  apply (tendsto_zero_iff_abs_tendsto_zero
    (fun index ↦ (certificate index).informationPath 1 -
      (certificate index).informationPath 0)).mpr
  simpa [Function.comp_def] using habs

/-- **Concrete bounded rank-one matched-Bayes invisibility.**  For the
`p+1`-dimensional rank-one singular spectrum, bounded prior variance and exact
identification of the normalized nuclear distance imply that the certified
information-density gap vanishes.  The nuclear/rank estimate is derived above,
not supplied by the caller. -/
theorem matchedInformationPath_rankOne_tendsto_zero_of_varianceBound
    (certificate : ℕ → MatchedInformationPathCertificate)
    (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength)
    (hvarianceBound : ∀ population,
      (certificate population).variance ≤ varianceBound)
    (hnuclear : ∀ population,
      (certificate population).nuclearDistance =
        (finiteRankOneSingularSpectrum population spikeStrength hspike).normalizedNuclearDistance) :
    Filter.Tendsto
      (fun population ↦ (certificate population).informationPath 1 -
        (certificate population).informationPath 0)
      Filter.atTop (nhds 0) := by
  apply matchedInformationPath_lowRank_tendsto_zero_of_varianceBound Filter.atTop
    certificate varianceBound spikeStrength
    (fun population ↦
      (finiteRankOneSingularSpectrum population spikeStrength hspike).rankFraction)
    hvarianceBound
    (finiteRankOneSingularSpectrum_rankFraction_tendsto_zero spikeStrength hspike)
  intro population
  rw [hnuclear population]
  exact
    FiniteLowRankSingularSpectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction
      (finiteRankOneSingularSpectrum population spikeStrength hspike) (by simp)

/-- The earlier common-variance formulation is a specialization of the
uniform-variance theorem, rather than a separate proof path. -/
theorem matchedInformationPath_lowRank_tendsto_zero
    {Index : Type*} (regime : Filter Index)
    (certificate : Index → MatchedInformationPathCertificate)
    (operatorBound : ℝ) (rankFraction : Index → ℝ)
    (hvariance : ∃ variance : ℝ, ∀ index, (certificate index).variance = variance)
    (hrankVanishing : Filter.Tendsto rankFraction regime (nhds 0))
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) :
    MatchedInformationPathGapTendsToZero regime certificate := by
  obtain ⟨variance, hvariance⟩ := hvariance
  exact matchedInformationPath_lowRank_tendsto_zero_of_varianceBound regime
    certificate variance operatorBound rankFraction
    (fun index ↦ (hvariance index).le) hrankVanishing hnuclearRank

/-- The exact Wishart Frobenius second-moment identity plus operator-norm trace
bounds gives the dimension-scale second-moment estimate. -/
theorem wishartFrobeniusSecondMoment_le_dimensionScale
    (dimension sampleSize operatorBound covarianceTrace covarianceTraceSq
      frobeniusSecondMoment : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hoperator : 0 ≤ operatorBound)
    (htrace : |covarianceTrace| ≤ dimension * operatorBound)
    (htraceSq : covarianceTraceSq ≤ dimension * operatorBound ^ 2)
    (hmoment : frobeniusSecondMoment =
      (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize) :
    frobeniusSecondMoment ≤
      operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize := by
  have hdimensionOperator : 0 ≤ dimension * operatorBound :=
    mul_nonneg hdimension.le hoperator
  have hproduct : 0 ≤
      (dimension * operatorBound - |covarianceTrace|) *
        (|covarianceTrace| + dimension * operatorBound) :=
    mul_nonneg (sub_nonneg.mpr htrace)
      (add_nonneg (abs_nonneg _) hdimensionOperator)
  have htracePower : covarianceTrace ^ 2 ≤
      (dimension * operatorBound) ^ 2 := by
    nlinarith [hproduct, sq_abs covarianceTrace]
  rw [hmoment]
  apply (div_le_div_iff_of_pos_right hsampleSize).mpr
  calc
    covarianceTrace ^ 2 + covarianceTraceSq ≤
        (dimension * operatorBound) ^ 2 +
          dimension * operatorBound ^ 2 :=
      add_le_add htracePower htraceSq
    _ = operatorBound ^ 2 * dimension * (dimension + 1) := by ring

/-- Taking square roots converts the Wishart second-moment estimate into the
Frobenius-error scale used by the nuclear comparison. -/
theorem wishartFrobeniusError_le_dimensionScale
    (dimension sampleSize operatorBound frobeniusSecondMoment
      frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hoperator : 0 ≤ operatorBound)
    (hfrobenius : frobeniusError ≤ Real.sqrt frobeniusSecondMoment)
    (hsecondMoment : frobeniusSecondMoment ≤
      operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize) :
    frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize)) := by
  have hratio : 0 ≤ dimension * ((dimension + 1) / sampleSize) := by positivity
  calc
    frobeniusError ≤ Real.sqrt frobeniusSecondMoment := hfrobenius
    _ ≤ Real.sqrt
        (operatorBound ^ 2 * dimension * (dimension + 1) / sampleSize) :=
      Real.sqrt_le_sqrt hsecondMoment
    _ = Real.sqrt (operatorBound ^ 2 *
        (dimension * ((dimension + 1) / sampleSize))) := by
      congr 1
      ring
    _ = Real.sqrt (dimension * ((dimension + 1) / sampleSize)) *
        Real.sqrt (operatorBound ^ 2) := by
      rw [mul_comm, Real.sqrt_mul hratio]
    _ = operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize)) := by
      rw [Real.sqrt_sq hoperator]
      ring

/-- **Deterministic Wishart nuclear-error ledger.**  Combining
`nuclearError ≤ sqrt dimension * frobeniusError` with the standard Wishart
Frobenius scale gives the normalized nuclear scale
`operatorBound * dimension * sqrt ((dimension + 1) / sampleSize)`. -/
theorem wishartNuclearError_le_dimensionScale
    (dimension sampleSize operatorBound nuclearError frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hfrobenius : frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :
    nuclearError ≤ operatorBound * dimension *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hratio : 0 ≤ (dimension + 1) / sampleSize := by positivity
  have hsqrtIdentity : Real.sqrt dimension *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize)) =
        dimension * Real.sqrt ((dimension + 1) / sampleSize) := by
    rw [show Real.sqrt (dimension * ((dimension + 1) / sampleSize)) =
        Real.sqrt ((dimension + 1) / sampleSize) * Real.sqrt dimension by
      rw [mul_comm, Real.sqrt_mul hratio]]
    calc
      Real.sqrt dimension *
          (Real.sqrt ((dimension + 1) / sampleSize) * Real.sqrt dimension) =
          (Real.sqrt dimension * Real.sqrt dimension) *
            Real.sqrt ((dimension + 1) / sampleSize) := by ring
      _ = dimension * Real.sqrt ((dimension + 1) / sampleSize) := by
        rw [Real.mul_self_sqrt hdimension.le]
  calc
    nuclearError ≤ Real.sqrt dimension * frobeniusError := hnuclear
    _ ≤ Real.sqrt dimension * (operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :=
      mul_le_mul_of_nonneg_left hfrobenius (Real.sqrt_nonneg _)
    _ = operatorBound * dimension *
        Real.sqrt ((dimension + 1) / sampleSize) := by
      calc
        Real.sqrt dimension *
            (operatorBound *
              Real.sqrt (dimension * ((dimension + 1) / sampleSize))) =
            operatorBound *
              (Real.sqrt dimension *
                Real.sqrt (dimension * ((dimension + 1) / sampleSize))) := by ring
        _ = _ := by rw [hsqrtIdentity]; ring

/-- **Explicit matched random-design comparison rate.**  The normalized
information-path nuclear estimate and the Wishart nuclear scale imply error at
most `signal * variance * operatorBound / 2 * sqrt ((p+1)/n)`. -/
theorem matchedInformationError_le_wishartScale
    (dimension sampleSize signal variance operatorBound : ℝ)
    (informationError nuclearError : ℝ)
    (hdimension : 0 < dimension) (hsignal : 0 ≤ signal)
    (hvariance : 0 ≤ variance)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError)
    (hnuclear : nuclearError ≤ operatorBound * dimension *
      Real.sqrt ((dimension + 1) / sampleSize)) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hcoefficient : 0 ≤ signal * variance / (2 * dimension) := by positivity
  calc
    |informationError| ≤ signal * variance / (2 * dimension) * nuclearError :=
      hinformation
    _ ≤ signal * variance / (2 * dimension) *
        (operatorBound * dimension *
          Real.sqrt ((dimension + 1) / sampleSize)) :=
      mul_le_mul_of_nonneg_left hnuclear hcoefficient
    _ = signal * variance * operatorBound / 2 *
        Real.sqrt ((dimension + 1) / sampleSize) := by
      field_simp

/-- The full deterministic comparison chain in one theorem: matrix
I--MMSE/nuclear sensitivity, nuclear-to-Frobenius control, and the Wishart
Frobenius scale imply the explicit normalized information error. -/
theorem matchedInformationError_le_of_wishartFrobenius
    (dimension sampleSize signal variance operatorBound : ℝ)
    (informationError nuclearError frobeniusError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hfrobenius : frobeniusError ≤ operatorBound *
      Real.sqrt (dimension * ((dimension + 1) / sampleSize))) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hnuclearScale := wishartNuclearError_le_dimensionScale
    dimension sampleSize operatorBound nuclearError frobeniusError
    hdimension hsampleSize hnuclear hfrobenius
  exact matchedInformationError_le_wishartScale
    dimension sampleSize signal variance operatorBound informationError nuclearError
    hdimension hsignal hvariance hinformation hnuclearScale

/-- **Complete Wishart-to-information comparison theorem.**  Starting from
the exact Wishart second-moment identity and elementary trace bounds, this
derives the normalized matched-information error in one chain. -/
theorem matchedInformationError_le_of_wishartMomentIdentity
    (dimension sampleSize signal variance operatorBound covarianceTrace
      covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
      informationError : ℝ)
    (hdimension : 0 < dimension) (hsampleSize : 0 < sampleSize)
    (hsignal : 0 ≤ signal) (hvariance : 0 ≤ variance)
    (hoperator : 0 ≤ operatorBound)
    (htrace : |covarianceTrace| ≤ dimension * operatorBound)
    (htraceSq : covarianceTraceSq ≤ dimension * operatorBound ^ 2)
    (hmoment : frobeniusSecondMoment =
      (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize)
    (hfrobenius : frobeniusError ≤ Real.sqrt frobeniusSecondMoment)
    (hnuclear : nuclearError ≤ Real.sqrt dimension * frobeniusError)
    (hinformation : |informationError| ≤
      signal * variance / (2 * dimension) * nuclearError) :
    |informationError| ≤ signal * variance * operatorBound / 2 *
      Real.sqrt ((dimension + 1) / sampleSize) := by
  have hsecondMoment := wishartFrobeniusSecondMoment_le_dimensionScale
    dimension sampleSize operatorBound covarianceTrace covarianceTraceSq
    frobeniusSecondMoment hdimension hsampleSize hoperator htrace htraceSq hmoment
  have hfrobeniusScale := wishartFrobeniusError_le_dimensionScale
    dimension sampleSize operatorBound frobeniusSecondMoment frobeniusError
    hdimension hsampleSize hoperator hfrobenius hsecondMoment
  exact matchedInformationError_le_of_wishartFrobenius
    dimension sampleSize signal variance operatorBound informationError nuclearError
    frobeniusError hdimension hsampleSize hsignal hvariance hinformation
    hnuclear hfrobeniusScale

/-- The explicit Wishart comparison scale itself vanishes with the adjusted
dimension/sample ratio.  This analytic fact is shared by information-error
convergence and by the two-design separation theorem. -/
theorem wishartSqrtComparisonError_tendsto_zero
    {Index : Type*} (regime : Filter Index)
    (adjustedRatio : Index → ℝ) (constant : ℝ)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0)) :
    Filter.Tendsto (fun index ↦ constant * Real.sqrt (adjustedRatio index))
      regime (nhds 0) := by
  have hsqrt : Filter.Tendsto
      (fun index ↦ Real.sqrt (adjustedRatio index)) regime (nhds 0) := by
    simpa using hratio.sqrt
  simpa using hsqrt.const_mul constant

/-- A uniform Wishart-scale information bound vanishes whenever the adjusted
dimension/sample ratio tends to zero. -/
theorem matchedInformationError_tendsto_zero_of_wishartRatio
    {Index : Type*} (regime : Filter Index)
    (informationError adjustedRatio : Index → ℝ) (constant : ℝ)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0))
    (herror : ∀ index,
      |informationError index| ≤ constant * Real.sqrt (adjustedRatio index)) :
    Filter.Tendsto informationError regime (nhds 0) := by
  have hbound := wishartSqrtComparisonError_tendsto_zero
    regime adjustedRatio constant hratio
  have habs : Filter.Tendsto (fun index ↦ |informationError index|)
      regime (nhds 0) :=
    squeeze_zero (fun index ↦ abs_nonneg _) herror hbound
  apply (tendsto_zero_iff_abs_tendsto_zero informationError).mpr
  simpa [Function.comp_def] using habs

/-- **Random-design reduction, as the sharp asymmetric error ledger.**  If the
left and right random-design information densities have errors `εₗ` and `εᵣ`,
the scalar gap `Δ` loses at most their sum. -/
theorem randomDesign_gap_of_scalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - (leftError + rightError) ≤ randomRight - randomLeft := by
  have hlowerLeft : randomLeft ≤ scalarLeft + leftError := by
    have := le_trans (le_abs_self (randomLeft - scalarLeft)) hleft
    linarith
  have hlowerRight : scalarRight - rightError ≤ randomRight := by
    have := le_trans (neg_le_abs (randomRight - scalarRight)) hright
    linarith
  linarith

/-- Equal comparison errors specialize the asymmetric ledger to the familiar
loss `2ε`. -/
theorem randomDesign_gap_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) :
    delta - 2 * epsilon ≤ randomRight - randomLeft := by
  simpa only [two_mul] using
    randomDesign_gap_of_scalarGap_asymmetric scalarLeft scalarRight randomLeft randomRight
      epsilon epsilon delta hleft hright hgap

/-- A scalar gap larger than the sum of the two comparison errors forces a
strict random-design gap. -/
theorem randomDesign_separates_of_scalarGap_asymmetric
    (scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ leftError)
    (hright : |randomRight - scalarRight| ≤ rightError)
    (hgap : scalarRight - scalarLeft = delta)
    (hpositive : leftError + rightError < delta) :
    randomLeft < randomRight := by
  have hbound := randomDesign_gap_of_scalarGap_asymmetric scalarLeft scalarRight
    randomLeft randomRight leftError rightError delta hleft hright hgap
  linarith

/-- In particular a scalar matched-channel gap larger than twice the comparison error forces a
random-design gap. -/
theorem randomDesign_separates_of_scalarGap
    (scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ epsilon)
    (hright : |randomRight - scalarRight| ≤ epsilon)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 2 * epsilon < delta) :
    randomLeft < randomRight :=
  randomDesign_separates_of_scalarGap_asymmetric scalarLeft scalarRight
    randomLeft randomRight epsilon epsilon delta hleft hright hgap (by
      simpa only [two_mul] using hpositive)

/-- **Finite large-aspect-ratio reduction.**  If both random-design channels
are within `constant / sqrt aspectRatio` of their scalar counterparts, the
scalar gap survives whenever it exceeds twice that explicit error. -/
theorem randomDesign_separates_of_scalarGap_of_inverseSqrtAspect
    (scalarLeft scalarRight randomLeft randomRight : ℝ)
    (aspectRatio constant delta : ℝ)
    (hleft : |randomLeft - scalarLeft| ≤ constant / Real.sqrt aspectRatio)
    (hright : |randomRight - scalarRight| ≤ constant / Real.sqrt aspectRatio)
    (hgap : scalarRight - scalarLeft = delta)
    (hthreshold : 2 * (constant / Real.sqrt aspectRatio) < delta) :
    randomLeft < randomRight :=
  randomDesign_separates_of_scalarGap scalarLeft scalarRight randomLeft randomRight
    (constant / Real.sqrt aspectRatio) delta hleft hright hgap hthreshold

/-- **A positive scalar matched-channel gap survives eventually when the two
possibly different comparison errors both vanish.**  This is the asymptotic
completion of the sharp asymmetric ledger.

The model-specific work is exactly the convergence of the two error functions;
no additional uniformity or hidden constant is assumed here. -/
theorem randomDesign_eventually_separates_of_scalarGap_asymmetric
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight leftError rightError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ leftError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ rightError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftVanishing : Filter.Tendsto leftError regime (nhds 0))
    (hrightVanishing : Filter.Tendsto rightError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index := by
  have hsum : Filter.Tendsto (fun index ↦ leftError index + rightError index)
      regime (nhds 0) := by
    simpa using hleftVanishing.add hrightVanishing
  have hbelow : ∀ᶠ index in regime, leftError index + rightError index < delta :=
    hsum.eventually_lt_const hpositive
  filter_upwards [hbelow] with index hthreshold
  exact randomDesign_separates_of_scalarGap_asymmetric
    scalarLeft scalarRight (randomLeft index) (randomRight index)
    (leftError index) (rightError index) delta (hleft index) (hright index)
    hgap hthreshold

/-- The common-error asymptotic theorem is the equal-error specialization of
the asymmetric result. -/
theorem randomDesign_eventually_separates_of_scalarGap
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta : ℝ)
    (randomLeft randomRight comparisonError : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ comparisonError index)
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ comparisonError index)
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (herrorVanishing : Filter.Tendsto comparisonError regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_asymmetric regime
    scalarLeft scalarRight delta randomLeft randomRight comparisonError comparisonError
    hleft hright hgap hpositive herrorVanishing herrorVanishing

/-- Reciprocation identifies the large-aspect filter exactly with approach to
zero from the positive side.  This is the precise bridge between the two
large-sample parameterizations used below; no positivity hypothesis is hidden,
because it is carried by the one-sided neighborhood `𝓝[>] 0`. -/
theorem aspectAtTop_iff_inverseTendstoNhdsGTZero
    {Index : Type*} (regime : Filter Index) (aspectRatio : Index → ℝ) :
    Filter.Tendsto aspectRatio regime Filter.atTop ↔
      Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (𝓝[>] 0) := by
  constructor
  · intro haspect
    exact tendsto_inv_atTop_nhdsGT_zero.comp haspect
  · intro hinverse
    have hreciprocal := hinverse.inv_tendsto_nhdsGT_zero
    convert hreciprocal using 1
    funext index
    simp

/-- In particular, a diverging aspect ratio has a reciprocal converging to
zero in the ordinary two-sided topology. -/
theorem inverseAspect_tendsto_zero
    {Index : Type*} (regime : Filter Index) (aspectRatio : Index → ℝ)
    (haspect : Filter.Tendsto aspectRatio regime Filter.atTop) :
    Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (nhds 0) :=
  haspect.inv_tendsto_atTop

/-- The inverse-square-root and square-root-of-reciprocal error formulas are
identical, including at zero and for negative inputs under Lean's totalized
real square root. -/
theorem div_sqrt_eq_mul_sqrt_inv (constant aspectRatio : ℝ) :
    constant / Real.sqrt aspectRatio =
      constant * Real.sqrt (aspectRatio⁻¹) := by
  rw [Real.sqrt_inv, div_eq_mul_inv]

/-- **Sharp two-design Wishart reduction.**  The two channels may have
different constants and different adjusted dimension/sample ratios.  If both
Wishart scales vanish, every fixed positive scalar gap eventually transfers. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_asymmetricWishartRatios
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta leftConstant rightConstant : ℝ)
    (leftRatio rightRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        leftConstant * Real.sqrt (leftRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        rightConstant * Real.sqrt (rightRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hleftRatio : Filter.Tendsto leftRatio regime (nhds 0))
    (hrightRatio : Filter.Tendsto rightRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_asymmetric regime
    scalarLeft scalarRight delta randomLeft randomRight
    (fun index ↦ leftConstant * Real.sqrt (leftRatio index))
    (fun index ↦ rightConstant * Real.sqrt (rightRatio index))
    hleft hright hgap hpositive
    (wishartSqrtComparisonError_tendsto_zero regime leftRatio leftConstant hleftRatio)
    (wishartSqrtComparisonError_tendsto_zero regime rightRatio rightConstant hrightRatio)

/-- **Common-ratio Wishart reduction.**  This is the equal-constant,
equal-ratio specialization of the sharp two-design theorem. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_wishartRatio
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (adjustedRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤
        constant * Real.sqrt (adjustedRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (hratio : Filter.Tendsto adjustedRatio regime (nhds 0)) :
    ∀ᶠ index in regime, randomLeft index < randomRight index :=
  randomDesign_eventually_separates_of_scalarGap_of_asymmetricWishartRatios regime
    scalarLeft scalarRight delta constant constant adjustedRatio adjustedRatio
    randomLeft randomRight hleft hright hgap hpositive hratio hratio

/-- **Concrete large-aspect-ratio asymptotic reduction.**  This applies the
Wishart-ratio theorem above after the reciprocal reparameterization
`adjustedRatio = aspectRatio⁻¹`.  Thus the two APIs have one proof path rather
than independent asymptotic arguments. -/
theorem randomDesign_eventually_separates_of_scalarGap_of_aspectAtTop
    {Index : Type*} (regime : Filter Index)
    (scalarLeft scalarRight delta constant : ℝ)
    (aspectRatio randomLeft randomRight : Index → ℝ)
    (hleft : ∀ index,
      |randomLeft index - scalarLeft| ≤ constant / Real.sqrt (aspectRatio index))
    (hright : ∀ index,
      |randomRight index - scalarRight| ≤ constant / Real.sqrt (aspectRatio index))
    (hgap : scalarRight - scalarLeft = delta) (hpositive : 0 < delta)
    (haspectRatio : Filter.Tendsto aspectRatio regime Filter.atTop) :
    ∀ᶠ index in regime, randomLeft index < randomRight index := by
  apply randomDesign_eventually_separates_of_scalarGap_of_wishartRatio regime
    scalarLeft scalarRight delta constant
    (fun index ↦ (aspectRatio index)⁻¹) randomLeft randomRight
  · intro index
    simpa only [div_sqrt_eq_mul_sqrt_inv] using hleft index
  · intro index
    simpa only [div_sqrt_eq_mul_sqrt_inv] using hright index
  · exact hgap
  · exact hpositive
  · exact inverseAspect_tendsto_zero regime aspectRatio haspectRatio

/-- **Low-rank perturbations cannot solve the matched scalar problem once the
nuclear estimate is available.**  The path-certificate theorem above derives
that estimate from matrix I--MMSE and posterior-covariance trace control; this
scalar corollary then turns rank fraction `ε` into error `constant * ε`. -/
theorem matchedDensity_lowRank_bound_of_nuclearEstimate
    (densityGap constant rankFraction epsilon : ℝ)
    (hconstant : 0 ≤ constant) (hrank : rankFraction ≤ epsilon)
    (hnuclear : |densityGap| ≤ constant * rankFraction) :
    |densityGap| ≤ constant * epsilon := by
  exact hnuclear.trans (mul_le_mul_of_nonneg_left hrank hconstant)

/-- **Sublinear-rank perturbations are asymptotically invisible to matched
information-density under the matrix I-MMSE/nuclear estimate.**  This is the
sequence theorem asserted by the low-rank boundary argument: once the rank
fraction tends to zero, the absolute information-density gap is squeezed to
zero by the same fixed nuclear-norm constant.

The final nuclear estimate may either be supplied directly or obtained from
`MatchedInformationPathCertificate`; the asymptotic passage from it to
invisibility is proved here. -/
theorem matchedDensity_lowRank_tendsto_zero_of_nuclearEstimate
    (densityGap rankFraction : ℕ → ℝ) (constant : ℝ)
    (hrankVanishing : Filter.Tendsto rankFraction Filter.atTop (nhds 0))
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    Filter.Tendsto densityGap Filter.atTop (nhds 0) := by
  have hbound :
      Filter.Tendsto (fun index ↦ constant * rankFraction index)
        Filter.atTop (nhds 0) := by
    have hconstant : Filter.Tendsto (fun _index : ℕ ↦ constant)
        Filter.atTop (nhds constant) := tendsto_const_nhds
    simpa using hconstant.mul hrankVanishing
  have habs :
      Filter.Tendsto (fun index ↦ |densityGap index|)
        Filter.atTop (nhds 0) :=
    squeeze_zero
      (fun index ↦ abs_nonneg (densityGap index))
      hnuclear hbound
  apply (tendsto_zero_iff_abs_tendsto_zero densityGap).mpr
  simpa [Function.comp_def] using habs

/-- **Finite extensive-rank certificate.**  Under the matrix
I--MMSE/nuclear estimate, a matched information-density gap of magnitude at
least `delta > 0` forces rank fraction at least `delta / constant`. -/
theorem matchedDensity_positiveGap_forces_rankFraction
    (densityGap constant rankFraction delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : delta ≤ |densityGap|)
    (hnuclear : |densityGap| ≤ constant * rankFraction) :
    0 < rankFraction ∧ delta / constant ≤ rankFraction := by
  have hlower : delta / constant ≤ rankFraction :=
    (div_le_iff₀ hconstant).mpr (by
      calc
        delta ≤ constant * rankFraction := hgap.trans hnuclear
        _ = rankFraction * constant := mul_comm _ _)
  exact ⟨(div_pos hdelta hconstant).trans_le hlower, hlower⟩

/-- A persistent positive matched-density gap forces an eventual uniform
lower bound on the perturbation rank fraction. -/
theorem matchedDensity_eventualGap_forces_eventualRankFraction
    {Index : Type*} (regime : Filter Index)
    (densityGap rankFraction : Index → ℝ) (constant delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : ∀ᶠ index in regime, delta ≤ |densityGap index|)
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    ∀ᶠ index in regime, delta / constant ≤ rankFraction index := by
  filter_upwards [hgap] with index hindex
  exact (matchedDensity_positiveGap_forces_rankFraction
    (densityGap index) constant (rankFraction index) delta
    hconstant hdelta hindex (hnuclear index)).2

/-- Consequently a persistent order-one matched-density separation is
incompatible with a rank fraction tending to zero.  This is the quantitative
extensive-rank obstruction required of any negative matched-Bayes witness. -/
theorem matchedDensity_eventualGap_not_sublinearRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (densityGap rankFraction : Index → ℝ) (constant delta : ℝ)
    (hconstant : 0 < constant) (hdelta : 0 < delta)
    (hgap : ∀ᶠ index in regime, delta ≤ |densityGap index|)
    (hnuclear : ∀ index,
      |densityGap index| ≤ constant * rankFraction index) :
    ¬ Filter.Tendsto rankFraction regime (nhds 0) := by
  have hrankLower := matchedDensity_eventualGap_forces_eventualRankFraction
    regime densityGap rankFraction constant delta hconstant hdelta hgap hnuclear
  intro hrankZero
  have hthreshold : 0 < delta / constant := div_pos hdelta hconstant
  have hrankUpper : ∀ᶠ index in regime,
      rankFraction index < delta / constant :=
    hrankZero.eventually_lt_const hthreshold
  obtain ⟨index, hlower, hupper⟩ := (hrankLower.and hrankUpper).exists
  exact (not_lt_of_ge hlower) hupper

/-- **Certified finite extensive-rank obstruction.**  A positive information
gap along an I--MMSE path, a uniform variance bound, and a nuclear-to-rank
comparison force an explicit positive rank fraction.  No final information
Lipschitz inequality is accepted as an assumption. -/
theorem matchedInformationPath_positiveGap_forces_rankFraction_of_varianceBound
    (certificate : MatchedInformationPathCertificate)
    (varianceBound operatorBound rankFraction delta : ℝ)
    (hvarianceBound : certificate.variance ≤ varianceBound)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hgap : delta ≤
      |certificate.informationPath 1 - certificate.informationPath 0|)
    (hnuclearRank : certificate.nuclearDistance ≤ operatorBound * rankFraction) :
    0 < rankFraction ∧
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction := by
  apply matchedDensity_positiveGap_forces_rankFraction
    (certificate.informationPath 1 - certificate.informationPath 0)
    (varianceBound * operatorBound / 2) rankFraction delta
  · positivity
  · exact hdelta
  · exact hgap
  · exact matchedInformationPath_lowRank_bound_of_varianceBound certificate
      varianceBound operatorBound rankFraction hvarianceBound hnuclearRank

/-- **Certified asymptotic extensive-rank obstruction.**  If a family of
I--MMSE paths has uniformly bounded positive variance scale and a persistent
order-one information gap, its perturbation rank fraction is eventually
bounded below by the exact finite constant and cannot tend to zero. -/
theorem matchedInformationPath_persistentGap_requires_extensiveRank
    {Index : Type*} (regime : Filter Index) [regime.NeBot]
    (certificate : Index → MatchedInformationPathCertificate)
    (varianceBound operatorBound delta : ℝ) (rankFraction : Index → ℝ)
    (hvariancePositive : 0 < varianceBound) (hoperator : 0 < operatorBound)
    (hdelta : 0 < delta)
    (hvarianceBound : ∀ index, (certificate index).variance ≤ varianceBound)
    (hnuclearRank : ∀ index,
      (certificate index).nuclearDistance ≤ operatorBound * rankFraction index)
    (hgap : ∀ᶠ index in regime, delta ≤
      |(certificate index).informationPath 1 -
        (certificate index).informationPath 0|) :
    (∀ᶠ index in regime,
      delta / (varianceBound * operatorBound / 2) ≤ rankFraction index) ∧
      ¬ Filter.Tendsto rankFraction regime (nhds 0) := by
  let densityGap := fun index ↦
    (certificate index).informationPath 1 - (certificate index).informationPath 0
  let constant := varianceBound * operatorBound / 2
  have hconstant : 0 < constant := by
    dsimp only [constant]
    positivity
  have hinformation : ∀ index,
      |densityGap index| ≤ constant * rankFraction index := by
    intro index
    exact matchedInformationPath_lowRank_bound_of_varianceBound
      (certificate index) varianceBound operatorBound (rankFraction index)
      (hvarianceBound index) (hnuclearRank index)
  exact ⟨matchedDensity_eventualGap_forces_eventualRankFraction regime
      densityGap rankFraction constant delta hconstant hdelta hgap hinformation,
    matchedDensity_eventualGap_not_sublinearRank regime densityGap rankFraction
      constant delta hconstant hdelta hgap hinformation⟩

end MatchedBayesBoundary

end TrafficInvariantSeparation
end Descent.Blindness
